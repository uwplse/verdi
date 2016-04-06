open Printf
open Unix

module M = Marshal

let _LOG = "/tmp/verdi-log"
let _SNAP = "/tmp/verdi-snapshot"
               
module type ARRANGEMENT = sig
  type name
  type state
  type input
  type output
  type msg
  type res = (output list * state) * ((name * msg) list)
  type request_id
  val init : name -> state
  val reboot : state -> state
  val handleIO : name -> input -> state -> res
  val handleNet : name -> name -> msg -> state -> res
  val handleTimeout : name -> state -> res
  val setTimeout : name -> state -> float
  val deserialize : string -> ((request_id *  input) option)
  val serialize : output -> (request_id * string)
  val debug : bool
  val debugRecv : state -> (name * msg) -> unit
  val debugSend : state -> (name * msg) -> unit
  val debugTimeout : state -> unit
end

module Shim (A: ARRANGEMENT) = struct
  type env =
      { restored_state : A.state
      ; snapfile : string
      ; clog : out_channel
      ; usock : file_descr
      ; isock : file_descr
      ; mutable csocks : file_descr list
      ; outstanding : (A.request_id, file_descr) Hashtbl.t
      ; mutable saves : int
      ; nodes : (A.name * sockaddr) list
      }

  type log_step =
  | LogInput of A.input
  | LogNet of A.name * A.msg
  | LogTimeout

  let denote env nm : sockaddr =
    List.assoc nm env.nodes

  let undenote env addr : A.name =
    let flip = function (x, y) -> (y, x) in
    List.assoc addr (List.map flip env.nodes)
               
  let update_state_from_log_entry log nm s =
    let op = ((M.from_channel log) : log_step) in
    (snd (fst (match op with
               | LogInput inp -> A.handleIO nm inp s
               | LogNet (src, m) -> A.handleNet nm src m s
               | LogTimeout -> A.handleTimeout nm s)))

  let rec restore_from_log log nm s =
    try
      let s' = update_state_from_log_entry log nm s in
      restore_from_log log nm s'
    with End_of_file -> (close_in log); s

  let get_initial_state snapfile nm =
    try
      let csnap = open_in snapfile in
      let (restored_state : A.state) = M.from_channel csnap in
      close_in csnap; restored_state
    with
      Sys_error _ -> A.init nm

  let restore snapfile log_file nm =
    let initial_state = get_initial_state snapfile nm in
    try
      let log = open_in_bin log_file in
      restore_from_log log nm initial_state
    with Sys_error _ -> initial_state

  let setup nm nodes =
    Random.self_init ();
    let port = snd (List.assoc nm nodes) in
    let clog = (_LOG ^ "-" ^ string_of_int port) in
    let snapfile = (_SNAP ^ "-" ^ string_of_int port) in
    let addressify (name, (ip, port)) =
      (name, ADDR_INET (inet_addr_of_string ip, port))
    in
    let restored_state = restore snapfile clog nm in
    let env =
      { restored_state = A.reboot restored_state
      ; snapfile = snapfile
      ; clog = out_channel_of_descr (openfile clog [O_WRONLY ; O_APPEND ; O_CREAT ; O_DSYNC] 0o640)
      ; usock = socket PF_INET SOCK_DGRAM 0
      ; isock = socket PF_INET SOCK_STREAM 0
      ; csocks = []
      ; outstanding = Hashtbl.create 64
      ; saves = 0
      ; nodes = List.map addressify nodes
      }
    in
    setsockopt env.isock SO_REUSEADDR true;
    setsockopt env.usock SO_REUSEADDR true;
    bind env.usock (ADDR_INET (inet_addr_any, port));
    bind env.isock (ADDR_INET (inet_addr_any, port-1000));
    listen env.isock 8;
    env

    
  let sendto sock buf addr =
    try
      ignore (Unix.sendto sock buf 0 (String.length buf) [] addr)
    with Unix_error (err, fn, arg) ->
      print_endline ("Error from sendto: " ^ (error_message err) ^ ", closing socket");
      close sock

  let send env ((nm : A.name), (msg : A.msg)) =
    sendto env.usock (M.to_string msg []) (denote env nm)

  let respond_to_client sock r =
    try
      ignore (Unix.send sock (r ^ "\n") 0 (String.length r) [])
    with Unix_error (err, fn, arg) ->
      print_endline ("Error from send: " ^ (error_message err) ^ ", closing socket");
      close sock

  let output env o =
    let (id, s) = A.serialize o in
    let socks = Hashtbl.find_all env.outstanding id in
    match socks with
    | sock :: _ ->
       respond_to_client sock s;
       Hashtbl.remove env.outstanding id
    | [] -> ()
                   
  let unpack_msg buf : A.msg =
    M.from_string buf 0

  let save env (step : log_step) (st : A.state)  =
    (if (env.saves > 0 && env.saves mod 1000 = 0) then
       (print_endline "snapshotting";
        let csnap = out_channel_of_descr (openfile env.snapfile [O_WRONLY ; O_TRUNC ; O_CREAT ; O_DSYNC] 0o640) in
        M.to_channel csnap st []; flush csnap; close_out csnap;
        ftruncate (descr_of_out_channel env.clog) 0));
    M.to_channel env.clog step []; flush env.clog; env.saves <- env.saves + 1

  let respond env ((os, s), ps) =
    List.iter (output env) os;
    List.iter (fun p -> (if A.debug then A.debugSend s p); send env p) ps;
    s

  let new_conn env =
    let (client_sock, _) = accept env.isock in
    env.csocks <- client_sock :: env.csocks

  let disconnect env client_sock =
    close client_sock;
    env.csocks <- List.filter (fun c -> c <> client_sock) env.csocks

  type severity =
    | S_info
    | S_error

  exception Disconnect_client of (severity * string)

  let read_from_socket sock len =
    let buf = String.make len '\x00' in
    try
      let bytes_read = recv sock buf 0 len [MSG_PEEK] in
      (if bytes_read == 0 then raise (Disconnect_client (S_info, "client closed socket")));
      let msg_len = (String.index buf '\n') + 1 in
      let buf2 = String.make msg_len '\x00' in
      let _ = recv sock buf2 0 msg_len [] in
      buf
    with
      Not_found -> raise (Disconnect_client (S_error, "client became invalid"))

  let input_step client_sock env nm s =
    let len = 1024 in
    let buf = read_from_socket client_sock len in
    let d = A.deserialize buf in
    match d with
    | Some (id, inp) ->
       save env (LogInput inp) s;
       Hashtbl.replace env.outstanding id client_sock;
       respond env (A.handleIO nm inp s)
    | None ->
       raise (Disconnect_client (S_error, "received invalid input"))

  let recv_step env nm s =
    let len = 65536 in
    let buf = String.make len '\x00' in
    let (_, from) = recvfrom env.usock buf 0 len [] in
    let (src, m) = (undenote env from, unpack_msg buf) in
    save env (LogNet (src, m)) s;
    let s' = respond env (A.handleNet nm src m s) in
    (if A.debug then A.debugRecv s' (src, m)); s'

  let timeout_step env nm s =
    save env LogTimeout s;
    (if A.debug then A.debugTimeout s);
    let x = A.handleTimeout nm s in
    respond env x

  let rec my_select rs ws es t =
    try select rs ws es t
    with Unix_error (err, fn, arg) ->
      my_select rs ws es t

  let rec eloop env nm s =
    let (fds, _, _) = my_select (List.append [env.usock; env.isock] env.csocks) [] [] (A.setTimeout nm s) in
    let s' =
      match (List.mem env.isock fds, List.mem env.usock fds, List.filter (fun c -> List.mem c fds) env.csocks) with
      | (true, _, _) -> new_conn env ; s
      | (_, _, c :: cs) ->
         (try input_step c env nm s
         with
           Unix_error (err, fn, arg) ->
             prerr_string fn;
             prerr_string " failed: ";
             prerr_endline (error_message err);
             disconnect env c;
             s
         | Disconnect_client (sev, msg) ->
             (match sev with
             | S_info -> ()
             | S_error ->
                print_string "client disconnected: ";
                print_endline msg);
             disconnect env c;
             s)
      | (_, true, _) -> recv_step env nm s
      | _ -> timeout_step env nm s in
    eloop env nm s'

  let default v o =
    match o with
    | None -> v
    | Some v' -> v'

  let main nm nodes =
    print_endline "running setup";
    let env = setup nm nodes in
    print_endline "starting";
    let s = env.restored_state in
    eloop env nm s
end
