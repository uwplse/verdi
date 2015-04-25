open Printf
open Unix

module M = Marshal

let _LOG = "/tmp/verdi-log"
let _SNAP = "/tmp/verdi-snapshot"
               
(* wrapper structure for Coq defined structure *)
module type ARRANGEMENT = sig
  type name
  type state
  type input
  type output
  type msg
  type res = (output list * state) * ((name * msg) list)
  val init : name -> state
  val reboot : state -> state
  val handleIO : name -> input -> state -> res
  val handleNet : name -> name -> msg -> state -> res
  val handleTimeout : name -> state -> res
  val setTimeout : name -> state -> float
  val deserialize : int -> string -> (input option)
  val serialize : output -> (int * string)
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
      (* outstanding is a collection of sockets *)
      ; outstanding : (int, file_descr) Hashtbl.t
      ; mutable id : int
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
    let (id, op) = ((M.from_channel log) : int * log_step) in
    (id, (snd (fst (match op with
                    (* call handleIO, which is a wrapper of input handler defined in coq *)
                    | LogInput inp -> A.handleIO nm inp s
                    | LogNet (src, m) -> A.handleNet nm src m s
                    | LogTimeout -> A.handleTimeout nm s))))

(* keep update 's' as the state by replaying all actions in the log *)
  let rec restore_from_log log nm id s =
    try
      let (id', s') = update_state_from_log_entry log nm s in
      restore_from_log log nm id' s'
    with End_of_file -> (close_in log); (id, s)

  let get_initial_state snapfile nm =
    try
      let csnap = open_in snapfile in
      let (restored_state : A.state) = M.from_channel csnap in
      close_in csnap; restored_state
    with
      Sys_error _ -> A.init nm

  let restore snapfile log_file nm =
    let initial_state = get_initial_state snapfile nm in
    let id = 0 in
    try
      let log = open_in_bin log_file in
      restore_from_log log nm id initial_state
    with Sys_error _ -> (id, initial_state)

  let setup nm nodes =
    Random.self_init ();
    let port = snd (List.assoc nm nodes) in
    let clog = (_LOG ^ "-" ^ string_of_int port) in
    let snapfile = (_SNAP ^ "-" ^ string_of_int port) in
    let addressify (name, (ip, port)) =
      (name, ADDR_INET (inet_addr_of_string ip, port))
    in
    let (id, restored_state) = restore snapfile clog nm in
    let env =
      { restored_state = A.reboot restored_state
      ; snapfile = snapfile
      ; clog = out_channel_of_descr (openfile clog [O_WRONLY ; O_APPEND ; O_CREAT ; O_DSYNC] 0o640)
      ; usock = socket PF_INET SOCK_DGRAM 0
      ; isock = socket PF_INET SOCK_STREAM 0
      ; csocks = []
      ; outstanding = Hashtbl.create 64
      ; id = id
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
    ignore (Unix.sendto sock buf 0 (String.length buf) [] addr)

  let send env ((nm : A.name), (msg : A.msg)) =
    sendto env.usock (M.to_string msg []) (denote env nm)

  let respond_to_client sock r =
    ignore (Unix.send sock r 0 (String.length r) [])

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
    M.to_channel env.clog (env.id, step) []; flush env.clog; env.saves <- env.saves + 1

  let respond env ((os, s), ps) =
    List.iter (output env) os;
    List.iter (fun p -> (if A.debug then A.debugSend s p); send env p) ps;
    s

  let new_conn env =
    let (client_sock, _) = accept env.isock in
    env.csocks <- client_sock :: env.csocks

  let input_step client_sock env nm s =
  (* let-binding should be regarded as local variable declaration, and executed once at the place of declaration *)
    let len = 1024 in
    let buf = String.make len '\x00' in
    let _ = recv client_sock buf 0 len [] in
    let i = A.deserialize env.id buf in
    match i with
    | Some inp ->
       save env (LogInput inp) s;
       Hashtbl.replace env.outstanding env.id client_sock;
       env.id <- env.id + 1;
       respond env (A.handleIO nm inp s)
    | None ->
       print_endline "received invalid input; closing connection";
       close client_sock;
       env.csocks <- List.filter (fun c -> c <> client_sock) env.csocks;
       s

  let recv_step env nm s =
    let len = 4096 in
    let buf = String.make len '\x00' in
    let (_, from) = recvfrom env.usock buf 0 len [] in
    let (src, m) = (undenote env from, unpack_msg buf) in
    save env (LogNet (src, m)) s;
    let s' = respond env (A.handleNet nm src m s) in
    (* a single s' at the last of the function means to return s' *)
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
  (* get new connection *)
    let (fds, _, _) = my_select (List.append [env.usock; env.isock] env.csocks) [] [] (A.setTimeout nm s) in
    let s' =
    (* matching decides which action applied on fds *)
      match (List.mem env.isock fds, List.mem env.usock fds, List.filter (fun c -> List.mem c fds) env.csocks) with
      (* four kinds of action *)
      (* new_conn will not update state 's', other function will update the state and return it *)
      | (true, _, _) -> new_conn env ; s
      | (_, _, c :: cs) -> input_step c env nm s
      | (_, true, _) -> recv_step env nm s
      | _ -> timeout_step env nm s in
    eloop env nm s'

  let default v o =
    match o with
    | None -> v
    | Some v' -> v'

  (* nm = number of nodes *)
  let main nm nodes =
    print_endline "running setup";
    let env = setup nm nodes in
    print_endline "starting";
    let s = env.restored_state in
    eloop env nm s
end
