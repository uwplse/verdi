open Printf
open Unix

module M = Marshal

let _CLOG = "clog.bin"
let _SNAP = "snapshot.bin"
               
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
  type client =
      { sock : file_descr
      ; addr : sockaddr
      }

  type cfg =
      { cluster : (A.name * (string * int)) list
      ; me : A.name
      ; port : int
      ; dbpath : string
      }

  type env =
      { cfg : cfg
      ; command_log : out_channel
      ; usock : file_descr
      ; isock : file_descr
      ; nodes : (A.name * sockaddr) list
      ; mutable clients : client list
      ; outstanding : (A.request_id, client) Hashtbl.t
      ; mutable saves : int
      }

  let command_log_path (cfg : cfg) : string =
    cfg.dbpath ^ "/" ^ _CLOG

  let snapshot_path (cfg : cfg) : string =
    cfg.dbpath ^ "/" ^ _SNAP

  type log_step =
  | LogInput of A.input
  | LogNet of A.name * A.msg
  | LogTimeout

  (* Translate node name to UDP socket address. *)
  let denote (env : env) (name : A.name) : sockaddr =
    List.assoc name env.nodes

  (* Translate UDP socket ddress to node name. *)
  let undenote (env : env) (addr : sockaddr) : A.name =
    let flip = function (x, y) -> (y, x) in
    List.assoc addr (List.map flip env.nodes)

  (* Return state with a single entry from the log applied to the given state. *)
  let update_state_from_log_entry (log : in_channel) (name : A.name) (state : A.state) : A.state =
    let op = ((M.from_channel log) : log_step) in
    (snd (fst (match op with
               | LogInput inp -> A.handleIO name inp state
               | LogNet (src, msg) -> A.handleNet name src msg state
               | LogTimeout -> A.handleTimeout name state)))

  (* Return state with as many entries from the log applied as possible. *)
  let rec restore_from_log (log : in_channel) (name : A.name) (state : A.state) : A.state =
    try
      let state' = update_state_from_log_entry log name state in
      restore_from_log log name state'
    with End_of_file -> (close_in log); state

  (* Gets state from the most recent snapshot, or the initial state from the arrangement. *)
  let get_initial_state (cfg : cfg) : A.state =
    try
      let snapshot = open_in (snapshot_path cfg) in
      let (restored_state : A.state) = M.from_channel snapshot in
      close_in snapshot;
      restored_state
    with
      Sys_error _ -> A.init (cfg.me)

  let restore (cfg : cfg) : A.state =
    let initial_state = get_initial_state cfg in
    try
      let log = open_in_bin (command_log_path cfg) in
      restore_from_log log cfg.me initial_state
    with Sys_error _ -> initial_state

  (* Load state from disk, initialize environment, and start server. *)
  let setup (cfg : cfg) : (env * A.state) =
    Random.self_init ();
    let port = snd (List.assoc cfg.me cfg.cluster) in
    let addressify (name, (host, port)) =
      let entry = gethostbyname host in
      (name, ADDR_INET (Array.get entry.h_addr_list 0, port))
    in
    begin
      try
        mkdir cfg.dbpath 0o700
      with Unix_error (err, fn, param) ->
        if err != EEXIST then
          raise (Unix_error (err, fn, param))
    end;
    let initial_state = A.reboot (restore cfg) in
    let env =
      { cfg = cfg
      ; command_log = out_channel_of_descr (openfile (command_log_path cfg) [O_WRONLY ; O_APPEND ; O_CREAT ; O_DSYNC] 0o640)
      ; usock = socket PF_INET SOCK_DGRAM 0
      ; isock = socket PF_INET SOCK_STREAM 0
      ; nodes = List.map addressify cfg.cluster
      ; clients = []
      ; outstanding = Hashtbl.create 64
      ; saves = 0
      }
    in
    setsockopt env.isock SO_REUSEADDR true;
    setsockopt env.usock SO_REUSEADDR true;
    bind env.usock (ADDR_INET (inet_addr_any, port));
    bind env.isock (ADDR_INET (inet_addr_any, cfg.port));
    listen env.isock 8;
    (env, initial_state)

  let string_of_sockaddr (saddr : sockaddr) : string =
    match saddr with
    | ADDR_UNIX path -> (sprintf "unix://%s" path)
    | ADDR_INET (addr, port) -> (sprintf "%s:%d" (string_of_inet_addr addr) port)

  let disconnect env client reason =
    close client.sock;
    env.clients <- List.filter (fun c -> c <> client) env.clients;
    printf "Client %s disconnected (%s)" (string_of_sockaddr client.addr) reason;
    print_newline ()

  let sendto sock buf addr =
    try
      ignore (Unix.sendto sock buf 0 (String.length buf) [] addr)
    with Unix_error (err, fn, arg) ->
      printf "Error from sendto: %s, dropping message" (error_message err);
      print_newline ()

  let send env ((nm : A.name), (msg : A.msg)) =
    sendto env.usock (M.to_string msg []) (denote env nm)

  let respond_to_client env client msg =
    try
      ignore (Unix.send client.sock (msg ^ "\n") 0 (String.length msg) [])
    with Unix_error (err, fn, arg) ->
      disconnect env client ("Error from send: " ^ (error_message err))

  let output env o =
    let (id, msg) = A.serialize o in
    let clients = Hashtbl.find_all env.outstanding id in
    match clients with
    | client :: _ ->
       respond_to_client env client msg;
       Hashtbl.remove env.outstanding id
    | [] -> ()
                   
  let unpack_msg buf : A.msg =
    M.from_string buf 0

  let save env (step : log_step) (st : A.state)  =
    if (env.saves > 0 && env.saves mod 1000 = 0) then begin
      print_endline "snapshotting";
      let csnap = out_channel_of_descr (openfile (snapshot_path env.cfg) [O_WRONLY ; O_TRUNC ; O_CREAT ; O_DSYNC] 0o640) in
      M.to_channel csnap st []; flush csnap; close_out csnap;
      ftruncate (descr_of_out_channel env.command_log) 0
    end;
    M.to_channel env.command_log step [];
    flush env.command_log;
    env.saves <- env.saves + 1

  let respond env ((os, s), ps) =
    List.iter (output env) os;
    List.iter (fun p -> (if A.debug then A.debugSend s p); send env p) ps;
    s

  let new_conn env =
    let (client_sock, client_addr) = accept env.isock in
    let client =
      { sock = client_sock
      ; addr = client_addr
      } in
    env.clients <- client :: env.clients;
    printf "Client connected on %s" (string_of_sockaddr client_addr);
    print_newline ()

  type severity =
    | S_info
    | S_error

  exception Disconnect_client of (severity * string)

  let read_from_socket sock len =
    let buf = String.make len '\x00' in
    try
      let bytes_read = recv sock buf 0 len [MSG_PEEK] in
      if bytes_read == 0 then begin
        raise (Disconnect_client (S_info, "client closed socket"))
      end;
      let msg_len = (String.index buf '\n') + 1 in
      let buf2 = String.make msg_len '\x00' in
      let _ = recv sock buf2 0 msg_len [] in
      buf
    with
      Not_found -> raise (Disconnect_client (S_error, "client became invalid"))

  let input_step (client : client) (env : env) (name : A.name) (state : A.state) =
    let len = 1024 in
    let buf = read_from_socket client.sock len in
    let d = A.deserialize buf in
    match d with
    | Some (id, inp) ->
       save env (LogInput inp) state;
       Hashtbl.replace env.outstanding id client;
       respond env (A.handleIO name inp state)
    | None ->
       raise (Disconnect_client (S_error, "received invalid input"))

  let recv_step (env : env) (state : A.state) : A.state =
    let len = 65536 in
    let buf = String.make len '\x00' in
    let (_, from) = recvfrom env.usock buf 0 len [] in
    let (src, msg) = (undenote env from, unpack_msg buf) in
    save env (LogNet (src, msg)) state;
    let state' = respond env (A.handleNet env.cfg.me src msg state) in
    if A.debug then begin
      A.debugRecv state' (src, msg)
    end;
    state'

  let timeout_step (env : env) (state : A.state) : A.state =
    save env LogTimeout state;
    if A.debug then begin
      A.debugTimeout state
    end;
    let x = A.handleTimeout env.cfg.me state in
    respond env x

  let rec my_select rs ws es t =
    try select rs ws es t
    with Unix_error (err, fn, arg) ->
      my_select rs ws es t

  let rec eloop (env : env) (state : A.state) : unit =
    let client_sockets = List.map (fun c -> c.sock) env.clients in
    let sockets = List.append [env.usock; env.isock] client_sockets in
    let (fds, _, _) = my_select sockets [] [] (A.setTimeout env.cfg.me state) in
    let state' =
      match (List.mem env.isock fds, List.mem env.usock fds, List.filter (fun c -> List.mem c.sock fds) env.clients) with
      | (true, _, _) -> new_conn env ; state
      | (_, _, client_socket :: _) -> begin
          try input_step client_socket env env.cfg.me state
          with
            Unix_error (err, fn, arg) ->
              disconnect env client_socket (sprintf "%s failed: %s" fn (error_message err));
              state
          | Disconnect_client (sev, msg) ->
              disconnect env client_socket msg;
              state
      end
      | (_, true, _) -> recv_step env state
      | _ -> timeout_step env state in
    eloop env state'

  let main (cfg : cfg) : unit =
    print_endline "Unordered shim running setup";
    let (env, initial_state) = setup cfg in
    print_endline "Unordered shim ready for action";
    eloop env initial_state
end
