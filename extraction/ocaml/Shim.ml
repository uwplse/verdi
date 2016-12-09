open Printf
open Unix
open Util

let _CLOG = "clog.bin"
let _SNAP = "snapshot.bin"
               
module type ARRANGEMENT = sig
  type name
  type state
  type input
  type output
  type msg
  type client_id
  type res = (output list * state) * ((name * msg) list)
  val systemName : string
  val init : name -> state
  val reboot : state -> state
  val handleIO : name -> input -> state -> res
  val handleNet : name -> name -> msg -> state -> res
  val handleTimeout : name -> state -> res
  val setTimeout : name -> state -> float
  val deserializeMsg : string -> msg
  val serializeMsg : msg -> string
  val deserializeInput : string -> client_id -> input option
  val serializeOutput : output -> client_id * string
  val debug : bool
  val debugInput : state -> input -> unit
  val debugRecv : state -> (name * msg) -> unit
  val debugSend : state -> (name * msg) -> unit
  val debugTimeout : state -> unit
  val createClientId : unit -> client_id
  val serializeClientId : client_id -> string
end

module Shim (A: ARRANGEMENT) = struct
  type cfg =
      { cluster : (A.name * (string * int)) list
      ; me : A.name
      ; port : int
      ; dbpath : string
      }

  type env =
      { cfg : cfg
      ; command_log : out_channel
      ; nodes_fd : file_descr
      ; clients_fd : file_descr
      ; nodes : (A.name * sockaddr) list
      ; client_read_fds : (file_descr, A.client_id) Hashtbl.t
      ; client_write_fds : (A.client_id, file_descr) Hashtbl.t
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
  let denote_node (env : env) (name : A.name) : sockaddr =
    List.assoc name env.nodes

  (* Translate UDP socket address to node name. *)
  let undenote_node (env : env) (addr : sockaddr) : A.name =
    let flip = function (x, y) -> (y, x) in
    List.assoc addr (List.map flip env.nodes)

  (* Translate client id to TCP socket address *)
  let denote_client (env : env) (c : A.client_id) : file_descr =
    Hashtbl.find env.client_write_fds c

  (* Translate TCP socket address to client id *)
  let undenote_client (env : env) (fd : file_descr) : A.client_id =
    Hashtbl.find env.client_read_fds fd

  (* Return state with a single entry from the log applied to the given state. *)
  let update_state_from_log_entry (log : in_channel) (name : A.name) (state : A.state) : A.state =
    let op = ((Marshal.from_channel log) : log_step) in
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
      let (restored_state : A.state) = Marshal.from_channel snapshot in
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
      ; nodes_fd = socket PF_INET SOCK_DGRAM 0
      ; clients_fd = socket PF_INET SOCK_STREAM 0
      ; nodes = List.map addressify cfg.cluster
      ; client_read_fds = Hashtbl.create 17
      ; client_write_fds = Hashtbl.create 17
      ; saves = 0
      }
    in
    setsockopt env.clients_fd SO_REUSEADDR true;
    setsockopt env.nodes_fd SO_REUSEADDR true;
    bind env.nodes_fd (ADDR_INET (inet_addr_any, port));
    bind env.clients_fd (ADDR_INET (inet_addr_any, cfg.port));
    listen env.clients_fd 8;
    (env, initial_state)

  let disconnect_client env fd reason =
    let c = undenote_client env fd in
    Hashtbl.remove env.client_read_fds fd;
    Hashtbl.remove env.client_write_fds c;
    close fd;
    printf "client %s disconnected: %s" (A.serializeClientId c) reason;
    print_newline ()

  let sendto sock buf addr =
    try
      ignore (Unix.sendto sock buf 0 (String.length buf) [] addr)
    with Unix_error (err, fn, arg) ->
      printf "error in sendto: %s, dropping message" (error_message err);
      print_newline ()

  let send env ((nm : A.name), (msg : A.msg)) =
    sendto env.nodes_fd (A.serializeMsg msg) (denote_node env nm)

  let send_to_client env fd out =
    try ignore (Unix.send fd (out ^ "\n") 0 (String.length out) [])
    with Unix_error (err, fn, arg) ->
      disconnect_client env fd (sprintf "error in send_to_client: %s" (error_message err))

  let output env o =
    let (c, out) = A.serializeOutput o in
    try send_to_client env (denote_client env c) out
    with Not_found ->
      printf "output: failed to find socket for client %s" (A.serializeClientId c);
      print_newline ()

  let save env (step : log_step) (st : A.state)  =
    if (env.saves > 0 && env.saves mod 1000 = 0) then begin
      print_endline "snapshotting";
      let csnap = out_channel_of_descr (openfile (snapshot_path env.cfg) [O_WRONLY ; O_TRUNC ; O_CREAT ; O_DSYNC] 0o640) in
      Marshal.to_channel csnap st []; flush csnap; close_out csnap;
      ftruncate (descr_of_out_channel env.command_log) 0
    end;
    Marshal.to_channel env.command_log step [];
    flush env.command_log;
    env.saves <- env.saves + 1

  let respond env ((os, s), ps) =
    List.iter (output env) os;
    List.iter (fun p -> if A.debug then A.debugSend s p; send env p) ps;
    s

  let new_client_conn env =
    let (client_fd, client_addr) = accept env.clients_fd in
    let c = A.createClientId () in
    Hashtbl.add env.client_read_fds client_fd c;
    Hashtbl.add env.client_write_fds c client_fd;
    printf "client %s connected on %s" (A.serializeClientId c) (string_of_sockaddr client_addr);
    print_newline ()

  exception Disconnect_client of string

  let read_from_client fd len =
    let buf = String.make len '\x00' in
    let bytes_read = recv fd buf 0 len [MSG_PEEK] in
    if bytes_read = 0 then raise (Disconnect_client "client closed socket");
    let msg_len =
      try (String.index buf '\n') + 1
      with Not_found -> raise (Disconnect_client "invalid data from client") in
    let buf2 = String.make msg_len '\x00' in
    ignore (recv fd buf2 0 msg_len []);
    buf

  let input_step (fd : file_descr) (env : env) (state : A.state) =
    try
      let buf = read_from_client fd 1024 in
      let c = undenote_client env fd in
      match A.deserializeInput buf c with
      | Some inp ->
        save env (LogInput inp) state;
        let state' = respond env (A.handleIO env.cfg.me inp state) in
        if A.debug then A.debugInput state' inp;
        state'
      | None ->
	disconnect_client env fd "input deserialization failed";
	state
    with
    | Disconnect_client s ->
      disconnect_client env fd s;
      state
    | Unix_error (err, fn, _) ->
      disconnect_client env fd (sprintf "error in %s: %s" fn (error_message err));
      state

  let recv_step (env : env) (state : A.state) : A.state =
    let len = 65536 in
    let buf = String.make len '\x00' in
    let (_, from) = recvfrom env.nodes_fd buf 0 len [] in
    let (src, msg) = (undenote_node env from, A.deserializeMsg buf) in
    save env (LogNet (src, msg)) state;
    let state' = respond env (A.handleNet env.cfg.me src msg state) in
    if A.debug then A.debugRecv state' (src, msg);
    state'

  let timeout_step (env : env) (state : A.state) : A.state =
    save env LogTimeout state;
    if A.debug then A.debugTimeout state;
    let x = A.handleTimeout env.cfg.me state in
    respond env x

  let rec select_unintr rs ws es t =
    try select rs ws es t
    with
    | Unix_error (EINTR, fn, arg) ->
      select_unintr rs ws es t
    | Unix_error (e, _, _) ->
      printf "select error: %s" (error_message e);
      print_newline ();
      select_unintr rs ws es t

  let process_fd env state fd : A.state =
    if fd = env.clients_fd then
      begin new_client_conn env; state end
    else if fd = env.nodes_fd then
      recv_step env state
    else
      input_step fd env state

  let rec eloop (env : env) (state : A.state) : unit =
    let client_fds = Hashtbl.fold (fun fd _ acc -> fd :: acc) env.client_read_fds [] in
    let all_fds = env.nodes_fd :: env.clients_fd :: client_fds in
    let (ready_fds, _, _) = select_unintr all_fds [] [] (A.setTimeout env.cfg.me state) in
    let state' =
      match ready_fds with
      | [] -> timeout_step env state
      | _ -> List.fold_left (process_fd env) state ready_fds in
    eloop env state'

  let main (cfg : cfg) : unit =
    printf "unordered shim running setup for %s" A.systemName;
    print_newline ();
    let (env, initial_state) = setup cfg in
    print_endline "unordered shim ready for action";
    eloop env initial_state
end
