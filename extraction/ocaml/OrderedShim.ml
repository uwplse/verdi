open Printf
open Unix
open Util
open Daemon

module type ARRANGEMENT = sig
  type name
  type state
  type input
  type output
  type msg
  type client_id
  type res = (output list * state) * ((name * msg) list)
  val systemName : string
  val serializeName : name -> string
  val deserializeName : string -> name option
  val init : name -> state
  val handleIO : name -> input -> state -> res
  val handleNet : name -> name -> msg -> state -> res
  val deserializeMsg : string -> msg
  val serializeMsg : msg -> string
  val deserializeInput : string -> client_id -> input option
  val serializeOutput : output -> client_id * string
  val failMsg : msg option
  val newMsg : msg option
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
      }

  type env =
      { cluster : (A.name, string * int) Hashtbl.t
      ; port : int
      ; me : A.name
      ; node_fd : file_descr
      ; client_fd : file_descr
      ; node_read_fds : (file_descr, A.name) Hashtbl.t
      ; node_write_fds : (A.name, file_descr) Hashtbl.t
      ; client_read_fds : (file_descr, A.client_id) Hashtbl.t
      ; client_write_fds : (A.client_id, file_descr) Hashtbl.t
      }

  exception Connection of string

  let sock_of_name (env : env) (node_name : A.name) : string * int =
    Hashtbl.find env.cluster node_name

  (* Translate node name to TCP socket address *)
  let denote_node (env : env) (node_name : A.name) : file_descr =
    Hashtbl.find env.node_write_fds node_name

  (* Translate TCP socket address to node name *)
  let undenote_node (env : env) (fd : file_descr) : A.name =
    Hashtbl.find env.node_read_fds fd

  (* Translate client id to TCP socket address *)
  let denote_client (env : env) (c : A.client_id) : file_descr =
    Hashtbl.find env.client_write_fds c

  (* Translate TCP socket address to client id *)
  let undenote_client (env : env) (fd : file_descr) : A.client_id =
    Hashtbl.find env.client_read_fds fd

  (* Gets state from the most recent snapshot, or the initial state from the arrangement. *)
  let get_initial_state (env : env) : A.state =
    A.init env.me

  (* Initialize environment, and start server. *)
  let setup (cfg : cfg) : (env * A.state) =
    Random.self_init ();
    let env =
      { cluster = Hashtbl.create (List.length cfg.cluster)
      ; port = cfg.port
      ; me = cfg.me
      ; node_fd = socket PF_INET SOCK_STREAM 0
      ; client_fd = socket PF_INET SOCK_STREAM 0
      ; node_read_fds = Hashtbl.create 17
      ; node_write_fds = Hashtbl.create 17
      ; client_read_fds = Hashtbl.create 17
      ; client_write_fds = Hashtbl.create 17
      } in
    let initial_state = get_initial_state env in
    List.iter (fun (n, s) -> Hashtbl.add env.cluster n s) cfg.cluster;
    let (ip, port) = Hashtbl.find env.cluster env.me in
    let entry = gethostbyname ip in
    let listen_addr = Array.get entry.h_addr_list 0 in
    setsockopt env.node_fd SO_REUSEADDR true;
    setsockopt env.client_fd SO_REUSEADDR true;
    bind env.node_fd (ADDR_INET (listen_addr, port));
    bind env.client_fd (ADDR_INET (inet_addr_any, env.port));
    listen env.node_fd 8;
    listen env.client_fd 8;
    (env, initial_state)

  let send_chunk (fd : file_descr) (buf : string) : unit =
    let len = String.length buf in
    let n = Unix.send fd (raw_bytes_of_int len) 0 4 [] in
    if n < 4 then raise (Connection "send_chunk: message header failed to send all at once");
    let n = Unix.send fd buf 0 len [] in
    if n < len then raise (Connection (sprintf "send_chunk: message of length %d failed to send all at once" len))

  let recv_or_raise fd buf offs len flags =
    let n = recv fd buf offs len flags in
    if n = 0 then raise (Connection "recv_or_close: other side closed connection");
    n

  let receive_chunk env (fd : file_descr) : bytes =
    let buf4 = Bytes.make 4 '\x00' in
    let n = recv_or_raise fd buf4 0 4 [] in
    if n < 4 then raise (Connection "receive_chunk: message header did not arrive all at once");
    let len = int_of_raw_bytes buf4 in
    let buf = Bytes.make len '\x00' in
    let n = recv_or_raise fd buf 0 len [] in
    if n < len then raise (Connection (sprintf "receive_chunk: message of length %d did not arrive all at once" len));
    buf

  let add_write_fd env node_name node_addr =
    printf "connecting to %s for the first time..." (A.serializeName node_name);
    print_newline ();
    let write_fd = socket PF_INET SOCK_STREAM 0 in
    connect write_fd node_addr;
    send_chunk write_fd (A.serializeName env.me);
    let (ip, port) = sock_of_name env env.me in
    send_chunk write_fd (sprintf "%s:%d" ip port);
    begin
      match A.newMsg with
      | Some m -> send_chunk write_fd (A.serializeMsg m)
      | None -> ()
    end;
    print_endline "...connected!";
    Hashtbl.replace env.node_write_fds node_name write_fd;
    write_fd

  let get_node_write_fd env node_name =
    try denote_node env node_name
    with Not_found ->
      if Hashtbl.mem env.cluster node_name then
        let (ip, port) = sock_of_name env node_name in
        let entry = gethostbyname ip in
        let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, port) in
        add_write_fd env node_name node_addr
      else
        failwith "get_node_write_fd: cannot find name"

  let send env ((nm : A.name), (msg : A.msg)) : unit =
    let fd = get_node_write_fd env nm in
    send_chunk fd (A.serializeMsg msg)

  let output env o =
    let (c, out) = A.serializeOutput o in
    let fd =
      try denote_client env c
      with Not_found -> failwith "output: failed to find destination client"
    in
    send_chunk fd out

  let respond env ((os, s), ps) =
    let go p =
      try
        if A.debug then A.debugSend s p;
        send env p
      with e -> printf "respond moving on after exception: %s" (Printexc.to_string e);
                print_newline () in
    List.iter (output env) os;
    List.iter go ps;
    s

  let deliver_msg env state src msg : A.state =
    let state' = respond env (A.handleNet env.me src msg state) in
    if A.debug then A.debugRecv state' (src, msg);
    state'

  let recv_step (env : env) (fd : file_descr) (state : A.state) : A.state =
    let buf = receive_chunk env fd in
    let src =
      try undenote_node env fd
      with Not_found -> failwith "recv_step: failed to find source for message (it has probably been marked failed)"
    in
    let msg = A.deserializeMsg buf in
    deliver_msg env state src msg

  let new_node_conn env =
    printf "new node connection";
    print_newline ();
    let (node_fd, node_addr) = accept env.node_fd in
    let name_buf = receive_chunk env node_fd in
    match A.deserializeName name_buf with
    | Some node_name ->
      let sock_buf = receive_chunk env node_fd in
      let sock =
	try Scanf.sscanf sock_buf "%[^:]:%d" (fun i p -> (i, p))
	with _ -> failwith (sprintf "new_node_conn: sscanf error %s" sock_buf)
      in
      Hashtbl.replace env.node_read_fds node_fd node_name;
      Hashtbl.replace env.cluster node_name sock;
      ignore (get_node_write_fd env node_name);
      printf "done processing new connection from node %s" (A.serializeName node_name);
      print_newline ();
      node_fd
    | None ->
      failwith (sprintf "new_node_conn: failed to deserialize name %s" name_buf)

  let new_client_conn env =
    let (client_fd, client_addr) = accept env.client_fd in
    let c = A.createClientId () in
    Hashtbl.replace env.client_read_fds client_fd c;
    Hashtbl.replace env.client_write_fds c client_fd;
    printf "client %s connected on %s" (A.serializeClientId c) (string_of_sockaddr client_addr);
    print_newline ();
    client_fd

  let connect_to_nodes env =
    let go nm =
      try ignore (get_node_write_fd env nm)
      with e -> printf "connect_to_nodes: moving on after exception %s" (Printexc.to_string e);
                print_newline () in
    List.iter go (Hashtbl.fold (fun nm _ acc -> if nm != env.me then nm :: acc else acc) env.cluster [])

  let input_step (fd : file_descr) (env : env) (state : A.state) =
    let buf = receive_chunk env fd in
    let c = undenote_client env fd in
    match A.deserializeInput buf c with
    | Some inp ->
      let state' = respond env (A.handleIO env.me inp state) in
      if A.debug then A.debugInput state' inp;
      state'
    | None ->
      failwith (sprintf "input_step: could not deserialize %s" buf)

  (* task: read node message *)
  let node_read_task fd =
    { fd = fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let state' = recv_step env t.fd state in
	    (false, [], state')
	  with Connection s ->
	    printf "connection to node %s: %s" (A.serializeName (undenote_node env t.fd)) s;
	    print_newline ();
	    (true, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize =
	(fun t env state ->
	  let n = undenote_node env t.fd in
	  printf "closing connection to node %s" (A.serializeName n);
	  print_newline ();
	  Hashtbl.remove env.node_read_fds t.fd;
	  Hashtbl.remove env.node_write_fds n;
	  Hashtbl.remove env.cluster n;
	  Unix.close t.fd;
	  match A.failMsg with
          | Some m -> deliver_msg env state n m
          | None -> state)
    }

  (* task: read client input *)
  let client_read_task fd =
    { fd = fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let state' = input_step t.fd env state in
	    (false, [], state')
	  with Connection s ->
	    printf "connection to client %s: %s" (A.serializeClientId (undenote_client env t.fd)) s;
	    print_newline ();
	    (true, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize =
	(fun t env state ->
	  let c = undenote_client env t.fd in
	  printf "closing connection to client %s" (A.serializeClientId c);
	  print_newline ();
	  Hashtbl.remove env.client_read_fds t.fd;
	  Hashtbl.remove env.client_write_fds c;
	  Unix.close t.fd;
	  state)
    }

  let main (cfg : cfg) : unit =
    printf "ordered shim running setup for %s" A.systemName;
    print_newline ();
    let (env, initial_state) = setup cfg in
    let tasks = Hashtbl.create 10 in
    let t_conn_nd = (* connect to neighbors in cluster *)
      { fd = Unix.dup env.node_fd
      ; select_on = false
      ; wake_time = Some 1.0
      ; process_read = (fun t env state -> (false, [], state))
      ; process_wake =
	  (fun t env state ->
	    begin
	      try connect_to_nodes env
	      with Connection s ->
		printf "connecting to nodes in cluster: %s" s;
		print_newline ()
	    end;
	    t.wake_time <- Some 1.0;
	    (false, [], state))
      ; finalize = (fun t env state -> Unix.close t.fd; state)
      } in
    let t_nd_conn = (* listen to neighbors connecting *)
      { fd = env.node_fd
      ; select_on = true
      ; wake_time = None
      ; process_read =
	  (fun t env state ->
	    try
	      let node_fd = new_node_conn env in
	      (false, [node_read_task node_fd], state)
	    with Connection s ->
	      printf "incoming node connection: %s" s;
	      print_newline ();
	      (false, [], state))
      ; process_wake = (fun t env state -> (false, [], state))
      ; finalize = (fun t env state -> Unix.close t.fd; state)
      } in
    let t_cl_conn = (* listen to clients connecting *)
      { fd = env.client_fd
      ; select_on = true
      ; wake_time = None
      ; process_read =
	  (fun t env state ->
	    try
	      let client_fd = new_client_conn env in
	      (false, [client_read_task client_fd], state)
	    with Connection s ->
	      printf "incoming client connection: %s" s;
	      print_newline ();
	      (false, [], state))
      ; process_wake = (fun t env state -> (false, [], state))
      ; finalize = (fun t env state -> Unix.close t.fd; state)
      } in
    Hashtbl.add tasks t_conn_nd.fd t_conn_nd;
    Hashtbl.add tasks t_nd_conn.fd t_nd_conn;
    Hashtbl.add tasks t_cl_conn.fd t_cl_conn;
    print_endline "ordered shim ready for action";
    eloop 2.0 (Unix.gettimeofday ()) tasks env initial_state

end
