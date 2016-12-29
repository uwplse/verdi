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
  type task_handler = name -> state -> res
  type timeout_setter = name -> state -> float
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
  val createClientId : unit -> client_id
  val serializeClientId : client_id -> string
  val timeoutTasks : (task_handler * timeout_setter) list
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
      ; nodes_fd : file_descr
      ; clients_fd : file_descr
      ; node_read_fds : (file_descr, A.name) Hashtbl.t
      ; node_fds_read : (A.name, file_descr) Hashtbl.t
      ; node_write_fds : (A.name, file_descr) Hashtbl.t
      ; client_read_fds : (file_descr, A.client_id) Hashtbl.t
      ; client_write_fds : (A.client_id, file_descr) Hashtbl.t
      ; tasks : (file_descr, (env, A.state) task) Hashtbl.t
      }

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

  (* Gets initial state from the arrangement *)
  let get_initial_state (env : env) : A.state =
    A.init env.me

  (* Initialize environment *)
  let setup (cfg : cfg) : (env * A.state) =
    Random.self_init ();
    let env =
      { cluster = Hashtbl.create (List.length cfg.cluster)
      ; port = cfg.port
      ; me = cfg.me
      ; nodes_fd = socket PF_INET SOCK_STREAM 0
      ; clients_fd = socket PF_INET SOCK_STREAM 0
      ; node_read_fds = Hashtbl.create 17
      ; node_fds_read = Hashtbl.create 17
      ; node_write_fds = Hashtbl.create 17
      ; client_read_fds = Hashtbl.create 17
      ; client_write_fds = Hashtbl.create 17
      ; tasks = Hashtbl.create 17
      } in
    let initial_state = get_initial_state env in
    List.iter (fun (n, s) -> Hashtbl.add env.cluster n s) cfg.cluster;
    let (ip, port) = Hashtbl.find env.cluster env.me in
    let entry = gethostbyname ip in
    let listen_addr = Array.get entry.h_addr_list 0 in
    setsockopt env.nodes_fd SO_REUSEADDR true;
    setsockopt env.clients_fd SO_REUSEADDR true;
    bind env.nodes_fd (ADDR_INET (listen_addr, port));
    bind env.clients_fd (ADDR_INET (inet_addr_any, env.port));
    listen env.nodes_fd 8;
    listen env.clients_fd 8;
    (env, initial_state)

  exception Disconnect of string

  (* throws Unix_error, Disconnect *)
  let send_chunk (fd : file_descr) (buf : string) : unit =
    let len = String.length buf in
    let n = Unix.send fd (raw_bytes_of_int len) 0 4 [] in
    if n < 4 then raise (Disconnect "send_chunk: message header failed to send all at once");
    let n = Unix.send fd buf 0 len [] in
    if n < len then raise (Disconnect (sprintf "send_chunk: message of length %d failed to send all at once" len))
  
  (* throws Unix_error, Disconnect *)
  let receive_chunk env (fd : file_descr) : bytes =
    let receive_check fd buf offs len flags =
      let n = Unix.recv fd buf offs len flags in
      if n = 0 then raise (Disconnect "receive_chunk: other side closed connection");
      n
    in
    let buf4 = Bytes.make 4 '\x00' in
    let n = receive_check fd buf4 0 4 [] in
    if n < 4 then raise (Disconnect "receive_chunk: message header did not arrive all at once");
    let len = int_of_raw_bytes buf4 in
    let buf = Bytes.make len '\x00' in
    let n = receive_check fd buf 0 len [] in
    if n < len then raise (Disconnect (sprintf "receive_chunk: message of length %d did not arrive all at once" len));
    buf

  let schedule_finalize_task t =
    t.select_on <- false;
    t.wake_time <- Some 0.5;
    t.process_read <- (fun t env state -> (true, [], state));
    t.process_wake <- (fun t env state -> (true, [], state))

  (* throws nothing *)
  let output env o =
    let (c, out) = A.serializeOutput o in
    try send_chunk (denote_client env c) out
    with
    | Not_found ->
      eprintf "output: failed to find socket for client %s\n" (A.serializeClientId c)
    | Disconnect s ->
      eprintf "output: failed send to client %s: %s\n" (A.serializeClientId c) s;
      schedule_finalize_task (Hashtbl.find env.tasks (denote_client env c))
    | Unix_error (err, fn, _) ->
      eprintf "output: error %s\n" (error_message err);
      schedule_finalize_task (Hashtbl.find env.tasks (denote_client env c))
  
  (* throws Unix_error *)
  let new_client_conn env =
    let (client_fd, client_addr) = accept env.clients_fd in
    let c = A.createClientId () in
    Hashtbl.replace env.client_read_fds client_fd c;
    Hashtbl.replace env.client_write_fds c client_fd;
    if A.debug then printf "[%s] client %s connected on %s\n" (timestamp ()) (A.serializeClientId c) (string_of_sockaddr client_addr);
    client_fd

  (* throws Disconnect *)
  let add_write_node_fd env node_name node_addr =
    if A.debug then printf "[%s] connecting to %s for the first time...\n" (timestamp ()) (A.serializeName node_name);
    let write_fd = Unix.socket PF_INET SOCK_STREAM 0 in
    try
      Unix.connect write_fd node_addr;
      send_chunk write_fd (A.serializeName env.me);
      let (ip, port) = sock_of_name env env.me in
      send_chunk write_fd (sprintf "%s:%d" ip port);
      if A.debug then printf "[%s] ...connected!\n" (timestamp ());
      Hashtbl.replace env.node_write_fds node_name write_fd;
      write_fd
    with
    | Disconnect s -> Unix.close write_fd; raise (Disconnect s)
    | Unix_error (err, fn, _) ->
      Unix.close write_fd; raise (Disconnect (sprintf "add_write_fd: error in %s: %s" fn (error_message err)))

  (* throws Disconnect *)
  let get_write_node_fd env node_name =
    try denote_node env node_name
    with Not_found ->
      try
	let (ip, port) = sock_of_name env node_name in
	let entry = gethostbyname ip in
	let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, port) in
	add_write_node_fd env node_name node_addr
      with Not_found -> raise (Disconnect "get_write_node_fd: lookup error")

  (* throws Disconnect *)
  let new_node_conn env =
    if A.debug then printf "[%s] new incoming node connection\n" (timestamp ());
    let (node_read_fd, node_addr) = accept env.nodes_fd in
    let name_buf = 
      try receive_chunk env node_read_fd
      with
      | Disconnect s -> Unix.close node_read_fd; raise (Disconnect s)
      | Unix_error (err, fn, _) ->
	Unix.close node_read_fd; raise (Disconnect (sprintf "new_node_conn: error in %s: %s" fn (error_message err)))
    in 
    match A.deserializeName name_buf with
    | None -> Unix.close node_read_fd; raise (Disconnect (sprintf "new_node_conn: failed to deserialize name %s" name_buf))
    | Some node_name ->
      let sock_buf = 
	try receive_chunk env node_read_fd 
	with
	| Disconnect s -> Unix.close node_read_fd; raise (Disconnect s)
	| Unix_error (err, fn, _) -> 
	  Unix.close node_read_fd; raise (Disconnect (sprintf "new_node_conn: error in %s: %s" fn (error_message err)))
      in
      let sock =
	try Scanf.sscanf sock_buf "%[^:]:%d" (fun i p -> (i, p))
	with _ -> Unix.close node_read_fd; raise (Disconnect (sprintf "new_node_conn: sscanf error %s" sock_buf))
      in
      Hashtbl.replace env.cluster node_name sock;
      begin
	try ignore (get_write_node_fd env node_name)
	with Disconnect s -> Unix.close node_read_fd; raise (Disconnect s)
      end;
      Hashtbl.replace env.node_read_fds node_read_fd node_name;
      Hashtbl.replace env.node_fds_read node_name node_read_fd;
      if A.debug then printf "[%s] done processing new connection from node %s\n" (timestamp ()) (A.serializeName node_name);
      node_read_fd

  (* throws nothing *)
  let connect_to_nodes env =
    let go node_name =
      try ignore (get_write_node_fd env node_name)
      with Disconnect s -> 
	eprintf "connect_to_nodes: moving on after error for node %s: %s\n" (A.serializeName node_name) s;
    in
    let ns = Hashtbl.fold (fun n _ acc -> if n != env.me then n :: acc else acc) env.cluster [] in
    List.iter go ns

  (* throws Disconnect, Unix_error *)
  let send_msg env node_name msg =
    let node_fd = 
      try denote_node env node_name
      with Not_found -> raise (Disconnect "send_msg: message destination not found")
    in
    send_chunk node_fd (A.serializeMsg msg)

  (* throws nothing *)
  let respond env ((os, s), ps) = (* assume outgoing message destinations have tasks *)
    let go ((node_name : A.name), (msg : A.msg)) =
      try if A.debug then A.debugSend s (node_name, msg); send_msg env node_name msg
      with
      | Disconnect s ->
	eprintf "respond: error for node %s: %s\n" (A.serializeName node_name) s;
	let task_fd = Hashtbl.find env.node_fds_read node_name in
	schedule_finalize_task (Hashtbl.find env.tasks task_fd)
      | Unix_error (err, fn, _) ->
	eprintf "respond: error for node %s: %s\n" (A.serializeName node_name) (error_message err);
	let task_fd = Hashtbl.find env.node_fds_read node_name in
	schedule_finalize_task (Hashtbl.find env.tasks task_fd)
    in
    List.iter (output env) os;
    List.iter go ps;
    s

  (* throws nothing *)
  let deliver_msg env state src msg : A.state =
    let state' = respond env (A.handleNet env.me src msg state) in
    if A.debug then A.debugRecv state' (src, msg);
    state'

  (* throws Disconnect, Unix_error *)
  let recv_step (env : env) (fd : file_descr) (state : A.state) : A.state =
    let buf = receive_chunk env fd in
    let src =
      try undenote_node env fd
      with Not_found -> failwith "recv_step: failed to find source for message"
    in
    let msg = A.deserializeMsg buf in
    deliver_msg env state src msg

  (* throws Disconnect, Unix_error *)
  let input_step (fd : file_descr) (env : env) (state : A.state) =
    let buf = receive_chunk env fd in
    let c = undenote_client env fd in
    match A.deserializeInput buf c with
    | Some inp ->
      let state' = respond env (A.handleIO env.me inp state) in
      if A.debug then A.debugInput state' inp;
      state'
    | None ->
      raise (Disconnect (sprintf "input_step: could not deserialize %s" buf))

  let node_read_task fd =
    { fd = fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let state' = recv_step env t.fd state in
	    (false, [], state')
	  with 
	  | Disconnect s ->
	    eprintf "connection error for node %s: %s\n" (A.serializeName (undenote_node env t.fd)) s;
	    (true, [], state)
	  | Unix_error (err, fn, _) ->
	    eprintf "error for node %s: %s\n" (A.serializeName (undenote_node env t.fd)) (error_message err);
	    (true, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize =
	(fun t env state ->
	  let read_fd = t.fd in
	  let node_name = undenote_node env read_fd in
	  let write_fd = denote_node env node_name in (* assumed to never throw Not_found *)
	  if A.debug then printf "[%s] closing connections for node %s\n" (timestamp ()) (A.serializeName node_name);
	  Hashtbl.remove env.node_read_fds read_fd;
	  Hashtbl.remove env.node_fds_read node_name;
	  Hashtbl.remove env.node_write_fds node_name;
	  Hashtbl.remove env.cluster node_name;
	  Unix.close read_fd;
	  Unix.close write_fd;
	  match A.failMsg with
          | None -> state
          | Some m -> deliver_msg env state node_name m)
    }

  let client_read_task fd =
    { fd = fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let state' = input_step t.fd env state in
	    (false, [], state')
	  with 
	  | Disconnect s ->
	    eprintf "connection error for client %s: %s\n" (A.serializeClientId (undenote_client env t.fd)) s;
	    (true, [], state)
	  | Unix_error (err, fn, _) ->
	    eprintf "error for client %s: %s\n" (A.serializeClientId (undenote_client env t.fd)) (error_message err);
	    (true, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize =
	(fun t env state ->
	  let client_fd = t.fd in
	  let c = undenote_client env client_fd in
	  if A.debug then printf "[%s] closing connection to client %s" (timestamp ()) (A.serializeClientId c);
	  Hashtbl.remove env.client_read_fds client_fd;
	  Hashtbl.remove env.client_write_fds c;
	  Unix.close client_fd;
	  state)
    }

  let connect_to_nodes_task env =
    { fd = Unix.dup env.nodes_fd
      ; select_on = false
      ; wake_time = Some 1.0
      ; process_read = (fun t env state -> (false, [], state))
      ; process_wake =
	  (fun t env state ->
	    connect_to_nodes env;
	    t.wake_time <- Some 1.0;
	    (false, [], state))
      ; finalize = (fun t env state -> Unix.close t.fd; state)
      }

  let node_connections_task env =
    { fd = env.nodes_fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let node_fd = new_node_conn env in
	    let state' =
	      match A.newMsg with
	      | None -> state
              | Some m -> deliver_msg env state (Hashtbl.find env.node_read_fds node_fd) m
	    in
	    (false, [node_read_task node_fd], state')
	  with Disconnect s ->
	    eprintf "incoming node connection error: %s\n" s;
	    (false, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize = (fun t env state -> Unix.close t.fd; state)
    }

  let client_connections_task env =
    { fd = env.clients_fd
    ; select_on = true
    ; wake_time = None
    ; process_read =
	(fun t env state ->
	  try
	    let client_fd = new_client_conn env in
	    (false, [client_read_task client_fd], state)
	  with Unix_error (err, fn, _) ->
	    eprintf "incoming client connection error in %s: %s\n" fn (error_message err);
	    (false, [], state))
    ; process_wake = (fun t env state -> (false, [], state))
    ; finalize = (fun t env state -> Unix.close t.fd; state)
    }

  let timeout_task env curr_state handler setter =
    { fd = Unix.dup env.clients_fd
    ; select_on = false
    ; wake_time = Some (setter env.me curr_state)
    ; process_read = (fun t env state -> (false, [], state))
    ; process_wake =
	(fun t env state ->
	  let state' = respond env (handler env.me state) in
	  t.wake_time <- Some (setter env.me state');
	  (false, [], state'))
    ; finalize = (fun t env state -> Unix.close t.fd; state)
    }
 
  let main (cfg : cfg) : unit =
    printf "ordered shim running setup for %s\n" A.systemName;
    let (env, initial_state) = setup cfg in
    let t_conn_nd = connect_to_nodes_task env in
    let t_nd_conn = node_connections_task env in
    let t_cl_conn = client_connections_task env in
    Hashtbl.add env.tasks t_conn_nd.fd t_conn_nd;
    Hashtbl.add env.tasks t_nd_conn.fd t_nd_conn;
    Hashtbl.add env.tasks t_cl_conn.fd t_cl_conn;
    List.iter (fun (h, s) ->
      let t = timeout_task env initial_state h s in
      Hashtbl.add env.tasks t.fd t) A.timeoutTasks;
    printf "ordered shim ready for action\n";
    eloop 2.0 (Unix.gettimeofday ()) env.tasks env initial_state
end
