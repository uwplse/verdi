open Printf
open Sys

module M = Marshal

module type DYNAMIC_ARRANGEMENT = sig
  type name
  type state
  type msg
  type timeout
  type res = state * (name * msg) list * timeout list * timeout list
  val addr_of_name : name -> (string * int)
  val name_of_addr : (string * int) -> name
  val init : name -> name list -> state * (name * msg) list * timeout list
  val handleNet : name -> name -> state -> msg -> res
  val handleTimeout : name -> state -> timeout -> res
  val setTimeout : timeout -> float
  val default_timeout : float
  val debug : bool
  val debugRecv : state -> (name * msg) -> unit
  val debugSend : state -> (name * msg) -> unit
  val debugTimeout : state -> timeout -> unit
end
module Shim (A: DYNAMIC_ARRANGEMENT) = struct
  type env =
    { listen_sock : Unix.file_descr
    ; recv_conns : (Unix.file_descr, A.name) Hashtbl.t
    ; send_conns : (A.name, Unix.file_descr) Hashtbl.t
    ; mutable last_tick : float
    }

  let unpack_msg buf : A.msg =
    M.from_string buf 0

  let keys_of_hashtbl h =
    let add_value_to_list k _ l = k :: l in
    Hashtbl.fold add_value_to_list h []

  let recv_fds env =
    keys_of_hashtbl (env.recv_conns)

  let readable_socks_in_env env =
    env.listen_sock :: keys_of_hashtbl env.recv_conns

  let mk_addr_inet nm =
    let ip, port = A.addr_of_name nm in
    Unix.ADDR_INET ((Unix.inet_addr_of_string ip), port)

  let setup nm =
    Random.self_init ();
    Hashtbl.randomize ();
    let env =
      { listen_sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0
      ; recv_conns = Hashtbl.create 64
      ; send_conns = Hashtbl.create 64
      ; last_tick = Unix.gettimeofday ()
      }
    in
    Unix.setsockopt env.listen_sock Unix.SO_REUSEADDR true;
    Unix.bind env.listen_sock (mk_addr_inet nm);
    Unix.listen env.listen_sock 20;
    env

  let connect_to nm =
    let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.connect sock (mk_addr_inet nm);
    sock

  let send_all sock buf =
    let rec send_chunk sock buf i l =
      print_endline (sprintf "sending %d bytes..." l);
      let sent = Unix.send sock buf i l [] in
      if sent < l
      then send_chunk sock buf (i + sent) (l - sent)
      else () in
    send_chunk sock buf 0 (String.length buf);
    print_endline "sent buf successfully"

  let rec find_conn_and_send_all env nm buf =
    print_endline "entering find_conn_and_send_all";
    if Hashtbl.mem env.send_conns nm
    then 
      let conn = Hashtbl.find env.send_conns nm in
      try
        send_all conn buf;
        print_endline "sent buf successfully"
      with Unix.Unix_error (errno, fn, arg) ->
        print_endline "couldn't send ... reconnecting";
        (* close this connection and try again *)
        Hashtbl.remove env.send_conns nm;
        find_conn_and_send_all env nm buf
    else
      try
        print_endline (sprintf "connecting to %s" (fst (A.addr_of_name nm)));
        let conn = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
        Unix.connect conn (mk_addr_inet nm);
        print_endline (sprintf "connected to %s" (fst (A.addr_of_name nm)));
        send_all conn buf;
        Hashtbl.replace env.send_conns nm conn
      with Unix.Unix_error (errno, fn, arg) ->
        (* this should do something different if errno = EAGAIN, etc *)
        print_endline (sprintf "find_conn_and_send_all: %s(%s): %s" fn arg (Unix.error_message errno))

  let send env ((nm : A.name), (msg : A.msg)) =
    let serialized = M.to_string msg [] in
    find_conn_and_send_all env nm serialized

  let respond_one env s p =
    (if A.debug then A.debugSend s p);
    send env p

  let filter_cleared clearedts ts =
    let not_cleared (_, t) = not (List.mem t clearedts) in
    List.filter not_cleared ts

  let add_times ts =
    let now = Unix.gettimeofday () in
    let add_time t = (now +. A.setTimeout t, t) in
    List.map add_time ts

  let respond env ts (s, ps, newts, clearedts) =
    let ts' = filter_cleared clearedts ts @ add_times newts in
    List.iter (respond_one env s) ps;
    s, ts'

  let ensure_conn_shutdown env nm =
    print_endline "killing connection";
    try
      Unix.shutdown (Hashtbl.find env.send_conns nm) Unix.SHUTDOWN_ALL
    with
    | Not_found -> ()
    | Unix.Unix_error (errno, fn, arg) ->
       print_endline (sprintf "could not shut down %d: %s(%s): %s"
                              (Obj.magic nm) fn arg (Unix.error_message errno))

  let sockaddr_to_name =
    function
    | Unix.ADDR_UNIX _ -> failwith "UNEXPECTED MESSAGE FROM UNIX ADDR"
    | Unix.ADDR_INET (addr, port) -> A.name_of_addr (Unix.string_of_inet_addr addr, port)

  (* Read exactly len bytes from sock.
     Return (Some buf), where buf has length len, if everything works.
     Return None otherwise. *)
  let rec recv_len sock len =
    print_endline (sprintf "trying to read %d bytes" len);
    if len == 0
    then Some ""
    else 
      let buf = String.make len '\x00' in
      try 
        let count = Unix.recv sock buf 0 len [] in
        print_endline (sprintf "got %d bytes" count);
        if count == 0
        then None
        else
          if count < len
          then
            match recv_len sock (len - count) with 
            | Some buf' -> Some (buf ^ buf')
            | None -> None
          else Some buf
      with Unix.Unix_error (errno, fn, arg) ->
        print_endline (sprintf "%s(%s): %s" fn arg (Unix.error_message errno));
        None

  let read_and_unpack sock : A.msg option =
    let read = recv_len sock in
    let explode s =
      let rec exp i l =
        if i < 0 then l else exp (i - 1) (s.[i] :: l) in
      exp (String.length s - 1) [] in
    match read M.header_size with
    | Some header ->
       print_endline "header:";
       (List.iter (fun c -> printf "%x " (Char.code c)) (explode header));
       print_endline "";
       let data_len = M.data_size header 0 in
       begin
         match read data_len with
         | Some body ->
            (print_endline (sprintf "%d" (String.length body)));
            (List.iter (fun c -> printf "%x " (Char.code c)) (explode (header ^ body))); print_endline "";
            (List.iter (fun c -> printf "%x " (Char.code c)) (explode (String.concat "" [header; body]))); print_endline "";
            Some (M.from_string (header ^ body) 0) 
         | None -> None
       end
    | None -> None

  let rec iterated_select rs t =
    try Unix.select rs [] [] t
    with Unix.Unix_error (errno, fn, arg) ->
      print_endline (sprintf "iterated_select: %s(%s): %s" fn arg (Unix.error_message errno));
      iterated_select rs t

  let rec uniqappend l =
    function
    | [] -> l
    | (h :: rest) ->
       if List.mem h l
       then uniqappend l rest
       else uniqappend (l @ [h]) rest

  let do_timeout env nm (s, sends, newts, clearedts) (deadline, t) =
    if not (List.mem t clearedts)
    then let (s', sends', newts', clearedts') = (A.handleTimeout nm s t) in
         (if A.debug then A.debugTimeout s' t);
         (s', sends @ sends', newts @ newts', uniqappend clearedts clearedts')
    else (s, sends, newts, clearedts)
    
  let timeout_step env nm s ts =
    print_endline "timeout_step";
    let now = Unix.gettimeofday () in
    let active = List.filter (fun (deadline, _) -> now > deadline) ts in
    let (s, sends, newts, clearedts) =
      List.fold_left (do_timeout env nm)
                     (s, [], [], [])
                     active in
    respond env ts (s, sends, newts, uniqappend clearedts (List.map snd active))

  let min_of_list default l =
    List.fold_left (fun acc x -> min acc x) default l

  let free_time ts =
    let now = Unix.gettimeofday () in
    max A.default_timeout ((min_of_list now (List.map fst ts)) -. now)

  let accept_connection env =
    let conn, sa = Unix.accept env.listen_sock in
    Hashtbl.add env.recv_conns conn (sockaddr_to_name sa)

  let send_connected_filter nm fd =
    try
      ignore (Unix.getpeername fd);
      Some fd
    with Unix.Unix_error (errno, fn, args) ->
      print_endline (sprintf "%s(%s): %s" fn args (Unix.error_message errno));
      None

  let recv_connected_filter fd nm =
    try
      ignore (Unix.getpeername fd);
      Some nm
    with Unix.Unix_error (errno, fn, args) ->
      print_endline (sprintf "%s(%s): %s" fn args (Unix.error_message errno));
      None

  let prune_conns env =
    Hashtbl.filter_map_inplace recv_connected_filter env.recv_conns;
    Hashtbl.filter_map_inplace send_connected_filter env.send_conns

  let recv_step env nm s ts sock =
    match read_and_unpack sock with
    | Some m ->
       print_endline (sprintf "successfully got a message %x" (Obj.magic m));
       let src = Hashtbl.find env.recv_conns sock in
       print_endline (sprintf "and it was from %s" (fst (A.addr_of_name src)));
       let (s', ts') = respond env ts (A.handleNet src nm s m) in
       (if A.debug then A.debugRecv s' (src, m));
       s', ts'
    | None ->
       let ip, port = A.addr_of_name (Hashtbl.find env.recv_conns sock) in
       printf "could not recv from node at %s:%d" ip port;
       s, ts

  let handle_readable_fds env nm s ts fds =
    if List.length fds > 0
    then
      if List.mem env.listen_sock fds
      then (print_endline "got new connection!"; accept_connection env; (s, ts))
      else recv_step env nm s ts (List.hd fds)
    else (s, ts)

  let rec eloop env nm (s, ts) =
    prune_conns env;
    let fds, _, _ = iterated_select (readable_socks_in_env env) (free_time ts) in
    let s', ts' = handle_readable_fds env nm s ts fds in
    let s'', ts'' = timeout_step env nm s' ts' in
    eloop env nm (s'', ts'')

  let default v o =
    match o with
    | None -> v
    | Some v' -> v'

  let init nm knowns =
    let (st, sends, nts) = A.init nm knowns in
    (st, sends, nts, [])

  let main nm knowns =
    let env = Unix.handle_unix_error setup nm in
    print_endline "starting";
    eloop env nm (respond env [] (init nm knowns));
end
