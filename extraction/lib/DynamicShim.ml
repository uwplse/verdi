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
    {
      listen_sock : Unix.file_descr;
      conns : (A.name, Unix.file_descr) Hashtbl.t;
      mutable last_tick : float
    }

  let values_of_hashtbl h =
    let add_value_to_list _ v l = v :: l in
    Hashtbl.fold add_value_to_list h []

  let socks_in_env env =
    values_of_hashtbl env.conns @ [env.listen_sock]

  let pack_msg buf =
    M.to_string buf []

  let unpack_msg buf : A.msg =
    M.from_string buf 0

  let mk_addr_inet nm =
    let ip, port = A.addr_of_name nm in
    try
      print_endline (sprintf "mk_addr_inet \"%s\" %d = %d" ip port (Obj.magic (Unix.inet_addr_of_string ip)));
      Unix.ADDR_INET ((Unix.inet_addr_of_string ip), port)
    with
      Unix.Unix_error (a, b, c) -> print_endline (sprintf "Could not make addr inet for %s:%d" ip port);
                                   raise (Unix.Unix_error (a, b, c))

  let setup nm =
    Random.self_init ();
    Hashtbl.randomize ();
    let env =
      { listen_sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0;
        conns = Hashtbl.create 256;
        last_tick = Unix.gettimeofday ()
      }
    in
    (try
      Unix.setsockopt env.listen_sock Unix.SO_REUSEADDR true;
      Unix.bind env.listen_sock (mk_addr_inet nm);
      Unix.listen env.listen_sock 20;
    with Unix.Unix_error (errno, fn, arg) ->
       print_endline (sprintf "could not listen at port %d: %s(%s): %s"
                              8000 fn arg (Unix.error_message errno)));
    env

  let connect_to nm =
    let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.connect sock (mk_addr_inet nm);
    sock

  let send_all sock buf =
    let rec send_chunk sock buf i l =
      let sent = Unix.send sock buf i l [] in
      if sent < l
      then send_chunk sock buf (i + sent) (l - sent)
      else () in
    send_chunk sock buf 0 (String.length buf)

  let rec find_conn_and_send_all env nm buf =
    if Hashtbl.mem env.conns nm
    then (print_endline (sprintf "already have a connection to %d" (Obj.magic nm));
          let conn = Hashtbl.find env.conns nm in
          try send_all conn buf
          with Unix.Unix_error _ ->
            (* remove this connection and try again *)
            Hashtbl.remove env.conns nm;
            find_conn_and_send_all env nm buf)
    else try (let conn = connect_to nm in
              print_endline (sprintf "successfully connected to %d: fd = %d" (Obj.magic nm) (Obj.magic conn));
              send_all (connect_to nm) buf;
              Hashtbl.add env.conns nm conn)
         with Unix.Unix_error (errno, fn, arg) ->
            print_endline (sprintf "could not connect to %d: %s(%s): %s"
                                   (Obj.magic nm) fn arg (Unix.error_message errno))

  let send env ((nm : A.name), (msg : A.msg)) =
    let serialized = pack_msg msg in
    find_conn_and_send_all env nm serialized

  let respond_one env s p =
    (if A.debug then A.debugSend s p);
    send env p

  let add_time t =
    let now = Unix.gettimeofday () in
    (now +. A.setTimeout t, t)

  let respond env ts (s, ps, newts, clearedts) =
    let ts' = (List.filter (fun (_, t) -> not (List.mem t clearedts))
                           ts)
              @ (List.map add_time newts) in
    List.iter (respond_one env s) ps;
    s, ts'

  let ensure_conn_shutdown env nm =
    print_endline "killing connection";
    try
      Unix.shutdown (Hashtbl.find env.conns nm) Unix.SHUTDOWN_ALL
    with
    | Not_found -> ()
    | Unix.Unix_error (errno, fn, arg) ->
       print_endline (sprintf "could not shut down %d: %s(%s): %s"
                              (Obj.magic nm) fn arg (Unix.error_message errno))

  let switch_to_conn env nm sock =
    if Hashtbl.mem env.conns nm
    then if Hashtbl.find env.conns nm = sock
         then ()
         else (ensure_conn_shutdown env nm;
               Hashtbl.replace env.conns nm sock)
    else Hashtbl.add env.conns nm sock

  let sockaddr_to_name =
    function
    | Unix.ADDR_UNIX _ -> failwith "UNEXPECTED MESSAGE FROM UNIX ADDR"
    | Unix.ADDR_INET (addr, port) -> A.name_of_addr (Unix.string_of_inet_addr addr, port)

  let recv_all sock =
    let rec aux bufs =
      let len = 4096 in
      let buf = String.make len '\x00' in
      try 
        let count = Unix.recv sock buf 0 len [] in
        if count = 0
        then bufs
        else aux bufs @ [buf]
      with Unix.Unix_error _ ->
        bufs in
    String.concat "" (aux [])

  let recv_step env nm s ts sock =
    let buf = recv_all sock in
    let src = sockaddr_to_name (Unix.getpeername sock) in
    switch_to_conn env src sock;
    let m = unpack_msg buf in
    let (s', ts') = respond env ts (A.handleNet src nm s m) in
    (if A.debug then A.debugRecv s' (src, m));
    s', ts'

  let rec my_select rs ws es t =
    try Unix.select rs ws es t
    with Unix.Unix_error (err, fn, arg) ->
      my_select rs ws es t

  let rec uniqappend l =
    function
    | [] -> l
    | (h :: rest) -> if List.mem h l
                     then uniqappend l rest
                     else uniqappend (l @ [h]) rest

  let do_timeout env nm (s, sends, newts, clearedts) (deadline, t) =
    if not (List.mem t clearedts)
    then let (s', sends', newts', clearedts') = (A.handleTimeout nm s t) in
         (if A.debug then A.debugTimeout s' t);
         (s', sends @ sends', newts @ newts', uniqappend clearedts clearedts')
    else (s, sends, newts, clearedts)
    
  let timeout_step env nm s ts =
    let now = Unix.gettimeofday () in
    let live = List.filter (fun (d, _) -> now > d) ts in
    let (s, sends, newts, clearedts) = List.fold_left (do_timeout env nm) (s, [], [], []) live in
    respond env ts (s, sends, newts, uniqappend clearedts (List.map snd live))

  let min_of_list default l =
    List.fold_left (fun acc x -> min acc x) default l

  let free_time ts =
    let now = Unix.gettimeofday () in
    max A.default_timeout ((min_of_list now (List.map fst ts)) -. now)

  let accept_connection env =
    let conn, sa = Unix.accept env.listen_sock in
    switch_to_conn env (sockaddr_to_name sa) conn

  let rec eloop env nm (s, ts) =
    let (fds, _, _) = my_select (socks_in_env env) [] [] (free_time ts) in
    printf "%d: %d fds open\n" (Obj.magic nm) (List.length fds);
    let (s', ts') = if List.length fds > 0
                    then if List.hd fds = env.listen_sock
                         then (accept_connection env; (s, ts))
                         else recv_step env nm s ts (List.hd fds)
                    else (s, ts) in
    let (s'', ts'') = timeout_step env nm s' ts' in
    eloop env nm (s'', ts'')

  let default v o =
    match o with
    | None -> v
    | Some v' -> v'

  let init nm knowns =
    let (st, sends, nts) = A.init nm knowns in
    (st, sends, nts, [])

  let main nm knowns =
    let env = setup nm in
    print_endline "starting";
    eloop env nm (respond env [] (init nm knowns));
end
