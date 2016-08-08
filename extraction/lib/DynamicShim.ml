open Printf
open Unix
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
  (* assoc list of start times mapping to (name, msg) pairs *)

  type env =
    {
      usock : file_descr;
      mutable last_tick : float
    }

  let setup nm =
    Random.self_init ();
    let ip, port = A.addr_of_name nm in
    let env =
      { usock = socket PF_INET SOCK_DGRAM 0;
        last_tick = Unix.gettimeofday ()
      }
    in
    setsockopt env.usock SO_REUSEADDR true;
    bind env.usock (ADDR_INET ((inet_addr_of_string ip), port));
    env

  let sendto sock buf addr =
    ignore (Unix.sendto sock buf 0 (String.length buf) [] addr)

  let send env ((nm : A.name), (msg : A.msg)) =
    let (ip, port) = A.addr_of_name nm in
    sendto env.usock (M.to_string msg []) (ADDR_INET (inet_addr_of_string ip, port))

  let respond_to_client sock r =
    ignore (Unix.send sock (r ^ "\n") 0 (String.length r) [])

  let unpack_msg buf : A.msg =
    M.from_string buf 0

  let respond_one env s p =
    (if A.debug then A.debugSend s p);
    send env p

  let add_time t =
    let now = Unix.gettimeofday () in
    (now +. A.setTimeout t, t)

  let respond env ts (s, ps, newts, clearedts) =
    let ts' = (List.filter (fun (_, t) -> not (List.mem t clearedts)) ts)
              @ (List.map add_time newts) in
    List.iter (respond_one env s) ps;
    s, ts'

  let recv_step env nm s ts =
    let len = 4096 in
    let buf = String.make len '\x00' in
    let (_, from) = recvfrom env.usock buf 0 len [] in
    let src =
    (match from with
     | ADDR_UNIX _ -> failwith "UNEXPECTED MESSAGE FROM UNIX ADDR"
     | ADDR_INET (addr,port) -> A.name_of_addr (string_of_inet_addr addr, port)) in
    let m = unpack_msg buf in
    let (s', ts') = respond env ts (A.handleNet src nm s m) in
    (if A.debug then A.debugRecv s' (src, m));
    s', ts'

  let rec my_select rs ws es t =
    try select rs ws es t
    with Unix_error (err, fn, arg) ->
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

  let rec eloop env nm (s, ts) =
    let (fds, _, _) = my_select [env.usock] [] [] (free_time ts) in
    let (s', ts') = if List.mem env.usock fds
             then (try (recv_step env nm s ts) with
                   | _ -> (s, ts))
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
    print_endline "running setup";
    let env = setup nm in
    print_endline "starting";
    eloop env nm (respond env [] (init nm knowns));
end
