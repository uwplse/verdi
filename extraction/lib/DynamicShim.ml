open Printf
open Unix
open Sys

module M = Marshal

module type DYNAMIC_ARRANGEMENT = sig
  type name
  type state
  type msg
  type res = state * (name * msg) list
  val addr_of_name : name -> (string * int)
  val name_of_addr : (string * int) -> name
  val is_request : msg -> bool
  val closes_request : msg -> msg -> bool
  val init : name -> name list -> res
  val handleNet : name -> name -> msg -> state -> res
  val handleTick : name -> state -> res
  val handleTimeout : name -> name -> state -> res
  val setTick : name -> state -> float
  val query_timeout : float
  val debug : bool
  val debugRecv : state -> (name * msg) -> unit
  val debugSend : state -> (name * msg) -> unit
  val debugTick : state -> unit
  val debugTimeout : state -> (name * msg) -> unit
end
module Shim (A: DYNAMIC_ARRANGEMENT) = struct
  (* assoc list of start times mapping to (name, msg) pairs *)

  type requests = (float * A.name * A.msg) list

  let empty_requests = []

  let rec timed_out_requests timeout ts : (A.name * A.msg) list =
    let now = Unix.gettimeofday () in
    match ts with
    | (t, dst, msg) :: rest ->
       if now -. t > timeout
       then (dst, msg) :: timed_out_requests timeout rest
       else timed_out_requests timeout rest
    | [] -> []

  let rec record_request rs (dst, msg) : requests =
    if A.is_request msg
    then (Unix.gettimeofday (), dst, msg) :: rs
    else rs

  let remove_requests rs dst : requests =
    List.filter (fun (_, d, _) -> d == dst) rs

  type env =
    {
      usock : file_descr;
      mutable open_requests : requests;
      mutable last_tick : float
    }

  let setup nm =
    Random.self_init ();
    let port = snd (A.addr_of_name nm) in
    let env =
      { usock = socket PF_INET SOCK_DGRAM 0;
        open_requests = empty_requests;
        last_tick = Unix.gettimeofday ()
      }
    in
    setsockopt env.usock SO_REUSEADDR true;
    bind env.usock (ADDR_INET (inet_addr_any, port));
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
    env.open_requests <- record_request env.open_requests p;
    send env p

  let respond env (s, ps) =
    List.iter (respond_one env s) ps; s

  let close_requests env src res =
    let closed (_, nm, req) = A.closes_request req res in
    List.filter closed env.open_requests

  let recv_step env nm s =
    let len = 4096 in
    let buf = String.make len '\x00' in
    let (_, from) = recvfrom env.usock buf 0 len [] in
    let src =
    (match from with
     | ADDR_UNIX _ -> failwith "UNEXPECTED MESSAGE FROM UNIX ADDR"
     | ADDR_INET (addr,port) -> A.name_of_addr (string_of_inet_addr addr, port)) in
    let m = unpack_msg buf in
    let s' = respond env (A.handleNet src nm m s) in
    (if A.debug then A.debugRecv s' (src, m));
    env.open_requests <- close_requests env src m;
    s'

  let tick_step env nm s =
    (if A.debug then A.debugTick s);
    env.last_tick <- Unix.gettimeofday ();
    let x = A.handleTick nm s in
    respond env x

  let do_timeout env nm (s, sends) (dst, msg) =
    let (s', sends') = A.handleTimeout nm dst s in
    env.open_requests <- remove_requests env.open_requests dst;
    A.debugTimeout s (dst, msg);
    (s', sends @ sends')

  let timeout_step env nm s =
    let timeouts = timed_out_requests A.query_timeout env.open_requests in
    let res = List.fold_left (do_timeout env nm) (s, []) timeouts in
    respond env res

  let maybe_tick env nm s =
    if (Unix.gettimeofday ()) -. env.last_tick > A.setTick nm s
    then tick_step env nm s
    else s

  let rec my_select rs ws es t =
    try select rs ws es t
    with Unix_error (err, fn, arg) ->
      my_select rs ws es t

  let rec eloop env nm s =
    let (fds, _, _) = my_select [env.usock] [] [] (A.setTick nm s) in
    let s' = if List.mem env.usock fds
             then (try (recv_step env nm s) with
                   | _ -> s)
             else s in
    let s'' = timeout_step env nm s' in
    let s''' = maybe_tick env nm s'' in
    eloop env nm s'''

  let default v o =
    match o with
    | None -> v
    | Some v' -> v'

  let main nm knowns =
    print_endline "running setup";
    let env = setup nm in
    print_endline "starting";
    eloop env nm (respond env (A.init nm knowns));
end
