open Printf
open Unix

module M = Marshal
               
module type DYNAMIC_ARRANGEMENT = sig
  type name
  type state
  type msg
  type res = state * (name * msg) list
  val addr_of_name : name -> (string * int)
  val name_of_addr : (string * int) -> name
  val init : name -> res
  val handleNet : name -> name -> msg -> state -> res
  val handleTimeout : name -> state -> res
  val setTimeout : name -> state -> float
  val debug : bool
  val debugRecv : state -> (name * msg) -> unit
  val debugSend : state -> (name * msg) -> unit
  val debugTimeout : state -> unit
end

module Shim (A: DYNAMIC_ARRANGEMENT) = struct
  type env =
    {
      usock : file_descr
    }

  let setup nm =
    Random.self_init ();
    let port = snd (A.addr_of_name nm) in
    let env =
      { usock = socket PF_INET SOCK_DGRAM 0
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

  let respond env (s, ps) =
    List.iter (fun p -> (if A.debug then A.debugSend s p); send env p) ps;
    s
    
  let recv_step env nm s =
    let len = 4096 in
    let buf = String.make len '\x00' in
    let (_, from) = recvfrom env.usock buf 0 len [] in
    let src =
    (match from with
     | ADDR_UNIX _ -> failwith "TODO"
     | ADDR_INET (addr,port) -> A.name_of_addr (string_of_inet_addr addr, port)) in
    let m = unpack_msg buf in
    let s' = respond env (A.handleNet nm src m s) in
    (if A.debug then A.debugRecv s' (src, m)); s'

  let timeout_step env nm s =
    (if A.debug then A.debugTimeout s);
    let x = A.handleTimeout nm s in
    respond env x

  let rec my_select rs ws es t =
    try select rs ws es t
    with Unix_error (err, fn, arg) ->
      my_select rs ws es t

  let rec eloop env nm s =
    let (fds, _, _) = my_select [env.usock] [] [] (A.setTimeout nm s) in
    let s' =
      match List.mem env.usock fds with
      | true -> recv_step env nm s
      | _ -> timeout_step env nm s in
    eloop env nm s'

  let default v o =
    match o with
    | None -> v
    | Some v' -> v'

  let main nm nodes =
    print_endline "running setup";
    let env = setup nm in
    print_endline "starting";
    eloop env nm (respond env (A.init nm))
end
