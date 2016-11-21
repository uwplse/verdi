open ExtractedChord
open Printf
open Str
(* open Random *)

let chord_port = 8000

let log level s =
  let now = Unix.gettimeofday () in
  print_float now;
  print_string " - ";
  print_string level;
  print_string ":";
  print_endline s

let dbg = log "DEBUG"

let info = log "INFO"

let octets_to_ip o1 o2 o3 o4 =
  o1 lsl 24 + o2 lsl 16 + o3 lsl 8 + o4

let weak_ip_regexp =
  regexp "\\([0-9]?[0-9]?[0-9]\\)\\.\
          \\([0-9]?[0-9]?[0-9]\\)\\.\
          \\([0-9]?[0-9]?[0-9]\\)\\.\
          \\([0-9]?[0-9]?[0-9]\\)$"

let int_of_ip s =
  if string_match weak_ip_regexp s 0
  then
    let int_of_kth_group k = int_of_string (matched_group k s) in
    let numbers = map int_of_kth_group [1; 2; 3; 4] in
    match numbers with
    | [o1; o2; o3; o4] ->
       if List.for_all (fun x -> 0 <= x && x <= 255) numbers
       then octets_to_ip o1 o2 o3 o4
       else invalid_arg s
    | _ -> invalid_arg s
  else invalid_arg s

let ip_of_int i =
  if i > 1 lsl 32
  then invalid_arg (string_of_int i)
  else let octets = [(i land (1 lsl 32 - 1 lsl 24)) lsr 24;
                     (i land (1 lsl 24 - 1 lsl 16)) lsr 16;
                     (i land (1 lsl 16 - 1 lsl 8)) lsr 8;
                     i land (1 lsl 8 - 1)] in
       String.concat "." (map string_of_int octets)

let show_addr a =
  ip_of_int a

let caps_bool b =
  if b then "True" else "False"

let show_pointer p =
  string_of_int (id_of p)

let show_pointer_list ps =
  let strs = map show_pointer ps in
  "[" ^ String.concat ", " strs ^ "]"

let map_default f d = function
  | None -> d
  | Some v -> f v

let show_opt_pointer p =
  map_default show_pointer "None" p

let show_msg = function
  | GetBestPredecessor p -> "GetBestPredecessor " ^ show_pointer p
  | GotBestPredecessor p -> "GotBestPredecessor " ^ show_pointer p
  | GetSuccList -> "GetSuccList"
  | GotSuccList ps -> "GotSuccList " ^ show_pointer_list ps
  | GetPredAndSuccs -> "GetPredAndSuccs"
  | GotPredAndSuccs (pred, succs) -> "GotPredAndSuccs " ^ show_opt_pointer pred ^ " " ^ show_pointer_list succs
  | Notify -> "Notify"
  | Ping -> "Ping"
  | Pong -> "Pong"
  | Busy -> "Busy"

let show_query = function
  | Rectify p -> "Rectify " ^ show_pointer p
  | Stabilize -> "Stabilize"
  | Stabilize2 p -> "Stabilize2 " ^ show_pointer p
  | Join p -> "Join " ^ show_pointer p
  | Join2 p -> "Join2 " ^ show_pointer p

let show_st_ptr st =
  show_pointer (ptr st)

let show_request ((ptr, q), _) =
  "query(" ^ show_pointer ptr ^ ", " ^ show_query q ^ ")"

let show_st_cur_request st =
  map_default show_request "None" (cur_request st)

let log_st st =
  let prefix = "node(" ^ show_st_ptr st ^ "):" in
  let log msg = info (prefix ^ msg) in
  log ("succ_list := " ^ show_pointer_list (succ_list st));
  log ("pred := " ^ show_opt_pointer (pred st));
  log ("known := " ^ show_pointer (known st));
  log ("joined := " ^ caps_bool (joined st));
  log ("rectify_with := " ^ show_opt_pointer (rectify_with st));
  log ("cur_request := " ^ show_st_cur_request st)

let log_recv st src msg =
  let prefix = "node(" ^ show_st_ptr st ^ "):" in
  let log msg = dbg (prefix ^ msg) in
  log ("recv from " ^ show_addr src ^ ": " ^ show_msg msg)

let log_send st dst msg =
  let prefix = "node(" ^ show_st_ptr st ^ "):" in
  let log msg = dbg (prefix ^ msg) in
  log ("send to " ^ show_addr dst ^ ":" ^ show_msg msg)

let log_timeout st = function
  | Tick -> dbg ("ticked")
  | KeepaliveTick -> dbg ("ticked for keepalive")
  | Request (dead, msg) ->
    dbg ("request " ^ show_msg msg
        ^ " from " ^ show_pointer (ptr st)
        ^ " to " ^ show_addr dead ^ " timed out")

let set_timeout = function
  | Tick -> 0.0 +. Random.float 10.0
  (* must be less than the request timeout *)
  | KeepaliveTick -> 0.0 +. Random.float 10.0
  | Request (a, b) -> 20.0

let rebracket4 (((a, b), c), d) = (a, b, c, d)
let rebracket3 ((a, b), c) = (a, b, c)

module ChordDebugArrangement = struct
  type name = addr
  type state = data
  type msg = payload
  type timeout = ExtractedChord.timeout
  type res = state * (name * msg) list * (timeout list) * (timeout list)
  let addr_of_name n =
    (ip_of_int n, chord_port)
  let name_of_addr (s, p) =
    int_of_ip s
  let init n ks =
    rebracket3 (init n ks)
  let handleNet s d m st =
    rebracket4 (handleNet s d m st)
  let handleTimeout n s t =
    rebracket4 (handleTimeout n s t)
  let setTimeout = set_timeout
  let default_timeout = 5.0
  let debug = true
  let debugRecv st (src, msg) = log_st st; log_recv st src msg
  let debugSend st (dst, msg) = log_st st; log_send st dst msg
  let debugTimeout st t = log_timeout st t
  let showTimeout = function
      | Tick -> "Tick"
      | KeepaliveTick -> "KeepaliveTick"
      | Request (dead, msg) ->
        "Request(" ^ show_addr dead ^ ", " ^ show_msg msg ^ ")"
end
