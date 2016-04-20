open ExtractedChord
open Printf

let log level s =
  print_string level;
  print_string ":";
  print_string s;
  print_newline ()

let dbg = log "DEBUG"

let info = log "INFO"

let show_addr a =
  string_of_int a

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

let show_query = function
  | Rectify p -> "Rectify " ^ show_pointer p
  | Stabilize -> "Stabilize"
  | Stabilize2 p -> "Stabilize2 " ^ show_pointer p
  | Join p -> "Join " ^ show_pointer p
  | Join2 p -> "Join2 " ^ show_pointer p

let show_st_ptr st =
  show_pointer (ExtractedChord.ptr st)

let show_request (ptr, q) =
  "query(" ^ show_pointer ptr ^ ", " ^ show_query q ^")"

let show_st_cur_request st =
  map_default show_request "None" (ExtractedChord.cur_request st)

let log_st st =
  let prefix = "node(" ^ show_st_ptr st ^ "):" in
  let log msg = info (prefix ^ msg) in
  log ("succ_list := " ^ show_pointer_list (ExtractedChord.succ_list st));
  log ("pred := " ^ show_opt_pointer (ExtractedChord.pred st));
  log ("known := " ^ show_pointer (ExtractedChord.known st));
  log ("joined := " ^ caps_bool (ExtractedChord.joined st));
  log ("rectify_with := " ^ show_opt_pointer (ExtractedChord.rectify_with st));
  log ("cur_request := " ^ show_st_cur_request st);
  log ("query_sent := " ^ caps_bool (ExtractedChord.query_sent st))

let log_recv src msg =
  dbg ("recv from " ^ show_addr src ^ ": " ^ show_msg msg)

let log_send dst msg =
  dbg ("send to " ^ show_addr dst ^ ":" ^ show_msg msg)

let log_timeout st (dead, msg) =
  dbg ("request " ^ show_msg msg
     ^ " from " ^ show_pointer (ptr st)
     ^ " to " ^ show_addr dead ^ " timed out")

module ChordDebugArrangement = struct
  type name = ExtractedChord.addr
  type state = ExtractedChord.data
  type msg = ExtractedChord.payload
  type res = state * (name * msg) list
  (* should put these two in coq so i can prove (name_of_addr (addr_of_name n)) = n *)
  let addr_of_name n =
      ("127.0.0.1", n)
  let name_of_addr (s, p) =
      p
  let is_request = ExtractedChord.is_request
  let handleNet = ExtractedChord.recv_handler
  let handleTick = ExtractedChord.tick_handler
  let handleTimeout = ExtractedChord.timeout_handler
  let closes_request = ExtractedChord.closes_request
  let setTick n s = 5.0
  let query_timeout = 10.0
  let debug = true
  let debugInit n knowns = dbg "running init"
  let debugRecv st (src, msg) = log_st st; log_recv src msg
  let debugSend st (dst, msg) = log_st st; log_send dst msg
  let debugTick st = log_st st; dbg "ticking"
  let debugTimeout st t = log_timeout st t
  let init = ExtractedChord.start_handler
end
