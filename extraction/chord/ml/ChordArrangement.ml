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

let show_pointer p =
  string_of_int (ExtractedChord.id_of p)

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

let show_st_id st =
  string_of_int (ExtractedChord.id_of (ExtractedChord.ptr st))

let show_st st = 
  let prefix = "node(" ^ show_st_id st ^ "):" in
  let log msg = info (prefix ^ msg) in
  log ("succ_list := " ^ show_pointer_list (ExtractedChord.succ_list st));
  log ("pred := " ^ show_opt_pointer (ExtractedChord.pred st))

let log_recv src msg =
  dbg ("recv at " ^ show_addr src ^ ": " ^ show_msg msg)

let log_send dst msg =
  dbg ("send from " ^ show_addr dst ^ ":" ^ show_msg msg)

module ChordDebugArrangement = struct
  type name = ExtractedChord.addr
  type state = ExtractedChord.data
  type msg = ExtractedChord.payload
  type res = state * (name * msg) list
  (* should I put these two fns in coq *)
  let addr_of_name n =
      ("127.0.0.1", n)
  let name_of_addr (s, p) =
      p
  let is_request = ExtractedChord.is_request
  let handleNet = ExtractedChord.recv_handler
  let handleTick = ExtractedChord.tick_handler
  let handleTimeout = ExtractedChord.timeout_handler
  let setTick n s = 5.0
  let debug = true
  let debugInit n knowns = dbg "running init"
  let debugRecv st (src, msg) = show_st st; log_recv src msg
  let debugSend st (dst, msg) = show_st st; log_send dst msg
  let debugTick st = show_st st
  let init = ExtractedChord.start_handler
end
