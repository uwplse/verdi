open ExtractedChord
open Printf

let log level s =
  print_string level;
  print_string ":";
  print_string s;
  print_newline ()

let dbg = log "DEBUG"

let info = log "INFO"

let show_pointer p =
  string_of_int (ExtractedChord.id_of p)

let show_st_id st =
  string_of_int (ExtractedChord.id_of (ExtractedChord.ptr st))

let map_default f d = function
  | None -> d
  | Some v -> f v

let show_pred st =
  let p = ExtractedChord.pred st in
  map_default show_pointer "None" p

let show_succ_list st =
  let strs = map show_pointer (ExtractedChord.succ_list st) in
  "[" ^ String.concat ", " strs ^ "]"

let show_st st = 
  let prefix = "node(" ^ show_st_id st ^ "):" in
  let strs = map show_pointer (ExtractedChord.succ_list st) in
  let log msg = info (prefix ^ msg) in
  log ("succ_list := [" ^ String.concat ", " strs ^ "]");
  log ("pred := " ^ show_pred st)

module ChordDebugArrangement = struct
  type name = ExtractedChord.addr
  type state = ExtractedChord.data
  type msg = ExtractedChord.payload
  type res = state * (name * msg) list
  let addr_of_name n =
      ("127.0.0.1", n)
  let name_of_addr (s, p) =
      p
  let handleNet = ExtractedChord.recv_handler
  let handleTimeout = ExtractedChord.tick_handler
  let setTimeout n s = 5.0
  let debug = true
  let debugInit n knowns = dbg "running init"
  let debugRecv st (src, msg) = show_st st
  let debugSend st (dst, msg) = show_st st
  let debugTimeout st = show_st st
  let init = ExtractedChord.start_handler
end
