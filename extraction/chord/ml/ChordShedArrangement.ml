open Printf

open ExtractedChordShed

let show_pointer p =
  sprintf "(id=%d, addr=%d)" (id_of p) (addr_of p)

let show_list show_item l =
  sprintf "[%s]" (String.concat "; " (map show_item l))

let show_addr_list l =
  show_list string_of_int l

let show_pointer_list ps =
  let strs = map show_pointer ps in
  "[" ^ String.concat ", " strs ^ "]"

let map_default f d = function
  | None -> d
  | Some v -> f v

let show_opt_pointer p =
  map_default show_pointer "None" p

let show_payload = function
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

let show_timeout = function
  | Tick -> "Tick"
  | KeepaliveTick -> "KeepaliveTick"
  | Request (a, p) -> sprintf "Request %d %s" a (show_payload p)

let picki r l =
  let i = r (List.length l) in
  (i, List.nth l i)

let pick r l =
  snd (picki r l)

let pick_timeout gst r =
  let hosts = filter (fun h -> List.length (timeouts gst h) > 0)
                     (nodes gst) in
  let h = pick r hosts in
  let t = pick r (timeouts gst h) in
  Op_timeout (h, t)

let pick_msg gst r =
  let (i, m) = picki r (msgs gst) in
  Op_deliver (i, m)
(*
let plan_deliver_or_timeout gst _ r =
  if List.length (msgs gst) == 0
  then pick_timeout gst r
  else if r 10 == 0
  then pick_timeout gst r
  else pick_msg gst r
 *)
let init_nodes =
    [10;30;50;70;90]

let pred_for_init = function
  | 10 -> 90
  | 30 -> 10
  | 50 -> 30
  | 70 -> 50
  | 90 -> 70
  | _ -> 0

let succs_for_init = function
  | 10 -> [30;50]
  | 30 -> [50;70]
  | 50 -> [70;90]
  | 70 -> [90;10]
  | 90 -> [10;30]
  | _ -> []
let mp = make_pointer (fun a -> a mod 256)
let init_sigma h =
    if List.mem h init_nodes
    then Some ({ ptr = mp h
              ; pred = Some (mp (pred_for_init h))
              ; succ_list = map mp (succs_for_init h)
              ; known = (mp (pred_for_init h))
              ; joined = true
              ; rectify_with = None
              ; cur_request = None
              ; delayed_queries = [] })
    else None

let init_timeouts h =
  if List.mem h init_nodes
  then [Tick]
  else []

let init =
    { nodes = init_nodes
    ; failed_nodes = []
    ; timeouts = init_timeouts
    ; sigma = init_sigma
    ; msgs = []
    ; trace = [] }

let implode l =
  String.init (List.length l) (List.nth l)

let show_field n i (name, value) =
  match i with
  | 0 -> sprintf "{| %s := %s;" name value
  | i -> if i < n
         then sprintf "   %s := %s;" name value
         else sprintf "   %s := %s; |}" name value

let show_record l =
  String.concat "\n" (List.mapi (show_field (List.length l)) l)

let show_st_cur_request st = "TODO show_st_cur_request"

let show_state st =
  show_record [ ("pred", show_opt_pointer st.pred)
              ; ("succ_list", show_pointer_list st.succ_list)
              ; ("known", show_pointer st.known)
              ; ("joined", string_of_bool st.joined)
              ; ("rectify_with", show_opt_pointer st.rectify_with)
              ; ("cur_request", show_st_cur_request st)]

let show_state_for n h =
  match n.sigma h with
  | None -> "NO STATE FOUND"
  | Some st -> show_state st

let info_header_for dead =
  if dead
  then sprintf "NODE %d (dead)"
  else sprintf "NODE %d"

let show_node_info n h =
  let dead = List.mem h n.failed_nodes in
  let header = info_header_for dead h in
  String.concat "\n"
                [ "STATE AT " ^ header
                ; show_state_for n h
                ; "TIMEOUTS AT " ^ header
                ; show_list show_timeout (timeouts n h) ]

let show_msg (src, (dst, p)) = 
  sprintf "%d -> %d: %s" src dst (show_payload p)

let show_net n =
  let node_strs = "NODES" :: map (show_node_info n) (nodes n) in
  let msgs_strs = ["MESSAGES"; show_list show_msg (msgs n)] in
  String.concat "\n" (node_strs @ msgs_strs)

let show_operation = function
  | Op_start (a, ks) -> 
      sprintf "op_start %d %s" a (show_addr_list ks)
  | Op_fail a -> 
      sprintf "op_fail %d" a
  | Op_timeout (a, t) ->
      sprintf "op_timeout %d %s" a (show_timeout t)
  | Op_deliver (n, (src, (dst, p))) ->
      sprintf "op_deliver %d %d %d %s" n src dst (show_payload p)

module ChordArrangement = struct
  type net = chord_net
  type operation = chord_operation
  type netpred = chord_netpred
  type tracepred = chord_tracepred
  let show_net = show_net
  let show_operation = show_operation
  let inits =
    [("hardcoded", init)]
  let np_name np = implode np.np_name
  let tp_name tp = implode tp.tp_name
  let netpreds =
    [all_nodes_live_netpred]
  let tracepreds =
    [const_true_tracepred]
  let plans =
    [("deliver_or_timeout", chord_plan_deliver_or_timeout)]
  type test_state = chord_test_state
  let ts_latest ts = ts.ts_latest
  let ts_trace ts = ts.ts_trace
  let ts_netpreds ts = ts.ts_netpreds
  let ts_tracepreds ts = ts.ts_tracepreds
  let mk_init_state = chord_mk_init_state
  let advance_test ts op = chord_advance_test ts op
end
(*
  let inits =
    [("hardcoded", init)]
  let tracepreds =
    [tp_const_true run]
  let run = run
  let plans =
    [{ np_name = "deliver_only",
       np_dec = plan_deliver_only}]
  let netpreds list =
    [ExtractedChordShed.all_nodes_live_netpred]
  let show_operation = function
  | Op_start (a, ks) -> 
      sprintf "op_start %d %s" a (show_addr_list ks)
  | Op_fail a -> 
      sprintf "op_fail %d" a
  | Op_timeout (a, t) ->
      sprintf "op_timeout %d %s" a (show_timeout t)
  | Op_deliver (n, (src, (dst, p))) ->
      sprintf "op_deliver %d %d %d %s" n src dst (show_payload p)
  let show_net gst = "there should be a network here."
end
 *)
