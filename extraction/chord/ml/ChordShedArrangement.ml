open Printf
open String

open ExtractedChordShed

let show_pointer p =
  string_of_int (id_of p)

let show_addr_list l =
  sprintf "[%s]" (String.concat "; " (map (sprintf "%d") l))

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

(* just deliver a message *)
let plan_deliver_only gst _ n =
  let n' = n mod (List.length (msgs gst)) in
  Op_deliver (n', (List.nth (msgs gst) n'))

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
              ; known = mp 10
              ; joined = true
              ; rectify_with = None
              ; cur_request = None
              ; delayed_queries = [] })
    else None

let init =
    { nodes = init_nodes
    ; failed_nodes = []
    ; timeouts = (fun _ -> [])
    ; sigma = init_sigma
    ; msgs = []
    ; trace = [] }

let implode l =
  String.init (List.length l) (List.nth l)

module ChordArrangement = struct
  type net = chord_net
  type operation = chord_operation
  type netpred = chord_netpred
  type tracepred = chord_tracepred
  let show_net n = ""
  let show_operation o = ""
  let inits =
    [("hardcoded", init)]
  let np_name np = implode np.np_name
  let tp_name tp = implode tp.tp_name
  let netpreds =
    [all_nodes_live_netpred]
  let tracepreds =
    [const_true_tracepred]
  let plans =
    [("deliver_only", plan_deliver_only)]
  type test_state = chord_test_state
  let ts_latest ts = (ts.ts_latest)
  let ts_trace ts = (ts.ts_trace)
  let ts_netpreds ts = (ts.ts_netpreds)
  let ts_tracepreds ts = (ts.ts_tracepreds)
  let mk_init_state = chord_mk_init_state
  let show_state ts = ""
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
