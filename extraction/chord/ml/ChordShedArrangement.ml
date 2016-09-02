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
let next gst n =
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

module ChordArrangement = struct
  type net = (addr, payload, data, timeout) global_state
  type operation = (addr, payload, timeout) ExtractedChordShed.operation
  let run = run 
  let next = next
  let inits = [("hardcoded", init)]
  let netpreds = [all_nodes_live_netpred, np_const_true]
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
