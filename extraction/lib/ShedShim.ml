open ExtractedShed
open List
open Random

module type SHED_ARRANGEMENT = sig
    type net
    type operation
    val run : net -> operation -> net option
    val next : net -> nat -> operation
    (* assoc list from identifiers to starting states *)
    val inits : (string * net) list
    val netpreds : (net netpred) list
    val tracepreds : ((net, operation) tracepred) list
    val show_operation : operation -> string
    val show_net : net -> string
end

let implode l =
  let res = String.create (length l) in
  let rec imp i = function
    | [] ->
       res
    | c :: l ->
       res.[i] <- c;
       imp (i + 1) l in
  imp 0 l

module Shim (A: SHED_ARRANGEMENT) = struct
    type cfg =
        { netpreds : (A.net netpred) list
        ; tracepreds : ((A.net, A.operation) tracepred) list
        ; init : A.net
        ; depth : int }

    let print_occ occ =
      print_endline (A.show_operation occ.occ_op)

    let print_np_res i (np, l) = 
      print_endline ((implode np.np_name) ^ ": " ^ string_of_bool (nth l i))

    let show_tp_result = function
      | Tp_True -> "tp_True"
      | Tp_False -> "tp_False"
      | Tp_Maybe -> "tp_Maybe"
      
    let print_tp_res i (tp, l) =
      print_endline ((implode tp.tp_name) ^ ": " ^ show_tp_result (nth l i))

    let print_step res i occ =
      print_occ occ;
      iter (print_np_res i) (ts_netpreds A.run res);
      iter (print_tp_res i) (ts_tracepreds A.run res)

    let print_res res =
      iteri (print_step res) res.ts_trace;
      print_endline "";
      print_endline (A.show_net res.ts_latest)
                      
    let find_np_by_name s =
      find (fun np -> s = np.np_name) A.netpreds
             
    let find_tp_by_name s =
      find (fun tp -> s = tp.tp_name) A.tracepreds

    let run_test cfg =
      let res = random_test A.run cfg.netpreds cfg.tracepreds cfg.init A.next cfg.depth in
      print_res res
                  
    let main = 
      let nps = ref [] in
      let tps = ref [] in
      let n = ref 5 in
      let init = ref "" in
      let add_np s = nps := find_np_by_name s :: !nps in
      let add_tp s = tps := find_tp_by_name s :: !tps in
      let opts =
          [ ("-np", Arg.String add_np, "network predicate to check")
          ; ("-tp", Arg.String add_tp, "network predicate to check")
          ; ("-depth", Arg.Set_int n, "number of steps to take")
          ; ("-init", Arg.Set_string init, "name of initial state") ] in
      Arg.parse opts (fun _ -> ());
      run_test { netpreds = !nps
               ; tracepreds = !tps
               ; init = assoc !init A.inits 
               ; depth = !n }
end

