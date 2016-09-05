open List
open Printf


module type SHED_ARRANGEMENT = sig
    type net
    type operation
    type netpred
    type tracepred
    val show_net : net -> string
    val show_operation : operation -> string
    (* assoc list from identifiers to starting states *)
    val inits : (string * net) list
    val np_name : netpred -> string
    val tp_name : tracepred -> string
    val netpreds : netpred list
    val tracepreds : tracepred list
    (* assoc list from names to fns for operation generation (first
       integer is the number of steps taken so far, second is a
       randomly generated integer in the range 0 to 2^16 - 1). *)
    val plans : (string * (net -> int -> (int -> int) -> operation option)) list
    type test_state
    val ts_latest : test_state -> net
    val ts_trace : test_state -> (net * operation) list
    val ts_netpreds : test_state -> (netpred * bool list) list
    val ts_tracepreds : test_state -> (tracepred * (bool option) list) list
    val mk_init_state : net -> netpred list -> tracepred list -> test_state
    val advance_test : test_state -> operation -> test_state option
end

let explode s =
  let rec exp i l =
    if i < 0
    then l
    else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

module Shim (A: SHED_ARRANGEMENT) = struct
    type cfg =
        { netpreds : A.netpred list
        ; tracepreds : A.tracepred list
        ; plan : A.net -> int -> (int -> int) -> A.operation option
        ; init : A.net
        ; depth : int }

    let print_occ occ =
      print_endline (A.show_operation (snd occ));
      print_endline (A.show_net (fst occ))

    let print_np_res i (np, l) = 
      print_endline (A.np_name np ^ ": " ^ string_of_bool (nth l i))

    let show_tp_result = function
      | Some true -> "true"
      | Some false -> "false"
      | None -> "maybe"
      
    let print_tp_res i (tp, l) =
      print_endline (A.tp_name tp ^ ": " ^ show_tp_result (nth l i))

    let print_step res i occ =
      printf "STEP %d\n" (i + 1);
      print_occ occ;
      iter (print_np_res i) (A.ts_netpreds res);
      iter (print_tp_res i) (A.ts_tracepreds res);
      print_newline ()

    let print_res res =
      iteri (print_step res) (A.ts_trace res);
      print_endline "";
      print_endline "FINAL STATE";
      print_endline (A.show_net (A.ts_latest res))

    let find_np_by_name s =
      find (fun np -> s = A.np_name np) A.netpreds
             
    let find_tp_by_name s =
      find (fun tp -> s = A.tp_name tp) A.tracepreds

    let combine_with_nils l =
      combine l (map (fun _ -> []) l)

    type test_result =
      | Ok of A.test_state
      | Stalled of A.test_state
      | Failed of A.test_state * A.operation

    let random_nat n =
      if n == 0
      then 0
      else Random.int n

    let rec test_loop st plan n =
      if n <= 0
      then Ok st
      else
        match plan (A.ts_latest st) n random_nat with
        | None -> Stalled st
        | Some op ->
           match A.advance_test st op with
           | None -> Failed (st, op)
           | Some st' -> test_loop st' plan (n - 1)

    let run_test cfg =
      let st = A.mk_init_state cfg.init cfg.netpreds cfg.tracepreds in
      match test_loop st cfg.plan cfg.depth with
      | Ok res -> print_res res
      | Failed (res, op) ->
         print_endline "!!! invalid operation !!!";
         print_endline (A.show_operation op);
         print_newline ();
         print_res res
      | Stalled res ->
         print_endline "!!! couldn't plan anything !!!";
         print_newline ();
         print_res res

    let main = 
      Random.self_init ();
      let nps = ref [] in
      let tps = ref [] in
      let n = ref 50 in
      let init = ref (fst (hd A.inits)) in
      let plan = ref (fst (hd A.plans))  in
      let add_np s = nps := find_np_by_name s :: !nps in
      let add_tp s = tps := find_tp_by_name s :: !tps in
      let opts =
          [ ("-np", Arg.String add_np, "network predicate to check")
          ; ("-tp", Arg.String add_tp, "network predicate to check")
          ; ("-plan", Arg.Set_string plan, "plan to use")
          ; ("-depth", Arg.Set_int n, "number of steps to take")
          ; ("-init", Arg.Set_string init, "name of initial state") ] in
      Arg.parse opts (fun _ -> ()) "todo";
      Printf.printf "running plan %s\n" !plan;
      run_test { netpreds = !nps
               ; tracepreds = !tps
               ; init = assoc !init A.inits 
               ; plan = assoc !plan A.plans
               ; depth = !n }
end

