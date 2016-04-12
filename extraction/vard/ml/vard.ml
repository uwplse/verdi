open List
open Printf
open Str

module VarDDebug = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.DebugParams))
module VarDBench = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.BenchParams))

let default_nodes = [ (1, ("127.0.0.1", 9001))
                    ; (2, ("127.0.0.1", 9002))
                    ; (3, ("127.0.0.1", 9003))
                    ]

let run debug node nodes =
  if debug then
    VarDDebug.main node nodes
  else
    VarDBench.main node nodes

let node_spec arg nodes_ref doc =
  let parse opt =
    if string_match (regexp "\\([0-9]+\\),\\(.+\\):\\([0-9]+\\)") opt 0 then
      (int_of_string (matched_group 1 opt),
       (matched_group 2 opt, int_of_string (matched_group 3 opt)))
    else
      raise (Arg.Bad (sprintf "wrong argument: '%s'; option '%s' expects an address in the form 'id,host:port'" arg opt))
  in (arg, Arg.String (fun opt -> nodes_ref := !nodes_ref @ [parse opt]), doc)

let _ =
  let name = ref 1 in
  let debug = ref false in
  let nodes = ref [] in
  let opts = [
    ("-debug", Arg.Set debug, "run in debug mode");
    node_spec "-node" nodes "specify node in the form id,host:port";
    ] in
  Arg.parse opts (fun args -> name := int_of_string args) "Try -help for help or one of the following." ;
  (if length !nodes == 0 then
    nodes := default_nodes);
  run !debug !name !nodes
