module VarDDebug = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.DebugParams))
module VarDBench = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.BenchParams))

let nodes = [ (1, ("127.0.0.1", 9001))
            ; (2, ("127.0.0.1", 9002))
            ; (3, ("127.0.0.1", 9003))
            ]

let run debug node =
  if debug then
    VarDDebug.main node nodes
  else
    VarDBench.main node nodes
              
let _ =
  let debug = ref false in
  let node = ref 1 in
  let opts = [
    ("-debug", Arg.Unit (fun () -> debug := true), "run in debug mode");
    ] in
  Arg.parse opts (fun args -> node := int_of_string args) "Try -help for help or one of the following." ;
  run !debug !node
