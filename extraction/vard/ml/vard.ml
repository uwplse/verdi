open List
open Printf
open Str

module VarDDebug = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.DebugParams))
module VarDBench = Shim.Shim(VarDArrangement.VarDArrangement(VarDArrangement.BenchParams))

let node_spec arg nodes_ref doc =
  let parse opt =
    (* name,ip:port *)
    if string_match (regexp "\\([0-9]+\\),\\(.+\\):\\([0-9]+\\)") opt 0 then
      (int_of_string (matched_group 1 opt),
       (matched_group 2 opt, int_of_string (matched_group 3 opt)))
    else
      raise (Arg.Bad (sprintf "wrong argument: '%s'; option '%s' expects an address in the form 'name,host:port'" arg opt))
  in (arg, Arg.String (fun opt -> nodes_ref := !nodes_ref @ [parse opt]), doc)

let _ =

  let cluster = ref [] in
  let me = ref 0 in
  let port = ref 8351 in
  let dbpath = ref "/var/lib/vard" in
  let debug = ref false in

  let validate () =
    if length !cluster == 0 then begin
      raise (Arg.Bad "Please specify at least one -node")
    end;
    if !me == 0 then begin
      raise (Arg.Bad "Please specify the node name -me")
    end;
    if not (mem_assoc !me !cluster) then begin
      raise (Arg.Bad (sprintf "%d is not a member of this cluster" !me))
    end
  in

  let opts =
    [ node_spec "-node" cluster "{id,host:port} one node in the cluster"
    ; ("-me", Arg.Set_int me, "{name} name for this node")
    ; ("-port", Arg.Set_int port, "{port} port for client commands")
    ; ("-dbpath", Arg.Set_string dbpath, "{path} directory for storing database files")
    ; ("-debug", Arg.Set debug, "run in debug mode")
    ] in
  Arg.parse opts (fun args -> raise (Arg.Bad (sprintf "%s does not take position arguments" Sys.argv.(0)))) "Try -help for help or one of the following.";

  let _ =
    try
      validate ()
    with Arg.Bad msg ->
      eprintf "%s: %s." Sys.argv.(0) msg;
      prerr_newline ();
      exit 2
  in

  if !debug then
    let open VarDDebug in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         ; dbpath = !dbpath
         }
  else
    let open VarDBench in
    main { cluster = !cluster
         ; me = !me
         ; port = !port
         ; dbpath = !dbpath
         }

