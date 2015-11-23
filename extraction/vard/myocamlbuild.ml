open Ocamlbuild_plugin;;

dispatch begin function
  | Before_options ->
      Options.ocaml_libs := ["unix"; "graphics"; "libocamlviz"];
  | _ -> ()
end;;
