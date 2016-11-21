open Str
module ChordDebug = DynamicShim.Shim(ChordArrangement.ChordDebugArrangement)

let parse_addr s =
    match split (regexp ":") s with
    | addr::port::[] -> ChordArrangement.ChordDebugArrangement.name_of_addr (addr, int_of_string port)
    | _ -> invalid_arg s

let _ =
    let len = Array.length Sys.argv in
    let me = parse_addr (Array.get Sys.argv 1) in
    Printf.printf "%d\n" me;
    let knowns = List.map parse_addr (Array.to_list (Array.sub Sys.argv 2 (len - 2))) in
    ChordDebug.main me knowns
