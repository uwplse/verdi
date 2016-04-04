module ChordDebug = DynamicShim.Shim(ChordArrangement.ChordDebugArrangement)

let parse_addr s =
    ChordArrangement.ChordDebugArrangement.name_of_addr ("127.0.0.1", int_of_string s)

let _ =
    let len = Array.length Sys.argv in
    let me = parse_addr (Array.get Sys.argv 1) in
    let knowns = List.map parse_addr (Array.to_list (Array.sub Sys.argv 2 (len - 2))) in
    ChordDebug.main me knowns
