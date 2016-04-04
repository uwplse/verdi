module ChordDebug = DynamicShim.Shim(ChordArrangement.ChordDebugArrangement)

let nodes = [ (1, ("127.0.0.1", 9001))
            ; (2, ("127.0.0.1", 9002))
            ; (3, ("127.0.0.1", 9003))
            ]

let parse_known s = int_of_string s

let _ =
    let knowns = List.map parse_known (List.tl (Array.to_list Sys.argv)) in
    ChordDebug.main 9000 knowns
