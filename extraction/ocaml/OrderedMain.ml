module OrderedMain (A : OrderedShim.ARRANGEMENT) = struct
  module S = OrderedShim.Shim(A)

  let usage msg =
    print_endline msg;
    Printf.printf "%s usage:" A.systemName;
    Printf.printf "    %s -me <MY_ID> <CLUSTER>\n" (Array.get Sys.argv 0);
    print_endline "where:";
    print_endline "    MY_ID     is the id of this node";
    print_endline "    CLUSTER   is a list of triples of ID IP_ADDR PORT,";
    print_endline "              giving all the nodes in the system";
    exit 1

  let cluster : (A.name * (string * int)) list ref = ref []
  let me : A.name option ref = ref None

  let parse_name s =
    match A.deserializeName s with
    | Some nm -> nm
    | None -> usage (Printf.sprintf "Unrecognized name %s" s)

  let rec parse_args = function
    | [] -> ()
    | "-me" :: arg :: args -> begin
        me := Some (parse_name arg);
        parse_args args
      end
    | name :: ip :: port :: args -> begin
        cluster := (parse_name name, (ip, int_of_string port)) :: !cluster;
        parse_args args
      end
    | arg :: args -> usage (Printf.sprintf "Don't know what to do with arg %s" arg)

  let string_of_cluster cluster =
    let string_of_entry =
      function (id, (ip, port)) ->
               Printf.sprintf "(%s, (%s, %d))" (A.serializeName id) ip port in
    String.concat ", " (List.map string_of_entry cluster)

  let main () =
    parse_args (List.tl (Array.to_list Sys.argv));
    match List.rev !cluster, !me with
      | [], _ -> usage "Empty cluster is not allowed"
      | _, None -> usage "-me flag is required"
      | cluster, Some me -> begin
          Printf.printf "Starting up with cluster %s\nI am node %s\n"
                        (string_of_cluster cluster) (A.serializeName me);
          S.main {
              S.cluster = cluster;
              S.me = me
            }
        end
end
