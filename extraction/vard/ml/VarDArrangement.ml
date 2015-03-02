open Str
open Printf
open VarDRaft

module type VardParams = sig
    val debug : bool
    val heartbeat_timeout : float
    val election_timeout : float
  end

module DebugParams = struct
    let debug = true
    let heartbeat_timeout = 2.0
    let election_timeout = 10.0
  end

module BenchParams = struct
    let debug = false
    let heartbeat_timeout = 0.05
    let election_timeout = 0.2
  end

module VarDArrangement (M : VardParams) = struct
  type name = VarDRaft.name
  type state = raft_data0
  type input = VarDRaft.raft_input
  type output = VarDRaft.raft_output
  type msg = VarDRaft.msg
  type res = (VarDRaft.raft_output list * raft_data0) * ((VarDRaft.name * VarDRaft.msg) list)
  type request_id = (int * int)
  let debug = M.debug
  let init x = Obj.magic (init_handlers0 vard_base_params vard_one_node_params raft_params x)
  let handleIO (n : name) (inp : input) (st : state) = Obj.magic (vard_raft_multi_params.input_handlers (Obj.magic n) (Obj.magic inp) (Obj.magic st))
  let handleNet (n : name) (src: name) (m : msg) (st : state)  = Obj.magic (vard_raft_multi_params.net_handlers (Obj.magic n) (Obj.magic src) (Obj.magic m) (Obj.magic st))
  let handleTimeout (me : name) (st : state) =
    (Obj.magic vard_raft_multi_params.input_handlers (Obj.magic me) (Obj.magic Timeout) (Obj.magic st))
  let reboot = Obj.magic (reboot vard_base_params raft_params)
  let setTimeout _ s =
    match s.type0 with
    | Leader -> M.heartbeat_timeout
    | _ -> M.election_timeout +. (Random.float 0.1)

  let char_list_of_string s =
    let rec exp i l =
      if i < 0 then l else exp (i - 1) (s.[i] :: l) in
    exp (String.length s - 1) []

  let string_of_char_list l =
    let res = String.create (List.length l) in
    let rec imp i = function
      | [] -> res
      | c :: l -> res.[i] <- c; imp (i + 1) l in
    imp 0 l

  let serialize out =
    match (Obj.magic out) with
    | NotLeader (client, id) ->
       ((client, id), "NotLeader\n")
    | ClientResponse (client, id, o) ->
       let Response (k, value, old) = (Obj.magic o) in
       ((client, id),
        match (value, old) with
        | Some v, Some o -> sprintf "Response %s %s %s\n"
                                    (string_of_char_list k)
                                    (string_of_char_list v)
                                    (string_of_char_list o)
        | Some v, None -> sprintf "Response %s %s -\n"
                                  (string_of_char_list k)
                                  (string_of_char_list v)
        | None, Some o -> sprintf "Response %s - %s\n"
                                  (string_of_char_list k)
                                  (string_of_char_list o)
        | None, None -> sprintf "Response %s - -\n" (string_of_char_list k))

  let deserialize_input i =
    let inp = String.trim i in
    let r = regexp "\\([0-9]+\\) \\([0-9]+\\) \\([A-Z]+\\) +\\([/A-za-z0-9]+\\|-\\) +\\([/A-za-z0-9]+\\|-\\) +\\([/A-za-z0-9]+\\|-\\)[^/A-za-z0-9]*" in
    if string_match r inp 0 then
      (match (matched_group 1 inp, matched_group 2 inp,
              matched_group 3 inp, matched_group 4 inp,
              matched_group 5 inp, matched_group 6 inp) with
       | (c, i, "GET", k, _, _) -> Some (int_of_string c, int_of_string i, Get (char_list_of_string k))
       | (c, i, "DEL", k, _, _) -> Some (int_of_string c, int_of_string i, Del (char_list_of_string k))
       | (c, i, "PUT", k, v, _) -> Some (int_of_string c, int_of_string i, Put ((char_list_of_string k), (char_list_of_string v)))
       | (c, i, "CAD", k, o, _) -> Some (int_of_string c, int_of_string i, CAD (char_list_of_string k, char_list_of_string o))
       | (c, i, "CAS", k, "-", v) -> Some (int_of_string c, int_of_string i, CAS ((char_list_of_string k), None, (char_list_of_string v)))
       | (c, i, "CAS", k, o, v) -> Some (int_of_string c, int_of_string i, CAS ((char_list_of_string k), Some (char_list_of_string o), (char_list_of_string v)))
       | _ -> None)
    else
      (print_endline "No match" ; None)

  let deserialize inp =
    match (deserialize_input inp) with
    | Some (client, id, input) ->
       Some ((client, id), (ClientRequest (client, id, (Obj.magic input))))
    | None -> None

  let debugRecv s (other, m) =
    (match m with
     | AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex) ->
        printf "[Term %d] Received %d entries from %d (currently have %d entries)\n"
               s.currentTerm (List.length entries) other (List.length s.log)
     | AppendEntriesReply (_, entries, success) ->
        printf "[Term %d] Received AppendEntriesReply %d entries %B, commitIndex %d\n"
               s.currentTerm (List.length entries) success s.commitIndex
     | RequestVoteReply (t, votingFor) ->
        printf "[Term %d] Received RequestVoteReply(%d, %B) from %d, have %d votes\n"
               s.currentTerm t votingFor other (List.length s.votesReceived)
     | _ -> ()); flush_all ()
  let debugSend s (other, m) =
    (match m with
     | AppendEntries (t, leaderId, prevLogIndex, prevLogTerm, entries, commitIndex) ->
        printf "[Term %d] Sending %d entries to %d (currently have %d entries), commitIndex=%d\n"
               s.currentTerm (List.length entries) other (List.length s.log) commitIndex
     | RequestVote _ ->
        printf "[Term %d] Sending RequestVote to %d, have %d votes\n"
               s.currentTerm other (List.length s.votesReceived)
     | _ -> ()); flush_all ()

  let debugTimeout (s : state) = ()
    (* (match s.type0 with
     | Leader -> printf "Leader\n"
     | Follower -> printf "Follower\n"
     | Candidate -> printf "Candidate\n"); *)

end
