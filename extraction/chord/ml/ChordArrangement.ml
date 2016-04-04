open ExtractedChord

module ChordDebugArrangement = struct
  type name = ExtractedChord.addr
  type state = ExtractedChord.data
  type msg = ExtractedChord.payload
  type res = state * (name * msg) list
  let addr_of_name n =
      ("127.0.0.1", n)
  let name_of_addr (s, p) =
      p
  let handleNet = ExtractedChord.recv_handler
  let handleTimeout = ExtractedChord.tick_handler
  let setTimeout n s = 10000000.0
  let debug = true
  let debugRecv _ _ = ()
  let debugSend _ _ = ()
  let debugTimeout s = ()
  let init = ExtractedChord.start_handler
end

