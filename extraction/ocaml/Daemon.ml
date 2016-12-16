type ('env, 'state) task  = 
  {
    fd : Unix.file_descr ;
    mutable select_on : bool ;
    mutable wake_time : float option ;
    mutable process_read : ('env, 'state) task -> 'env -> 'state -> bool * ('env, 'state) task list * 'state ;
    mutable process_wake : ('env, 'state) task -> 'env -> 'state -> bool * ('env, 'state) task list * 'state ;
    finalize : ('env, 'state) task -> 'env -> 'state -> 'state ;
  }

let process process_f t hts env state =
  let state = ref state in
  let (finished, ts, state') = process_f t env !state in
  state := state';
  if finished then begin 
    Hashtbl.remove hts t.fd; 
    state := t.finalize t env !state 
  end;
  List.iter (fun t' -> Hashtbl.add hts t'.fd t') ts;
  !state

let rec eloop default_timeout old_timestamp hts env state =
  let state = ref state in
  let (select_fds, min_timeout) = 
    Hashtbl.fold
      (fun fd t (fds, timeout) ->
	let fds' = if t.select_on then fd :: fds else fds in
	let timeout' =
	  match t.wake_time with
	  | None -> timeout
	  | Some wake_time -> min timeout wake_time 
	in (fds', timeout'))
      hts ([], default_timeout) in
  let (ready_fds, _, _) = Unix.select select_fds [] [] min_timeout in
  List.iter
    (fun fd -> 
      let t = Hashtbl.find hts fd in 
      state := process t.process_read t hts env !state) ready_fds;
  let new_timestamp = Unix.gettimeofday () in
  let elapsed_time = new_timestamp -. old_timestamp in
  let wake_tasks =
    Hashtbl.fold
      (fun fd t ts ->
	match t.wake_time with
	| None -> ts
	| Some wake_time ->
	  if elapsed_time >= wake_time then
	    t :: ts
	  else
	    (t.wake_time <- Some (wake_time -. elapsed_time); ts))
      hts [] in
  List.iter (fun t -> state := process t.process_wake t hts env !state) wake_tasks;
  eloop default_timeout new_timestamp hts env !state
