type task = 
  {
    fd : Unix.file_descr ;
    mutable select_on : bool ;
    mutable wake_time : float option ;
    mutable process_read : task -> bool * task list ;
    mutable process_wake : task -> bool * task list ;
    finalize : task -> unit ;
  }

let handle_result hts task finish ts =
  if finish then (Hashtbl.remove hts task.fd; task.finalize task);
  List.iter (fun t -> Hashtbl.add hts t.fd t) ts

let rec eloop default_timeout hts =
  let start_time = Unix.gettimeofday () in
  let (select_fds, min_timeout) = 
    Hashtbl.fold 
      (fun fd t (fds, timeout) ->
	let fds' = if t.select_on then fd :: fds else fds in
	let timeout' = 
	  match t.wake_time with 
	  | None -> timeout 
	  | Some wake_time -> min timeout wake_time in
        (fds', timeout'))
      hts ([], default_timeout) in
  let (ready_fds, _, _) = Unix.select select_fds [] [] min_timeout in
  List.iter 
    (fun fd -> 
      let t = Hashtbl.find hts fd in
      let (finish, ts) = t.process_read t in
      handle_result hts t finish ts) 
    ready_fds;
  let elapsed_time = Unix.gettimeofday () -. start_time in
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
  List.iter 
    (fun t -> 
      let (finish, ts) = t.process_wake t in
      handle_result hts t finish ts)
    wake_tasks;
  eloop default_timeout hts
