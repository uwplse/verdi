let raw_bytes_of_int (x : int) : bytes =
  let buf = Bytes.make 4 '\x00' in
  Bytes.set buf 0 (char_of_int (x land 0xff));
  Bytes.set buf 1 (char_of_int ((x lsr 8) land 0xff));
  Bytes.set buf 2 (char_of_int ((x lsr 16) land 0xff));
  Bytes.set buf 3 (char_of_int ((x lsr 24) land 0xff));
  buf

let int_of_raw_bytes (buf : bytes) : int =
  (int_of_char (Bytes.get buf 0)) lor
    ((int_of_char (Bytes.get buf 1)) lsl 8) lor
    ((int_of_char (Bytes.get buf 2)) lsl 16) lor
    ((int_of_char (Bytes.get buf 3)) lsl 24)

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

let mk_addr_inet (ip, port) =
  Unix.ADDR_INET (Unix.inet_addr_of_string ip, port)

let mk_addr_inet_random_port ip =
  mk_addr_inet (ip, 0)

let string_of_sockaddr (saddr : Unix.sockaddr) : string =
  match saddr with
  | Unix.ADDR_UNIX path -> (Printf.sprintf "unix://%s" path)
  | Unix.ADDR_INET (addr, port) -> (Printf.sprintf "%s:%d" (Unix.string_of_inet_addr addr) port)

let octets_to_ip o1 o2 o3 o4 =
  o1 lsl 24 + o2 lsl 16 + o3 lsl 8 + o4

(* Matches four groups of at most three digits separated by dots *)
let weak_ip_regexp =
  Str.regexp "\\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)$"

(* Convert the string representation s of an ip, e.g., "10.14.122.04" to a
   32-bit integer.
   Throws Invalid_argument if s does not represent a valid IPv4 address. *)
let int_of_ip s =
  if Str.string_match weak_ip_regexp s 0
  then
    let int_of_kth_group k = int_of_string (Str.matched_group k s) in
    let numbers = List.map int_of_kth_group [1; 2; 3; 4] in
    match numbers with
    | [o1; o2; o3; o4] ->
       if List.for_all (fun x -> 0 <= x && x <= 255) numbers
       then octets_to_ip o1 o2 o3 o4
       else invalid_arg s
    | _ -> invalid_arg s
  else invalid_arg s

(* Convert a 32-bit integer to its dotted octet representation. *)
let ip_of_int i =
  if i > 1 lsl 32
  then invalid_arg (string_of_int i)
  else let octets = [(i land (1 lsl 32 - 1 lsl 24)) lsr 24;
                     (i land (1 lsl 24 - 1 lsl 16)) lsr 16;
                     (i land (1 lsl 16 - 1 lsl 8)) lsr 8;
                     i land (1 lsl 8 - 1)] in
       String.concat "." (List.map string_of_int octets)

let map_default f d = function
  | None -> d
  | Some v -> f v

let log level s =
  let now = Unix.gettimeofday () in
  Printf.printf "%f - %s: %s\n" now level s

let dbg = log "DEBUG"

let info = log "INFO"
