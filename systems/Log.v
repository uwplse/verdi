Require Import Verdi.Verdi.

Require Import Cheerios.Cheerios.

Import DeserializerNotations.

Set Implicit Arguments.

Class LogParams `(P : MultiParams) :=
  {
    log_data_serializer :> Serializer data ;
    log_name_serializer :> Serializer name ;
    log_msg_serializer :> Serializer msg ;
    log_input_serializer :> Serializer input ;
    log_snapshot_interval : nat
  }.

Section Log.
  Context {orig_base_params : BaseParams}.
  Context {orig_multi_params : MultiParams orig_base_params}.
  Context {orig_failure_params : FailureParams orig_multi_params}.
  Context {log_params : LogParams orig_multi_params}.

  Definition entry : Type := input + (name * msg).

  Inductive log_files :=
  | Count
  | Snapshot
  | Log.

  Definition log_files_eq_dec : forall x y : log_files, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Record log_state :=
    mk_log_state { log_num_entries : nat ;
                   log_data : data }.

  Definition log_net_handlers dst src m st : list (disk_op log_files) *
                                             list output *
                                             log_state *
                                             list (name * msg)  :=
    let '(out, data, ps) := net_handlers dst src m (log_data st) in
    let n := log_num_entries st in
    if S n =? log_snapshot_interval
    then ([Delete Log; Write Snapshot (serialize data); Write Count (serialize 0)],
          out,
          mk_log_state 0 data,
          ps)
    else ([Append Log (serialize (inr (src , m) : entry)); Write Count (serialize (S n))],
          out,
          mk_log_state (S n) data,
          ps).

  Definition log_input_handlers h inp st : list (disk_op log_files) *
                                           list output *
                                           log_state *
                                           list (name * msg) :=
    let '(out, data, ps) := input_handlers h inp (log_data st) in
    let n := log_num_entries st in
    if S n =? log_snapshot_interval
    then ([Delete Log; Write Snapshot (serialize data); Write Count (serialize 0)],
          out,
          mk_log_state 0 data,
          ps)
    else ([Append Log (serialize (inl inp : entry)); Write Count (serialize (S n))],
          out,
          mk_log_state (S n) data,
          ps).

  Instance log_base_params : BaseParams :=
    {
      data := log_state ;
      input := input ;
      output := output
    }.

  Definition log_init_handlers h :=
    mk_log_state 0 (init_handlers h).

  Definition init_disk (h : name) : do_disk log_files :=
    fun file =>
      match file with
      | Count => serialize 0
      | Snapshot => serialize (init_handlers h)
      | Log => IOStreamWriter.empty
      end.

  Instance log_multi_params : DiskOpMultiParams log_base_params :=
    {
      do_name := name;
      file_name := log_files;
      do_name_eq_dec := name_eq_dec;
      do_msg := msg;
      do_msg_eq_dec := msg_eq_dec;
      file_name_eq_dec := log_files_eq_dec;
      do_nodes := nodes;
      do_all_names_nodes := all_names_nodes;
      do_no_dup_nodes := no_dup_nodes;
      do_init_handlers := log_init_handlers;
      do_init_disk := init_disk;
      do_net_handlers := log_net_handlers;
      do_input_handlers := log_input_handlers
    }.

  Definition wire_to_log (w : file_name -> IOStreamWriter.wire) : option (nat * @data orig_base_params * list entry) :=
    match deserialize_top deserialize (w Count), deserialize_top deserialize (w Snapshot) with
    | Some n, Some d =>
      match deserialize_top (list_deserialize_rec' _ _ n) (w Log) with
      | Some es => Some (n, d, es)
      | None => None
      end
    | _, _ => None
    end.

  Definition apply_entry h d e :=
    match e with
     | inl inp => let '(_, d', _) := input_handlers h inp d in d'
     | inr (src, m) => let '(_, d', _) := net_handlers h src m d in d'
    end.

  Fixpoint apply_log h (d : @data orig_base_params) (entries : list entry) : @data orig_base_params :=
    match entries with
    | [] => d
    | e :: entries => apply_log h (apply_entry h d e) entries
    end.

  Definition do_log_reboot (h : do_name) (w : log_files -> IOStreamWriter.wire) :
    data * do_disk log_files :=
    match wire_to_log w with
    | Some (n, d, es) =>
      let d' := reboot (apply_log h d es) in
      (mk_log_state 0 d',
       fun file => match file with
                  | Count => serialize 0
                  | Snapshot => serialize d'
                  | Log => IOStreamWriter.empty
                  end)
    | None =>
      let d' := reboot (init_handlers h) in
      (mk_log_state 0 d',
       fun file => match file with
                  | Count => serialize 0
                  | Snapshot => serialize d'
                  | Log => IOStreamWriter.empty
                  end)
    end.

  Instance log_failure_params : DiskOpFailureParams log_multi_params :=
    { do_reboot := do_log_reboot }.
End Log.

Hint Extern 5 (@BaseParams) => apply log_base_params : typeclass_instances.
Hint Extern 5 (@DiskOpMultiParams _) => apply log_multi_params : typeclass_instances.
Hint Extern 5 (@DiskOpFailureParams _ _) => apply log_failure_params : typeclass_instances.
