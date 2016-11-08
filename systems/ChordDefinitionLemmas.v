Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import Verdi.Chord.
Require Import Verdi.ChordLocalProps.


Ltac expand_def :=
  repeat (try break_or_hyp; try break_and; try break_exists);
  subst_max;
  try tuple_inversion;
  try (exfalso; tauto).

Section ChordDefinitionLemmas.
  Variable SUCC_LIST_LEN : nat.
  Variable N : nat.
  Variable hash : addr -> id.
  Notation start_handler := (start_handler SUCC_LIST_LEN hash).
  Notation recv_handler := (recv_handler SUCC_LIST_LEN hash).
  Notation timeout_handler := (timeout_handler hash).
  Notation tick_handler := (tick_handler hash).
  Notation handle_query_res := (handle_query_res SUCC_LIST_LEN hash).
  Notation handle_query_timeout := (handle_query_timeout hash).
  Notation make_pointer := (make_pointer hash).
  Notation start_query := (start_query hash).
  Notation handle_stabilize := (handle_stabilize SUCC_LIST_LEN hash).
  Notation do_rectify := (do_rectify hash).
  Notation make_succs := (make_succs SUCC_LIST_LEN).

  (* Definition lemmas *)
  Lemma handle_query_req_busy_definition :
    forall src dst st msg st' ms newts clearedts,
      handle_query_req_busy src dst st msg = (st', ms, newts, clearedts) ->
      st' = delay_query st src msg /\
      ms = [(src, Busy)] /\
      clearedts = [] /\
      ((delayed_queries st = [] /\ newts = [KeepaliveTick]) \/
       (delayed_queries st <> [] /\ newts = [])).
  Proof.
    unfold handle_query_req_busy.
    intros.
    repeat break_match; tuple_inversion; tauto.
  Qed.

  Lemma handle_query_res_definition :
    forall src dst st blank q p st' ms newts clearedts,
      handle_query_res src dst st blank q p = (st', ms, newts, clearedts) ->
      (request_payload p /\
       st' = delay_query st src p /\
       clearedts = [] /\
       (delayed_queries st = [] /\
        newts = [KeepaliveTick]) \/
       (delayed_queries st <> [] /\
        newts = [])) \/
      (p = Busy /\
       st' = st /\
       newts = timeouts_in st /\
       clearedts = timeouts_in st) \/
      (exists n,
          q = Rectify n /\
          p = Pong /\
          (exists pr,
              pred st = Some pr /\
              end_query (handle_rectify st pr n) = (st', ms, newts, clearedts)) \/
          (pred st = None /\
           end_query (update_pred st n, [], [], []) = (st', ms, newts, clearedts))) \/
      (q = Stabilize /\
       (exists new_succ succs,
           p = GotPredAndSuccs (Some new_succ) succs /\
           handle_stabilize dst (make_pointer src) st q new_succ succs = (st', ms, newts, clearedts)) \/
       (exists succs,
           p = GotPredAndSuccs None succs /\
           end_query (st, [], [], []) = (st', ms, newts, clearedts))) \/
      (exists new_succ,
          q = Stabilize2 new_succ /\
          exists succs,
            p = GotSuccList succs /\
            end_query (update_succ_list st (make_succs new_succ succs),
                           [(addr_of new_succ, Notify)], [], []) = (st', ms, newts, clearedts)) \/
      (exists k,
          q = Join k /\
          (exists bestpred,
              p = GotBestPredecessor bestpred /\
              clearedts = [Request src (GetBestPredecessor (make_pointer dst))] /\
              st' = st /\
              (addr_of bestpred = src /\
               ms = [(src, GetSuccList)] /\
               newts = [Request src GetSuccList]) \/
              (addr_of bestpred <> src /\
               ms = [(addr_of bestpred, (GetBestPredecessor (make_pointer dst)))] /\
               newts = [Request (addr_of bestpred) (GetBestPredecessor (make_pointer dst))])) \/
          (p = GotSuccList [] /\
           end_query (st, [], [], []) = (st', ms, newts, clearedts)) \/
          (exists new_succ rest,
              p = GotSuccList (new_succ :: rest) /\
              start_query (addr_of new_succ) st (Join2 new_succ) = (st', ms, newts, clearedts))) \/
      (exists new_succ succs,
          q = Join2 new_succ /\
          p = GotSuccList succs /\
          add_tick (end_query (update_for_join st (make_succs new_succ succs), [], [], [])) = (st', ms, newts, clearedts)) \/
      st' = st /\ ms = [] /\ newts = [] /\ clearedts = [].
  Proof.
    unfold handle_query_res.
    intros.
    repeat break_match; try tuple_inversion; try tauto.
    - right. right. left. eexists. intuition eauto.
    - intuition eauto.
    - intuition eauto.
    - intuition eauto.
    - intuition eauto.
    - do 5 right. left.
      exists p0. left. firstorder.
      eexists; intuition eauto.
      admit.
    - do 5 right. left.
      exists p0. intuition eauto.
    - repeat find_rewrite.
      do 5 right. left.
      exists p0. right.
      intuition.
      admit.
    - do 5 right. left.
      exists p0.
      intuition eauto.
      admit.
  Admitted.

  Lemma recv_handler_definition :
    forall src dst st p st' ms newts clearedts,
      recv_handler src dst st p = (st', ms, newts, clearedts) ->
      p = Ping /\
      st' = st /\
      ms = [(src, Pong)] /\
      newts = [] /\
      clearedts = [] \/

      p = Notify /\
      st' = set_rectify_with st (make_pointer src) /\
      ms = [] /\
      newts = [] /\
      clearedts = [] \/

      (exists qd q qm,
          cur_request st = Some (qd, q, qm) /\
          (request_payload p /\
           st' = delay_query st src p /\
           clearedts = [] /\
           (delayed_queries st = [] /\
            newts = [KeepaliveTick]) \/
           (delayed_queries st <> [] /\
            newts = [])) \/
          (p = Busy /\
           st' = st /\
           newts = timeouts_in st /\
           clearedts = timeouts_in st) \/
          (exists n,
              q = Rectify n /\
              p = Pong /\
              (exists pr,
              pred st = Some pr /\
              end_query (handle_rectify st pr n) = (st', ms, newts, clearedts)) \/
          (pred st = None /\
           end_query (update_pred st n, [], [], []) = (st', ms, newts, clearedts))) \/
      (q = Stabilize /\
       (exists new_succ succs,
           p = GotPredAndSuccs (Some new_succ) succs /\
           handle_stabilize dst (make_pointer src) st q new_succ succs = (st', ms, newts, clearedts)) \/
       (exists succs,
           p = GotPredAndSuccs None succs /\
           end_query (st, [], [], []) = (st', ms, newts, clearedts))) \/
      (exists new_succ,
          q = Stabilize2 new_succ /\
          exists succs,
            p = GotSuccList succs /\
            end_query (update_succ_list st (make_succs new_succ succs),
                           [(addr_of new_succ, Notify)], [], []) = (st', ms, newts, clearedts)) \/
      (exists k,
          q = Join k /\
          (exists bestpred,
              p = GotBestPredecessor bestpred /\
              clearedts = [Request src (GetBestPredecessor (make_pointer dst))] /\
              st' = st /\
              (addr_of bestpred = src /\
               ms = [(src, GetSuccList)] /\
               newts = [Request src GetSuccList]) \/
              (addr_of bestpred <> src /\
               ms = [(addr_of bestpred, (GetBestPredecessor (make_pointer dst)))] /\
               newts = [Request (addr_of bestpred) (GetBestPredecessor (make_pointer dst))])) \/
          (p = GotSuccList [] /\
           end_query (st, [], [], []) = (st', ms, newts, clearedts)) \/
          (exists new_succ rest,
              p = GotSuccList (new_succ :: rest) /\
              start_query (addr_of new_succ) st (Join2 new_succ) = (st', ms, newts, clearedts))) \/
      (exists new_succ succs,
          q = Join2 new_succ /\
          p = GotSuccList succs /\
          add_tick (end_query (update_for_join st (make_succs new_succ succs), [], [], [])) = (st', ms, newts, clearedts)) \/
      st' = st /\ ms = [] /\ newts = [] /\ clearedts = []
      ) \/

      (cur_request st = None /\
       st' = st /\
       clearedts = [] /\
       newts = [] /\
       ((exists h,
           p = GetBestPredecessor h /\
           ms = [(src, GotBestPredecessor (best_predecessor (ptr st) (succ_list st) h))]) \/
       (p = GetSuccList /\
        ms = [(src, GotSuccList (succ_list st))]) \/
       (p = GetPredAndSuccs /\
        ms = [(src, GotPredAndSuccs (pred st) (succ_list st))]))) \/

      st = st' /\ ms = [] /\ newts = [] /\ clearedts = [].
  Admitted.

  Lemma do_rectify_definition :
    forall h st st' ms' nts' cts',
      do_rectify h st = (st', ms', nts', cts') ->
      (cur_request st = None /\
       joined st = true /\
       (exists new,
           rectify_with st = Some new /\
           (exists x,
               pred st = Some x /\
               start_query h (clear_rectify_with st) (Rectify new) = (st', ms', nts', cts')) \/
           (pred st = None /\
            st' = clear_rectify_with (update_pred st new) /\
            ms' = [] /\
            nts' = [] /\
            cts' = []))) \/
      ((joined st = false \/ rectify_with st = None \/ exists r, cur_request st = Some r) /\
       st' = st /\ ms' = [] /\ nts' = [] /\ cts' = []).
  Proof.
    unfold do_rectify.
    intros.
    repeat break_match; try tuple_inversion; try tauto.
    - firstorder eauto.
    - firstorder eauto.
    - left.
      repeat (eexists; firstorder).
  Qed.

  Lemma start_query_definition :
    forall h st k st' ms nts cts,
      start_query h st k = (st', ms, nts, cts) ->
      (exists dst msg,
          make_request hash h st k = Some (dst, msg) /\
          st' = update_query st dst k msg /\
          ms = [(addr_of dst, msg)] /\
          nts = [Request (addr_of dst) msg] /\
          cts = timeouts_in st) \/
      (make_request hash h st k = None /\
       st' = st /\
       ms = [] /\
       ms = [] /\
       nts = [] /\
       cts = []).
  Proof.
    unfold start_query.
    intros.
    repeat break_match; tuple_inversion; try tauto.
    left; repeat eexists.
  Qed.

  Lemma handle_delayed_queries_definition :
    forall h st st' ms nts cts,
     do_delayed_queries h st = (st', ms, nts, cts) ->
     (exists r, cur_request st = Some r /\
           st' = st /\ ms = [] /\ nts = [] /\ cts = []) \/
     (cur_request st = None /\
      st' = clear_delayed_queries st /\
      ms = concat (map (handle_delayed_query h st) (delayed_queries st)) /\
      nts = [] /\
      cts = [KeepaliveTick]).
  Proof.
    unfold do_delayed_queries.
    intros.
    repeat break_match; tuple_inversion;
    [left; eexists|]; tauto.
  Qed.

  Lemma end_query_definition :
    forall st ms newts clearedts st' ms' newts' clearedts',
      end_query (st, ms, newts, clearedts) = (st', ms', newts', clearedts') ->
      st' = clear_query st /\
      ms' = ms /\
      newts' = newts /\
      clearedts' = timeouts_in st ++ clearedts.
  Proof.
    unfold end_query; simpl.
    intros.
    tuple_inversion; tauto.
  Qed.

  Lemma handle_rectify_definition :
    forall st my_pred notifier st' ms nts cts,
      handle_rectify st my_pred notifier = (st', ms, nts, cts) ->
      ms = [] /\
      nts = [] /\
      cts = [] /\
      (between (id_of my_pred) (id_of notifier) (id_of (ptr st)) /\
       st' = update_pred st notifier \/
       ~ between (id_of my_pred) (id_of notifier) (id_of (ptr st)) /\
       st' = st).
  Proof.
    unfold handle_rectify.
    intros.
    rewrite between_between_bool_equiv.
  Admitted.

End ChordDefinitionLemmas.
