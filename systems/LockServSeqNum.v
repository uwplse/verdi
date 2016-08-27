Require Import Verdi.

Require Import LockServ.
Require SeqNum.
Require Import SeqNumCorrect.

Section LockServSeqNum.

  Variable num_Clients : nat.

  Definition transformed_base_params :=
    @SeqNum.base_params (LockServ_BaseParams num_Clients) (LockServ_MultiParams num_Clients).
  Definition transformed_multi_params :=
    @SeqNum.multi_params (LockServ_BaseParams num_Clients) (LockServ_MultiParams num_Clients).

  Definition transformed_network :=
    @network transformed_base_params transformed_multi_params.

  Theorem transformed_correctness :
    forall (net : transformed_network) tr,
      step_dup_star (params := transformed_multi_params) step_async_init net tr ->
      @mutual_exclusion num_Clients (nwState (revertNetwork net)).
  Proof.
    intros.
    pose proof @true_in_reachable_transform _ (LockServ_MultiParams num_Clients)
         (fun net : network => mutual_exclusion (nwState net))
         (@true_in_reachable_mutual_exclusion num_Clients).
    unfold true_in_reachable in *.
    apply H0.
    unfold reachable.
    eauto.
  Qed.

End LockServSeqNum.
