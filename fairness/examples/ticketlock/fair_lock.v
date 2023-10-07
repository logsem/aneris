From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness Require Import trace_helpers.
(* TODO: rearrange the code *)
From trillium.fairness.examples.comp Require Import lemmas trace_len trace_lookup.
From trillium.fairness.examples.ticketlock Require Import set_map_properties ext_models.


Section FairLock.
  Context (EM: ExtModel). 

  Let m := @innerM EM. 
  Let St := fmstate m.
  Let R := fmrole m.
  Let EFM := ext_model_FM EM. 

  Context (can_lock_st can_unlock_st has_lock_st active_st: R -> St -> Prop).
  Context {active_st_Dec: forall ρ st, Decision (active_st ρ st)}. 
  Context (is_init_st: St -> Prop). 
  

  (* Definition eventual_release (tr: mtrace EFM) (ρ: R) (i: nat) := *)
  (*   forall (ρ': R) j st' (JTH: tr S!! j = Some st') *)
  (*     (HAS_LOCK: has_lock_st ρ' st') *)
  (*     (PREVr: ρ' = ρ -> j < i), *)
  (*   exists k st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st''. *)
  (* Definition eventual_release (tr: mtrace EFM) (ρ: R) (i: nat) := *)
  (*   forall (ρ': R) j st' (JTH: tr S!! j = Some st') *)
  (*     (HAS_LOCK: has_lock_st ρ' st'), *)
  (*   exists k st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st''. *)
  Definition eventual_release (tr: mtrace EFM) (ρ: R) (i: nat) :=
    forall (ρ': R) j st' (JTH: tr S!! j = Some st')
      (HAS_LOCK: has_lock_st ρ' st')
      (AFTER: i <= j -> (ρ' ≠ ρ /\ forall k st_k (BETWEEN: i <= k <= j) (KTH: tr S!! k = Some st_k), ¬ has_lock_st ρ st_k)),
      exists k st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st''.

  (* Lemma eventual_release_strenghten tr ρ i *)
  (*   (EV_REL: eventual_release tr ρ i): *)
  (*   forall ρ' j st' (JTH: tr S!! j = Some st') *)
  (*     (HAS_LOCK: has_lock_st ρ' st') *)
  (*     (PREVr: ρ' = ρ -> j < i), *)
  (*   exists k, ClassicalFacts.Minimal  *)
  (*          (fun k => exists st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st'') k. *)
  (* Proof using active_st_Dec.  *)
  (*   intros. red in EV_REL. specialize (EV_REL _ _ _ JTH HAS_LOCK PREVr). *)
  (*   destruct EV_REL as [k EV_REL]. pattern k in EV_REL.  *)
  (*   eapply min_prop_dec in EV_REL; eauto. *)
  (*   intros. *)
  (*   destruct (tr S!! n) as [st | ] eqn:NTH. *)
  (*   2: { right. intros (? & ? & ?). congruence. } *)
  (*   destruct (decide (j <= n)). *)
  (*   2: { right. intros (? & ? & ?). lia. } *)
  (*   destruct (active_st_Dec ρ' st). *)
  (*   - left. eauto. *)
  (*   - right. intros (? & ? & ? & ?). congruence. *)
  (* Qed. *)

  Lemma eventual_release_strenghten tr ρ i (EV_REL: eventual_release tr ρ i):
    forall (ρ': R) j st' (JTH: tr S!! j = Some st')
      (HAS_LOCK: has_lock_st ρ' st')
      (AFTER: i <= j -> (ρ' ≠ ρ /\ forall k st_k (BETWEEN: i <= k <= j) (KTH: tr S!! k = Some st_k), ¬ has_lock_st ρ st_k)),
    exists k, ClassicalFacts.Minimal
           (fun k => exists st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st'') k.
  Proof using active_st_Dec.
    intros. red in EV_REL. specialize (EV_REL _ _ _ JTH HAS_LOCK AFTER).
    destruct EV_REL as [k EV_REL]. pattern k in EV_REL.
    eapply min_prop_dec in EV_REL; eauto.
    intros.
    destruct (tr S!! n) as [st | ] eqn:NTH.
    2: { right. intros (? & ? & ?). congruence. }
    destruct (decide (j <= n)).
    2: { right. intros (? & ? & ?). lia. }
    destruct (active_st_Dec ρ' st).
    - left. eauto.
    - right. intros (? & ? & ? & ?). congruence.
  Qed.
      

  Definition fair_lock_progress :=
    forall (tr: mtrace EFM) (ρ: R) (i: nat) (st: St)
      (VALID: mtrace_valid tr)
      (FROM_INIT: forall st0, tr S!! 0 = Some st0 -> is_init_st st0)
      (FAIR: inner_fair_ext_model_trace EM tr)
      (ITH: tr S!! i = Some st)
      (CAN_LOCK: can_lock_st ρ st)
      (ACT: active_st ρ st)
      (EV_REL: eventual_release tr ρ i),
    exists n st', i < n /\ tr S!! n = Some st' /\ has_lock_st ρ st' /\ ¬ active_st ρ st'.

      
  Class FairLock := {
      lock_progress: fair_lock_progress
  }.

End FairLock.
