From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness Require Import trace_helpers.
(* TODO: rearrange the code *)
From trillium.fairness Require Import lemmas trace_len trace_lookup utils.
From trillium.fairness.ext_models Require Import ext_models.


Section FairLock.
  Context {M: FairModel}.
  
  Context {allows_unlock: fmstate M -> fmstate M -> Prop}
          {allows_lock: fmrole M -> fmstate M -> fmstate M -> Prop}.
  
  (* Context {AU_DEC: forall st, Decision (∃ st', allows_unlock st st')} *)
  (*         {AL_DEC: forall st ρ, Decision (∃ st', allows_lock ρ st st')}.  *)

  Inductive fl_EI := flU | flL (ρ: fmrole M).

  Global Instance fl_EI_dec: EqDecision fl_EI. 
  Proof using. solve_decision. Qed. 

  Global Instance fl_EI_cnt: Countable fl_EI. 
  Proof using.
    assert (Countable (fmrole M)) as CNTρ by apply _.    
    eapply inj_countable' with 
      (f := fun ι => match ι with | flU => 0 | flL ρ => S (encode_nat ρ) end)
      (g := fun n => match n with 
                  | 0 => flU 
                  | S n' => match decode_nat n' with
                           | Some ρ => flL ρ
                           | None => flU
                           end end).
    intros. destruct x; auto. by rewrite decode_encode_nat. 
  Qed.

  Context (fl_active_exts: fmstate M -> gset fl_EI). 

  Definition fl_ETs (ι: fl_EI) :=
    match ι with
    | flU => allows_unlock
    | flL ρ => allows_lock ρ
    end.

  Context (fl_active_exts_spec: 
            forall st ι, ι ∈ fl_active_exts st <-> ∃ st', fl_ETs ι st st'). 

  (* Context {EM: ExtModel M}. *)
  Definition FL_EM: ExtModel M.
    refine {| active_exts_spec := fl_active_exts_spec |}.
  Defined. 

  Let St := fmstate M.
  Let R := fmrole M.
  Let EFM := @ext_model_FM _ FL_EM. 

  Context (can_lock_st can_unlock_st has_lock_st active_st: R -> St -> Prop).
  Context {active_st_Dec: forall ρ st, Decision (active_st ρ st)}. 
  (* Context (is_init_st: St -> Prop). *)
  Context (state_wf: St -> Prop). 
  
  Definition eventual_release (tr: mtrace EFM) (ρ: R) (i: nat) :=
    forall (ρ': R) j st' (JTH: tr S!! j = Some st')
      (HAS_LOCK: has_lock_st ρ' st')
      (AFTER: i <= j -> (ρ' ≠ ρ /\ forall k st_k (BETWEEN: i <= k <= j) (KTH: tr S!! k = Some st_k), ¬ has_lock_st ρ st_k)),
      exists k st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st''.

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
      (FROM_INIT: forall st0, tr S!! 0 = Some st0 -> state_wf st0)
      (FAIR: inner_fair_ext_model_trace tr)
      (ITH: tr S!! i = Some st)
      (CAN_LOCK: can_lock_st ρ st)
      (ACT: active_st ρ st)
      (EV_REL: eventual_release tr ρ i),
    exists n st', i < n /\ tr S!! n = Some st' /\ has_lock_st ρ st' /\ ¬ active_st ρ st'.
  

  (* TODO: mention these function equivalents of relations
           in the definition of EM itself? *)
  Class FairLock := {
      lock_progress: fair_lock_progress;

      allow_unlock_impl: fmstate M -> fmstate M;
      allow_lock_impl: fmrole M -> fmstate M -> fmstate M;
      allows_unlock_impl_spec st (WF: state_wf st):
      forall st', allows_unlock st st' <-> 
              (allow_unlock_impl st = st' /\ (exists ρ, has_lock_st ρ st /\ ¬ active_st ρ st));
      allows_lock_impl_spec ρ st:
      forall st', allows_lock ρ st st' <-> 
              (allow_lock_impl ρ st = st' /\ (can_lock_st ρ st /\ ¬ active_st ρ st));

      has_lock_st_dec :> forall ρ st, Decision (has_lock_st ρ st);
      can_lock_st_dec :> forall ρ st, Decision (can_lock_st ρ st);
      active_st_dec :> forall ρ st, Decision (active_st ρ st);
  }.

End FairLock.
