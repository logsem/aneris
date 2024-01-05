From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness Require Import trace_helpers.
(* TODO: rearrange the code *)
From trillium.fairness Require Import lemmas trace_len trace_lookup utils trace_helpers.
From trillium.fairness.ext_models Require Import ext_models.


Class FairLockPredicates (M: FairModel) := {
  can_lock_st: fmrole M -> fmstate M -> Prop;
  has_lock_st: fmrole M -> fmstate M -> Prop;
  active_st: fmrole M -> fmstate M -> Prop;
  disabled_st: fmrole M -> fmstate M -> Prop;
  is_unused: fmrole M -> fmstate M -> Prop;
  (* state_wf: fmstate M -> Prop; *)
  (* is_unused := fun ρlg st => ¬ can_lock_st ρlg st /\ ¬ has_lock_st ρlg st; *)

  has_lock_st_dec :> forall ρ st, Decision (has_lock_st ρ st);
  can_lock_st_dec :> forall ρ st, Decision (can_lock_st ρ st);
  active_st_dec :> forall ρ st, Decision (active_st ρ st);
  disabled_st_dec :> forall ρ st, Decision (disabled_st ρ st);
  is_unused_dec :> forall ρ st, Decision (is_unused ρ st);
}.


Section FairLock.
  Context `{FL: FairLockPredicates M}. 
  Context {EM: ExtModel M}. 
  
  Let St := fmstate M.
  Let R := fmrole M.
  Let EFM := @ext_model_FM _ EM.

  Definition eventual_release (tr: mtrace EFM) (ρ: R) (i: nat) :=
    forall (ρ': R) j st' (JTH: tr S!! j = Some st')
      (HAS_LOCK: has_lock_st ρ' st')
      (* (DIS: ¬ role_enabled_model ρ' st') *)
      (DIS: disabled_st ρ' st')
      (AFTER: i <= j -> (ρ' ≠ ρ /\ forall k st_k (BETWEEN: i <= k <= j) (KTH: tr S!! k = Some st_k), ¬ has_lock_st ρ st_k)),
      exists k st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st''.

  Lemma eventual_release_strenghten tr ρ i (EV_REL: eventual_release tr ρ i):
    forall (ρ': R) j st' (JTH: tr S!! j = Some st')
      (HAS_LOCK: has_lock_st ρ' st')
      (* (DIS: ¬ role_enabled_model ρ' st') *)
      (DIS: disabled_st ρ' st')
      (AFTER: i <= j -> (ρ' ≠ ρ /\ forall k st_k (BETWEEN: i <= k <= j) (KTH: tr S!! k = Some st_k), ¬ has_lock_st ρ st_k)),
    exists k, ClassicalFacts.Minimal
           (fun k => exists st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st'') k.
  Proof using.
    intros. red in EV_REL. specialize (EV_REL _ _ _ JTH HAS_LOCK DIS AFTER).
    destruct EV_REL as [k EV_REL]. pattern k in EV_REL.
    eapply min_prop_dec in EV_REL; eauto.
    intros.
    destruct (tr S!! n) as [st | ] eqn:NTH.
    2: { right. intros (? & ? & ?). congruence. }
    destruct (decide (j <= n)).
    2: { right. intros (? & ? & ?). lia. }
    destruct (decide (active_st ρ' st)). 
    - left. eauto.
    - right. intros (? & ? & ? & ?). congruence.
  Qed.
      

  Definition fair_lock_progress :=
    forall (tr: mtrace EFM) (ρ: R) (i: nat) (st: St)
      (VALID: mtrace_valid tr)
      (* (FROM_INIT: forall st0, tr S!! 0 = Some st0 -> @state_wf _ FL st0) *)
      (FAIR: inner_fair_ext_model_trace tr)
      (ITH: tr S!! i = Some st)
      (CAN_LOCK: can_lock_st ρ st)
      (ACT: active_st ρ st)
      (EV_REL: eventual_release tr ρ i),
    exists n st', i < n /\ tr S!! n = Some st' /\ has_lock_st ρ st' /\ 
               (* ¬ role_enabled_model ρ st'. *)
               disabled_st ρ st'. 
  
End FairLock.



Section FairLockEM.
  Context {M: FairModel}.
  Inductive fl_EI := flU (ρ: fmrole M) | flL (ρ: fmrole M).
  Context {au al: fmrole M -> fmstate M -> fmstate M -> Prop}. 

  Global Instance fl_EI_dec: EqDecision fl_EI. 
  Proof using. solve_decision. Qed. 

  Global Instance fl_EI_cnt: Countable fl_EI. 
  Proof using.
    assert (Countable (fmrole M)) as CNTρ by apply _.
    eapply inj_countable' with 
      (f := fun ι => match ι with | flU ρ => inl ρ
                                | flL ρ => inr ρ end)
      (g := fun sn => match sn with | inl n => flU n
                            | inr n => flL n end).
    by destruct x. 
  Qed.

  Definition fl_ETs (ι: fl_EI) :=
    match ι with
    | flU ρ => au ρ
    | flL ρ => al ρ
    end.

  Context (fl_active_exts: fmstate M -> gset fl_EI).
  Context (fl_active_exts_spec: forall st ι, ι ∈ fl_active_exts st <-> ∃ st', fl_ETs ι st st'). 


  Definition FL_EM': ExtModel M.
    refine {| active_exts_spec := fl_active_exts_spec |}.
  Defined. 

End FairLockEM.


Class FairLockExt (M: FairModel) := {
  allows_unlock: fmrole M -> fmstate M -> fmstate M -> Prop;
  allows_lock: fmrole M -> fmstate M -> fmstate M -> Prop;
  fl_active_exts: fmstate M -> gset (@fl_EI M);
  fl_active_exts_spec: forall st ι, ι ∈ fl_active_exts st <-> ∃ st', (@fl_ETs _ allows_unlock allows_lock) ι st st';
}.


Definition FL_EM `(FLE: FairLockExt M) :=
  @FL_EM' M allows_unlock allows_lock fl_active_exts fl_active_exts_spec. 


Definition proj_role `{FLE: FairLockExt M}
  (eρ: @ext_role _ (FL_EM FLE)): fmrole M :=
  match eρ with 
  | inr (env (flL ρ))
  | inr (env (flU ρ))
  | inl ρ => ρ
  end.

Definition other_proj `{FLE: FairLockExt M} (ρ: fmrole M):
  (* (option $ @ext_role _ (FL_EM FLE)) *)
  (option $ fmrole $ @ext_model_FM _ (FL_EM FLE))
  -> Prop :=
  fun oeρ' => match oeρ' with
           | Some eρ' => proj_role eρ' ≠ ρ
           | None => True
           end. 


Class FairLock (M: FairModel) (FLP: FairLockPredicates M) (FLE: FairLockExt M) := {
  allow_unlock_impl: fmrole M -> fmstate M -> fmstate M;
  allow_lock_impl: fmrole M -> fmstate M -> fmstate M;
  allows_unlock_impl_spec ρ st
    :
    forall st', allows_unlock ρ st st' <->
             (allow_unlock_impl ρ st = st' /\ 
                has_lock_st ρ st /\ disabled_st ρ st
             );
  allows_lock_impl_spec ρ st:
    forall st', allows_lock ρ st st' <->
             (allow_lock_impl ρ st = st' /\ 
                can_lock_st ρ st /\ disabled_st ρ st);
    
  step_keeps_lock_dis: forall (ρ: fmrole M),
      label_kept_state
        (fun st => has_lock_st ρ st /\ disabled_st ρ st)
        (other_proj ρ (FLE := FLE))
        (M := @ext_model_FM _ (FL_EM FLE));

  step_keeps_unused: forall (ρ: fmrole M),
      label_kept_state
        (fun st => is_unused ρ st)
        (fun _ => True)
        (M := @ext_model_FM _ (FL_EM FLE));
  unused_can_lock_incompat: forall tl_st ρlg,
    is_unused ρlg tl_st -> can_lock_st ρlg tl_st -> False;
  unused_has_lock_incompat: forall tl_st ρlg,
    is_unused ρlg tl_st -> has_lock_st ρlg tl_st -> False;
  unused_active_incompat: forall tl_st ρlg,
    is_unused ρlg tl_st -> active_st ρlg tl_st -> False;
  unused_live_incompat: forall tl_st ρlg,
    is_unused ρlg tl_st -> active_st ρlg tl_st -> False;
  (* model_step_keeps_unused: forall st1 ρ st2, *)
  (*     fmtrans M st1 (Some ρ) st2 -> forall ρ', is_unused ρ' st1 <-> is_unused ρ' st2; *)
  (* ext_step_keeps_unused: forall st1 ρ st2 mkEI, *)
  (*     mkEI ∈ [flU; flL] -> @ETs _ (FL_EM FLE) (mkEI ρ) st1 st2 -> *)
  (*     forall ρ', is_unused ρ' st1 <-> is_unused ρ' st2; *)

  (* (* TODO: is it possible to get rid of this active_st - live_roles duplication? *) *)
  (* active_st_live: forall tl_st ρlg, *)
  (*     active_st ρlg tl_st -> ρlg ∈ live_roles _ tl_st; *)

  disabled_not_live: forall tl_st ρlg,
      disabled_st ρlg tl_st -> ρlg ∉ live_roles _ tl_st;

  has_lock_st_excl: forall tl_st ρlg1 ρlg2,
      has_lock_st ρlg1 tl_st -> has_lock_st ρlg2 tl_st -> ρlg1 = ρlg2;

  can_has_lock_incompat: forall tl_st ρlg,
    has_lock_st ρlg tl_st -> can_lock_st ρlg tl_st -> False;

  (* TODO: introduce more uniform treatment of ETs pre- and postconditions *)
  allows_unlock_spec: forall tl_st1 ρlg tl_st2,
    allows_unlock ρlg tl_st1 tl_st2 ->
    has_lock_st ρlg tl_st1 /\ disabled_st ρlg tl_st1 /\
    has_lock_st ρlg tl_st2 /\ active_st ρlg tl_st2;

  lock_progress: @fair_lock_progress _ FLP (FL_EM FLE);
}.


(* Lemma not_live_not_active `(@FairLock M FLP FLE): *)
(*   forall tl_st ρlg, ρlg ∉ live_roles _ tl_st -> ¬ active_st ρlg tl_st. *)
(* Proof.  *)
(*   intros. pose proof (active_st_live tl_st ρlg). tauto. *)
(* Qed. *)
