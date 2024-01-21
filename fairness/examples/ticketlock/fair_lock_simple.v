From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness Require Import trace_helpers.
(* TODO: rearrange the code *)
From trillium.fairness Require Import lemmas trace_len trace_lookup utils trace_helpers.
From trillium.fairness.ext_models Require Import ext_models.


Class FairLockPredicates (M: FairModel) := {
  does_lock: fmrole M -> fmstate M -> Prop;
  does_unlock: fmrole M -> fmstate M -> Prop;
  (* active_st: fmrole M -> fmstate M -> Prop; *)
  (* disabled_st: fmrole M -> fmstate M -> Prop; *)
  is_unused: fmrole M -> fmstate M -> Prop;
  (* state_wf: fmstate M -> Prop; *)
  (* is_unused := fun ρlg st => ¬ can_lock_st ρlg st /\ ¬ has_lock_st ρlg st; *)

  does_lock_st_dec :> forall ρ st, Decision (does_lock ρ st);
  does_unlock_st_dec :> forall ρ st, Decision (does_unlock ρ st);
  (* active_st_dec :> forall ρ st, Decision (active_st ρ st); *)
  (* disabled_st_dec :> forall ρ st, Decision (disabled_st ρ st); *)
  is_unused_dec :> forall ρ st, Decision (is_unused ρ st);
}.

(* TODO: legacy; remove *)
Definition active_st `{FLP: FairLockPredicates M} := @role_enabled_model M. 
Definition disabled_st `{FLP: FairLockPredicates M} :=
  fun ρ st => ¬ @role_enabled_model M ρ st.


Section FairLock.
  Context `{FL: FairLockPredicates M}. 
  Context {EM: ExtModel M}. 
  
  Let St := fmstate M.
  Let R := fmrole M.
  Let EFM := @ext_model_FM _ EM.

  Definition eventual_release (tr: mtrace EFM) (ρ: R) (i: nat) :=
    forall (ρ': R) j st' (JTH: tr S!! j = Some st')
      (HAS_LOCK: does_unlock ρ' st')
      (DIS: disabled_st ρ' st')
      (AFTER: i <= j -> (ρ' ≠ ρ /\ forall k st_k (BETWEEN: i <= k <= j) (KTH: tr S!! k = Some st_k), ¬ (does_unlock ρ st_k /\ disabled_st ρ st_k))),
      exists k st'', tr S!! k = Some st'' /\ j <= k /\ active_st ρ' st''.

  Lemma eventual_release_strenghten tr ρ i (EV_REL: eventual_release tr ρ i):
    forall (ρ': R) j st' (JTH: tr S!! j = Some st')
      (HAS_LOCK: does_unlock ρ' st')
      (* (DIS: ¬ role_enabled_model ρ' st') *)
      (DIS: disabled_st ρ' st')
      (AFTER: i <= j -> (ρ' ≠ ρ /\ forall k st_k (BETWEEN: i <= k <= j) (KTH: tr S!! k = Some st_k), ¬ (does_unlock ρ st_k /\ disabled_st ρ st_k))),
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
      
  (* Lemma ev_rel_after tr ρ i atr *)
  (*   (AFTER: after i tr = Some atr) *)
  (*   (EV_REL: eventual_release atr ρ 0): *)
  (*   eventual_release tr ρ i. *)
  (* Proof. *)
  (*   red. intros ρ' k **. red in EV_REL. *)
  (*   specialize_full EV_REL. *)
  (*   { erewrite state_lookup_after; eauto. } *)
  (*   all: eauto. *)
  (*   { intros LE. specialize_full AFTER0; [lia| ]. destruct AFTER0 as [? RESTR]. *)
  (*     split; auto. *)
  (*     intros. destruct BETWEEN as [[d ->]%Nat.le_sum LE2]. *)
  (*     eapply RESTR. *)
  (*     2: { erewrite state_lookup_after; eauto. } *)
  (*     lia. } *)
  (*   destruct EV_REL as (?&?&?&[d ->]%Nat.le_sum&?). *)
  (*   do 2 eexists. repeat split. *)
  (*   { erewrite state_lookup_after with (k := k + d); eauto. *)
  (*     by rewrite Nat.add_assoc. } *)
  (*   { lia. } *)
  (*   done. *)
  (* Qed. *)


  Lemma ev_rel_after tr ρ i atr
    (* j atr *)
    (EV_REL : eventual_release tr ρ i)
    (AFTER: after i tr = Some atr)
    :
    (* eventual_release atr ρ (i - j). *)
    eventual_release atr ρ 0.
  Proof.
    red. intros ρ' k **. red in EV_REL.
    specialize_full EV_REL.
    { erewrite state_lookup_after in JTH; eauto. }
    all: eauto.
    { intros LE. specialize_full AFTER0; [lia| ]. destruct AFTER0 as [? RESTR].
      split; auto.
      intros. destruct BETWEEN as [[d ->]%Nat.le_sum LE2].  
      eapply RESTR.
      2: { erewrite state_lookup_after; eauto. }
      lia. }
    destruct EV_REL as (?&?&?&[d ->]%Nat.le_sum&?).
    do 2 eexists. repeat split.
    { erewrite state_lookup_after with (k := k + d); eauto.
      by rewrite Nat.add_assoc. }
    { lia. }
    done.
  Qed. 

  Definition fl_lock_progress (fair: mtrace EFM -> Prop) :=
    forall (tr: mtrace EFM) (ρ: R) (i: nat) (st: St)
      (VALID: mtrace_valid tr)
      (* (FAIR: inner_fair_ext_model_trace tr) *)
      (FAIR: fair tr)
      (ITH: tr S!! i = Some st)
      (CAN_LOCK: does_lock ρ st)
      (ACT: active_st ρ st)
      (EV_REL: eventual_release tr ρ i),
    exists n st', i < n /\ tr S!! n = Some st' /\ does_unlock ρ st' /\ 
               (* ¬ role_enabled_model ρ st'. *)
               disabled_st ρ st'. 
  
  Definition fl_unlock_termination (fair: mtrace EFM -> Prop) :=
    forall (tr: mtrace EFM) (ρ: R) (i: nat) (st: St)
      (VALID: mtrace_valid tr)
      (FAIR: fair tr)
      (ITH: tr S!! i = Some st)
      (CAN_LOCK: does_unlock ρ st)
      (ACT: active_st ρ st),
    exists n st', i < n /\ tr S!! n = Some st' /\ does_lock ρ st' /\ 
               disabled_st ρ st'.

  (* Definition fl_trace_termination (fair: mtrace EFM -> Prop) := *)
  (*   forall (tr: mtrace EFM) *)
  (*     (VALID: mtrace_valid tr) *)
  (*     (FAIR: fair tr) *)
  (*     (EXT_BOUND: ext_trans_bounded tr) *)
  (*     (EV_REL: forall ρ i, eventual_release tr ρ i), *)
  (*     terminating_trace tr.  *)
  
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


Definition allows_unlock `{FLP: FairLockPredicates M} (ρ: fmrole M) (st1 st2: fmstate M): Prop :=
  does_unlock ρ st1 /\ disabled_st ρ st1 /\
  does_unlock ρ st2 /\ active_st ρ st2. 
  
Definition allows_lock `{FLP: FairLockPredicates M} (ρ: fmrole M) (st1 st2: fmstate M): Prop :=
  does_lock ρ st1 /\ disabled_st ρ st1 /\
  does_lock ρ st2 /\ active_st ρ st2. 
  

Class FairLockExt `{FLP: FairLockPredicates M} := {
  au_impl: fmrole M -> fmstate M -> fmstate M -> Prop;
  al_impl: fmrole M -> fmstate M -> fmstate M -> Prop;
  au_impl_spec: forall ρ st1 st2, au_impl ρ st1 st2 -> allows_unlock ρ st1 st2;
  al_impl_spec: forall ρ st1 st2, al_impl ρ st1 st2 -> allows_lock ρ st1 st2;
  fl_active_exts: fmstate M -> gset (@fl_EI M);
  fl_active_exts_spec: forall st ι, ι ∈ fl_active_exts st <-> ∃ st', (@fl_ETs _ au_impl al_impl) ι st st';
}.


Definition FL_EM `(FLE: FairLockExt M) :=
  @FL_EM' M au_impl al_impl fl_active_exts fl_active_exts_spec. 


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

Class FairLock (M: FairModel) (FLP: FairLockPredicates M) (FLE: @FairLockExt M FLP)
               (fair: emtrace (EM := (@FL_EM _ _ FLE)) -> Prop)
 := {
  allow_unlock_impl: fmrole M -> fmstate M -> fmstate M;
  allow_lock_impl: fmrole M -> fmstate M -> fmstate M;
  allows_unlock_impl_spec ρ st
    :
    forall st', au_impl ρ st st' <->
             (allow_unlock_impl ρ st = st' /\ 
                does_unlock ρ st /\ disabled_st ρ st
             );
  allows_lock_impl_spec ρ st:
    forall st', al_impl ρ st st' <->
             (allow_lock_impl ρ st = st' /\ 
                does_lock ρ st /\ disabled_st ρ st);
    
  step_keeps_unlock_dis: forall (ρ: fmrole M),
      label_kept_state
        (fun st => does_unlock ρ st /\ disabled_st ρ st)
        (* (other_proj ρ (FLE := FLE)) *)
        (fun oℓ => oℓ ≠ Some (inr (env ((@flU M ρ): @EI _ (@FL_EM _ _ FLE)))))
        (M := @ext_model_FM _ (FL_EM FLE));

  step_keeps_lock_dis: forall (ρ: fmrole M),
      label_kept_state
        (fun st => does_lock ρ st /\ disabled_st ρ st)
        (* (other_proj ρ (FLE := FLE)) *)
        (fun oℓ => oℓ ≠ Some (inr (env ((@flL M ρ): @EI _ (@FL_EM _ _ FLE)))))
        (M := @ext_model_FM _ (FL_EM FLE));

  step_keeps_unused: forall (ρ: fmrole M),
      label_kept_state
        (fun st => is_unused ρ st)
        (fun _ => True)
        (M := @ext_model_FM _ (FL_EM FLE));
  unused_does_lock_incompat: forall tl_st ρlg,
    is_unused ρlg tl_st -> does_lock ρlg tl_st -> False;
  unused_does_unlock_incompat: forall tl_st ρlg,
    is_unused ρlg tl_st -> does_unlock ρlg tl_st -> False;
  unused_active_incompat: forall tl_st ρlg,
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
      does_unlock ρlg1 tl_st -> disabled_st ρlg1 tl_st ->
      does_unlock ρlg2 tl_st -> disabled_st ρlg2 tl_st ->
      ρlg1 = ρlg2;

  does_lock_unlock_incompat: forall tl_st ρlg,
    does_lock ρlg tl_st -> does_unlock ρlg tl_st -> False;
  does_lock_unlock_trichotomy: forall tl_st ρlg,
    does_lock ρlg tl_st \/ does_unlock ρlg tl_st \/ is_unused ρlg tl_st;

  lock_progress: @fl_lock_progress _ FLP (FL_EM FLE) fair;
  unlock_termination: @fl_unlock_termination _ FLP (FL_EM FLE) fair;
  (* trace_termination: @fl_trace_termination _ FLP (FL_EM FLE) fair *)
}.

From trillium.fairness Require Import my_omega.
Lemma eventual_release_strenghten2 (M: FairModel) (FLP: FairLockPredicates M) 
  (FLE: FairLockExt )
  (* (fair: emtrace (EM := (@FL_EM _ _ FLE)) -> Prop)
     (FL: FairLock M FLP FLE fair) *)
  (UNLOCK_DIS_KEPT: forall (ρ: fmrole M),
      label_kept_state
        (fun st => does_unlock ρ st /\ disabled_st ρ st)
        (fun oℓ => oℓ ≠ Some (inr (env ((@flU M ρ): @EI _ (@FL_EM _ _ FLE)))))
        (M := @ext_model_FM _ (FL_EM FLE)))
  
  (LOCK_EXCL: forall tl_st ρlg1 ρlg2,
      does_unlock ρlg1 tl_st -> disabled_st ρlg1 tl_st ->
      does_unlock ρlg2 tl_st -> disabled_st ρlg2 tl_st ->
      ρlg1 = ρlg2)

  tr ρ i (EV_REL: eventual_release tr ρ i (FL := FLP) (EM := @FL_EM _ _ FLE)):
  forall (ρ': fmrole M) j st' (JTH: tr S!! j = Some st')
    (HAS_LOCK: does_unlock ρ' st' (FairLockPredicates := FLP))
    (DIS: disabled_st ρ' st')
    (AFTER: i <= j -> (ρ' ≠ ρ /\ forall k st_k (BETWEEN: i <= k <= j) (KTH: tr S!! k = Some st_k), ¬ (does_unlock ρ st_k /\ disabled_st ρ st_k)))
    (VALID: mtrace_valid tr)
  ,
  exists k st1 st2,
    j <= k /\
    tr !! k = Some (st1, Some (Some (inr (env ((@flU M ρ'): @EI _ (@FL_EM _ _ FLE)))), st2)). 
Proof using.
  intros. 
  eapply eventual_release_strenghten in EV_REL; eauto.
  destruct EV_REL as (p & [(δ_p & PTH & LEm & ENp) MIN]).

  pose proof (trace_has_len tr) as [len LEN].

  apply Nat.le_lteq in LEm as [LTm | ->].  
  2: { congruence. }

  destruct p as [| p]; [lia| ]. 
  forward eapply trace_lookup_dom_strong with (i := p); eauto. intros KTH%proj2.
  specialize_full KTH.
  { eapply mk_is_Some, state_lookup_dom in PTH; eauto. lia_NO' len. }
  destruct KTH as (st & ℓ & st_ & KTH).
  exists p. repeat eexists.
  { lia. }
  rewrite KTH. repeat f_equal. 
  
  apply state_label_lookup in KTH as (KTH & KTH' & LBL).
  rewrite Nat.add_1_r PTH in KTH'. inversion KTH'. subst δ_p. clear KTH'.

  assert (¬ active_st ρ' st) as DIS'.
  { intros ACT.
    specialize_full MIN.
    { exists st. eauto. repeat split; eauto. lia. }
    lia. }
  
  forward eapply trace_valid_steps'' as STEP; eauto.
  { rewrite Nat.add_1_r. eauto. }
  simpl in STEP.

  forward eapply steps_keep_state.
  3: { apply UNLOCK_DIS_KEPT. }
  { eauto. }
  { simpl. eauto. }
  3: { apply KTH. }
  2: { split; [| reflexivity]. lia. }
  { intros c **. simpl. intros ->.
    enough (S p <= c + 1); [lia| ]. apply MIN.
    apply trace_label_lookup_simpl' in H as (?&?&CTH).
    apply state_label_lookup in CTH as (?&?&?). 
    eexists. repeat split; eauto. 
    { lia. }
    forward eapply trace_valid_steps'' with (i := c) as STEPc; eauto.
    simpl in STEPc. inversion STEPc; subst.    
    simpl in REL. apply FLE in REL. apply REL. }
  intros [UNLOCKp DISp].

  inversion STEP; subst.
  { forward eapply (UNLOCK_DIS_KEPT ρ' st); eauto.
    { done. }
    intros [? DIS_]. red in DIS_. done. } 
  repeat f_equal.

  destruct ι; f_equal; simpl in REL. 
  - eapply (LOCK_EXCL st); eauto. all: apply FLE in REL; apply REL.
  - forward eapply (UNLOCK_DIS_KEPT ρ' st); eauto.
    { done. }
    intros [? DIS'']. red in DIS''. done.
Qed. 


Section FairLockProperties.
  Context `{FL: FairLock}.

  Lemma disabled_mtrans_kept (ρ: fmrole M):
    label_kept_state (disabled_st ρ) is_Some.
  Proof. 
    red. intros.
    red in Poℓ. destruct Poℓ as [? ->].
    destruct (decide (is_unused ρ st)) as [UN | US]. 
    { eapply step_keeps_unused in UN. specialize_full UN; [done| ..].
      { left. eauto. }
      red. intros ?. eapply unused_active_incompat; eauto. }
          
    destruct (does_lock_unlock_trichotomy st ρ) as [L | [U | UN]].
    3: { eapply step_keeps_unused in UN. specialize_full UN; [done| ..].
         { left. eauto. }
         red. intros ?. eapply unused_active_incompat; eauto. }
    1: eapply step_keeps_lock_dis. 4: eapply step_keeps_unlock_dis. 
    all: eauto.
    2, 4: by left; eauto.
    all: congruence. 
  Qed.

End FairLockProperties.
