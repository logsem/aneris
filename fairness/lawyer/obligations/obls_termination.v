Require Import Coq.Program.Wf.
Require Import Relation_Operators.
(* From stdpp Require Import namespaces. *)
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len my_omega.
From trillium.fairness.lawyer.obligations Require Import obligations_model multiset_utils obls_utils wf_utils obls_pf.
From stdpp Require Import relations.


Section Termination.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP.

  Context (tr: obls_trace OP).
  Hypothesis (VALID: obls_trace_valid OP tr). 
  Hypothesis (WF: forall i δ, tr S!! i = Some δ -> om_st_wf OP δ).
  
  Hypothesis (LVL_WF: wf (strict lvl_le)).
  
  Context `{Inhabited Level}. 
  Let lvl__def := @inhabitant Level _.

  Definition sig_val_at sid i := 
    from_option (fun δ => from_option snd true (ps_sigs _ δ !! sid)) true (tr S!! i). 
    
  Definition never_set_after sid c := 
    forall i, c <= i -> sig_val_at sid i = false.

  (* TODO: get rid of excessive negations *)
  Definition eventually_set sid :=
    forall c, ¬ never_set_after sid c.

  Definition sb_prop sid n := 
    forall i, eventually_set sid -> n <= i -> sig_val_at sid i = true. 

  Context {set_before: SignalId -> nat}.
  Hypothesis (SET_BEFORE_SPEC: forall sid, sb_prop sid (set_before sid)). 
  
  Definition lvl_at (sid_i: SignalId * nat): Level :=
    let '(sid, i) := sid_i in
    from_option (fun δ => from_option fst lvl__def (ps_sigs _ δ !! sid)) lvl__def (tr S!! i).

  Definition tr_sig_lt: relation (SignalId * nat) := MR (strict lvl_le) lvl_at. 
  
  Lemma tr_sig_lt_wf: wf tr_sig_lt.
  Proof using LVL_WF. apply measure_wf. apply LVL_WF. Qed.
  
  Lemma never_set_after_after sid i j
    (LE: i <= j):
    never_set_after sid i -> never_set_after sid j.
  Proof using.
    rewrite /never_set_after. intros NEVER m LE'.
    eapply NEVER. lia. 
  Qed.

  Definition phase_ge := flip phase_le. 
  Definition PF (π: Phase) := PF' OP set_before (phase_ge π).
  Definition TPF (π: Phase) := TPF' OP tr set_before (phase_ge π).

  (* TODO: move *)
  Let π0: Phase := nil. 

  Lemma other_expect_ms_le π__ow δ1 τ δ2 k
    (OTHER: let π := default π0 (ps_phases _ δ1 !! τ) in
            (* phases_incompat π__ow π *)
            phases_disj π__ow π
    ):
    expect_ms_le OP set_before (phase_ge π__ow) δ1 τ δ2 k. 
  Proof using.
    clear LVL_WF SET_BEFORE_SPEC WF VALID.
    red. intros sid π' d EXP. 
    rewrite /PF /PF'.
    inversion EXP; subst.
    destruct δ1. simpl in *.
    subst new_cps0.
    
    rewrite !mset_filter_disj_union mset_map_disj_union.
    rewrite !mset_filter_singleton.
    rewrite decide_False.
    2: { rewrite LOC_PHASE in OTHER. simpl in OTHER.
         eapply phases_disj_not_le; eauto. by symmetry. }
    
    rewrite mset_map_empty. apply ms_le_disj_union.
    + eapply ms_le_Proper; [reflexivity| | reflexivity]. mss.
    + apply ms_le_exp_mono; [lia | reflexivity].
  Qed.

  Lemma min_owner_expect_ms_le δ1 τ δ2 k
    (SET_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                           let n := (LIM_STEPS + 2) * set_before sid in
                           k < n)
    :
    let π__ow := default π0 (ps_phases _ δ1 !! τ) in
    expect_ms_le OP set_before (phase_ge π__ow) δ1 τ δ2 k. 
  Proof using.
    clear LVL_WF SET_BEFORE_SPEC WF VALID.
    intros. red. intros sid π' d EXP. 
    rewrite /PF /PF'.
    
    inversion EXP; subst.
    destruct δ1. simpl in *. subst new_cps0.
    subst π__ow. rewrite LOC_PHASE. simpl. 
    
    rewrite !mset_filter_disj_union mset_map_disj_union.
    rewrite !mset_filter_singleton.
    rewrite decide_True; [| red; reflexivity].
    rewrite mset_map_singleton. simpl. 
    
    rewrite -gmultiset_disj_union_assoc. apply ms_le_disj_union.
    { apply ms_le_refl. }
    rewrite (union_difference_singleton_L _ _ EP).
    
    rewrite filter_union_L.
    rewrite !gset_singleton_if_equiv.
    rewrite decide_True; [| tauto].
    
    rewrite (union_comm_L {[ _ ]} _).
    rewrite !approx_expects_add.
    2, 3: set_solver.
    simpl. rewrite gmultiset_disj_union_comm.
    rewrite -gmultiset_disj_union_assoc.
    apply ms_le_disj_union.
    { apply ms_le_exp_mono; [lia | reflexivity]. }
    
    move SET_BOUND at bottom. specialize_full SET_BOUND; [by eauto| ].
    eapply ms_le_Proper; [reflexivity| ..| apply ms_le_refl].
    rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.
  Qed.

  (* TODO: move *)
  Lemma exist_impl_forall {A: Type} {P: A -> Prop} {Q: Prop}:
    ((exists x, P x) -> Q) <-> (forall x, P x -> Q).
  Proof using.
    clear -A. 
    split.
    - intros PQ x Px. eauto.
    - intros PQ [x Px]. eauto.
  Qed. 

  (* TODO: move *)
  Lemma obls_assigned_equiv δ:
    obls_assigned OP δ <-> 
      forall s l, ps_sigs _ δ !! s = Some (l, false) ->
      map_Exists (fun τ obs => s ∈ obs) (ps_obls _ δ).
  Proof using.
    clear -π0. 
    rewrite /obls_assigned. rewrite elem_of_subseteq.
    apply forall_proper. intros s.
    rewrite elem_of_dom.
    rewrite map_filter_lookup. simpl. 
    destruct (ps_sigs _ δ !! s) as [[??]| ] eqn:SIGS; rewrite SIGS; simpl. 
    2: { split; intros; try done. by destruct H1. }
    destruct b; simpl. 
    { simpl. split; intros; try done. by destruct H1. }
    rewrite -exist_impl_forall. rewrite ex_det_iff.
    2: { intros ? [=]. subst. reflexivity. }
    apply ZifyClasses.impl_morph; [set_solver| ].
    rewrite flatten_gset_spec. rewrite map_Exists_lookup.
    setoid_rewrite elem_of_map_img. set_solver.
  Qed.

  Lemma never_set_after_eq_false sid c:
    never_set_after sid c -> forall i, c <= i -> 
      exists δ l, tr S!! i = Some δ /\ ps_sigs _ δ !! sid = Some (l, false).
  Proof using.
    intros NEVER i LE.
    red in NEVER. specialize (NEVER _ LE).
    rewrite /sig_val_at in NEVER. destruct (tr S!! i) eqn:ITH; [| done].
    simpl in *.
    destruct (ps_sigs _ m !! sid) as [[??]|] eqn:SIG; try done.
    simpl in NEVER. subst. eauto. 
  Qed. 

  Lemma never_set_owned s c
    (NEVER_SET: never_set_after s c):
    forall i, c <= i ->
         map_Exists (fun τ obs => s ∈ obs) (from_option (ps_obls _) ∅ (tr S!! i)). 
  Proof using WF.
    intros i LE.
    eapply never_set_after_eq_false in NEVER_SET as (?&?&ITH&?); eauto.
    rewrite ITH. simpl.
    eapply obls_assigned_equiv; eauto. 
    eapply WF; eauto.
  Qed.

  (* TODO: move *)
  Section MoreWF.

    Definition sig_st_le (st1 st2: option $ @SignalState Level) :=
      match st1, st2 with
      | Some (l1, b1), Some (l2, b2) => l1 = l2 /\ bool_le b1 b2
      | None, _ => True
      | _, _ => False
      end.    

    Lemma loc_step_sig_st_le_pres τ sid st: 
      preserved_by OP (loc_step_of OP τ) (fun δ => sig_st_le st (ps_sigs _ δ !! sid)).
    Proof using.
      do 2 red. intros δ1 δ2 SIG_LE STEP.
      pose proof (next_sig_id_fresh _ δ1) as FRESH.  
      inv_loc_step STEP; destruct δ1; try done; simpl in *.
      - subst new_sigs0.
        destruct (decide (sid = s0)) as [-> | ?].
        2: { rewrite lookup_insert_ne. apply SIG_LE. done. }
        rewrite lookup_insert.
        apply not_elem_of_dom_1 in FRESH. rewrite FRESH in SIG_LE.
        by destruct st as [[??]|]; done.
      - subst new_sigs0.
        destruct (decide (sid = x)) as [-> | ?].
        2: { rewrite lookup_insert_ne; [| done]. apply SIG_LE. }
        rewrite lookup_insert.
        rewrite SIG in SIG_LE. destruct st as [[??]| ]; try done.
        simpl in SIG_LE. destruct SIG_LE as [-> ?].
        split; auto. destruct b; done.
    Qed.

    Lemma fork_step_sig_st_le_pres τ sid st:
      preserved_by OP (fork_step_of OP τ) (fun δ => sig_st_le st (ps_sigs _ δ !! sid)).
    Proof using. 
      do 2 red. intros δ1 δ2 SIG_LE STEP.
      red in STEP. destruct STEP as (?&?&STEP). 
      inversion STEP; destruct δ1; done.
    Qed.

    Lemma sig_st_le_refl ost:
      sig_st_le ost ost.
    Proof using.
      destruct ost as [[??]|]; done.
    Qed.

    Lemma sig_st_le_lookup_helper i j δi δj s
      (LE: i <= j)
      (ITH: tr S!! i = Some δi)
      (JTH: tr S!! j = Some δj):
      sig_st_le (ps_sigs _ δi !! s) (ps_sigs _ δj !! s).
    Proof using VALID.
      forward eapply pres_by_valid_trace; eauto.
      { intros. apply loc_step_sig_st_le_pres with (sid := s). }
      { intros. apply fork_step_sig_st_le_pres. }
      { rewrite ITH. simpl. apply sig_st_le_refl. }
      by rewrite JTH.
    Qed.       

    Lemma loc_steps_rep_phase_exact_pres δ1 τs δ2 τ oπ k
      (PH: ps_phases _ δ1 !! τ = oπ)
      (STEPS: nsteps (loc_step_of _ τs) k δ1 δ2):
      ps_phases _ δ2 !! τ = oπ.
    Proof using.
      forward eapply pres_by_loc_step_implies_rep.
      { apply loc_step_phases_pres. }
      intros P. red in P. rewrite /preserved_by in P. specialize_full P; eauto.
      { reflexivity. }
      red in P. rewrite P. done.
    Qed. 

    Lemma phases_not_le δ (WF0: om_st_wf _ δ) τ1 τ2 π1 π2
      (P1: ps_phases _ δ !! τ1 = Some π1)
      (P2: ps_phases _ δ !! τ2 = Some π2)
      (PH_LE: phase_le π1 π2):
      τ1 = τ2 /\ π1 = π2.
    Proof using.
      destruct (decide (τ1 = τ2)) as [-> | ?].
      { rewrite P1 in P2. inversion P2. done. }
      edestruct (om_wf_ph_disj _ δ); eauto. tauto. 
    Qed.

    Lemma other_loc_step_pres_obls τ R τs
      (OTHER: τs ≠ τ):
      preserved_by _ (loc_step_of _ τs) (fun δ => ps_obls _ δ !! τ = Some R /\ om_st_wf _ δ).
    Proof using.
      red. intros δ1 δ2 [OB WF1] STEP.
      split.
      2: { eapply wf_preserved_by_loc_step; eauto. } 
      inv_loc_step STEP; destruct δ1; try done; simpl in *.
      - subst new_obls0. rewrite lookup_insert_ne; done.
      - subst new_obls0. rewrite lookup_insert_ne; done.
    Qed.

    Lemma other_fork_step_pres_obls' τ R τs
      (OTHER: τs ≠ τ):
      preserved_by _ (fork_step_of _ τs) (fun δ => ps_obls _ δ !! τ = Some R /\ om_st_wf _ δ).
    Proof using.
      red. intros ?? [OB WF1] (?&?&STEP).
      split.
      2: { eapply wf_preserved_by_fork_step; eauto. red. eauto. }
      inversion STEP. subst. destruct δ1; simpl in *.
      subst new_obls0.
      rewrite lookup_insert_ne.
      2: { intros ->. destruct FRESH'.
           apply om_wf_dpo in WF1. rewrite WF1. 
           by eapply elem_of_dom. }
      rewrite lookup_insert_ne; done. 
    Qed.  

    (* Context `(STEP: om_trans OP δ1 τ δ2). *)
    Context (δ1 δ2: ProgressState OP).    
    Context (WF1: om_st_wf _ δ1).

    Lemma om_step_wf_dom τ (LOC_STEP: loc_step OP δ1 τ δ2):
      τ ∈ dom $ ps_obls _ δ1.
    Proof using WF1.
      enough (τ ∈ dom $ ps_obls _ δ1 \/ τ ∈ dom $ ps_phases _ δ1 \/
              is_Some (ps_obls _ δ1 !! τ) \/ is_Some (ps_phases _ δ1 !! τ)) as IN.
      { rewrite -!elem_of_dom in IN. rewrite om_wf_dpo in IN; eauto. tauto. }
      inv_loc_step LOC_STEP; eauto.
    Qed.

  End MoreWF.

  Lemma other_om_trans_ms_le πτ τ n
    (PH: from_option (fun δ => ps_phases _ δ !! τ = Some πτ) False (tr S!! n))
    (NOτ: tr L!! n ≠ Some τ):
    ms_le deg_le (TPF πτ (S n)) (TPF πτ n).
  Proof using WF VALID.
    destruct (tr S!! (S n)) as [δ'| ] eqn:NEXT.
    2: { rewrite /TPF /TPF'. rewrite NEXT. simpl. apply empty_ms_le. }
    
    eapply om_trans_ms_rel with (bd := false); auto.
    { intros.
      rewrite Nat.add_succ_r. rewrite Nat.add_0_r.  
      destruct H4 as (?&?&?). eapply burns_cp_ms_le; eauto. }
    
    (* TODO: extract the lemma below? *)
    
    intros τ' IDTHl. 
    red. intros δk δk' mb mf k ITH BOUND NSTEPS BSTEP FSTEP. 
    rewrite IDTHl in NOτ.
    assert (τ' ≠ τ) as X by (by intros ->). clear NOτ. rename X into NOτ. 

    clear BSTEP. 
    generalize dependent mb. induction k.
    { intros ? ->%obls_utils.nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    clear δ' NEXT. 
    intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
    specialize (IHk ltac:(lia) _ STEPS).
    etrans; eauto.

    eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
    { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
    apply other_expect_ms_le. simpl.

    assert (om_st_wf OP δ') as WF'.
    { eapply pres_by_loc_step_implies_rep; eauto. 
      { apply wf_preserved_by_loc_step. }
      apply (WF n). by apply state_label_lookup in ITH as (?&?&?). }
    
    assert (exists π', ps_phases _ δ' !! τ' = Some π') as [π' PH'].
    { apply om_step_wf_dom in STEP; [| done]. 
      rewrite -om_wf_dpo in STEP; [| done]. eapply elem_of_dom in STEP; eauto. }
    rewrite PH'. simpl.

    apply state_label_lookup in ITH as (IDTH & ? & ?).
    rewrite IDTH in PH. simpl in PH. 

    symmetry. eapply (om_wf_ph_disj _ δ'); eauto.
    eapply loc_steps_rep_phase_exact_pres; eauto.    
  Qed.

  Lemma loc_step_pres_phase_eq τ π τs:
    preserved_by _ (loc_step_of _ τs) (fun δ => ps_phases _ δ !! τ = Some π).
  Proof using.
    red. intros ?? PH STEP.
    eapply loc_step_phases_pres in STEP; [| reflexivity].
    by rewrite STEP.
  Qed. 
    
  Lemma other_fork_step_pres_phase_eq τ π τs
    (OTHER: τs ≠ τ):
    preserved_by _ (fork_step_of _ τs) (fun δ => ps_phases _ δ !! τ = Some π).
  Proof using.
    red. intros ?? PH (?&?&STEP).
    inversion STEP. subst. destruct δ1; simpl in *.
    subst new_phases0.
    rewrite lookup_insert_ne.
    2: { intros ->. destruct FRESH'. by eapply elem_of_dom. }
    rewrite lookup_insert_ne; done. 
  Qed.  
    
  Lemma next_step_rewind τ π i δ0 j
    (ITH: tr S!! i = Some δ0)
    (PH: ps_phases _ δ0 !! τ = Some π)
    (LE: i <= j)
    (NOτ: forall k, i <= k < j -> tr L!! k ≠ Some τ):
    ms_le deg_le (TPF π j) (TPF π i).
  Proof using WF VALID.
    clear SET_BEFORE_SPEC LVL_WF. 
    apply Nat.le_sum in LE as [d ->]. induction d.
    { rewrite Nat.add_0_r. reflexivity. }
    specialize_full IHd.
    { intros. apply NOτ. lia. }
    etrans; eauto.
    rewrite -plus_n_Sm.
    
    destruct (tr S!! (S (i + d))) as [δ'| ] eqn:NEXT.
    2: { rewrite /TPF /TPF'. rewrite NEXT. simpl. apply empty_ms_le. }
    forward eapply (state_lookup_prev _ _ ltac:(eauto) _ (PeanoNat.Nat.le_succ_diag_r _)).
    intros [δ IDTH].
    
    eapply other_om_trans_ms_le; eauto.
    2: { specialize (NOτ (i + d) ltac:(lia)). done. }
    rewrite IDTH. simpl. 
    
    forward eapply (pres_by_valid_trace_strong _ tr i (i + d)). 
    4: { apply (other_fork_step_pres_phase_eq τ π). }
    3: { intros. apply (loc_step_pres_phase_eq τ π). }
    all: try done. 
    { lia. }
    { rewrite ITH. done. }
    { intros. simpl. specialize (NOτ k). specialize_full NOτ; eauto.
      { lia. }
      rewrite H2 in NOτ. set_solver. }
    by rewrite IDTH.
  Qed.

  (* TODO: move *)
  Lemma clos_refl_nsteps {A: Type} (R: relation A) x y
    (CR: clos_refl _ R x y):
    exists n, nsteps R n x y.
  Proof using.
    inversion CR; subst.
    - exists 1. by apply nsteps_1.
    - exists 0. by apply nsteps_0.
  Qed.                          
    
  Lemma signal_false_between δ1 δ2 δ' s l n m τ
    (F1: ps_sigs _ δ1 !! s = Some (l, false))
    (F2: ps_sigs _ δ2 !! s = Some (l, false))
    (STEPS1: nsteps (obls_any_step_of _ τ) n δ1 δ')
    (STEPS2: nsteps (obls_any_step_of _ τ) m δ' δ2):
    ps_sigs _ δ' !! s = Some (l, false).
  Proof using.
    forward eapply pres_by_rel_implies_rep.
    { apply pres_by_loc_fork_steps_implies_any_pres.
      - apply (loc_step_sig_st_le_pres τ s).
      - apply fork_step_sig_st_le_pres. }    
    intros SIG1. red in SIG1. specialize_full SIG1.
    2: { apply STEPS1. }
    { rewrite F1. apply sig_st_le_refl. } 

    forward eapply pres_by_rel_implies_rep.
    { apply pres_by_loc_fork_steps_implies_any_pres.
      - apply (loc_step_sig_st_le_pres τ s).
      - apply fork_step_sig_st_le_pres. }    
    intros SIG2. red in SIG2. specialize_full SIG2.
    2: { apply STEPS2. }
    { apply sig_st_le_refl. }
    rewrite F2 in SIG2.

    destruct (ps_sigs OP δ' !! s) as [[??]| ]; try done.
    simpl in SIG1, SIG2. destruct SIG1, SIG2; subst.
    destruct b; tauto.
  Qed.     

  (* TODO: rephrase in terms of preserved_by? *)
  Lemma expected_signal_created_before δ1 δ2 τ n sid l
    (NSTEPS: nsteps (loc_step_of _ τ) n δ1 δ2)
    (SIG2: ps_sigs _ δ2 !! sid = Some (l, false))
    (LT2: lt_locale_obls _ l τ δ2):
    ps_sigs _ δ1 !! sid = Some (l, false).
  Proof using.
    clear WF VALID SET_BEFORE_SPEC LVL_WF set_before.
    assert (sid ∉ default ∅ (ps_obls OP δ2 !! τ)) as NO2.
    { intros IN2. 
      destruct (ps_obls OP δ2 !! τ) eqn:OBLS2; [| done]. simpl. 
      do 2 red in LT2. specialize (LT2 l).
      rewrite OBLS2 in LT2. simpl in LT2.
      specialize_full LT2.
      2: { by apply strict_ne in LT2. }
      apply extract_Somes_gset_spec.
      apply elem_of_map. eexists. split; eauto.
      by rewrite SIG2. }
    clear LT2. generalize dependent δ2. induction n.
    { by intros ? ->%nsteps_0. }
    intros δ2 (δ' & STEPS & STEP)%rel_compose_nsteps_next SIG2 NO2.
    forward eapply (loc_step_sig_st_le_pres τ sid).
    intros LE'. red in LE'. specialize_full LE'; [| eauto |]. 
    { apply sig_st_le_refl. }
    rewrite SIG2 in LE'.

    assert (ps_sigs OP δ' !! sid = Some (l, false)) as SIG'.
    { destruct (ps_sigs OP δ' !! sid) as [[??]| ] eqn:SIG'.
      { simpl in LE'. destruct LE' as [??]. subst. destruct b; tauto. }
      clear dependent δ1. 
      red in STEP.
      inv_loc_step STEP; destruct δ'; simpl in *; subst.
      + by rewrite SIG2 in SIG'.
      + by rewrite SIG2 in SIG'.
      + subst new_sigs0. rewrite lookup_insert_ne in SIG2.
        { by rewrite SIG2 in SIG'. }
        intros ->. subst new_obls0.
        destruct NO2. rewrite lookup_insert. simpl. set_solver.
      + subst new_sigs0. rewrite lookup_insert_ne in SIG2.
        { by rewrite SIG2 in SIG'. }       
        intros ->. by rewrite SIG' in SIG.
      + by rewrite SIG2 in SIG'.
      + by rewrite SIG2 in SIG'. }
    clear LE'. 

    eapply IHn; eauto.
    destruct (ps_obls OP δ' !! τ) eqn:OBLS'; [| done]. simpl. intros IN'.
    inv_loc_step STEP; destruct δ'; simpl in *; subst. 
    + by rewrite OBLS' in NO2. 
    + by rewrite OBLS' in NO2.
    + subst new_sigs0 new_obls0.
      destruct NO2. subst cur_loc_obls0. rewrite OBLS' lookup_insert. set_solver.
    + subst new_sigs0 new_obls0.
      subst cur_loc_obls0.
      destruct (decide (x = sid)) as [-> | ?].
      { rewrite lookup_insert in SIG2. done. }
      rewrite lookup_insert_ne in SIG2; [| done].
      destruct NO2. rewrite OBLS'. simpl. rewrite lookup_insert. simpl. set_solver.
    + rewrite OBLS' in NO2. done.
    + rewrite OBLS' in NO2. done. 
  Qed.

  Definition asg_bound sid πb δ :=
    (* map_Forall (fun _ obls_ => sid ∉ obls_) (ps_obls _ δ) \/ *)
    (exists l, ps_sigs _ δ !! sid = Some (l, true)) \/
    exists τ π, sid ∈ default ∅ (ps_obls _ δ !! τ) /\
            ps_phases _ δ !! τ = Some π /\
            phase_le πb π.

  Lemma loc_step_pres_asg_bound sid πb τ:
    preserved_by _ (loc_step_of _ τ) (fun δ => asg_bound sid πb δ /\ om_st_wf _ δ).
  Proof using.
    clear set_before WF SET_BEFORE_SPEC LVL_WF VALID.

    red. intros δ1 δ2 [AB WF1] STEP.
    split; [| by eapply wf_preserved_by_loc_step].

    destruct AB as [SET | AB].
    { destruct SET as [l SID]. red.
      left. eapply (loc_step_sig_st_le_pres _ sid) in STEP.
      2: { apply sig_st_le_refl. }
      rewrite SID in STEP.
      destruct (ps_sigs OP δ2 !! sid) as [[??]|] eqn:ST; try done.
      simpl in STEP. destruct STEP as [-> ?]. 
      destruct b; try done. eauto. }

    red. 
    inv_loc_step STEP; destruct δ1; try (right; done); simpl in *.
    - right. subst new_obls0.
      destruct AB as (?&?&?&?&?).
      destruct (decide (sid = s0)) as [-> | OLD].
      + edestruct @next_sig_id_fresh.
        eapply om_wf_obls_are_sigs; eauto. simpl.
        eapply flatten_gset_spec. eexists. split; eauto.
        eapply elem_of_map_img; eauto.
        apply om_wf_dpo in WF1.
        apply mk_is_Some, elem_of_dom in H2.
        red in WF1. rewrite WF1 in H2. simpl in H2. apply elem_of_dom in H2 as [??].
        exists x0. rewrite H2. done.
      + subst new_ps. 
        destruct (decide (x0 = τ)) as [-> | NEQ].
        * exists τ. rewrite lookup_insert. simpl. eexists. split; eauto.
          set_solver.
        * exists x0. rewrite lookup_insert_ne; [| done]. eauto.
    - destruct (decide (x = sid)) as [-> | NEQ].
      { left. subst new_sigs0. rewrite lookup_insert. eauto. }
      right. move AB at bottom. destruct AB as (?&?&?&?&?).
      destruct (decide (x0 = τ)) as [-> | NEQ'].
      + exists τ. rewrite lookup_insert. simpl. eexists. split; eauto.
        set_solver.
      + exists x0. rewrite lookup_insert_ne; [| done]. eauto.
  Qed.

  Lemma fork_step_pres_asg_bound sid πb τ:
    preserved_by _ (fork_step_of _ τ) (fun δ => asg_bound sid πb δ /\ om_st_wf _ δ).
  Proof using.
    clear tr set_before WF SET_BEFORE_SPEC LVL_WF VALID.

    red. intros δ1 δ2 [AB WF1] STEP.
    split.
    2: { eapply wf_preserved_by_fork_step; eauto. }

    destruct AB as [SET | AB].
    { destruct SET as [l SID]. red.
      left. eapply (fork_step_sig_st_le_pres _ sid) in STEP.
      2: { apply sig_st_le_refl. }
      rewrite SID in STEP.
      destruct (ps_sigs OP δ2 !! sid) as [[??]|] eqn:ST; try done.
      simpl in STEP. destruct STEP as [-> ?]. 
      destruct b; try done. eauto. }

    destruct STEP as (?&?&STEP). inversion STEP; subst. red. right.
    move AB at bottom. destruct AB as (?&?&?&?&?).
    destruct δ1; try (right; done); simpl in *.
    subst new_obls0 cur_obls0 obls' new_phases0. 
    destruct (decide (x1 = τ)) as [-> | NEQ'].
    2: { exists x1, x2. rewrite lookup_insert_ne.
         2: { intros <-. destruct FRESH'. by apply elem_of_dom. }
         rewrite lookup_insert_ne; [| done].
         rewrite lookup_insert_ne. 
         2: { intros <-. destruct FRESH'. by apply elem_of_dom. }
         rewrite lookup_insert_ne; [| done].
         eauto. }
    rewrite LOC_PHASE in H2. inversion H2. subst x2. 
    destruct (decide (sid ∈ cur_obls ∩ x0)).
    { exists x. rewrite !lookup_insert. simpl. eexists. split; eauto.
      split; eauto. etrans; eauto. apply phase_lt_fork. }
    exists τ. eexists. rewrite lookup_insert_ne.
    2: { intros ->. destruct FRESH'. by apply elem_of_dom. }
    rewrite lookup_insert. simpl. 
    rewrite lookup_insert_ne.
    2: { intros ->. destruct FRESH'. by apply elem_of_dom. }
    rewrite lookup_insert. simpl.
    split; [set_solver|  ]. split; eauto.
    etrans; eauto. apply phase_lt_fork.
  Qed. 

  Lemma owm_om_trans_ms_lt πτ τ n s δ0
    (NTH: tr S!! n = Some δ0)
    (PH: ps_phases _ δ0 !! τ = Some πτ)
    (NEVER_SET : never_set_after s n)
    (MIN: minimal_in_prop tr_sig_lt (s, n) (λ sn, never_set_after sn.1 sn.2 /\ n <= sn.2))
    (OWNER: s ∈ default ∅ (ps_obls _ δ0 !! τ))
    (LBL: tr L!! n = Some τ):
    ms_lt deg_le (TPF πτ (S n)) (TPF πτ n).
  Proof using VALID WF SET_BEFORE_SPEC.
    clear LVL_WF. 
    forward eapply (proj1 (label_lookup_states' _ _)); eauto. intros [δ' NTH']. 
    
    eapply om_trans_ms_rel with (bd := true); auto.
    { intros.
      rewrite Nat.add_succ_r Nat.add_0_r.
      apply state_label_lookup in H1 as (NTH_&?&LBL_).
      rewrite LBL in LBL_. inversion LBL_. subst τ0. 
      rewrite NTH in NTH_. inversion NTH_. subst δ0. 
      destruct H4 as (?&?&?).
      
      inversion H4. subst. 
      assert (ps_phases _ mb !! τ = Some πτ) as PH'.
      { eapply loc_steps_rep_phase_exact_pres; eauto. }
      rewrite LOC_PHASE in PH'. inversion PH'. subst π__max.  
      
      eapply burns_cp_own_ms_lt with (πb := x); eauto. }
    
    (* TODO: extract the lemma below? *)
    
    clear δ' NTH'. 
    intros τ' IDTHl. 
    red. intros δk δk' mb mf k ITH BOUND NSTEPS BSTEP FSTEP.
    apply state_label_lookup in ITH as (IDTH & IDTH' & _). 
    rewrite NTH in IDTH. inversion IDTH. subst δ0. clear IDTH. 
    rewrite LBL in IDTHl. inversion IDTHl. subst τ'. clear IDTHl.

    (* destruct (ps_sigs OP δk !! s) as [[ls ?]|] eqn:SIG__min.  *)
    pose proof (never_set_after_eq_false _ _ NEVER_SET _ ltac:(reflexivity)) as X.
    destruct X as (?&ls&NTH_&SIGsn).
    rewrite NTH in NTH_. inversion NTH_. subst x.
    pose proof (never_set_after_eq_false _ _ NEVER_SET _ ltac:(apply Nat.le_succ_diag_r)) as X.
    destruct X as (?&?&NTH'_&SIGsn').
    rewrite -Nat.add_1_r IDTH' in NTH'_. inversion NTH'_. subst x.

    forward eapply sig_st_le_lookup_helper with (i := n) (j := n + 1) (s := s); eauto; [lia| ].
    rewrite SIGsn SIGsn'. simpl. intros [<- _].   

    apply clos_refl_nsteps in FSTEP as [r FSTEP]. 
    forward eapply signal_false_between; [apply SIGsn | apply SIGsn'| ..].
    { eapply nsteps_mono; [| apply NSTEPS].
      do 2 red. rewrite /obls_any_step_of. eauto. }
    { apply rel_compose_nsteps_next'. eexists. split. 
      - red. left. red. red. left. eauto.
      - eapply nsteps_mono; [| apply FSTEP].
        do 2 red. rewrite /obls_any_step_of. eauto. }
    intros SIGmb. 
 
    clear dependent mf. clear dependent δk'. 
    
    generalize dependent mb. induction k.
    { intros ? ->%obls_utils.nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    intros mb (δ' & STEPS & STEP)%nsteps_inv_r SF.

    assert (ps_sigs _ δ' !! s = Some (ls, false)) as SIG'.
    { eapply signal_false_between; [apply SIGsn | apply SF| ..].
      - eapply nsteps_mono; [| apply STEPS].
        do 2 red. rewrite /obls_any_step_of. eauto.
      - apply nsteps_1. left. eauto. }
    specialize (IHk ltac:(lia) _ STEPS ltac:(done)).
    etrans; eauto.
    eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
    { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
    
    assert (ps_phases _ δ' !! τ = Some πτ) as PHδ'.
    { eapply loc_steps_rep_phase_exact_pres; eauto. }
    
    replace πτ with (default π0 (ps_phases OP δ' !! τ)).
    2: { rewrite PHδ'. done. }
    
    apply min_owner_expect_ms_le. simpl.
    
    intros sid π d EXP. simpl.
    inversion EXP. subst.
    rewrite PHδ' in LOC_PHASE. inversion LOC_PHASE. subst π__max.
    
    enough (set_before sid > n).
    { apply PeanoNat.Nat.le_succ_l in H1. 
      apply Nat.le_sum in H1 as [u EQ]. rewrite EQ. lia. }
        
    move NEVER_SET at bottom. red in NEVER_SET.
    specialize (NEVER_SET _ ltac:(reflexivity)).
    rewrite /sig_val_at in NEVER_SET. rewrite NTH in NEVER_SET. simpl in NEVER_SET. 

    assert (s ∈ default ∅ (ps_obls _ δ' !! τ)) as OBL'.
    { unshelve eapply (pres_by_rel_implies_rep _ _ _ _ _ _ _) in STEPS.
      { apply (loc_step_pres_asg_bound s πτ). }
      2: { split.
           2: { eapply WF; eauto. }
           red. right. exists τ, πτ. set_solver. }           
      simpl in STEPS. destruct STEPS as [ASG' WF']. red in ASG'.
      destruct ASG' as [[? ?] | ]; [congruence| ].
      destruct H1 as (τ' & π' & IN' & PH' & LE').
      destruct (decide (τ' = τ)) as [| NEQ]; [congruence| ].
      eapply om_wf_ph_disj in NEQ; eauto.
      eapply phases_disj_not_le in LE'; [done| ].
      symmetry. eapply NEQ; eauto. }

    pose proof OBLS_LT as OL. 
    specialize (OBLS_LT ls). specialize_full OBLS_LT.
    { apply extract_Somes_gset_spec.
      destruct (ps_obls OP δ' !! τ) as [obs| ] eqn:OBLS'; [| set_solver].
      simpl in OBL'. simpl. apply elem_of_map. eexists. split; eauto.
      rewrite SIG'. done. }
    
    red. destruct (Nat.lt_ge_cases n (set_before sid)) as [?|GE]; [done| ].   
    
    (* either it was there when the big step started,
       or it's a new signal, but then the thread holds an obligation
       and cannot wait on it *)
    assert (ps_sigs OP δk !! sid = Some (l, false)) as SIG0.
    { eapply expected_signal_created_before; eauto. }
    
    pose proof (SET_BEFORE_SPEC sid n). specialize_full H1; [| done| ].
    2: { rewrite /sig_val_at in H1. 
         rewrite NTH in H1. simpl in H1.
         rewrite SIG0 in H1. done. }
    
    intros c NEVER_SET_.

    assert (never_set_after sid (max n c)) as NEVER_SET'.
    { eapply never_set_after_after; [| apply NEVER_SET_]. lia. } 
    clear NEVER_SET_.
    move MIN at bottom. red in MIN.

    (* specialize (MIN (_, _) NEVER_SET'). *)
    specialize (MIN (sid, (n `max` c)) ltac:(split; [done| simpl; lia])). 

    eapply never_set_after_eq_false in NEVER_SET'; [| reflexivity].
    destruct NEVER_SET' as (?&?&NC&NCsig). 
    rewrite /tr_sig_lt /MR in MIN. simpl in MIN.
    rewrite NC NTH in MIN. simpl in MIN. rewrite NCsig SIGsn in MIN. simpl in MIN.

    forward eapply pres_by_valid_trace with (i := n) (j := max n c); eauto.
    { intros. apply (loc_step_sig_st_le_pres _ sid (Some (l, false))). }
    { intros. apply fork_step_sig_st_le_pres. }
    { rewrite NTH. simpl. rewrite SIG0. done. }
    { lia. }
    rewrite NC //= NCsig. intros [<- _].     
    
    specialize (MIN OBLS_LT).
    edestruct @strict_not_both; eauto. done.  

  Qed. 

  Definition s_ow (s: SignalId) (i: nat) := 
    let π := 
      δ ← tr S!! i;
      let owners := dom $ filter (fun '(_, obs) => s ∈ obs) (ps_obls _ δ) in
      let ow_phs := extract_Somes_gset $ set_map (fun τ => ps_phases _ δ !! τ) owners: gset Phase in
      ow ← gset_pick ow_phs;
      mret ow
    in default π0 π.

  Lemma S_OWNER s i π τ δ
    (ITH: tr S!! i = Some δ)
    (PH: ps_phases _ δ !! τ = Some π)
    (OW: s ∈ default ∅ (ps_obls _ δ !! τ)):
    s_ow s i = π.
  Proof using WF.
    clear dependent set_before LVL_WF VALID. 
    intros. rewrite /s_ow. rewrite ITH. simpl.
    destruct (ps_obls OP δ !! τ) as [obls| ] eqn:OBLS; [| done]. simpl in OW.
    erewrite <- map_difference_union with (m2 := (ps_obls OP δ)).
    2: { eapply map_singleton_subseteq_l; eauto. }
    rewrite map_filter_union.
    2: { apply map_disjoint_dom. set_solver. }
    rewrite map_filter_singleton decide_True; [| done].
    rewrite (proj2 (map_filter_empty_iff _ _)).
    2: { red. intros τ' ? LOC' IN'.
         apply lookup_difference_Some in LOC'. destruct LOC' as [OBLS' ?%lookup_singleton_None].
         edestruct @om_wf_obls_disj; eauto.
         - by rewrite OBLS.
         - by rewrite OBLS'. }
    rewrite map_union_empty dom_singleton_L.
    rewrite set_map_singleton_L. rewrite PH.
    rewrite extract_Somes_gset_singleton. rewrite gset_pick_singleton.
    done.
  Qed.

  Lemma fresh_phase_is_fork δ1 τ δ2 π
    (WF1: om_st_wf _ δ1)
    (STEP: om_trans _ δ1 τ δ2)
    (FRESH: π ∈ (map_img (ps_phases _ δ2): gset Phase) ∖ (map_img (ps_phases _ δ1): gset Phase)):
    exists π0, ps_phases _ δ1 !! τ = Some π0 /\ is_fork π0 π.
  Proof using.
    clear WF SET_BEFORE_SPEC LVL_WF VALID.
    red in STEP. destruct STEP as (δ' & PSTEP & FSTEP).
    
    forward eapply pres_by_loc_step_implies_progress.
    { apply loc_step_phases_pres. }
    intros PH_EQ. do 2 red in PH_EQ. specialize_full PH_EQ; eauto.
    { reflexivity. }
    red in PH_EQ. rewrite -PH_EQ in FRESH. 

    forward eapply pres_by_loc_step_implies_progress.
    { apply wf_preserved_by_loc_step. }
    intros WF'. do 2 red in WF'. specialize_full WF'; eauto.

    inversion FSTEP; [| set_solver].
    subst. destruct H1 as (?&?&FORK). inversion FORK. subst.
    destruct δ'. simpl in *.
    rewrite -PH_EQ. eexists. split; eauto. 
    revert FRESH. subst new_phases0. rewrite map_img_insert_L.
    rewrite delete_notin.
    2: { apply not_elem_of_dom. rewrite dom_insert.
         apply not_elem_of_union. split; auto.
         apply not_elem_of_singleton. intros ->.
         destruct FRESH'. eapply elem_of_dom. eauto. }
    rewrite map_img_insert_L.
    rewrite !difference_union_distr_l.
    rewrite difference_disjoint.
    2: { apply disjoint_singleton_l.
         intros [τ1 IN1]%elem_of_map_img.
         edestruct phases_not_le; [apply WF'| ..]; simpl.
         { apply LOC_PHASE. }
         { apply IN1. }
         { apply phase_lt_fork. }
         pose proof (phase_lt_fork π1 1) as [??]%strict_spec_alt. done. }
    rewrite difference_disjoint.
    2: { apply disjoint_singleton_l.
         intros [τ' IN']%elem_of_map_img.
         edestruct phases_not_le; [apply WF'| ..]; simpl.
         { apply LOC_PHASE. }
         { apply IN'. }
         { apply phase_lt_fork. }
         pose proof (phase_lt_fork π1 0) as [??]%strict_spec_alt. done. }
    rewrite subseteq_empty_difference.
    2: { apply map_subseteq_img, delete_subseteq. }

    rewrite union_empty_r_L elem_of_union !elem_of_singleton.
    rewrite /is_fork. intros [-> | ->]; eauto.
  Qed.

  Lemma om_trans_cps_bound δ1 τ δ2 π cp τ' π'
    (WF1: om_st_wf _ δ1)
    (PH: ps_phases _ δ1 !! τ = Some π)
    (STEP: om_trans _ δ1 τ δ2)
    (IN2 : cp ∈ ps_cps _ δ2)
    (PH': ps_phases _ δ2 !! τ' = Some π')
    (LE: phase_le π π')
    (LEcp : phase_le cp.1 π'):
    phase_le cp.1 π.
  Proof using.    
    destruct (decide (π' = π)) as [-> | NEQ].
    { done. }
    
    forward eapply (om_trans_wf_pres _ _ δ1) as WF2; eauto.

    assert (π' ∉ (map_img (ps_phases _ δ1): gset Phase)) as FRESHπ'.
    { intros IN.
      rename π' into π''.
      apply elem_of_map_img in IN as (τ'' & T'').
      destruct (decide (τ'' = τ)) as [-> | ?]; [set_solver| ].      
      edestruct @om_wf_ph_disj.
      { eapply WF1; eauto. }
      all: eauto. }

    assert (is_fork π π') as [d PH_FORK]; [| subst π'].
    { eapply fresh_phase_is_fork in STEP; eauto.
      2: { apply elem_of_difference. split; eauto. apply elem_of_map_img. eauto. }
      destruct STEP as (? & PH0 & ?). congruence. }

    apply phase_le_ext_split in LEcp as [EQ | ?]; [| done]. 

    red in STEP. destruct STEP as (δ' & PSTEP & FSTEP).
      
    forward eapply pres_by_loc_step_implies_progress.
    { apply loc_step_phases_pres. }
    intros PH_EQ. do 2 red in PH_EQ. specialize_full PH_EQ; eauto.
    { reflexivity. }
    red in PH_EQ. rewrite -PH_EQ in PH.
    
    forward eapply pres_by_loc_step_implies_progress.
    { apply wf_preserved_by_loc_step. }
    intros WF'. do 2 red in WF'. specialize_full WF'.
    2: { red. eauto. }
    all: eauto.
    
    assert (ps_cps _ δ2 = ps_cps _ δ') as CPS2.
    { inversion FSTEP; [| done].
      subst. destruct H1 as (?&?&FORK). inversion FORK. subst.
      by destruct δ'. }
    
    rewrite CPS2 in IN2.
    apply om_wf_cps_ph_bound in WF'. red in WF'. simpl in WF'.
    destruct WF'. do 3 eexists. split; [| split]; eauto.
    rewrite EQ. apply phase_lt_fork.
  Qed. 

  (* TODO: unify with previous *)
  Lemma om_trans_eps_bound δ1 τ δ2 π ep τ' π'
    (WF1: om_st_wf _ δ1)
    (PH: ps_phases _ δ1 !! τ = Some π)
    (STEP: om_trans _ δ1 τ δ2)
    (IN2 : ep ∈ ps_eps _ δ2)
    (PH': ps_phases _ δ2 !! τ' = Some π')
    (LE: phase_le π π')
    (LEcp : phase_le ep.1.2 π'):
    phase_le ep.1.2 π.
  Proof using.    
    destruct (decide (π' = π)) as [-> | NEQ].
    { done. }
    
    forward eapply (om_trans_wf_pres _ _ δ1) as WF2; eauto.

    assert (π' ∉ (map_img (ps_phases _ δ1): gset Phase)) as FRESHπ'.
    { intros IN.
      rename π' into π''.
      apply elem_of_map_img in IN as (τ'' & T'').
      destruct (decide (τ'' = τ)) as [-> | ?]; [set_solver| ].      
      edestruct @om_wf_ph_disj.
      { eapply WF1; eauto. }
      all: eauto. }

    assert (is_fork π π') as [d PH_FORK]; [| subst π'].
    { eapply fresh_phase_is_fork in STEP; eauto.
      2: { apply elem_of_difference. split; eauto. apply elem_of_map_img. eauto. }
      destruct STEP as (? & PH0 & ?). congruence. }

    apply phase_le_ext_split in LEcp as [EQ | ?]; [| done]. 

    red in STEP. destruct STEP as (δ' & PSTEP & FSTEP).
      
    forward eapply pres_by_loc_step_implies_progress.
    { apply loc_step_phases_pres. }
    intros PH_EQ. do 2 red in PH_EQ. specialize_full PH_EQ; eauto.
    { reflexivity. }
    red in PH_EQ. rewrite -PH_EQ in PH.
    
    forward eapply pres_by_loc_step_implies_progress.
    { apply wf_preserved_by_loc_step. }
    intros WF'. do 2 red in WF'. specialize_full WF'.
    2: { red. eauto. }
    all: eauto.
    
    assert (ps_eps _ δ2 = ps_eps _ δ') as EPS2.
    { inversion FSTEP; [| done].
      subst. destruct H1 as (?&?&FORK). inversion FORK. subst.
      by destruct δ'. }
    
    rewrite EPS2 in IN2.
    apply om_wf_eps_ph_bound in WF'. red in WF'. simpl in WF'.
    destruct WF'. do 3 eexists. split; [| split]; eauto.
    rewrite EQ. apply phase_lt_fork.
  Qed.

  (* TODO: move *)
  Lemma gset_filter_subseteq_mono_strong `{Countable A} (P Q: A -> Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
    (g: gset A)
    (IMPL: ∀ x, x ∈ g -> P x -> Q x):
    filter P g ⊆ filter Q g.
  Proof using. clear -IMPL. set_solver. Qed. 

  Lemma min_owner_PF_decr s c
    (FAIR: ∀ τ, obls_trace_fair OP τ tr)
    (UNSET: never_set_after s c)
    (MIN: minimal_in_prop tr_sig_lt (s, c)
            (λ ab : SignalId * nat, never_set_after ab.1 ab.2 /\ c <= ab.2))
    (OTF := λ i, TPF (s_ow s i) i):
    ∀ d, c ≤ d → ∃ j, d < j ∧ ms_lt deg_le (OTF j) (OTF d).
  Proof using VALID WF SET_BEFORE_SPEC.
    clear LVL_WF.
    intros d LE.
    pose proof (never_set_owned _ _ UNSET) as OWN. specialize (OWN _ LE).  
    destruct (tr S!! d) as [δ| ] eqn:DTH.
    2: { simpl in OWN. by apply map_Exists_empty in OWN. }
    simpl in OWN. rewrite map_Exists_lookup in OWN. 
    destruct OWN as [τ OWN]. 
    destruct (ps_obls OP δ !! τ) as [obs| ] eqn:OBLSd.
    2: { set_solver. }
    destruct OWN as (? & [=<-] & OWN). 
    pose proof (FAIR τ) as F. apply fair_by_equiv, fair_by'_strenghten in F.
    2: { solve_decision. }
    red in F. specialize (F d). specialize_full F.
    { rewrite DTH. simpl. red. rewrite OBLSd. simpl. set_solver. }
    destruct F as (m & (δm & MTH & STEP) & MINm).
    
    assert (exists π, ps_phases _ δ !! τ = Some π) as [π PH].
    { apply mk_is_Some, elem_of_dom in OBLSd. rewrite -om_wf_dpo in OBLSd; eauto.
      by apply elem_of_dom. }
    
    (* rewrite /OTF in EMP. erewrite S_OWNER in EMP; eauto. *)
    (* 2: { rewrite OBLSd. set_solver. }  *)

    assert (∀ k, d <= k < d + m → tr L!! k ≠ Some τ) as OTHER_STEPS.
    { intros k BOUNDk Kτ.
      specialize (MINm (k - d)).
      specialize_full MINm; [| lia].
      rewrite -Nat.le_add_sub; [| lia].
      forward eapply (proj1 (label_lookup_states _ _)); eauto. intros [[? KTH] _].
      eexists. split; eauto. red. right. eauto. } 
    
    forward eapply next_step_rewind. 
    { apply DTH. }
    { eauto. }
    { apply (Nat.le_add_r _ m). }
    { done. }
    
    intros TPFle.
    
    (* rewrite EMP in TPFle. apply ms_le_empty in TPFle. *)
    
    assert (ps_obls OP δm !! τ = Some obs) as OBLSm.
    { forward eapply (pres_by_valid_trace_strong _ tr d (d + m)). 
      4: { eapply (other_fork_step_pres_obls' τ obs). }
      3: { apply other_loc_step_pres_obls. }
      all: try done. 
      { lia. }
      { rewrite DTH. simpl. eauto. }
      { simpl. intros. set_solver. }
      simpl. rewrite MTH. simpl. tauto. }

    red in STEP. destruct STEP.
    { rewrite /has_obls in H1. rewrite OBLSm in H1. set_solver. }
    destruct H1 as (?&LBL&<-).
    forward eapply (proj1 (label_lookup_states' _ _)); eauto.
    rewrite -Nat.add_1_r. intros [δm' MTH'].
    
    (* forward eapply (trace_valid_steps'' _ _ VALID (d + m)) as STEP; eauto. *)
    (* simpl in STEP. *)
    
    assert (ps_phases OP δm !! τ = Some π) as PHm.
    { forward eapply (pres_by_valid_trace_strong _ tr d (d + m)). 
      4: { apply (other_fork_step_pres_phase_eq τ π). }
      3: { intros. apply (loc_step_pres_phase_eq τ π). }
      all: try done. 
      { lia. }
      { rewrite DTH. done. }
      { set_solver. }
      by rewrite MTH. }
    
    forward eapply (owm_om_trans_ms_lt π τ (d + m)); eauto.
    { eapply never_set_after_after; [| apply UNSET]. lia. }
    { red. intros [??] [N' LE'] ?. simpl in LE', N'.
      move MIN at bottom. red in MIN.
      specialize (MIN (_, _) ltac:(split; [apply N'| simpl; lia])).
      pose proof (never_set_after_eq_false _ _ UNSET c ltac:(lia)).
      pose proof (never_set_after_eq_false _ _ UNSET (d + m) ltac:(lia)).
      destruct H2 as (?&l&CTH&SIGc), H3 as (?&l_&DMTH&SIGdm).

      forward eapply pres_by_valid_trace with (i := c) (j := d + m); eauto.
      { intros. apply (loc_step_sig_st_le_pres _ s (Some (l, false))). }
      { intros. apply fork_step_sig_st_le_pres. }
      { rewrite CTH. simpl. by rewrite SIGc. }
      { lia. }
      rewrite DMTH. simpl. rewrite SIGdm. simpl. intros [<- _].

      clear -H1 MIN SIGc SIGdm DMTH CTH.
      unfold tr_sig_lt, MR, lvl_at in *.
      (* rewrite DMTH. simpl. rewrite SIGdm. simpl. *)
      rewrite CTH in MIN. simpl in MIN. rewrite SIGc in MIN. simpl in MIN.
      apply MIN. rewrite DMTH in H1. simpl in H1. rewrite SIGdm in H1. done. }
    { by rewrite OBLSm. }
    
    intros LT.
    exists (S (d + m)). split; [lia| ].
    rewrite /OTF /TPF /TPF'. erewrite (S_OWNER _ d); eauto.
    2: { by rewrite OBLSd. }
    eapply strict_transitive_l; [| apply TPFle]. 
    eapply strict_transitive_r; [| apply LT].
    
    (* forward eapply (obls_transfer_phase δm τ) with (τs := τ).  *)
    (* { eapply trace_valid_steps''; eauto. } *)
    (* { rewrite OBLSm. done. } *)
    (* { eauto. } *)
    forward eapply pres_by_loc_fork_steps_implies_om_trans.
    { apply loc_step_pres_asg_bound. }
    { apply fork_step_pres_asg_bound. }
    intros PRES. do 2 red in PRES. specialize_full PRES.
    { split; [| by apply (WF (d + m))].
      red. right. exists τ, π. rewrite OBLSm. simpl. do 2 (split; [done| ]).
      reflexivity. }
    { red. eapply trace_valid_steps''; eauto. }
    apply proj1 in PRES. red in PRES. destruct PRES as [[l NO_OWN] | OWN'].
    { pose proof (UNSET (d + m + 1) ltac:(lia)) as U.
      rewrite /sig_val_at in U. rewrite MTH' in U. simpl in U.
      rewrite NO_OWN in U. done. }
    
    destruct OWN' as (τ' & π' & OWN' & PH' & LE').
    destruct (ps_obls OP δm' !! τ') as [obs'| ] eqn:OBLSd'.
    2: { set_solver. }
    
    erewrite S_OWNER.
    3: { apply PH'. }
    2: { rewrite -MTH'. f_equal. lia. }
    2: { rewrite OBLSd'. done. } 
    
    (* TODO: extract? *)
    rewrite /TPF /TPF' /PF'.
    generalize ((LIM_STEPS + 2) * S (d + m)) as N. intros.
    rewrite plus_n_Sm -Nat.add_1_r Nat.add_assoc MTH'. simpl.
    apply ms_le_disj_union.
    - apply ms_le_sub, mset_map_sub.
      apply mset_filter_subseteq_mono_strong.
      intros [pi de] IN' LEpi.

      replace pi with (pi, de).1; [| done].
      eapply (om_trans_cps_bound δm); eauto.
      eapply trace_valid_steps''; eauto.
    - apply ms_le_exp_mono; [lia| ].
      apply gset_filter_subseteq_mono_strong. 
      intros ep IN' LEpi.
      destruct ep as [[? pi]?] eqn:EP.

      replace pi with ep.1.2 by (by subst). 
      eapply (om_trans_eps_bound δm); eauto.
      2, 3: by subst. 
      eapply trace_valid_steps''; eauto.
  Qed. 
  
  Theorem signals_eventually_set
    (FAIR: forall τ, obls_trace_fair _ τ tr)
    (DEG_WF: wf (strict deg_le)):
    (* ¬ exists sid c, never_set_after sid c.  *)
    forall sid, eventually_set sid. 
  Proof using LVL_WF VALID WF SET_BEFORE_SPEC H0.
    intros sid. red. intros m UNSET.
    (* red in UNSET.  *)

    assert (exists ab, never_set_after ab.1 ab.2 /\ m <= ab.2) as MIN. 
    { exists (sid, m). eauto. }

    eapply sets_have_min in MIN; [| apply tr_sig_lt_wf]. clear sid UNSET. 
    apply ex_prod in MIN. simpl in MIN. destruct MIN as (s & c & [UNSET LEm] & MIN).
    
    set (OTF i := TPF (s_ow s i) i).
    
    set (R := MR (ms_lt deg_le) (fun i => OTF (c + i))). 
    forward eapply well_founded_ind with (R := R) (P := fun _ => False).
    4: done.
    3: exact 0.
    { eapply measure_wf. by apply ms_lt_wf. }
    intros i NEXT.
    (* pose proof (min_owner_PF_decr (c + i) ltac:(lia)) as D. *)
    forward eapply min_owner_PF_decr with (d := c + i); eauto.
    { red. intros [??] [N LE] ?.
      eapply MIN; eauto. split; auto. lia. }
    { lia. }
    intros (j & AFTER & DECR).
    apply (NEXT (j - c)). red. red.
    rewrite -Nat.le_add_sub; [| lia]. done. 
    
  Qed.

  Let any_phase (_: Phase) := True.
  Definition APF := TPF' OP tr set_before any_phase.

  (* TODO: move *)
  Lemma gset_filter_True `{Countable K} (g: gset K)
    (P: K -> Prop)
    `{∀ x, Decision (P x)}
    (TRUE: forall k, k ∈ g -> P k):
    filter P g = g.
  Proof using. clear -TRUE. set_solver. Qed. 
  
  Lemma any_expect_ms_le δ1 τ δ2 k
    (SET_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                  let n := (LIM_STEPS + 2) * set_before sid in
                  k < n)
    :
    expect_ms_le OP set_before any_phase δ1 τ δ2 k. 
  Proof using SET_BEFORE_SPEC VALID.
    clear LVL_WF WF.
    intros. red. intros sid π' d EXP. 
    rewrite /PF /PF'.
    
    inversion EXP; subst.
    destruct δ1. simpl in *. subst new_cps0.
    rewrite !mset_filter_True.
    2, 3: intros [??]; done.
    rewrite gset_filter_True.
    2: intros ((?&?)&?); done.      
    
    rewrite mset_map_disj_union.
    rewrite mset_map_singleton. simpl. 
    
    (* rewrite mset_map_disj_union. *)
    rewrite -gmultiset_disj_union_assoc. apply ms_le_disj_union.
    { apply ms_le_refl. }
    rewrite (union_difference_singleton_L _ _ EP).
    
    rewrite (union_comm_L {[ _ ]} _).
    rewrite !approx_expects_add.
    2, 3: set_solver.
    simpl. rewrite gmultiset_disj_union_comm.
    rewrite -gmultiset_disj_union_assoc.
    apply ms_le_disj_union.
    { apply ms_le_exp_mono; [lia | reflexivity]. }
    
    move SET_BOUND at bottom. specialize_full SET_BOUND; [by eauto| ].
    eapply ms_le_Proper; [reflexivity| ..| apply ms_le_refl].
    rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.
  Qed.
  
  (* TODO: try to unify with similar lemmas? *)
  Lemma om_trans_all_ms_lt n
    (DOM: is_Some (tr S!! (S n)))
    (ALL_SET: ∀ sid, eventually_set sid)
    :
    ms_lt deg_le (APF (S n)) (APF n).
  Proof using VALID SET_BEFORE_SPEC.
    destruct DOM as [δ' NTH']. 
    
    eapply om_trans_ms_rel with (bd := true); auto.
    { intros δ δ'_ τ mb mf k NTH BOUND PSTEPS BURNS FORKS. 
      rewrite Nat.add_succ_r Nat.add_0_r.
      apply state_label_lookup in NTH as (NTH_&NTH'_&LBL_).
      rewrite Nat.add_1_r NTH' in NTH'_. inversion NTH'_. subst δ'_. 
      destruct BURNS as (?&?&BURNS).
      inversion BURNS. subst. 
      eapply burns_cp_own_ms_lt with (πb := x); done. }
    
    (* TODO: extract the lemma below? *)
    
    clear δ' NTH'. 
    intros τ' IDTHl. 
    red. intros δn δn' mb mf k ITH%trace_state_lookup BOUND NSTEPS BSTEP FSTEP.
    clear dependent BSTEP FSTEP δn'. 
    
    generalize dependent mb. induction k.
    { intros ? ->%obls_utils.nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
    specialize (IHk ltac:(lia) _ STEPS).
    etrans; eauto.
    eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
    { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
    
    eapply any_expect_ms_le. 
    
    intros sid π d EXP. simpl.
    inversion EXP. subst.
    
    enough (set_before sid > n).
    { apply PeanoNat.Nat.le_succ_l in H1. 
      apply Nat.le_sum in H1 as [u EQ]. rewrite EQ. lia. }
    
    red.
    clear LE. 
    edestruct Nat.lt_ge_cases as [LT | LE]; [apply LT| ].   
    pose proof SET_BEFORE_SPEC as SB.
    specialize (SB _ _ (ALL_SET sid) LE).
    rewrite /sig_val_at in SB. rewrite ITH in SB. simpl in SB.
    
    (* either it was there when the big step started,
       or it's a new signal, but then the thread holds an obligation
       and cannot wait on it *)
    assert (ps_sigs OP δn !! sid = Some (l, false)) as SIG0'.
    { eapply expected_signal_created_before; eauto. }
    rewrite SIG0' in SB. done. 
    
  Qed. 

  Theorem trace_terminates
    (FAIR: forall τ, obls_trace_fair _ τ tr)
    (DEG_WF: wf (strict deg_le)):
    terminating_trace tr. 
  Proof using WF VALID SET_BEFORE_SPEC LVL_WF H0.
    set (R := MR (ms_lt deg_le) APF).    
    forward eapply well_founded_ind with (R := R) (P := fun _ => terminating_trace tr).
    4: done.
    3: exact 0. 
    { eapply measure_wf. eapply ms_lt_wf; eauto. }
    intros i NEXT.

    destruct (tr S!! (S i)) eqn:ITH'.
    2: { pose proof (trace_has_len tr) as [len ?]. 
         eapply state_lookup_dom_neg in ITH'; eauto.
         lia_NO' len.
         eapply terminating_trace_equiv; eauto. }

    forward eapply om_trans_all_ms_lt; eauto.
    by apply signals_eventually_set. 
  Qed. 

End Termination.


(* TODO: merge the sections *)
Section TerminationFull.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP.

  Context (tr: obls_trace OP).
  Hypothesis (VALID: obls_trace_valid OP tr) (FAIR: ∀ τ, obls_trace_fair OP τ tr).

  Lemma set_before_ex
    :
    forall sid, exists b, sb_prop OP tr sid b. 
  Proof using VALID.
    intros sid.
    destruct (Classical_Prop.classic (exists c, sig_val_at OP tr sid c = false)) as [[c USED] | UNUSED].
    2: { exists 0. red. intros.
         apply not_exists_forall_not with (x := i) in UNUSED.
         by apply not_false_is_true. }
    destruct (Classical_Prop.classic (exists s, c <= s /\ sig_val_at OP tr sid s = true)) as [[s SET] | UNSET].
    - exists s. red. intros.
      unfold sig_val_at in *.
      destruct (tr S!! c) eqn:CTH; [| done]. simpl in USED.
      destruct (ps_sigs OP m !! sid) as [[??]| ] eqn:SIGm; [| done]. simpl in USED. subst.
      
      destruct (tr S!! i) eqn:ITH; [| done]. simpl.
      
      destruct SET as [LE SET]. 
      forward eapply state_lookup_prev; [eauto | apply H1| ]. intros [? STH]. 
      rewrite STH in SET. simpl in SET. 
      
      forward eapply pres_by_valid_trace with (i := c) (j := s); eauto.
      { intros. apply (loc_step_sig_st_le_pres _ _ sid (Some (l, false))). }
      { intros. apply fork_step_sig_st_le_pres. }
      { rewrite CTH. simpl. by rewrite SIGm. }
      rewrite STH. simpl.
      destruct (ps_sigs OP x !! sid) as [[??]| ] eqn:SIGs; [| done].
      simpl in SET. subst. intros [<- ?]. 

      forward eapply pres_by_valid_trace with (i := s) (j := i); eauto.
      { intros. apply (loc_step_sig_st_le_pres _ _ sid (Some (l, true))). }
      { intros. apply fork_step_sig_st_le_pres. }
      { rewrite STH. simpl. by rewrite SIGs. }
      rewrite ITH. simpl. destruct (ps_sigs OP m0 !! sid) as [[??]| ]; [| done].
      simpl. intros [??]. destruct b; done. 
    - exists c. red. intros i SET ?.
      destruct UNSET. red in SET. specialize (SET i).
      rewrite /never_set_after in SET.
      apply not_forall_exists_not in SET as [c' SET].
      apply Classical_Prop.imply_to_and in SET as [LEic SET].
      exists c'. split; [lia| ]. by apply not_false_is_true.
  Qed. 

  Theorem obls_fair_trace_terminate
    (TR_WF: ∀ i δ, tr S!! i = Some δ → om_st_wf OP δ)
    (LVL_WF: wf (strict lvl_le))
    (DEG_WF: wf (strict deg_le))
    (LVL_INH: Inhabited Level):
    terminating_trace tr.
  Proof using VALID FAIR.
    Require Import Coq.Logic.ClassicalChoice.
    pose proof (choice _ set_before_ex) as [sb ?].
    eapply trace_terminates; eauto. 
  Qed.

End TerminationFull.
