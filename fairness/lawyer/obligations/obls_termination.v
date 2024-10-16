Require Import Coq.Program.Wf.
Require Import Relation_Operators.
From stdpp Require Import namespaces.
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
  
  Let π0 := nroot.

  Lemma other_expect_ms_le π__ow δ1 τ δ2 k
    (OTHER: let π := default π0 (ps_phases _ δ1 !! τ) in
            (* phases_incompat π__ow π *)
            phases_disj π__ow π
    ):
    expect_ms_le OP set_before (phase_ge π__ow) δ1 τ δ2 k. 
  Proof using.
    clear LVL_WF SET_BEFORE_SPEC WF.
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
    clear LVL_WF SET_BEFORE_SPEC WF.
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
    (VALID: obls_trace_valid OP tr)
    (PH: from_option (fun δ => ps_phases _ δ !! τ = Some πτ) False (tr S!! n))
    (NOτ: tr L!! n ≠ Some τ):
    ms_le deg_le (TPF πτ (S n)) (TPF πτ n).
  Proof using WF.
    destruct (tr S!! (S n)) as [δ'| ] eqn:NEXT.
    2: { rewrite /TPF /TPF'. rewrite NEXT. simpl. apply empty_ms_le. }
    
    eapply om_trans_ms_rel with (bd := false); auto.
    { intros.
      rewrite Nat.add_succ_r. rewrite Nat.add_0_r.  
      destruct H4 as (?&?&?). eapply burns_cp_ms_le; eauto. }
    
    (* TODO: extract the lemma below? *)
    
    intros δ τ' IDTHl. 
    red. intros δk k IDTH BOUND NSTEPS. 
    rewrite IDTHl in NOτ.
    assert (τ' ≠ τ) as X by (by intros ->). clear NOτ. rename X into NOτ. 
    
    generalize dependent δk. induction k.
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
      apply wf_preserved_by_loc_step. }
    
    assert (exists π', ps_phases _ δ' !! τ' = Some π') as [π' PH'].
    { apply om_step_wf_dom in STEP; [| done]. 
      rewrite -om_wf_dpo in STEP; [| done]. eapply elem_of_dom in STEP; eauto. }
    rewrite PH'. simpl.
    rewrite IDTH in PH. simpl in PH. 

    symmetry. eapply (om_wf_ph_disj _ δ'); eauto.
    eapply loc_steps_rep_phase_exact_pres; eauto. 
  Qed.

  Lemma other_loc_step_pres_phase_eq τ π τs
    (OTHER: τs ≠ τ):
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
    (VALID: obls_trace_valid OP tr)
    (ITH: tr S!! i = Some δ0)
    (PH: ps_phases _ δ0 !! τ = Some π)
    (LE: i <= j)
    (NOτ: forall k, i <= k < j -> tr L!! k ≠ Some τ):
    ms_le deg_le (TPF π j) (TPF π i).
  Proof using WF.
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
    3: { apply (other_loc_step_pres_phase_eq τ π). }
    all: try done. 
    { lia. }
    { rewrite ITH. done. }
    { intros. simpl. specialize (NOτ k). specialize_full NOτ; eauto.
      { lia. }
      rewrite H2 in NOτ. set_solver. }
    by rewrite IDTH.
  Qed. 
    
  Lemma owm_om_trans_ms_lt πτ τ n s δ0
    (NTH: tr S!! n = Some δ0)
    (VALID: obls_trace_valid OP tr)
    (PH: ps_phases _ δ0 !! τ = Some πτ)
    (NEVER_SET : never_set_after s n)
    (MIN: minimal_in_prop tr_sig_lt (s, n) (λ sn, never_set_after sn.1 sn.2))
    (OWNER: s ∈ default ∅ (ps_obls _ δ0 !! τ))
    (LBL: tr L!! n = Some τ):
    ms_lt deg_le (TPF πτ (S n)) (TPF πτ n).
  Proof using.
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
    intros δ τ' IDTHl. 
    red. intros δk k IDTH BOUND NSTEPS.
    rewrite NTH in IDTH. inversion IDTH. subst δ. 
    rewrite LBL in IDTHl. inversion IDTHl. subst τ'. clear IDTHl. 
    
    generalize dependent δk. induction k.
    { intros ? ->%obls_utils.nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
    specialize (IHk ltac:(lia) _ STEPS).
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
    destruct (ps_sigs OP δ0 !! s) as [[ls ?]|] eqn:SIG__min; [| done].
    simpl in NEVER_SET. subst. 
    
    assert (s ∈ default ∅ (ps_obls _ δ' !! τ)) as OBL' by admit.
    assert (ps_sigs _ δ' !! s = Some (ls, false)) as SIG' by admit. 
    specialize (OBLS_LT ls). specialize_full OBLS_LT.
    { apply extract_Somes_gset_spec.
      destruct (ps_obls OP δ' !! τ) as [obs| ] eqn:OBLS'; [| set_solver].
      simpl in OBL'. simpl. apply elem_of_map. eexists. split; eauto.
      rewrite SIG'. done. }
    
    red. destruct (Nat.lt_ge_cases n (set_before sid)) as [?|GE]; [done| ].   
    
    (* either it was there when the big step started,
       or it's a new signal, but then the thread holds an obligation
       and cannot wait on it *)
    assert (ps_sigs OP δ0 !! sid = Some (l, false)) as SIG0 by admit.
    
    pose proof (SET_BEFORE_SPEC sid n). specialize_full H1; [| done| ].
    2: { rewrite /sig_val_at in H1. 
         rewrite NTH in H1. simpl in H1.
         rewrite SIG0 in H1. done. }
    
    intros c NEVER_SET_.

    assert (never_set_after sid (max n c)) as NEVER_SET'.
    { eapply never_set_after_after; [| apply NEVER_SET_]. lia. } 
    clear NEVER_SET_.
    move MIN at bottom. red in MIN. specialize (MIN (_, _) NEVER_SET').
    eapply never_set_after_eq_false in NEVER_SET'; [| reflexivity].
    destruct NEVER_SET' as (?&?&NC&NCsig). 
    rewrite /tr_sig_lt /MR in MIN. simpl in MIN.
    rewrite NC NTH in MIN. simpl in MIN. rewrite NCsig SIG__min in MIN. simpl in MIN.

    forward eapply pres_by_valid_trace with (i := n) (j := max n c); eauto.
    { intros. apply (loc_step_sig_st_le_pres _ sid (Some (l, false))). }
    { intros. apply fork_step_sig_st_le_pres. }
    { rewrite NTH. simpl. rewrite SIG0. done. }
    { lia. }
    rewrite NC //= NCsig. intros [<- _].     
    
    specialize (MIN OBLS_LT).
    edestruct @strict_not_both; eauto. 

  Admitted.

  Definition asg_bound sid πb δ :=
    (* map_Forall (fun _ obls_ => sid ∉ obls_) (ps_obls _ δ) \/ *)
    (exists l, ps_sigs _ δ !! sid = Some (l, true)) \/
    exists τ π, sid ∈ default ∅ (ps_obls _ δ !! τ) /\
            ps_phases _ δ !! τ = Some π /\
            phase_le πb π.

  Lemma loc_step_pres_asg_bound sid πb τ:
    preserved_by _ (loc_step_of _ τ) (fun δ => asg_bound sid πb δ /\ om_st_wf _ δ).
  Proof using.
    clear tr set_before WF SET_BEFORE_SPEC LVL_WF.

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
    clear tr set_before WF SET_BEFORE_SPEC LVL_WF.

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

  (* Lemma om_trans_new_cps δ1 τ δ2 *)
  (*   (STEP: om_trans _ δ1 τ δ2) *)
  (*   (πτ := default π0 (ps_phases _ δ1 !! τ)) *)
  (*   : *)
  (*   forall cp, cp ∈ ps_cps _ δ2 ∖ ps_cps _ δ1 -> cp.1 = πτ. *)
  (* Proof using. Admitted.  *)
  
  (* Lemma om_trans_new_eps δ1 τ δ2 *)
  (*   (STEP: om_trans _ δ1 τ δ2) *)
  (*   (πτ := default π0 (ps_phases _ δ1 !! τ)) *)
  (*   : *)
  (*   forall ep, ep ∈ ps_eps _ δ2 ∖ ps_eps _ δ1 -> phase_le (ep.1.2) πτ. *)
  (* Proof using. Admitted. *)
  
  Lemma om_trans_cps_bound δ1 τ δ2 πτ cp π'
    (PH: ps_phases _ δ1 !! τ = Some πτ)
    (STEP: om_trans _ δ1 τ δ2)
    (IN2 : cp ∈ ps_cps _ δ2)
    (LEcp : phase_le cp.1 π')
    (FRESHπ': π' ∉ (map_img (ps_phases _ δ1) : gset Phase)):
    phase_le cp.1 πτ.
  Proof using. Admitted.

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
    clear dependent set_before LVL_WF. 
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

  Lemma min_owner_PF_decr s c
    (VALID: obls_trace_valid OP tr)
    (FAIR: ∀ τ, obls_trace_fair OP τ tr)
    (UNSET: never_set_after s c)
    (MIN: minimal_in_prop tr_sig_lt (s, c)
            (λ ab : SignalId * nat, never_set_after ab.1 ab.2))
    (OTF := λ i, TPF (s_ow s i) i):
    ∀ d, c ≤ d → ∃ j, d < j ∧ ms_lt deg_le (OTF j) (OTF d).
  Proof using.
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
    
    forward eapply next_step_rewind. 
    { eauto. }
    { apply DTH. }
    { eauto. }
    { apply (Nat.le_add_r _ m). }
    { intros k BOUNDk Kτ.
      specialize (MINm (k - d)).
      specialize_full MINm; [| lia].
      rewrite -Nat.le_add_sub; [| lia].
      forward eapply (proj1 (label_lookup_states _ _)); eauto. intros [[? KTH] _].
      eexists. split; eauto. red. right. eauto. }
    intros TPFle.
    
    (* rewrite EMP in TPFle. apply ms_le_empty in TPFle. *)
    
    red in STEP. destruct STEP.
    { (* steps in between keep the obligation assigned *)
      admit. }
    destruct H1 as (?&LBL&<-).
    forward eapply (proj1 (label_lookup_states' _ _)); eauto.
    rewrite -Nat.add_1_r. intros [δm' MTH'].
    
    (* forward eapply (trace_valid_steps'' _ _ VALID (d + m)) as STEP; eauto. *)
    (* simpl in STEP. *)
    
    assert (ps_obls OP δm !! τ = Some obs) as OBLSm.
    { (* obligations haven't been changed with other threads' steps *)
      admit. }
    
    assert (ps_phases OP δm !! τ = Some π) as PHm.
    { forward eapply (pres_by_valid_trace_strong _ tr d (d + m)). 
      4: { apply (other_fork_step_pres_phase_eq τ π). }
      3: { apply (other_loc_step_pres_phase_eq τ π). }
      all: try done. 
      { lia. }
      { rewrite DTH. done. }
      { intros ? ? [LE' LT'] LBL' ->.
        apply Nat.le_sum in LE' as [u ->]. 
        specialize (MINm u). specialize_full MINm; [| lia]. 
        eapply mk_is_Some, state_lookup_prev with (j := d + u) in MTH' as [? K].
        2: lia.
        eexists. split; eauto. red. right. eauto. }
      by rewrite MTH. }
    
    forward eapply (owm_om_trans_ms_lt π τ (d + m)); eauto.
    { eapply never_set_after_after; [| apply UNSET]. lia. }
    { (* tr_sig_lt doesn't depend on concrete index *)
      admit. }
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
      destruct (decide (π' = π)) as [-> | NEQ]; [done| ].
      assert (π' ∉ (map_img (ps_phases _ δm): gset Phase)) as FRESHπ'.
      { (* should follow from phase incompatibility for δm *)
        admit. }
      replace pi with (pi, de).1; [| done]. eapply om_trans_cps_bound; eauto.
      eapply trace_valid_steps''; eauto.  
    - apply ms_le_exp_mono; [lia| ].
      admit.
  Admitted.
  
  Theorem signals_eventually_set
    (VALID: obls_trace_valid OP tr)
    (FAIR: forall τ, obls_trace_fair _ τ tr):
    (* ¬ exists sid c, never_set_after sid c.  *)
    forall sid, eventually_set sid. 
  Proof using.
    intros sid. red. intros c UNSET.
    (* red in UNSET.  *)
    pattern c in UNSET. apply ex_intro in UNSET. 
    pattern sid in UNSET. apply ex_intro in UNSET. 
    
    apply ex_prod' in UNSET. 
    eapply sets_have_min in UNSET; [| apply tr_sig_lt_wf]. clear sid c. 
    apply ex_prod in UNSET. simpl in UNSET. destruct UNSET as (s & c & UNSET & MIN).
    
    set (OTF i := TPF (s_ow s i) i).
    
    set (R := MR (ms_lt deg_le) (fun i => OTF (c + i))). 
    forward eapply well_founded_ind with (R := R) (P := fun _ => False).
    4: done.
    3: exact 0.
    { eapply measure_wf.
      admit. }
    intros i NEXT.
    (* pose proof (min_owner_PF_decr (c + i) ltac:(lia)) as D. *)
    forward eapply min_owner_PF_decr with (d := c + i); eauto.
    { lia. }
    intros (j & AFTER & DECR).
    apply (NEXT (j - c)). red. red.
    rewrite -Nat.le_add_sub; [| lia]. done. 
    
  Admitted.

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
  Proof using SET_BEFORE_SPEC.
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
    (VALID: obls_trace_valid OP tr)
    (DOM: is_Some (tr S!! (S n)))
    (ALL_SET: ∀ sid, eventually_set sid)
    :
    ms_lt deg_le (APF (S n)) (APF n).
  Proof using.
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
    intros δ τ' IDTHl. 
    red. intros δk k IDTH BOUND NSTEPS.
    
    generalize dependent δk. induction k.
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
    rewrite /sig_val_at in SB. rewrite IDTH in SB. simpl in SB.
    
    (* either it was there when the big step started,
       or it's a new signal, but then the thread holds an obligation
       and cannot wait on it *)
    assert (ps_sigs OP δ !! sid = Some (l, false)) as SIG0'.
    { admit. }
    rewrite SIG0' in SB. done. 
    
  Admitted. 

  Theorem trace_terminates
    (VALID: obls_trace_valid OP tr)
    (FAIR: forall τ, obls_trace_fair _ τ tr):
    terminating_trace tr. 
  Proof using.      
    set (R := MR (ms_lt deg_le) APF).    
    forward eapply well_founded_ind with (R := R) (P := fun _ => terminating_trace tr).
    4: done.
    3: exact 0. 
    { eapply measure_wf.
      admit. }
    intros i NEXT.

    destruct (tr S!! (S i)) eqn:ITH'.
    2: { pose proof (trace_has_len tr) as [len ?]. 
         eapply state_lookup_dom_neg in ITH'; eauto.
         lia_NO' len.
         eapply terminating_trace_equiv; eauto. }

    forward eapply om_trans_all_ms_lt; eauto.
    by apply signals_eventually_set. 
  Admitted. 

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

  Theorem obls_fair_trace_terminate:
    terminating_trace tr.
  Proof using VALID FAIR.
    Require Import Coq.Logic.ClassicalChoice.
    pose proof (choice _ set_before_ex) as [sb ?].
    eapply trace_terminates; eauto. 
  Qed. 

End TerminationFull.
