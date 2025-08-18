Require Import Relation_Operators.
From stdpp Require Import namespaces fin_maps ssreflect fin_map_dom gmultiset.
From trillium.traces Require Import trace_lookup.
From fairness Require Import fairness locales_helpers utils utils_tactics.
From lawyer.obligations Require Import obligations_model obls_utils.


Section Wf.
  Context `{OP: ObligationsParams Degree Level Locale LIM_STEPS}.
  
  Definition obls_assigned δ :=
    dom $ filter (fun '(s, (l, b)) => b = false) (ps_sigs δ) ⊆
    flatten_gset $ map_img $ ps_obls δ.

  Lemma obls_assigned_equiv δ:
    obls_assigned δ <-> 
      forall s l, ps_sigs δ !! s = Some (l, false) ->
      map_Exists (fun τ obs => s ∈ obs) (ps_obls δ).
  Proof using.
    rewrite /obls_assigned. rewrite elem_of_subseteq.
    apply forall_proper. intros s.
    rewrite elem_of_dom.
    rewrite map_lookup_filter. simpl. 
    destruct (ps_sigs δ !! s) as [[??]| ] eqn:SIGS; rewrite SIGS; simpl. 
    2: { split; intros; try done. by destruct H0. }
    destruct b; simpl. 
    { simpl. split; intros; try done. by destruct H0. }
    rewrite -exist_impl_forall. rewrite ex_det_iff.
    2: { intros ? [=]. subst. reflexivity. }
    apply ZifyClasses.impl_morph; [set_solver| ].
    rewrite flatten_gset_spec. rewrite map_Exists_lookup.
    setoid_rewrite elem_of_map_img. set_solver.
  Qed.

  Definition dom_phases_disj δ :=
    forall τ1 τ2 π1 π2, 
      τ1 ≠ τ2 ->
      ps_phases δ !! τ1 = Some π1 ->
      ps_phases δ !! τ2 = Some π2 ->
      phases_disj π1 π2. 

  Definition eps_phase_bound δ :=
    ¬ (exists τ π ep, ps_phases δ !! τ = Some π /\
                  ep ∈ ps_eps δ /\ phase_lt π ep.1.2).

  Definition cps_phase_bound δ :=
    ¬ (exists τ π cp, ps_phases δ !! τ = Some π /\
                  cp ∈ ps_cps δ /\ phase_lt π cp.1).

  Definition obligations_are_signals δ :=
    flatten_gset $ map_img $ ps_obls δ ⊆ dom $ ps_sigs δ. 

  Definition obls_disjoint δ :=
    forall τ1 τ2, τ1 ≠ τ2 -> 
             default ∅ (ps_obls δ !! τ1) ## default ∅ (ps_obls δ !! τ2).   

  Definition is_fork (π1 π2: Phase) := exists (d: nat), π2 = ext_phase π1 d. 

  Lemma phase_le_ext_split π1 π2 d
    (LE: phase_le π1 (ext_phase π2 d)):
    π1 = ext_phase π2 d \/ phase_le π1 π2.
  Proof using.
    do 2 red in LE. destruct LE as [p EQ]. rewrite /ext_phase in EQ.
    destruct p.
    { simpl in EQ. eauto. }
    rewrite -app_comm_cons in EQ. inversion EQ. subst.
    right. red. red. exists p. eauto.
  Qed. 

  Record om_st_wf (δ: ProgressState) := {
    om_wf_dpo: dom_phases_obls δ;
    om_wf_asg: obls_assigned δ;
    om_wf_ph_disj: dom_phases_disj δ;
    om_wf_cps_ph_bound: cps_phase_bound δ;
    om_wf_eps_ph_bound: eps_phase_bound δ;
    om_wf_obls_are_sigs: obligations_are_signals δ;
    om_wf_obls_disj: obls_disjoint δ;
  }.

  Definition preserved_by 
    (R: ProgressState -> ProgressState -> Prop) (P: ProgressState -> Prop) :=
    ∀ δ1 δ2, P δ1 -> R δ1 δ2 -> P δ2.
  
  Definition preserved_by_loc_step_ex := preserved_by loc_step_ex. 

  Definition preserved_by_fork τ := preserved_by (fork_step_of τ).

  Definition preserved_by_rep_loc_step_ex :=
    fun P => forall n, preserved_by (relations.nsteps loc_step_ex n) P. 

  Definition preserved_by_progress_step τ :=
    preserved_by (progress_step_of τ). 
  Definition preserved_by_om_trans τ :=
    preserved_by (om_trans_of τ). 

  Lemma pres_by_rel_implies_rep R P
    (PRES: preserved_by R P)
    :
    forall n, preserved_by (relations.nsteps R n) P. 
  Proof.
    red. intros n. intros δ1.
    induction n.
    { simpl. intros ?? ->%nsteps_0. done. }
    intros ?? (δ'&STEP1&STEP2)%rel_compose_nsteps_next.
    apply IHn in STEP1; eauto.
  Qed.

  Lemma pres_by_loc_step_implies_rep P
    (PRES: preserved_by_loc_step_ex P)
    :
    preserved_by_rep_loc_step_ex P. 
  Proof.
    red. intros. eapply pres_by_rel_implies_rep; eauto.
  Qed.

  Lemma pres_by_loc_step_implies_progress τ P
    (PPRES: preserved_by_loc_step_ex P)
    :
    preserved_by_progress_step τ P. 
  Proof using.
    do 2 red. intros δ1 δ2 P1 STEP. 
    red in STEP. destruct STEP as (n&?&STEP).
    eapply rel_compose_mono in STEP.
    2: reflexivity.
    1: apply rel_compose_nsteps_next in STEP.
    2: { do 2 red. intros.
         eapply loc_step_with_ex. left. red. eauto. }
    eapply pres_by_loc_step_implies_rep; eauto.
  Qed.

  Lemma pres_by_loc_fork_steps_implies_om_trans τ P
    (PPRES: preserved_by_loc_step_ex P)
    (FPRES: preserved_by_fork τ P)
    :
    preserved_by_om_trans τ P. 
  Proof using.
    do 2 red. intros δ1 δ2 P1 STEP. 
    red in STEP. destruct STEP as (?&PSTEP&FSTEP).
    eapply pres_by_loc_step_implies_progress in PPRES.
    do 2 red in PPRES. specialize_full PPRES; eauto.
    inversion FSTEP; subst; try done.
    eapply FPRES; eauto. 
  Qed.

  Lemma pres_by_loc_fork_steps_implies_any_pres τ P
    (PPRES: preserved_by_loc_step_ex P)
    (FPRES: preserved_by_fork τ P)
    :
    preserved_by (obls_any_step_of τ) P. 
  Proof using.
    red. intros ??? [? | ?]; eauto.
  Qed.

  Lemma pres_by_valid_trace_strong (tr: obls_trace) i j P (T: Locale -> Prop)
    (LE: i <= j)
    (VALID: obls_trace_valid tr)
    (PPRES: preserved_by_loc_step_ex P)
    (FPRES: forall τ, T τ -> preserved_by_fork τ P)
    (Pi: from_option P True (tr S!! i))
    (Tij: forall k τ, i <= k < j -> tr L!! k = Some τ -> T τ)
    :
    from_option P True (tr S!! j). 
  Proof using.
    apply Nat.le_sum in LE as [d ->]. induction d.
    { rewrite Nat.add_0_r. done. }
    rewrite -plus_n_Sm.
    destruct (tr S!! S (i + d)) eqn:NEXT; [| done]. simpl.
    forward eapply (proj1 (next_state_lookup _ _)); eauto.
    intros [[? CUR] [? LBL]].
    rewrite CUR in IHd. simpl in IHd.
    forward eapply trace_valid_steps''; eauto.
    { rewrite Nat.add_1_r. eauto. }
    intros STEP.
    pose proof (Tij (i + d) _ ltac:(lia) LBL).
    eapply pres_by_loc_fork_steps_implies_om_trans; eauto.
    2: { apply STEP. }
    apply IHd. intros. eapply Tij; eauto. lia.  
  Qed.

  Lemma pres_by_valid_trace (tr: obls_trace) i P
    (VALID: obls_trace_valid tr)
    (PPRES: preserved_by_loc_step_ex P)
    (FPRES: forall τ, preserved_by_fork τ P)
    (Pi: from_option P True (tr S!! i)):
    forall j, i <= j -> from_option P True (tr S!! j).
  Proof using.
    intros. eapply pres_by_valid_trace_strong with (T := fun _ => True); eauto.
  Qed. 

  Lemma loc_step_dpo_pres: preserved_by_loc_step_ex dom_phases_obls.
  Proof using.
    do 2 red. intros δ1 δ2 PHASES_CORR STEP.
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *.
    - subst new_obls0. red. subst new_ps. simpl. set_solver. 
    - subst new_obls0. simpl. red. set_solver.
  Qed.

  Lemma loc_step_asg_pres: preserved_by_loc_step_ex obls_assigned.
  Proof using.
    do 2 red. intros δ1 δ2 ASG STEP.
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *. 
    - subst new_ps. red. simpl.
      subst new_sigs0 new_obls0. 
      rewrite map_filter_insert. setoid_rewrite decide_True; [| done].
      rewrite dom_insert_L.
      rewrite map_img_insert_L.
      rewrite flatten_gset_union flatten_gset_singleton.
      rewrite (union_comm_L _ {[ _ ]}) -union_assoc_L.
      apply union_mono; [done| ]. etrans; [apply ASG| ].
      simpl. rewrite {1}(map_img_sets_split_helper τ ps_obls). done. 
    - subst new_ps. red. simpl.
      subst new_sigs0 new_obls0.
      rewrite map_filter_insert. setoid_rewrite decide_False; [| done].
      rewrite map_img_insert_L.
      rewrite flatten_gset_union flatten_gset_singleton.
      apply elem_of_dom in DOM as [obls DOM].
      subst cur_loc_obls0. rewrite DOM. simpl.

      apply elem_of_subseteq. intros s' DOM'. rewrite elem_of_union. 
      rewrite elem_of_dom in DOM'. destruct DOM' as [[l' b'] DOM'].
      apply map_lookup_filter_Some in DOM' as [DOM' ->].
      apply lookup_delete_Some in DOM' as [NEQ DOM'].
      forward eapply (@ASG s').
      { simpl. apply elem_of_dom. eexists.
        eapply map_lookup_filter_Some; eauto. split; done. }
      simpl. intros ASG'.
      apply flatten_gset_spec in ASG'. destruct ASG' as (obls'&ASG'&IN').
      apply elem_of_map_img in ASG' as [τ' ASG'].
      destruct (decide (τ' = τ)) as [-> | ]. 
      { rewrite DOM in ASG'. inversion ASG'. subst. set_solver. }
      right. apply flatten_gset_spec. eexists. split; eauto.
      apply elem_of_map_img. eexists. eapply lookup_delete_Some; eauto.
  Qed.

  Lemma loc_step_dpd_pres: preserved_by_loc_step_ex dom_phases_disj.
  Proof using.
    do 2 red. intros δ1 δ2 DPD STEP.
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *.
  Qed.

  Definition phases_eq R δ1 := ps_phases δ1 = R.

  Lemma loc_step_phases_pres R: preserved_by loc_step_ex (phases_eq R).
  Proof using. 
    do 2 red. intros δ1 δ2 PH STEP.
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *.
  Qed.

  Lemma loc_step_cpb_pres': preserved_by_loc_step_ex
                                (fun δ => cps_phase_bound δ /\ dom_phases_disj δ). 
  Proof using.
    do 2 red. intros δ1 δ2 [CPB DPD] STEP.
    split.
    2: { eapply loc_step_dpd_pres; eauto.  }
    pose proof (@loc_step_phases_pres _ _ _ eq_refl ltac:(red; eauto)) as PH.
    add_case (ps_cps δ2 ⊆ ps_cps δ1) CPS_LE.
    { intros LE. red. intros (τ' & π & cp & PH2 & IN & LT).
      eapply gmultiset_elem_of_subseteq in IN; eauto.
      rewrite PH in PH2. 
      edestruct CPB; eauto. set_solver. }
    
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *.
    - apply CPS_LE. multiset_solver.
    - red. simpl. intros (τ' & π' & cp & PH2 & IN & LT).
      subst new_cps0. rewrite gmultiset_elem_of_disj_union in IN.
      destruct IN as [IN | IN].
      { edestruct CPB; eauto. set_solver. }
      apply gmultiset_elem_of_singleton in IN as ->. simpl in *.
      pose proof LT as LE''%strict_include. 
      eapply phases_disj_not_le in LE''; eauto.
      eapply DPD; eauto.
      intros ->. rewrite LOC_PHASE in PH2. inversion PH2. subst.
      apply strict_spec_alt in LT. tauto.
    - red. simpl. intros (τ' & π' & cp & PH2 & IN & LT).
      subst new_cps0. rewrite gmultiset_elem_of_disj_union in IN.
      destruct IN as [IN | IN].
      { apply gmultiset_elem_of_weaken in IN.
        edestruct CPB; eauto. set_solver. }
      apply gmultiset_elem_of_scalar_mul in IN as [? IN].
      apply gmultiset_elem_of_singleton in IN as ->. simpl in *.
      edestruct CPB; eauto. set_solver.
    - apply CPS_LE. multiset_solver.
  Qed.

  Lemma loc_step_epb_pres':
    preserved_by_loc_step_ex (fun δ => eps_phase_bound δ /\ cps_phase_bound δ /\ dom_phases_disj δ).
  Proof using.
    do 2 red. intros δ1 δ2 (EPB & CPB & DPD) STEP.
    split.
    2: { eapply loc_step_cpb_pres'; eauto. } 

    pose proof (@loc_step_phases_pres _ _ _ eq_refl ltac:(red; eauto)) as PH. 
    
    add_case (ps_eps δ2 ⊆ ps_eps δ1) EPS_LE.
    { intros LE. red. intros (τ' & π & ep & PH2 & IN & LT).
      eapply elem_of_subseteq in IN; eauto.
      rewrite PH in PH2. 
      edestruct EPB; eauto. set_solver. }
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *.
    red. intros (τ' & π' & ep & PH2 & IN & LT).
    subst new_ps new_eps0. simpl in IN.
    apply elem_of_union in IN as [IN | IN].
    { edestruct EPB; eauto. set_solver. }
    apply elem_of_singleton in IN as ->.
    simpl in *.

    (* assert (phase_lt π' π__max) as LE'. *)
    (* { eapply strict_transitive_l; eauto. }  *)

    (* move EPB at bottom. red in EPB. simpl in EPB.  *)

    red in CPB. simpl in CPB. edestruct CPB.
    do 3 eexists. eauto.
  Qed.

  Lemma loc_step_obls_sigs_pres: preserved_by_loc_step_ex obligations_are_signals.
  Proof using.
    do 2 red. intros δ1 δ2 OS STEP.
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *.
    - subst new_ps. red. simpl. subst new_obls0 new_sigs0.
      rewrite map_img_insert_L dom_insert_L.
      rewrite flatten_gset_union flatten_gset_singleton.
      rewrite (union_comm_L _ {[ _ ]}) -union_assoc_L.
      apply union_mono; [done| ].
      red in OS. simpl in OS.
      etrans; [| apply OS].
      rewrite {1}(map_img_sets_split_helper τ ps_obls). done.
    - subst new_ps. red. simpl. subst new_obls0 new_sigs0.
      etrans; [| etrans]; [| apply OS| ]; simpl.
      2: { set_solver. }
      rewrite map_img_insert_L.
      rewrite flatten_gset_union flatten_gset_singleton.
      rewrite {1}(map_img_sets_split_helper τ ps_obls). 
      subst cur_loc_obls0. set_solver.
  Qed. 

  Lemma loc_step_obls_disj_pres': 
    preserved_by_loc_step_ex (fun δ => obls_disjoint δ /\ obligations_are_signals δ).
  Proof using.
    do 2 red. intros δ1 δ2 [DPI OS] STEP.
    split.
    2: { eapply loc_step_obls_sigs_pres; eauto.  }
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *.
    - subst new_ps. red. simpl. intros τ1 τ2 NEQ.
      subst new_obls0. simpl.

      destruct (<[τ:=cur_loc_obls0 ∪ {[s0]}]> ps_obls !! τ1) eqn:L1, (<[τ:=cur_loc_obls0 ∪ {[s0]}]> ps_obls !! τ2) eqn:L2.
      all: try set_solver. simpl.
      rewrite !lookup_insert_Some in L1, L2. subst cur_loc_obls0.
      destruct L1 as [(<- & EQ1) | (NEQ1 & EQ1)], L2 as [(<- & EQ2) | (NEQ2 & EQ2)]; try done. 
      + subst g. apply disjoint_union_l. split.
        * eapply disjoint_proper. 
          3: eapply DPI; eauto.
          ** simpl. done.
          ** simpl. rewrite EQ2. done.
        * apply disjoint_singleton_l. subst s0.
          intros IN. destruct (next_sig_id_fresh (default ∅ (ps_obls !! τ) ∪ dom ps_sigs)).
          apply elem_of_union_r. 
          apply OS. simpl. apply flatten_gset_spec. eexists.
          split; eauto. eapply elem_of_map_img; eauto.
      + subst g0. apply disjoint_union_r. split.
        * symmetry. eapply disjoint_proper. 
          3: eapply DPI; eauto.
          ** simpl. done.
          ** simpl. rewrite EQ1. done.
        * symmetry. apply disjoint_singleton_l. subst s0.
          intros IN. edestruct (next_sig_id_fresh (default ∅ (ps_obls !! τ) ∪ dom ps_sigs)).
          apply elem_of_union_r. apply OS. simpl.
          apply flatten_gset_spec. eexists. split; eauto.
          eapply elem_of_map_img; eauto. 
      + forward eapply (DPI _ _ NEQ); eauto. simpl. rewrite EQ1 EQ2. set_solver.  
    - subst new_ps. red. simpl. intros τ1 τ2 NEQ.
      subst new_obls0. simpl.
      eapply disjoint_subseteq; revgoals.
      + eapply DPI; eauto.
      + simpl. destruct (decide (τ2 = τ)) as [-> | ?].
        * rewrite lookup_insert. set_solver.
        * rewrite lookup_insert_ne; done.
      + simpl. destruct (decide (τ1 = τ)) as [-> | ?].
        * rewrite lookup_insert. set_solver.
        * rewrite lookup_insert_ne; done.
      + apply _. 
  Qed.
        
  Lemma wf_preserved_by_loc_step: preserved_by loc_step_ex om_st_wf.
  Proof using.
    red. intros ?? WF1 STEP. 
    split.
    - eapply loc_step_dpo_pres; eauto. apply WF1.
    - eapply loc_step_asg_pres; eauto. apply WF1.  
    - eapply loc_step_dpd_pres; eauto. apply WF1.
    - eapply loc_step_cpb_pres'; eauto. split; apply WF1.
    - eapply loc_step_epb_pres'; eauto.
      split; [| split]; apply WF1.
    - eapply loc_step_obls_sigs_pres; eauto. apply WF1.
    - eapply loc_step_obls_disj_pres'; eauto. split; apply WF1.
  Qed.

  Lemma fork_step_obls_reorder δ1 τ δ2
    (STEP: fork_step_of τ δ1 δ2)
    (DPO1: dom_phases_obls δ1):
    flatten_gset (map_img $ ps_obls δ2) = flatten_gset (map_img $ ps_obls δ1).
  Proof using.
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst.
    assert (x ∉ dom $ ps_obls δ1) as FRESH''.
    { rewrite -DPO1; auto. }
    destruct δ1; subst; simpl in *.
subst new_obls0.
    rewrite map_img_insert_L. rewrite delete_insert_ne.
    2: { intros ->. destruct FRESH'. by apply elem_of_dom. }
    rewrite map_img_insert_L. 
    rewrite (map_img_sets_split_helper x ps_obls).
    rewrite not_elem_of_dom_1; [| done]. 
    simpl. rewrite union_empty_l_L. erewrite !delete_notin with (i := x).
    2: { by apply not_elem_of_dom. }
    rewrite (map_img_sets_split_helper τ ps_obls).
    rewrite !flatten_gset_union !flatten_gset_singleton.
    rewrite union_assoc_L. f_equal. 
    subst cur_obls0 obls' cur_obls.
    destruct (ps_obls !! τ); simpl; [| set_solver].
    apply set_eq. intros k. destruct (decide (k ∈ x0)); set_solver.
  Qed.  

  Lemma fork_step_dpo_pres τ:
    preserved_by (fork_step_of τ) dom_phases_obls. 
  Proof using.
    do 2 red. intros δ1 δ2 ASG STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst.
    destruct δ1; simpl in *.
    subst new_phases0 new_obls0.
    rewrite !dom_insert_L. set_solver.
  Qed. 

  Lemma fork_step_asg_pres' τ:
    preserved_by (fun δ1 δ2 => fork_step_of τ δ1 δ2 /\ dom_phases_obls δ1) obls_assigned.
  Proof using.
    do 2 red. intros δ1 δ2 ASG [STEP WF1].
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst.
    erewrite fork_step_obls_reorder; eauto.
    2: { red. eauto. }
    destruct δ1; subst; simpl in *. done. 
  Qed.

  Lemma ext_phase_not_le π (i j: nat) (NEQ: i ≠ j):
    ¬ phase_le (ext_phase π i) (ext_phase π j).
  Proof using.
    rewrite /ext_phase /phase_le.
    intros. intros [p PREF].
    destruct p; simpl in PREF. 
    - inversion PREF. done.
    - apply (f_equal length) in PREF. simpl in PREF.
      rewrite app_length in PREF. simpl in PREF. lia.  
  Qed. 

  Lemma phases_disj_forks π (i j: nat) (NEQ: i ≠ j):
    phases_disj (ext_phase π i) (ext_phase π j).
  Proof using.
    split; apply ext_phase_not_le; done. 
  Qed.

  Lemma phase_disj_ext π1 π2 (i: nat)
    (DISJ: phases_disj π1 π2):
    phases_disj (ext_phase π1 i) π2.
  Proof using.
    red. rewrite /ext_phase. split.  
    - intros [p ->]. red in DISJ. apply proj1 in DISJ. edestruct DISJ; eauto.
      rewrite cons_middle app_assoc. red. red. eauto.
    - intros [p EQ]. red in DISJ.
      destruct p.
      { simpl in EQ. subst. apply proj1 in DISJ. edestruct DISJ; eauto.
        red. red. exists [i]. eauto. }
      rewrite -app_comm_cons in EQ. inversion EQ. subst.
      apply proj2 in DISJ. edestruct DISJ; eauto.
      red. red. exists p. eauto.
  Qed. 

  Lemma fork_step_dpd_pres τ:
    preserved_by (fork_step_of τ) dom_phases_disj.
  Proof using.
    do 2 red. intros δ1 δ2 DPD STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst. subst ps'. simpl.
    destruct δ1; simpl in *. subst new_phases0.
    intros τ1 τ2 π1 π2. 
    rewrite !lookup_insert_Some.    
    intros NEQ [[-> <-] | [NEQ1 [[<- <-]| [NEQ1' PH1]]]] [[-> <-] | [NEQ2 [[<- <-]| [NEQ2' PH2]]]]; try tauto || by apply phases_disj_forks.
    3, 4: symmetry.
    1-3: by apply phase_disj_ext; eapply DPD; simpl; eauto. 
    { apply phase_disj_ext. eapply DPD; [apply NEQ1'| ..]; eauto. }
    eapply DPD; [apply NEQ|..]; eauto. 
  Qed.

  Lemma fork_step_cpb_pres τ: preserved_by (fork_step_of τ) cps_phase_bound.
  Proof using.
    do 2 red. intros δ1 δ2 CPB STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst. subst ps'. simpl.
    destruct δ1; simpl in *. subst new_phases0.
    repeat setoid_rewrite lookup_insert_Some.
    intros (? & ? & ? & ([[-> <-] | [NEQ [[<- <-]| [NEQ' PH]]]] & IN & LT)).
    - destruct CPB. exists τ. do 2 eexists. split; [| split]; eauto.
      etrans; eauto. apply phase_lt_fork.
    - destruct CPB. exists τ. do 2 eexists. split; [| split]; eauto.
      etrans; eauto. apply phase_lt_fork.
    - destruct CPB. exists x1. eauto.
  Qed. 

  Lemma fork_step_epb_pres τ: preserved_by (fork_step_of τ) eps_phase_bound.
  Proof using.
    do 2 red. intros δ1 δ2 EPB STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst. subst ps'. simpl.
    destruct δ1; simpl in *. subst new_phases0.
    repeat setoid_rewrite lookup_insert_Some.
    intros (? & ? & ? & ([[-> <-] | [NEQ [[<- <-]| [NEQ' PH]]]] & IN & LT)).
    - destruct EPB. exists τ. do 2 eexists. split; [| split]; eauto.
      etrans; eauto. apply phase_lt_fork.
    - destruct EPB. exists τ. do 2 eexists. split; [| split]; eauto.
      etrans; eauto. apply phase_lt_fork.
    - destruct EPB. exists x1. eauto.
  Qed. 

  Lemma fork_step_obls_sigs_pres τ: preserved_by (fun δ1 δ2 => fork_step_of τ δ1 δ2 /\ dom_phases_obls δ1) obligations_are_signals.
  Proof using.
    do 2 red. intros δ1 δ2 OS [STEP DPO1].
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP; subst.
    erewrite fork_step_obls_reorder; eauto.
    2: { red. eauto. }
    destruct δ1; simpl in *. done.
  Qed.

  Lemma fork_step_obls_disj_pres τ:
    preserved_by (fork_step_of τ) obls_disjoint. 
  Proof using.
    do 2 red. intros δ1 δ2 OS STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP; subst.
    destruct δ1; simpl in *. subst new_obls0.
    intros τ1 τ2 NEQ. 
    rewrite !insert_union_singleton_l !lookup_union.
    rewrite !lookup_map_singleton.
    
    repeat destruct decide; subst; try tauto.
    all: repeat rewrite union_Some_l; repeat rewrite option_union_left_id; simpl; subst obls' cur_obls cur_obls0.
    - eapply disjoint_subseteq.
      4: { apply OS, NEQ. }
      { apply _. }
      all: set_solver.
    - set_solver. 
    - eapply disjoint_subseteq.
      4: { symmetry. apply OS, n1. }
      { apply _. }
      all: simpl; set_solver.
    - set_solver.
    - eapply disjoint_subseteq.
      4: { symmetry. apply OS, n1. }
      { apply _. }
      all: simpl; set_solver.
    - eapply disjoint_subseteq.
      4: { apply OS, n0. }
      { apply _. }
      all: simpl; set_solver.
    - eapply disjoint_subseteq.
      4: { apply OS, n0. }
      { apply _. }
      all: simpl; set_solver.
    - eapply disjoint_subseteq.
      4: { apply OS, n0. }
      { apply _. }
      all: simpl; set_solver.
    - eapply disjoint_subseteq; eauto. apply _. 
  Qed.     

  Lemma wf_preserved_by_fork_step τ: preserved_by (fork_step_of τ) om_st_wf.
  Proof using.
    red. intros ?? WF1 STEP. 
    split.
    - eapply fork_step_dpo_pres; eauto. apply WF1.
    - eapply fork_step_asg_pres'; [| split]; eauto; apply WF1.
    - eapply fork_step_dpd_pres; eauto. apply WF1.
    - eapply fork_step_cpb_pres; eauto. apply WF1.
    - eapply fork_step_epb_pres; eauto. apply WF1.
    - eapply fork_step_obls_sigs_pres; [| split]; eauto; apply WF1.
    - eapply fork_step_obls_disj_pres; eauto. apply WF1.
  Qed.

  Lemma om_trans_wf_pres τ: preserved_by (om_trans_of τ) om_st_wf.
  Proof using.
    apply pres_by_loc_fork_steps_implies_om_trans.
    - apply wf_preserved_by_loc_step.
    - apply wf_preserved_by_fork_step.
  Qed.
    
  Definition dom_obls_eq R δ1 := dom $ ps_obls δ1 = R.
      
  Lemma loc_step_dom_obls_pres R: preserved_by loc_step_ex (dom_obls_eq R).
  Proof using.
    do 2 red. intros δ1 δ2 OE STEP. 
    add_case (dom $ ps_obls δ2 = dom $ ps_obls δ1) SAME.
    { intros EQ. by rewrite EQ. }
    inv_loc_step_ex STEP; destruct δ1; try done; simpl in *.
    - subst new_obls0. rewrite dom_insert_L. simpl. set_solver.
    - subst new_obls0. rewrite dom_insert_L. simpl. set_solver.
  Qed.

End Wf.
