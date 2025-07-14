From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From fairness Require Import utils utils_tactics utils_multisets.
From heap_lang Require Import simulation_adequacy.
From lawyer Require Import sub_action_em action_model.
From lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am unfair_termination env_helpers.
From lawyer.examples Require Import orders_lib.
From lawyer.examples.nondet Require Import nondet.


Section NondetAdequacy.

  Instance NDPre: ObligationsParamsPre (bounded_nat 2) unit nondet_LS_LB.
    esplit; try by apply _.
    - apply nat_bounded_PO.
    - apply unit_PO.
  Defined.

  Local Instance ND_OP_HL: OP_HL (bounded_nat 2) unit nondet_LS_LB.
  Proof. esplit; try by apply _. Defined.

  Let EM := TopAM_EM ObligationsASEM (fun {Σ} {aGS: asem_GS Σ} τ _ => obls τ ∅ (oGS := aGS)).

  Definition NDΣ := #[
    GFunctor $ (exclR unitO); 
    iemΣ HeapLangEM EM
  ].
  Global Instance subG_NDΣ {Σ}: 
    subG NDΣ Σ → NondetPreG Σ.
  Proof. solve_inG. Qed.

  Let d1 := bn_ith 1 1.
  Let d0 := bn_ith 1 0.

  Local Instance OHE
    (HEAP: @heapGS NDΣ _ (TopAM_EM ObligationsASEM (λ Σ (aGS : ObligationsGS Σ) τ _, obls τ ∅)))
    : OM_HL_Env ND_OP_HL EM NDΣ.
  Proof.
    unshelve esplit; try by apply _. 
    - apply (@heap_fairnessGS _ _ _ HEAP).
    - apply AMU_lift_top. 
    - intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top.
  Defined.

  Instance NDΣ_pre: @IEMGpreS _ _ HeapLangEM EM NDΣ.
  Proof.
    split; try by (apply _ || solve_inG).
    - simpl. apply _.
    - simpl. apply obls_Σ_pre. apply _.
  Qed.

  Theorem nondet_termination
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([nondet #()], Build_state ∅ ∅))
    (VALID: extrace_valid extr):
    extrace_fairly_terminating extr.
  Proof.
    assert (@heapGpreS NDΣ _ EM) as HPreG.
    { econstructor. }

    eapply @obls_terminates_impl with
      (cps_degs := 2 *: {[+ d1 +]})
      (eb := 0); eauto.
    1-5: by apply _.
    { apply unit_WF. }
    { apply fin_wf. }

    iIntros (?) "[HEAP INIT]".

    pose proof @nondet_spec as SPEC. 
    specialize SPEC with 
      (OHE := OHE HEAP)
      (d0 := d0) (d1 := d1).
    iApply (SPEC with "[-]"). 
    { exact tt. }
    { apply ith_bn_lt; lia. }
    { (** for nondet as the closed program, K is irrelevant *)
      apply le_0_n. }
    { simpl. iIntros (? _) "X". iApply "X". }
    { lia. }
    2: { simpl. iNext. iIntros (?) "(%&% &?&?&?&?)". iFrame. }

    rewrite START. by iApply closed_pre_helper.
  Qed.

  Definition conf_init_pre (cnt flag: loc) := ([stop_and_read #cnt #flag; incr_loop #cnt #flag], Build_state {[ cnt := #0; flag := #false ]} ∅). 

  Definition δ_init_pre: ProgressState := 
      {| ps_cps := 30 *: {[+ (π0, d0) +]};
         ps_sigs := {[ 0 := (tt, false) ]};
         ps_obls := {[ 0 := {[ 0 ]}; 1 := ∅ ]};
         ps_eps := {[ (0, π0, d0) ]};
         ps_phases := {[ 0 := ext_phase π0 0; 1 := ext_phase π0 1 ]};
         ps_exc_bound := 30 |}. 

  Lemma init_pre_is_init cnt flag:
    obls_is_init_st (conf_init_pre cnt flag) δ_init_pre.
  Proof using.
    rewrite /conf_init_pre /δ_init_pre. 
    repeat split; simpl. 
    - red. simpl. set_solver.
    - simpl in *. repeat rewrite lookup_insert_Some in H0, H1.
      destruct H0 as [[<- <-] | [? [[<- <-] | [? ?]]]], H1 as [[<- <-] | [? [[<- <-] | [? ?]]]].
      all: try set_solver.
      all: by apply obligations_wf.ext_phase_not_le.
    - simpl in *. repeat rewrite lookup_insert_Some in H0, H1.
      destruct H0 as [[<- <-] | [? [[<- <-] | [? ?]]]], H1 as [[<- <-] | [? [[<- <-] | [? ?]]]].
      all: try set_solver.
      all: by apply obligations_wf.ext_phase_not_le.
    - red. simpl. intros (?&?&?& IN&IN'&LT).
      repeat rewrite lookup_insert_Some in IN.
      apply gmultiset_elem_of_scalar_mul in IN' as (?&IN').
      apply gmultiset_elem_of_singleton in IN'. subst.
      simpl in LT.
      destruct IN as [[<- <-] | [? [[<- <-] | [? ?]]]]; try set_solver.
      all: apply strict_spec in LT as (_&LT); apply LT; apply phase_lt_fork. 
    - red. simpl. intros (?&?&?& IN&IN'&LT).
      repeat rewrite lookup_insert_Some in IN.
      apply elem_of_singleton in IN'. subst.
      simpl in LT.
      destruct IN as [[<- <-] | [? [[<- <-] | [? ?]]]]; try set_solver.
      all: apply strict_spec in LT as (_&LT); apply LT; apply phase_lt_fork.
    - red. simpl. set_solver.
    - red. simpl. intros.
      destruct τ1 as [|[|]], τ2 as [|[|]]; simpl; try set_solver.
      + rewrite lookup_insert. repeat (rewrite lookup_insert_ne; [| done]).
        set_solver. 
      + do 1 (rewrite lookup_insert_ne; [| done]).
        rewrite lookup_singleton_ne; [| done].
        set_solver. 
      + do 3 (rewrite lookup_insert_ne; [| done]). done.
  Qed.

  Lemma init_live_tids cnt flag:
    obls_fairness_preservation.om_live_tids id locale_enabled
      (conf_init_pre cnt flag) δ_init_pre.
  Proof using.
    rewrite /conf_init_pre /δ_init_pre.
    red. rewrite /has_obls /locale_enabled. simpl.
    intros ?. destruct ζ as [|[|]].
    - rewrite lookup_insert. intros _.
      eexists _. simpl.
      rewrite from_locale_lookup. simpl. eauto.
    - rewrite lookup_insert_ne; [| done]. rewrite lookup_insert.
      set_solver.
    - repeat (rewrite lookup_insert_ne; [| done]). set_solver. 
  Qed.

  Theorem nondet_pre_allocated_termination
    (extr : heap_lang_extrace)    
    (cnt: loc := Loc 15) (flag: loc := Loc 47) (** arbitrary locations for counter and flag*)
    (START: trfirst extr = conf_init_pre cnt flag)
    (VALID: extrace_valid extr):
    extrace_fairly_terminating extr.
  Proof.
    assert (@heapGpreS NDΣ _ EM) as HPreG.
    { econstructor. }
    
    eapply @obls_terminates_impl_multiple with
      (δ := δ_init_pre); eauto.
    1-2: by apply _.
    { apply unit_WF. }
    { apply fin_wf. }
    { simpl. lia. }
    { apply init_pre_is_init. }
    { apply init_live_tids. }

    iIntros (?) "[HEAP INIT]". simpl.
    rewrite big_sepM_insert.
    2: { rewrite lookup_insert_ne; done. }
    rewrite big_sepM_singleton.
    iDestruct "HEAP" as "[CNT FLAG]".

    rewrite /obls_init_resource. iDestruct "INIT" as "(CPS & SIGS & OBS & #EPS & PHS & #EB)".
    simpl. rewrite /sig_map_repr /obls_map_repr. simpl.
    rewrite map_fmap_singleton. rewrite !fmap_insert fmap_empty insert_empty.   

    replace #0 with #0%nat by done.

    rewrite insert_union_singleton_l. rewrite -gmap_op_union.
    2: { apply map_disjoint_dom. set_solver. }
    rewrite auth_frag_op own_op. iDestruct "OBS" as "[OB0 OB1]".
    pose proof @alloc_nondet_inv_impl.
    specialize (H _ _ _ ND_OP_HL _ EM NDΣ (OHE HEAP) () 0 _ 0 cnt flag 0).

    iApply fupd_mask_mono; [apply empty_subseteq| ]. 
    iMod (H with "[$] [$] [$] [$] []") as "foo".
    { iApply (exc_lb_le with "[$]"). lia. }
    iDestruct "foo" as (ND) "(#INV & OB0 & #SGN' & TOK)".
    iModIntro. rewrite bi.sep_assoc. iSplit; [| done].
    rewrite big_sepM_insert.
    2: { rewrite lookup_insert_ne; done. }
    rewrite big_sepM_singleton. iDestruct "PHS" as "[PH0 PH1]".
    pose proof (cp_mul_alt π0 d0 30). rewrite -H0. clear H0.
    replace 30 with (15 + 15) by lia. iDestruct (cp_mul_split with "CPS") as "[CPS0 CPS1]". 
    iSplitL "OB0 PH0 CPS0 TOK".
    - pose proof @stop_and_read_spec as SPEC. 
      specialize SPEC with (OHE := OHE HEAP) (d0 := d0) (d1 := d1) (l__f := ()).
      iApply (SPEC with "[-]").
      { apply ith_bn_lt; lia. }
      { (** for nondet as the closed program, K is irrelevant *)
        apply le_0_n. }
      { simpl. iIntros (? _) "X". iApply "X". }
      { lia. }
      2: { simpl. iNext. iIntros (?) "(%&% &?&?&?&?)". iFrame. }
      iFrame "INV PH0 TOK SGN' OB0".      
      iSplitR. 
      + iApply (exc_lb_le with "[$]"). lia.
      + iApply (cp_mul_weaken with "[$]").
        * apply phase_lt_fork.
        * lia.
    - pose proof @incr_loop_spec as SPEC. 
      specialize SPEC with (OHE := OHE HEAP) (d0 := d0) (l__f := ()).
      iApply (SPEC with "[-]").
      4: { by iIntros "!> % ?". }
      2: lia.
      2: iFrame "INV PH1 OB1".
      { lia. }
      iSplitL. 
      + iApply (cp_mul_weaken with "[$]").
        * apply phase_lt_fork.
        * lia.
      + rewrite /eps_repr.
        rewrite /ep. iExists _. iFrame "EPS".
        iPureIntro. apply phase_lt_fork.
  Qed.

End NondetAdequacy.
