From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import utils utils_tactics trace_len utils_multisets.
From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am unfair_termination.
From trillium.fairness.lawyer.examples Require Import orders_lib.
From trillium.fairness.lawyer.examples.rt_bound Require Import rt_bound.
From trillium.fairness.lawyer.examples.nondet Require Import nondet nondet_adequacy.
From trillium.fairness.lawyer.examples.const_term Require Import const_term const_term_adequacy.


Section RTBAdequacy.

  Definition LB := max_list [ nondet.nondet_LS_LB; S DECR_ITER_LEN]. 

  Instance RTBPre: ObligationsParamsPre (bounded_nat 2) unit LB. 
    esplit; try by apply _.
    - apply nat_bounded_PO. 
    - apply unit_PO. 
  Defined.

  Definition RTBOP := LocaleOP (Locale := locale heap_lang). 
  Existing Instance RTBOP.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).
  Let OM := ObligationsModel. 
  Let M := AM2M ObligationsAM. 

  Definition RTBΣ := #[
    NDΣ;
    CTΣ;
    heapΣ EM
  ].
  Global Instance subG_DecrΣ {Σ}: 
    subG RTBΣ Σ → DecrPreG Σ.
  Proof. solve_inG. Qed.
  Global Instance subG_NDΣ {Σ}: 
    subG RTBΣ Σ → NondetPreG Σ.
  Proof. solve_inG. Qed.

  Let d1 := bn_ith 1 1.
  Let d0 := bn_ith 1 0.

  Theorem rt_bound_termination
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([rt_bound #()], Build_state ∅ ∅))
    (VALID: extrace_valid extr):
    extrace_fairly_terminating extr.
  Proof.
    assert (heapGpreS RTBΣ EM) as HPreG.
    { apply _. }

    eapply @obls_terminates_impl with
      (cps_degs := 5 *: {[+ d1 +]})
      (eb := 0); eauto.
    1-5: by apply _.
    { apply unit_WF. }
    { apply fin_wf. } 

    iIntros (?) "[HEAP INIT]".

    pose proof @rt_bound_spec as SPEC. 
    specialize SPEC with 
      (OPRE := RTBPre) (hGS := HEAP) (oGS' := (@heap_fairnessGS _ _ _ HEAP))
      (d0 := d0) (d1 := d1).
    iApply (SPEC with "[-]"). 
    { exact tt. }
    { apply ith_bn_lt; lia. } 
    { apply AMU_lift_top. }
    { intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top. }
    { simpl. iIntros (? _) "X". iApply "X". }
    { unfold LB. apply max_list_elem_of_le. apply elem_of_list_here. }
    { unfold LB. apply max_list_elem_of_le. apply elem_of_list_further, elem_of_list_here. }
    2: { simpl. iNext. iIntros (?) "?". iFrame. }

    clear SPEC.
    rewrite START. simpl.
    rewrite /obls_init_resource /init_om_state.      
    rewrite init_phases_helper.
    rewrite locales_of_cfg_simpl. simpl.
    iDestruct "INIT" as "(CPS & SIGS & OB & EPS & PH & EB)".
    rewrite union_empty_r_L !gset_to_gmap_singleton.
    rewrite big_sepM_singleton. iFrame.  
    rewrite /cps_repr /sig_map_repr /eps_repr /obls_map_repr.
    rewrite !fmap_empty map_fmap_singleton.      
    iFrame.
    rewrite !mset_map_mul !mset_map_singleton.
    rewrite -!(cp_mul_alt (oGS := (@heap_fairnessGS _ _ _ HEAP))).
    iApply cp_mul_weaken; [..| by iFrame]; apply phase_lt_fork || lia. 
  Qed.

End RTBAdequacy.
