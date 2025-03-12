From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import utils utils_tactics trace_len utils_multisets.
From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am unfair_termination.
From trillium.fairness.lawyer.examples Require Import orders_lib.
From trillium.fairness.lawyer.examples.nondet Require Import nondet.


Section NondetAdequacy.

  Instance NDPre: ObligationsParamsPre (bounded_nat 2) unit nondet_LS_LB. 
    esplit; try by apply _.
    - apply nat_bounded_PO. 
    - apply unit_PO. 
  Defined.

  Definition NDOP := LocaleOP (Locale := locale heap_lang). 
  Existing Instance NDOP.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).
  Let OM := ObligationsModel. 
  Let M := AM2M ObligationsAM. 

  Definition NDΣ := #[
    GFunctor $ (exclR unitO); 
    heapΣ EM
  ].
  Global Instance subG_NDΣ {Σ}: 
    subG NDΣ Σ → NondetPreG Σ.
  Proof. solve_inG. Qed.

  Let d1 := bn_ith 1 1.
  Let d0 := bn_ith 1 0.

  Theorem nondet_termination
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([nondet #()], Build_state ∅ ∅))
    (VALID: extrace_valid extr):
    extrace_fairly_terminating extr.
  Proof.
    assert (heapGpreS NDΣ EM) as HPreG.
    { apply _. }

    eapply @obls_terminates_impl with
      (cps_degs := 2 *: {[+ d1 +]})
      (eb := 0); eauto.
    1-5: by apply _.
    { apply unit_WF. }
    { apply fin_wf. } 

    iIntros (?) "[HEAP INIT]".

    pose proof @nondet_spec as SPEC. 
    specialize SPEC with 
      (OPRE := NDPre) (hGS := HEAP) (oGS' := (@heap_fairnessGS _ _ _ HEAP))
      (d0 := d0) (d1 := d1).
    iApply (SPEC with "[-]"). 
    { exact tt. }
    { apply ith_bn_lt; lia. }
    { (* for nondet as the closed program, K is irrelevant *)
      apply le_0_n. }
    { apply AMU_lift_top. }
    { intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top. }
    { simpl. iIntros (? _) "X". iApply "X". }
    { lia. }
    2: { simpl. iNext. iIntros (?) "(%&% &?&?&?&?)". iFrame. }

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

End NondetAdequacy.
