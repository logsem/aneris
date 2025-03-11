From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import utils.
From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import sub_action_em action_model.
From trillium.fairness.lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am.
From trillium.fairness.lawyer.examples.const_term Require Import const_term.


Section ConstTermAdequacy.

  (* TODO: move these relations to lib *)
  Definition unit_rel (_: unit) (_: unit) := True. 

  Global Instance unit_PO: PartialOrder unit_rel.
  Proof using.
    split.
    - split; done.
    - red. by intros [] [].
  Qed.

  Lemma unit_WF: wf (strict unit_rel).
  Proof using.
    red. intros x. constructor.
    intros y NE. destruct x, y.
    by apply strict_ne in NE.
  Qed.

  Definition empty_rel (_: Empty_set) (_: Empty_set) := True.

  Global Instance empty_PO: PartialOrder empty_rel.
  Proof using.
    split. 
    - split; done.
    - red. done.
  Qed.  

  Lemma empty_WF: wf (strict empty_rel).
  Proof using. done. Qed.

  Instance CTPre: ObligationsParamsPre unit Empty_set 0. 
    esplit; try by apply _.
    - apply unit_PO. 
    - apply empty_PO. 
  Defined.

  Definition CTOP := LocaleOP (Locale := locale heap_lang). 
  Existing Instance CTOP.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).
  Let OM := ObligationsModel. 
  Let M := AM2M ObligationsAM. 

  Definition CTΣ := #[
    GFunctor $ (excl_authUR natO); 
    heapΣ EM
  ].
  Global Instance subG_CTΣ {Σ}: 
    subG CTΣ Σ → DecrPreG Σ.
  Proof. solve_inG. Qed.

  Lemma const_term_terminates N
    (prog := const_term N)
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([prog #()], Build_state ∅ ∅)):
    extrace_fairly_terminating extr.
  Proof.
    assert (heapGpreS CTΣ EM) as HPreG.
    { apply _. }

    eapply @obls_terminates_impl with
      (cps_degs := ((N + 2) * 10) *: {[+ () +]})
      (eb := 0); eauto.
    1-5: by apply _.
    { apply empty_WF. }
    { apply unit_WF. }

    iIntros (?) "[HEAP INIT]".

    pose proof @const_term_spec as SPEC. specialize SPEC with (OPRE := CTPre) (hGS := HEAP) (oGS' := (@heap_fairnessGS _ _ _ HEAP)).

    iApply (SPEC with "[-]").
    { apply AMU_lift_top. }
    { intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top. }
    { simpl. iIntros (? _) "X". iApply "X". }
    2: { simpl. iNext. iIntros (_) "X". iApply "X". }

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

End ConstTermAdequacy.

