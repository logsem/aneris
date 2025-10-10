From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From fairness Require Import utils.
From heap_lang Require Import simulation_adequacy.
From lawyer Require Import sub_action_em action_model.
From lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am env_helpers.
From lawyer.examples.eo_fin Require Import eo_fin.
From lawyer.examples Require Import orders_lib signal_map.


Section EOFinAdequacy.
  Context (B: nat).

  Existing Instance EO_OP'. 

  Local Instance EOF_OP_HL: OP_HL (EODegree 5) (EOLevel (B + 1)) 10.
  Proof.
    esplit; try by apply _.
  Defined.

  Let EM := TopAM_EM ObligationsASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).

  Let eofinΣ: gFunctors := #[
      GFunctor (excl_authR natO); 
      sig_mapΣ;
      heapΣ EM
  ].

  Global Instance subG_eofinΣ {Σ}: subG eofinΣ Σ → EoFinPreG Σ.
  Proof. solve_inG. Qed.

  Local Instance OHE
    (HEAP: heapGS eofinΣ (TopAM_EM ObligationsASEM (λ Σ (aGS : ObligationsGS Σ) τ, obls τ ∅)))
    : OM_HL_Env EOF_OP_HL EM eofinΣ.
  Proof.
    unshelve esplit; try by apply _. 
    - apply (@heap_fairnessGS _ _ _ HEAP).
    - apply AMU_lift_top. 
    - intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top.
  Defined.

  Lemma eofin_terminates_impl
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([start #(0%nat) #B], Build_state ∅ ∅)):
    extrace_fairly_terminating extr. 
  Proof.
    assert (heapGpreS eofinΣ EM) as HPreG.
    { apply subG_heapPreG. apply _. }

    eapply @obls_terminates_impl with
      (cps_degs := (2 * B + 5) *: {[+ d2 B +]} ⊎ 50 *: {[+ d0 B +]})
      (eb := 20); eauto.
    1-5: by apply _.
    1-2: by apply fin_wf.
    { apply _. }

    iIntros (?) "[HEAP INIT]".
    pose proof @main_spec as SPEC. 
    specialize SPEC with 
      (OHE := OHE HEAP)
      .

    iApply (SPEC with "[-]"). 
    { simpl. iIntros (? _) "X". iApply "X". }
    2: { simpl. iNext. iIntros (_) "X". iApply "X". }

    simpl. rewrite START.
    rewrite /obls_init_resource /init_om_state. 
      
    rewrite init_phases_helper.
    rewrite locales_of_cfg_simpl. simpl.
    rewrite union_empty_r_L.
    iDestruct "INIT" as "(CPS & SIGS & OB & EPS & PH & EB)".
    rewrite /cps_repr /sig_map_repr /eps_repr /obls_map_repr.
    rewrite obligations_resources.obls_unseal. 
    rewrite big_sepM_singleton. 
    rewrite fmap_empty.
    rewrite !gset_to_gmap_singleton. 
    rewrite map_fmap_singleton.      
    iFrame. rewrite big_sepS_empty. iApply bi.sep_assoc. iSplitL; [| done]. 
    rewrite mset_map_disj_union. rewrite big_sepMS_disj_union.
    rewrite !mset_map_mul !mset_map_singleton.

    rewrite -!(cp_mul_alt (oGS := (@heap_fairnessGS _ _ _ HEAP))).
    iDestruct "CPS" as "[CPS2 CPS0]". 
    iSplitL "CPS2"; (iApply cp_mul_weaken; [..| by iFrame]); apply phase_lt_fork || lia. 
  Qed.

End EOFinAdequacy.

Theorem eofin_terminates (N: nat):
  forall extr,
    trfirst extr = ([start #(0%nat) #N], Build_state ∅ ∅) ->
    extrace_fairly_terminating extr.
Proof using.
  intros. eapply eofin_terminates_impl; eauto.  
Qed.
