From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From trillium.traces Require Import trace_len.
From fairness Require Import utils utils_tactics utils_multisets.
From heap_lang Require Import simulation_adequacy.
From lawyer Require Import sub_action_em action_model.
From lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am unfair_termination env_helpers.
From lawyer.examples Require Import orders_lib.
From lawyer.examples.lf_counter Require Import lf_counter.


Section LFCAdequacy.

  Let LS := 2 + INCR_ITER_LEN.

  Instance LFCPre: ObligationsParamsPre (bounded_nat 2) Empty_set LS. 
    esplit; try by apply _.
    - apply nat_bounded_PO. 
    - apply empty_PO. 
  Defined.

  Local Instance LFC_OP_HL: OP_HL (bounded_nat 2) Empty_set LS.
  Proof. esplit; try by apply _. Defined.

  Let EM := TopAM_EM ObligationsASEM (fun {Σ} {aGS: asem_GS Σ} τ _ => obls τ ∅ (oGS := aGS)).

  Definition LFCΣ := #[
    GFunctor $ (authUR (gmapUR nat natUR)); 
    (* heapΣ EM *)
    iemΣ HeapLangEM EM
  ].
  Global Instance subG_LFCΣ {Σ}: 
    subG LFCΣ Σ → LFCPreG Σ.
  Proof. solve_inG. Qed.

  Let d1 := bn_ith 1 1.
  Let d0 := bn_ith 1 0.

  Local Instance OHE
    (HEAP: @heapGS LFCΣ _ (TopAM_EM ObligationsASEM (λ Σ (aGS : ObligationsGS Σ) τ _, obls τ ∅)))
    : OM_HL_Env LFC_OP_HL EM LFCΣ.
  Proof.
    unshelve esplit; try by apply _. 
    - apply (@heap_fairnessGS _ _ _ HEAP).
    - apply AMU_lift_top. 
    - intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top.
  Defined.

  Instance LFCΣ_pre: @IEMGpreS _ _ HeapLangEM EM LFCΣ.
  Proof.
    split; try by (apply _ || solve_inG).
    - simpl. apply _.
    - simpl. apply obls_Σ_pre. apply _.
  Qed.

  Theorem lf_counter_termination
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([counter_client #()], Build_state ∅ ∅))
    (VALID: extrace_valid extr):
    terminating_trace extr.
  Proof.
    assert (@heapGpreS LFCΣ _ EM) as HPreG.
    { econstructor. }

    forward eapply @obls_match_impl with
      (cps_degs := 5 *: {[+ d1 +]})
      (eb := 0); eauto.
    1-5: by apply _.
    2: { intros (omtr & MATCH & TR_WF & FIRST).
         eapply traces_match_preserves_termination; eauto.
         apply always_term_wo_lvls; eauto.
         { eapply traces_match_valid2; eauto. }
         apply fin_wf. } 

    iIntros (?) "[HEAP INIT]".

    pose proof @counter_client_spec as SPEC. 
    specialize SPEC with 
      (OHE := OHE HEAP)
      (d0 := d0) (d1 := d1).
    iApply (SPEC with "[-]"). 
    { apply ith_bn_lt; lia. }
    { reflexivity. }
    { simpl. iIntros (? _) "X". iApply "X". }
    2: { simpl. iNext. iIntros (?) "?". iFrame. }

    rewrite START. by iApply closed_pre_helper.
  Qed.

End LFCAdequacy.
