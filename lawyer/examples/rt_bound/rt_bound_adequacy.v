From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From fairness Require Import utils utils_tactics utils_multisets.
From heap_lang Require Import simulation_adequacy.
From lawyer Require Import sub_action_em action_model.
From lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am unfair_termination env_helpers.
From lawyer.examples Require Import orders_lib.
From lawyer.examples.rt_bound Require Import rt_bound.
From lawyer.examples.nondet Require Import nondet_par nondet_par_adequacy.
From lawyer.examples.const_term Require Import const_term const_term_adequacy.


Section RTBAdequacy.

  Let RTB_Degree := bounded_nat 3.
  Let RTB_Level := bounded_nat 2.

  Definition LB := max_list [ nondet_par.nondet_LS_LB; S DECR_ITER_LEN]. 

  Instance RTBPre: ObligationsParamsPre RTB_Degree RTB_Level LB. 
    esplit; try by apply _.
    1, 2: by apply nat_bounded_PO. 
  Defined.

  Local Instance RTB_OP_HL: OP_HL RTB_Degree RTB_Level LB.
  Proof. esplit; try by apply _. Defined.

  Let EM := TopAM_EM ObligationsASEM (fun {Σ} {aGS: asem_GS Σ} τ _ => obls τ ∅ (oGS := aGS)).

  Definition RTBΣ := #[
    NDΣ;
    CTΣ;
    iemΣ HeapLangEM EM;
    par.parΣ
  ].
  Global Instance subG_DecrΣ {Σ}: 
    subG RTBΣ Σ → DecrPreG Σ.
  Proof. solve_inG. Qed.
  Global Instance subG_NDΣ {Σ}: 
    subG RTBΣ Σ → NondetPreG Σ.
  Proof. solve_inG. Qed.

  Let d2 := bn_ith 2 2.
  Let d1 := bn_ith 2 1.
  Let d0 := bn_ith 2 0.

  Let l__w := bn_ith 1 1.
  Let l__f := bn_ith 1 0.

  Local Instance OHE
    (HEAP: @heapGS RTBΣ _ (TopAM_EM ObligationsASEM (λ Σ (aGS : ObligationsGS Σ) τ _, obls τ ∅)))
    : OM_HL_Env RTB_OP_HL EM RTBΣ.
  Proof.
    unshelve esplit; try by apply _. 
    - apply (@heap_fairnessGS _ _ _ HEAP).
    - apply AMU_lift_top. 
    - intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top.
  Defined.

  Instance RTBΣ_pre: @IEMGpreS _ _ HeapLangEM EM RTBΣ.
  Proof.
    split; try by (apply _ || solve_inG).
    - simpl. apply subG_heap1PreG. apply _. 
    - simpl. apply obls_Σ_pre. apply _.
  Qed.

  Theorem rt_bound_termination
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([rt_bound #()], Build_state ∅ ∅))
    (VALID: extrace_valid extr):
    extrace_fairly_terminating extr.
  Proof.
    assert (@heapGpreS RTBΣ _ EM) as HPreG.
    { econstructor. }

    eapply @obls_terminates_impl with
      (cps_degs := 7 *: {[+ d2 +]})
      (eb := 0); eauto.
    1, 2: by apply _.
    1, 2: by apply fin_wf.

    iIntros (?) "[HEAP INIT]".

    pose proof @rt_bound_spec as SPEC. 
    specialize SPEC with 
      (OHE := OHE HEAP)
      (d0 := d0) (d1 := d1) (d2 := d2)
      (l__f := l__f) (l__w := l__w). 
    iApply (SPEC with "[-]").
    1-3: apply ith_bn_lt; lia.
    { simpl. iIntros (? _) "X". iApply "X". }
    { unfold LB. apply max_list_elem_of_le. apply elem_of_list_here. }
    { unfold LB. apply max_list_elem_of_le. apply elem_of_list_further, elem_of_list_here. }
    2: { simpl. iNext. iIntros (?) "?". iFrame. }

    rewrite START. by iApply closed_pre_helper.
  Qed.

End RTBAdequacy.
