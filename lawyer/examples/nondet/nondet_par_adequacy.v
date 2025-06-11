From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From fairness Require Import utils utils_tactics trace_len utils_multisets.
From heap_lang Require Import simulation_adequacy.
From lawyer Require Import sub_action_em action_model.
From lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am unfair_termination env_helpers.
From lawyer.examples Require Import orders_lib par.
From lawyer.examples.nondet Require Import nondet_par.


Section NondetAdequacy.

  Let ND_Degree := bounded_nat 3.
  Let ND_Level := bounded_nat 2.

  Instance NDPre: ObligationsParamsPre ND_Degree ND_Level nondet_LS_LB.
    esplit; try by apply _.
    1, 2: by apply nat_bounded_PO.
  Defined.

  Local Instance ND_OP_HL: OP_HL ND_Degree ND_Level nondet_LS_LB.
  Proof. esplit; try by apply _. Defined.

  Let EM := TopAM_EM ObligationsASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).

  Definition NDΣ := #[
    GFunctor $ (exclR unitO); 
    heapΣ EM;
    parΣ
  ].
  Global Instance subG_NDΣ {Σ}: 
    subG NDΣ Σ → NondetPreG Σ.
  Proof. solve_inG. Qed.

  Let d2 := bn_ith 2 2.
  Let d1 := bn_ith 2 1.
  Let d0 := bn_ith 2 0.

  Let l__w := bn_ith 1 1.
  Let l__f := bn_ith 1 0.

  Local Instance OHE
    (HEAP: heapGS NDΣ (TopAM_EM ObligationsASEM (λ Σ (aGS : ObligationsGS Σ) τ, obls τ ∅)))
    : OM_HL_Env ND_OP_HL EM NDΣ.
  Proof.
    unshelve esplit; try by apply _. 
    - apply (@heap_fairnessGS _ _ _ HEAP).
    - apply AMU_lift_top. 
    - intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top.
  Defined.

  Theorem nondet_par_termination
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([nondet_par #()], Build_state ∅ ∅))
    (VALID: extrace_valid extr):
    extrace_fairly_terminating extr.
  Proof.
    assert (heapGpreS NDΣ EM) as HPreG.
    { apply subG_heapPreG. apply _. }

    eapply @obls_terminates_impl with
      (cps_degs := 3 *: {[+ d2 +]})
      (eb := 0); eauto.
    1-5: by apply _.
    1, 2: by apply fin_wf.

    iIntros (?) "[HEAP INIT]".

    pose proof @nondet_par_spec as SPEC. 
    specialize SPEC with 
      (OHE := OHE HEAP)
      (d0 := d0) (d1 := d1) (d2 := d2)
      (l__f := l__f) (l__w := l__w). 
    iApply (SPEC with "[-]"). 
    1, 2: apply ith_bn_lt; lia.
    { (* for nondet as the closed program, K is irrelevant *)
      apply le_0_n. }
    { simpl. iIntros (? _) "X". iApply "X". }
    { lia. }
    { apply ith_bn_lt. lia. }
    2: { simpl. iNext. iIntros (?) "(%&?&?&?&?)". iFrame. }

    rewrite START. by iApply closed_pre_helper.
  Qed.

End NondetAdequacy.
