From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.proofmode Require Import tactics.
From fairness Require Import utils utils_tactics trace_len utils_multisets.
From heap_lang Require Import simulation_adequacy heap_lang_defs.
From lawyer Require Import sub_action_em action_model.
From lawyer.obligations Require Import obligations_adequacy obligations_logic obligations_em obligations_resources obligations_model obligations_am unfair_termination env_helpers.
From lawyer.examples Require Import orders_lib.
From lawyer.examples.const_term Require Import const_term.


Section ConstTermAdequacy.

  Instance CTPre: ObligationsParamsPre unit Empty_set 0. 
    esplit; try by apply _.
    - apply unit_PO. 
    - apply empty_PO. 
  Defined.

  Local Instance CT_OP_HL: OP_HL unit Empty_set 0.
  Proof. esplit; try by apply _. Defined.

  Let EM := TopAM_EM ObligationsASEM (fun {Σ} {aGS: asem_GS Σ} τ => obls τ ∅ (oGS := aGS)).

  Definition CTΣ := #[
    GFunctor $ (excl_authUR natO); 
    heapΣ EM
  ].
  Global Instance subG_CTΣ {Σ}: 
    subG CTΣ Σ → DecrPreG Σ.
  Proof. solve_inG. Qed.

  Local Instance OHE
    (HEAP: heapGS CTΣ (TopAM_EM ObligationsASEM (λ Σ (aGS : ObligationsGS Σ) τ, obls τ ∅)))
    : OM_HL_Env CT_OP_HL EM CTΣ.
  Proof.
    unshelve esplit; try by apply _. 
    - apply (@heap_fairnessGS _ _ _ HEAP).
    - apply AMU_lift_top. 
    - intros. rewrite /AMU_lift_MU__f.
      rewrite -nclose_nroot.
      apply AMU_lift_top.
  Defined.

  Theorem const_term_bound_termination N
    (prog := const_term N)
    (bound := (N + 2) * 10)
    (extr : heap_lang_extrace)
    (START: trfirst extr = ([prog #()], Build_state ∅ ∅))
    (VALID: extrace_valid extr):
    trace_len_le extr (bound + 1). 
  Proof.
    assert (heapGpreS CTΣ EM) as HPreG.
    { apply subG_heapPreG. (* why it's not applied automatically now? *)
      apply _. }

    forward eapply @obls_match_impl with
      (cps_degs := bound *: {[+ () +]})
      (eb := 0); eauto.
    1-5: by apply _.
    2: { intros (mtr & MATCH & OM_WF & FIRST).
         (* TODO: extract lemma *)
         enough (trace_len_le mtr (bound + 1)).
         { destruct H as (len & LEN & LE). eexists. split; eauto.
           destruct (trace_has_len extr) as [len' LEN'].
           eapply traces_match_same_length in MATCH as <-; eauto. }
         replace bound with (fuel_left (trfirst mtr)).
         { apply always_terminates_within_bound.
           - eapply traces_match_valid2; eauto.
           - eauto. } 
         subst bound. rewrite /fuel_left.
         rewrite FIRST. simpl.
         rewrite mset_map_size. rewrite gmultiset_size_scalar_mul.
         rewrite gmultiset_size_singleton. lia. }           

    iIntros (?) "[HEAP INIT]".

    pose proof @const_term_spec as SPEC.
    specialize SPEC with (OHE := OHE HEAP). 

    iApply (SPEC with "[-]").
    { simpl. iIntros (? _) "X". iApply "X". }
    2: { simpl. iNext. iIntros (_) "X". iApply "X". }
   
    clear SPEC.
    rewrite START. by iApply closed_pre_helper.
  Qed.

End ConstTermAdequacy.
