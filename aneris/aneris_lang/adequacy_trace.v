From aneris.aneris_lang Require Import aneris_lang proofmode adequacy_no_model.

Definition heap_invariance `{anerisPreG Σ unit_model} (N : namespace) (I : list val → Prop) ip e σ :
  I (state_trace σ) →
  (∀ `(anerisG Σ), ⊢ trace_inv N I -∗ trace_is (state_trace σ) -∗ WP e @[ip] ⊤ {{ _, True }}) →
  ∀ σ' t,
    step ([(mkExpr ip e)], σ) (t, σ') →
    I (state_trace σ').
Proof.
  (* intros HI Hwp σ' t.
  eapply (wp_invariance Σ _ s _ _ _ _ (I (trace σ'))). iIntros (Hinv κs) "".
  iMod (gen_heap_init σ.(heap)) as (?) "Hh".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (trace_auth_init σ.(trace)) as (?) "(Hta & Ht & Hth)".
  iDestruct (inv_alloc N _ (∃ t, trace_half_frag t ∗ ⌜I t⌝) with "[Hth]") as ">#HI".
  { iNext. eauto. }
  iModIntro. iExists
    (λ σ κs _, (gen_heap_ctx σ.(heap) ∗ trace_auth σ.(trace) ∗ proph_map_ctx κs σ.(used_proph_id))%I),
    (λ _, True%I).
  iFrame. iSplitL.
  { iDestruct (Hwp (HeapG _ _ _ _ _)) as "Hwp". iApply ("Hwp" with "HI Ht"). }
  iIntros "(_ & Hta & _)". iExists _.
  iInv "HI" as ">Ht'" "_". iDestruct "Ht'" as (t') "(Ht' & %)".
  iDestruct (trace_auth_half_frag_agree with "Hta Ht'") as %->. iModIntro. eauto.
Qed. *)
Admitted.

Lemma module_invariance {Σ} `{anerisPreG Σ unit_model} (N: namespace) ip
  (Φ: ∀ `{anerisG Σ}, iProp Σ → val → iProp Σ)  (* Module specification *)
  (P0: iProp Σ) (* Initial resources required by the module *)
  (e: val → expr) (* Context program, parameterized by the module *)
  (e_init: expr) (* Initialization code, used to allocate resources for P0 *)
  (imimpl: val) (* Implementation of the module (instrumented) *)
  (good_trace: list val → Prop) (* Trace property *)
  (σ: state): (* Initial state *)
  (* The initial trace must satisfy the property *)
  good_trace (state_trace σ) →
  (* The context must be safe, given a module satisfying the specification Φ *)
  (⊢ ∀ `(anerisG Σ) P m, Φ P m -∗ {{{ P }}} e m @[ip] {{{ v, RET v; True }}}) →
  (* The initialization code must provide P0 *)
  (⊢ ∀ `(anerisG Σ), {{{ True }}} e_init @[ip] {{{ v, RET v; P0 }}}) →
  (* The implementation provided for the module (iops) must satisfy the specification Φ.
     On top of P0 it is given SL resources for the trace. *)
  (⊢ ∀ `(anerisG Σ), Φ (P0 ∗ trace_is (state_trace σ) ∗ trace_inv N good_trace)%I imimpl) →
  (* Then the trace remains good at every step *)
  ∀ σ' e',
    step ([(mkExpr ip (e_init ;; e imimpl))], σ) (e', σ') →
    good_trace (state_trace σ').
Proof.
  intros Htrσ Hctx Hinit Himpl σ' e' Hsteps.
  eapply heap_invariance. done.
  2: eapply Hsteps.
  iIntros (?) "HI Htr". wp_bind e_init.
  iApply Hinit; first done.
  iNext.
  iIntros (v) "H0". wp_pures.
  iApply (Hctx with "[] [H0 Htr HI]").
  - iApply Himpl.
  - iFrame.
  - eauto.
Qed.