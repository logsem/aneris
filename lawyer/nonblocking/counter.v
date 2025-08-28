From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_model.
From heap_lang Require Import lang.


Section Counter.

  Definition incr (l: loc): val :=
    λ: <>,
      FAA #l #(1:nat)
  .

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}.

  Notation "'Degree'" := (om_hl_Degree).
  Context (d: Degree).

  Existing Instance OHE.

  Context (l: loc).

  Definition counter_inv_ns := nroot .@ "cnt". 

  Definition counter_inv: iProp Σ :=
    inv counter_inv_ns (∃ (n: nat), l ↦ #n).

  Definition counter_is_init_st (c: cfg heap_lang) :=
    (heap c.2) !! l = Some #(0: nat).

  Lemma counter_init_inv (c: cfg heap_lang) (INIT: counter_is_init_st c):
    let _: heap1GS Σ := iem_phys _ EM in 
    hl_phys_init_resource c ={⊤}=∗ counter_inv. 
  Proof using.
    simpl. iIntros "INIT". rewrite /hl_phys_init_resource.
    red in INIT. rewrite -(map_union_empty (heap _)).
    erewrite <- union_delete_insert; eauto.
    iDestruct (big_sepM_union with "INIT") as "[_ L]".
    { apply map_disjoint_dom. set_solver. }
    rewrite insert_empty big_sepM_singleton.
    iMod (inv_alloc counter_inv_ns _ with "[-]") as "#INV".
    2: iModIntro; by iApply "INV".
    iNext. iExists _. iFrame.
  Qed.

  (* TODO: derive from LAT spec *)
  (* TODO: restrict the set of arguments *)
  Lemma counter_mock_spec τ π q (a: val):
    {{{ cp_mul π d 5 ∗ th_phase_frag τ π q ∗ counter_inv }}}
        incr l a @ τ
    {{{ (n: nat), RET #n; th_phase_frag τ π q }}}.
  Proof using.
    iIntros (Φ) "(CPS & PH & #INV) POST". rewrite /incr. 
    pure_steps.
    iApply wp_atomic.
    iInv "INV" as "(%n & >L)" "CLOS". iModIntro.
    iApply sswp_MU_wp; [done| ]. iApply (wp_faa with "[$]"). iIntros "!> L".
    MU_by_burn_cp.
    pure_steps.
    iMod ("CLOS" with "[L]") as "_".
    { iNext. replace (n + 1%nat) with (Z.of_nat (n + 1)); [| lia]. 
      iExists _. iFrame. }
    iModIntro. by iApply "POST".
  Qed. 

End Counter.


From lawyer.nonblocking Require Import om_wfree_inst.

Lemma counter_wfree_spec (l: loc):
  ∀ (M : Model) (EM : ExecutionModel heap_lang M) (Σ : gFunctors) 
    (OHE : OM_HL_Env OP_HL_WF EM Σ) (τ : locale heap_lang) 
    (π : Phase) (q : Qp) (a : val) (Φ : language.val heap_lang → iPropI Σ),
    cp_mul π d_wfr0 5 ∗ th_phase_frag τ π q ∗
    (λ (M0 : Model) (EM0 : ExecutionModel heap_lang M0) 
       (Σ0 : gFunctors) (OHE0 : OM_HL_Env OP_HL_WF EM0 Σ0), 
       counter_inv l)
      M EM Σ OHE -∗
    ▷ (∀ v : language.val heap_lang, th_phase_frag τ π q -∗ Φ v) -∗
    WP incr l a @τ {{ v, Φ v }}.
Proof using.
  intros. simpl.
  iIntros "(CPS & PH & #INV) POST".
  iApply (counter_mock_spec with "[-POST]").
  { by iFrame. }
  iIntros "!> % ?". by iApply "POST".
Qed.

Lemma counter_wfree_init_inv (l : loc):
  forall (M : Model) (EM : ExecutionModel heap_lang M) 
   (Σ : gFunctors) (OHE : OM_HL_Env OP_HL_WF EM Σ) (c : cfg heap_lang),
   counter_is_init_st l c ->
    let _: heap1GS Σ := iem_phys _ EM in 
     hl_phys_init_resource c ={⊤}=∗ counter_inv l (OHE := OHE).
Proof using.
  intros. by apply counter_init_inv.
Qed.


Definition counter_WF_spec (l: loc): WaitFreeSpec (incr l) := {|
  wfs_init_mod := counter_wfree_init_inv l;
  wfs_spec := counter_wfree_spec l;  
|}. 
