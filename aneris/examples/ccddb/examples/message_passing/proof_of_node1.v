From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     lang network tactics proofmode lifting adequacy.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb Require Import spec_util.
From aneris.examples.ccddb.examples Require Import lib.
From aneris.examples.ccddb.examples.message_passing Require Import prog.
From aneris.examples.ccddb.examples.message_passing Require Import
     proof_resources.


Section ProofOfProgram1.
  Context `{!anerisG Mdl Σ,!mpG Σ}.
  Context `{!DB_time, !DB_events, !Maximals_Computing}.
  Context `{!DB_resources Mdl Σ}.

  Lemma z1_spec γ s rd:
    GlobalInv -∗
    read_spec rd 1 z1 -∗
    {{{ Seen 1 s ∗ inv Ny (inv_y γ) ∗ token γ }}}
      z1_prog rd @[ip_of_address z1]
    {{{ (h : gmem) a, RET (InjRV #37);
          ⌜Maximum h = Some a⌝ ∗ ⌜WE_val a = #37⌝ ∗ "x" ↦ᵤ h }}}.
  Proof.
    iIntros "#HIG #Hrd !#" (Φ) "(#Hs & #HIy & Htok) HΦ".
    rewrite /z1_prog. wp_pures.
    wp_apply (repeat_read_until_spec with "[] Hs"); [done|done|].
    iIntros (s2 e) "(% & Hs2 & % & % & #Hsnap & %) /=".
    iApply fupd_aneris_wp.
    iInv Ny as "H" "Hcl".
    iDestruct "H" as (h) "[>Hy H]".
    iMod (OwnMemSnapshot_included with "HIG Hy Hsnap") as "[Hy %Hincl]";
      first solve_ndisj.
    iAssert (▷ ∃ a, ⌜a <ₜ e⌝ ∗ inv Nx (inv_x γ a))%I as "#He".
    { iNext.
      iDestruct ("H" $! (erasure e) with "[]") as (a) "Ha".
      { iPureIntro. split; first set_solver.
        rewrite erasure_val; done. }
      rewrite erasure_time; eauto. }
    assert (e ∈ s2).
    { by eapply elem_of_Maximals_restrict_key. }
    iMod ("Hcl" with "[Hy H]") as "_".
    { iNext; iExists _; iFrame. }
    iModIntro.
    wp_seq.
    iDestruct "He" as (a) "[% #HIx]".
    wp_apply fupd_aneris_wp.
    iInv Nx as ">[Hx | Htok']" "Hclose"; last first.
    { iDestruct (token_exclusive with "Htok Htok'") as "[]". }
    iDestruct "Hx" as (h') "(Hxu & % & %Hv37)".
    iMod ("Hclose" with "[Htok]") as "_"; first by iRight.
    iModIntro.
    wp_apply ("Hrd" with "[//] Hs2").
    iIntros (w) "Hw".
    iApply fupd_aneris_wp.
    iDestruct "Hw" as (s3 Hs3) "[#Hs3 [[-> %Hx]|Hw]]".
    - iMod (Maximum_causality e _ with "HIG Hs3 Hxu") as ([? [? ?]]) "Hxu";
        [solve_ndisj|set_solver|done|done|].
      set_solver.
    - iDestruct "Hw" as (v e') "(-> & <- & %He'1 & Hxe' & %He'2)".
      iMod (Maximum_elem_of_ghst with "HIG Hxu") as "[% Hxu]";
        [solve_ndisj|done|].
      iMod (Causality_2 e a with "HIG Hs3 Hxu") as ([e'' [? <-]]) "Hxu";
        [solve_ndisj|set_solver|done|done|].
      iMod (OwnMemSnapshot_included with "HIG Hxu Hxe'") as "[Hxu %Hincl']";
      first solve_ndisj.
      iMod (Maximum_maximals_val_agree with "HIG Hs3 Hxu") as "[%Heq Hxu]";
          [solve_ndisj|done|done|done|set_solver|].
      iModIntro.
      assert (AE_val e' = #37) as -> by by rewrite -Heq -erasure_val.
      wp_pures.
      wp_lam.
      wp_pures.
      iApply "HΦ"; eauto.
  Qed.

End ProofOfProgram1.

Section ProofOfNode1.
  Context `{!anerisG Mdl Σ, !mpG Σ}.
  Context `{!DB_time, !DB_events, !Maximals_Computing}.
  Context `{!DB_resources Mdl Σ}.
  Context `{!DB_init_function, !DB_init}.

  Theorem z1_node_spec γ :
    GlobalInv -∗
    init_spec init -∗
    {{{ init_resources z1 1 ∗ inv Ny (inv_y γ) ∗ token γ }}}
      z1_node dbs @[ip_of_address z1]
    {{{ RET (InjRV #37); True }}}.
  Proof.
    iIntros "#HIG #init_spec".
    iIntros (Φ) "!> (Hinit & #HIy & Htok) HΦ".
    rewrite /z1_prog. wp_pures. wp_bind (init _ _).
    wp_apply ("init_spec" $! 1 with "[] [] [$]"); [|done|].
    { iPureIntro. cbn; eauto. }
    iClear "init_spec".
    iIntros (rd wr) "(Hs & #Hrd & #Hwr) /=".
    do 8 wp_pure _.
    iApply (z1_spec with "HIG Hrd [$Htok $Hs $HIy]").
    iIntros "!#" (??) "_". by iApply "HΦ".
  Qed.

End ProofOfNode1.
