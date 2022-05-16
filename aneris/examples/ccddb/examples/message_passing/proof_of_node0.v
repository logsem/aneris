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


Section ProofOfProgram0.
  Context `{!anerisG Mdl Σ,!mpG Σ}.
  Context `{!DB_time, !DB_events, !Maximals_Computing}.
  Context `{!DB_resources Mdl Σ}.

  Lemma z0_spec γ wr (h : gmem) s :
    h ⊆ erasure_set s →
    GlobalInv -∗
    write_spec wr 0 z0 -∗
    {{{ "x" ↦ᵤ h ∗ Seen 0 s ∗ inv Ny (inv_y γ) }}}
      z0_prog wr @[ip_of_address z0]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hhs) "#HIG #Hwr !#". iIntros (Φ) "(Hxu & #Hs & #HIy) HΦ".
    rewrite /z0_prog. wp_pures. wp_bind (wr _ _).
    (* write 37 to x *)
    iDestruct (write_spec_implies_simplified_write_spec with "Hwr") as "Hswr".
    wp_apply ("Hswr" $! _ (SerVal #37) with "[] [] [$Hxu $Hs]"); [done|done|].
    iDestruct 1 as (s2 ex) "(% & % & % & %Hkx & % & %Hmax_s2 & % & #Hs2 & Hxu) /=".
    iApply fupd_aneris_wp.
    (* allocate the invariant for [x] *)
    iMod (Maximum_ghst _ _ ex with "HIG Hs2 Hxu") as "[%Hmax_h' Hxu]";
      [done| |set_solver|done|].
    { apply union_singleton_erasure_set. set_solver. }
    iMod (inv_alloc Nx _ (inv_x γ (erasure ex)) with "[Hxu]") as "#HIx".
    { iModIntro. iLeft. rewrite erasure_val; eauto. }
    iModIntro. wp_seq.
    (* write 1 to y *)
    set (P := True%I).
    set (Q := (λ (e : ae) (h : gmem) (s : lhst), True : iProp Σ)%I).
    wp_apply ("Hwr" $! (⊤ ∖ ↑Ny) _ (SerVal #1) _ P Q
                with "[] [] [] [$Hs2]"); [done|solve_ndisj| |done|].
    { iIntros "!#" (s3 ey) "% % %Hky % Hxu". rewrite /P/Q.
      iInv Ny as (hy') "[>Hyu Hhy']" "Hclose".
      iIntros "!# % % % %Hmax #Hs3 Hys".
      iDestruct (User_Sys_agree with "Hyu Hys") as %<-.
      iMod (OwnMem_update _ _ (hy' ∪ {[erasure ey]})
              with "Hyu Hys") as "[Hyu Hys]"; first set_solver.
      iModIntro. iFrame.
      iMod (Maximum_lhst_gt ex ey  with "HIG Hs3") as %Hneq;
        [solve_ndisj|by eapply ae_key_neq |set_solver|done|].
      iMod ("Hclose" with "[-]") as "_"; last by iIntros "!#".
      iExists (_ ∪ _). iFrame.
      iIntros "!#" (e'). rewrite elem_of_union.
      iIntros ([[? | ->%elem_of_singleton] ?]); first by iApply "Hhy'".
      iExists _. eauto. }
    iIntros "_". by iApply "HΦ".
  Qed.

End ProofOfProgram0.

Section ProofOfNode0.
  Context `{!anerisG Mdl Σ, !mpG Σ}.
  Context `{!DB_time, !DB_events, !Maximals_Computing}.
  Context `{!DB_resources Mdl Σ}.
  Context `{!DB_init_function, !DB_init}.

  Theorem z0_node_spec A γ :
    z0 ∈ A →
    GlobalInv -∗
    init_spec init -∗
    {{{ init_resources z0 A 0 ∗ "x" ↦ᵤ ∅ ∗ inv Ny (inv_y γ) }}}
      z0_node dbs @[ip_of_address z0]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Hz0) "#HIG #init_spec".
    iIntros (Φ) "!> (Hinit & Hxu & #HIy) HΦ".
    rewrite /z0_node. wp_pures. wp_bind (init _ _)%E.
    wp_apply ("init_spec" $! _ 0 with "[] [] [] [$]"); [|done|done|].
    { iPureIntro. cbn; eauto. }
    iClear "init_spec".
    iIntros (rd wr) "(Hs & #Hrd & #Hwr) /=".
    do 8 wp_pure _.
    by iApply (z0_spec with "HIG Hwr [$Hxu $Hs $HIy]").
  Qed.

End ProofOfNode0.
