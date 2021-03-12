From iris.algebra Require Import auth agree excl csum.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Definition frac_oneshotR := csumR fracR (agreeR unitO).
Definition pending_tok q : frac_oneshotR := Cinl q.
Definition shot_tok : frac_oneshotR := Cinr (to_agree ()).

Class frac_oneshotG Σ := {
  frac_oneshotG_inG :> inG Σ frac_oneshotR;
  frac_oneshotG_name : gname
}.
Class frac_oneshotGPreG Σ := {
  frac_oneshotG_inPreG :> inG Σ frac_oneshotR
}.

Definition frac_oneshotGΣ : gFunctors :=
    #[GFunctor (csumR fracR (agreeR unitO))].

Global Instance subG_frac_oneshotG {Σ} :
  subG frac_oneshotGΣ Σ → frac_oneshotGPreG Σ.
Proof. solve_inG. Qed.

Definition pending_def `{frac_oneshotG Σ} q := own frac_oneshotG_name (pending_tok q).
Definition pending_aux `{frac_oneshotG Σ} : seal pending_def. by eexists. Qed.
Definition pending `{frac_oneshotG Σ} := pending_aux.(unseal).
Global Arguments pending {_ _} _%Qp.
Definition shot_def `{frac_oneshotG Σ} := own frac_oneshotG_name shot_tok.
Definition shot_aux `{frac_oneshotG Σ} : seal shot_def. by eexists. Qed.
Definition shot `{frac_oneshotG Σ} := shot_aux.(unseal).

Lemma pending_alloc `{!frac_oneshotGPreG Σ} :
  ⊢ |==> ∃ _ : frac_oneshotG Σ, pending 1.
Proof.
  iIntros.
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iExists {| frac_oneshotG_name := γ |}.
  rewrite /pending pending_aux.(seal_eq). by iFrame.
Qed.

Section frac_oneshot_lemmas.
  Context `{!frac_oneshotG Σ}.

  Global Instance shot_timeless : Timeless shot.
  Proof. rewrite /shot shot_aux.(seal_eq). apply _. Qed.

  Global Instance shot_persistent : Persistent shot.
  Proof. rewrite /shot shot_aux.(seal_eq). apply _. Qed.

  Global Instance pending_timeless q : Timeless (pending q).
  Proof. rewrite /pending pending_aux.(seal_eq). apply _. Qed.

  Lemma pending_split q p1 p2 :
    q = (p1 + p2)%Qp →
    pending q ⊢ pending (p1) ∗ pending (p2).
  Proof.
    intros Heq.
    by rewrite /pending pending_aux.(seal_eq) -own_op -Cinl_op frac_op Heq.
  Qed.

  Lemma pending_join p1 p2 :
    pending p1 ∗ pending p2 ⊢ pending (p1 + p2).
  Proof.
    by rewrite /pending pending_aux.(seal_eq)
       -own_op -Cinl_op frac_op.
  Qed.

  Lemma pending_shot q : pending q -∗ shot -∗ False.
  Proof.
    rewrite /shot shot_aux.(seal_eq).
    rewrite /pending pending_aux.(seal_eq).
    iIntros "H H'".
    { by iDestruct (own_valid_2 with "H H'") as %?. }
  Qed.

  Lemma pending_upd_shot : pending 1 ==∗ shot.
  Proof.
    rewrite /shot shot_aux.(seal_eq).
    rewrite /pending pending_aux.(seal_eq).
    iIntros "H". iMod (own_update with "H") as "$".
    { by apply cmra_update_exclusive. }
    done.
  Qed.
  
End frac_oneshot_lemmas.
