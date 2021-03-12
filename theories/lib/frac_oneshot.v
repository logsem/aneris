From iris.algebra Require Import auth agree excl csum.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Section def.
  Context (A : ofe).
  Definition frac_oneshotR := csumR fracR (agreeR A).
  Definition pending_tok q : frac_oneshotR := Cinl q.
  Definition shot_tok (a : A) : frac_oneshotR := Cinr (to_agree a).
End def.

Class frac_oneshotG Σ A := {
  frac_oneshotG_inG :> inG Σ (frac_oneshotR A);
  frac_oneshotG_name : gname
}.
Class frac_oneshotGPreG Σ A := {
  frac_oneshotG_inPreG :> inG Σ (frac_oneshotR A)
}.

Definition frac_oneshotGΣ A : gFunctors :=
    #[GFunctor (csumR fracR (agreeR A))].

Global Instance subG_frac_oneshotG {Σ} (A : ofe) :
  subG (frac_oneshotGΣ A) Σ → frac_oneshotGPreG Σ A.
Proof. solve_inG. Qed.

Definition pending_def `{frac_oneshotG Σ A} q :=
  own frac_oneshotG_name (pending_tok A q).
Definition pending_aux `{frac_oneshotG Σ A} : seal pending_def. by eexists. Qed.
Definition pending `{frac_oneshotG Σ A} := pending_aux.(unseal).
Global Arguments pending {_ _ _} _%Qp.
Definition shot_def `{frac_oneshotG Σ A} a := own frac_oneshotG_name (shot_tok A a).
Definition shot_aux `{frac_oneshotG Σ A} : seal shot_def. by eexists. Qed.
Definition shot `{frac_oneshotG Σ A} := shot_aux.(unseal).

Lemma pending_alloc `{!frac_oneshotGPreG Σ A} :
  ⊢ |==> ∃ _ : frac_oneshotG Σ A, pending 1.
Proof.
  iIntros.
  iMod (own_alloc (Cinl 1%Qp)) as (γ) "H".
  { rewrite //=. }
  iExists {| frac_oneshotG_name := γ |}.
  rewrite /pending pending_aux.(seal_eq). by iFrame.
Qed.

Section frac_oneshot_lemmas.
  Context `{!frac_oneshotG Σ A}.

  Global Instance shot_timeless `{OfeDiscrete A} a :
    Timeless (shot a).
  Proof. rewrite /shot shot_aux.(seal_eq) /shot_def. apply _. Qed.

  Global Instance shot_persistent a : Persistent (shot a).
  Proof. rewrite /shot shot_aux.(seal_eq). apply _. Qed.

  Global Instance pending_timeless q : Timeless (pending q).
  Proof. rewrite /pending pending_aux.(seal_eq). apply _. Qed.

  Lemma pending_split q p1 p2 :
    q = (p1 + p2)%Qp →
    pending q ⊢ pending p1 ∗ pending p2.
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

  Lemma pending_shot `{OfeDiscrete A} a q : pending q -∗ shot a  -∗ False.
  Proof.
    rewrite /shot shot_aux.(seal_eq).
    rewrite /pending pending_aux.(seal_eq).
    iIntros "H H'".
    { by iDestruct (own_valid_2 with "H H'") as %?. }
  Qed.

  Lemma pending_update_shot a : pending 1 ==∗ shot a.
  Proof.
    rewrite /shot shot_aux.(seal_eq).
    rewrite /pending pending_aux.(seal_eq).
    iIntros "H". iMod (own_update with "H") as "$".
    { by apply cmra_update_exclusive. }
    done.
  Qed.

  Lemma shot_agreeL `{!LeibnizEquiv A, !OfeDiscrete A} a b :
    shot a -∗ shot b -∗ ⌜a = b⌝.
  Proof.
    rewrite /shot shot_aux.(seal_eq).
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite -Cinr_op csum_validI. iDestruct "H" as %?.
    iIntros "!%". by apply (to_agree_op_inv_L (A := A)).
  Qed.

End frac_oneshot_lemmas.
