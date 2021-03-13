From iris.algebra Require Import dfrac agree csum.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Section def.
  Context (A : ofe).
  Definition dfrac_oneshotR := csumR dfracR (agreeR A).
  Definition pending_tok (q : Qp) : dfrac_oneshotR := Cinl (DfracOwn q).
  Definition pending_discarded_tok : dfrac_oneshotR := Cinl DfracDiscarded.
  Definition shot_tok (a : A) : dfrac_oneshotR := Cinr (to_agree a).
End def.

Class dfrac_oneshotG Σ A := {
  dfrac_oneshotG_inG :> inG Σ (dfrac_oneshotR A);
  dfrac_oneshotG_name : gname
}.
Class dfrac_oneshotGPreG Σ A := {
  dfrac_oneshotG_inPreG :> inG Σ (dfrac_oneshotR A)
}.

Definition dfrac_oneshotGΣ A : gFunctors :=
    #[GFunctor (csumR dfracR (agreeR A))].

Global Instance subG_dfrac_oneshotG {Σ} (A : ofe) :
  subG (dfrac_oneshotGΣ A) Σ → dfrac_oneshotGPreG Σ A.
Proof. solve_inG. Qed.

Definition pending_def `{dfrac_oneshotG Σ A} (q : Qp) :=
  own dfrac_oneshotG_name (pending_tok A q).
Definition pending_aux `{dfrac_oneshotG Σ A} : seal pending_def. by eexists. Qed.
Definition pending `{dfrac_oneshotG Σ A} := pending_aux.(unseal).
Global Arguments pending {_ _ _} _%Qp.
Definition pending_discarded_def `{dfrac_oneshotG Σ A} :=
  own dfrac_oneshotG_name (pending_discarded_tok A).
Definition pending_discarded_aux `{dfrac_oneshotG Σ A}
  : seal pending_discarded_def. by eexists. Qed.
Definition pending_discarded `{dfrac_oneshotG Σ A} := pending_discarded_aux.(unseal).
Definition shot_def `{dfrac_oneshotG Σ A} a := own dfrac_oneshotG_name (shot_tok A a).
Definition shot_aux `{dfrac_oneshotG Σ A} : seal shot_def. by eexists. Qed.
Definition shot `{dfrac_oneshotG Σ A} := shot_aux.(unseal).

Lemma pending_alloc `{!dfrac_oneshotGPreG Σ A} :
  ⊢ |==> ∃ _ : dfrac_oneshotG Σ A, pending 1.
Proof.
  iIntros.
  iMod (own_alloc (Cinl (DfracOwn 1%Qp))) as (γ) "H".
  { rewrite //=. }
  iExists {| dfrac_oneshotG_name := γ |}.
  rewrite /pending pending_aux.(seal_eq). by iFrame.
Qed.

Section dfrac_oneshot_lemmas.
  Context `{!dfrac_oneshotG Σ A}.

  Global Instance pending_timeless q : Timeless (pending q).
  Proof. rewrite /pending pending_aux.(seal_eq). apply _. Qed.

  Global Instance pending_discared_timeless : Timeless pending_discarded.
  Proof.
    rewrite /pending_discarded pending_discarded_aux.(seal_eq). apply _.
  Qed.

  Global Instance pending_discared_persistent : Persistent pending_discarded.
  Proof.
    rewrite /pending_discarded pending_discarded_aux.(seal_eq). apply _.
  Qed.

  Global Instance shot_timeless `{OfeDiscrete A} a :
    Timeless (shot a).
  Proof. rewrite /shot shot_aux.(seal_eq) /shot_def. apply _. Qed.

  Global Instance shot_persistent a : Persistent (shot a).
  Proof. rewrite /shot shot_aux.(seal_eq). apply _. Qed.


  Lemma pending_split q p1 p2 :
    q = (p1 + p2)%Qp →
    pending q ⊢ pending p1 ∗ pending p2.
  Proof.
    intros Heq.
    by rewrite /pending pending_aux.(seal_eq) -own_op -Cinl_op dfrac_op_own Heq.
  Qed.

  Lemma pending_join p1 p2 :
    pending p1 ∗ pending p2 ⊢ pending (p1 + p2).
  Proof.
    by rewrite /pending pending_aux.(seal_eq) -own_op -Cinl_op dfrac_op_own.
  Qed.

  Lemma pending_discard q :
    pending q ==∗ pending_discarded.
  Proof.
    rewrite /pending pending_aux.(seal_eq)
            /pending_discarded pending_discarded_aux.(seal_eq).
    apply own_update, csum_update_l, dfrac_discard_update.
  Qed.

  Lemma pending_discarded_shot `{OfeDiscrete A} a :
     pending_discarded -∗ shot a -∗ False.
  Proof.
    rewrite /pending_discarded pending_discarded_aux.(seal_eq).
    rewrite /shot shot_aux.(seal_eq).
    iIntros "H H'".
    by iDestruct (own_valid_2 with "H H'") as %?.
  Qed.

  Lemma pending_shot `{OfeDiscrete A} a q : pending q -∗ shot a  -∗ False.
  Proof.
    rewrite /shot shot_aux.(seal_eq).
    rewrite /pending pending_aux.(seal_eq).
    iIntros "H H'".
    by iDestruct (own_valid_2 with "H H'") as %?.
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

End dfrac_oneshot_lemmas.
