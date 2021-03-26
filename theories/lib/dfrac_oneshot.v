From iris.algebra Require Import dfrac agree csum.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.

Definition dfrac_oneshotR (A : ofe) := csumR dfracR (agreeR A).

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

Section def.
  Context `{dfrac_oneshotG Σ A}.

  Definition pending_def (q : Qp) :=
    own dfrac_oneshotG_name (Cinl (DfracOwn q)).
  Definition pending_aux : seal (pending_def). by eexists. Qed.
  Definition pending := pending_aux.(unseal).
  Definition pending_eq : pending = pending_def := pending_aux.(seal_eq).

  Definition pending_discarded_def :=
    own dfrac_oneshotG_name (Cinl DfracDiscarded).
  Definition pending_discarded_aux
    : seal pending_discarded_def. by eexists. Qed.
  Definition pending_discarded := pending_discarded_aux.(unseal).
  Definition pending_discarded_eq : pending_discarded = pending_discarded_def :=
    pending_discarded_aux.(seal_eq).

  Definition shot_def a := own dfrac_oneshotG_name (Cinr (to_agree a)).
  Definition shot_aux : seal shot_def. by eexists. Qed.
  Definition shot := shot_aux.(unseal).
  Definition shot_eq : shot = shot_def := shot_aux.(seal_eq).
End def.

Global Arguments pending  {_ _ _} _%Qp.

Lemma pending_alloc `{!dfrac_oneshotGPreG Σ A} :
  ⊢ |==> ∃ _ : dfrac_oneshotG Σ A, pending 1.
Proof.
  iIntros.
  iMod (own_alloc (Cinl (DfracOwn 1%Qp))) as (γ) "H".
  { rewrite //=. }
  iExists {| dfrac_oneshotG_name := γ |}.
  rewrite pending_eq /pending_def. by iFrame.
Qed.

Section dfrac_oneshot_lemmas.
  Context `{!dfrac_oneshotG Σ A}.

  Global Instance pending_timeless q : Timeless (pending q).
  Proof. rewrite pending_eq /pending_def. apply _. Qed.

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
  Proof. rewrite shot_eq /shot_def. apply _. Qed.

  Global Instance shot_persistent a : Persistent (shot a).
  Proof. rewrite shot_eq /shot_def. apply _. Qed.

  Lemma pending_split p1 p2 :
    pending (p1 + p2) ⊣⊢ pending p1 ∗ pending p2.
  Proof.
    rewrite pending_eq /pending_def -own_op -Cinl_op dfrac_op_own; auto.
  Qed.

  Definition nat_to_Qp n := pos_to_Qp (Pos.of_nat n).

  Lemma big_sepS_pending_combine `{Countable B} (X : gset B) q :
    ([∗ set] _ ∈ X, pending q) ⊣⊢
    if decide (size X = 0) then True else pending ((nat_to_Qp (size X)) * q).
  Proof.
    rewrite pending_eq /pending_def.
    induction X using set_ind_L.
    - rewrite big_sepS_empty size_empty //.
    - rewrite big_sepS_union ?big_sepS_singleton /=; [|set_solver].
      rewrite size_union ?size_singleton /=; [|set_solver].
      rewrite IHX.
      destruct (decide (size X = 0)) as [->|].
      { rewrite /nat_to_Qp /Pos.of_nat /=  Qp_mul_1_l bi.sep_emp //. }
      rewrite -own_op -Cinl_op dfrac_op_own.
      rewrite /nat_to_Qp -Pos.of_nat_succ -Pos.succ_of_nat //.
      rewrite Pplus_one_succ_l -pos_to_Qp_add Qp_mul_add_distr_r Qp_mul_1_l //.
  Qed.

  Lemma pending_split_gset `{Countable B} (X : gset B) :
    X ≠ ∅ →
    pending 1 ⊣⊢ [∗ set] _ ∈ X, pending (/ nat_to_Qp (size X)).
  Proof.
    intros Hnempty.
    rewrite big_sepS_pending_combine.
    destruct (decide (size X = 0)) as [?%size_empty_inv|].
    { simplify_eq. }
    rewrite Qp_mul_inv_r //.
  Qed.

  Lemma pending_discard q :
    pending q ==∗ pending_discarded.
  Proof.
    rewrite pending_eq /pending_def
            pending_discarded_eq /pending_discarded_def.
    apply own_update, csum_update_l, dfrac_discard_update.
  Qed.

  Lemma pending_discarded_shot `{OfeDiscrete A} a :
     pending_discarded -∗ shot a -∗ False.
  Proof.
    rewrite pending_discarded_eq /pending_discarded_def shot_eq /shot_def.
    iIntros "H H'".
    by iDestruct (own_valid_2 with "H H'") as %?.
  Qed.

  Lemma pending_shot `{OfeDiscrete A} a q : pending q -∗ shot a  -∗ False.
  Proof.
    rewrite pending_eq /pending_def shot_eq /shot_def.
    iIntros "H H'".
    by iDestruct (own_valid_2 with "H H'") as %?.
  Qed.

  Lemma pending_update_shot a : pending 1 ==∗ shot a.
  Proof.
    rewrite pending_eq /pending_def shot_eq /shot_def.
    iIntros "H". iMod (own_update with "H") as "$".
    { by apply cmra_update_exclusive. }
    done.
  Qed.

  Lemma shot_agreeL `{!LeibnizEquiv A, !OfeDiscrete A} a b :
    shot a -∗ shot b -∗ ⌜a = b⌝.
  Proof.
    rewrite shot_eq /shot_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite -Cinr_op csum_validI. iDestruct "H" as %?.
    iIntros "!%". by apply (to_agree_op_inv_L (A := A)).
  Qed.

End dfrac_oneshot_lemmas.
