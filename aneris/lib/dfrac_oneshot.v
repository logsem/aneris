From iris.bi.lib Require Import fractional.
From iris.algebra Require Import dfrac agree csum.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Export own.
From iris.prelude Require Import options.
Set Default Proof Using "Type".

Definition dfrac_oneshotR (A : ofe) := csumR dfracR (agreeR A).

Definition dfrac_oneshotΣ A : gFunctors :=
    #[GFunctor (dfrac_oneshotR A)].

Global Instance subG_dfrac_oneshotG {Σ} (A : ofe) :
  subG (dfrac_oneshotΣ A) Σ → inG Σ (dfrac_oneshotR A).
Proof. solve_inG. Qed.

Section def.
  Context `{!inG Σ (dfrac_oneshotR A)}.

  Definition pending_def (γ : gname) (q : Qp) :=
    own γ (Cinl (DfracOwn q)).
  Definition pending_aux : seal (pending_def). Proof. by eexists. Qed.
  Definition pending := pending_aux.(unseal).
  Definition pending_eq : pending = pending_def := pending_aux.(seal_eq).

  Definition pending_discarded_def (γ : gname) :=
    own γ (Cinl DfracDiscarded).
  Definition pending_discarded_aux
    : seal pending_discarded_def. Proof. by eexists. Qed.
  Definition pending_discarded := pending_discarded_aux.(unseal).
  Definition pending_discarded_eq : pending_discarded = pending_discarded_def :=
    pending_discarded_aux.(seal_eq).

  Definition shot_def γ a := own γ (Cinr (to_agree a)).
  Definition shot_aux : seal shot_def. Proof. by eexists. Qed.
  Definition shot := shot_aux.(unseal).
  Definition shot_eq : shot = shot_def := shot_aux.(seal_eq).
End def.

Global Arguments pending  {_ _ _} _ _%Qp.

Lemma pending_alloc `{!inG Σ (dfrac_oneshotR A)} :
  ⊢ |==> ∃ (γ : gname), pending γ 1.
Proof.
  iIntros.
  iMod (own_alloc (Cinl (DfracOwn 1%Qp))) as (γ) "H".
  { rewrite //=. }
  iExists _.
  rewrite pending_eq /pending_def. by iFrame.
Qed.

Section dfrac_oneshot_lemmas.
  Context `{!inG Σ (dfrac_oneshotR A)}.

  Global Instance pending_timeless γ q : Timeless (pending γ q).
  Proof. rewrite pending_eq /pending_def. apply _. Qed.

  Global Instance pending_fractional γ : Fractional (λ q, pending γ q).
  Proof.
    intros ??.
    rewrite pending_eq /pending_def -own_op -Cinl_op dfrac_op_own; auto.
  Qed.

  Global Instance pending_as_fractional γ q :
    AsFractional (pending γ q) (λ q, pending γ q)%I q.
  Proof. split; [done|]. apply _. Qed.

  Global Instance pending_discared_timeless γ : Timeless (pending_discarded γ).
  Proof.
    rewrite /pending_discarded pending_discarded_aux.(seal_eq). apply _.
  Qed.

  Global Instance pending_discared_persistent γ :
    Persistent (pending_discarded γ).
  Proof.
    rewrite /pending_discarded pending_discarded_aux.(seal_eq). apply _.
  Qed.

  Global Instance shot_timeless `{OfeDiscrete A} γ a :
    Timeless (shot γ a).
  Proof. rewrite shot_eq /shot_def. apply _. Qed.

  Global Instance shot_persistent γ a : Persistent (shot γ a).
  Proof. rewrite shot_eq /shot_def. apply _. Qed.

  Definition nat_to_Qp n := pos_to_Qp (Pos.of_nat n).

  Lemma big_sepS_pending_combine `{Countable B} (X : gset B) γ q :
    ([∗ set] _ ∈ X, pending γ q) ⊣⊢
    if decide (size X = 0) then True else pending γ ((nat_to_Qp (size X)) * q).
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

  (* TODO: upstream? *)
  Lemma size_set_seq start len :
    size (set_seq start len : gset _) = len.
  Proof.
    revert start. induction len; [done|]. intros start.
    rewrite set_seq_S_start.
    rewrite size_union ?size_singleton; [|set_solver by lia].
    rewrite IHlen //.
  Qed.

  Lemma pending_split_N γ (N : nat) :
    N > 0 →
    pending γ 1 ⊣⊢ [∗ set] _ ∈ set_seq 0 N, pending γ (/ nat_to_Qp N).
  Proof.
    intros ?.
    rewrite big_sepS_pending_combine.
    rewrite size_set_seq.
    destruct decide; [lia|].
    rewrite Qp_mul_inv_r //.
  Qed.

  Lemma pending_split_gset `{Countable B} (X : gset B) γ :
    X ≠ ∅ →
    pending γ 1 ⊣⊢ [∗ set] _ ∈ X, pending γ (/ nat_to_Qp (size X)).
  Proof.
    intros Hnempty.
    rewrite big_sepS_pending_combine.
    destruct (decide (size X = 0)) as [?%size_empty_inv|].
    { simplify_eq. }
    rewrite Qp_mul_inv_r //.
  Qed.

  Lemma pending_discard γ q :
    pending γ q ==∗ pending_discarded γ.
  Proof.
    rewrite pending_eq /pending_def
            pending_discarded_eq /pending_discarded_def.
    apply own_update, csum_update_l, dfrac_discard_update.
  Qed.

  Lemma pending_discarded_shot `{OfeDiscrete A} a γ :
     pending_discarded γ -∗ shot γ a -∗ False.
  Proof.
    rewrite pending_discarded_eq /pending_discarded_def shot_eq /shot_def.
    iIntros "H H'".
    by iDestruct (own_valid_2 with "H H'") as %?.
  Qed.

  Lemma pending_shot `{OfeDiscrete A} γ a q :
    pending γ q -∗ shot γ a -∗ False.
  Proof.
    rewrite pending_eq /pending_def shot_eq /shot_def.
    iIntros "H H'".
    by iDestruct (own_valid_2 with "H H'") as %?.
  Qed.

  Lemma pending_update_shot γ a : pending γ 1 ==∗ shot γ a.
  Proof.
    rewrite pending_eq /pending_def shot_eq /shot_def.
    iIntros "H". iMod (own_update with "H") as "$".
    { by apply cmra_update_exclusive. }
    done.
  Qed.

  Lemma shot_agreeL `{!LeibnizEquiv A, !OfeDiscrete A} γ a b :
    shot γ a -∗ shot γ b -∗ ⌜a = b⌝.
  Proof.
    rewrite shot_eq /shot_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite -Cinr_op csum_validI. iDestruct "H" as %?.
    iIntros "!%". by apply (to_agree_op_inv_L (A := A)).
  Qed.

End dfrac_oneshot_lemmas.
