Require Import Arith ZArith ZifyClasses ZifyInst Lia.
From stdpp Require Import base numbers.
From iris.algebra Require Import updates csum excl agree big_op.
Set Default Proof Using "Type".

(** * Indexed Oneshot RA *)
(* This resource algebra corresponds intuitively to an indexed oneshot algebra
   with elements [pending b] and [shot b v] governed by the usual rules where
   [b] is the index. This generalization allows us to allocate [pending b] for
   all [b : nat] at once and split these in various ways, allowing a party to
   own all [pending b] such that some fact holds for [b], e.g. [even b]. *)
Definition ballot_oneshotUR (A : ofe) :=
  discrete_funUR (λ (b : nat), optionUR (csumR (exclR (unitR)) (agreeR A))).

(* For the [lia] tactic to support [Z.div], [Z.modulo], [Z.quot], and [Z.rem] *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.
(* For the [lia] tactic to support [Nat.modulo] and [Nat.div]. *)
#[global] Program Instance Op_Nat_mod : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp Op_Nat_mod.
#[global] Program Instance Op_Nat_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_Nat_div.

Section arith_lemmas.

  Lemma mod_exists b N i :
    N ≠ 0 →
    b `mod` N = i ↔ b = (b / N) * N + i.
  Proof. auto with lia. Qed.

  Lemma plus_lt_reg_r n m p : n + p < m + p -> n < m.
  Proof. rewrite 2!(Nat.add_comm _ p). apply Nat.add_lt_mono_l.
  Qed.

  Lemma mod_lowerbound_incr b b' i N :
    N ≠ 0 →
    b' `mod` N = i →
    b * N + i < b' →
    (b + 1) * N + i ≤ b'.
  Proof.
    move=> Hneq.
    rewrite mod_exists // => ->.
    have: 0 < N by lia.
    move=> Hlt /plus_lt_reg_r /(Nat.mul_lt_mono_pos_r N b _ Hlt) ?.
    apply Nat.add_le_mono_r, Nat.mul_le_mono_r.
    lia.
  Qed.

End arith_lemmas.

Section ra.
  Context {A : ofe}.

  (* a [pending] element for all naturals *)
  Definition pending_all : ballot_oneshotUR A :=
    λ b, Some (Cinl (Excl ())).

  (* an element for every [b] in the equivalence class [i mod N] with the
     [lb] least elements removed *)
  Definition pending_class (i : nat) (N : nat) (lb : nat) : ballot_oneshotUR A :=
    λ b, if (b `mod` N =? i) && (lb * N + i <=? b) then Some (Cinl (Excl ())) else None.

  (* a single [pending] element for ballot [c] *)
  Definition pending_ballot (c : nat)  : ballot_oneshotUR A :=
    λ b, if b =? c then Some (Cinl (Excl ())) else None.

  (* the [shot] element for ballot [c] and value [a] *)
  Definition shot_ballot (c : nat) (a : A) : ballot_oneshotUR A :=
    λ b, if b =? c then Some (Cinr (to_agree a)) else None.

  Hint Rewrite leb_correct_conv using lia : natb.
  Hint Rewrite leb_correct using lia : natb.
  Hint Rewrite leb_complete using lia : natb.

  Global Instance shot_core_id b v : CoreId (shot_ballot b v).
  Proof.
    rewrite /CoreId /= /shot_ballot.
    rewrite /pcore /cmra_pcore /= /ucmra_pcore /=.
    rewrite /discrete_fun_pcore_instance.
    f_equiv. intros ?. by destruct (x =? b).
  Qed.

  Local Lemma filter_class (b N : nat) :
    N ≠ 0 →
    filter (λ y : nat, b `mod` N = y ∧ y ≤ b) (set_seq 0 N) =
    {[b `mod` N]} :> gset nat.
  Proof.
    intros HN.
    apply set_eq_subseteq; split.
    - intros x.
      rewrite elem_of_filter elem_of_set_seq elem_of_singleton /=;
              intros [[? ?] ?]; lia.
    - intros x; rewrite elem_of_filter elem_of_set_seq elem_of_singleton /=.
      intros ->; split_and!; [done| |lia|lia].
      apply Nat.Div0.mod_le; done.
  Qed.

  Lemma big_opS_apply (g : gset nat) (f : nat → ballot_oneshotUR A) (b : nat) :
    ([^op set] x ∈ g, f x) b ≡ [^op set] x ∈ g, f x b.
  Proof.
    induction g as [|z g' Hz IHg'] using set_ind_L.
    - rewrite !big_opS_empty; done.
    - assert (∀ g1 g2 : ballot_oneshotUR A, ∀ x, g1 ≡ g2 → g1 x ≡ g2 x) as Hconv.
      { intros ??? Hequiv; apply Hequiv. }
      transitivity ((f z ⋅ [^op set] x ∈ g', f x) b).
      { apply Hconv.
        rewrite big_opS_union; last set_solver.
        rewrite big_opS_singleton; done. }
      rewrite big_opS_union; last set_solver.
      rewrite big_opS_singleton.
      rewrite discrete_fun_lookup_op.
      f_equiv; done.
  Qed.

  Lemma pending_all_split_classes N :
    N ≠ 0 →
    pending_all ≡ [^op set] x ∈ set_seq 0 N, pending_class x N 0.
  Proof.
    intros HNnz.
    intros b.
    rewrite big_opS_apply.
    rewrite /pending_all.
    rewrite (big_opS_proper _ (λ x, if decide ((b `mod` N = x) ∧ (x <= b)) then
                 Some (Cinl (Excl ())) else None)); last first.
    { intros x Hx.
      rewrite /pending_class.
      destruct decide as [[? ?]|].
      - erewrite (proj2 (Nat.eqb_eq _ _)); last done.
        erewrite (proj2 (Nat.leb_le _ _)); done.
      - destruct (decide (b `mod` N = x)); destruct (decide (x ≤ b)).
        + lia.
        + erewrite (proj2 (Nat.eqb_eq _ _)); last done.
          erewrite (proj2 (Nat.leb_nle _ _)); done.
        + erewrite (proj2 (Nat.eqb_neq _ _)); last done.
          erewrite (proj2 (Nat.leb_le _ _)); done.
        + erewrite (proj2 (Nat.eqb_neq _ _)); last done.
          erewrite (proj2 (Nat.leb_nle _ _)); done. }
    rewrite -big_opS_filter' filter_class; last done.
    rewrite big_opS_singleton; done.
  Qed.

  Lemma pending_set_split i N b :
    N ≠ 0 →
    i < N →
    pending_class i N b ≡ pending_class i N (b + 1) ⋅ pending_ballot (b * N + i).
  Proof.
    rewrite /pending_class /pending_ballot.
    intros Hneq Hlt b'.
    rewrite discrete_fun_lookup_op.
    destruct ((b' `mod` N =? i) && (b * N + i <=? b')) eqn:Heq.
    - apply andb_true_iff in Heq.
      destruct Heq as [Hmod%Nat.eqb_eq ?%leb_complete]; simpl.
      rewrite Hmod Nat.eqb_refl /=.
      destruct (b' =? b * N + i) eqn:Heq.
      { apply Nat.eqb_eq in Heq. by autorewrite with natb. }
      apply Nat.eqb_neq in Heq.
      assert ((b + 1) * N + i <=? b' = true) as ->; [|done].
      apply leb_correct.
      assert (b * N + i < b') by lia.
      by apply mod_lowerbound_incr.
    - apply andb_false_iff in Heq.
      destruct Heq as [Heq | Heq]; simpl.
      + rewrite Heq /=.
        apply Nat.eqb_neq in Heq.
        assert (b' =? b * N + i = false) as ->; [|done].
        apply Nat.eqb_neq. intros ->.
        rewrite -{2}(Nat.mod_small _ _ Hlt) Nat.add_comm
                    Nat.Div0.mod_add // in Heq.
     + apply leb_iff_conv in Heq.
       assert ((b + 1) * N + i <=? b' = false) as ->.
       { by autorewrite with natb. }
       rewrite andb_false_r.
       assert (b' =? b * N + i = false) as ->; [|done].
       apply Nat.eqb_neq. lia.
  Qed.

  Lemma ballot_update b v :
    pending_ballot b ~~> shot_ballot b v.
  Proof.
    rewrite /pending_ballot /shot_ballot.
    move=> n [c|] + b' /=; [|by destruct (b' =? b)].
    move=> /(_ b') /=.
    rewrite !discrete_fun_lookup_op.
    destruct (b' =? b); [|done].
    destruct c as [c0|]; [|done].
    rewrite -!Some_op !Some_validN.
    have: (✓ Cinr (to_agree v))=> H; [done|].
    apply (cmra_update_exclusive _ (H _) _ (Some c0)).
  Qed.

  Lemma pending_shot_not_valid b v :
    ✓ (pending_ballot b ⋅ shot_ballot b v) → False.
  Proof.
    rewrite /pending_ballot /shot_ballot=> /(_ b).
    rewrite discrete_fun_lookup_op Nat.eqb_refl //.
  Qed.

  Lemma shot_shot_valid b v1 v2:
    ✓ (shot_ballot b v1 ⋅ shot_ballot b v2) ↔ v1 ≡ v2.
  Proof.
    rewrite /shot_ballot. split.
    - move=> /(_ b).
      rewrite discrete_fun_lookup_op Nat.eqb_refl.
      rewrite -Some_op -Cinr_op Some_valid Cinr_valid.
      move=> /agree_op_inv /(inj to_agree _ _) //.
    - move=> Heq b'.
      rewrite discrete_fun_lookup_op.
      destruct (b' =? b); [|done].
      rewrite -Some_op -Cinr_op Some_valid Cinr_valid.
      by apply to_agree_op_valid.
  Qed.

End ra.
