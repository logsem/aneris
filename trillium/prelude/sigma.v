From Coq.Unicode Require Import Utf8.
From stdpp Require Import base list.
From trillium.prelude Require Import classical.
From Coq.ssr Require Import ssreflect.

Lemma sig_eq {A} (P : A → Prop) (x y : sig P) :
  proj1_sig x = proj1_sig y → x = y.
Proof.
  destruct x as [x Px]; simpl.
  destruct y as [y Py]; simpl.
  intros ->.
  rewrite (ProofIrrelevance _ Px Py); trivial.
Qed.

Definition sig_prod_and {A B P Q} (a : {x : A | P x}) (b : {x : B | Q x}) :
    {x : A * B | P (fst x) ∧ Q (snd x)} :=
  (proj1_sig a, proj1_sig b) ↾ (conj (proj2_sig a) (proj2_sig b)).

Definition sig_prod_or_l {A P Q} (a : {x : A | P x}) :
  {x : A | P x ∨ Q x} := (proj1_sig a) ↾ (or_introl (proj2_sig a)).

Definition sig_prod_or_r {A P Q} (a : {x : A | Q x}) :
    {x : A | P x ∨ Q x} := (proj1_sig a) ↾ (or_intror (proj2_sig a)).

Definition sig_and {A} {P Q : A -> Prop} (a : {x : A | P x}) (HQ: Q (proj1_sig a)) :
    { x : A | P x ∧ Q x } := (proj1_sig a) ↾ (conj (proj2_sig a) (HQ)).

Fixpoint sig_and_list {A} (P Q : A → Prop) `{!∀ x, Decision (Q x)}
             (enum : list { x | P x }) : list { x | P x ∧ Q x } :=
    match enum with
    | [] => []
    | x :: xs => match (decide (Q $ proj1_sig x)) with
                 | left HQ => (sig_and x HQ) :: sig_and_list P Q xs
                 | _ => sig_and_list P Q xs
                 end
    end.

Lemma sig_and_list_le {A} (P Q : A → Prop)
      `{!EqDecision A} `{!∀ x, Decision (Q x)}
      `{!∀ x, ProofIrrel (P x)} `{!∀ x, ProofIrrel (Q x)}
      (enum : list { x | P x }) :
  ∀ x HQ, sig_and x HQ ∈ (sig_and_list P Q enum) → x ∈ enum.
Proof.
  intros x y Hin.
  induction enum; [by apply elem_of_nil in Hin|].
  apply elem_of_cons.
  destruct (decide (x = a)) as [Heq|Hneq]; simplify_eq /=; [left;done|right].
  destruct (decide (Q (`a))); [|by apply IHenum].
  apply elem_of_cons in Hin as [Hin|Hin]; [|by apply IHenum].
  inversion Hin as [Heq]. by apply proj1_sig_inj in Heq.
Qed.
