(** Realisation of global and local events. *)

From aneris.aneris_lang Require Import lang inject.
From aneris.aneris_lang.lib Require Import vector_clock_proof.
From aneris.prelude Require Export time.
From aneris.aneris_lang.lib Require Import list_proof.

Record global_event :=
  GlobalEvent {
    ge_payload : val;
    ge_time : vector_clock;
    ge_orig : nat
  }.

Instance: Inhabited global_event := populate (GlobalEvent #() inhabitant 0).

Global Instance ge_decidable : EqDecision global_event.
Proof. solve_decision. Qed.

Global Instance ge_countable : Countable global_event.
Proof.
  refine {| encode := λ a, encode (ge_payload a, ge_time a, ge_orig a);
            decode := λ n,
                      (λ x, {| ge_payload := x.1.1;
                               ge_time := x.1.2; ge_orig := x.2 |}) <$>
                        @decode
                        (val * vector_clock * nat)%type
                        _ _ n
         |}.
  by intros []; rewrite /= decode_encode /=.
Qed.


(* TODO: using vector_clock_to_val is a bit of a hack. Ideally, we'd just
   do $ (..., a.(ge_time), ...) and deprecate vector_clock_to_val.
   Unfortunately, vector_clock_to_val is used in many places at the moment,
   so we're keeping it for now. *)
Global Program Instance Inject_global_event : Inject global_event val :=
  {| inject a := $(a.(ge_payload), vector_clock_to_val a.(ge_time), a.(ge_orig))
  |}.
Next Obligation.
  intros w1 w2 Heq.
  inversion Heq as [[Hp Ht Ho]].
  assert (ge_time w1 = ge_time w2) as Ht'.
  { by apply (inj (R := eq)) in Ht; [ | apply _]. }
  destruct w1, w2; simpl in *.
  by apply Z_of_nat_inj in Ho; subst.
Qed.


Record local_event :=
  LocalEvent {
    le_payload : val;
    le_time : vector_clock;
    le_orig : nat;
    le_seqid : nat
  }.

Instance: Inhabited local_event := populate (LocalEvent #() inhabitant 0 0).

Global Instance le_decidable : EqDecision local_event.
Proof. solve_decision. Qed.

Global Instance le_countable : Countable local_event.
Proof.
  refine {| encode :=
              λ a, encode (le_payload a, le_time a, le_orig a, le_seqid a);
            decode :=
              λ n,
              (λ x, {| le_payload := x.1.1.1;
                       le_time := x.1.1.2; le_orig := x.1.2;
                       le_seqid := x.2|})
                <$>
                @decode
                (val * vector_clock * nat * nat)%type
                _ _ n
         |}.
  by intros []; rewrite /= decode_encode /=.
Qed.

Definition erase (le : local_event) : global_event :=
  match le with
    LocalEvent p t o _ => GlobalEvent p t o
  end.

Lemma erase_orig : ∀ (e : local_event), (erase e).(ge_orig) = e.(le_orig).
Proof. by destruct e. Qed.

Lemma erase_payload : ∀ (e : local_event), (erase e).(ge_payload) = e.(le_payload).
Proof. by destruct e. Qed.

Lemma erase_time : ∀ (e : local_event), ge_time (erase e) = le_time e.
Proof. by destruct e. Qed.

Definition is_gev (v : val) (e : global_event) :=
  ∃ p vc o,
    v = ((p, vc), o)%V ∧
    p = e.(ge_payload) ∧
    is_vc vc e.(ge_time) ∧
    o = #e.(ge_orig).

Definition is_lev (v : val) (a : local_event) := is_gev v (erase a).
