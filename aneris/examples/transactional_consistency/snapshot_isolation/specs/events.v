From aneris.aneris_lang Require Import lang inject.
From aneris.examples.transactional_consistency Require Import user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.specs
     Require Import time.

(** Write events *)

Section Events.
  Context `{!KVS_time}.

  (* Definition EV_id : Set := socket_address * nat. *)

 (** Write event *)
  Record write_event :=
    {
      we_key : Key;
      we_val : val;
      we_active : bool;
      we_time : Time;
    }.

End Events.

Notation "s '<ₜ' t" :=
  (TM_lt (we_time s) (we_time t)) (at level 70, no associativity).

Notation "s '≤ₜ' t" :=
  (TM_lt (we_time s) (we_time t) ∨ s = t) (at level 70, no associativity).
Notation "s '=ₜ' t" :=
  (we_time s = we_time t) (at level 70, no associativity).


Section Events_lemmas.
  Context `{!KVS_time}.

  Global Instance write_event_dec : EqDecision write_event.
  Proof. solve_decision. Qed.

  Global Instance write_event_countable : Countable write_event.
  Proof.
    refine {| encode := λ a, encode (we_key a, we_val a, we_active a, we_time a);
              decode := λ n,
                      (λ x, {| we_key := x.1.1.1; we_val := x.1.1.2;
                               we_active := x.1.2; we_time := x.2 |}) <$>
                        @decode
                        (Key * val * bool * Time)%type
                        _ _ n
           |}.
    by intros []; rewrite /= decode_encode /=.
  Qed.

End Events_lemmas.



Global Instance int_time : KVS_time :=
  {| Time := nat;
    TM_lt := Nat.lt;
    TM_lt_tricho := PeanoNat.Nat.lt_trichotomy |}.

Instance: Inhabited (@write_event int_time) := populate (Build_write_event "" #() true inhabitant).

Global Program Instance Inject_write_event : Inject write_event val :=
  {| inject a := $(a.(we_key), (a.(we_val), (a.(we_active), a.(we_time))))
  |}.
Next Obligation.
  intros w1 w2 Heq.
  inversion Heq as [[Hk Hv Ha Ht]].
  assert (we_time w1 = we_time w2) as Ht'.
  { by apply (inj (R := eq)) in Ht; [ | apply _]. }
  destruct w1, w2; simpl in *.
  by apply Nat2Z.inj in Ht; subst.
Qed.

Canonical Structure write_eventO := leibnizO write_event.
Definition whist := list write_eventO.

