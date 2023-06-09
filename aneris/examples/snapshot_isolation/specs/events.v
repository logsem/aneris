From aneris.aneris_lang Require Import lang.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params  time.

(** Write and apply events *)

Section Write_event.
  Context `{!KVS_time}.

  Definition EV_id : Set := socket_address * nat.

 (** Write event *)
  Record we :=
    {
      we_key : Key;
      we_val : val;
      we_time : Time;
    }.

End Write_event.

Notation "s '<ₜ' t" :=
  (TM_lt (we_time s) (we_time t)) (at level 70, no associativity).

Notation "s '≤ₜ' t" :=
  (TM_lt (we_time s) (we_time t) ∨ s = t) (at level 70, no associativity).
Notation "s '=ₜ' t" :=
  (we_time s = we_time t) (at level 70, no associativity).


Section Events_lemmas.
  Context `{!KVS_time}.

  Global Instance we_dec : EqDecision we.
  Proof. solve_decision. Qed.

  Global Instance we_countable : Countable we.
  Proof.
    refine {| encode := λ a, encode (we_key a, we_val a, we_time a);
              decode := λ n,
                      (λ x, {| we_key := x.1.1; we_val := x.1.2;
                               we_time := x.2; |}) <$>
                        @decode
                        (Key * val * Time)%type
                        _ _ n
           |}.
    by intros []; rewrite /= decode_encode /=.
  Qed.

 End Events_lemmas.
