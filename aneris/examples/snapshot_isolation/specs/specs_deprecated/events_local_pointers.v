
From aneris.aneris_lang Require Import lang.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params.
From aneris.examples.snapshot_isolation.specs.specs_deprecated
     Require Import time.


(** Write and apply events *)

Section Events.
  Context `{!KVS_time}.

  (* Definition EV_id : Set := socket_address * nat. *)

 (** Write event *)
  Record write_event :=
    {
      we_key : Key;
      we_val : val;
      we_time : Time;
    }.
 (** Cache event *)
  Record cache_event :=
   {
     cache_snap : option write_event;
     cache_newv : option val;
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

  Global Instance cahce_event_dec : EqDecision cache_event.
  Proof. solve_decision. Qed.

  Global Instance cache_event_countable : Countable cache_event.
  Proof.
    refine {| encode := λ a, encode (cache_snap a, cache_newv a);
              decode := λ n,
                      (λ x, {| cache_snap := x.1; cache_newv := x.2; |}) <$>
                        @decode
                        (option write_event * option val)%type
                        _ _ n
           |}.
    by intros []; rewrite /= decode_encode /=.
  Qed.

 End Events_lemmas.
