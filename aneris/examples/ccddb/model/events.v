(** Realisation of the write and apply events. *)

From aneris.aneris_lang Require Import lang inject.
From aneris.examples.ccddb.spec Require Export base.
From aneris.aneris_lang.lib Require Import vector_clock_proof.
From aneris.prelude Require Export time.
From aneris.aneris_lang.lib Require Import list_proof.

Record write_event :=
  WriteEvent {
    we_key : string;
    we_val : val;
    we_time : vector_clock;
    we_orig : nat
  }.

Instance: Inhabited write_event := populate (WriteEvent "" #() inhabitant 0).

Global Instance we_decidable : EqDecision write_event.
Proof. solve_decision. Qed.

Global Instance we_countable : Countable write_event.
Proof.
  refine {| encode := λ a, encode (we_key a, we_val a, we_time a, we_orig a);
            decode := λ n,
                      (λ x, {| we_key := x.1.1.1; we_val := x.1.1.2;
                               we_time := x.1.2; we_orig := x.2 |}) <$>
                        @decode
                        (string * val * vector_clock * nat)%type
                        _ _ n
         |}.
  by intros []; rewrite /= decode_encode /=.
Qed.


(* TODO: using vector_clock_to_val is a bit of a hack. Ideally, we'd just
   do $ (..., a.(we_time), ...) and deprecate vector_clock_to_val.
   Unfortunately, vector_clock_to_val is used in many places at the moment,
   so we're keeping it for now. *)
Global Program Instance Inject_write_event : Inject write_event val :=
  {| inject a := $(a.(we_key), a.(we_val), vector_clock_to_val a.(we_time), a.(we_orig))
  |}.
Next Obligation.
  intros w1 w2 Heq.
  inversion Heq as [[Hk Hv Ht Ho]].
  assert (we_time w1 = we_time w2) as Ht'.
  { by apply (inj (R := eq)) in Ht; [ | apply _]. }
  destruct w1, w2; simpl in *.
  by apply Z_of_nat_inj in Ho; subst.
Qed.


Record apply_event :=
  ApplyEvent {
    ae_key : string;
    ae_val : val;
    ae_time : vector_clock;
    ae_orig : nat;
    ae_seqid : nat
  }.

Instance: Inhabited apply_event := populate (ApplyEvent "" #() inhabitant 0 0).

Global Instance ae_decidable : EqDecision apply_event.
Proof. solve_decision. Qed.

Global Instance ae_countable : Countable apply_event.
Proof.
  refine {| encode :=
              λ a, encode (ae_key a, ae_val a, ae_time a, ae_orig a, ae_seqid a);
            decode :=
              λ n,
              (λ x, {| ae_key := x.1.1.1.1; ae_val := x.1.1.1.2;
                       ae_time := x.1.1.2; ae_orig := x.1.2;
                       ae_seqid := x.2|})
                <$>
                @decode
                (string * val * vector_clock * nat * nat)%type
                _ _ n
         |}.
  by intros []; rewrite /= decode_encode /=.
Qed.

Definition erase (ae : apply_event) : write_event :=
  match ae with
    ApplyEvent k v t o _ => WriteEvent k v t o
  end.

Lemma erase_orig : ∀ (e : apply_event), (erase e).(we_orig) = e.(ae_orig).
Proof. by destruct e. Qed.

Lemma erase_key : ∀ (e : apply_event), (erase e).(we_key) = e.(ae_key).
Proof. by destruct e. Qed.

Lemma erase_val : ∀ (e : apply_event), (erase e).(we_val) = e.(ae_val).
Proof. by destruct e. Qed.

Lemma erase_time : ∀ (e : apply_event), we_time (erase e) = ae_time e.
Proof. by destruct e. Qed.

Definition restrict_key (k : Key) (s : gset apply_event) : gset apply_event :=
  filter (λ x, x.(ae_key) = k) s.
