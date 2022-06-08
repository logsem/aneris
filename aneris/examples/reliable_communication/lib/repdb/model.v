From aneris.aneris_lang Require Import lang inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events.


Global Instance int_time : DB_time :=
  {| Time := nat;
    TM_lt := Nat.lt;
    TM_lt_tricho := PeanoNat.Nat.lt_trichotomy |}.

Instance: Inhabited (@we int_time) := populate (Build_we "" #() inhabitant).

Global Program Instance Inject_write_event : Inject we val :=
  {| inject a := $(a.(we_key), a.(we_val), a.(we_time))
  |}.
Next Obligation.
  intros w1 w2 Heq.
  inversion Heq as [[Hk Hv Ht]].
  assert (we_time w1 = we_time w2) as Ht'.
  { by apply (inj (R := eq)) in Ht; [ | apply _]. }
  destruct w1, w2; simpl in *.
  by apply Z_of_nat_inj in Ht; subst.
Qed.

Definition write_event := @we int_time.
Definition write_eventO := leibnizO write_event.
Definition wrlog := list write_eventO.


(* -------------------------------------------------------------------------- *)
(** The state validity defines coherence of the log and the memory model. *)

Section ValidStates.
  Context `{!DB_params}.

  (** Global Validity. *)
  Definition mem_dom (M : gmap Key (option write_event)) := DB_keys = dom M.

  Definition mem_we_key (M : gmap Key (option write_event)) :=
    ∀ k (we : write_event), k ∈ dom M →
                            M !! k = Some (Some we) → we.(we_key) = k.

  Definition mem_log_coh (L : wrlog) (M : gmap Key (option write_event)) :=
    ∀ k, k ∈ dom M → M !! k = Some (at_key k L).

  Definition in_log_mem_some_coh (L : wrlog) (M : gmap Key (option write_event)) :=
    ∀ k we, at_key k L = Some we → M !! we.(we_key) = Some (Some we).

 Definition mem_serializable_vals (M : gmap Key (option write_event)) :=
    ∀ k we, k ∈ dom M → M !! k = Some (Some we) →
            Serializable DB_serialization we.(we_val).

  Definition allocated_in_mem (L : wrlog) (M : gmap Key (option write_event)) :=
    ∀ l k wel, l ≤ₚ L → at_key k l = Some wel →
               ∃ weL, M !! k = Some (Some weL) ∧ wel ≤ₜ weL.

  Definition log_events (L : wrlog) :=
    ∀ (i : nat), 0 <= i → i < List.length L →
         ∃ we, List.nth_error L i = Some we ∧ i = we.(we_time).

  Record valid_state (L : wrlog) (M : gmap Key (option write_event)) : Prop :=
    {
      DB_GSTV_mem_dom : mem_dom M;
      DB_GSTV_mem_we_key : mem_we_key M;
      DB_GSTV_mem_log_coh : mem_log_coh L M;
      DB_GSTV_mem_in_log_mem_some_coh : in_log_mem_some_coh L M;
      DB_GSTV_mem_serializable_vals : mem_serializable_vals M;
      DB_GSTV_mem_allocated_in_mem : allocated_in_mem L M;
      DB_GSTV_log_events L : log_events L;
    }.

  Lemma valid_state_empty : valid_state [] ∅.
  Proof. Admitted.

  Lemma log_events_serializable L M :
    valid_state L M →
    ∀ (we : write_event),
    In we L →
    Serializable
     (prod_serialization
        (prod_serialization string_serialization DB_serialization)
        int_serialization) ($ we).
  Proof.
  Admitted.


 (** Local Validity. *)
  Definition mem_dom_local (M : gmap Key val) := dom M ⊆ DB_keys.

  Definition in_mem_log_some_coh_local (L : wrlog) (M : gmap Key val) :=
    ∀ k v, k ∈ dom M → M !! k = Some v → ∃ we, at_key k L = Some we ∧ we.(we_val) = v.

  Definition in_mem_log_none_coh_local (L : wrlog) (M : gmap Key val) :=
    ∀ k, k ∈ dom M → M !! k = None → at_key k L = None.

  Definition mem_serializable_vals_local (M : gmap Key val) :=
    ∀ k v, k ∈ dom M → M !! k = Some v → Serializable DB_serialization v.

  Definition in_log_mem_some_coh_local (L : wrlog) (M : gmap Key val) :=
    ∀ k we, at_key k L = Some we →  M !! we.(we_key) = Some we.(we_val).

  Definition in_log_mem_none_coh_local (L : wrlog) (M : gmap Key val) :=
    ∀ k, at_key k L = None → M !! k = None.

  Definition allocated_in_mem_local (L : wrlog) (M : gmap Key val) :=
    ∀ l k we1, l ≤ₚ L → at_key k l = Some we1 →
               ∃ we2, M !! k = Some we2.(we_val) ∧ we1 ≤ₜ we2.

  Record valid_state_local (L : wrlog) (M : gmap Key val) : Prop :=
    {
      DB_LSTV_log_events L : log_events L;
      DB_LSTV_mem_dom : mem_dom_local M;
      DB_LSTV_mem_serializable_vs_local : mem_serializable_vals_local M;
      DB_LSTV_in_mem_log_some_coh_local : in_mem_log_some_coh_local L M;
      DB_LSTV_in_mem_log_none_coh_local : in_mem_log_none_coh_local L M;
      DB_LSTV_in_log_mem_some_coh_local : in_log_mem_some_coh_local L M;
      DB_LSTV_in_log_mem_none_coh_local : in_log_mem_none_coh_local L M;
      DB_LSTV_mem_allocated_in_mem : allocated_in_mem_local L M;
    }.

(* TODO : valid state update lemmas. *)

  Lemma valid_state_local_empty : valid_state_local [] ∅.
  Proof. Admitted.

End ValidStates.
