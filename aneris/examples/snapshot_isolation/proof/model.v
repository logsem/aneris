From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params.
From aneris.examples.snapshot_isolation.proof
     Require Import time events.


Global Instance int_time : KVS_time :=
  {| Time := nat;
    TM_lt := Nat.lt;
    TM_lt_tricho := PeanoNat.Nat.lt_trichotomy |}.

Instance: Inhabited (@write_event int_time) := populate (Build_write_event "" #() inhabitant).

Global Program Instance Inject_write_event : Inject write_event val :=
  {| inject a := $(a.(we_key), a.(we_val), a.(we_time))
  |}.
Next Obligation.
  intros w1 w2 Heq.
  inversion Heq as [[Hk Hv Ht]].
  assert (we_time w1 = we_time w2) as Ht'.
  { by apply (inj (R := eq)) in Ht; [ | apply _]. }
  destruct w1, w2; simpl in *.
  by apply Nat2Z.inj in Ht; subst.
Qed.

Definition write_event := @write_event int_time.
Definition write_eventO := leibnizO write_event.
Definition whist := list write_eventO.
Definition kvsMdl :=  gmap Key whist.


Section Whist_valid.
  Context `{!anerisG Mdl Σ, !User_params}.

  Definition whist_keys (s : whist) :=
    ∀ e, e ∈ s → e.(we_key) ∈ KVS_keys.

  Definition whist_times (h : whist) :=
    ∀ ei ej (i j : nat),
    i < j → h !! i = Some ei →
    h !! j = Some ej →
    ej.(we_time) < ei.(we_time).

  Definition whist_vals (h : whist) :=
    ∀ e, e ∈ h → Serializable KVS_serialization e.(we_val).

  Definition whist_ext (h : whist) :=
    ∀ e e', e ∈ h → e' ∈ h → e.(we_time) = e'.(we_time) → e = e'.

  Record whist_valid (h : whist) : Prop := {
    whist_ValidKeys: whist_keys h;
    whist_ValidTimes: whist_times h;
    whist_ValidVals: whist_vals h;
    whist_ValidExt: whist_ext h;
}.


  Lemma whist_events_no_dup h : whist_valid h → NoDup h.
  Proof.
  Admitted.

  Global Arguments whist_ValidKeys {_ _} _.
  Global Arguments whist_ValidExt {_ _} _.
  Global Arguments whist_ValidTimes {_ _} _.
  Global Arguments whist_ValidVals {_ _} _.

End Whist_valid.

(** For now, we don't use a commit-times M map : nat → gmap key write_event that would track in the logic
    for each commit time T the events that extended the KVS with the cache M(T), but maybe it could be
    necessary or useful.
    Similarly, we don't model separately commit times and start times, and currently use only one global time
    for both, which gives a very simple kvs model coherence. In particular, if the global time is strictly
    positive, it does not imply that any commit happened previously. *)

Section KVS_valid.
  Context `{!User_params}.

  Definition kvs_dom (M : kvsMdl) := KVS_keys = dom M.

  Definition kvs_whists (M : kvsMdl) :=
    ∀ k h, M !! k = Some h → whist_valid h.

  Definition kvs_keys (M : kvsMdl) :=
    ∀ k h, M !! k = Some h → ∀ e, e ∈ h → e.(we_key) = k.

  Definition kvs_whist_commit_times (M : kvsMdl) (T : nat) :=
    ∀ k h, M !! k = Some h → ∀ e, e ∈ h → e.(we_time) <= T.


  Record kvs_valid (M : kvsMdl) (T : nat) : Prop :=
    {
      kvs_ValidDom: kvs_dom M;
      kvs_ValidWhists : kvs_whists M;
      kvs_ValidKeys : kvs_keys M;
      kvs_ValidCommitTimes : kvs_whist_commit_times M T;
    }.

  Lemma valid_state_empty :
    kvs_valid (gset_to_gmap [] KVS_keys) 0.
  Proof.
    split; rewrite /kvs_ValidDom /kvs_dom /kvs_whists /kvs_ValidWhists /kvs_ValidCommitTimes.
    -  by rewrite dom_gset_to_gmap.
    - intros ? ? Habs. apply lookup_gset_to_gmap_Some in Habs as [_ <-].
      split; rewrite /whist_times /whist_ext; set_solver.
    - rewrite /kvs_keys. intros  ? ? Habs e eh.
      apply lookup_gset_to_gmap_Some in Habs as [_ <-]. set_solver.
    - rewrite /kvs_whist_commit_times. intros ? ? Habs.
      apply lookup_gset_to_gmap_Some in Habs as [_ <-]. set_solver.
   Qed.

  Definition update_kvs (M0 : kvsMdl) (C : gmap Key SerializableVal) (T : nat) :=
      map_fold
        (λ k v M,
           (<[ k := {| we_key := k; we_val := v.(SV_val); we_time := T |} :: default [] (M !! k)]> M))
        M0 C.

  Lemma kvs_valid_update_cell  (M : kvsMdl) (T : nat) (k : Key) (v : SerializableVal) :
    k ∈ KVS_keys →
    kvs_valid M T ->
    kvs_valid
      (<[ k := {| we_key := k; we_val := v; we_time := (T + 1)%nat |} :: default [] (M !! k)]> M)
      (T+1).
  Proof.
  Admitted.

  Lemma kvs_valid_update  (M : kvsMdl) (T : nat) (cache : gmap Key SerializableVal) :
    dom cache ⊆ KVS_keys →
    kvs_valid M T ->
    kvs_valid (update_kvs M cache (T+1)) (T+1).
  Proof.
  Admitted.

End KVS_valid.


(** Local Validity tying physical and logical state. *)

Section KVSL_valid.
  Context `{!User_params}.

  Definition kvsl_dom (m : gmap Key val) := dom m ⊆ KVS_keys.

  Definition kvsl_in_model_empty_coh (m : gmap Key val) (M : kvsMdl) :=
    ∀ k, M !! k = Some [] → m !! k = None.

  Definition kvsl_in_model_some_coh (m : gmap Key val) (M : kvsMdl) :=
    ∀ k (h: whist), M !! k = Some h → h ≠ [] → m !! k = Some $h.

  Definition kvsl_in_local_some_coh (m : gmap Key val) (M : kvsMdl) :=
    ∀ k (h: whist), m !! k = Some $h → M !! k = Some h.

  Record kvsl_valid (m : gmap Key val) (M : kvsMdl) (T : nat) : Prop :=
    {
      kvsl_ValidDom: kvsl_dom m;
      kvsl_ValidInModelEmpty : kvsl_in_model_empty_coh m M;
      kvsl_ValidInModelSome : kvsl_in_model_some_coh m M;
      kvsl_ValidLocalSome : kvsl_in_local_some_coh m M;
      kvsl_ValidModel : kvs_valid M T
    }.

  Lemma kvsl_valid_empty :
    kvsl_valid ∅ (gset_to_gmap [] KVS_keys) 0.
  Proof.
  Admitted.

(* TODO: adapt for local state *)
  (* Definition update_kvs (M0 : kvsMdl) (C : gmap Key SerializableVal) (T : nat) := *)
(*       map_fold *)
(*         (λ k v M, *)
(*            (<[ k := {| we_key := k; we_val := v.(SV_val); we_time := T |} :: default [] (M !! k)]> M)) *)
(*         M0 C. *)

(*   Lemma kvs_valid_update_cell  (M : kvsMdl) (T : nat) (k : Key) (v : SerializableVal) : *)
(*     k ∈ KVS_keys → *)
(*     kvs_valid M T -> *)
(*     kvs_valid *)
(*       (<[ k := {| we_key := k; we_val := v; we_time := (T + 1)%nat |} :: default [] (M !! k)]> M) *)
(*       (T+1). *)
(*   Proof. *)
(*   Admitted. *)

(*   Lemma kvs_valid_update  (M : kvsMdl) (T : nat) (cache : gmap Key SerializableVal) : *)
(*     dom cache = KVS_keys → *)
(*     kvs_valid M T -> *)
(*     kvs_valid (update_kvs M cache (T+1)) (T+1). *)
(*   Proof. *)
(*   Admitted. *)
(* End KVSL_valid. *)

End KVSL_valid.

(** We might need as well some model of client side state. *)
