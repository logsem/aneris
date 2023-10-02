From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib.serialization Require Import
  serialization_proof.
From aneris.examples.snapshot_isolation.specs Require Export
  user_params.
From aneris.examples.snapshot_isolation.proof Require Export
  time events.


Global Instance int_time : KVS_time :=
  {| Time := nat;
    TM_lt := Nat.lt;
    TM_lt_tricho := PeanoNat.Nat.lt_trichotomy |}.

Instance: Inhabited (@write_event int_time) := populate (Build_write_event "" #() inhabitant).

Global Program Instance Inject_write_event : Inject write_event val :=
  {| inject a := $(a.(we_key), (a.(we_val), a.(we_time)))
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

Section Whist_valid.
  Context `{!anerisG Mdl Σ, !User_params}.

  Definition whist_keys (s : whist) :=
    ∀ e, e ∈ s → e.(we_key) ∈ KVS_keys.

  Definition whist_times (h : whist) :=
    ∀ ei ej (i j : nat),
    i < j →
    h !! i = Some ei →
    h !! j = Some ej →
    ei.(we_time) < ej.(we_time).

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

  (** TODO: Proof this lemma if needed or remove. *)
  Lemma whist_events_no_dup h : whist_valid h → NoDup h.
  Proof.
  Admitted.

  Global Arguments whist_ValidKeys {_ _} _.
  Global Arguments whist_ValidExt {_ _} _.
  Global Arguments whist_ValidTimes {_ _} _.
  Global Arguments whist_ValidVals {_ _} _.

End Whist_valid.

Definition global_mem :=  gmap Key whist.
Definition snapshots := gmap nat global_mem.

Definition map_included (m1 m2 : global_mem) : Prop :=
  dom m1 = dom m2 ∧
  ∀ k h1, m1 !! k = Some h1 →
    ∃ h2, m2 !! k = Some h2 ∧ h1 `prefix_of` h2.


Section KVS_valid.
  Context `{!User_params}.

  Definition kvs_dom (M : global_mem) := KVS_keys = dom M.

  Definition kvs_whists (M : global_mem) :=
    ∀ k h, M !! k = Some h → whist_valid h.

  Definition kvs_keys (M : global_mem) :=
    ∀ k h, M !! k = Some h → ∀ e, e ∈ h → e.(we_key) = k.

  Definition kvs_whist_commit_times (M : global_mem) (T : nat) :=
    ∀ k h, M !! k = Some h → ∀ e, e ∈ h → e.(we_time) <= T.
  
  (** Importantly, note that there is currently no relation between snapshots
      for two given transactions. We only relate snapshots to the state of 
      the global memory. *)
  Definition kvs_snapshots_included (M : global_mem) (S : snapshots) : Prop :=
    ∀ t Mt,
      S !! t = Some Mt →
      map_included Mt M.
   
  Definition kvs_snapshots_cuts (M : global_mem) (S : snapshots) : Prop :=
    ∀ t k h_snap h_curr Mt,
      S !! t = Some Mt →
      Mt !! k = Some h_snap →
      M !! k = Some h_curr →
      ∃ h_after, h_curr = h_snap ++ h_after ∧
              (∀ e, e ∈ h_snap → e.(we_time) < t) ∧
              (∀ e, e ∈ h_after → t < e.(we_time)).

  Definition kvs_time_snapshot_map_valid (S : snapshots) (T : nat) : Prop :=
    ∀ (t : nat), t ∈ dom S → (t <= T)%nat.
 
  Record kvs_valid (M : global_mem) (S : snapshots) (T : nat) : Prop :=
    {
      kvs_ValidDom: kvs_dom M;
      kvs_ValidWhists : kvs_whists M;
      kvs_ValidKeys : kvs_keys M;
      kvs_ValidCommitTimes : kvs_whist_commit_times M T;
      kvs_ValidSnapshotTimesTime : kvs_time_snapshot_map_valid S T;
      kvs_ValidSnapshotTimesInclusion : kvs_snapshots_included M S;
      kvs_ValidSnapshotTimesCuts : kvs_snapshots_cuts M S
    }.

  Definition update_kvs
    (M0 : global_mem) (C : gmap Key SerializableVal) (T : nat) :=
      map_fold
        (λ k v M,
           (<[ k := (default [] (M !! k)) ++
                      [{|
                          we_key := k;
                          we_val := v.(SV_val);
                          we_time := T
                        |}]
             ]> M))
        M0 C.

  Lemma upd_serializable
    (cache : gmap Key SerializableVal)
    (M : gmap Key (list write_event)) (T : nat) :
    map_Forall
      (λ (_ : Key) (l : list events.write_event),
        Forall (λ we : events.write_event,
              KVS_Serializable (we_val we)) l) M
    →
    map_Forall
      (λ (_ : Key) (l : list events.write_event),
        Forall (λ we : events.write_event,
              KVS_Serializable (we_val we)) l) (update_kvs M cache T).
  Proof.
  Admitted. 


  
  (** The initial state of the system is valid. *)
  Lemma valid_init_state :
    kvs_valid (gset_to_gmap [] KVS_keys) ∅ 0.
  Proof.
  Admitted.
  (*
    split; rewrite /kvs_ValidDom /kvs_dom /kvs_whists /kvs_ValidWhists /kvs_ValidCommitTimes.
    -  by rewrite dom_gset_to_gmap.
    - intros ? ? Habs. apply lookup_gset_to_gmap_Some in Habs as [_ <-].
      split; rewrite /whist_times /whist_ext; set_solver.
    - rewrite /kvs_keys. intros  ? ? Habs e eh.
      apply lookup_gset_to_gmap_Some in Habs as [_ <-]. set_solver.
    - rewrite /kvs_whist_commit_times. intros ? ? Habs.
      apply lookup_gset_to_gmap_Some in Habs as [_ <-]. set_solver.
    - by rewrite /time_tss_valid.
    - by rewrite /kvs_tss_valid.
   Qed. *)
  
  (** A system step starting new transaction is valid.  *)
  Lemma kvs_valid_step_start_transaction M S T :
    kvs_valid M S T →
    kvs_valid M (<[(T+1)%nat := M]>S) (T + 1).
  Proof.
  Admitted.

  (** A system step updating the memory with the effect of commit 
      of a transaction is valid *)
  Lemma kvs_valid_update M S T (cache : gmap Key SerializableVal) :
    dom cache ⊆ KVS_keys →
    kvs_valid M S T →
    kvs_valid (update_kvs M cache (T+1)) S (T+1).
  Proof.
  Admitted.

  (**  Weakening lemma. *)
  Lemma kvs_valid_single_snapshot M Mts T t Mt:
    kvs_valid M Mts T →
    Mts !! t = Some Mt →
    kvs_valid M {[ t := Mt ]} T.
  Proof.
  Admitted.
  
  (** Strong Weakening lemma. *)
  Lemma kvs_valid_global_mem_prefix M Mts T t Mt Msub:
    kvs_valid M Mts T →
    Mts !! t = Some Mt →
    map_included Mt Msub →
    map_included Msub M →
    kvs_valid Msub {[ t := Mt ]} T.
  Proof.
  Admitted.

End KVS_valid.

(** Local Validity tying physical and logical state. *)

Section KVSL_valid.
  Context `{!User_params}.

  Definition kvsl_dom (m : gmap Key val) := dom m ⊆ KVS_keys.

  Definition kvsl_in_model_empty_coh (m : gmap Key val) (M : global_mem) :=
    ∀ k, M !! k = Some [] → m !! k = None.

  Definition kvsl_in_model_some_coh (m : gmap Key val) (M : global_mem) :=
    ∀ k (h: whist), M !! k = Some h → h ≠ [] → m !! k = Some $(reverse h).

  Definition kvsl_in_local_some_coh (m : gmap Key val) (M : global_mem) :=
    ∀ k (h: whist), m !! k = Some $h → M !! k = Some (reverse h).

  Record kvsl_valid
    (m : gmap Key val) (M : global_mem) (S : snapshots) (T : nat) : Prop :=
    {
      kvsl_ValidDom: kvsl_dom m;
      kvsl_ValidInModelEmpty : kvsl_in_model_empty_coh m M;
      kvsl_ValidInModelSome : kvsl_in_model_some_coh m M;
      kvsl_ValidLocalSome : kvsl_in_local_some_coh m M;
      kvsl_ValidModel : kvs_valid M S T
    }.
  
  Lemma kvsl_valid_empty :
    kvsl_valid ∅ (gset_to_gmap [] KVS_keys) ∅ 0.
  Proof.
  Admitted.

  Definition update_kvsl
    (m0 : gmap Key val)
    (C : gmap Key SerializableVal)
    (T : nat) :=
    map_fold (λ k v m, 
               (<[ k := SOMEV ($(k, (v.(SV_val), T)), v)]> m))
      m0 C.

  (** Used for commit *)
  Lemma kvsl_valid_update
    (m : gmap Key val)
    (M : global_mem)
    (Mts : snapshots)
    (T : nat) 
    (cache : gmap Key SerializableVal) :
    dom cache ⊆ KVS_keys →
    kvsl_valid m M Mts T →
    kvsl_valid
      (update_kvsl m cache (T+1))
      (update_kvs M cache (T+1)) Mts (T+1).
  Proof.
  Admitted.

  (** Used for start *)
  Lemma kvsl_valid_next M S (m : gmap Key val) T :
    kvsl_valid m M S T →
    kvsl_valid m M (<[(T+1)%nat := M]>S) (T + 1).
  Proof. Admitted.

  
  (** Weakening lemma *)
  Lemma kvs_valid_filter M S t Mt (mu : gmap Key (list val)) T :
    kvs_valid M S T →
    S !! t = Some Mt →
    kvs_valid
      (filter (λ k : Key * list write_event, k.1 ∈ dom mu) M)
      {[t := (filter (λ k : Key * list write_event, k.1 ∈ dom mu) Mt) ]}
      T.
  Proof.
  Admitted.
  
End KVSL_valid.

Section Snapshot.
  Context `{!User_params}.

  Definition kvs_valid_snapshot
    (Msnap : global_mem) (t : Time) :=
    (* dom Msnap ⊆ KVS_keys ∧ *)
    (* kvs_whists Msnap ∧ *)
    (* kvs_keys Msnap ∧ *)
    ∀ k h, Msnap !! k = Some h → ∀ e, e ∈ h → e.(we_time) < t.

  Lemma kvs_valid_snapshot_delete M ts k :
    kvs_valid_snapshot M ts ->
    kvs_valid_snapshot (delete k M) ts.
  Proof. Admitted.
  
End Snapshot.

