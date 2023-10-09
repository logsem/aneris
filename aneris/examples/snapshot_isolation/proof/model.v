From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib.serialization Require Import
  serialization_proof.
From aneris.examples.snapshot_isolation.specs Require Export
  user_params.
From aneris.examples.snapshot_isolation.specs Require Export
  time events.

Section Whist_valid.
  Context `{!User_params}.

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

  Global Arguments whist_ValidKeys {_ _} _.
  Global Arguments whist_ValidExt {_ _} _.
  Global Arguments whist_ValidTimes {_ _} _.
  Global Arguments whist_ValidVals {_ _} _.

  Lemma whist_valid_included (h h' : whist) :
    h `prefix_of` h' →
    whist_valid h' →
    whist_valid h.
  Proof.
    move=>h_h' [keys times vals ext].
    split.
    - move=>we we_h.
      apply keys.
      by apply (elem_of_prefix h).
    - move=>wei wej i j i_j h_i h_j.
      apply (times _ _ i j);
        [done|by apply (prefix_lookup_Some h)..].
    - move=>we we_h.
      apply vals.
      by apply (elem_of_prefix h).
    - move=>we we' we_h we'_h e_e'.
      apply ext;
        [by apply (elem_of_prefix h)..|done].
  Qed.

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
    ∀ k h, M !! k = Some h → ∀ e, e ∈ h → (e.(we_time) <= T)%nat.
  
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
    split; rewrite /kvs_ValidDom /kvs_dom /kvs_whists /kvs_ValidWhists /kvs_ValidCommitTimes.
    -  by rewrite dom_gset_to_gmap.
    - intros ? ? Habs. apply lookup_gset_to_gmap_Some in Habs as [_ <-].
      split; rewrite /whist_times /whist_ext; set_solver.
    - rewrite /kvs_keys. intros  ? ? Habs e eh.
      apply lookup_gset_to_gmap_Some in Habs as [_ <-]. set_solver.
    - rewrite /kvs_whist_commit_times. intros ? ? Habs.
      apply lookup_gset_to_gmap_Some in Habs as [_ <-]. set_solver.
    - by rewrite /kvs_time_snapshot_map_valid.
    - by rewrite /kvs_snapshots_included.
    - by rewrite /kvs_snapshots_cuts.
   Qed. 
  
  (** A system step starting new transaction is valid.  *)
  Lemma kvs_valid_step_start_transaction M S T :
    kvs_valid M S T →
    kvs_valid M (<[(T+1)%nat := M]>S) (T + 1).
  Proof.
    destruct 1.
    split; 
    unfold
      kvs_whists,
      kvs_keys,
      kvs_whist_commit_times,
      kvs_time_snapshot_map_valid,
      kvs_snapshots_included,
      kvs_snapshots_cuts in *;
      try eauto with set_solver.
    - intros k h Hk e He.
      specialize (kvs_ValidCommitTimes0 k h Hk e He). lia.
    - intros n Hn.
      specialize (kvs_ValidSnapshotTimesTime0 n).
      rewrite dom_insert in Hn.
      apply elem_of_union in Hn as [Hn|Hn].
      -- by rewrite elem_of_singleton in Hn; eauto with lia.
      -- specialize (kvs_ValidSnapshotTimesTime0 Hn).
         eauto with lia.
    - intros t Mt Hmt.
      destruct (bool_decide (t = (T + 1)%nat)) eqn:Hteq. 
      -- rewrite bool_decide_eq_true in Hteq. subst.
         rewrite lookup_insert in Hmt.
         inversion Hmt.
         rewrite /map_included; eauto.
      -- rewrite bool_decide_eq_false in Hteq.
         rewrite lookup_insert_ne in Hmt; last done.
         naive_solver. 
    - intros t k h_snap h_curr Mt Hmt Hmtk Hmk.
      destruct (bool_decide (t = (T + 1)%nat)) eqn:Hteq. 
      -- rewrite bool_decide_eq_true in Hteq. subst.
         rewrite lookup_insert in Hmt.
         inversion Hmt; subst.
         rewrite Hmk in Hmtk.
         inversion Hmtk; subst.
         exists []. split; first by apply app_nil_end.
         split; last by set_solver.
         intros e He.
         specialize (kvs_ValidCommitTimes0 k h_snap Hmk e He). lia.
      -- rewrite bool_decide_eq_false in Hteq.
         rewrite lookup_insert_ne in Hmt; last done.
         naive_solver. 
  Qed.  

  (** A system step updating the memory with the effect of commit 
      of a transaction is valid *)
  Lemma kvs_valid_update M S T (cache : gmap Key SerializableVal) :
    dom cache ⊆ KVS_keys →
    kvs_valid M S T →
    kvs_valid (update_kvs M cache (T+1)) S (T+1).
  Proof.
  Admitted.

  (* TODO rephrase without delete *)
  Lemma kvs_valid_single_snapshot_delete M Mts T t Mt k :
    kvs_valid M Mts T →
    Mts !! t = Some Mt →
    kvs_valid (delete k M) {[t := delete k Mt]} T.
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
    move=>[dom_M hists_valid keys_M commit_times snapshot_valid snapshots_included
            snapshots_cut Mts_t Mt_Msub [dom_Msub Msub_M]].
    split.
    - set_solver.
    - move=>k h Msub_k.
      move: (Msub_M _ _ Msub_k)=>[h' [/hists_valid h'_valid h_h']].
      apply (whist_valid_included _ _ h_h' h'_valid).
    - move=>k h Msub_k we we_h.
      move: (Msub_M _ _ Msub_k)=>[h' [M_k h_h']].
      apply (keys_M _ h'); first done.
      by apply (elem_of_prefix h).
    - move=>k h Msub_k we we_h.
      move: (Msub_M _ _ Msub_k)=>[h' [M_k h_h']].
      apply (commit_times k h'); first done.
      by apply (elem_of_prefix h).
    - move=>T0 T0_t.
      apply elem_of_dom in T0_t.
      move: T0_t=>[x/lookup_singleton_Some][<- _] {T0 x}.
      apply snapshot_valid, elem_of_dom.
      by exists Mt.
    - by move=>t' Mt'/lookup_singleton_Some[_ <-].
    - move=>t' k h_snap h_curr Mt' /lookup_singleton_Some [<- <-] Mt_k.
      move:Mt_Msub=>[_]/(_ k h_snap Mt_k)[h_snap'][Msub_k][h' h_snap_def].
      rewrite h_snap_def in Msub_k.
      rewrite Msub_k=>[][<-] {t' h_curr Mt' h_snap_def h_snap'}.
      move:Msub_k=>/Msub_M[h][M_k][h'' h_def].
      move: (snapshots_cut _ _ _ _ _ Mts_t Mt_k M_k)=>
            [h_after [h_curr'_eq][snap_t after_t]].
      exists h'.
      do 2 (split; first done).
      rewrite -app_assoc  h_curr'_eq in h_def.
      apply app_inv_head in h_def.
      rewrite h_def in after_t.
      move=>we we_h'.
      apply after_t, elem_of_app.
      tauto.
  Qed.

  (**  Weakening lemma. *)
  Lemma kvs_valid_single_snapshot M Mts T t Mt:
    kvs_valid M Mts T →
    Mts !! t = Some Mt →
    kvs_valid M {[ t := Mt ]} T.
  Proof.
    intros M_valid Mts_t.
    apply (kvs_valid_global_mem_prefix _ _ _ _ _ _ M_valid Mts_t); last split.
    - apply (kvs_ValidSnapshotTimesInclusion _ _ _ M_valid t Mt Mts_t).
    - done.
    - move=>k h1 ->.
      by exists h1.
  Qed.

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
    split; [set_solver|done| |done|apply valid_init_state].
    move=>k h emp_k abs.
    apply lookup_gset_to_gmap_Some in emp_k.
    by move: emp_k abs=>[_ <-].
  Qed.

  Definition update_kvsl
    (m0 : gmap Key val)
    (C : gmap Key SerializableVal)
    (T : nat) : gmap Key val :=
    map_fold (λ k v m, 
        (<[ k := SOMEV ($(k, (v.(SV_val), T)),
                     (default NONEV (m0 !! k)))]> m))
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
  Proof.
    move=>[dom_m empty_coh model_coh local_coh valid].
    split; [done..|exact: kvs_valid_step_start_transaction].
  Qed.

  (* TODO rephrase without delete *)
  Lemma kvsl_model_empty_delete m M k :
    kvsl_in_model_empty_coh m M →
    kvsl_in_model_empty_coh m (delete k M).
  Proof.
  Admitted.

  (* TODO rephrase without delete *)
  Lemma kvsl_model_some_delete m M k :
    kvsl_in_model_some_coh m M →
    kvsl_in_model_some_coh m (delete k M).
  Proof.
  Admitted.

  (* TODO rephrase without filter. When mu = ∅ and M ≠ ∅,
      the domain condition cannot be proven *)
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


  Definition kvs_valid_snapshot
    (Msnap : global_mem) (t : nat) :=
    (* dom Msnap ⊆ KVS_keys ∧ *)
    (* kvs_whists Msnap ∧ *)
    (* kvs_keys Msnap ∧ *)
    ∀ k h, Msnap !! k = Some h → ∀ e, e ∈ h → e.(we_time) < t.

  (* TODO rephrase without delete *)
  Lemma kvs_valid_snapshot_delete M ts k :
    kvs_valid_snapshot M ts ->
    kvs_valid_snapshot (delete k M) ts.
  Proof. Admitted.
  

