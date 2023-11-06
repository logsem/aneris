From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib.serialization Require Import
  serialization_proof.
From aneris.examples.snapshot_isolation.specs Require Export
  user_params.
From aneris.examples.snapshot_isolation.specs Require Export
  time events.
Import gset_map.

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

  Lemma whist_valid_empty : whist_valid [].
  Proof.
    split.
    - by move=>?/elem_of_nil.
    - move=>? ? ? ? ?.
      by rewrite lookup_nil.
    - by move=>?/elem_of_nil.
    - by move=>? ? /elem_of_nil.
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
    (M : global_mem) (C : gmap Key SerializableVal) (T : nat) : global_mem :=
      fn_to_gmap (dom M) (λ k,
        let h := default [] (M !! k) in
        match C !! k with
          | Some v => (h ++
                      [{|
                        we_key := k;
                        we_val := v.(SV_val);
                        we_time := T
                      |}])
          | None => h
        end).

  Lemma lookup_update_kvs_Some M C T k h :
    update_kvs M C T !! k = Some h ↔
    (C !! k = None ∧ M !! k = Some h) ∨ (
      ∃ h' v, M !! k = Some h' ∧ C !! k = Some v ∧
      h = h' ++ [{|
                  we_key := k;
                  we_val := v.(SV_val);
                  we_time := T
                |}]).
  Proof.
    split.
    + move=>/lookup_fn_to_gmap[]/[swap]/elem_of_dom[h'->]/=.
      case C_k : (C !! k)=>[v|]<-.
      - right.
        by exists h', v.
      - by left.
    + by move=>[[C_k M_k]|[h'][v][M_k][C_k]->]; apply lookup_fn_to_gmap; rewrite C_k M_k/=;
        (split; last apply elem_of_dom).
  Qed.

  Lemma upd_dom M C T :
    dom (update_kvs M C T) = dom M.
  Proof.
    by rewrite fn_to_gmap_dom.
  Qed.

  Lemma update_kvs_empty M T :
    update_kvs M ∅ T = M.
  Proof.
    apply map_eq.
    move=>k.
    case M_k : (M !! k)=>[h|].
    - apply lookup_update_kvs_Some.
      by left.
    - by apply lookup_fn_to_gmap_not_in, not_elem_of_dom.
  Qed.

  Lemma update_kvs_insert_Some m C T k v h :
    m !! k = Some h →
    update_kvs m (<[k := v]> C) T =
      <[k := h ++ [{|
                  we_key := k;
                  we_val := v.(SV_val);
                  we_time := T
                |}]]> (update_kvs m C T).
  Proof.
    move=>m_k.
    apply map_eq=>k'.
    case (string_eq_dec k k')=>[<-|neq].
    {
      rewrite lookup_insert.
      apply lookup_update_kvs_Some.
      right.
      erewrite lookup_insert.
      eauto.
    }
    rewrite lookup_insert_ne; last done.
    set m_k'_ := m !! k'.
    case m_k' : m_k'_=>[h'|]; rewrite /m_k'_ in m_k'=>{m_k'_};
      last by rewrite !not_elem_of_dom_1//upd_dom; apply not_elem_of_dom.
    set C_k'_ := C !! k'.
    case C_k' : C_k'_=>[v'|]; rewrite /C_k'_ in C_k'=>{C_k'_}.
    - erewrite (proj2 (lookup_update_kvs_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvs_Some. right. eauto. }
      right. by erewrite lookup_insert_ne; first eauto.
    - erewrite (proj2 (lookup_update_kvs_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvs_Some. left. eauto. }
      left. by erewrite lookup_insert_ne; first eauto.
  Qed.

  Lemma update_kvs_insert_None m C T k v :
    m !! k = None →
    update_kvs m (<[k := v]> C) T = (update_kvs m C T).
  Proof.
    move=>m_k.
    apply map_eq=>k'.
    case (string_eq_dec k k')=>[<-|neq];
      first by rewrite !not_elem_of_dom_1//upd_dom; apply not_elem_of_dom.
    set m_k'_ := m !! k'.
    case m_k' : m_k'_=>[h'|]; rewrite /m_k'_ in m_k'=>{m_k'_};
      last by rewrite !not_elem_of_dom_1//upd_dom; apply not_elem_of_dom.
    set C_k'_ := C !! k'.
    case C_k' : C_k'_=>[v'|]; rewrite /C_k'_ in C_k'=>{C_k'_}.
    - erewrite (proj2 (lookup_update_kvs_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvs_Some. right. eauto. }
      right. by erewrite lookup_insert_ne; first eauto.
    - erewrite (proj2 (lookup_update_kvs_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvs_Some. left. eauto. }
      left. by erewrite lookup_insert_ne; first eauto.
  Qed.

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
    move=>M_ser k h/lookup_update_kvs_Some[[cache_k M_k]|[h'][v][M_k][cache_k]->];
    specialize (M_ser _ _ M_k); first done.
    apply Forall_app.
    split; first done.
    apply Forall_singleton, _.
  Qed.

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

  Lemma kvs_whist_commit_times_delete k M T :
    kvs_whist_commit_times M T →
    kvs_whist_commit_times (delete k M) T.
  Proof.
    by move=>commit_times k' h/lookup_delete_Some[_]/commit_times.
  Qed.

  Lemma kvs_time_snapshot_map_valid_delete t St k S T :
    kvs_time_snapshot_map_valid S T →
    S !! t = Some St →
    kvs_time_snapshot_map_valid {[t := delete k St]} T.
  Proof.
    move=>map_valid S_t t'.
    rewrite dom_singleton_L elem_of_singleton=>->.
    apply map_valid, elem_of_dom.
    by exists St.
  Qed.

  Lemma kvs_snapshots_included_delete t St k M S :
    kvs_snapshots_included M S →
    S !! t = Some St →
    kvs_snapshots_included (delete k M) {[t := delete k St]}.
  Proof.
    move=>included /included[dom_eq hist_included] t' Mt/lookup_singleton_Some[_ <-].
    split; first set_solver.
    move=>k' h1/lookup_delete_Some[k_k']/hist_included[h2][M_k' h1_h2].
    exists h2.
    split; last done.
    by apply lookup_delete_Some.
  Qed.

  Lemma kvs_snapshots_cuts_delete t St k M S :
    kvs_snapshots_cuts M S →
    S !! t = Some St →
    kvs_snapshots_cuts (delete k M) {[t := delete k St]}.
  Proof.
    by move=>/[apply] cuts t' k' h_snap h_curr Mt/lookup_singleton_Some[<-]<-
      /lookup_delete_Some[_]/cuts cuts'/lookup_delete_Some[_]/cuts'.
  Qed.

  (** A system step updating the memory with the effect of commit 
      of a transaction is valid *)
  Lemma kvs_valid_update M S T (cache : gmap Key SerializableVal) :
    dom cache ⊆ KVS_keys →
    kvs_valid M S T →
    kvs_valid (update_kvs M cache (T+1)) S (T+1).
  Proof.
    move=> dom_incl [dom_eq whists_valid keys_valid commit_times time_valid
        snapshots_incl cuts].
    split.
    - by rewrite /kvs_dom upd_dom -dom_eq.
    - move=>k h/lookup_update_kvs_Some[[cache_k /whists_valid]|[h'][v][M_k][cache_k]->];
        first done.
      destruct (whists_valid _ _ M_k) as (keys, times, vals, ext).
      split.
      + by move=>we/elem_of_app[/(keys_valid _ _ M_k) ->|/elem_of_list_singleton->/=];
        rewrite dom_eq; apply elem_of_dom; rewrite M_k.
      + move=>ei ej i j ij/lookup_snoc_Some[[_ h'_i]|[eqi]];
          last by rewrite (lookup_ge_None_2 _ j); [|rewrite app_length -eqi/=; lia].
        move=>/lookup_snoc_Some[[_ h'_j]|[_ <-/=]];
          first by apply (times _ _ i j).
        move: (commit_times k h' M_k ei (elem_of_list_lookup_2 _ _ _ h'_i)).
        lia.
      + by move=>we/elem_of_app[/vals|/elem_of_list_singleton->]; last apply _.
      + move=>we we'/elem_of_app[we_h'|/elem_of_list_singleton->]/elem_of_app
          [we'_h'|/elem_of_list_singleton->]; [by apply ext|simpl..|done].
        move: (commit_times _ _ M_k _ we_h'). lia.
        move: (commit_times _ _ M_k _ we'_h'). lia.
    - move=>k h/lookup_update_kvs_Some[[cache_k M_k]|[h'][v][M_k][cache_k]->] we;
        first by apply keys_valid.
      by move=>/elem_of_app[/(keys_valid _ _ M_k)|/elem_of_list_singleton->].
    - move=>k h/lookup_update_kvs_Some[[cache_k M_k]|
          [h'][v][M_k][cache_k]->] we; first (move=>/(commit_times _ _ M_k); lia).
      move=>/elem_of_app[/(commit_times _ _ M_k)|/elem_of_list_singleton->/=]; lia.
    - move=>t/time_valid. lia.
    - move=>t Mt S_t.
      move: (snapshots_incl _ _ S_t)=>[Mt_M incl].
      split; first by rewrite upd_dom ?Mt_M -dom_eq.
      move=>k h1 Mt_k.
      move: (incl k h1 Mt_k)=>{incl} [h2][M_k h1_h2].
      set o := cache !! k.
      case cache_k : o=>[v|]; rewrite/o in cache_k=>{o}.
      + exists (h2 ++ [{|we_key := k; we_val := v;
              we_time := ((T+1)%nat : int_time.(Time))|}]).
        split; last by apply prefix_app_r.
        apply lookup_update_kvs_Some.
        right.
        by exists h2, v.
      + exists h2.
        split; last done.
        apply lookup_update_kvs_Some.
        by left.
    - move=>t k h_snap h_curr Mt S_t Mt_k/lookup_update_kvs_Some[[cache_k M_k]|
          [h'][v][M_k][cache_k]->];
      move:(cuts _ _ _ _ _ S_t Mt_k M_k)=>[h_after][->][before_t after_t].
      + by exists h_after.
      + exists (h_after ++ [{|we_key := k; we_val := v;
              we_time := ((T+1)%nat : int_time.(Time))|}]).
        split; first by rewrite app_assoc.
        split; first done.
        move=>we /elem_of_app[/after_t|/elem_of_list_singleton->/=]; first done.
        generalize (elem_of_dom_2 _ _ _ S_t)=>/time_valid. lia.
  Qed.

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

  Lemma kvsl_in_local_some' m M S T k h :
    kvsl_valid m M S T →
    m !! k = Some h →
    ∃ h', h = $ h' ∧ M !! k = Some (reverse h').
  Proof.
    move=>[dom_m model_empty model_some local [dom_M _ _ _ _ _ _]].
    case M_k : (M !! k)=>[h'|].
    - move: h' M_k=>[|we h'].
      + by move=>/model_empty->.
      + move=>M_k m_k.
        rewrite (model_some _ _ M_k) in m_k; last done.
        move: m_k =>[]<-.
        exists (reverse (we :: h')).
        by rewrite reverse_involutive.
    - move=>m_k.
      apply not_elem_of_dom in M_k.
      exfalso; apply M_k.
      rewrite -dom_M.
      apply elem_of_dom_2 in m_k.
      set_solver.
  Qed.

  Lemma kvsl_in_local_empty m M S T k :
    kvsl_valid m M S T →
    m !! k = None →
    k ∈ KVS_keys →
    M !! k = Some [].
  Proof.
    move=>[_ model_empty model_some local [dom_M _ _ _ _ _ _]].
    case M_k : (M !! k)=>[[//|we h]|].
    - apply model_some in M_k.
      by rewrite M_k.
    - apply not_elem_of_dom in M_k.
      by rewrite -dom_M in M_k.
  Qed.

 Definition update_kvsl
    (m : gmap Key val)
    (C : gmap Key SerializableVal)
    (T : nat) : gmap Key val :=
    fn_to_gmap (dom m ∪ dom C) (λ k,
      let h := default NONEV (m !! k) in
      match C !! k with
        | None => h
        | Some v => SOMEV ($(k, (v.(SV_val), T)), h)
      end).

  Lemma update_kvsl_dom m C T :
    dom (update_kvsl m C T) = dom m ∪ dom C.
  Proof.
    by rewrite fn_to_gmap_dom.
  Qed.

  Lemma lookup_update_kvsl_Some m C T k h :
    update_kvsl m C T !! k = Some h ↔
    (C !! k = None ∧ m !! k = Some h) ∨
    (∃ v, C !! k = Some v ∧ m !! k = None ∧ h = SOMEV ($(k, (v.(SV_val), T)), NONEV)) ∨
    (∃ h' v, C !! k = Some v ∧ m !! k = Some h' ∧
      h = SOMEV ($(k, (v.(SV_val), T)), h')).
  Proof.
    split.
    - move=>/lookup_fn_to_gmap[]/[swap]/elem_of_union[]/elem_of_dom.
      + move=>[h']->.
        case C_k : (C !! k)=>[v|]/=<-.
        * right. right. by exists h', v.
        * by left.
      + move=>[v]->.
        case m_k : (m !! k)=>[h'|]/=<-.
        * right. right. by exists h', v.
        * right. left. by exists v.
    - move=>[[C_k m_k]|[[v][C_k][m_k]->|[h'][v][C_k][m_k]->]].
      all: apply lookup_fn_to_gmap.
      all: rewrite C_k m_k.
      all: split; first done.
      1, 3: apply elem_of_dom_2 in m_k.
      3: apply elem_of_dom_2 in C_k.
      all: set_solver.
  Qed.

  Lemma lookup_update_kvsl_None m C T k :
    update_kvsl m C T !! k = None ↔ C !! k = None ∧ m !! k = None.
  Proof.
    split.
    - by move=>/lookup_fn_to_gmap_not_in/not_elem_of_union[/not_elem_of_dom m_k]
        /not_elem_of_dom C_k.
    - move=>[/not_elem_of_dom C_k]/not_elem_of_dom m_k.
      apply lookup_fn_to_gmap_not_in.
      set_solver.
  Qed.

  Lemma update_kvsl_empty m T :
    update_kvsl m ∅ T = m.
  Proof.
    apply map_eq=>k.
    case m_k : (m !! k)=>[h|].
    - apply lookup_update_kvsl_Some.
      by left.
    - by apply lookup_update_kvsl_None.
  Qed.

  Lemma upadte_kvsl_insert_Some m C T k v h :
    m !! k = Some h →
    update_kvsl m (<[k := v]> C) T =
      <[k := SOMEV ($(k, (v.(SV_val), T)), h)]> (update_kvsl m C T).
  Proof.
    move=>m_k.
    apply map_eq=>k'.
    case (string_eq_dec k k')=>[<-|neq].
    {
      rewrite lookup_insert.
      apply lookup_update_kvsl_Some.
      right. right.
      erewrite lookup_insert.
      eauto.
    }
    rewrite lookup_insert_ne; last done.
    set C_k'_ := C !! k'.
    case C_k' : C_k'_=>[v'|]; rewrite /C_k'_ in C_k'=>{C_k'_};
    set m_k'_ := m !! k';
    case m_k' : m_k'_=>[h'|]; rewrite /m_k'_ in m_k'=>{m_k'_}.
    - erewrite (proj2 (lookup_update_kvsl_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvsl_Some. right. right. eauto. }
      right. right. by erewrite lookup_insert_ne; first eauto.
    - erewrite (proj2 (lookup_update_kvsl_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvsl_Some. right. left. eauto. }
      right. left. by erewrite lookup_insert_ne; first eauto.
    - erewrite (proj2 (lookup_update_kvsl_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvsl_Some. left. eauto. }
      left. by erewrite lookup_insert_ne; first eauto.
    - rewrite (proj2 (lookup_update_kvsl_None _ _ _ _));
        last by rewrite lookup_insert_ne.
      by apply eq_sym, lookup_update_kvsl_None.
  Qed.

  Lemma update_kvsl_insert_None m C T k v :
    m !! k = None →
    update_kvsl m (<[k := v]> C) T = 
      <[k := SOMEV ($(k, (v.(SV_val), T)), NONEV)]> (update_kvsl m C T).
  Proof.
    move=>m_k.
    apply map_eq=>k'.
    case (string_eq_dec k k')=>[<-|neq].
    {
      rewrite lookup_insert.
      apply lookup_update_kvsl_Some.
      right. left. erewrite lookup_insert.
      eauto.
    }
    rewrite lookup_insert_ne; last done.
    set C_k'_ := C !! k'.
    case C_k' : C_k'_=>[v'|]; rewrite /C_k'_ in C_k'=>{C_k'_};
    set m_k'_ := m !! k';
    case m_k' : m_k'_=>[h'|]; rewrite /m_k'_ in m_k'=>{m_k'_}.
    - erewrite (proj2 (lookup_update_kvsl_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvsl_Some. right. right. eauto. }
      right. right. by erewrite lookup_insert_ne; first eauto.
    - erewrite (proj2 (lookup_update_kvsl_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvsl_Some. right. left. eauto. }
      right. left. by erewrite lookup_insert_ne; first eauto.
    - erewrite (proj2 (lookup_update_kvsl_Some _ _ _ _ _)).
      { apply eq_sym, lookup_update_kvsl_Some. left. eauto. }
      left. by erewrite lookup_insert_ne; first eauto.
    - rewrite (proj2 (lookup_update_kvsl_None _ _ _ _));
        last by rewrite lookup_insert_ne.
      by apply eq_sym, lookup_update_kvsl_None.
  Qed.

  Lemma kvsl_model_empty_delete m M k :
    kvsl_in_model_empty_coh m M →
    kvsl_in_model_empty_coh m (delete k M).
  Proof.
    by move=>coh i /lookup_delete_Some[_]/coh.
  Qed.

  Lemma kvsl_model_some_delete m M k :
    kvsl_in_model_some_coh m M →
    kvsl_in_model_some_coh m (delete k M).
  Proof.
    by move=>coh i h /lookup_delete_Some[_]/coh.
  Qed.

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
    move=>dom_cache [dom_m model_empty model_some local_some valid].
    split.
    - rewrite /kvsl_dom update_kvsl_dom. set_solver.
    - move=>k/lookup_update_kvs_Some[[cache_k M_k]|[h][v][M_k][cache_k]abs];
        last by (apply eq_sym, app_nil in abs; destruct abs).
      apply lookup_update_kvsl_None.
      split; first done.
      by apply model_empty.
    - move=>k h/lookup_update_kvs_Some[[cache_k M_k] neq|[h'][v][M_k][cache_k]->_].
      + apply lookup_update_kvsl_Some.
        left.
        split; first done.
        by apply model_some.
      + apply lookup_update_kvsl_Some.
        right.
        move:h' M_k=>[|we h'] M_k.
        * left.
          exists v.
          split; first done.
          split; last done.
          by apply model_empty.
        * right.
          exists $(reverse (we::h')), v.
          split; first done.
          split; first by apply model_some.
          by rewrite reverse_snoc.
    - move=>k h/lookup_update_kvsl_Some[[cache_k m_k]|[[v]|[h'][v]][cache_k][m_k]eq_h];
        apply lookup_update_kvs_Some.
      + left.
        split; first done.
        by apply local_some.
      + right.
        exists [], v.
        split; first by apply (kvsl_in_local_empty m M Mts T k);
            last (apply elem_of_dom_2 in cache_k; set_solver).
        split; first done.
        rewrite -(reverse_involutive (_ ++ _)).
        f_equal.
        apply (inj inject).
        by rewrite eq_h.
      + right.
        apply (kvsl_in_local_some' m M Mts T) in m_k; last done.
        destruct m_k as [h'' [eq M_k]].
        exists (reverse h''), v.
        split; first done.
        split; first done.
        rewrite -(reverse_involutive (_ ++ _)) reverse_snoc reverse_involutive.
        f_equal.
        apply (inj inject).
        by rewrite eq_h eq.
    - by apply kvs_valid_update.
  Qed.

  (** Used for start *)
  Lemma kvsl_valid_next M S (m : gmap Key val) T :
    kvsl_valid m M S T →
    kvsl_valid m M (<[(T+1)%nat := M]>S) (T + 1).
  Proof.
    move=>[dom_m empty_coh model_coh local_coh valid].
    split; [done..|exact: kvs_valid_step_start_transaction].
  Qed.

End KVSL_valid.

  Definition kvs_valid_snapshot
    (Msnap : global_mem) (t : nat) :=
    (* dom Msnap ⊆ KVS_keys ∧ *)
    (* kvs_whists Msnap ∧ *)
    (* kvs_keys Msnap ∧ *)
    ∀ k h, Msnap !! k = Some h → ∀ e, e ∈ h → e.(we_time) < t.