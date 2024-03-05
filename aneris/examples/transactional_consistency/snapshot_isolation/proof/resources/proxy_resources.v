From iris.algebra Require Import
     agree auth excl gmap frac_auth excl_auth updates local_updates csum.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.mt_server Require Import
  user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof Require Import
  model kvs_serialization utils.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources Require Import
  server_resources.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.

Import gen_heap_light.

Inductive proxy_state : Type :=
| PSCanStart
| PSActive of global_mem.

Section Proxy.
  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ, !MTS_resources }.
  (** Those are ghost names allocated before resources are instantiated. *)
  Context (γGsnap γT γTrs : gname).
  Context (γKnownClients : gname).

  Definition ownMsnapAuth γ (M : gmap Key (list write_event)) : iProp Σ :=
    ghost_map_auth γ (1/2)%Qp M ∗ [∗ map] k ↦ h ∈ M, ghost_map_elem γ k (DfracOwn 1%Qp) h.

  Definition ownMsnapFrag γ (M : gmap Key (list write_event)) : iProp Σ :=
    ghost_map_auth γ (1/2)%Qp M.

  Definition ownMsnapFull γ : iProp Σ :=
    ghost_map_auth γ 1%Qp ∅.

  Definition client_gnames_token_defined γCst γ1 γ2 γ3 γ4 γ5 : iProp Σ
    := own γCst (Cinr (to_agree (γ1, γ2, γ3, γ4, γ5))).

  Definition client_gnames_token_pending γCst : iProp Σ
    := own γCst (Cinl (Excl ())).

  Definition CanStartToken (γS : gname) : iProp Σ := own γS (Excl ()).
  Definition isActiveToken (γA : gname) : iProp Σ := own γA (Excl ()).

  Definition is_coherent_cache
    (cache_updatesM : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap :  gmap Key (list write_event)) :=
      dom cache_logicalM = dom Msnap ∧
      dom cache_updatesM ⊆ dom cache_logicalM ∧
      dom cache_updatesM ⊆ KVS_keys ∧
      (** Cache Logical and Snapshot Coherence *)
      (∀ k v,
        (cache_logicalM !! k) = Some (Some v, false) →
        ∃ h e,
          Msnap !! k = Some h ∧
          hist_to_we h = Some e ∧
          e.(we_val) = v) ∧
      (∀ k,
          (cache_logicalM !! k) = Some (None, false) →
          Msnap !! k = Some []) ∧
      (** Cache Logical and Cache Updates Coherence *)
      (∀ k v,
        cache_updatesM !! k = Some v ↔
        cache_logicalM !! k = Some (Some v, true)) ∧
        (∀ k vo,
           k ∈ dom Msnap →
           vo = from_option
                  (λ h, (from_option
                           (λ we : events.write_event,
                               Some (we_val we)) None (last h)))
                  None (Msnap !! k) →
           (cache_updatesM !! k) = None ↔
            cache_logicalM !! k = Some (vo, false)) ∧
       (∀ k vo, (cache_logicalM !! k = Some (vo, true)) → is_Some vo).

  Lemma is_coherent_cache_upd k v cuM cM Msnap :
    k ∈ KVS_keys →
    is_Some (cM !! k) →
    is_coherent_cache cuM cM Msnap →
    is_coherent_cache (<[k:=v]> cuM) (<[k:=(Some v, true)]> cM) Msnap.
  Proof.
    intros H_in H_some
      (H_coh_1 & H_coh_2 & H_coh_3 & H_coh_4 &
       H_coh_5 & H_coh_6 & H_coh_7 & H_coh_8).
    unfold is_coherent_cache.
    split.
    - rewrite -H_coh_1.
      by apply dom_insert_lookup_L.
    - split.
      + set_solver.
      + split.
        * set_solver.
        * split.
          -- intros k' v' H_lookup.
              destruct (decide (k = k')) as [<- | H_neq].
              {
                by rewrite lookup_insert in H_lookup.
              }
              {
                apply H_coh_4.
                apply (lookup_insert_ne cM _ _ (Some v, true)) in H_neq.
                by rewrite H_neq in H_lookup.
              }
          -- split.
              ++ intros k' H_lookup.
                destruct (decide (k = k')) as [<- | H_neq].
                {
                  by rewrite lookup_insert in H_lookup.
                }
                {
                  apply H_coh_5.
                  apply (lookup_insert_ne cM _ _ (Some v, true)) in H_neq.
                  by rewrite H_neq in H_lookup.
                }
              ++ split.
                ** intros k' v'.
                   split; intro H_lookup.
                    --- destruct (decide (k = k')) as [<- | H_neq].
                    {
                      rewrite lookup_insert in H_lookup.
                      rewrite lookup_insert.
                      by rewrite H_lookup.
                    }
                    {
                      apply (lookup_insert_ne cuM _ _ v) in H_neq as H_neq'.
                      rewrite H_neq' in H_lookup.
                      apply H_coh_6 in H_lookup.
                      rewrite -H_lookup.
                      by apply lookup_insert_ne.
                    }
                    --- destruct (decide (k = k')) as [<- | H_neq].
                    {
                      rewrite lookup_insert in H_lookup.
                      rewrite lookup_insert.
                      set_solver.
                    }
                    {
                      apply (lookup_insert_ne cM _ _ ((Some v, true))) in H_neq as H_neq'.
                      rewrite H_neq' in H_lookup.
                      apply H_coh_6 in H_lookup.
                      rewrite -H_lookup.
                      by apply lookup_insert_ne.
                    }
                ** split.
                  --- intros k' vo Hdom Hvo.
                      split.
                      { intros Hupd.
                        destruct (decide (k = k')) as [<- | H_neq].
                        {
                          by rewrite lookup_insert in Hupd. }
                        {
                          apply (lookup_insert_ne cuM _ _ v) in H_neq as H_neq'.
                          rewrite H_neq' in Hupd.
                          rewrite lookup_insert_ne; last done.
                          specialize (H_coh_7 k' vo Hdom Hvo) as (H_coh_7 & ?).
                          by apply H_coh_7. }
                      }
                      intros Hupd.
                      destruct (decide (k = k')) as [<- | H_neq].
                      {
                        by rewrite lookup_insert in Hupd. }
                      {
                        apply (lookup_insert_ne cuM _ _ v) in H_neq as H_neq'.
                        rewrite H_neq'.
                        specialize (H_coh_7 k' vo Hdom Hvo) as (Hcoh & H_coh_7).
                        apply H_coh_7.
                        by rewrite lookup_insert_ne in Hupd.
                      }
                  --- intros k' vo' Hvo.
                      destruct (decide (k = k')) as [<- | H_neq].
                      {
                        rewrite lookup_insert in Hvo. by simplify_eq /=. 
                      }
                      {
                        rewrite lookup_insert_ne in Hvo; last done.
                        by apply (H_coh_8 k').
                      }
  Qed.

  Lemma is_coherent_cache_delete k cuM cM Msnap :
    is_coherent_cache cuM cM Msnap →
    is_coherent_cache (delete k cuM) (delete k cM) (delete k Msnap).
  Proof.
    intros [H_coh_1 [H_coh_2 [H_coh_3 [H_coh_4 [H_coh_5 [H_coh_6 [H_coh_7 H_coh_8]]]]]]].
    unfold is_coherent_cache.
    split; first set_solver.
    split; first set_solver.
    split; first set_solver.
    split.
    - intros k' v' H_lookup.
        destruct (decide (k = k')) as [<- | H_neq].
        {
          by rewrite lookup_delete in H_lookup. 
        }
        {
          rewrite lookup_delete_ne in H_lookup; last done.
          rewrite lookup_delete_ne; last done.
          by apply H_coh_4.
        }
    - split.
        + intros k' H_lookup.
          destruct (decide (k = k')) as [<- | H_neq].
          {
            by rewrite lookup_delete in H_lookup.
          }
          {
            rewrite lookup_delete_ne in H_lookup; last done.
            rewrite lookup_delete_ne; last done.
            by apply H_coh_5.
          }
        + split.
          * intros k' v'.
            split; intro H_lookup.
              -- destruct (decide (k = k')) as [<- | H_neq].
              {
                by rewrite lookup_delete in H_lookup.
              }
              {
                rewrite lookup_delete_ne in H_lookup; last done.
                rewrite lookup_delete_ne; last done.
                by apply H_coh_6.
              }
              -- destruct (decide (k = k')) as [<- | H_neq].
              {
                by rewrite lookup_delete in H_lookup.
              }
              {
                rewrite lookup_delete_ne in H_lookup; last done.
                rewrite lookup_delete_ne; last done.
                by apply H_coh_6.
              }
          * split.
            -- intros k' vo Hdom Hvo.
               split.
               { 
                 intros Hupd.
                 destruct (decide (k = k')) as [<- | H_neq].
                 {
                   set_solver.
                 }
                 {
                  rewrite lookup_delete_ne in Hvo; last done.
                  rewrite lookup_delete_ne in Hupd; last done.
                  rewrite lookup_delete_ne; last done.
                  apply H_coh_7; try done.
                  set_solver.
                 }
                }
                intros Hupd.
                destruct (decide (k = k')) as [<- | H_neq].
                {
                  set_solver.
                }
                {
                  rewrite lookup_delete_ne in Hvo; last done.
                  rewrite lookup_delete_ne in Hupd; last done.
                  rewrite lookup_delete_ne; last done.
                  eapply H_coh_7; try done.
                  set_solver.
                }
            -- intros k' vo' Hvo.
                destruct (decide (k = k')) as [<- | H_neq].
                {
                  by rewrite lookup_delete in Hvo.
                }
                {
                  rewrite lookup_delete_ne in Hvo; last done.
                  by apply (H_coh_8 k'). 
                }
  Qed.

  Definition cacheM_from_Msnap (M : gmap Key (list write_event))
    : gmap Key (option val * bool) :=
    (λ h : list events.write_event,
        (from_option (λ we : events.write_event,
               Some (we_val we)) None (last h), false)) <$> M.

  Lemma is_coherent_cache_start M :
    is_coherent_cache ∅ (cacheM_from_Msnap M) M.
  Proof.
    split.
      - unfold cacheM_from_Msnap.
        by rewrite dom_fmap_L.
      - split.
        + by rewrite dom_empty_L.
        + split.
          * by rewrite dom_empty_L.
          * split.
            -- intros k v Hyp.
               unfold cacheM_from_Msnap in Hyp.
               rewrite lookup_fmap in Hyp.
               destruct (M !! k) eqn:H_lookup.
               {
                 inversion Hyp as [Hyp'].
                 exists l.
                 destruct l.
                 1 : done.
                 assert (w :: l ≠ []) as H_neq.
                 { set_solver. }
                 apply last_of_none_empty_list_is_some in H_neq as H_eq.
                 destruct H_eq as [v' H_eq]. 
                 exists v'. split; first done.
                 simpl in *.
                 rewrite H_eq.
                 split; first done.
                 rewrite -H_eq in Hyp'.
                 simpl in Hyp'.
                 set_solver.
               }
               {
                by inversion Hyp.
               }
            -- split.
              ++ intros k Hyp.
                unfold cacheM_from_Msnap in Hyp.
                rewrite lookup_fmap in Hyp.
                destruct (M !! k) eqn:H_lookup.
                {
                  simpl in Hyp.
                  inversion Hyp as [Hyp'].
                  destruct l.
                  1 : done.
                  assert (w :: l ≠ []) as H_neq.
                  { set_solver. }
                  apply last_of_none_empty_list_is_some in H_neq as H_eq.
                  destruct H_eq as [v H_eq].
                  rewrite -H_eq in Hyp.
                  by simpl in Hyp.
                }
                {
                  by inversion Hyp.
                }
              ++ split.
                ** split.
                  1: set_solver.
                  intros Hyp.
                  unfold cacheM_from_Msnap in Hyp.
                  rewrite lookup_fmap in Hyp.
                  destruct (M !! k) eqn:H_lookup;
                  inversion Hyp.
                ** split.
                  --- intros k vo Hdom Hvo.
                      split; last done.
                      1: intros Hyp.
                      simplify_eq /=.
                      rewrite /cacheM_from_Msnap.
                      rewrite! lookup_fmap.
                      destruct (M !! k) eqn:H_lookup.
                      { simpl. by do 2 f_equal. }
                      { rewrite elem_of_dom in Hdom.
                        rewrite H_lookup in Hdom. rewrite /is_Some in Hdom. set_solver. }
                  --- intros k vo Hvo.
                      rewrite /cacheM_from_Msnap in Hvo.
                      destruct vo; first done.
                      rewrite! lookup_fmap in Hvo.
                      by destruct (M !! k) eqn:H_lookup. 
  Qed.

  Definition is_connected_def
             (n : ip_address) (cst : val) (l : loc)
    (γS γA γCache γMsnap : gname) : iProp Σ :=
    ∃ (sv : val),
      l ↦[n] sv ∗
      MTSCanRequest n cst ∗
      (
        (** If no active transaction is running on the connection: *)
        (⌜sv = NONEV⌝ ∗
            (** then the lock has start token and guards an empty logical cache map. *)
         ghost_map_auth γCache 1 (∅ : gmap Key (option val * bool)) ∗
         ownMsnapFull γMsnap ∗
         CanStartToken γS) ∨
        (** Or an active transaction is running: *)
          (∃ (ts : nat) (Msnap Msnap_full : gmap Key (list write_event))
           (cache_updatesL : loc)
           (cache_updatesV : val)
           (cache_updatesM : gmap Key val)
           (cacheM : gmap Key (option val * bool)),
            ⌜sv = SOMEV (#ts, #cache_updatesL)⌝ ∗
            (** then lock has active token and guards a logical cache map
                whose domain is equal to the one of the snapshot. *)
            ⌜is_coherent_cache cache_updatesM cacheM Msnap⌝ ∗
            ⌜map_Forall (λ k v, KVS_Serializable v) cache_updatesM⌝ ∗
            ⌜kvs_valid_snapshot Msnap ts⌝ ∗
            ⌜is_map cache_updatesV cache_updatesM⌝ ∗
            ⌜Msnap ⊆ Msnap_full⌝ ∗
            ownTimeSnap γT ts ∗
            ([∗ map] k ↦ h ∈ Msnap, ownMemSeen γGsnap k h) ∗
            ownSnapFrag γTrs ts Msnap_full ∗
            cache_updatesL ↦[n] cache_updatesV ∗
            ghost_map_auth γCache 1 cacheM ∗
            ownMsnapAuth γMsnap Msnap ∗
            isActiveToken γA)).
  
  Notation connection_token sa γCst := (connected_client_token γKnownClients sa γCst).

  Definition client_can_connect sa : iProp Σ :=
   ∃ γCst, connection_token sa γCst ∗ client_gnames_token_pending γCst.

  Definition client_connected sa γCst γCache γlk γA γS γMsnap : iProp Σ :=
   connection_token sa γCst ∗ client_gnames_token_defined γCst γCache γlk γA γS γMsnap.

  Definition is_connected (c : val) (sa : socket_address)
    : iProp Σ :=
    ∃ (lk : val) (cst : val) (l : loc)
      (γCst γlk γS γA γCache γMsnap : gname),
      ⌜c = (#sa, (lk, (cst, #l)))%V⌝ ∗
      client_connected sa γCst γA γS γlk γCache γMsnap ∗
      is_lock (KVS_InvName .@ (socket_address_to_str sa)) (ip_of_address sa) γlk lk
              (is_connected_def (ip_of_address sa) cst l γS γA γCache γMsnap).

  Lemma connection_state_gen_persistent c sa : Persistent (is_connected c sa).
  Proof. apply _. Qed.

  (** Tokens forbid the connection state to be duplicable and so
      prohibit concurrent use of start/commit operations which would
      make the use of the library inconsistent because one should not
      run start and commit in parallel, only reads and/or writes. *)
 Definition connection_state (c : val) (sa : socket_address) (s : proxy_state) : iProp Σ :=
   ∃ (v : val) (γCst γA γS γlk γCache γMsnap : gnameO),
     ⌜c = (#sa, v)%V⌝ ∗
     client_connected sa γCst γA γS γlk γCache γMsnap ∗
       match s with
       | PSCanStart => isActiveToken γA
       | PSActive Msnap =>
           CanStartToken γS ∗
           ([∗ map] k ↦ h ∈ Msnap, ownMemSeen γGsnap k h) ∗
           ownMsnapFrag γMsnap Msnap
       end.


 (** Having a cache pointer guarantees that the connection state is in active
  mode because the domain of the cache map cannot be empty by agreement on
  ghost map. *)
  Definition ownCacheUser (k : Key) (c : val) (vo : option val) : iProp Σ :=
    ∃ (sa : socket_address) (v: val)
      (γCst γA γS γlk γCache γMsnap : gname) (b : bool),
      ⌜c = (#sa, v)%V⌝ ∗
      client_connected sa γCst γA γS γlk γCache γMsnap ∗
      ghost_map_elem γCache k (DfracOwn (1/2)%Qp) (vo, b) ∗
      ⌜match vo with
       | None => b = false
       | Some w => KVS_Serializable w
       end⌝.

  Lemma ownCacheUser_timeless k c vo : Timeless (ownCacheUser k c vo).
  Proof. apply _. Qed.

 (** To update cache pointers, one need to change the update status of the key.
  This is enforced by giving half of the pointer permission to the cache pointer
  the other half to the key_upd_status predicate. *)
  Definition key_upd_status (c : val) (k : Key) (b : bool) : iProp Σ :=
    ∃ (sa : socket_address) (vp : val) (γCst γA γS γlk γCache γMsnap : gname)
      (vo : option val),
      ⌜c = (#sa, vp)%V⌝ ∗
      client_connected sa γCst γA γS γlk γCache γMsnap ∗
      ghost_map_elem γCache k (DfracOwn (1/2)%Qp) (vo, b) ∗
      (⌜b = true → is_Some vo⌝).


  Lemma own_cache_user_serializable k cst v :
     ownCacheUser k cst (Some v) -∗
     ownCacheUser k cst (Some v) ∗ ⌜KVS_Serializable v⌝.
  Proof.
    iIntros "[%sa [%v' [%γCst [%γA [%γS [%γlk [%γCache [%γMsnap [%b
    (H_eq & H_cli & H_key & %H_ser)]]]]]]]]]".
    iSplit.
    2 : { by iPureIntro. }
    iExists _, _, _, _, _, _, _, _.
    iFrame.
    iExists _. iFrame. by iPureIntro.
  Qed.

  Lemma client_connected_agree :
  ∀ sa γCst γA γS γlk γCache γMsnap γCst' γA' γS' γlk' γCache' γMsnap',
  client_connected sa γCst γCache γlk γA γS γMsnap -∗
  client_connected sa γCst' γCache' γlk' γA' γS' γMsnap' -∗
  ⌜(γCst, γA, γS, γlk, γCache, γMsnap) = (γCst', γA', γS', γlk', γCache', γMsnap')⌝.
  Proof.
    iIntros (sa γCst γA γS γlk γCache γMsnap γCst' γA' γS' γlk' γCache' γMsnap')
            "(H_sa & H_cst) (H_sa' & H_cst')".
    unfold client_gnames_token_defined.
    unfold connection_token.
    iAssert (⌜γCst = γCst'⌝%I) as %H_eq_cst.
    {
      iDestruct (own_valid_2 with "H_sa H_sa'") as "%H_sa_combined".
      iPureIntro.
      apply auth_frag_op_valid_1 in H_sa_combined.
      rewrite singleton_op in H_sa_combined.
      rewrite singleton_valid in H_sa_combined.
      by apply to_agree_op_valid_L in H_sa_combined.
    }
    rewrite -H_eq_cst.
    iDestruct (own_valid_2 with "H_cst H_cst'") as "H_cst_combined".
    rewrite -Cinr_op csum_validI.
    iDestruct "H_cst_combined" as "%H_cst_combined".
    iPureIntro.
    apply to_agree_op_valid_L in H_cst_combined.
    set_solver.
  Qed.

  Lemma own_cache_user_from_ghost_map_elem_big (M :gmap Key (list write_event)) :
    ∀ sa v γCst γA γS γlk γCache γMsnap,
    ⌜map_Forall (λ k l, Forall (λ we, KVS_Serializable (we_val we)) l) M⌝ -∗
    client_connected sa γCst γA γS γlk γCache γMsnap -∗
    ([∗ map] k↦hv ∈ cacheM_from_Msnap M, ghost_map.ghost_map_elem γCache k (DfracOwn 1) hv) -∗
    [∗ map] k↦hw ∈ ((λ hw : list write_event, to_hist hw) <$> M),
          ownCacheUser k (#sa, v)%V (last hw) ∗ key_upd_status (#sa, v)%V k false.
  Proof.
    iIntros (sa v γCst γA γS γlk γCache γMsnap) "%H_ser #H_cli H_map".
    iApply big_sepM_fmap.
    unfold ownCacheUser, key_upd_status.
    iApply (big_sepM_mono (λ k y,
      (∃ (γCst0 γA0 γS0 γlk0 : gname),
      client_connected sa γCst0 γA0 γS0 γlk0 γCache γMsnap) ∗
      (∃ (sa0 : socket_address) (v0 : val) (b : bool),
          ⌜(#sa, v)%V = (#sa0, v0)%V⌝ ∗
          ghost_map.ghost_map_elem γCache k (DfracOwn (1 / 2)) (last (to_hist y), b) ∗
          ⌜match last (to_hist y) with
            | Some w => KVS_Serializable w
            | None => b = false
            end⌝) ∗
      (∃ (sa0 : socket_address) (vp : val)
      (vo : option val),
          ⌜(#sa, v)%V = (#sa0, vp)%V⌝ ∗
          ghost_map.ghost_map_elem γCache k (DfracOwn (1 / 2)) (vo, false) ∗
          ⌜false = true → is_Some vo⌝))%I).
    - iIntros (k x H_eq) "(H_cli & H_cache & H_key)".
      iDestruct "H_cli" as "[%γCst0 [%γA0 [%γS0 [%γlk0 #H_cli]]]]".
      iSplitL "H_cache".
      + iDestruct "H_cache" as "[%sa' [%v' [%b (%H_eq_pair & H_key_half & H_ser)]]]".
        iExists _, _, _, _, _, _, _ , _.
        iExists _.
        iFrame "#∗".
        by iPureIntro.
      + iDestruct "H_key" as "[%sa' [%v' [%vo (%H_eq_pair & H_key_half & H_imp)]]]".
        iExists _, _, _, _, _, _, _, _.
        iExists _. iFrame "#∗".
        by iPureIntro.
      - iApply big_sepM_sep.
        iSplitR.
        + iApply big_sepM_dup; first set_solver.
          iExists _, _, _, _.
          iFrame "#".
        + unfold cacheM_from_Msnap.
          iDestruct ((big_sepM_fmap (λ h : list events.write_event,
                                      (from_option
                                        (λ we : events.write_event,
                                          Some (we_val we)) None (last h), false)))
                      with "H_map") as "H_map".
          iApply big_sepM_mono; last done.
          iIntros (k l H_eq) "H_key".
          assert (1%Qp = (1 / 2 + 1 / 2)%Qp) as H_eq_frac.
          { by rewrite Qp.div_2. }
          rewrite -> H_eq_frac at 1.
          iDestruct (ghost_map.ghost_map_elem_fractional with "H_key") as "[H_key H_key']".
          iSplitL "H_key".
          * iExists _, _, _.
            iSplit; first done.
            assert (last (to_hist l) = from_option
                                        (λ we : events.write_event,
                                        Some (we_val we)) None (last l))
            as ->.
            {
              clear H_eq.
              destruct l as [| h l]; first done.
              unfold to_hist.
              rewrite fmap_last.
              assert (h :: l ≠ []) as H_neq.
              { set_solver. }
              apply last_of_none_empty_list_is_some in H_neq as H_eq.
              destruct H_eq as [u H_eq].
              rewrite -H_eq.
              by simpl.
            }
            iSplitL; first done.
            iPureIntro.
            apply H_ser in H_eq.
            destruct (last l) eqn:H_eq_last; last done; simpl.
            apply last_in in H_eq_last.
            rewrite List.Forall_forall in H_eq.
            by apply H_eq in H_eq_last.
          * iExists _, _, _.
            iSplit; first done.
            iSplit; iFrame.
            iPureIntro; done.
   Qed.

End Proxy.
