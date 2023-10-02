From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.specs Require Import
  user_params time events aux_defs resource_algebras.
From aneris.examples.snapshot_isolation.proof
  Require Import model kvs_serialization
  rpc_user_params utils.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
Section Proof_of_commit_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT γTrs).
  Import snapshot_isolation_code_api.

  Lemma check_at_key_spec (k : Key) (ts tc : nat) (vl kvs cache : val)
    (cache_updatesM m : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap M : gmap Key (list write_event))
    (S Sg : snapshots) :
    kvsl_valid m M Sg tc →
    kvs_valid M S tc →
    S !! ts = Some Msnap →
    (match m !! k with
      | Some p => vl = $p
      | None => vl = InjLV #()
    end) → 
    {{{ ⌜True⌝ }}}
      check_at_key #k #ts #(tc + 1) vl @[ip_of_address MTC.(MTS_saddr)]
    {{{ (br : bool), RET #br;
      (⌜br = true⌝ ∗ ⌜M !! k = Msnap !! k⌝)
      ∨ (⌜br = false⌝ ∗ 
        ⌜∀ (v1 v2 : list write_event), M !! k = Some v1 → Msnap !! k = Some v2 → to_hist v1 ≠ to_hist v2⌝)
    }}}.
  Proof.
    iIntros (H_kvsl H_kvs H_lookup_snap H_match Φ) "_ HΦ".
    unfold check_at_key.
    unfold assert.
    wp_pures.
    case_bool_decide as H_le; last first.
    {
      assert (ts <= tc); last lia.
      assert (is_Some (S !! ts)) as H_some; first set_solver.
      rewrite -elem_of_dom in H_some.
      apply (kvs_ValidSnapshotTimesTime M S tc) in H_some; try done.
      lia.
    }
    wp_pures.
    destruct (m !! k) as [ p | ] eqn:H_lookup_m.
    - destruct (M !! k) as [ wl | ] eqn:H_lookup_M.
      + assert (m !! k = Some $(reverse wl)).
        {
          apply (kvsl_ValidInModelSome m M Sg tc); try done.
          destruct wl as [ | w wl]; last done.
          apply (kvsl_ValidInModelEmpty m M Sg tc) in H_lookup_M; last done.
          set_solver.
        }
        simpl in H_match.
        simplify_eq.
        simpl.
        destruct (reverse wl) as [ | rw rwl] eqn:H_reverse_wl.
        {
          exfalso.
          assert (reverse (reverse wl) = wl) as H_rev_rev_wl; first apply reverse_involutive.
          rewrite H_reverse_wl in H_rev_rev_wl.
          rewrite reverse_nil in H_rev_rev_wl.
          simplify_eq.
          apply (kvsl_ValidInModelEmpty m M Sg tc) in H_lookup_M; last done.
          set_solver.
        }
        simpl.
        wp_pures.
        assert (rw ∈ wl) as H_rw_in_wl.
        {
          apply elem_of_reverse.
          rewrite H_reverse_wl.
          set_solver.
        }
        case_bool_decide as H_leq.
        {
          exfalso.
          apply (kvs_ValidCommitTimes M S tc) in H_lookup_M; last done.
          apply (H_lookup_M rw) in H_rw_in_wl.
          lia.
        }
        wp_pures.
        case_bool_decide as H_eq.
        {
          exfalso.
          destruct (Msnap !! k) as [ wl' | ] eqn:H_lookup_Msnap.
          - eapply (kvs_ValidSnapshotTimesCuts M S tc) in H_lookup_snap; last done.
            destruct (H_lookup_snap H_lookup_Msnap H_lookup_M) as [h_after (H_wl_eq & H_times_le & H_times_gt)].
            rewrite H_wl_eq in H_rw_in_wl.
            apply elem_of_app in H_rw_in_wl as [H_in_first | H_in_last].
            + apply H_times_le in H_in_first.
              lia.
            + apply H_times_gt in H_in_last.
              lia.
          - apply (kvs_ValidSnapshotTimesInclusion M S tc) in H_lookup_snap as (H_dom_eq & _); last done.
            apply not_elem_of_dom in H_lookup_Msnap.
            assert (is_Some (M !! k)) as H_is_some_M; first done.
            apply elem_of_dom in H_is_some_M.
            set_solver.
        }
        wp_pures.
        case_bool_decide as H_le'; iApply "HΦ".
        * iLeft.
          iSplit; first done.
          iPureIntro.
          assert (wl = (reverse rwl) ++ [rw]) as ->.
          {
            rewrite -reverse_cons.
            rewrite -H_reverse_wl.
            by rewrite (reverse_involutive wl).
          }
          destruct (Msnap !! k) as [ wl' | ] eqn:H_lookup_Msnap.
          -- eapply (kvs_ValidSnapshotTimesCuts M S tc) in H_lookup_snap; last done.
             destruct (H_lookup_snap H_lookup_Msnap H_lookup_M) 
              as [h_after (H_wl_eq & H_times_le & H_times_gt)].
              destruct h_after as [| we h_after].
              ++ by rewrite H_wl_eq app_nil_r.
              ++ assert (rw ∈ we :: h_after) as H_rw_in; first by eapply list_later_in. 
                 apply H_times_gt in H_rw_in.
                 lia.
          -- apply (kvs_ValidSnapshotTimesInclusion M S tc) in H_lookup_snap as (H_dom_eq & _); last done.
            apply not_elem_of_dom in H_lookup_Msnap.
            assert (is_Some (M !! k)) as H_is_some_M; first done.
            apply elem_of_dom in H_is_some_M.
            set_solver.
        * iRight.
          iSplit; first done.
          iPureIntro.
          intros v1 v2 H_some_eq H_lookup_Msnap. 
          eapply (kvs_ValidSnapshotTimesCuts M S tc) in H_lookup_snap; last done.
          destruct (H_lookup_snap H_lookup_Msnap H_lookup_M)
          as [h_after (H_wl_eq & H_times_le & H_times_gt)].
          simplify_eq.
          intro H_abs.
          destruct h_after as [| we h_after]; first set_solver.
          unfold to_hist in H_abs.
          rewrite fmap_app in H_abs.
          rewrite <- (app_nil_r ((λ e : events.write_event, we_val e) <$> v2)) in H_abs at 2.
          by apply app_inv_head in H_abs.
      + exfalso.
        apply not_elem_of_dom in H_lookup_M.
        assert (is_Some (m !! k)) as H_is_some_m; first done.
        apply elem_of_dom in H_is_some_m.
        rewrite -(kvs_ValidDom M S tc) in H_lookup_M; last done.
        assert (dom m ⊆ KVS_keys) as H_subset_eq; last set_solver.
        apply (kvsl_ValidDom m M Sg tc); done.
    - simplify_eq.
      wp_pures.
      iApply "HΦ".
      iLeft.
      iSplit; first done.
      iPureIntro.
      destruct (M !! k) as [ wl | ] eqn:H_lookup_M.
      + destruct wl as [ | w wl].
        * assert (Msnap !! k = Some []); last done.
          apply (kvs_ValidSnapshotTimesInclusion M S tc) in H_lookup_snap; last done.
          destruct H_lookup_snap as (H_eq_dom & H_included).
          assert (k ∈ dom Msnap) as H_k_in_Msnap.
          {
            assert (is_Some (M !! k)) as H_is_some_M; first done.
            apply elem_of_dom in H_is_some_M.
            set_solver.
          }
          apply elem_of_dom in H_k_in_Msnap.
          destruct (Msnap !! k) as [ wl' | ] eqn:H_lookup_Msnap; 
            last by inversion H_k_in_Msnap.
          apply H_included in H_lookup_Msnap as [wl'' (H_lookup_M' & H_leq)].
          assert (wl'' = []) as -> .
          {
            rewrite H_lookup_M in H_lookup_M'.
            by inversion H_lookup_M'.
          }
          apply f_equal.
          destruct wl' as [ | w' wl']; first done.
          by inversion H_leq.
        * assert (m !! k = Some $(reverse (w :: wl))); last set_solver.
          apply (kvsl_ValidInModelSome m M Sg tc); done.
      + apply (kvs_ValidSnapshotTimesInclusion M S tc) in H_lookup_snap; last done.
        destruct H_lookup_snap as (H_eq_dom & H_included).
        assert (k ∉ dom Msnap) as H_k_nin_Msnap.
        {
          apply not_elem_of_dom in H_lookup_M.
          set_solver.
        }
        by apply not_elem_of_dom in H_k_nin_Msnap.
  Qed.

  Lemma can_not_do_commit M Msnap cache_logicalM k :
    (∃ vo : option val,
          cache_logicalM !! k =
          Some (vo, true)) → 
    (∀ v1 v2 : list write_event,
            M !! k = Some v1
            → Msnap !! k = Some v2
              → to_hist v1 ≠ to_hist v2) →
    k ∈ KVS_keys →
    k ∈ dom Msnap →
    ¬ can_commit
      ((λ hw : list write_event, to_hist hw) <$>
      filter
        (λ k : Key * list write_event,
            k.1 ∈ dom Msnap) M)
      ((λ hw : list write_event, to_hist hw) <$>
      Msnap) cache_logicalM.
  Proof.
    intros H_some H_neq H_in H_in' H_abs.
    unfold can_commit in H_abs.
    apply bool_decide_unpack in H_abs.
    specialize (H_abs k).
    destruct (cache_logicalM !! k) as [ p | ] eqn:H_lookup; 
      try by inversion H_some.
    specialize (H_abs H_in).
    inversion H_some as [vo H_eq].
    inversion H_eq as [H_p_eq].
    rewrite H_p_eq in H_abs.
    apply bool_decide_unpack in H_abs.
    do 2 rewrite lookup_fmap in H_abs.
    pose proof H_in' as H_k_some.
    rewrite elem_of_dom in H_k_some.
    apply lookup_lookup_total in H_k_some.
    rewrite H_k_some in H_abs.
    simpl in H_abs.
    destruct (M !! k) as [wl | ] eqn:H_lookup'.
    - rewrite (map_filter_lookup_Some_2 _ _ _ wl) in H_abs; try done.
      simpl in H_abs.
      specialize (H_neq wl (Msnap !!! k)).
      apply H_neq; try done.
      by inversion H_abs.
    - rewrite map_filter_lookup_None_2 in H_abs; try done.
      by left.
  Qed.

  Lemma can_do_commit (key : Key) (M Msnap : gmap Key (list write_event)) 
    (cache_logicalM : gmap Key (option val * bool)) :
    key ∈ dom Msnap →
    M !! key = Msnap !! key →
    can_commit
      ((λ hw : list write_event, to_hist hw) <$>
      filter (λ k : Key * list write_event, k.1 ∈ dom (delete key Msnap)) M)
      ((λ hw : list write_event, to_hist hw) <$> delete key Msnap)
      (delete key cache_logicalM) →
    can_commit
      ((λ hw : list write_event, to_hist hw) <$>
      filter (λ k : Key * list write_event, k.1 ∈ dom Msnap) M)
      ((λ hw : list write_event, to_hist hw) <$> Msnap) cache_logicalM.
  Proof.
    intros H_in_snap H_commit H_com_status.
    apply bool_decide_pack.
    intros k H_in_keys.
    apply bool_decide_unpack in H_com_status.
    destruct (decide (k = key)) as [<-| H_neq_k].
    - destruct (cache_logicalM !! k) as [p |]; last done.
      destruct p as [vo b].
      destruct b; last done.
      apply bool_decide_pack.
      pose proof H_in_snap as H_k_some.
      apply elem_of_dom in H_k_some.
      destruct (Msnap !! k) as [wl | ] eqn:H_lookup; last by inversion H_k_some.
      do 2 rewrite lookup_fmap.
      rewrite (map_filter_lookup_Some_2 _ _ _ wl); try done.
      by rewrite H_lookup.
    - specialize (H_com_status k H_in_keys).
      rewrite lookup_delete_ne in H_com_status; last done.
      destruct (cache_logicalM !! k) as [p |]; last done.
      destruct p as [vo b].
      destruct b; last done.
      apply bool_decide_pack.
      apply bool_decide_unpack in H_com_status.
      do 2 rewrite lookup_fmap.
      do 2 rewrite lookup_fmap in H_com_status.
      rewrite lookup_delete_ne in H_com_status; last done.
      destruct (M !! k) as [wl |] eqn:H_lookup'.
      + destruct (decide (k ∈ dom Msnap)) as [H_k_in_snap | H_k_nin_snap]; try done.
        * rewrite (map_filter_lookup_Some_2 _ _ _ wl); try done.
          rewrite (map_filter_lookup_Some_2 _ _ _ wl) in H_com_status; try done.
          set_solver.
        * rewrite map_filter_lookup_None_2.
          2 : right; set_solver. 
          rewrite map_filter_lookup_None_2 in H_com_status; first done.
          right; set_solver.
      + rewrite map_filter_lookup_None_2; last by left.
        by rewrite map_filter_lookup_None_2 in H_com_status; last by left.
  Qed.

  Lemma can_not_do_commit_delete (key : Key) (M Msnap : gmap Key (list write_event)) 
    (cache_logicalM : gmap Key (option val * bool)) :
    key ∈ dom Msnap →
    M !! key = Msnap !! key →
    ¬ can_commit
      ((λ hw : list write_event, to_hist hw) <$>
      filter (λ k : Key * list write_event, k.1 ∈ dom (delete key Msnap)) M)
      ((λ hw : list write_event, to_hist hw) <$> delete key Msnap)
      (delete key cache_logicalM) →
    ¬ can_commit
      ((λ hw : list write_event, to_hist hw) <$>
      filter (λ k : Key * list write_event, k.1 ∈ dom Msnap) M)
      ((λ hw : list write_event, to_hist hw) <$> Msnap) cache_logicalM.
  Proof.
    intros H_in_snap H_commit H_com_status.
    intros H_com_status'.
    apply H_com_status.
    unfold can_commit.
    apply bool_decide_pack.
    intros k H_k_in.
    apply bool_decide_unpack in H_com_status'.
    destruct (decide (k = key)) as [<-| H_neq_k].
    - by rewrite lookup_delete.
    - rewrite lookup_delete_ne; last done.
      specialize (H_com_status' k H_k_in).
      destruct (cache_logicalM !! k) as [p |]; last done.
      destruct p as [vo b].
      destruct b; last done.
      apply bool_decide_pack.
      apply bool_decide_unpack in H_com_status'.
      do 2 rewrite lookup_fmap.
      do 2 rewrite lookup_fmap in H_com_status'.
      rewrite lookup_delete_ne; last done.
      destruct (M !! k) as [wl |] eqn:H_lookup'.
      + destruct (decide (k ∈ dom Msnap)) as [H_k_in_snap | H_k_nin_snap]; try done.
        * rewrite (map_filter_lookup_Some_2 _ _ _ wl); try done.
          rewrite (map_filter_lookup_Some_2 _ _ _ wl) in H_com_status'; try done.
          set_solver.
        * rewrite map_filter_lookup_None_2.
          2 : right; set_solver. 
          rewrite map_filter_lookup_None_2 in H_com_status'; first done.
          right; set_solver. 
      + rewrite map_filter_lookup_None_2; last by left.
        by rewrite map_filter_lookup_None_2 in H_com_status'; last by left.
  Qed.

  Lemma map_forall_spec (ts tc : nat) (kvs cache : val) 
    (cache_updatesM m : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap M : gmap Key (list write_event)) 
    (S Sg : snapshots) :
    is_coherent_cache cache_updatesM cache_logicalM Msnap →
    is_map cache cache_updatesM →
    is_map kvs m →
    kvsl_valid m M Sg tc →
    kvs_valid M S tc →
    S !! ts = Some Msnap →
    {{{ ⌜True⌝ }}}
      map_forall (λ: "k" "_v",
                    let: "vlsto" := map_lookup "k" kvs in
                    let: "vs" := 
                      if: "vlsto" = InjL #()
                      then InjL #()
                      else network_util_code.unSOME "vlsto" 
                    in
                    check_at_key "k" #ts #(tc + 1) "vs")%V cache
                    @[ip_of_address MTC.(MTS_saddr)]
    {{{ (b : bool), RET #b; 
      (⌜b = true⌝ ∗ ⌜can_commit ((λ hw, to_hist hw) <$> filter (λ k, k.1 ∈ dom Msnap) M) 
                       ((λ hw, to_hist hw) <$> Msnap) cache_logicalM⌝) 
      ∨ (⌜b = false⌝ ∗ ⌜¬ can_commit ((λ hw, to_hist hw) <$> filter (λ k, k.1 ∈ dom Msnap) M)
                         ((λ hw, to_hist hw) <$> Msnap) cache_logicalM⌝) }}}.
  Proof.
    iIntros (H_coh H_map_cache H_map_kvs H_kvsl H_kvs H_lookup_snap Φ) "_ HΦ".
    iLöb as "IH" forall (cache cache_updatesM cache_logicalM Msnap S M m kvs H_map_kvs H_kvsl H_kvs H_coh H_map_cache H_lookup_snap).
    unfold map_forall.
    wp_pures.
    destruct H_map_cache as [l (H_eq_updates & H_eq_cache & H_dup)].
    destruct cache as [ abs | abs | abs | cache | cache ];
    [
     destruct l; inversion H_eq_cache |
     destruct l; inversion H_eq_cache |
     destruct l; inversion H_eq_cache | |
    ].
    - wp_pures.
      iApply "HΦ".
      iLeft.
      iSplit; first done.
      iPureIntro.
      destruct l as [| e  l']; last done.
      rewrite list_to_map_nil in H_eq_updates.
      simplify_eq.
      unfold is_coherent_cache in H_coh.
      destruct H_coh as ( _ & _ & _ & _ & _ & H_coh1 & _ & H_coh2).
      apply bool_decide_pack.
      intros k H_k_in.
      destruct (cache_logicalM !! k) as [p | ] eqn:H_lookup; last done.
      destruct p as [vo b].
      destruct b; last done.
      pose proof (H_coh2 _ _ H_lookup) as H_some.
      destruct vo as [v | ]; last by inversion H_some.
      by apply H_coh1 in H_lookup.
    - wp_pures.
      destruct l as [| e  l']; first done.
      destruct e as [e_key e_val].
      pose proof H_coh as (H_coh1 & H_coh2 & H_coh3 & _ & _ & H_coh6 & _).
      assert (e_key ∈ KVS_keys) as H_e_in; first set_solver.
      assert (e_key ∈ dom Msnap) as H_e_in'; first set_solver.
      assert (∃ vo : option val, cache_logicalM !! e_key = Some (vo, true)) as H_some.
      {
        simpl in H_eq_updates.
        rewrite H_eq_updates in H_coh6.
        exists (Some e_val).
        apply H_coh6.
        apply lookup_insert.
      }
      simpl in H_eq_cache.
      inversion H_eq_cache as [H_eq_v].
      wp_pures. 
      wp_apply (wp_map_lookup _ e_key kvs m); first done.
      iIntros (v H_match).
      wp_pures.
      destruct (m !! e_key) as [ v' | ] eqn:H_lookup; 
        rewrite H_match; wp_pures.
      + unfold network_util_code.unSOME.
        wp_pures.
        wp_apply (check_at_key_spec e_key ts tc v' kvs cache 
          cache_updatesM m cache_logicalM Msnap M); try done.
        1 : by rewrite H_lookup.
        iIntros (br [(-> & H_commit) | (-> & H_neq)]).
        * wp_if_true.
          simpl in H_eq_updates.
          iApply "IH".
          -- admit.
          -- admit.
          -- admit.
          -- iPureIntro.
             eapply (is_coherent_cache_delete e_key); last apply H_coh.
          -- iPureIntro.
             eexists l'.
             split_and!; try done.
             ++ rewrite H_eq_updates.
                   rewrite delete_insert_dom; first done.
                   apply NoDup_cons_1_1 in H_dup.
                   simpl in H_dup.
                   rewrite dom_list_to_map_L.
                   set_solver.
             ++ by apply NoDup_cons_1_2 in H_dup.
          -- admit.
          -- iModIntro.
             iIntros (b) "HΦ'".
             iApply "HΦ".
             destruct b.
             ++ iLeft.
                iSplit; first done.
                iDestruct "HΦ'" as "[(_ & %H_com_status) | (%Habs & _)]"; last done.
                iPureIntro.
                apply (can_do_commit e_key); done.
             ++ iRight.
                iSplit; first done.
                iDestruct "HΦ'" as "[(%Habs & _) | (_ & %H_com_status)]"; first done.
                iPureIntro.
                apply (can_not_do_commit_delete e_key); done.
        * wp_if_false.
          iApply "HΦ".
          iRight.
          iSplit; first done.
          iPureIntro.
          eapply can_not_do_commit; try done.
      + wp_apply (check_at_key_spec e_key ts tc (InjLV #()) kvs cache 
          cache_updatesM m cache_logicalM Msnap M); try done.
          1 : by rewrite H_lookup.
        iIntros (br [(-> & H_commit) | (-> & H_neq)]).
        * wp_if_true.
          simpl in H_eq_updates.
          iApply "IH".
          -- admit.
          -- admit.
          -- admit.
          -- iPureIntro.
             eapply (is_coherent_cache_delete e_key); last apply H_coh.
          -- iPureIntro.
             eexists l'.
             split_and!; try done.
             ++ rewrite H_eq_updates.
                   rewrite delete_insert_dom; first done.
                   apply NoDup_cons_1_1 in H_dup.
                   simpl in H_dup.
                   rewrite dom_list_to_map_L.
                   set_solver.
             ++ by apply NoDup_cons_1_2 in H_dup.
          -- admit.
          -- iModIntro.
             iIntros (b) "HΦ'".
             iApply "HΦ".
             destruct b.
             ++ iLeft.
                iSplit; first done.
                iDestruct "HΦ'" as "[(_ & %H_com_status) | (%Habs & _)]"; last done.
                iPureIntro. 
                apply (can_do_commit e_key); done.
             ++ iRight.
                iSplit; first done.
                iDestruct "HΦ'" as "[(%Habs & _) | (_ & %H_com_status)]"; first done.
                iPureIntro.
                apply (can_not_do_commit_delete e_key); done.
        * wp_if_false.
          iApply "HΦ".
          iRight.
          iSplit; first done.
          iPureIntro.
          eapply can_not_do_commit; try done.
  Admitted.

  Lemma update_kvs_spec (kvs cacheV : val) (tc : nat)
    (cache_updatesM m : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap M : gmap Key (list write_event)) 
    (cache : gmap Key SerializableVal)
    (S : snapshots) :
    (∀ k v, (∃ sv, cache !! k = Some sv ∧ sv.(SV_val) = v) ↔ cache_updatesM !! k = Some v) →
    is_coherent_cache cache_updatesM cache_logicalM Msnap →
    is_map (InjRV cacheV) cache_updatesM →
    is_map kvs m →
    kvsl_valid m M S tc →
    {{{ ⌜True⌝ }}}
      snapshot_isolation_code.update_kvs kvs (InjRV cacheV) #(tc + 1) 
        @[ip_of_address MTC.(MTS_saddr)]
    {{{ (kvs_updated : val), RET kvs_updated; 
        ⌜is_map kvs_updated (update_kvsl m cache (tc + 1))⌝}}}.
  Proof.
  Admitted.

  Lemma cache_updatesM_to_cache (cache_updatesM: gmap Key val) :
    map_Forall (λ k v, KVS_Serializable v) cache_updatesM →
    (∃ cache : gmap Key SerializableVal,
      (∀ k v, (∃ sv, cache !! k = Some sv ∧ sv.(SV_val) = v) ↔ cache_updatesM !! k = Some v)).
  Proof.
    intros Hyp.
    induction cache_updatesM as [|i x m H_eq IH] using map_ind.
    - exists ∅.
      intros k v.
      split.
      + intros [v' (Habs & _)].
        by rewrite lookup_empty in Habs. 
      + intro Habs.
        by rewrite lookup_empty in Habs. 
    - eapply map_Forall_insert_1_2 in H_eq as Hyp_less; last apply Hyp.
      apply IH in Hyp_less as [cache H_cache].
      apply map_Forall_insert_1_1 in Hyp as H_ser_x.
      exists (<[i:={| SV_val := x; SV_ser := H_ser_x|}]> cache).
      intros k v.
      split.
      + intro H_lookup.
        destruct (decide (k = i)) as [<-| H_neq_k].
        * rewrite lookup_insert.
          rewrite lookup_insert in H_lookup.
          set_solver.
        * rewrite lookup_insert_ne; last done.
          rewrite lookup_insert_ne in H_lookup; last done.
          by apply H_cache.
      + intro H_lookup.
        destruct (decide (k = i)) as [<-| H_neq_k].
        * rewrite lookup_insert.
          rewrite lookup_insert in H_lookup.
          set_solver.
        * rewrite lookup_insert_ne; last done.
          rewrite lookup_insert_ne in H_lookup; last done.
          by apply H_cache.
  Qed.

  Lemma cache_dom_eq (cache_updatesM : gmap Key val) (cache : gmap Key SerializableVal) :
    (∀ (k : Key) (v : val),
      (∃ sv : SerializableVal, cache !! k = Some sv ∧ sv.(SV_val) = v)
      ↔ cache_updatesM !! k = Some v) →
    dom cache = dom cache_updatesM.
  Proof.
    intros H_some. 
    assert (∀ k, k ∈ dom cache ↔ k ∈ dom cache_updatesM) as H_in_in.
    {
      intro k.
      split; intro H_is_some.
      - apply elem_of_dom in H_is_some. 
        destruct (cache !! k) as [v | ] eqn:H_lookup.
        + specialize (H_some k v).
          destruct H_some as [H_some _].
          apply elem_of_dom.
          rewrite H_some; first done.
          set_solver.
        + by inversion H_is_some.
      - apply elem_of_dom in H_is_some.
        destruct (cache_updatesM !! k) as [v | ] eqn:H_lookup. 
        + specialize (H_some k v).
          destruct H_some as [_ H_some].
          apply H_some in H_lookup as [sv [H_lookup _]].
          apply elem_of_dom.
          by rewrite H_lookup.
        + by inversion H_is_some.
    }
    set_solver.
  Qed.

  Lemma commit_handler_spec
    (lk : val)
    (kvs vnum : loc)
    (reqd : ReqData)
    (Φ : val → iPropI Σ)
    (E : coPset)
    (P : iProp Σ)
    (Q : val → iProp Σ)
    (ts : nat)
    (cache_updatesM : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap : gmap Key (list write_event))
    (cmapV : val) :
    reqd = inr (inr (E, ts, cache_updatesM, cache_logicalM, Msnap, P, Q)) →
    ↑KVS_InvName ⊆ E →
    is_map cmapV cache_updatesM →
    is_coherent_cache cache_updatesM cache_logicalM Msnap →
    kvs_valid_snapshot Msnap ts →
    map_Forall (λ (_ : Key) (v : val), KVS_Serializable v) cache_updatesM →
    server_lock_inv γGauth γT γlk lk kvs vnum -∗
    Global_Inv clients γKnownClients γGauth γGsnap γT γTrs -∗
    ownTimeSnap γT ts -∗
    ([∗ map] k↦h' ∈ Msnap, ownMemSeen γGsnap k h') -∗
    P -∗
    (P ={⊤,E}=∗
        ∃ m_current : gmap Key (list val), ⌜dom m_current = dom Msnap⌝ ∗
          ([∗ map] k↦hv ∈ m_current, OwnMemKey_def γGauth γGsnap k hv) ∗
          ▷ (∀ b : bool,
              ⌜b = true⌝ ∗
              ⌜can_commit m_current
                  ((λ h : list write_event, to_hist h) <$> Msnap)
                  cache_logicalM⌝ ∗
              ([∗ map] k↦h;p ∈ m_current;cache_logicalM,
                OwnMemKey_def γGauth γGsnap k (commit_event p h) ∗
                Seen_def γGsnap k (commit_event p h)) ∨ 
                ⌜b = false⌝ ∗
              ⌜¬ can_commit m_current
                    ((λ h : list write_event, to_hist h) <$> Msnap)
                    cache_logicalM⌝ ∗
              ([∗ map] k↦h ∈ m_current, OwnMemKey_def γGauth γGsnap k h ∗
                Seen_def γGsnap k h) ={E,⊤}=∗ Q #b)) -∗
    (∀ (repv : val) (repd : RepData),
         ⌜sum_valid_val (option_serialization KVS_serialization)
            (sum_serialization int_serialization bool_serialization) repv⌝ ∗
         ReqPost clients γKnownClients γGauth γGsnap γT γTrs repv reqd repd -∗
         Φ repv) -∗
    WP let: "res" := InjR
                      (InjR
                        (acquire lk ;;
                        let: "res" := (λ: <>,
                                        let: "tc" :=
                                        ! #vnum + #1 in
                                        let: "kvs_t" :=
                                        ! #kvs in
                                        let: "ts" :=
                                        Fst (#ts, cmapV)%V in
                                        let: "cache" :=
                                        Snd (#ts, cmapV)%V in
                                        if: list_is_empty "cache" then #true
                                        else let: "b" :=
                                             map_forall
                                               (λ: "k" "_v",
                                                  let: "vlsto" :=
                                                  map_lookup "k" "kvs_t" in
                                                  let: "vs" :=
                                                  if:
                                                  "vlsto" = InjL #()
                                                  then
                                                  InjL #()
                                                  else
                                                  network_util_code.unSOME
                                                    "vlsto" in
                                                  check_at_key "k" "ts" "tc" "vs")
                                               "cache" in
                                             if: "b"
                                             then #vnum <- "tc" ;;
                                                  #kvs <-
                                                  snapshot_isolation_code.update_kvs
                                                    "kvs_t" "cache" "tc" ;; #true
                                             else #false)%V #() in
                       release lk ;; "res")) in "res" @[
      ip_of_address KVS_address] {{ v, Φ v }}.
  Proof.
  Admitted.
    (* iIntros (Hreqd Hsub Hmap Hcoh Hvalid Hall) "#Hlk #HGlobInv #Htime #Hseen HP Hshift HΦ".
    wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#".
    iIntros (?) "(-> & Hlock & Hlkres)".
    wp_pures.
    unfold lkResDef.
    iDestruct "Hlkres"
      as (M S T m kvsV Hmap' Hvalid')
      "(%Hser & HmemLoc & HtimeLoc & HkvsL & HvnumL)".
    wp_load.
    wp_pures.
    unfold list_is_empty.
    destruct Hmap as [l (HcupdEq & HcmapEq & HnoDup)].
    destruct cmapV as [ abs | abs | abs | v | v ];
    [
     destruct l; inversion HcmapEq |
     destruct l; inversion HcmapEq |
     destruct l; inversion HcmapEq | |
    ].
    - (* Cache is empty case *)
      wp_bind (Load _).
      wp_apply (aneris_wp_atomic _ _ E).
      (* Viewshift *)
      iMod ("Hshift" with "[$HP]") as (m_current HdomEq) "(Hkeys & Hpost)".
      iModIntro.
      wp_load.
      (* Closing of viewshift *)
      iDestruct ("Hpost" with "[Hkeys]") as "HQ".
      + iLeft.
        iSplitR; first done.
        destruct l; inversion HcmapEq as [HvEq].
        simpl in HcupdEq.
        simplify_eq.
        destruct Hcoh as (Hdom & _ & _ & _ & _ & Hcoh1 & _ & Hcoh2).
        iSplit.
        * iPureIntro.
          apply bool_decide_pack.
          intros k HkKVs.
          destruct (cache_logicalM !! k) eqn:Hlookup; last done.
          destruct p as [p1 p2].
          destruct p2; last done.
          apply Hcoh2 in Hlookup as Hsome.
          destruct p1; last by inversion Hsome.
          by rewrite -Hcoh1 in Hlookup.
        * iApply (big_sepM2_mono
            (λ k v1 v2, OwnMemKey_def γGauth γGsnap k v1 ∗ Seen_def γGsnap k v1)%I).
          -- iIntros (k v1 v2 Hlookupv1 Hlookupv2) "Hkeys".
             assert (commit_event v2 v1 = v1) as ->; last iFrame.
             unfold commit_event.
             destruct v2 as [v2 b].
             destruct v2; last done.
             destruct b; last done.
             apply Hcoh2 in Hlookupv2 as Hsome.
             by rewrite -Hcoh1 in Hlookupv2.
          -- iApply (big_sepM2_mono
               (λ k v1 v2, (OwnMemKey_def γGauth γGsnap k v1 ∗ Seen_def γGsnap k v1) ∗ emp)%I).
               {
                iIntros (? ? ? ? ?) "((? & ?) & ?)".
                iFrame.
               }
             iApply (big_sepM2_sepM_2
               (λ k v, OwnMemKey_def γGauth γGsnap k v ∗ Seen_def γGsnap k v)%I
               (λ k v, emp)%I m_current cache_logicalM with "[Hkeys] [//]").
             2 : iApply (mem_implies_seen with "[$Hkeys]").
             rewrite -Hdom in HdomEq.
             intro k.
             destruct (decide (k ∈ dom m_current)) as [Hin | Hnin].
             {
               apply elem_of_dom in Hin as Hsome.
               rewrite HdomEq in Hin.
               by apply elem_of_dom in Hin as Hsome'.
             }
             apply not_elem_of_dom_1 in Hnin as Hnone.
             rewrite HdomEq in Hnin.
             apply not_elem_of_dom_1 in Hnin as Hnone'.
             rewrite Hnone Hnone'.
             split; intro Habs; by inversion Habs.
      + (* Proceding with proof after viewshift *)
        iMod "HQ".
        iModIntro.
        wp_pures.
        wp_apply (release_spec with
          "[$Hlock $Hlk HkvsL HvnumL HmemLoc HtimeLoc]").
        {
          unfold lkResDef.
          iExists M, S, T, m, kvsV.
          iFrame "#∗".
          by iPureIntro.
        }
        iIntros (v' ->).
        wp_pures.
        iApply "HΦ".
        iSplit.
        * iPureIntro.
          eexists _.
          right.
          split; first done.
          simpl.
          eexists _.
          right.
          split; first done.
          simpl.
          by exists true.
        * unfold ReqPost.
          iFrame "#".
          do 2 iRight.
          iExists _, _, _, _, _, _, _, _.
          iSplit; first done.
          iSplit; first done.
          iSplit; done.
    - (* Cache is not empty case. *) 
      (* Note: We have to figure out now whether the commit will be successful,
         and not wait till we apply map_forall_spec, as we will have no atomic 
         operations left to apply the viewshift if the commit is unsuccessful. *)
      destruct (decide (can_commit
                          ((λ hw, to_hist hw) <$> filter (λ k, k.1 ∈ dom Msnap) M) 
                          ((λ hw, to_hist hw) <$> Msnap) 
                          cache_logicalM)) as [H_commit | H_commit].
      + (* Commit is successfull case *)
        wp_load.
        wp_pures.
        wp_apply (map_forall_spec ts T kvsV (InjRV v) cache_updatesM m cache_logicalM Msnap M S); try eauto.
        {
          by eexists _.
        }
        iIntros (b) "[(-> & %H_com_status) | (-> & %H_com_status)]"; last done.
        (* Valid case when we know commit is successful *)
        wp_pures.
        wp_store.
        pose proof (cache_updatesM_to_cache _ Hall) as [cache H_cache].
        pose proof (cache_dom_eq _ _ H_cache) as H_cache_eq.
        pose proof Hcoh as ( _ & _ & H_sub & _).
        rewrite -H_cache_eq in H_sub.
        unfold snapshot_isolation_code.update_kvs.
        wp_apply (update_kvs_spec kvsV v T cache_updatesM m cache_logicalM Msnap M cache S); try eauto.
        {
          by eexists _.
        }
        iIntros (kvs_updated) "%H_map_up".
        wp_bind (Store _ _).
        wp_apply (aneris_wp_atomic _ _ E).
        (* Viewshift and opening of invariant *)
        iMod ("Hshift" with "[$HP]") as (m_current_client) "(%H_dom_eq_cl & Hkeys & Hpost)".
        iInv KVS_InvName as (Mg Sg Tg gMg) 
          ">(HmemGlob & HsnapAuth & HtimeGlob & Hccls & %Hdom & %HkvsValid)".
        (* Getting ready for update of logical ressources *)
        iDestruct "HmemGlob" as "(HmemGlobAuth & HmemMono)".
        iAssert (⌜M = Mg⌝%I) as "<-".
        { 
          iApply (ghost_map.ghost_map_auth_agree γGauth (1/2)%Qp (1/2)%Qp M
            with "[$HmemLoc][$HmemGlobAuth]").
        }
        iDestruct (mono_nat.mono_nat_auth_own_agree with "[$HtimeGlob][$HtimeLoc]")
          as "(%Hleq & ->)".
        iDestruct (mem_auth_lookup_big with "[$HmemLoc] [$Hkeys]")
          as "(HmemLoc & Hkeys & %Hmap_eq)".
        apply map_eq_filter_dom in Hmap_eq.
        (* Update of logical ressources *)
        iDestruct (commit_logical_update clients γKnownClients γGauth γGsnap γT γTrs
          ts T Sg cache_logicalM cache_updatesM cache M Msnap m_current_client) as "H_upd".
        iDestruct ("H_upd" with "[] [] [] [] [] [] [] [$HmemMono] [$HtimeGlob]
          [$HtimeLoc] [$HmemGlobAuth] [$HmemLoc] [$Hkeys]") as 
          ">(HtimeGlob & HtimeLoc & HmemGlob & HmemLoc & HmemMono & Hkeys)"; try done.
        {
          iPureIntro. 
          by rewrite Hmap_eq  H_dom_eq_cl.
        }
        (* Closing of invaraint *)
        iSplitL "HtimeGlob HmemGlob Hccls HmemMono HsnapAuth".
        {
          iModIntro.
          iNext.
          iExists (update_kvs M cache (T + 1)%nat), Sg, (T + 1)%nat, gMg.
          iFrame.
          iSplit; first done.
          iPureIntro.
          apply kvs_valid_update; try done.
        }
        iModIntro.
        iModIntro.
        wp_store.
        (* Closing of viewshift *)
        iDestruct ("Hpost" $! true with "[Hkeys]") as "HQ".
        {
          iLeft.
          iFrame.
          iSplit; first done.
          iPureIntro. 
          by rewrite Hmap_eq  H_dom_eq_cl.
        }
        (* Proceding with proof after viewshift *)
        iMod "HQ".
        iModIntro.
        wp_pures.
        wp_apply (release_spec with
          "[$Hlock $Hlk HkvsL HvnumL HmemLoc HtimeLoc]").
        {
          iExists (update_kvs M cache (T + 1)%nat), S, (T + 1)%nat, 
            (update_kvsl m cache (T + 1)%nat), kvs_updated.
          iFrame "#∗".
          iSplit; first done.
          iSplit.
          {
            iPureIntro.
            apply kvsl_valid_update; try done.
          }
          iSplit.
          {
            iPureIntro.
            by apply upd_serializable.
          }
          replace (Z.of_nat T + 1)%Z with (Z.of_nat (T + 1)) by lia.
          iFrame.
        }
        iIntros (? ->).
        wp_pures.
        iApply ("HΦ" $! _ _).
        iSplit.
        {
          iPureIntro. 
          by apply ser_commit_reply_valid.
        }
        rewrite /ReqPost.
        iFrame "#".
        do 2 iRight.
        iExists _, _, _, _, _, _, _, _.
        iSplit; first done.
        iSplit; first done.
        iSplit; done.
        Unshelve.
        all : try done.
      + (* Commit is not successful case *)
        wp_bind (Load _).
        wp_apply (aneris_wp_atomic _ _ E).
        (* Viewshift *)
        iMod ("Hshift" with "[$HP]") as (m_current HdomEq) "(Hkeys & Hpost)".
        iModIntro.
        iDestruct (mem_auth_lookup_big with "[$HmemLoc] [$Hkeys]")
          as "(HmemLoc & Hkeys & %Hmap_eq)".
        apply map_eq_filter_dom in Hmap_eq.
        wp_load.
        (* Closing of viewshift *)
        iDestruct ("Hpost" with "[Hkeys]") as "HQ".
        * iRight.
          iSplitR; first done.
          iSplitR.
          {
            iPureIntro.
            rewrite Hmap_eq.
            by rewrite HdomEq.
          }
          by iApply mem_implies_seen.
        * (* Proceding with proof after viewshift *)
          iMod "HQ".
          iModIntro.
          wp_pures.
          wp_apply (map_forall_spec ts T kvsV (InjRV v) cache_updatesM m cache_logicalM Msnap M S); try eauto.
          {
            by eexists _.
          }
          iIntros (b) "[(-> & %H_com_status) | (-> & %H_com_status)]"; first done.
          (* Valid case when we know commit is not successful *)
          wp_pures.
          wp_apply (release_spec with
            "[$Hlock $Hlk HkvsL HvnumL HmemLoc HtimeLoc]").
          {
            iExists M, S, T, m, kvsV.
            iFrame "#∗".
            iPureIntro.
            split_and!; done.
          }
          iIntros (? ->).
          wp_pures.
          iApply ("HΦ" $! _ _).
          iSplit.
          {
            iPureIntro. 
            by apply ser_commit_reply_valid.
          }
          rewrite /ReqPost.
          iFrame "#".
          do 2 iRight.
          iExists _, _, _, _, _, _, _, _.
          iSplit; first done.
          iSplit; first done.
          iSplit; done.
  Qed. *)

End Proof_of_commit_handler.
