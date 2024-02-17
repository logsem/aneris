From iris.algebra Require Import agree auth excl gmap updates local_updates.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.snapshot_isolation.specs Require Import
  user_params aux_defs time events resource_algebras.
From aneris.examples.snapshot_isolation.proof
     Require Import utils model.
From aneris.examples.snapshot_isolation.proof.resources Require Import
  server_resources proxy_resources global_invariant.

Section Wrapper_defs.
  Context `{!anerisG Mdl Σ, !IDBG Σ, !MTS_resources}.
  Context `{!User_params}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs : gname).

  Definition to_local_state (s : proxy_state) : local_state :=
    match s with
      PSCanStart => CanStart
    | PSActive M => Active ((λ h, to_hist h) <$> M)
    end.

  Definition GlobalInv_def : iProp Σ :=
    Global_Inv clients γKnownClients γGauth γGsnap γT γTrs.

  Definition OwnMemKey_def k h : iProp Σ :=
    ∃ hw, ownMemUser γGauth γGsnap k hw ∗ ⌜h = to_hist hw⌝.

  Definition ConnectionState_def c sa s : iProp Σ :=
    ∃ sp, connection_state γGsnap γKnownClients c sa sp ∗ ⌜s = to_local_state sp⌝.

  Definition Seen_def k h : iProp Σ :=
    ∃ hw, ownMemSeen γGsnap k hw ∗ ⌜h = to_hist hw⌝.

  Definition client_can_connect_res sa : iProp Σ :=
    client_can_connect γKnownClients sa.

  Lemma mem_implies_seen (m : gmap Key (list val)) :
    ([∗ map] k↦h ∈ m, OwnMemKey_def k h) -∗
    ([∗ map] k↦h ∈ m, OwnMemKey_def k h ∗ Seen_def k h).
  Proof.
    iIntros "Hkeys".
    iApply (big_sepM_wand with "[$Hkeys] []").
    iApply big_sepM_intro.
    iModIntro.
    iIntros (k v Hlookup) "[%hwe ((Helem & #Hseen') & %HhistEq)]".
    iSplitL "Helem".
    all : iExists hwe.
    all : by iFrame "#∗".
  Qed.

  Lemma mem_auth_lookup_big
    (q : Qp) (mu : gmap Key (list val)) (M : gmap Key (list write_event)) :
    ghost_map.ghost_map_auth γGauth q%Qp M -∗
    ([∗ map] k↦h ∈ mu, OwnMemKey_def k h) -∗
    ghost_map.ghost_map_auth γGauth q%Qp M ∗
    ([∗ map] k↦h ∈ mu, OwnMemKey_def k h) ∗
    ([∗ map] k↦h ∈ mu,
      ⌜mu !! k =
            ((λ h : list write_event, to_hist h)
                <$> (filter (λ k : Key * list write_event, k.1 ∈ dom mu) M))
              !! k⌝).
  Proof.
    iIntros "H_auth H_keys".
    iInduction mu as [|i x m H_eq] "IH" using map_ind forall (q); first by iFrame.
    iDestruct (big_sepM_insert with "H_keys") as "(H_key & H_keys)"; first apply H_eq.
    iDestruct "H_key" as (hw) "((H_key & H_seen) & %H_eq_x_hw)".
    iDestruct (ghost_map_lookup with "H_auth H_key") as "%H_lookup".
    iDestruct ("IH" $! q%Qp with "H_auth H_keys") as "(H_auth & H_keys & IH_instance)".
    iFrame.
    iSplitL "H_keys H_key H_seen".
    {
      iApply big_sepM_insert; first apply H_eq.
      iFrame.
      iExists hw.
      by iFrame.
    }
    iApply big_sepM_insert; first apply H_eq.
    iSplitL "".
    - iPureIntro.
      rewrite lookup_insert.
      rewrite lookup_fmap.
      eapply (map_filter_lookup_Some_2
        (λ k : Key * list write_event, k.1 ∈ dom (<[i:=x]> m))) in H_lookup
        as ->; set_solver.
    - iApply (big_sepM_wand with "[$IH_instance]").
      iApply big_sepM_intro.
      iPureIntro.
      simpl.
      intros k lv H_eq_some IH.
      destruct (decide (k = i)) as [ -> | ]; first set_solver.
      rewrite lookup_insert_ne; last done.
      rewrite lookup_fmap.
      destruct (decide (k ∈ dom m)) as [H_in | H_nin].
      + destruct (M !! k) as [ lw | ] eqn:H_k_lookup.
        * eapply (map_filter_lookup_Some_2
          (λ k : Key * list write_event, k.1 ∈ dom (<[i:=x]> m))) in H_k_lookup
          as H_k_lookup'; last set_solver.
          eapply (map_filter_lookup_Some_2
          (λ k : Key * list write_event, k.1 ∈ dom m)) in H_k_lookup
          as H_k_lookup''; last set_solver.
          rewrite IH lookup_fmap.
          by rewrite H_k_lookup' H_k_lookup''.
        * rewrite map_filter_lookup_None_2; last set_solver.
          rewrite lookup_fmap in IH.
          by rewrite map_filter_lookup_None_2 in IH; last set_solver.
      + rewrite map_filter_lookup_None_2; last set_solver.
        rewrite lookup_fmap in IH.
        by rewrite map_filter_lookup_None_2 in IH; last set_solver.
    Qed.

  Lemma mem_auth_lookup_big_some
    (q : Qp) (mu : gmap Key (list val)) (M : gmap Key (list write_event)) :
    ghost_map.ghost_map_auth γGauth q%Qp M -∗
    ([∗ map] k↦h ∈ mu, OwnMemKey_def  k h) -∗
    ghost_map.ghost_map_auth γGauth q%Qp M ∗
    ([∗ map] k↦h ∈ mu, ∃ hwe, ownMemUser γGauth γGsnap k hwe ∗
        ⌜h = to_hist hwe⌝ ∗ ⌜M !! k = Some hwe⌝).
  Proof.
    iIntros "H_auth H_keys".
    iInduction mu as [|i x m H_eq] "IH" using map_ind forall (q); first by iFrame.
    iDestruct (big_sepM_insert with "H_keys") as "(H_key & H_keys)"; first apply H_eq.
    iDestruct "H_key" as (hw) "((H_key & H_seen) & %H_eq_x_hw)".
    iDestruct (ghost_map_lookup with "H_auth H_key") as "%H_lookup".
    iDestruct ("IH" $! q%Qp with "H_auth H_keys") as "(H_auth & H_keys)".
    iFrame.
    iApply big_sepM_insert; first apply H_eq.
    iFrame.
    iExists hw.
    by iFrame.
  Qed.

  Lemma map_eq_filter_dom
        (mu : gmap Key (list val)) (M : gmap Key (list write_event)) :
    map_Forall
      (λ (k : Key) (_ : list val),
         mu !! k =
           ((λ h : list write_event, to_hist h)
              <$>  filter (λ k0 : Key * list write_event, k0.1 ∈ dom mu) M)
             !! k) mu →
    mu =
      (λ h : list write_event, to_hist h)
        <$> filter (λ k : Key * list write_event, k.1 ∈ dom mu) M.
  Proof.
    intro Hmap_eq.
    apply map_eq.
    intros i.
    destruct (mu !! i) eqn:Hmi.
    - specialize (Hmap_eq i l Hmi). simpl in Hmap_eq.
      by rewrite -Hmap_eq.
    - rewrite lookup_fmap.
      simplify_eq /=.
      symmetry.
      destruct ((λ h : list write_event, to_hist h)
                  <$> filter (λ k : Key * list write_event, k.1 ∈ dom mu) M !! i)
               eqn:Hmfi; last done.
      apply fmap_Some_1 in Hmfi as (hl & Hmfi & ->) .
      apply map_filter_lookup_Some_1_2 in Hmfi; simpl in Hmfi.
      apply elem_of_dom in Hmfi.
      rewrite Hmi in Hmfi.
      by destruct Hmfi.
  Qed.

  Lemma commit_logical_update (ts T : nat) (S : snapshots)
    (cache_logicalM : gmap Key (option val * bool))
    (cache_updatesM : gmap Key val)
    (cache : gmap Key SerializableVal)
    (M Msnap : gmap Key (list write_event))
    (m_current : gmap Key (list val)) :
      ⌜dom m_current = dom Msnap⌝ -∗
      ⌜is_coherent_cache cache_updatesM cache_logicalM Msnap⌝ -∗
      ⌜kvs_valid_snapshot Msnap ts⌝ -∗
      ⌜kvs_valid M S T⌝ -∗
      ⌜map_Forall (λ (_ : Key) (v : val), KVS_Serializable v) cache_updatesM⌝ -∗
      ⌜(∀ k v, (∃ sv, cache !! k = Some sv ∧ sv.(SV_val) = v) ↔ cache_updatesM !! k = Some v)⌝ -∗
      ⌜can_commit m_current
           ((λ h : list write_event, to_hist h) <$> Msnap) cache_logicalM⌝ -∗
       ownMemMono γGsnap M -∗
       ownTimeGlobal γT T -∗
       ownTimeLocal γT T -∗
       ownMemAuthGlobal γGauth M -∗
       ownMemAuthLocal γGauth M -∗
      ([∗ map] k↦hv ∈ m_current, OwnMemKey_def k hv) -∗
        |==>
          ownTimeGlobal γT (T+1) ∗
          ownTimeLocal γT (T+1) ∗
          ownMemAuthGlobal γGauth (update_kvs M cache (T+1)) ∗
          ownMemAuthLocal γGauth (update_kvs M cache (T+1)) ∗
          ownMemMono γGsnap (update_kvs M cache (T+1)) ∗
          ([∗ map] k↦h;p ∈ m_current;cache_logicalM,
                OwnMemKey_def k (commit_event p h) ∗
                Seen_def k (commit_event p h)).
    Proof.
      iIntros (dom0 cache_coh snap_valid M_valid updates_ser eval_updates commit_current) "ownM ownTimeGlobal
        ownTimeLocal ownAuthGlobal ownAuthLocal ownMemKey".
      apply bool_decide_spec in commit_current.
      iCombine "ownTimeGlobal ownTimeLocal" as "ownTime".
      iMod (mono_nat_own_update (T+1) with "ownTime")
              as "[[ownTimeGlobal ownTimeLocal] _]"; first lia.
      iFrame.
      iRevert (cache_updatesM cache_logicalM Msnap m_current cache_coh commit_current
          updates_ser eval_updates dom0 snap_valid) "ownMemKey".
      iInduction cache as [|k sv cache cache_k] "IH" using map_ind.
      all: iIntros (cache_updatesM cache_logicalM Msnap m_current cache_coh commit_current
          updates_ser eval_updates dom0 snap_valid) "ownMemKey".
      all: destruct (cache_coh) as [dom1 [dom2 [dom3 [logical_false [logical_false_empty
             [updates_some [updates_none logical_true]]]]]]].
      - iModIntro.
        rewrite update_kvs_empty.
        iFrame.
        iPoseProof (mem_implies_seen with "ownMemKey") as "ownMemKey".
        iAssert ([∗ map] k↦h;_ ∈ m_current;cache_logicalM,
          (OwnMemKey_def k h ∗ Seen_def k h) ∗ True)%I
          with "[ownMemKey]" as "ownMemKey".
        {
          iApply (big_sepM2_sepM_2 with "ownMemKey"); last done.
          move=>k.
          by split=>/(proj2 (elem_of_dom _ _ ))Hk;
            apply elem_of_dom; move: Hk; rewrite dom0 dom1.
        }
        iApply (big_sepM2_impl with "ownMemKey").
        iIntros "!>%k %h1 %h2 %m_current_k %cache_logicalM_k ((OwnMemKey & Seen) & _)".
        move:h2 cache_logicalM_k=>[][v[]|b]cache_logicalM_k; [|iFrame..].
        apply updates_some, eval_updates in cache_logicalM_k.
        by destruct cache_logicalM_k as [sv (abs & _)].
      - iSpecialize ("IH" with "[$] [$] [$]").
        iSpecialize ("IH" $! (delete k cache_updatesM) (delete k cache_logicalM)
                              (delete k Msnap) (delete k m_current)).
        have [hm m_current_k] : is_Some (m_current !! k).
        {
          apply elem_of_dom.
          rewrite dom0 -dom1.
          apply (elem_of_subseteq (dom cache_updatesM)); first done.
          apply elem_of_dom.
          exists (sv.(SV_val)).
          apply eval_updates.
          exists sv.
          by rewrite lookup_insert.
        }
        iPoseProof (big_sepM_delete _ _ _ _ m_current_k with "ownMemKey")
          as "((%hw & (k_hw & #ownMemSeen) & ->) & ownMemKey)".
        iMod ("IH" with "[] [] [] [] [] [] ownMemKey")
          as "(global & local & mono & ownMemKey)"; [iPureIntro..|].
        + by apply is_coherent_cache_delete.
        + move=>k' k'_key.
          case delete_k' : (delete k cache_logicalM !! k')=>[[a [|//]]|//].
          move: delete_k'=>/lookup_delete_Some[k_k' logical_k'].
          apply bool_decide_spec.
          rewrite lookup_delete_ne; last done.
          move: (commit_current k' k'_key).
          rewrite logical_k'=>/bool_decide_spec->.
          by rewrite !lookup_fmap lookup_delete_ne.
        + by apply map_Forall_delete.
        + move=>k' v.
          split.
          * move=>[sv'][cache_k' <-].
            apply lookup_delete_Some.
            have k_k' : k ≠ k'.
            { move=>k_k'. by rewrite -k_k' cache_k in cache_k'. }
            split; first done.
            apply eval_updates.
            exists sv'.
            by rewrite lookup_insert_ne.
          * move=>/lookup_delete_Some[k_k']/eval_updates[sv'][].
            rewrite (lookup_insert_ne _ _ _ _ k_k')=>-><-.
            by exists sv'.
        + by rewrite !dom_delete_L dom0.
        + by move=>k' h/lookup_delete_Some[k_k']/snap_valid.
        + set M_k_ := (M !! k).
          case M_k : M_k_=>[h|]; rewrite /M_k_ in M_k=>{M_k_}; last first.
          {
            rewrite update_kvs_insert_None//.
            iFrame.
            have [vo logical_k] : ∃ vo, cache_logicalM !! k = Some (vo, false).
            {
              exists (from_option
                     (λ h : list write_event,
                        from_option
                          (λ we : write_event, Some (we_val we))
                          None (last h)) None 
                     (Msnap !! k)).
              apply updates_none.
              * rewrite -dom0. apply elem_of_dom. eauto.
              * done.
              * apply not_elem_of_dom, (not_elem_of_weaken _ _ KVS_keys); last done.
                rewrite (kvs_ValidDom _ _ _ M_valid). by apply not_elem_of_dom.
            }
            iModIntro.
            iApply (big_sepM2_delete with "[k_hw ownMemSeen $ownMemKey]");
              [done..|].
            iSplitL; last first.
            {
              iExists hw.
              iSplit; first done.
              iPureIntro.
              by case vo.
            }
            iExists hw.
            iSplit; first iFrame "∗#".
            iPureIntro.
            by case vo.
          }
          rewrite (update_kvs_insert_Some _ _ _ _ _ _ M_k).
          iCombine "k_hw global" gives "%upd_some".
          move:upd_some=>/lookup_update_kvs_Some[[_]|[?][?][?][abs]];
            last by rewrite cache_k in abs.
          rewrite M_k=>[][]eq. subst.
          set we := {| we_key := k; we_val := sv;
            we_time := T + 1 : int_time.(Time) |}.
          iCombine "global local" as "auth".
          iMod (ghost_map_update (hw ++ [we]) with "auth k_hw")
            as "((global & local) & k_h)".
          iMod (own_update _ _ (● global_memUR
            (<[k := hw ++ [we]]>(update_kvs M cache (T + 1)))) with "mono") as "mono".
          { 
            unfold global_memUR.
            apply (auth_update_auth _ _ (to_max_prefix_list <$> {[k := hw ++ [we]]})).
            do 2 rewrite fmap_insert.
            rewrite fmap_empty insert_empty.
            apply (insert_alloc_local_update _ _ _ (to_max_prefix_list hw)); try done.
            - rewrite lookup_fmap.
              unfold update_kvs.
              rewrite gset_map.lookup_fn_to_gmap_2'.
              by rewrite cache_k M_k.
              by rewrite elem_of_dom.
            - assert (to_max_prefix_list (hw ++ [we]) ⋅ to_max_prefix_list hw ≡ to_max_prefix_list (hw ++ [we])) 
                as H_eq1.
              + apply to_max_prefix_list_op_r.
                by apply prefix_app_r.
              + rewrite <- H_eq1 at 1.
                assert (to_max_prefix_list (hw ++ [we]) ⋅ ε ≡ to_max_prefix_list (hw ++ [we])) 
                  as H_eq2; first by rewrite right_id.
                rewrite <- H_eq2 at 2.
                apply op_local_update.
                intros.
                rewrite H_eq1.
                apply to_max_prefix_list_validN.
          }
          iMod (get_OwnMemSeen _ _ k (hw ++ [we]) with "mono") as "(mono & #seen)";
            first apply lookup_insert.
          iModIntro.
          iFrame.
          iApply big_sepM2_delete; first done.
          { apply updates_some, eval_updates.
            exists sv. by split; first apply lookup_insert. }
          iFrame.
          simpl.
          change [sv.(SV_val)] with (to_hist [we]).
          rewrite -fmap_snoc.
          by iSplit; iExists (hw ++ [we]); repeat iSplit.
    Qed.

End Wrapper_defs.
