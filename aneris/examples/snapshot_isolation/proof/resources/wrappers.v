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
From aneris.examples.snapshot_isolation.specs Require Import user_params resources.
From aneris.examples.snapshot_isolation.proof
     Require Import utils model.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import resource_algebras server_resources proxy_resources
     global_invariant.

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


  (** A candidate for a high-level logical update to be used in the proof of commit.

      Remark 1: Check that this is indeed a good candidate toghether with checking that the model lemma
      is stated in a reasonable way, i.e.

      (** Used for commit *)
      Lemma kvs_valid_update  (M : kvsMdl) (T : nat) (Tss : gset nat) (cache : gmap Key SerializableVal) :
        dom cache ⊆ KVS_keys →
        kvs_valid M T Tss ->
        kvs_valid (update_kvs M cache (T+1)) (T+1) Tss.
      Proof.
      Admitted.

      Remark 2: A possible way to proceed would be to prove several intermediate update lemmas modifying
      different components, e.g. time, monotone memory, etc.
      For instance :

         Lemma own_mem_mono_update M (cache : gmap Key SerializableVal) (T : nat) :
            ownMemMono M ⊢ |==> ownMemMono (update_kvs M cache (T+1)).
         Proof.
         Admitted.

      Remark 3: It can also be useful to see if we can improve the definitions (in the easiest possible way)
      to make `cache_updatesM` already of the type  `gmap Key SerializableVal` so that there is no need
      to have both `cache` and  `cache_updatesM` or something similar. **)

  (* TODO : Fixme w.r.t. (S : snapshots) *)
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
    Admitted.

End Wrapper_defs.
