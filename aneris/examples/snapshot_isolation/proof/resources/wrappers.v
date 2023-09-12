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
     Require Import time events model.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import resource_algebras server_resources proxy_resources
     global_invariant.

(** TODO: try to prove this lemma unfolding it down to big_opM and using induction.
            Should probably be done in a similar way to how e.g. big_sepM_filter is proven. *)
  Lemma big_sepM_split_frac:
      ∀ {Σ :  gFunctors} {K1 : Type} {K2 : Type}
        {EqDecision1 : EqDecision K1} {EqDecision2 : EqDecision K2}
        {H1 : Countable K1} {H2 : Countable K2} {A1 : Type} {A2: Type}
        (m1 : gmap K1 A1)  (m2 : gmap K2 A2) (q : Qp) (γ : gname)
        {H0 : ghost_map.ghost_mapG Σ K1 A1},
          ghost_map.ghost_map_auth γ q m1 ⊣⊢
          [∗ map] k ↦ _ ∈ m2,
            ghost_map.ghost_map_auth γ (q / pos_to_Qp (Pos.of_nat (size m2))) m1.
  Proof. Admitted.

Section Wrapper_defs.
  Context `{!anerisG Mdl Σ, !IDBG Σ, !MTS_resources}.
  Context `{!User_params}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTss : gname).

  Definition to_local_state (s : proxy_state) : local_state :=
    match s with
      PSCanStart => CanStart
    | PSActive M => Active ((λ h, to_hist h) <$> M)
    end.

  Lemma to_hist_prefix_mono hw hw' :
    hw `prefix_of` hw' →  to_hist hw `prefix_of` to_hist hw'.
  Proof.
    intros Hp.
    generalize dependent hw'.
    induction hw as [|x l]; intros hw' Hp.
    - by apply prefix_nil.
    - destruct hw' as [|x' l'].
      -- by apply prefix_nil_not in Hp.
      -- simplify_eq /=.
         assert (x = x') as -> by by apply prefix_cons_inv_1 in Hp.
         apply prefix_cons.
         apply IHl.
         by apply prefix_cons_inv_2 in Hp.
  Qed.

  Definition GlobalInv_def : iProp Σ :=
    Global_Inv clients γKnownClients γGauth γGsnap γT γTss.

  Definition OwnMemKey_def k h : iProp Σ :=
    ∃ hw, ownMemUser γGauth γGsnap k hw ∗ ⌜h = to_hist hw⌝.

  Definition ConnectionState_def c sa s : iProp Σ :=
    ∃ sp, connection_state γGsnap γKnownClients c sa sp ∗ ⌜s = to_local_state sp⌝.

  Definition Seen_def k h : iProp Σ :=
    ∃ hw, ownMemSeen γGsnap k hw ∗ ⌜h = to_hist hw⌝.

  Definition client_can_connect_res sa : iProp Σ :=
    client_can_connect γKnownClients sa.

  (* Lemma mem_key_map_we_exists m : *)
  (*   ([∗ map] k↦hv ∈ m, OwnMemKey_def k hv) -∗ *)
  (*   ∃ M, ([∗ map] k↦h ∈ M, ownMemUser γGauth γGsnap k h) ∗ *)
  (*        ⌜m = (λ h, to_hist h)<$>M⌝. *)
  (* Proof. Admitted. *)

  Lemma mem_auth_lookup_big
    (q : Qp) (mu : gmap Key (list val)) (M : gmap Key (list write_event)) :
    ghost_map.ghost_map_auth γGauth q%Qp M -∗
    ([∗ map] k↦h ∈ mu, OwnMemKey_def  k h) -∗
    ghost_map.ghost_map_auth γGauth q%Qp M ∗
    ([∗ map] k↦h ∈ mu, OwnMemKey_def  k h) ∗
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

End Wrapper_defs.
