From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import ras log_resources resources_def.

Import gen_heap_light.
Import lock_proof.


Section Global_Invariant.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname) (N : gmap socket_address gname).

  (* ------------------------------------------------------------------------ *)
  (** Definition of the global invariant. *)
  Definition global_inv_def : iProp Σ :=
    ∃ (L : wrlog)
      (M : gmap Key (option write_event)),
      ⌜DB_keys = dom M⌝ ∗
      ⌜dom N = DB_followers ∪ {[DB_addrF]}⌝ ∗
      ⌜DB_followers ## {[DB_addrF]}⌝ ∗
      own_mem_sys γM M ∗
      own_logL_global γL L ∗
      known_replog_tokens N ∗
      ([∗ map] sa ↦ γ ∈ N, ∃ l, own_replog_global γL γ sa l) ∗
      ⌜valid_state L M⌝.

  Definition Global_Inv : iProp Σ :=
    ([∗ map] sa ↦ γ ∈ N, known_replog_token sa γ) ∗
    inv DB_InvName global_inv_def.



  (* TODO: Utils: Move!  *)
  Lemma obs_prefix_leader_follower sa h h' :
    own_obs γL sa h -∗ own_logL_global γL h' -∗
    ⌜h `prefix_of` h'⌝.
  Proof.
    iIntros "Hobs HlogL".
    iDestruct "Hobs" as "[[%Heq Hobs]|Hobs]".
    { by iDestruct (own_obs_prefix with "HlogL Hobs") as %Hprefix. }
    iDestruct "Hobs" as (γ) "(Hrep & Hobs & HL)".
    by iDestruct (own_obs_prefix with "HlogL Hobs") as %Hprefix.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** Properties entailed by the global invariant. *)

  Lemma Global_InvPersistent : Persistent Global_Inv.
  Proof. apply _. Qed.

  Lemma OwnMemKey_key_holds k q we E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user γM k q (Some we) ={E}=∗
    own_mem_user γM k q (Some we) ∗ ⌜we_key we = k⌝.
  Proof.
    iIntros (HE) "[H HGinv] Hmem".
    iInv DB_InvName as (L M) ">IH".
    iDestruct "IH" as (Hkeys Hdom Hfollower) "(Hmems&HlogL&Htoks&Hlogs&%Hvalid)".
    destruct Hvalid.
    iDestruct (gen_heap_light_valid with "Hmems Hmem") as %Hvalid'.
    assert (we_key we = k) as Hkey.
    { by eapply DB_GSTV_mem_we_key. }
    iModIntro. iSplitR "Hmem".
    { iExists _, _. iFrame. eauto. }
    iFrame. done.
  Qed.

  Lemma Obs_compare_holds a a' h h' :
    own_obs γL a h -∗ own_obs γL a' h' -∗ ⌜h ≤ₚ h'⌝ ∨ ⌜h' ≤ₚ h⌝.
  Proof.
    iIntros "Hobs1 Hobs2".
    iDestruct "Hobs1" as "[[%Heq1 Hobs1] | Hobs1]";
      iDestruct "Hobs2" as "[[%Heq2 Hobs2] | Hobs2]".
    - by iDestruct (obs_obs_prefix with "[$Hobs1 $Hobs2]") as %H''.
    - iDestruct "Hobs2" as (γ) "(_ & Hobs2 & _)".
      by iDestruct (obs_obs_prefix with "[$Hobs1 $Hobs2]") as %H''.
    - iDestruct "Hobs1" as (γ) "(_ & Hobs1 & _)".
      by iDestruct (obs_obs_prefix with "[$Hobs1 $Hobs2]") as %H''.
    - iDestruct "Hobs1" as (γ1) "(_ & Hobs1 & _)".
      iDestruct "Hobs2" as (γ2) "(_ & Hobs2 & _)".
      by iDestruct (obs_obs_prefix with "[$Hobs1 $Hobs2]") as %H''.
  Qed.

  Lemma Obs_exists_at_leader_holds a1 h1 E:
    ↑DB_InvName ⊆ E → Global_Inv ⊢
    own_obs γL a1 h1 ={E}=∗ ∃ h2, own_obs γL DB_addr h2 ∗ ⌜h1 ≤ₚ h2⌝.
  Proof.
    iIntros (HE) "[Htok HGinv] Hobs".
    iInv DB_InvName as ">IH".
    iDestruct "IH" as (L M Hkeys Hdom Hdisj)
                        "(Hmem & HlogL & Htoks & Hglob & %Hvalid)".

    iDestruct (obs_prefix_leader_follower with "Hobs HlogL") as %Hprefix.
    iDestruct (get_obs with "HlogL") as "#Hobs'".
    iModIntro.
    iSplitR "Hobs'".
    { iExists _, _. iFrame. done. }
    iModIntro. iExists L.
    iFrame "#". iSplit; [by iLeft|done].
  Qed.

  Lemma Obs_get_smaller_holds a h h' :
    h ≤ₚ h' → own_obs γL a h' -∗ own_obs γL a h.
  Proof.
    iIntros (Hprefix%mono_list_lb_mono) "[[%Heq Hobs]|Hobs]".
    - iLeft. iSplit; [done|by iApply own_mono].
    - iDestruct "Hobs" as (γ) "(Hlog&HlogL&Hown)".
      iRight. iExists _. iFrame.
      iSplitL "HlogL"; by iApply own_mono.
  Qed.

  (* TODO: Remove *)
  (* Lemma Obs_snoc_time_holds a h1 e1 h2 E : *)
  (*   nclose DB_InvName ⊆ E → *)
  (*   own_obs γL a (h1 ++ [e1] ++ h2) ={E}=∗ *)
  (*   ⌜∀ e0, e0 ∈ h1 → e0 <ₜ e1⌝ ∧ ⌜∀ e2, e2 ∈ h2 → e1 <ₜ e2⌝. *)
  (* Proof. Admitted. *)

  (* Todo: Remove *)
  (* Lemma Obs_ext_we_holds a a' h h' E : *)
  (*   nclose DB_InvName ⊆ E → *)
  (*   Global_Inv ⊢ own_obs γL a h -∗ own_obs γL a' h' ={E}=∗ *)
  (*   ⌜∀ e e', e ∈ h → e' ∈ h' → e =ₜ e' → e = e'⌝. *)
  (* Proof. Admitted. *)

  (* TODO: Remove *)
  (* Lemma Obs_ext_hist_holds a1 a2 h1 h2 k E : *)
  (*   nclose DB_InvName ⊆ E → *)
  (*   at_key k h1 = at_key k h2 → *)
  (*   Global_Inv ⊢ own_obs γL a1 h1 -∗ own_obs γL a2 h2 ={E}=∗ *)
  (*   ⌜hist_at_key k h1 = hist_at_key k h2⌝. *)
  (* Proof. Admitted. *)

  (* TODO: Used ad-hoc outside API: fix? *)
  Lemma OwnMemKey_wo_obs_holds k q wo E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user γM k q wo ={E}=∗
    own_mem_user γM k q wo ∗
      ∃ h, own_obs γL DB_addr h ∗ ⌜at_key k h = wo⌝.
  Proof. Admitted.

  Lemma OwnMemKey_some_obs_we_holds k q we E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user γM k q (Some we) ={E}=∗
    own_mem_user γM k q (Some we) ∗
      ∃ h, own_obs γL DB_addr h ∗ ⌜at_key k h = Some we⌝.
  Proof.
    iIntros (HE) "HGinv Hmem".
    iMod (OwnMemKey_wo_obs_holds with "HGinv Hmem") as "H"; [solve_ndisj|].
    iModIntro. done.
  Qed.

  Lemma OwnMemKey_obs_frame_prefix_holds a k q h h' E :
    nclose DB_InvName ⊆ E →
    h ≤ₚ h' →
    Global_Inv ⊢
    own_mem_user γM k q (at_key k h) ∗ own_obs γL a h' ={E}=∗
    own_mem_user γM k q (at_key k h) ∗ ⌜at_key k h = at_key k h'⌝.
  Proof. Admitted.

  Lemma OwnMemKey_obs_frame_prefix_some_holds a k q h h' we E :
    nclose DB_InvName ⊆ E →
    h ≤ₚ h' →
    at_key k h = Some we →
    Global_Inv ⊢
    own_mem_user γM k q (Some we) ∗ own_obs γL a h' ={E}=∗
    own_mem_user γM k q (Some we) ∗ ⌜at_key k h' = Some we⌝.
  Proof.
    iIntros (HE Hprefx <-) "HGinv [Hmem Hobs]".
    iMod (OwnMemKey_obs_frame_prefix_holds with "HGinv [$Hmem $Hobs]")
      as "[$ %Heq]"; [solve_ndisj|done|].
    iModIntro. iPureIntro. by symmetry.
  Qed.

  Lemma OwnMemKey_some_obs_frame_holds a k q we h hf E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_mem_user γM k q (Some we) ∗ own_obs γL a (h ++ [we] ++ hf) ={E}=∗
    own_mem_user γM k q (Some we) ∗ ⌜at_key k hf = None⌝.
  Proof.
    iIntros (?) "#[Htoks Hinv] [Hu1 #Hu2]".
    iInv DB_InvName as
      (lM M) ">(%Hkeys & %HNdom & %Hfollowers & Hsys & Hglog & HknN & Hreplogs & %Hvs)".
    iDestruct (obs_prefix_leader_follower with "Hu2 Hglog") as %[fr ->].
    rewrite -!assoc !(assoc _ h).
    rewrite -!assoc !(assoc _ h) in Hvs.
    iDestruct (gen_heap_light_valid with "Hsys Hu1") as %HMk.
    pose proof HMk as HMk'.
    rewrite (DB_GSTV_mem_log_coh _ _ Hvs k) in HMk; last by apply elem_of_dom; eauto.
    simplify_eq.
    iModIntro.
    iSplitR "Hu1".
    { iNext; iExists _, _; iFrame; eauto. }
    iFrame.
    iModIntro; iPureIntro.
    apply (at_key_not_in_app _ _ fr).
    eapply at_key_app_none; first by eapply valid_state_log_no_dup.
    rewrite HMk.
    rewrite at_key_snoc_some; first done.
    eapply at_key_has_key; done.
  Qed.

  Lemma OwnMemKey_none_obs_holds a k q h E :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
      own_mem_user γM k q None ∗ own_obs γL a h ={E}=∗
      own_mem_user γM k q None ∗ ⌜hist_at_key k h = []⌝.
  Proof.
    iIntros (?) "#[Htoks Hinv] [Hu1 #Hu2]".
    iInv DB_InvName as
      (lM M) ">(%Hkeys & %HNdom & %Hfollowers & Hsys & Hglog & HknN & Hreplogs & %Hvs)".
    iDestruct (obs_prefix_leader_follower with "Hu2 Hglog") as %[fr ->].
    iDestruct (gen_heap_light_valid with "Hsys Hu1") as %HMk.
    pose proof HMk as HMk'.
    rewrite (DB_GSTV_mem_log_coh _ _ Hvs k) in HMk; last by apply elem_of_dom; eauto.
    simplify_eq.
    iModIntro.
    iSplitR "Hu1".
    { iNext; iExists _, _; iFrame; eauto. }
    iFrame.
    iModIntro; iPureIntro.
    apply hist_at_key_empty_at_key.
    apply (at_key_not_in_app _ _ fr); done.
  Qed.

  (* TODO: Remove *)
  (* Lemma OwnMemKey_allocated_holds k q h0 h1 we0 E : *)
  (*   nclose DB_InvName ⊆ E → *)
  (*   h0 ≤ₚ h1 → *)
  (*   at_key k h0 = Some we0 → *)
  (*   Global_Inv ⊢ *)
  (*   own_mem_user γM k q (at_key k h1) ={E}=∗ *)
  (*   ∃ we1, own_mem_user γM k q (at_key k h1) ∗ *)
  (*            ⌜at_key k h1 = Some we1⌝ ∗ ⌜we0 ≤ₜ we1⌝. *)
  (* Proof. Admitted. *)

  (* TODO: Used ad hoc outside of API: fix? *)
  Lemma Obs_we_serializable a h E we :
    nclose DB_InvName ⊆ E →
    Global_Inv ⊢
    own_obs γL a (h ++ [we]) ={E}=∗
    ⌜Serializable
     (prod_serialization
        (prod_serialization string_serialization DB_serialization)
        int_serialization) ($ we)⌝.
  Proof.
    iIntros (HE) "[H HGinv] Hobs".
    iInv DB_InvName as (L M) ">IH".
    iDestruct "IH" as (Hkeys Hdom Hfollower) "(Hmems&HlogL&Htoks&Hlogs&%Hvalid)".
    iDestruct (obs_prefix_leader_follower with "Hobs HlogL") as %[k Heq].
    iModIntro.
    iSplitR "Hobs".
    { iExists _, _. iFrame. done. }
    iModIntro. iPureIntro.
    eapply log_events_serializable; [done|].
    set_solver.
Qed.

End Global_Invariant.

Section Alloc_resources.
 Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.

  Lemma alloc_gmem :
    ⊢ |==>
          ∃ γM : gname,
            own_mem_sys γM (gset_to_gmap (@None write_event) DB_keys) ∗
           ([∗ set] k ∈ DB_keys, own_mem_user γM k 1%Qp None).
  Proof.
    iMod (own_alloc (● (to_gen_heap ((gset_to_gmap (@None write_event) ∅))))) as (γ) "HM"; [by apply auth_auth_valid|].
    iAssert (|==>
               own γ (● to_gen_heap (gset_to_gmap None DB_keys)) ∗
               ([∗ set] k ∈ DB_keys, lmapsto γ k 1 None))%I
    with "[HM]" as "HF".
    { iInduction DB_keys as [|a l Hnotin] "IHl" using set_ind_L.
      - iModIntro. rewrite big_sepS_empty. iFrame.
      - iMod ("IHl" with "HM") as "[HM Hs]".
        iMod (gen_heap_light_alloc _ a with "HM") as "[HM H]".
        { by apply lookup_gset_to_gmap_None. }
        rewrite big_sepS_union; [|set_solver].
        rewrite big_sepS_singleton.
        iFrame.
        by rewrite gset_to_gmap_union_singleton. }
    iMod "HF".
    iModIntro. iExists γ. done.
  Qed.

  Lemma alloc_leader_logM  :
   ⊢ |==> ∃ γL, own_obs γL DB_addr [] ∗ own_log_auth γL 1 [].
  Proof.
    iMod (own_alloc (●ML [] ⋅ ◯ML [])) as (γ) "[Hown1 Hown2]".
    { apply mono_list_both_dfrac_valid.
      by split; [done|exists []; done]. }
    iExists γ. iFrame. by iLeft.
  Qed.

  Lemma alloc_logM_and_followers_gnames γL :
    DB_addrF ∉ DB_followers →
    own_log_obs γL [] ∗
    known_replog_tokens ∅ ⊢ |==>
          ∃ (N : gmap socket_address gname),
            ⌜dom N = DB_followers ∪ {[DB_addrF]}⌝ ∗
            known_replog_tokens N ∗
            ([∗ map] sa ↦ γ ∈ N,
               known_replog_token sa γ ∗
               own_log_obs γ [] ∗
               own_log_obs γL [] ∗
               own_log_auth γ (1/2) []) ∗
            ([∗ map] sa ↦ γ ∈ N, own_log_auth γ (1/2) []).
  Proof.
    iIntros (Hfollower) "[#Hlog Htoks]".
    iMod (own_alloc (●ML [] ⋅ ◯ML [])) as (γF) "[HlogFa HlogFf]".
    { apply mono_list_both_dfrac_valid.
      by split; [done|exists []; done]. }
    iMod (own_update with "Htoks") as "[Htoks HtokF]".
    { apply (auth_update_alloc _
                               ({[DB_addrF := to_agree γF]})
                               ({[DB_addrF := to_agree γF]})).
      rewrite fmap_empty.
      by apply alloc_singleton_local_update. }
    iInduction (DB_followers) as [|f s Hnin] "IH" using set_ind_L.
    {
      iModIntro. iExists {[DB_addrF := γF]}.
      rewrite /known_replog_tokens.
      rewrite fmap_insert fmap_empty.
      rewrite !big_opM_singleton. iFrame "#∗".
      iSplit; [ iPureIntro; set_solver |].
      rewrite -{1}Qp_half_half -dfrac_op_own mono_list_auth_dfrac_op.
      iDestruct "HlogFa" as "[$ $]". }
    iMod ("IH" with "[] HlogFa HlogFf Htoks HtokF")
      as (N Hdom) "(Htoks & Hlogs & HN)".
    { iPureIntro. set_solver. }
    iClear "IH".
    iMod (own_alloc (●ML [] ⋅ ◯ML [])) as (γ) "[HlogFa HlogFf]".
    { apply mono_list_both_dfrac_valid.
      by split; [done|exists []; done]. }
    iMod (own_update with "Htoks") as "[Htoks Htok]".
    { apply (auth_update_alloc _
               (to_agree <$> (<[f:=γ]>N))
               ({[f := to_agree γ]})).
      rewrite fmap_insert.
      apply alloc_singleton_local_update; [|done].
      rewrite -not_elem_of_dom. set_solver. }
    iExists (<[f := γ]>N).
    rewrite !big_opM_insert; [|rewrite -not_elem_of_dom; set_solver..].
    iFrame "#∗".
    iModIntro.
    iSplit; [ iPureIntro; set_solver |].
    rewrite -{1}Qp_half_half -dfrac_op_own mono_list_auth_dfrac_op.
    iDestruct "HlogFa" as "[$ $]".
  Qed.

End Alloc_resources.
