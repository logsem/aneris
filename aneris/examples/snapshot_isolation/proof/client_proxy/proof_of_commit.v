From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list.
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
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model kvs_serialization rpc_user_params.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     resource_algebras server_resources proxy_resources global_invariant wrappers.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Section Commit_Proof.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params clients γKnownClients γGauth γGsnap γT).
  Import snapshot_isolation_code_api.

  Definition commit_spec_internal {MTR : MTS_resources} : iProp Σ :=
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    is_connected γGsnap γT γKnownClients c sa -∗
    @make_request_spec _ _ _ _ MTC _ -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
         ConnectionState_def γKnownClients c sa (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, OwnMemKey_def γGauth γGsnap k h) ∗
        ([∗ map] k ↦ p ∈ mc,
           ownCacheUser γKnownClients k c p.1 ∗ key_upd_status γKnownClients c k p.2) >>>
      SI_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
         ConnectionState_def γKnownClients c sa CanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
          ([∗ map] k↦ h;p ∈ m; mc,
            OwnMemKey_def γGauth γGsnap k (commit_event p h) ∗ Seen_def γGsnap k (commit_event p h))) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ h ∈ m, OwnMemKey_def γGauth γGsnap k h ∗ Seen_def γGsnap k h)) >>>.


  Lemma commit_spec_internal_holds {MTR : MTS_resources}  :
    Global_Inv clients γKnownClients γGauth γGsnap γT  ⊢ commit_spec_internal.
  Proof.
    iIntros "#Hinv". 
    iIntros (c sa E HE) "#Hlk #Hspec %Φ !# Hsh".
    rewrite /SI_commit /= /commit.
    wp_pures.
    unfold is_connected.
    iDestruct "Hlk" as (lk cst l γCst γlk γS γA γCache) "(-> & Hcc1 & Hlk)".
    wp_pures.
    wp_apply (acquire_spec with "Hlk").
    iIntros (?) "(-> & Hlkd & HisC)".
    unfold is_connected_def.
    iDestruct "HisC" as (s sv) "(Hl & Hcr & Hdisj)".
    wp_pures.
    wp_load.
    iDestruct "Hdisj" as "[Hst|Habs]".
    { 
      iDestruct "Hst" as (-> ->) "(Hgh & Hst)".
      wp_pure _.
      wp_bind (Lam _ _).
      wp_apply (aneris_wp_atomic _ _ (E)).
      iMod "Hsh" as (m ms mc) "[(Hcst & _) Hclose]".
      iDestruct "Hcst" as (sp) "(Hcst & %Heq)".
      iDestruct "Hcst" as (? ? ? ? ? ? ->) "(#Habs1 & Hsp)".
      destruct sp; simplify_eq /=.
      iDestruct (client_connected_agree with "[$Hcc1][$Habs1]") as "%Heq'".
      simplify_eq /=.
      by iDestruct (own_valid_2 with "Hst Hsp") as %?.
    }
    iDestruct "Habs" as (ts Msnap cache_updatesL cache_updatesV cache_updatesM cacheM) 
      "(-> & -> & (Hcoh & Hvalid & Hismap & Htime & Hseen & Hupd & Hauth & Htok))".
    wp_pures.
    wp_load.
    wp_pures.
    wp_op; first apply bin_op_eval_eq_val.
    case_bool_decide as Heq; wp_pures.
    - wp_bind (_ <- _)%E.
      wp_apply (aneris_wp_atomic _ _ (E)).
      iMod "Hsh" as (m ms mc) "((Hcon & %Hdomm & %Hdomms & Hkey & Hcache) & Hclose)".
      iModIntro.
      wp_store.
      iSpecialize ("Hclose" $! true).
      unfold is_coherent_cache.
      iMod ("Hclose" with "[Htok Hkey Hcache]") as "HΦ".
      + iSplitR.
        {
          unfold ConnectionState_def, connection_state.
          iExists PSCanStart.
          iSplitL; last by iPureIntro.
          iExists _, _, _, _, _, _.
          iSplitR; first by iPureIntro.
          iFrame "∗#".
        }
        iLeft.
        iSplitR; first by iPureIntro.
        admit. (* Case from mattermost *)
      + iModIntro.
        wp_pures.
        wp_apply (release_spec with "[$Hlk $Hlkd Hcon Hl Hcr Hauth]").
        {
          iExists _, _.
          iFrame.
          iLeft.
          iSplit; first by iPureIntro.
          iSplit; first by iPureIntro.
          iDestruct "Hcon" as (sp) "(Hst' & %Heq')".
          iDestruct "Hst'" as (???????) "(#Hcc2 & Hst')".
          destruct sp; simplify_eq /=.
          admit. (* TODO *)
        }
        iIntros (? ->).
        by wp_pures.
    - (* TODO: the non-empty cache case *) admit.


(* 
    {
      wp_store.
      wp_pures.
      wp_apply (release_spec with "[$Hlk $Hlkd]").
    }
    
    wp_pures.
    case_bool_decide.
    destruct ().
    set (rd := (inr (inr (E, ts, cache_updatesM, cacheM, Msnap, ⌜True⌝%I,
                           (λ b, ghost_map.ghost_map_auth γCache 1 ∅ ∗
                               CanStartToken γS ∗ Φ #())%I))) : @ReqData Σ).
    wp_apply ("Hspec" $! _ _ _ rd with "[]").
    { iSplit.
      - iPureIntro.
        simplify_eq /=.
        eapply sum_is_ser_valid.
        rewrite /sum_is_ser.
        eexists (InjLV #())%V, _. right.
        split; first eauto.
        simpl. split; last done.
        eexists #(), _.
        left.
        split_and!; try done.
      - rewrite /MTS_handler_pre /= /ReqPre.
        iSplit; first done.
        iRight.
        iLeft.
        iExists E, _, _.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iSplit; first done.
        iIntros "_".
        iMod "Hsh" as (m) "[(Hst' & Hpts) Hclose]".
        iModIntro.
        iExists m.
        iFrame.
        iNext.
        iIntros (ts M HmM) "(%Hvsn & Hts & Hpts)".
        iDestruct "Hst'" as (sp) "(Hst' & %Heq')".
        iDestruct "Hst'" as (???????) "(#Hcc2 & Hst')".
        destruct sp; simplify_eq /=.
        iDestruct (client_connected_agree with "[$Hcc1][$Hcc2]") as "%Heq2".
        simplify_eq /=.
        iExists ts, M, (cacheM_from_Msnap M).
        iFrame.
        iAssert (([∗ map] k↦h ∈ M, ownMemSeen γGsnap k h)%I) as "#Hseen1".
        { iApply (big_sepM_mono with "[$Hpts]").
          iIntros (???) "(H1 & H2)".
          by iDestruct "H1" as "(H11 & H12)". }
        iAssert (([∗ map] k↦h ∈ ((λ h : list write_event, to_hist h) <$> M),
              Seen_def γGsnap k h)%I) as "#Hseen2".
        { rewrite /Seen_def.
          iApply big_sepM_fmap.
          iApply (big_sepM_mono with "[$Hseen1]").
          iIntros (???) "Hs". by eauto. }
        iMod (ghost_map.ghost_map_insert_big (cacheM_from_Msnap M) with "[$Hgh]")
          as "(Hgh & Hcpts)".
        { apply map_disjoint_empty_r. }
        replace ((cacheM_from_Msnap M) ∪ ∅)
          with (cacheM_from_Msnap M)
               by by rewrite right_id_L.
        iApply fupd_frame_l; iFrame.
        iApply fupd_frame_l; iSplit; first done.
        iApply fupd_frame_l; iSplit.
        { iPureIntro; by apply is_coherent_cache_start. }
        iApply fupd_frame_l; iSplit; first done.
        iApply fupd_frame_l; iSplit.
        iFrame "#".
        iApply "Hclose".
        iSplitL "Hst".
        { iExists (PSActive M).
          iSplit; last done.
          iExists _, _, _, _, _, _.
          eauto with iFrame. }
        iSplitL "Hpts".
        { iApply big_sepM_fmap.
          iApply (big_sepM_mono with "[$Hpts]").
          iIntros (???) "(Hs & %Ht)".
          iExists _. by eauto. }
        iSplitL.
        { iApply (own_cache_user_from_ghost_map_elem_big γKnownClients γT
                   with "[$Hcc1][$Hcpts]"). }
        iFrame "#". }
    iIntros (repd repv) "(Hcr & Hpost)".
    iDestruct "Hpost" as "(_ & [Habs|Hpost])";
      first by iDestruct "Habs" as (? ? ? ? ?) "Habs".
    iDestruct "Hpost" as "[Hpost | Habs]";
      last by iDestruct "Habs" as (? ? ? ? ? ? ? ? ?) "Habs".
    iDestruct "Hpost" as (? ? ? ? ? Heq1 Heq2 Heq3) "Hpost".
    simplify_eq /=.
    wp_pures.
    wp_apply (@wp_map_empty Mdl Σ _ Key _ _ _ val _ with "[//]").
    iIntros (mv Hmv).
    wp_alloc cm as "Hc".
    wp_pures.
    wp_store.
    iDestruct "Hpost"
      as (t Msnap ?) "(Htk & Hgh & Htm & -> & %Hcoh & %Hval & Hseen & Hpost)".
    wp_apply (release_spec with "[$Hlkd $Hlk Hl Hcr Hgh Htk Hseen Htm Hc]").
    {
      iExists (PSActive Msnap), (InjRV (#t, #cm))%V.
      iFrame "Hl Hcr".
      iRight.
      iExists _, _, _, _, ∅, _.
      iFrame "#∗".
      iPureIntro.
      split_and!; try done. }
    by iIntros (? ->). *)
  Admitted.

End Commit_Proof.
