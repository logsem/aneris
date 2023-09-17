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

Section Start_Proof.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTss: gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params clients γKnownClients γGauth γGsnap γT γTss).
  Import snapshot_isolation_code_api.

  Definition start_spec_internal {MTR : MTS_resources} : iProp Σ :=
    ∀ (c : val) (sa : socket_address)
       (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    is_connected γGsnap γT γTss γKnownClients c sa -∗
    @make_request_spec _ _ _ _ MTC _ -∗
    <<< ∀∀ (m : gmap Key (list val)),
        ConnectionState_def γKnownClients γGsnap c sa CanStart ∗
       [∗ map] k ↦ h ∈ m, OwnMemKey_def γGauth γGsnap k h >>>
      SI_start c @[ip_of_address sa] E
    <<<▷ RET #();
        ConnectionState_def γKnownClients γGsnap c sa (Active m) ∗
       ([∗ map] k ↦ h ∈ m, OwnMemKey_def γGauth γGsnap k h) ∗
       ([∗ map] k ↦ h ∈ m,
          ownCacheUser γKnownClients k c (last h) ∗
          key_upd_status γKnownClients c k false) ∗
       ([∗ map] k ↦ h ∈ m, Seen_def γGsnap k h)>>>.

  Lemma start_spec_internal_holds {MTR : MTS_resources}  :
     Global_Inv clients γKnownClients γGauth γGsnap γT γTss ⊢ start_spec_internal.
  Proof.
    iIntros "#Hinv".
    iIntros (c sa E HE) "#Hlk #Hspec %Φ !# Hsh".
    rewrite /SI_start /= /start.
    wp_pures.
    iDestruct "Hlk" as (lk cst l γCst γlk γS γA γCache γMsnap) "(-> & Hcc1 & Hlk)".
    wp_pures.
    wp_apply (acquire_spec with "Hlk").
    iIntros (?) "(-> & Hlkd & HisC)".
    iDestruct "HisC" as (sv) "(Hl & Hcr & Hdisj)".
    wp_pures.
    wp_load.
    iDestruct "Hdisj" as "[Hst|Habs]"; last first.
    { iDestruct "Habs" as (? ? ? ? ? ? ->) "Habs".
      wp_pure _.
      wp_bind (Lam _ _).
      wp_apply (aneris_wp_atomic _ _ (E)).
      iMod "Hsh" as (m) "[(Hcst & _) Hclose]".
      iDestruct "Habs" as (? ? ? ?) "(? & ? & ? & ? & Habs)".
      iDestruct "Hcst" as (sp) "(Hcst & %Heq)".
      iDestruct "Hcst" as (? ? ? ? ? ? ? ->) "(#Habs1 & Hsp)".
      destruct sp; simplify_eq /=.
      iDestruct (client_connected_agree with "[$Hcc1][$Habs1]") as "%Heq'".
      simplify_eq /=.
      iDestruct "Habs" as "(_ & Habs)".
      by iDestruct (own_valid_2 with "Habs Hsp") as %?. }
    iDestruct "Hst" as (->) "(Hgh & Hsnap & Hst)".
    wp_pures.
    set (rd := (inr (inl (E, ⌜True⌝%I,
                           (λ tsv,
                        ∃ ts Msnap cacheM,
                        isActiveToken γA ∗
                        ghost_map.ghost_map_auth γCache 1 cacheM ∗
                        ownMsnapAuth γMsnap Msnap ∗
                        ownTimeSnap γT γTss ts ∗
                        ⌜tsv = #ts⌝ ∗
                        ⌜is_coherent_cache ∅ cacheM Msnap⌝ ∗
                        ⌜kvs_valid_snapshot Msnap ts⌝ ∗
                        ([∗ map] k↦h ∈ Msnap, ownMemSeen γGsnap k h) ∗
                        Φ #())%I))) : @ReqData Σ).
    wp_apply ("Hspec" $! _ _ _ rd with "[$Hcr Hsh Hst Hgh Hsnap]").
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
        iIntros (ts M HmM) "(%Hvsn & Hser & Hts & Hpts & #Hseen)".
        iDestruct "Hst'" as (sp) "(Hst' & %Heq')".
        iDestruct "Hst'" as (???????->) "(#Hcc2 & Hst')".
        destruct sp; simplify_eq /=.
        iDestruct (client_connected_agree with "[$Hcc1][$Hcc2]") as "%Heq2".
        simplify_eq /=.
        iExists ts, M, (cacheM_from_Msnap M).
        iFrame.
        iAssert (([∗ map] k↦h ∈ ((λ h : list write_event, to_hist h) <$> M),
              Seen_def γGsnap k h)%I) as "#Hseen2".
        { rewrite /Seen_def.
          iApply big_sepM_fmap.
          iApply (big_sepM_mono with "[$Hseen]").
          iIntros (???) "Hs". by eauto. }
        iMod (ghost_map.ghost_map_insert_big (cacheM_from_Msnap M) with "[$Hgh]")
          as "(Hgh & Hcpts)".
        { apply map_disjoint_empty_r. }
        replace ((cacheM_from_Msnap M) ∪ ∅)
          with (cacheM_from_Msnap M)
               by by rewrite right_id_L.
        iApply fupd_frame_l; iFrame.
        rewrite /ownMsnapFull.
        iMod ((@ghost_map.ghost_map_insert_big _ _ (list write_event) _ _ _ γMsnap0 ∅ M) with "[$Hsnap]")
          as "((HghM1 & HghM2) & HcptsM)"; first by apply map_disjoint_empty_r.
        replace (M ∪ ∅)
          with M
               by by rewrite right_id_L.
        iFrame.
        iApply fupd_frame_l.
        iSplit; first done.
        iApply fupd_frame_l; iSplit.
        { iPureIntro; by apply is_coherent_cache_start. }
        iApply fupd_frame_l; iSplit; first done.
        iApply fupd_frame_l; iSplit.
        iFrame "#∗".
        iApply "Hclose".
        iSplitL "Hst HghM1".
        { iExists (PSActive M).
          iSplit; last done.
          iExists _, _, _, _, _, _, _.
          iSplit; first done.
          iFrame "#∗". }
        iFrame "#∗".
        iApply (own_cache_user_from_ghost_map_elem_big
                   with "[$Hser][$Hcc1][$Hcpts]"). }
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
      as (t Msnap ?) "(Htk & Hgh & Hmfr & Htm & -> & %Hcoh & %Hval & Hseen & Hpost)".
    wp_apply (release_spec with "[$Hlkd $Hlk Hl Hcr Hgh Htk Hseen Htm Hc Hmfr]").
    {
      iExists (InjRV (#t, #cm))%V.
      iFrame "Hl Hcr".
      iRight.
      iExists _, _, _, _, _, _.
      iFrame "#∗".
      iPureIntro.
      split_and!; try done. }
    by iIntros (? ->).
  Qed.

End Start_Proof.
