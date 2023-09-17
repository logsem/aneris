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
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model kvs_serialization rpc_user_params.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     resource_algebras server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
Section Proof_of_commit_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTss γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT).
  Import snapshot_isolation_code_api.

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
    server_lock_inv γGauth γT γTss γlk lk kvs vnum -∗
    Global_Inv clients γKnownClients γGauth γGsnap γT γTss -∗
    ownTimeSnap γT γTss ts -∗
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
                Seen_def γGsnap k (commit_event p h)) ∨ ⌜
              b = false⌝ ∗
              ⌜¬ can_commit m_current
                    ((λ h : list write_event, to_hist h) <$> Msnap)
                    cache_logicalM⌝ ∗
              ([∗ map] k↦h ∈ m_current, OwnMemKey_def γGauth γGsnap k h ∗
                Seen_def γGsnap k h) ={E,⊤}=∗ Q #b)) -∗
    (∀ (repv : val) (repd : RepData),
         ⌜sum_valid_val (option_serialization KVS_serialization)
            (sum_serialization int_serialization bool_serialization) repv⌝ ∗
         ReqPost clients γKnownClients γGauth γGsnap γT γTss repv reqd repd -∗
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
    iIntros (Hreqd Hsub Hmap Hcoh Hvalid Hall) "#Hlk #HGlobInv #Htime #Hseen HP Hshift HΦ".
    wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#".
    iIntros (?) "(-> & Hlock & Hlkres)".
    wp_pures.
    unfold lkResDef.
    iDestruct "Hlkres"
      as (kvsV T tss' m M Hmap' Hvalid')
           "(%Hser & HmemLoc & HtimeLoc & #HtimeSnaps & HkvsL & HvnumL)".
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
    - wp_bind (Load _).
      wp_apply (aneris_wp_atomic _ _ E).
      iMod ("Hshift" with "[$HP]") as (m_current HdomEq) "(Hkeys & Hpost)".
      iModIntro.
      wp_load.
      iDestruct ("Hpost" with "[Hkeys]") as "HQ".
      + iLeft.
        iSplitR; first done.
        destruct l; inversion HcmapEq as [HvEq].
        simpl in HcupdEq.
        simplify_eq.
        destruct Hcoh as (Hdom & _ & _ & _ & Hcoh1 & _ & Hcoh2).
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
      + iMod "HQ".
        iModIntro.
        wp_pures.
        wp_apply (release_spec with
          "[$Hlock $Hlk HkvsL HvnumL HmemLoc HtimeLoc]").
        {
          iExists kvsV, T, tss', m, M.
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
    - wp_load.
      wp_pures.
      admit.
  Admitted.

End Proof_of_commit_handler.
