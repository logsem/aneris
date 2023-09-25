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
                     clients γKnownClients γGauth γGsnap γT γTss).
  Import snapshot_isolation_code_api.

  Lemma check_at_key_spec (k : Key) (ts tc : nat) (tss : gset nat) (kvs cache : val) 
    (vl : list write_event)
    (cache_updatesM m : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap M : gmap Key (list write_event)) :
    is_coherent_cache cache_updatesM cache_logicalM Msnap →
    is_map (InjRV cache) cache_updatesM →
    is_map kvs m →
    kvsl_valid m M tc tss →
    M !! k = Some vl → 
    {{{ ⌜True⌝ }}}
      check_at_key #k #ts #tc $vl @[ip_of_address MTC.(MTS_saddr)]
    {{{ (br : bool), RET #br; 
      (⌜br = true⌝ ∗ ⌜match cache_logicalM !! k : option (option val * bool) with
                      | Some p =>
                        let (_, b) := p in
                        if b then bool_decide (M !! k = Msnap !! k) else true
                      | None => true
                      end⌝) 
      ∨ (⌜br = false⌝ ∗ ⌜is_Some (cache_logicalM !! k)⌝ ∗ ⌜M !! k ≠ Msnap !! k⌝)
    }}}.
  Proof.
  Admitted.

  Lemma map_forall_spec (ts tc : nat) (tss : gset nat) (kvs cache : val) 
    (cache_updatesM m : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap M : gmap Key (list write_event)) :
    is_coherent_cache cache_updatesM cache_logicalM Msnap →
    is_map (InjRV cache) cache_updatesM →
    is_map kvs m →
    kvsl_valid m M tc tss →
    {{{ ⌜True⌝ }}}
      map_forall (λ: "k" "_v",
                    let: "vlsto" := map_lookup "k" kvs in
                    let: "vs" := 
                      if: "vlsto" = InjL #()
                      then InjL #()
                      else network_util_code.unSOME "vlsto" 
                    in
                    check_at_key "k" #ts #(tc + 1) "vs")%V (InjRV cache)
                    @[ip_of_address MTC.(MTS_saddr)]
    {{{ (m_current : gmap Key (list val)) (b : bool), RET #b; 
      ⌜dom m_current = dom Msnap⌝ ∗
      ⌜m_current = (λ hw, to_hist hw) <$> filter (λ k, k.1 ∈ dom m_current) M⌝ ∗
      ((⌜b = true⌝ ∗ ⌜can_commit m_current ((λ hw, to_hist hw) <$> Msnap) cache_logicalM⌝) 
      ∨ (⌜b = false⌝ ∗ ⌜¬ can_commit m_current ((λ hw, to_hist hw) <$> Msnap) cache_logicalM⌝)) }}}.
  Proof.
  Admitted.

  Lemma update_kvs_spec (kvs cacheV : val) (tc : nat) (tss : gset nat)
    (cache_updatesM m : gmap Key val)
    (cache_logicalM : gmap Key (option val * bool))
    (Msnap M : gmap Key (list write_event)) 
    (cache : gmap Key SerializableVal) :
    (∀ k v, (∃ sv, cache !! k = Some sv ∧ sv.(SV_val) = v) ↔ cache_updatesM !! k = Some v) →
    is_coherent_cache cache_updatesM cache_logicalM Msnap →
    is_map (InjRV cacheV) cache_updatesM →
    is_map kvs m →
    kvsl_valid m M tc tss →
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
        wp_apply (map_forall_spec ts T tss' kvsV v cache_updatesM m cache_logicalM Msnap M); try eauto.
        {
          by eexists _.
        }
        iIntros (m_current b) "(%H_dom_eq & %H_curr_eq & [(-> & %H_com_status) | (-> & %H_com_status)])".
        * (* Valid case when we know commit is successful *)
          wp_pures.
          wp_store.
          pose proof (cache_updatesM_to_cache _ Hall) as [cache H_cache].
          pose proof (cache_dom_eq _ _ H_cache) as H_cache_eq.
          pose proof Hcoh as ( _ & _ & H_sub & _).
          rewrite -H_cache_eq in H_sub.
          unfold snapshot_isolation_code.update_kvs.
          wp_apply (update_kvs_spec kvsV v T tss' cache_updatesM m cache_logicalM Msnap M cache); try eauto.
          {
            by eexists _.
          }
          iIntros (kvs_updated) "%H_map_up".
          wp_bind (Store _ _).
          wp_apply (aneris_wp_atomic _ _ E).
          (* Viewshift and opening of invariant *)
          iMod ("Hshift" with "[$HP]") as (m_current_client) "(%H_dom_eq_cl & Hkeys & Hpost)".
          iInv KVS_InvName as (Mg Tg Tssg gMg) 
            ">(HmemGlob & HtimeGlob & HtimeStartsGlob & Hccls & %Hdom & %HkvsValid)".
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
          assert (m_current = m_current_client) as <-.
          {
            rewrite H_curr_eq Hmap_eq.
            by rewrite H_dom_eq_cl H_dom_eq.
          }
          (* Update of logical ressources *)
          iDestruct (commit_logical_update clients γKnownClients γGauth γGsnap γT γTss
            ts T Tssg cache_logicalM cache_updatesM cache M Msnap m_current) as "H_upd".
          iDestruct ("H_upd" with "[] [] [] [] [] [] [] [$HmemMono] [$HtimeGlob]
            [$HtimeLoc] [$HmemGlobAuth] [$HmemLoc] [$Hkeys]") as 
            ">(HtimeGlob & HtimeLoc & HmemGlob & HmemLoc & HmemMono & Hkeys)"; try done.
          (* Closing of invaraint *)
          iSplitL "HtimeGlob HmemGlob Hccls HmemMono HtimeStartsGlob".
          {
            iModIntro.
            iNext.
            iExists (update_kvs M cache (T + 1)), (T + 1), Tssg, gMg.
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
            by iFrame.
          }
          (* Proceding with proof after viewshift *)
          iMod "HQ".
          iModIntro.
          wp_pures.
          wp_apply (release_spec with
            "[$Hlock $Hlk HkvsL HvnumL HmemLoc HtimeLoc]").
          {
            iExists kvs_updated, (T + 1), tss', 
              (update_kvsl m cache (T + 1)), (update_kvs M cache (T + 1)).
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
        * (* Absurd case when we know commit is successful *)
          rewrite H_curr_eq in H_com_status.
          by rewrite H_dom_eq in H_com_status.
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
          wp_apply (map_forall_spec ts T tss' kvsV v cache_updatesM m cache_logicalM Msnap M); try eauto.
          {
            by eexists _.
          }
          iIntros (m_current' b) "(%H_dom_eq & %H_curr_eq & [(-> & %H_com_status) | (-> & %H_com_status)])".
          -- (* Absurd case when we know commit is not successful *)
             rewrite H_curr_eq in H_com_status.
             by rewrite H_dom_eq in H_com_status.
          -- (* Valid case when we know commit is not successful *)
             wp_pures.
             wp_apply (release_spec with
               "[$Hlock $Hlk HkvsL HvnumL HmemLoc HtimeLoc]").
             {
               iExists kvsV, T, tss', m, M.
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
  Qed.

End Proof_of_commit_handler.
