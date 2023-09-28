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
     Require Import utils model kvs_serialization rpc_user_params.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     resource_algebras server_resources proxy_resources global_invariant wrappers.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Section Commit_Proof.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params clients γKnownClients γGauth γGsnap γT γTrs).
  Import snapshot_isolation_code_api.


  Lemma cache_inversion (mc : gmap Key (option val * bool)) sa lk cst l (γCst γA γS γlk γCache γMsnap : gname) :
    client_connected γKnownClients sa γCst γA γS γlk γCache γMsnap
    ⊢  [∗ map] k↦p ∈ mc, ((∃ (sa0 : socket_address)
                             (v : val) (γCst0 γA0 γS0 γlk0 γCache0
                                              γMsnap0 : gname)
                             (b : bool),
                              ⌜(#sa, (lk, (cst, #l)))%V = (#sa0, v)%V⌝ ∗
                                client_connected γKnownClients sa0 γCst0
                                                 γA0 γS0 γlk0 γCache0 γMsnap0 ∗
                             ghost_map.ghost_map_elem γCache0 k
                                                      (DfracOwn (1 / 2)) (
                                                        p.1, b) ∗
                             ⌜match p.1 with
                              | Some w => KVS_Serializable w
                              | None => b = false
                              end⌝) ∗
                         key_upd_status γKnownClients (#sa, (lk, (cst, #l))) k p.2) -∗
                      (ghost_map.ghost_map_elem γCache k (DfracOwn (1 / 2)) p ∗
                         ⌜match p.1 with
                          | Some w => KVS_Serializable w
                          | None => p.2 = false
                          end⌝ ∗
                         ghost_map.ghost_map_elem γCache k (DfracOwn (1 / 2)) p)%I.
  Proof.
    iIntros "#Hcc1".
    iApply big_sepM_intro.
    iIntros "!#".
    iIntros (k p Hkp) "(H & Hk)".
    iDestruct "H" as (? ? ? ? ? ? ? ? b Heq) "(#Hcc2 & Hm1 & %Hyp)".
    simplify_eq /=.
    iDestruct (client_connected_agree with "[$Hcc1][$Hcc2]") as "%Heq'".
    simplify_eq /=.
    iDestruct "Hk" as (? ? ? ? ? ? ? ? ? Heq) "(#Hcc3 & Hm2 & %Hcond)".
    simplify_eq /=.
    iDestruct (client_connected_agree with "[$Hcc1][$Hcc3]") as "%Heq''".
    simplify_eq /=.
    iDestruct (@ghost_map.ghost_map_elem_combine with "[$Hm2][$Hm1]") as "((Hm1 & Hm2) & %Heq)".
    simplify_eq /=.
    destruct p. by iFrame.
  Qed.

  Definition commit_spec_internal {MTR : MTS_resources} : iProp Σ :=
   ∀ (c : val) (sa : socket_address)
     (E : coPset),
    ⌜↑KVS_InvName ⊆ E⌝ -∗
    is_connected γGsnap γT γTrs γKnownClients c sa -∗
    @make_request_spec _ _ _ _ MTC _ -∗
    <<< ∀∀ (m ms: gmap Key Hist)
           (mc : gmap Key (option val * bool)),
         ConnectionState_def γKnownClients γGsnap c sa (Active ms) ∗
        ⌜dom m = dom ms⌝ ∗ ⌜dom ms = dom mc⌝ ∗
        ([∗ map] k ↦ h ∈ m, OwnMemKey_def γGauth γGsnap k h) ∗
        ([∗ map] k ↦ p ∈ mc,
           ownCacheUser γKnownClients k c p.1 ∗ key_upd_status γKnownClients c k p.2) >>>
      SI_commit c @[ip_of_address sa] E
    <<<▷∃∃ b, RET #b;
         ConnectionState_def γKnownClients γGsnap c sa CanStart ∗
        (** Transaction has been commited. *)
        ((⌜b = true⌝ ∗ ⌜can_commit m ms mc⌝ ∗
          ([∗ map] k↦ h;p ∈ m; mc,
            OwnMemKey_def γGauth γGsnap k (commit_event p h) ∗ Seen_def γGsnap k (commit_event p h))) ∨
        (** Transaction has been aborted. *)
         (⌜b = false⌝ ∗ ⌜¬ can_commit m ms mc⌝ ∗
           [∗ map] k ↦ h ∈ m, OwnMemKey_def γGauth γGsnap k h ∗ Seen_def γGsnap k h)) >>>.

  Lemma commit_spec_internal_holds {MTR : MTS_resources}  :
    Global_Inv clients γKnownClients γGauth γGsnap γT γTrs ⊢ commit_spec_internal.
  Proof.
    iIntros "#Hinv".
    iIntros (c sa E HE) "#Hlk #Hspec %Φ !# Hsh".
    rewrite /SI_commit /= /commit.
    wp_pures.
    unfold is_connected.
    iDestruct "Hlk" as (lk cst l γCst γlk γS γA γCache γMsnap) "(-> & Hcc1 & Hlk)".
    wp_pures.
    wp_apply (acquire_spec with "Hlk").
    iIntros (?) "(-> & Hlkd & HisC)".
    unfold is_connected_def.
    iDestruct "HisC" as (sv) "(Hl & Hcr & Hdisj)".
    wp_pures.
    wp_load.
    iDestruct "Hdisj" as "[Habs|Hst]".
    {
      iDestruct "Habs" as (->) "(Hgh & Hst & Htk')".
      wp_pure _.
      wp_bind (Lam _ _).
      wp_apply (aneris_wp_atomic _ _ (E)).
      iMod "Hsh" as (m ms mc) "[(Hcst & _) Hclose]".
      iDestruct "Hcst" as (sp) "(Hcst & %Heq)".
      iDestruct "Hcst" as (? ? ? ? ? ? ? ->) "(#Habs1 & Hsp)".
      destruct sp; simplify_eq /=.
      iDestruct "Hsp" as "(Hsp & _)".
      iDestruct (client_connected_agree with "[$Hcc1][$Habs1]") as "%Heq'".
      simplify_eq /=.
      by iDestruct (own_valid_2 with "Htk' Hsp") as %?.
    }
    iDestruct "Hst" as (ts Msnap Msnap_full cache_updatesL cache_updatesV cache_updatesM cacheM)
      "( -> & (%Hcoh & %Hser & %Hvalid & %Hismap & %Hsub & 
              #Htime & #Hseen & #Hfrag & Hupd & Hauth & HauthMsnap & Htok))".
    wp_pures.
    wp_load.
    wp_pures.
    wp_op; first apply bin_op_eval_eq_val.
    case_bool_decide as Heq; wp_pures.
    (* Case 1: cache is empty (read-only transaction). *)
    - wp_bind (_ <- _)%E.
      wp_apply (aneris_wp_atomic _ _ (E)).
      iMod "Hsh" as (m ms mc) "((Hcon & %Hdomm & %Hdomms & Hkeys & Hcache) & Hclose)".
      iModIntro.
      wp_store.
      iSpecialize ("Hclose" $! true).
      unfold is_coherent_cache.
      rewrite /is_map in Hismap.
      destruct Hismap as (lm & Hlm1 & Hlm2 & Hlm3).
      simplify_eq /=.
      destruct lm as [|? lm_abs]; last done.
      simplify_eq /=.
      iDestruct (big_sepM_wand with "[$Hcache][]") as "Hcache".
      by iApply cache_inversion.
      iDestruct (@ghost_map.ghost_map_lookup_big with "[$Hauth][Hcache]") as "%HsubMap".
      iApply (big_sepM_mono with "[$Hcache]").
      { iIntros (k p Hkp) "(H1 & (%Heq & H2))".
        by iSplitL "H1"; iFrame "∗". }
      iAssert (⌜∀ k vo b, mc !! k = Some (vo, b) → cacheM !! k = mc !! k⌝%I) as "%HmcEq0".
      { iPureIntro. intros k vo b Hin.
        by destruct (lookup_weaken mc cacheM k (vo, b) Hin HsubMap). }
      iAssert (⌜∀ k v b, mc !! k = Some (Some v, b) -> b = false⌝%I) as "%HmcEq1".
      {
        iPureIntro.
        intros k v b H_pure_eq_mc.
        destruct Hcoh as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7 & Hc8).
        destruct b; last done.
        specialize (HmcEq0 k (Some v) true H_pure_eq_mc).
        rewrite -HmcEq0 in H_pure_eq_mc.
        specialize (Hc6 k v) as (_ & Habs).
        by apply Habs in H_pure_eq_mc.
      }
      iAssert (⌜∀ k vo b h, mc !! k = Some (vo, b) →
                           m !! k = Some h →
                          commit_event (vo, b) h = h⌝%I) as "%HmcEq2".
      {
        iPureIntro.
        intros k vo b h H_pure_eq_mc H_pure_eq_m.
        destruct vo; last done.
        by apply (HmcEq1 _ _ _) in H_pure_eq_mc as ->.
      }
      iMod ("Hclose" with "[Htok Hkeys]") as "HΦ".
      + iSplitL "Htok".
        {
          unfold ConnectionState_def, connection_state.
          iExists PSCanStart.
          iSplitL; last by iPureIntro.
          iExists _, _, _, _, _, _, _.
          iSplitR; first by iPureIntro.
          iFrame "∗#".
        }
        iLeft.
        iSplit; first done.
        iSplit.
        rewrite /can_commit.
        case_bool_decide as Hb; first done.
        iPureIntro. apply Hb.
        intros k Hk.
        destruct (mc !! k) as [(vo,[|])|] eqn:Hmc; last done; last done.
        { destruct vo.
          - by specialize (HmcEq1 k v true Hmc).
          -   destruct Hcoh as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7 & Hc8).
              assert (cacheM !! k = Some (None, true)) as Hcm.
              { by eapply map_subseteq_spec. }
              by destruct (Hc8 k None Hcm). }
        iDestruct (big_sepM2_sepM_2 _ ((λ k h, True)%I) _ mc with "[$Hkeys] []") as "Hkeys".
        * intros k.
          split; intros H_some.
          -- apply elem_of_dom in H_some.
             rewrite Hdomm in H_some.
             rewrite Hdomms in H_some.
             by apply elem_of_dom in H_some.
          -- apply elem_of_dom in H_some.
            rewrite -Hdomms in H_some.
            rewrite -Hdomm in H_some.
            by apply elem_of_dom in H_some.
        * by iApply (big_sepM_dup).
        * iApply big_sepM2_mono; last done.
          iIntros (k h p H_some_eq_m H_some_eq_mc) "(H_key & _)".
          destruct p.
          apply (HmcEq2 _ _ _ _ H_some_eq_mc) in H_some_eq_m as ->.
          unfold OwnMemKey_def.
          iDestruct "H_key" as (hw) "(H_key & %H_key_eq)".
          unfold ownMemUser.
          iDestruct "H_key" as "(H_key & #H_key_seen)".
          iSplit.
          {
             iExists hw.
             iFrame "#∗".
             by iPureIntro.
          }
          {
            unfold Seen_def.
            iExists hw.
            iFrame "#".
            by iPureIntro.
          }
      + iModIntro.
        wp_pures.
        iDestruct "Hcon" as (sp) "(Hst' & %Heq')".
        iDestruct "Hst'" as (??????? Heq) "(#Hcc2 & Hst')".
        destruct sp as [|Msnap']; simplify_eq /=.
        iDestruct "Hst'" as "(Htk & #Hseen' & HauthFrag1)".
        iDestruct "HauthMsnap"  as "(HauthFrag2 & Hfict)".
        rewrite /ownMsnapFrag.
        iDestruct (client_connected_agree with "[$Hcc1][$Hcc2]") as "%Heq'".
        simplify_eq /=.
        iDestruct ((@ghost_map.ghost_map_auth_agree _ Key (list write_event))
                    with "[$HauthFrag1][$HauthFrag2]")  as "->".
        wp_apply fupd_aneris_wp.
        iDestruct (ghost_map.ghost_map_delete_big mc with "[$Hauth][Hcache]") as ">Hcache".
        { iApply (big_sepM_mono with "[$Hcache]").
          iIntros (k p H_some_mc) "(Hm1 & (%H_upd & Hm2))".
          by iSplitL "Hm1"; iFrame. }
        iDestruct (@ghost_map.ghost_map_delete_big with "[HauthFrag1 HauthFrag2][$Hfict]") as ">Hmsnap".
        { by iCombine "HauthFrag1" "HauthFrag2" as "Hauth". }
        iModIntro.
        wp_apply (release_spec with "[$Hlk $Hlkd Hl Hcr Hcache Hmsnap Htk]").
        {
          iExists _.
          iFrame.
          iLeft.
          iSplit; first by iPureIntro.
          assert (dom cacheM = dom mc) as H_dom_cacheM_mc.
          {
            destruct Hcoh as (H_dom_msnap_chacheM & _).
            set_solver.
          }
          assert (mc = cacheM) as ->.
          { apply subseteq_dom_eq; first done.
            set_solver. }
          rewrite !map_difference_diag.
          by iFrame. }
        iIntros (? ->).
        by wp_pures.
    -  set (rd := (inr (inr (E, ts, cache_updatesM, cacheM, Msnap,  ⌜True⌝%I,
                           (λ vb,
                              ghost_map.ghost_map_auth γCache 1 (∅ : gmap Key (option val * bool)) ∗
                              ownMsnapFull γMsnap  ∗
                              CanStartToken γS ∗
                              Φ vb)%I))) : @ReqData Σ).
       wp_apply ("Hspec" $! _ _ _ rd with "[$Hcr Hsh Hauth HauthMsnap Htok]").
       { iSplit.
         -  iPureIntro.
            simplify_eq /=.
            destruct Hismap as (lm & Hlm1 & Hlm2 & Hlm3).
            apply is_list_inject in Hlm2.
            simpl in Hlm2.
            unfold sum_valid_val.
            eexists.
            right.
            split; first done.
            simpl.
            unfold sum_valid_val.
            eexists.
            right.
            split; first done.
            simpl.
            unfold prod_valid_val.
            eexists _, _.
            split; first done.
            split.
            {
              simpl.
              unfold int_valid_val.
              by eexists.
            }
            simpl.
            unfold list_valid_val.
            exists ((λ p, $p) <$> lm).
            split.
            + clear Hlm1 Hlm3 Heq.
              generalize dependent cache_updatesV.
              induction lm; first done.
              intros cache_updatesV H_list.
              destruct cache_updatesV;
              [ inversion H_list as [t (Habs & _)]; first inversion Habs |
                inversion H_list as [t (Habs & _)]; first inversion Habs |
                inversion H_list as [t (Habs & _)]; first inversion Habs |
                inversion H_list as [t (Habs & _)]; first inversion Habs |
              ].
              inversion H_list as [t (H_eq & _)].
              rewrite H_eq.
              rewrite H_eq in H_list.
              rewrite fmap_cons.
              exists t.
              split; first done.
              apply IHlm.
              set_solver.
            + clear rd Hcoh Heq.
              generalize dependent cache_updatesV.
              generalize dependent cache_updatesM.
              induction lm; first intros; first set_solver.
              intros cache_updatesM Hser Hlm1 cache_updatesV Hlm2 e H_e_in.
              rewrite fmap_cons in H_e_in.
              destruct a.
              rewrite list_to_map_cons in Hlm1.
              rewrite Hlm1 in Hser.
              assert (KVS_Serializable v) as H_ser_v.
              {
                apply (Hser k v).
                apply lookup_insert.
              }
              apply elem_of_cons in H_e_in as [H_e_eq | H_e_in].
              {
                rewrite H_e_eq.
                eexists _, _.
                split_and!; try done.
                by eexists.
              }
              inversion Hlm2 as [t (H_eq_updates & H_t_list)].
              destruct cache_updatesM.
              eapply (IHlm _ (list_to_map lm)); try done.
              Unshelve.
              2 : by apply NoDup_cons_1_2 in Hlm3.
              unfold map_Forall.
              unfold map_Forall in Hser.
              intros i x H_i_x_some.
              destruct (decide (k = i)) as [H_eq_k_i | ].
              {
                exfalso.
                rewrite -H_eq_k_i in H_i_x_some.
                simpl in Hlm3.
                apply NoDup_cons_1_1 in Hlm3.
                apply elem_of_list_to_map_2 in H_i_x_some.
                apply Hlm3.
                clear Hlm3 IHlm H_eq_updates Hser Hlm1 Hlm2 H_e_in H_t_list.
                induction lm; first inversion H_i_x_some.
                destruct a as [k' v'].
                simpl.
                destruct (decide (k = k')); first set_solver.
                apply elem_of_cons.
                right.
                apply IHlm.
                apply elem_of_cons in H_i_x_some.
                destruct H_i_x_some; set_solver.
              }
              {
                eapply (Hser i x).
                rewrite -H_i_x_some.
                by apply lookup_insert_ne.
              }
         -  rewrite /MTS_handler_pre /= /ReqPre.
            iSplit; first done.
            iRight.
            iRight.
            iExists E, _, _, _, _, _, _, _.
            do 7 (iSplit; first done).
            iFrame "#∗".
            iSplit; first done.
            iIntros "_".
            iMod "Hsh" as (m ms mc) "[Hpre Hclose]".
            iDestruct "Hpre" as "(Hst & %Hdom1 & %Hdom2 & Hkeys & Hcache)".
            iModIntro.
            iExists m.
            destruct Hcoh as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7 & Hc8).
            iDestruct "Hst" as (sp) "(Hst' & %Heq')".
            iDestruct "Hst'" as (??????? Heq2) "(#Hcc2 & Hst')".
            destruct sp as [|Msnap']; simplify_eq /=.
            iDestruct "Hst'" as "(Htk & #Hseen' & HauthFrag1)".
            iDestruct "HauthMsnap"  as "(HauthFrag2 & Hfict)".
            rewrite /ownMsnapFrag.
            iDestruct (client_connected_agree with "[$Hcc1][$Hcc2]") as "%Heq'".
            simplify_eq /=.
            iDestruct ((@ghost_map.ghost_map_auth_agree _ Key (list write_event))
              with "[$HauthFrag1][$HauthFrag2]")  as "->".
            iDestruct (big_sepM_wand with "[$Hcache][]") as "Hcache".
            by iApply cache_inversion.
            iDestruct (@ghost_map.ghost_map_lookup_big with "[$Hauth][Hcache]") as "%HsubMap".
            iApply (big_sepM_mono with "[$Hcache]").
            { iIntros (k p Hkp) "(H1 & (%Heq' & H2))".
              by iSplitL "H1"; iFrame "∗". }
            iSplit; first by iPureIntro; set_solver.
            iFrame.
            iNext.
            iIntros (b) "Hpost".
            iDestruct (ghost_map.ghost_map_delete_big mc with "[$Hauth][Hcache]") as ">Hcache".
            { iApply (big_sepM_mono with "[$Hcache]").
              iIntros (k p H_some_mc) "(Hm1 & (%H_upd & Hm2))".
              iSplitL "Hm1"; iFrame. }
            iDestruct (@ghost_map.ghost_map_delete_big
                        with "[HauthFrag1 HauthFrag2][$Hfict]") as ">Hmsnap".
            { by iCombine "HauthFrag1" "HauthFrag2" as "Hauth". }
            assert (dom cacheM = dom mc) as H_dom_cacheM_mc by set_solver.
            assert (mc = cacheM) as ->.
            { apply subseteq_dom_eq; first done.
              set_solver. }
            rewrite !map_difference_diag.
             iFrame.
             iApply "Hclose".
             iFrame.
             iExists PSCanStart.
             simplify_eq /=.
             iSplit; last done.
             iExists _, _, _, _, _, _, _. by iFrame "#∗". }
       iIntros (repd repv) "(Hcr & Hpost)".
       iDestruct "Hpost" as "(_ & [Habs|Hpost])";
         first by iDestruct "Habs" as (? ? ? ? ?) "Habs".
       iDestruct "Hpost" as "[Habs | Hpost]";
         first by iDestruct "Habs" as (? ? ? ? ? ? ?) "Habs".
       iDestruct "Hpost" as (? ? ? ? ? ? ? ? Heq1 Heq2) "(-> & Hpost)".
       simplify_eq /=.
       wp_pures.
       wp_store.
       wp_pures.
       iDestruct "Hpost" as "(Ha1 & Ha2 & HtkS & HΦ)".
       wp_apply (release_spec with "[$Hlk $Hlkd Hl Hcr Ha1 Ha2 HtkS]").
       {
         iExists _.
         iFrame.
         iLeft.
         iSplit; first by iPureIntro.
         by iFrame. }
       iIntros (v ->).
       by wp_pures.
  Qed.

End Commit_Proof.
