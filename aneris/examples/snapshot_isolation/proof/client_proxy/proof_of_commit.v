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
    is_connected γGsnap γT γKnownClients c sa -∗
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
    Global_Inv clients γKnownClients γGauth γGsnap γT  ⊢ commit_spec_internal.
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
    iDestruct "Hst" as (ts Msnap cache_updatesL cache_updatesV cache_updatesM cacheM)
      "( -> & (%Hcoh & %Hvalid & %Hismap & Htime & Hseen & Hupd & Hauth & HauthMsnap & Htok))".
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
        destruct Hcoh as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6).
        destruct b; last done.
        specialize (HmcEq0 k (Some v) true H_pure_eq_mc).
        rewrite -HmcEq0 in H_pure_eq_mc.
        specialize (Hc5 k v) as (_ & Habs).
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
          -   destruct Hcoh as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7).
              assert (cacheM !! k = Some (None, true)) as Hcm.
              { by eapply map_subseteq_spec. }
              by destruct (Hc7 k None Hcm). }
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
    - (* TODO: the non-empty cache case *) admit.
  Admitted.

End Commit_Proof.
