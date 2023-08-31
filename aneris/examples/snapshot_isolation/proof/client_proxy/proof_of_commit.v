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
      unfold ownCacheUser.
      (* Should be provable. Maybe state as Forall *)
      iAssert (⌜∀ k vo b, mc !! k = Some (vo, b) -> b = false⌝%I) as "%HmcEq1".
      {
        iPureIntro.
        intros k vo b H_pure_eq_mc.
        admit.
      }
      iAssert (⌜∀ k vo b h, mc !! k = Some (vo, b) →
                           m !! k = Some h →
                          commit_event (vo, b) h = h⌝%I) as "%HmcEq2".
      {
        iPureIntro.
        intros k vo b h H_pure_eq_mc H_pure_eq_m.
        apply (HmcEq1 _ _ _) in H_pure_eq_mc as ->.
        simpl.
        by destruct vo.
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
        { by specialize (HmcEq1 k vo true Hmc). }
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
        wp_apply (release_spec with "[$Hlk $Hlkd Hcon Hl Hcr Hauth Hcache HauthMsnap]").
        {
          iExists _.
          iFrame.
          iLeft.
          iDestruct "Hcon" as (sp) "(Hst' & %Heq')".
          iDestruct "Hst'" as (???????->) "(#Hcc2 & Hst')".
          iSplit; first by iPureIntro.
          destruct sp; simplify_eq /=.
          iDestruct "Hst'" as "(Htk & #Hseen & HauthMsnap')".
          iDestruct (client_connected_agree with "[$Hcc1][$Hcc2]") as "%Heq'".
          simplify_eq /=.
          iFrame.
          iDestruct (ghost_map.ghost_map_delete_big mc with "[$Hauth][Hcache]") as "df".
          - iDestruct (big_sepM_mono _ 
            (λ k v0, ghost_map.ghost_map_elem _ k (DfracOwn 1) v0)%I 
            with "[$Hcache]") as "H_goal".
            * iIntros (k p H_some_mc) "(H_cache & H_upd)".
              iDestruct "H_cache" as (sa_c v_c γCst_c γA_c γS_c γlk_c γCache_c γMsnap_c b)
                "(%H_pair_eq_c & H_conn_c & H_elem_c & _)".
              iDestruct "H_upd" as (sa_u v_u γCst_u γA_u γS_u γlk_u γCache_u γMsnap_u vo)
                "(%H_pair_eq_u & H_conn_u & H_elem_u & _)".
              simplify_eq.
              iDestruct (client_connected_agree with "[$H_conn_c][$H_conn_u]") as "%Heq'".
              simplify_eq.
              iDestruct (ghost_map.ghost_map_elem_combine
                  with "[$H_elem_c][$H_elem_u]") as "(H_elem & %H_eq)".
              inversion H_eq.
              rewrite dfrac_op_own Qp.half_half.
              destruct p.
              simpl.
              admit.
            * admit.
      
(*   alternative approach to the above
          - 
            iDestruct (big_sepM_mono _ (λ k y,
              (∃ (γCst0 γA0 γS0 γlk0 γCache γMsnap: gname),
                client_connected γKnownClients sa γCst0 γA0 γS0 γlk0 γCache γMsnap) ∗
                ownCacheUser γKnownClients k (#sa, v) y.1 ∗
                key_upd_status γKnownClients (#sa, v) k y.2)%I 
              with "[$Hcache]") as "Hcache".
            + iIntros (k x H_mc_some) "(H_cache & H_upd)". 
              iDestruct "H_cache" as (sa_c vo_c γCst_c γA_c γS_c γlk_c γCache_c γMsnap_c b_c) 
                "(%H_eq_c & #H_conn_c & H_map_c & H_match_c)".
              iDestruct "H_upd" as (sa_u v_u γCst_u γA_u γS_u γlk_u γCache_u γMsnap_u vo_u) 
                "(%H_eq_u & #H_conn_u & H_map_u & H_imp_u)".
              simplify_eq.
              iDestruct (client_connected_agree with "[$H_conn_c][$H_conn_u]") as "%Heq'".
              simplify_eq.
              iSplit.
              {
               iExists _, _, _, _, _, _.
               iFrame "#". 
              }
              iSplitL "H_map_c H_match_c".
              {
                iExists _, _, _, _, _, _, _, _.
                iExists _.
                iSplit; first by iPureIntro.
                iFrame "#∗".
              }
              iExists _, _, _, _, _, _, _, _.
              iExists _.
              iSplit; first by iPureIntro.
              iFrame "#∗".
            + iDestruct (big_sepM_sep
                (λ k y, (∃ γCst1 γA1 γS1 γlk1 γCache γMsnap : gname,
                        client_connected γKnownClients sa γCst1 γA1 γS1 γlk1 γCache γMsnap))%I
                (λ k y, ownCacheUser γKnownClients k (#sa, v) y.1 ∗
                        key_upd_status γKnownClients (#sa, v) k y.2)%I 
                mc with "Hcache") as "(Hconn & Hcache)".
              destruct (decide (mc = ∅)) as [-> | H_mc_neq_emp].
              * by iApply big_sepM_empty.
              * apply map_choose in H_mc_neq_emp as H_mc_some.
                destruct H_mc_some as [i [x H_mc_some]].
                iDestruct (big_sepM_lookup_dom _ _ i with "[$Hconn]") as "Hconn"; first by rewrite H_mc_some.
                iDestruct "Hconn" as (γCst1' γA1' γS1' γlk1' γCache' γMsnap') "#Hconn".
                iDestruct (client_connected_agree with "[$Hconn][$Hcc2]") as "%Heq'".
                simplify_eq.
                (* .... *)
                iApply (big_sepM_mono); last done.
                iIntros (k p H_some_mc) "(H_cache & H_upd)".
                iDestruct "H_cache" as (sa_c v_c γCst_c γA_c γS_c γlk_c γCache_c γMsnap_c b)
                  "(%H_pair_eq_c & H_conn_c & H_elem_c & _)".
                iDestruct "H_upd" as (sa_u v_u γCst_u γA_u γS_u γlk_u γCache_u γMsnap_u vo)
                  "(%H_pair_eq_u & H_conn_u & H_elem_u & _)".
                simplify_eq.
                iDestruct (client_connected_agree with "[$H_conn_c][$H_conn_u]") as "%Heq'".
                simplify_eq.
                iDestruct (ghost_map.ghost_map_elem_combine
                    with "[$H_elem_c][$H_elem_u]") as "(H_elem & %H_eq)".
                inversion H_eq.
                rewrite dfrac_op_own Qp.half_half.
                destruct p. 
                simpl.
                iFrame.
              admit. *)
            - unfold ownMsnapFull, ownMsnapFrag.
              iDestruct "HauthMsnap" as "(HauthMsnap & HauthMsnap'')".
              iAssert ((⌜Msnap = g⌝)%I) as "<-".
              {
                admit.
              }
              assert (dom cacheM = dom mc) as H_dom_cacheM_mc.
              {
                destruct Hcoh as (H_dom_msnap_chacheM & _).
                set_solver.
              }
              assert (cacheM ∖ mc = ∅) as ->.
              {
                admit.
              }
              iSplitL "df".
              {
                admit.
              }
              {
                admit.
              }
          }
          iIntros (? ->).
          by wp_pures.
    - (* TODO: the non-empty cache case *) admit.
  Admitted.

End Commit_Proof.
