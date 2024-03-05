From iris.algebra Require Import agree auth excl gmap updates local_updates.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import
  serialization_proof.
From aneris.examples.reliable_communication.spec
     Require Import ras.
From aneris.examples.reliable_communication.lib.mt_server.spec
  Require Import api_spec.
From aneris.examples.transactional_consistency.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency
     Require Import code_api.
From aneris.aneris_lang Require Import resources.
From aneris.examples.reliable_communication.lib.mt_server Require Import
  user_params.
From aneris.examples.reliable_communication.lib.mt_server.proof Require Import
  mt_server_proof.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time specs resources events aux_defs.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources
  Require Import
  global_invariant
  server_resources
  proxy_resources
  wrappers.
From aneris.examples.transactional_consistency.snapshot_isolation.proof Require Import
  rpc_user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
  snapshot_isolation_api_implementation
  instantiation_of_resources.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.client_proxy Require Import
  proof_of_init_client_proxy
  proof_of_read
  proof_of_write
  proof_of_commit
  proof_of_start
  proof_of_commit.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.server Require Import
  proof_of_init_server.

 Notation snapsTy := (gmapUR nat 
                        (agreeR
                           (gmapUR Key
                              (max_prefix_listR write_eventO)))).
 Notation gnamesTy := (gmapUR socket_address
                                   (agreeR (leibnizO gname))).

 Notation csumTy := (csum.csumR (exclR unitR) (agreeR (prodO (prodO (prodO (prodO gnameO gnameO) gnameO) gnameO) gnameO))).
 
Section Init_setup_proof.
  Context `{!anerisG Mdl Σ, DB : !User_params, !KVSG Σ}.
  Context `{!ras.SpecChanG Σ}.
  
  Lemma init_setup_holds (E : coPset) (clients : gset socket_address) :
    ↑KVS_InvName ⊆ E →
    ⊢ |={E}=>
          ∃ res : SI_resources Mdl Σ,
           ([∗ set] k ∈ KVS_keys, k ↦ₖ []) ∗
             KVS_Init ∗
             GlobalInv ∗
             ([∗ set] sa ∈ clients, KVS_ClientCanConnect sa) ∗
             ⌜init_kvs_spec⌝ ∗
             ⌜init_client_proxy_spec⌝ ∗
             ⌜read_spec⌝ ∗
             ⌜write_spec⌝ ∗
             ⌜start_spec⌝ ∗
             ⌜commit_spec⌝.
  Proof.
    iIntros (Hne).
    iMod (ghost_map_alloc ((gset_to_gmap [] KVS_keys)))
      as (γGauth) "((HmemG & HmemL) & Hkeys)".
    iMod (own_alloc (● (∅ : snapsTy))) as (γTrs) "HauthTrs";
      first by apply auth_auth_valid.
    iMod (own_alloc (● ∅ : authR gnamesTy)) as (γClts) "HauthClts";
      first by apply auth_auth_valid.
    iMod (own_alloc
            (● (∅ : gmapUR Key (max_prefix_listR write_eventO))))
      as (γGsnap) "HGsnap". 
     { apply auth_auth_valid. done. }
    iAssert (|==>
               own γGsnap
               (● global_memUR
                  (gset_to_gmap ([] : list write_event) KVS_keys)) ∗
               ([∗ map] k↦v ∈ gset_to_gmap ([] : list write_event)
                  KVS_keys,
              own γGsnap (◯ {[k := to_max_prefix_list []]})))%I
              with "[HGsnap]" as ">(HGsnap & #Hseens)".
     { rewrite big_sepM_gset_to_gmap.
       iInduction KVS_keys as [|k ks] "IH" using set_ind_L.
       - iModIntro.
         rewrite /gset_to_gmap fmap_empty /global_memUR //=.
         rewrite fmap_empty; by iFrame.
       - iMod ("IH" with "HGsnap") as "(HGsnap & Hks)".
         rewrite big_sepS_insert; last done.
         iFrame.
         rewrite gset_to_gmap_union_singleton.
         rewrite /global_memUR fmap_insert.
         iMod (own_update _ _
                 (● ((to_max_prefix_list <$>
                        (<[k := []]> (gset_to_gmap [] ks))) :
                   gmapUR Key (max_prefix_listR write_eventO)  ) ⋅
                 ◯  {[k := to_max_prefix_list []]})
               with "HGsnap") as "(HGsnap & Hks)".
        { apply auth_update_alloc.
          rewrite -insert_empty.
          rewrite fmap_insert.
          eapply (alloc_local_update); last done.
          apply not_elem_of_dom.
          by rewrite dom_fmap dom_gset_to_gmap. }
        rewrite fmap_insert. by iFrame. } 
    iAssert (|==> ∃ M,
                 own γClts (● ((to_agree <$> M) :gnamesTy)) ∗
                 ⌜dom M = clients⌝ ∗
                 [∗ set] sa ∈ clients,
                 client_can_connect γClts sa)%I with
      "[HauthClts]" as "HauthClts". 
    { iInduction clients as [|x xs] "IH" using set_ind_L.
      - iModIntro. iExists ∅. iFrame; eauto.
        rewrite dom_empty_L. rewrite fmap_empty. iFrame. iSplit; first done.
        set_solver. 
      - iMod ("IH" with "HauthClts") as (M) "(Hauth & %Hdom & Hclts)".
        iMod (own_alloc (csum.Cinl (Excl ()) : csumTy
                  )) as (γsa) "Hsa". 
        done.
        iMod (own_update _ _
                (● ((to_agree<$>(<[x := γsa]>M)) : gnamesTy) ⋅
                 ◯ {[x := to_agree γsa]})
               with "Hauth") as "(Hauth & Hclsa)".
        { apply auth_update_alloc.
          rewrite -insert_empty.
          rewrite fmap_insert.
          eapply (alloc_local_update); last done.
          apply not_elem_of_dom. set_solver. }
        iModIntro; iExists _; iFrame.
        iSplit; first (rewrite dom_insert_L; set_solver).
        rewrite big_sepS_insert; last done.
        iFrame. rewrite /client_can_connect. eauto. }
    iMod "HauthClts" as (M) "(HauthClts & %Hdom & Hclts)".
    iMod (mono_nat_own_alloc 0) as (γT) "((HTimeG & HTimeL) & _)" .
    iMod (inv_alloc KVS_InvName E
            (global_inv_def clients γClts γGauth γGsnap γT γTrs)
           with "[HmemG HGsnap HauthTrs HauthClts HTimeG]")
      as "#Hginv".
    { iNext. iExists _, ∅, _, _.
      iFrame. unfold ownSnapAuth, connected_clients.
      rewrite fmap_empty. iFrame. iSplit; first done.
      iPureIntro. apply model.valid_init_state. }
    set (MTSC := client_handler_rpc_user_params clients
                   γClts γGauth γGsnap γT γTrs).
    iMod (MTS_init_setup E MTSC)
      as (srv_si SrvInit MTRC) "(Hsinit & #HsrvS & #HcltS & #HreqS)". 
    { simplify_eq /=; solve_ndisj. }
    iModIntro.
    iExists (SI_resources_instance clients
               γClts γGauth γGsnap γT γTrs srv_si SrvInit).
    iFrame "#∗".
    iSplitL "Hkeys".
    { rewrite !big_sepM_gset_to_gmap.
      iDestruct (big_sepS_sep with "[$Hkeys $Hseens]") as "Hkeys".
      iApply (big_sepS_mono with "Hkeys").
      iIntros (k Hk) "Hk".
      iExists [].
      by iFrame. }
    iSplit.
    {  rewrite /KVS_ClientCanConnect //=.
       iApply big_sepS_sep.
       iSplit.
       - iApply big_sepS_dup; eauto.
       - iApply big_sepS_sep.
       iFrame "#∗".
       iApply big_sepS_dup; eauto. }
    iSplit.
    { iPureIntro. iIntros (Φ) "(#Hsi & Hh & Hfs & Hinit) HΦ".
      iDestruct "Hinit" as "(? & ? & ? & ? & ?)".
      wp_apply (init_server_spec_internal_holds with "[$][$HΦ]"). } 
    iSplit.
    { iPureIntro.
      iIntros (sa Φ) "(Ha & #Hsi & Hm & (#Hc1 & Hc2 & #Hc3 & #Hc4) & Hf) HΦ".
      wp_apply (init_client_leader_proxy_internal_holds clients
                 with "[$][HΦ]").
      iNext. iIntros (cs) "(H1 & H2)".
      iApply "HΦ".
      rewrite / ConnectionState //=.
      iFrame "#∗". 
    }
    iSplit.
    { iPureIntro.
      iIntros (?????) "#(H1 & H2 & H3) !#".
      iIntros (Φ) "Hk HΦ".
      rewrite /OwnLocalKey /IsConnected //=.  
      wp_apply (read_spec_internal_holds clients γClts γGauth γGsnap γT γTrs
                 with "[//][$][$Hk][$HΦ]").
      iFrame "#∗". }
    iSplit.
    { iPureIntro.
      iIntros (???????) "#(H1 & H2 & H3) !#".
      iIntros (Φ) "Hk HΦ".
      rewrite /OwnLocalKey /IsConnected //=.  
      by wp_apply (write_spec_internal_holds γClts γGsnap γT γTrs
                 with "[//][$Hk][$HΦ]"). }
    iSplit.
    { iPureIntro.
      iIntros (????) "#(H1 & H2 & H3) !#".
      iIntros (Φ) "HΦ".
      wp_apply (start_spec_internal_holds clients γClts γGauth γGsnap γT γTrs
                 with "[//][$][$][$][$HΦ]"). }
    iPureIntro.
      iIntros (????) "#(H1 & H2 & H3) !#".
      iIntros (Φ) "HΦ".
      wp_apply (commit_spec_internal_holds clients γClts γGauth γGsnap γT γTrs
                 with "[//][$][$][$][$HΦ]").
  Qed.
  
End Init_setup_proof.

Global Instance SI_init_instanciation
  `{!anerisG Mdl Σ, !User_params, !KVSG Σ, !SpecChanG Σ}: SI_init.
  Proof.
    split.
    iIntros (E HE clts).
    iMod (init_setup_holds E HE) as "(%R & df)"; first done.
    iModIntro.
    iExists R. by iFrame.
  Qed.

   
