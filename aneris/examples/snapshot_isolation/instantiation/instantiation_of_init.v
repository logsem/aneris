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
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code
                    snapshot_isolation_code_api.
From aneris.aneris_lang Require Import resources.
From aneris.examples.reliable_communication.lib.mt_server Require Import
  user_params.
From aneris.examples.reliable_communication.lib.mt_server.proof Require Import
  mt_server_proof.
From aneris.examples.snapshot_isolation.specs Require Import
  user_params resources specs.
From aneris.examples.snapshot_isolation.specs Require Import
  user_params time events aux_defs resource_algebras.
From aneris.examples.snapshot_isolation.proof.resources
  Require Import
  global_invariant
  server_resources
  proxy_resources
  wrappers.
From aneris.examples.snapshot_isolation.proof Require Import
  rpc_user_params.
From aneris.examples.snapshot_isolation.instantiation Require Import
  snapshot_isolation_api_implementation
  instantiation_of_resources.
From aneris.examples.snapshot_isolation.proof.server Require Import
  proof_of_init_server.

Section Init_setup_proof.
  Context `{!anerisG Mdl Σ, DB : !User_params, !KVSG Σ,  !ras.SpecChanG Σ}.

  
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
    iMod (own_alloc (● (global_memUR (gset_to_gmap [] KVS_keys))))
      as (γSnap) "HSnap".
    { apply auth_auth_valid.
      intro k.
      rewrite /global_memUR.
      rewrite lookup_fmap lookup_gset_to_gmap.
      rewrite option_guard_bool_decide.
      destruct (decide (k ∈ KVS_keys)).
      - by rewrite bool_decide_eq_true_2.
      - by rewrite bool_decide_eq_false_2. }
    iMod (own_alloc (● (∅ :
                         (gmapUR nat (agreeR (gmapUR Key (max_prefix_listR write_eventO))))))) as (γTrs) "HauthTrs"; first by apply auth_auth_valid.
    iMod (own_alloc (● ∅ :(authR (gmapUR socket_address (agreeR (leibnizO gname)))))) as (γClts) "HauthClts"; first by apply auth_auth_valid. 
    iAssert (|==> ∃ M,
                 own γClts (● ((to_agree <$> M) : (gmapUR socket_address (agreeR (leibnizO gname))))) ∗
                         ⌜dom M = clients⌝ ∗
                       [∗ set] sa ∈ clients,
               client_can_connect γClts sa)%I with
      "[HauthClts]" as "df". 
    { iInduction clients as [|x xs] "IH" using set_ind_L.
      - iModIntro. iExists ∅. iFrame; eauto.
        rewrite dom_empty_L. rewrite fmap_empty; set_solver.
      - iMod ("IH" with "HauthClts") as (M) "(Hauth & %Hdom & Hclts)".
        iMod (own_alloc (csum.Cinl (Excl ()) : (csum.csumR (exclR unitR) (agreeR (prodO (prodO (prodO (prodO gnameO gnameO) gnameO) gnameO) gnameO))))) as (γsa) "Hsa". 
        done.
        iMod (own_update _ _
                (● ((to_agree<$>(<[x := γsa]>M)) :
                     (gmapUR socket_address
                        (agreeR (leibnizO gname)))
                   ) ⋅
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
    iMod "df" as (M) "(HauthClts & %Hdom & Hclts)".
    iMod (mono_nat_own_alloc 0) as (γT) "((HTimeG & HTimeL) & _)" .
    iMod (inv_alloc KVS_InvName E
            (global_inv_def clients γClts γGauth γSnap γT γTrs)
           with "[HmemG HSnap HauthTrs HauthClts HTimeG]")
      as "#Hginv".
    { iNext.
      iExists _, ∅, _, _. iFrame. unfold ownSnapAuth, connected_clients.
      rewrite fmap_empty.
      iFrame. iSplit; first done.
      iPureIntro.
      apply model.valid_init_state. }
    set (MTSC := client_handler_rpc_user_params clients
                   γClts γGauth γSnap γT γTrs).
    iMod (MTS_init_setup E MTSC)
      as (srv_si SrvInit MTRC) "(Hsinit & #HsrvS & #HcltS & #HreqS)". 
    { simplify_eq /=; solve_ndisj. }
    iModIntro.
    iExists (SI_resources_instance clients
               γClts γGauth γSnap γT γTrs srv_si SrvInit).
    iFrame "#∗".
    iSplitL "Hkeys".
    { rewrite big_sepM_gset_to_gmap.
      iApply (big_sepS_mono with "Hkeys").
      iIntros (k Hk) "Hk".
      iExists [].
      iFrame.
      admit. }
    admit.
  Admitted.
  
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

   
