From iris.algebra Require Import excl.
From iris.algebra Require Import auth gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
From aneris.prelude Require Import collect.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import tactics proofmode.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.mt_server.proof
     Require Import mt_server_proof.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import
     ras
     events
     resources
     api_spec.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras
     log_resources
     resources_def
     resources_local_inv
     resources_global_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import
     log_proof
     repdb_serialization
     db_resources_instance.
From aneris.examples.reliable_communication.lib.repdb.proof.leader
     Require Import
     clients_mt_user_params
     followers_mt_user_params
     proof_of_client_handler
     proof_of_followers_handler
     proof_of_init_leader
     proof_of_proxy
     proof_of_update_log_copy_loop.
From aneris.examples.reliable_communication.lib.repdb.proof.follower
     Require Import
     clients_at_follower_mt_user_params
     proof_of_clients_handler
     proof_of_proxy
     proof_of_sync_loop
     proof_of_init_follower.

Import user_params.
Section Init_setup_proof.
  Context `{!anerisG Mdl Σ, DB : !DB_params, !DBPreG Σ}.

  Lemma init_setup_holds (E : coPset) :
    ↑DB_InvName ⊆ E →
    DB_addr ∉ DB_followers →
    DB_addrF ∉ DB_followers →
    ⊢ |={E}=>
      ∃ (DBRS : @DB_resources _ _ _ _ DB)
        (Init_leader : iProp Σ)
        (leader_si : message → iProp Σ)
        (leaderF_si : message → iProp Σ),
      GlobalInv ∗
      Obs DB_addr [] ∗
      ([∗ set] k ∈ DB_keys, k ↦ₖ None) ∗
      Init_leader ∗
      ((∀ A, init_leader_spec A Init_leader leader_si leaderF_si) ∗
         (∀ A ca, init_client_proxy_leader_spec A ca leader_si)) ∗
      ([∗ set] fsa ∈ DB_followers,
         ∃ (f_si : message → iProp Σ)
           (Init_follower : iProp Σ),
           Init_follower ∗
           Obs fsa [] ∗
           (∀ A f2lsa, init_follower_spec f2lsa fsa A
                                          Init_follower f_si leaderF_si) ∗
           (∀ A f2csa csa, init_client_proxy_follower_spec A csa f2csa f_si)).
  Proof.
    iIntros (HE Hn1 Hn2).
    iMod (own_alloc
            (● (to_agree <$> ∅ : (gmapUR socket_address (agreeR gnameO))))) as
      (γFls) "Hgnames"; first by apply auth_auth_valid.
    set ( dbg :=
            {|
              IDBG_Global_mem := DB_preG_Global_mem;
              IDBG_Global_history_mono := DB_preG_Global_history_mono;
              IDBG_Known_replog := DB_preG_Known_replog;
              IDBG_lockG := DB_preG_lockG;
              IDBG_known_replog_name := γFls
            |}).
    iMod (alloc_gmem) as (γM) "(HownSys & HownUser)".
    iMod (alloc_leader_logM) as (γL) "(#HobsL & HlogLM)".
    iDestruct (Obs_own_log_obs with "[$HobsL]") as "HobsL'".
    iMod (alloc_logM_and_followers_gnames γL with "[$HobsL' $Hgnames]")
      as (N) "(%Hdom & Hreplog & Hmap & Hmap')"; first done.
    set (DBR := DbRes γL γM N).
    set (MTSC := client_handler_at_leader_user_params γL γM N).
    set (MTSF := follower_handler_user_params  γL γM N).
    iExists DBR.
    iMod (MTS_init_setup E MTSC)
      as (leader_si SrvInit) "(Hsinit & #HsrvS & #HcltS)".
    { simplify_eq /=; solve_ndisj. }
    iMod (MTS_init_setup E MTSF)
      as (leaderF_si SrvInitF) "(HsinitF & #HsrvSF & #HcltSF)".
    { simplify_eq /=; solve_ndisj. }
     iAssert (([∗ map] sa↦γ ∈ N, known_replog_token sa γ)%I) as "#Htks".
    { iApply (big_sepM_mono with "[$Hmap]").
      by iIntros (sa γsa Hin) "(Hkn & _ & _)". }
    iAssert (⌜∃ γdbF, N !! DB_addrF = Some γdbF⌝)%I as (γdbF) "%NdbF".
    { admit. }
    iDestruct (big_sepM_delete _ N DB_addrF γdbF with "Htks")
      as "#(HtkF & Htks')"; first done.
    set (initL := init_leader_res γL γM N SrvInit SrvInitF γdbF).
    rewrite -{2} Qp_half_half.
    iDestruct (own_log_auth_split _ (1/2) (1/2) [] with "[$HlogLM]")
      as "(HlogL1 & HlogL2)".
    iMod (inv_alloc
            DB_InvName _
            (global_inv_def γL γM N)
           with "[HownSys Hreplog HlogL1 Hmap]") as "#HGinv".
    { iNext.
      iExists [], (gset_to_gmap (@None write_event) DB_keys).
      iSplit; first by rewrite dom_gset_to_gmap.
      iSplit; first done.
      iSplit; first by iPureIntro; set_solver.
      iFrame.
      iSplitL; last by iPureIntro; apply valid_state_empty.
      rewrite /own_replog_global.
      iApply (big_sepM_mono with "[HobsL' $Hmap]").
      iIntros (sa γsa Hin) "(Hkn & Hobs & Hown)".
      eauto with iFrame. }
    iExists initL, leader_si, leaderF_si.
    simpl.
    iFrame "HGinv Htks HobsL HownUser Hsinit HsinitF HlogL2 HtkF".
    iDestruct (big_sepM_delete _ N DB_addrF γdbF with "Hmap'")
      as "(HdbF & Hmap')"; first done.
    iSplitL "HdbF"; first by iFrame.
    iSplitR.
    iSplitL.
    iModIntro.
    iIntros (A).

    (* iAssert ((init_leader_spec_internal *)
    (*               γL γM N leader_si leaderF_si *)
    (*               SrvInit SrvInitF γdbF A)%I) as "df".  *)
    (* { iDestruct (init_leader_spec_internal_holds with "[HsrvS][HsrvSF]") as "df". *)
    (*   admit. admit. admit. admit. *)
    (* as "#HsrvSI". *)
 Admitted.

  Global Instance db_init_instance : DB_init.
  Proof.
    split. iIntros (E HE Hn1 Hn2 _).
    iMod (init_setup_holds E HE Hn1 Hn2)
      as "(%DBRes & %init & %lsi & %lsfi & Hinit)".
    iModIntro.
    iExists _, _, _, _. by iFrame.
  Qed.

End Init_setup_proof.
