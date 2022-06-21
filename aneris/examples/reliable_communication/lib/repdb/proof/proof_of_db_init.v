From iris.algebra Require Import excl.
From iris.algebra Require Import auth gmap dfrac.
From iris.algebra.lib Require Import mono_list.
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
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_code.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_prelude dlm_resources dlm_code dlm_spec.
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

Section Alloc_ghost_resources.
  Context `{!anerisG Mdl Σ, DB : !DB_params, !IDBG Σ }.

  (* Move later to resources/?.v *)

  Lemma alloc_gmem :
    ⊢ |==>
          ∃ γM : gname,
            own_mem_sys γM (gset_to_gmap (@None write_event) DB_keys) ∗
           ([∗ set] k ∈ DB_keys, own_mem_user γM k 1%Qp None).
  Proof.
    (* B induction on the set DB_keys. *)
    (* set (empty_mem := (gset_to_gmap (@None write_event) DB_keys)). *)
    (* iMod (gen_heap_light_init empty_mem) as "(%γM & Hmem)". *)
  Admitted.

  Lemma alloc_leader_logM  :
   ⊢ |==>∃ γL, own_obs γL DB_addr [] ∗ own_log_auth γL 1 [].
  Proof.
  Admitted.

  Lemma alloc_logM_and_followers_gnames :
    DB_addrF ∉ DB_followers →
    known_replog_tokens ∅ ⊢ |==>
          ∃ (N : gmap socket_address gname),
            ⌜dom N = DB_followers ∪ {[DB_addrF]}⌝ ∗
            known_replog_tokens N ∗
            ([∗ map] sa ↦ γ ∈ N,
               known_replog_token sa γ ∗
               own_log_obs γ [] ∗
               own_log_auth γ 1 []).
  Proof.
    (* By induction on the set DB_followers ∪ DB_addrF. *)
  Admitted.

End Alloc_ghost_resources.

Section Init_setup_proof.
  Context `{!anerisG Mdl Σ, DB : !DB_params, !DBPreG Σ }.

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
    iMod (alloc_logM_and_followers_gnames with "[$Hgnames]")
      as (N) "(%Hdom & Hreplog & Hmap)"; first done.
    set (DBR := DbRes γL γM N).
    iExists DBR.
    (* Next step : Use MTS_init. *)
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
