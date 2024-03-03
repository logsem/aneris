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
From aneris.examples.transactional_consistency.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events aux_defs resource_algebras.
From aneris.examples.transactional_consistency Require Import user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof
     Require Import utils model kvs_serialization rpc_user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.server
     Require Import
     proof_of_start_handler
     proof_of_read_handler
     proof_of_commit_handler.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Section Proof_of_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT γTrs).
  Import code_api.

  Lemma client_request_handler_spec (lk : val) (kvs vnum : loc) :
    ∀ reqv reqd,
    {{{ server_lock_inv γGauth γT γlk lk kvs vnum ∗
        MTC.(MTS_handler_pre) reqv reqd }}}
        client_request_handler lk #kvs #vnum reqv  @[ip_of_address MTC.(MTS_saddr)]
    {{{ repv repd, RET repv;
        ⌜Serializable (rep_serialization) repv⌝ ∗
         MTC.(MTS_handler_post) repv reqd repd }}}.
  Proof.
    iIntros (reqv reqd Φ) "(#Hlk & Hpre) HΦ".
    rewrite /client_request_handler.
    wp_pures.
    rewrite /MTS_handler_pre //= /ReqPre.
    rewrite /lk_handle.
    iDestruct "Hpre" as "(#HGlobInv & [HpreRead|[HpreStart|HpreCommit]])".
    1:{
      iDestruct "HpreRead" as (k ts h Msf Hin Hreqd ->) "(%Hts & %Hmsf & #HsnapT & #HsnapH & #Hfrag)".
      wp_pures.
      wp_lam.
      wp_pures.
      iApply (read_handler_spec _ _ _ _ _ _ _ _ _ _ _ 
                reqd ts h Msf Φ Hin Hreqd 
       with "[$Hlk][$HGlobInv][$HsnapT][$HsnapH][$Hfrag]"); try done.
      intros e He. 
      specialize (Hts e He).
      replace ts with (Z.abs_nat ts) in Hts; lia. }
    2:{
      iDestruct "HpreCommit" as (E P Q cmapV cache_updatesM cache_logicaM Msnap Msnap_full ts Hreqd)
        "HpreCommit".
      iDestruct "HpreCommit" as (-> Hin Hmap Hcoh Hall Hvalid Hsubeq)
        "(Hsnap & HsnapFrag & Hseen & Hp & Hshift)".
      wp_pures.
      wp_lam.
      wp_pures.
      by iApply (commit_handler_spec _ _ _ _ _ _ _ _ _ _ _ Φ _ _ _ _ _ _ _ _ _
        Hreqd Hin Hmap Hcoh Hvalid Hall Hsubeq with "[][][$Hsnap][$HsnapFrag][$Hseen][$Hp][$Hshift]"). }
    iDestruct "HpreStart" as (E P Q Hreqd ->) "(%HinE & HP & Hsh)".
    wp_pures.
    wp_lam.
    wp_pures.
    by iApply (start_handler_spec _ _ _ _ _ _ _ _ _ _ _ Φ _ _ _ Hreqd HinE
             with "[$Hlk][$HGlobInv][$HP][$Hsh]").
   Qed.

End Proof_of_handler.
