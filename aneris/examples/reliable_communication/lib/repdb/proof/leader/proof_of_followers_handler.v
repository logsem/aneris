From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.reliable_communication.lib.repdb Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import ras resources_def resources_global_inv resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import log_proof repdb_serialization.
From aneris.examples.reliable_communication.lib.repdb.proof.leader
     Require Import followers_mt_user_params.

Import gen_heap_light.
Import lock_proof.

Section Followers_MT_spec_params.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname).
  Context (mγ γF : gname) (mv : val) (logFLoc : loc).

  Notation MTU_F := (follower_handler_user_params γL γM).


  Definition handler_cloj : val :=
    λ: "mv" "reqv", follower_request_handler #logFLoc "mv" "reqv".

  Lemma follower_request_handler_spec  :
    ∀ reqv reqd,
    {{{ is_monitor
          (DB_InvName .@ "leader_secondary")
          (ip_of_address MTU_F.(MTS_saddr)) mγ mv
          (log_monitor_inv_def
             (ip_of_address MTU_F.(MTS_saddr)) γF (1/4) logFLoc
             (leader_local_secondary_res γL γF)) ∗
        lock_proof.locked mγ ∗
        (log_monitor_inv_def
             (ip_of_address MTU_F.(MTS_saddr)) γF (1/4) logFLoc
             (leader_local_secondary_res γL γF)) ∗
        MTU_F.(MTS_handler_pre) reqv reqd }}}
      handler_cloj mv reqv @[ip_of_address MTU_F.(MTS_saddr)]
    {{{ repv repd, RET repv;
        ⌜Serializable rep_l2f_serialization repv⌝ ∗
        lock_proof.locked mγ ∗
        (log_monitor_inv_def
             (ip_of_address MTU_F.(MTS_saddr)) γF (1/4) logFLoc
             (leader_local_secondary_res γL γF)) ∗
        MTU_F.(MTS_handler_post) repv reqd repd }}}.
  Proof.
  Admitted.

  Global Instance follower_handler_spec_params :  @MTS_spec_params _ _ _ _ MTU_F :=
    {|
      MTS_mR := (log_monitor_inv_def
                   (ip_of_address MTU_F.(MTS_saddr)) γF (1/4) logFLoc
                   (leader_local_secondary_res γL γF));
      MTS_mγ := mγ;
      MTS_mv := mv;
      MTS_handler := handler_cloj;
      MTS_handler_spec := follower_request_handler_spec;
    |}.

End Followers_MT_spec_params.
