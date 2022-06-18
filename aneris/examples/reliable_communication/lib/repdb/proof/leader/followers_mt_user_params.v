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
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params events.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import ras log_resources resources_def
     resources_global_inv resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import repdb_serialization.

Import gen_heap_light.
Import lock_proof.

Section MT_user_params.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM γF : gname).

  Definition ReqData : Type := wrlog.

  Definition RepData : Type := wrlog.

  Definition ReqPre (reqv : val) (reqd : ReqData) : iProp Σ :=
    Global_Inv γL γM ∗ ⌜reqv = #(List.length reqd)⌝ ∗ own_replog_obs γL DB_addrF reqd.

  Definition ReqPost
    (repv : val) (reqd : ReqData) (repd : RepData) : iProp Σ :=
    ∃ (we : write_event),
      ⌜repd = reqd ++ [we]⌝ ∗
      ⌜we.(we_time) = (List.length reqd)⌝ ∗
      ⌜repv = $ we⌝ ∗
      own_replog_obs γL DB_addrF repd.

  Global Instance follower_handler_user_params : MTS_user_params :=
    {|
      MTS_req_ser  := req_f2l_serialization;
      MTS_req_ser_inj := req_f2l_ser_is_injective;
      MTS_req_ser_inj_alt := req_f2l_ser_is_injective_alt;
      MTS_req_data := ReqData;
      MTS_rep_ser  := rep_l2f_serialization;
      MTS_rep_ser_inj := rep_l2f_ser_is_injective;
      MTS_rep_ser_inj_alt := rep_l2f_ser_is_injective_alt;
      MTS_rep_data := RepData;
      MTS_saddr := DB_addrF;
      MTS_mN := (DB_InvName .@ "leader_secondary");
      MTS_handler_pre  := ReqPre;
      MTS_handler_post := ReqPost;
    |}.

End MT_user_params.
