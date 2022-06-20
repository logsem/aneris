From iris.algebra Require Import agree auth excl gmap dfrac.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
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

(* -------------------------------------------------------------------------- *)
Section MT_user_params.

  Context `{!anerisG Mdl Σ, !DB_params, !IDBG Σ}.
  Context (γL γM : gname) (N: gmap socket_address gname) (sa : socket_address).

  Definition ReqData : Type := string * wrlog.

  Definition RepData : Type := wrlog.

  (* Definition ReqPre (reqv : val) (reqd : ReqData) : iProp Σ := *)
  (*   Global_Inv γL γM N ∗ *)
  (*   ∃ k h, ⌜k ∈ DB_keys⌝ ∗ ⌜reqd = (k, h)⌝ ∗ ⌜reqv = #(LitString k)⌝ ∗ *)
  (*           known_replog_token sa γF ∗ own_logL_obs γL h ∗ *)
  (*           own_log_obs γF h. *)

  (* Definition ReqPost (repv : val) (reqd : ReqData) (repd : RepData) *)
  (*   : iProp Σ := *)
  (*   ∃ k h h', ⌜reqd = (k,h)⌝ ∗ ⌜repd = h'⌝ ∗ ⌜h ≤ₚ h'⌝ ∗ *)
  (*             known_replog_token sa γF ∗ own_logL_obs γL h' ∗ *)
  (*             own_log_obs γF h' ∗ *)
  (*             ((⌜repv = NONEV⌝ ∗ ⌜at_key k h' = None⌝) ∨ *)
  (*              (∃ a, ⌜repv = SOMEV (we_val a)⌝ ∗ ⌜at_key k h' = Some a⌝)). *)

 Definition ReqPre (reqv : val) (reqd : ReqData) : iProp Σ :=
    Global_Inv γL γM N ∗
    ∃ k h, ⌜k ∈ DB_keys⌝ ∗ ⌜reqd = (k, h)⌝ ∗ ⌜reqv = #(LitString k)⌝ ∗
             own_replog_obs γL sa h.

  Definition ReqPost (repv : val) (reqd : ReqData) (repd : RepData)
    : iProp Σ :=
    ∃ k h h', ⌜reqd = (k,h)⌝ ∗ ⌜repd = h'⌝ ∗ ⌜h ≤ₚ h'⌝ ∗
               own_replog_obs γL sa h' ∗
              ((⌜repv = NONEV⌝ ∗ ⌜at_key k h' = None⌝) ∨
               (∃ a, ⌜repv = SOMEV (we_val a)⌝ ∗ ⌜at_key k h' = Some a⌝)).

  Global Instance client_handler_at_follower_user_params
    : MTS_user_params :=
    {|
      MTS_req_ser  := req_c2f_serialization;
      MTS_req_ser_inj := req_c2f_ser_is_injective;
      MTS_req_ser_inj_alt := req_c2f_ser_is_injective_alt;
      MTS_req_data := ReqData;
      MTS_rep_ser  := rep_f2c_serialization;
      MTS_rep_ser_inj := rep_f2c_ser_is_injective;
      MTS_rep_ser_inj_alt := rep_f2c_ser_is_injective_alt;
      MTS_rep_data := RepData;
      MTS_saddr := sa;
      MTS_mN := (DB_InvName.@socket_address_to_str sa);
      MTS_handler_pre  := ReqPre;
      MTS_handler_post := ReqPost;
    |}.

End MT_user_params.
