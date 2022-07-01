From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof monitor_proof serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From actris.channel Require Import proto.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Import lock_proof.

Class MTS_user_params `{ !anerisG Mdl Σ, !lockG Σ } :=
  { (* Requests. *)
    MTS_req_ser  : serialization;
    MTS_req_ser_inj : ser_is_injective MTS_req_ser;
    MTS_req_ser_inj_alt : ser_is_injective_alt MTS_req_ser;
    MTS_req_data : Type;
    (* Replies. *)
    MTS_rep_ser  : serialization;
    MTS_rep_ser_inj : ser_is_injective MTS_rep_ser;
    MTS_rep_ser_inj_alt : ser_is_injective_alt MTS_rep_ser;
    MTS_rep_data : Type;
    MTS_handler_pre  : val → MTS_req_data → iProp Σ;
    MTS_handler_post : val → MTS_req_data → MTS_rep_data → iProp Σ;
    MTS_saddr : socket_address;
    MTS_mN : namespace;
  }.

Arguments MTS_user_params {_ _ _ _}.

Definition handler_spec `{MTS_user_params} (handler : val) : iProp Σ :=
  ∀ reqv reqd,
  {{{ MTS_handler_pre reqv reqd }}}
    handler reqv @[ip_of_address MTS_saddr]
  {{{ repv repd, RET repv;
      ⌜Serializable MTS_rep_ser repv⌝ ∗
      MTS_handler_post repv reqd repd }}}.
