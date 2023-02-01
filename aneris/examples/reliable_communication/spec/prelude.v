From aneris.aneris_lang Require Import lang.
From actris.channel Require Import proto.
From aneris.examples.reliable_communication.resources Require Export session_escrow.
From aneris Require Import aneris_weakestpre.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Canonical Structure locO := leibnizO loc.
Canonical Structure sideO := leibnizO side.

Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

(** =============================== GHOST NAMES ============================= *)

Definition Nsession_escrow := nroot .@ "session_escrow".

Section iProto_sessions.
  Context `{!anerisG Mdl Σ, !session_escrowG Σ val}.
  Context (N : namespace).
  
  Definition ses_own := ses_own Nsession_escrow.
End iProto_sessions.

Record lock_name :=
  LockName {
      lock_lock_name : gname;
      lock_idx_name : gname;
    }.

Record endpoint_name :=
  EndpointName {
      endpoint_session_escrow_name : session_escrow_name;
      endpoint_send_lock_name : lock_name;
      endpoint_recv_lock_name : lock_name;
      endpoint_address_name : gname;
      endpoint_side_name : gname;
      endpoint_idxs_name : gname;
      (* can be later generalized to the endpoint_endpoint_name *)
    }.

Record session_name :=
  SessionName {
      session_session_escrow_name : session_escrow_name;
      session_clt_idx_name : gname;
      session_srv_idx_name : gname;
      session_srv_cookie_name : gname;
      session_status_gname : gname;
    }.

Notation socket_addressO := (leibnizO socket_address).

Global Instance lock_name_inhabited : Inhabited lock_name :=
  populate (LockName inhabitant inhabitant).
Global Instance lock_name_eq_dec : EqDecision lock_name.
Proof. solve_decision. Qed.
Global Instance lock_name_countable : Countable lock_name.
Proof.
  refine (inj_countable (λ '(LockName γ_lk γ_idx), (γ_lk, γ_idx))
                        (λ '(γ_lk, γ_idx), Some (LockName γ_lk γ_idx)) _);
    by intros [].
Qed.

Global Instance session_name_inhabited : Inhabited session_name :=
  populate (SessionName inhabitant inhabitant inhabitant inhabitant inhabitant).
Global Instance session_name_eq_dec : EqDecision session_name.
Proof. solve_decision. Qed.
Global Instance session_name_countable : Countable session_name.
Proof.
  refine (inj_countable (λ '(SessionName γc γ_slk γ_rlk γck γmd), (γc, γ_slk, γ_rlk, γck, γmd))
                        (λ '(γc, γ_slk, γ_rlk, γck, γmd), Some (SessionName γc γ_slk γ_rlk γck γmd)) _);
    by intros [].
Qed.
