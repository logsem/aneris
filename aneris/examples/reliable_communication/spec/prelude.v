From aneris.aneris_lang Require Import lang.
From actris.channel Require Import proto.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Canonical Structure locO := leibnizO loc.
Canonical Structure sideO := leibnizO side.

Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

(** =============================== GHOST NAMES ============================= *)

(** Ghost names for channel data (buffers and counters) *)
Record chan_logbuf_name := ChanLogBufName {
  chan_logbuf_buf_name : gname;
  chan_logbuf_cpt_name : gname
}.

(** Ghost names for channels, channel endpoint data, and channel session (shared data). *)
Record chan_name :=
  ChanName {
      chan_proto_name : proto_name;
      chan_Tl_name : chan_logbuf_name;
      chan_Tr_name : chan_logbuf_name;
      chan_Rl_name : chan_logbuf_name;
      chan_Rr_name : chan_logbuf_name;
      chan_N : namespace
    }.

Record lock_name :=
  LockName {
      lock_lock_name : gname;
      lock_idx_name : gname;
    }.

Record endpoint_name :=
  EndpointName {
      endpoint_chan_name : chan_name;
      endpoint_send_lock_name : lock_name;
      endpoint_recv_lock_name : lock_name;
      endpoint_address_name : gname;
      endpoint_side_name : gname;
      endpoint_idxs_name : gname;
      (* can be later generalized to the endpoint_endpoint_name *)
    }.

Record session_name :=
  SessionName {
      session_chan_name : chan_name;
      session_clt_idx_name : gname;
      session_srv_idx_name : gname;
      session_srv_cookie_name : gname;
      session_status_gname : gname;
    }.

Notation socket_addressO := (leibnizO socket_address).


Global Instance chan_logbuf_name_inhabited : Inhabited chan_logbuf_name :=
  populate (ChanLogBufName inhabitant inhabitant).

Global Instance chan_logbuf_name_eq_dec : EqDecision chan_logbuf_name.
Proof. solve_decision. Qed.

Global Instance chan_logbuf_name_countable : Countable chan_logbuf_name.
Proof.
  refine (inj_countable (λ '(ChanLogBufName γlbuf γcpt), (γlbuf,γcpt))
    (λ '(γlbuf, γcpt), Some (ChanLogBufName γlbuf γcpt)) _); by intros [].
Qed.

Global Instance chan_name_inhabited : Inhabited chan_name :=
  populate (ChanName inhabitant inhabitant inhabitant inhabitant inhabitant nroot).
Global Instance chan_name_eq_dec : EqDecision chan_name.
Proof. solve_decision. Qed.
Global Instance chan_name_countable : Countable chan_name.
Proof.
  refine (inj_countable (λ '(ChanName γp γTl γTr γRl γRr N),
                           (γp, γTl, γTr, γRl, γRr, N))
                        (λ '(γp, γTl, γTr, γRl, γRr, N),
                           Some (ChanName γp γTl γTr γRl γRr N)) _); by intros [].
Qed.

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
