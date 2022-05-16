From aneris.algebra Require Import monotone.
From iris.algebra Require Import gmap agree auth numbers excl frac_auth gset csum.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import mono_nat.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Export inject.
From aneris.aneris_lang.lib.serialization Require Export serialization_proof.
From actris.channel Require Export proto.
From aneris.examples.reliable_communication.prelude Require Export ser_inj list_minus.
From aneris.examples.reliable_communication.spec Require Export prelude.

(** Serialization. *)

Definition id_serialization := int_serialization.
Definition init_serialization :=
  (prod_serialization string_serialization int_serialization).

Definition idmsg_serialization payload_ser :=
  sum_serialization
    int_serialization
    (prod_serialization int_serialization payload_ser).

Definition msg_serialization payload_ser :=
  sum_serialization init_serialization (idmsg_serialization payload_ser).

Definition socket_address_to_str (sa : socket_address) : string :=
  match sa with SocketAddressInet ip p => ip +:+ (string_of_pos p) end.

(** Side switch. *)

Definition side_elim {A} (s : side) (l r : A) : A :=
  match s with
  | Left => l
  | Right => r
  end.

Definition dual_side (s : side) : side :=
  match s with
  | Left => Right
  | Right => Left
  end.

(** ===================== INTERNAL GLOBAL SERVER GHOST NAMES  ===================== *)

Class server_ghost_names :=
  ServerGhostNames {
    γ_srv_known_sessions_name : gname;
    γ_srv_known_messages_R_name : gname;
    γ_srv_known_messages_T_name : gname;
}.


(** ====================== INTERNAL ALGEBRA DEFINITIONS  ======================== *)

Definition chan_msg_history (A : ofe) :=
  authUR (@monotoneUR (listO A) (prefix)).
Notation PrinCMH l := (principal prefix l).

Class ChanMsgHist A Σ := {
    CMH_msghΣ :> inG Σ (chan_msg_history A);
    CMH_msgcΣ :> inG Σ (frac_authR natR)
  }.

Definition ChanMsgHistΣ A : gFunctors :=
  #[GFunctor (chan_msg_history A);
    GFunctor (frac_authR natR)].

Global Instance subG_ChanMsgHistΣ A {Σ} :
  subG (ChanMsgHistΣ A) Σ → ChanMsgHist A Σ.
Proof. solve_inG. Qed.

Definition session_names_mapUR : ucmra :=
  gmapUR socket_address (agreeR (leibnizO (session_name))).
Definition session_names_map :=
  gmap socket_address (leibnizO (session_name)).

Definition oneShotR := csumR (exclR unitO) (agreeR unitO).


(** Algebras for tracking resources in the logic, including meta tokens. *)
Class chanPreG Σ := {
    chanGPreG_proto :> protoG Σ val;
    chanGPreG_chan_logbuf :> ChanMsgHist valO Σ;
    chanGPreG_ids :> mono_natG Σ;
    chanGPreG_cookie :> inG Σ (frac_authR natR);
    chanGPreG_session_names_map :> inG Σ (authR session_names_mapUR);
    chanGPreG_address :> inG Σ (agreeR (prodO socket_addressO socket_addressO));
    chanGPreG_side :> inG Σ (agreeR (leibnizO side));
    chanGPreG_idxs :> inG Σ (agreeR (prodO locO locO));
    chanGPreG_mhst :> inG Σ (authUR (gsetUR message));
    chanGPreG_status :> inG Σ oneShotR;
   }.

Class chanG Σ := {
    chanG_protoG :> protoG Σ val;
    chanG_chan_logbufG :> ChanMsgHist valO Σ;
    chanG_ids :> mono_natG Σ;
    chanG_cookie :> inG Σ (frac_authR natR);
    chanG_session_names_map :> inG Σ (authR session_names_mapUR);
    chanG_address :> inG Σ (agreeR (prodO socket_addressO socket_addressO));
    chanG_side :> inG Σ (agreeR (leibnizO side));
    chanG_idxs :> inG Σ (agreeR (prodO locO locO));
    chanG_mhst :> inG Σ (authUR (gsetUR message));
    chanG_status :> inG Σ oneShotR;
  }.

Definition chanPreΣ : gFunctors :=
  #[ protoΣ val;
     ChanMsgHistΣ valO;
     mono_natΣ;
     GFunctor (frac_authR natR);
     GFunctor (authR session_names_mapUR);
     GFunctor (agreeR (prodO socket_addressO socket_addressO));
     GFunctor (agreeR (leibnizO side));
     GFunctor (agreeR (prodO locO locO));
     GFunctor (authUR (gsetUR message));
     GFunctor oneShotR
    ].

Global Instance subG_chanPreΣ {Σ} : subG chanPreΣ Σ → chanPreG Σ.
Proof. solve_inG. Qed.
