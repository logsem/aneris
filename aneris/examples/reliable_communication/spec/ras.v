From aneris.algebra Require Import monotone.
From iris.algebra Require Import gmap agree auth numbers excl frac_auth gset csum.
From iris.algebra.lib Require Import excl_auth mono_nat.
From iris.base_logic.lib Require Import mono_nat.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof.
From actris.channel Require Import proto.
From aneris.examples.reliable_communication.spec Require Import prelude.
From aneris.examples.reliable_communication.resources Require Import session_escrow.

Definition session_names_mapUR : ucmra :=
  gmapUR socket_address (agreeR (leibnizO (session_name))).
Definition session_names_map :=
  gmap socket_address (leibnizO (session_name)).

Notation socket_addressO := (leibnizO socket_address).

Definition oneShotR := csumR (exclR unitO) (agreeR unitO).

Class SpecChanG Σ := {
    SpecChanG_session_escrow :> session_escrowG Σ val;
    SpecChanG_ids :> mono_natG Σ;
    SpecChanG_cookie :> inG Σ (frac_authR natR);
    SpecChanG_session_names_map :>
      inG Σ (authR (gmapUR socket_address (agreeR (leibnizO (session_name)))));
    SpecChanG_address :> inG Σ (agreeR (prodO socket_addressO socket_addressO));
    SpecChanG_side :> inG Σ (agreeR (leibnizO side));
    SpecChanG_idxs :> inG Σ (agreeR (prodO locO locO));
    SpecChanG_mhst :> inG Σ (authUR (gsetUR message));
    SpecChanG_status :> inG Σ oneShotR;
    SpecChanG_lock :> lockG Σ;
   }.

Definition SpecChanΣ : gFunctors :=
  #[ session_escrowΣ val;
     mono_natΣ;
     GFunctor (frac_authR natR);
     GFunctor (authR (gmapUR socket_address (agreeR (leibnizO (session_name)))));
     GFunctor (agreeR (prodO socket_addressO socket_addressO));
     GFunctor (agreeR (leibnizO side));
     GFunctor (agreeR (prodO locO locO));
     GFunctor (authUR (gsetUR message));
     GFunctor oneShotR;
     lockΣ
    ].

#[global] Instance subG_SPecChanΣ {Σ} : subG SpecChanΣ Σ → SpecChanG Σ.
Proof. econstructor; solve_inG. Qed.
