From stdpp Require Import gmap.

From iris.base_logic Require Import invariants bi.
From iris.algebra Require Import agree auth excl gmap.

From aneris.algebra Require Import monotone.
From aneris.aneris_lang
  Require Import lang network tactics proofmode lifting resources.
From aneris.aneris_lang.lib
  Require Import list_proof lock_proof vector_clock_proof serialization_proof
    map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.prelude Require Import misc time.

From aneris.examples.crdt.spec
  Require Import crdt_events crdt_resources crdt_denot crdt_time crdt_base.
From aneris.examples.crdt.statelib.resources
  Require Import utils resources resources_inv resources_local resources_global resources_lock.

From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.user_model
  Require Import params model semi_join_lattices.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import utils gst lst.
From aneris.examples.crdt.statelib.proof
  Require Import spec events utils.

Instance timeinst : Log_Time := timestamp_time.

Ltac token_excl A B := (try (iDestruct (own_valid_2 with A) as %B; destruct B)).


(** Nomenclature:
  * In this file (in every section) there are physical and logical operations
  * and states. I will try to use the following names to help reading the proofs
  * and specifications.
  *
  *  → Operations:
  *    ↪ in AnerisLang      (type: val)  : op_v
  *    ↪ logical operations (type LogOp) : op_log
  *
  *  → States:
  *    ↪ serialized         (type: val)  : st_serialized
  *    ↪ in AnerisLang      (type: val)  : st_v
  *    ↪ logical operations (type LogSt) : st_log
  *    ↪ local states, STS  (type Lst) : lst
  *    ↪ global states, STS (type Gst) : lst
  *
  * Note on coherence:
  *
  * There are coherence predicates over these different versions of operations
  * and states:
  *
  * → Operations:
  *    ↪ LogOp → val : StLib_Op_Coh
  *
  * → States:
  *    ↪ val   ↔ serialized : StLib_StSerialization
  *    ↪ LogSt → val        : StLib_St_Coh
  *    ↪ Lst   → LogSt      : denotation
  *
  *)



Section ToBeMoved.
  Context `{!anerisG Mdl Σ}.

  (** TODO: factorize loop_forever and this spec.
    * The following has been copied from
    * [aneris/examples/rcb/proof/proof_of_network.v] *)
  Lemma wp_loop_forever (fv : val) P ip :
    {{{ {{{ P }}} fv #() @[ip] {{{ RET #(); P }}} ∗
        P
    }}}
      loop_forever fv @[ip]
    {{{ RET #(); False }}}.
  Proof.
    iIntros (ϕ) "[#Hfv HP] Hϕ".
    iLöb as "IH".
    rewrite /loop_forever.
    wp_pures.
    wp_bind (fv _).
    iApply ("Hfv" with "HP").
    iModIntro.
    iIntros "HP". do 2 wp_pure _.
    iApply ("IH" with "HP").
    done.
  Qed.

End ToBeMoved.

Section ToBeMoved'.

  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt}.

  Notation StLib_Serializable v := (Serializable StLib_StSerialization v).
  Record StLib_SerializableVal :=
    StLib_SerVal {StLib_SV_val : val;
            StLib_SV_ser : StLib_Serializable StLib_SV_val }.
  Coercion StLib_SV_val : StLib_SerializableVal >-> val.
  Existing Instance StLib_SV_ser.
  Arguments StLib_SerVal _ {_}.

End ToBeMoved'.



Section SocketProtolDefinition.

  Context {LogOp LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt}.
  Context `{!Internal_StLibG LogOp Σ, !StLib_GhostNames}.

  Definition socket_proto (repId : RepId) : socket_interp Σ :=
    λ m,
      let (from, to) := (m_sender m, m_destination m) in
      let mb := m_body m in
      (∃ (st_v: val) (st_log: LogSt) (h__local h__sub: event_set LogOp) (i: RepId),
        ⌜ CRDT_Addresses !! i = Some from ⌝ ∗
        ⌜ s_is_ser StLib_StSerialization st_v mb ⌝ ∗
        ⌜ StLib_St_Coh st_log st_v ⌝ ∗
        ⌜⟦h__local ∪ h__sub⟧ ⇝ st_log⌝ ∗
        StLib_OwnLocalSnap i h__local h__sub)%I.

  Global Instance socket_proto_Persistent (repId: RepId) (m: message):
    Persistent (socket_proto repId m).
  Proof. apply _. Qed.

  Definition socket_inv (repId: RepId) (h: socket_handle) (z: socket_address) (s: socket) : iProp Σ :=
    inv (nroot .@ "socketinv")
      (∃ R S,
        h ↪[ip_of_address z] s ∗
        ⌜ saddress s = Some z ⌝ ∗
        ⌜ CRDT_Addresses !! repId = Some z ⌝ ∗
        z ⤳ (R, S) ∗
        [∗ set] m ∈ R, socket_proto repId m).

End SocketProtolDefinition.



Section LockInvariant.

  Context {LogOp LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt}.
  Context `{!Internal_StLibG LogOp Σ, !StLib_GhostNames}.

  Definition lock_inv_aux (i : RepId) (st_loc : loc) : iProp Σ :=
    ∃ (ip : ip_address) (phys_st : val) (log_st : LogSt)
      (h__own h__for : gset (Event LogOp)),
      ⌜ip_of_address <$> CRDT_Addresses !! i = Some ip⌝ ∗
      st_loc ↦[ip] phys_st ∗
      ⌜StLib_St_Coh log_st phys_st⌝ ∗
      OwnLockInv i h__own h__for ∗
      ⌜⟦h__own ∪ h__for⟧ ⇝ log_st⌝.

  Definition lock_inv_ns := nroot.@"lock_inv_ns".

  Definition lock_inv (saddr : socket_address) (γ__lock : gname) (lockv : val)
                      (i : nat) (st_loc : loc) : iProp Σ :=
    is_lock lock_inv_ns (ip_of_address saddr) γ__lock lockv (lock_inv_aux i st_loc).

End LockInvariant.
