From aneris.aneris_lang Require Import resources.
From aneris.aneris_lang.lib Require Import serialization_proof.
From aneris.examples.crdt.spec Require Import crdt_spec.
From aneris.examples.crdt.statelib.proof Require Import events.
From aneris.examples.crdt.statelib.STS Require Import lst.
From aneris.examples.crdt.statelib.user_model
  Require Import model semi_join_lattices.

Section Params.
  Context `{LogOp: Type, LogSt: Type,
            !anerisG Mdl Σ,
            !EqDecision LogOp, !Countable LogOp, !Lattice LogSt,
            !CRDT_Params, !EventSetValidity LogOp}.

  (* User-supplied parameters when using the library. *)
  Class StLib_Params := {
    (* Serialization of operations. *)
    StLib_StSerialization : serialization;

    (* CRDT model *)
    StLib_Denot :> CrdtDenot LogOp LogSt;
    StLib_Model :> StateCrdtModel LogOp LogSt;

    (* Coherence between logical and physical state: for
       states, operations, and events (event = operation + timestamp).

       For example, for a counter CRDT the logical state is
       (morally) an integer, while the physical state is an
       AnerisLang `val` (containing the integer).
       The correspondence is trivial in that case, but can
       be more complicated for other CRDTs. *)
    StLib_Op_Coh : LogOp -> val -> Prop;
    StLib_Op_Coh_Inj o1 o2 v : StLib_Op_Coh o1 v -> StLib_Op_Coh o2 v -> o1 = o2;
    StLib_St_Coh : LogSt -> val -> Prop;
    StLib_St_Coh_Inj o1 o2 v : StLib_St_Coh o1 v -> StLib_St_Coh o2 v -> o1 = o2;
    StLib_StCoh_Ser st v : StLib_St_Coh st v -> Serializable StLib_StSerialization v;
  }.

  Class StLib_Res `{!CRDT_Params} := {
    StLib_CRDT_Res :> CRDT_Res_Mixin Mdl Σ LogOp;
    StLib_InitToken : (fin (length CRDT_Addresses)) -> iProp Σ;
    StLib_SocketProto : socket_interp Σ;
  }.

End Params.

Global Arguments StLib_Params (LogOp LogSt) {_ _ _ _ _}.
Global Arguments StLib_Res (LogOp) {_ _ _ _ _ _}.

