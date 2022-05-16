From stdpp Require Import gmap.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.crdt.spec Require Import crdt_base crdt_resources.
From aneris.examples.crdt.oplib.spec Require Import spec.

(** * Instantiation of RCB params given crdt params *)

Section RCB_Params.

  (* Invariant names:
     To manage invariant names, we receive as argument a root namespace
     CRDT_Invname. Within it, we then create _two_ sub namespaces:
     1) one for use by RCB's global invariant: .@ "RCB_Inv".
     2) the other for use by Oplib's invariant: .@ "OpLib_Inv"
        (see proof.v)
  *)
  Context `{!CRDT_Params, !EqDecision LogOp, !Countable LogOp, !OpLib_Params LogOp LogST}.

  Definition OpLib_InvName := CRDT_InvName .@ "OpLib_Inv".

  Global Instance RCB_Params_From_CRDT : RCB_params := {
    RCB_addresses := CRDT_Addresses;
    RCB_addresses_NoDup := CRDT_Addresses_NoDup;
    RCB_InvName := CRDT_InvName .@ "RCB_Inv";
    RCB_serialization := OpLib_Serialization;
  }.

  Lemma rcb_invname_subseteq : (↑RCB_InvName : coPset) ⊆ ↑CRDT_InvName.
  Proof.
    apply nclose_subseteq.
  Qed.

  Lemma rcb_invname_subseteq' (E : coPset) : ↑CRDT_InvName ⊆ E -> ↑RCB_InvName ⊆ E.
  Proof.
    apply nclose_subseteq'.
  Qed.

  Lemma rcb_invname_diff_subseteq :
    (↑RCB_InvName : coPset) ⊆ ↑CRDT_InvName ∖ ↑OpLib_InvName.
  Proof.
    assert ((↑RCB_InvName : coPset) ## ↑OpLib_InvName) as Hdisj.
    { apply ndot_ne_disjoint.
      done. }
    pose proof rcb_invname_subseteq as Hsub.
    set_solver.
  Qed.

  Lemma rcb_invname_subseteq_mask E :
    (↑CRDT_InvName : coPset) ⊆ E -> ↑RCB_InvName ⊆ E ∖ ↑OpLib_InvName.
  Proof.
    intros Hsub.
    pose proof rcb_invname_diff_subseteq.
    set_solver.
  Qed.

  Lemma crdt_invname_subseteq : (↑OpLib_InvName : coPset) ⊆ ↑CRDT_InvName.
  Proof.
    apply nclose_subseteq.
  Qed.

  Lemma crdt_invname_subseteq' (E : coPset) : ↑CRDT_InvName ⊆ E -> ↑OpLib_InvName ⊆ E.
  Proof.
    apply nclose_subseteq'.
  Qed.

End RCB_Params.
