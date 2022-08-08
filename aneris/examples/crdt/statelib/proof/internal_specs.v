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
  Require Import resources resources_inv resources_local resources_global resources_lock.

From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.user_model
  Require Import params model semi_join_lattices.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import utils gst lst.
From aneris.examples.crdt.statelib.proof
  Require Import spec events resources utils resources
    stlib_proof_utils.

Instance timeinst : Log_Time := timestamp_time.

Section StateLib_InternalSpecs.

  Context `{LogOp: Type, LogSt : Type,
            !anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt,
            !Internal_StLibG LogOp Σ, !StLib_GhostNames,
            st_deser: val, stser: serialization}.

  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  Definition internal_get_state_spec
    (get_state : val) (repId : nat) (addr : socket_address) : iProp Σ :=
    ⌜CRDT_Addresses !! repId = Some addr⌝ -∗
     <<< ∀∀ (s1 s2 : event_set LogOp), StLib_OwnLocalState repId s1 s2 >>>
       get_state #() @[ip_of_address addr] ↑CRDT_InvName
     <<<▷ ∃∃ (s2' : event_set LogOp) (phys_st : val) (log_st : LogSt), RET phys_st;
             ⌜s2 ⊆ s2'⌝ ∗
             StLib_OwnLocalState repId s1 s2' ∗
             ⌜StLib_St_Coh log_st phys_st⌝ ∗
             ⌜⟦s1 ∪ s2'⟧ ⇝ log_st⌝ >>>.

  Definition internal_update_spec (update : val) (repId : nat) (addr : socket_address) : iProp Σ :=
    ∀ (op : val) (log_op : LogOp),
    ⌜CRDT_Addresses !! repId = Some addr⌝ -∗
    ⌜StLib_Op_Coh log_op op⌝ -∗
    <<< ∀∀ (h s1 s2 : gset (Event LogOp)),
           StLib_OwnGlobalState h ∗
           StLib_OwnLocalState repId s1 s2 >>>
      update op @[ip_of_address addr] ↑CRDT_InvName
    <<<▷ ∃∃ (e : Event LogOp) (h' s1' s2' : event_set LogOp), RET #();
           ⌜e.(EV_Op) = log_op⌝ ∗
           ⌜e.(EV_Orig) = repId⌝ ∗
           ⌜h' = h ∪ {[ e ]}⌝ ∗
           ⌜s1' = s1 ∪ {[ e ]}⌝ ∗
           ⌜s2 ⊆ s2'⌝ ∗
           ⌜e ∉ h⌝ ∗
           ⌜e ∉ s1⌝ ∗
           ⌜e ∈ Maximals h'⌝ ∗
           ⌜Maximum (s1' ∪ s2') = Some e⌝ ∗
           StLib_OwnGlobalState h' ∗
           StLib_OwnLocalState repId s1' s2' >>>.

End StateLib_InternalSpecs.

