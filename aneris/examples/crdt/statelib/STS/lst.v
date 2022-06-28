From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap sets.
From aneris.prelude Require Import misc gset_map.
From aneris.examples.crdt Require Import crdt_spec crdt_events crdt_time.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.time Require Import time maximality.

Section Lst_definition.
  Context `{!anerisG Mdl Σ, !CRDT_Params}.
  Context `{Op: Type, !EqDecision Op, !Countable Op}.

  Definition Lst : Type := event_set Op.

  Definition event_set_orig_lt_len (ls: Lst) :=
    @event_set_orig_lt _ _ _ (length CRDT_Addresses) ls.

  Definition event_set_orig_max_len (ls: Lst) :=
    @event_set_orig_max _ _ _ (length CRDT_Addresses) ls.
  
  Definition event_set_seqid_val (ls: Lst) : Prop :=
    ∀ ev, ev ∈ ls → get_seqnum ev =
      size (filter (λ v: EvId, v.1 = ev.(EV_Orig)) ev.(EV_Time)).
     
  Definition event_set_evid_incl_event (ls: Lst): Prop :=
    ∀ ev, ev ∈ ls → get_evid ev ∈ get_deps ev.

  Definition event_set_seqnum_non_O (ls: Lst) :=
    ∀ ev, ev ∈ ls → (O < get_seqnum ev)%nat.

  Record Lst_Validity (ls: Lst) :=
    {
      VLst_dep_closed : dep_closed ls;
      VLst_same_orig_comp : event_set_same_orig_comparable ls;
      VLst_ext_eqid : events_ext_evid ls;
      VLst_ext_time : events_ext_time ls;
      VLst_orig : event_set_orig_lt_len ls;
      VLst_seqid_val : event_set_seqid_val ls;
      VLst_orig_deps_seq : event_set_orig_deps_seq ls;
      VLst_seqnum_non_O : event_set_seqnum_non_O ls;
      VLst_orig_max : event_set_orig_max_len ls;
      VLst_evid_mon : event_set_evid_mon ls;
      VLst_evid_incl_event: event_set_evid_incl_event ls;
    }.
    Arguments VLst_orig {_ _ _} ls.

End Lst_definition.
Arguments Lst (Op) {_ _}.

