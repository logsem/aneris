From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap sets.
From aneris.prelude Require Import misc gset_map.
From aneris.examples.crdt Require Import crdt_spec crdt_events crdt_time.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.time Require Import time maximality.

Section Lst_definition.
  Context `{!CRDT_Params}.
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
      VLst_evid_incl_time_le: ∀ ev ev', ev ∈ ls → ev' ∈ ls → get_evid ev' ∈ EV_Time ev → ev' ≤_t ev;
    }.
    Arguments VLst_orig {_ _ _} ls.

End Lst_definition.
Arguments Lst (Op) {_ _}.



Section Lst_helper.
  Context `{!CRDT_Params}.
  Context `{Op: Type, !EqDecision Op, !Countable Op}.

  Lemma Lst_Validity_implies_event_set_valid (s: Lst Op):
    Lst_Validity s → event_set_valid s.
  Proof.
    intros [Hdc Horig_comp Hext_eid Hext_time Horig Hseqid Horig_depseq Hseqnum Horig_max Hevis_mon Hevis_incl_ev].
    split; first done.
    intros e e' He_in He'_in. split.
    - intros Hevs_orig.
      destruct Horig_comp with e e' as [? |[-> |?]]; try done.
      + left. by apply strict_include.
      + by left.
      + right. by apply strict_include.
    - intros Hevs_eqt.
      by destruct Hext_time with e e'.
  Qed.

  Lemma Lst_Validity_implies_events_ext (s: Lst Op):
    Lst_Validity s → events_ext s.
  Proof. by intros []. Qed.
  Lemma Lst_Validity_implies_same_orig_comparable (s: Lst Op):
    Lst_Validity s → event_set_same_orig_comparable s.
  Proof. by intros []. Qed.


  Lemma lst_init_valid:
    Lst_Validity (∅: Lst Op).
  Proof.
    split; try done.
    intros??. by left.
  Qed.
End Lst_helper.
