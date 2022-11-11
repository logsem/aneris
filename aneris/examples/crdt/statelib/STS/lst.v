From aneris.aneris_lang Require Import lang.
From aneris.examples.crdt Require Import crdt_spec.
From aneris.examples.crdt.statelib.time Require Import time maximality.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.prelude Require Import gset_map.

Section Lst_definition.
  Context `{!CRDT_Params,
            Op: Type, !EqDecision Op, !Countable Op}.

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


(* TODO: prove lemma. *)
Section Lst_helper.
  Context `{!CRDT_Params, Op: Type, !EqDecision Op, !Countable Op}.

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

  Definition fil (s: event_set Op) (i: nat) : event_set Op :=
    filter (λ ev: Event Op, EV_Orig ev = i) s.

  Lemma lst_validity_valid_event_map
        {Op' : Type} `{!EqDecision Op'} `{!Countable Op'}
        s  (f : Op → Op') :
    Lst_Validity s  → Lst_Validity (gset_map (event_map f) s).
  Proof. Admitted.


  Lemma lst_validity_filtered (s s': event_set Op) :
    Lst_Validity s
    → Lst_Validity s'
    → Lst_Validity (s ∪ s')
    → ∀ (i: nat), fil s i ⊆ fil s' i ∨ fil s' i ⊆  fil s i.
  Proof.
    intros Hv Hv' Hv'' i.
    destruct (decide ( fil ( s ∪ s' ) i = ∅ )) as [ | n ]; first (left; set_solver).
    epose proof (iffLR (compute_maximum_non_empty (fil (s ∪ s') i) _ _) n)
      as (m & [[Hm_orig [Hm_in|Hm_in]%elem_of_union]%elem_of_filter Hm_ismax]%compute_maximum_correct); last first.
    { intros??[_?]%elem_of_filter[_?]%elem_of_filter?.
      by apply (VLst_ext_time _ Hv''). }
    1: left. 2: right.
    all: intros x [Hx_orig Hx_in]%elem_of_filter.
    all: apply elem_of_filter; split; try assumption.
    all: destruct (decide (x = m)) as [ -> | ]; first assumption.
    all: assert (Hx: x ∈ fil (s ∪ s') i); first set_solver.
    all: pose proof (Hm_ismax x Hx n0).
    1: pose proof (VLst_evid_incl_event _ Hv x Hx_in).
    2: pose proof (VLst_evid_incl_event _ Hv' x Hx_in).
    all: assert (H2: get_evid x ∈ EV_Time m); first set_solver.
    + destruct (VLst_dep_closed _ Hv' m (get_evid x) Hm_in H2)
        as (x' & Hx'_in & Hx'_evid).
      by rewrite <-(VLst_ext_eqid _ Hv''
                                 x' x (elem_of_union_r x' s s' Hx'_in) (elem_of_union_l x s s' Hx_in)
                                 Hx'_evid).
    + destruct (VLst_dep_closed _ Hv m (get_evid x) Hm_in H2)
        as (x' & Hx'_in & Hx'_evid).
      by rewrite <-(VLst_ext_eqid _ Hv''
                                 x' x (elem_of_union_l x' s s' Hx'_in) (elem_of_union_r x s s' Hx_in)
                                 Hx'_evid).
      Unshelve.
      all: intros x y [Hx_orig Hx_in]%elem_of_filter [Hy_orig Hy_in]%elem_of_filter.
      apply (VLst_same_orig_comp _ Hv'' _ _ Hx_in Hy_in).
      by rewrite Hx_orig Hy_orig.
      apply (VLst_ext_time _ Hv'' _ _ Hx_in Hy_in).
  Qed.

End Lst_helper.
