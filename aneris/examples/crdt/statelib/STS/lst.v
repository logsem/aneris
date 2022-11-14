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

  Lemma event_map_inv {Op' : Type} `{!EqDecision Op'} `{!Countable Op'}
        (f : Op → Op') (ev0 : Event Op) (ev : Event Op') :
        event_map f ev0 = ev →
        EV_Op ev = f (EV_Op ev0) ∧ EV_Orig ev0 = EV_Orig ev ∧ EV_Time ev0 = EV_Time ev.
  Proof. intros Heq. naive_solver. Qed.

  Lemma event_map_elem_of
        {Op' : Type} `{!EqDecision Op'} `{!Countable Op'}
        (f : Op → Op') (ev : Event Op') (s : gset (Event Op)) :
    ev ∈ gset_map (event_map f) s → ∃ ev0, ev0 ∈ s ∧ event_map f ev0 = ev.
  Proof.
    intros Hev. apply gset_map_correct2 in Hev. set_solver.
  Qed.

  Lemma lst_validity_valid_event_map
        {Op' : Type} `{!EqDecision Op'} `{!Countable Op'}
        (s : gset (Event Op))  (f : Op → Op') :
    Lst_Validity s  → Lst_Validity (gset_map (event_map f) s).
  Proof.
    destruct 1 as [Hl1 Hl2 Hl3 Hl4 Hl5 Hl6 Hl7 Hl8 Hl9 Hl10 Hl11 Hl12].
    split.
    - intros ev id Hev Hid.
      pose proof (event_map_elem_of f ev s Hev) as (ev0 & Hin0 & Hev0).
      destruct (event_map_inv f ev0 ev Hev0) as (Heq1 & Heq2 & Heq3).
      rewrite -Heq3 in Hid.
      specialize (Hl1 ev0 id Hin0 Hid) as (ev1 & Hdep).
      exists (event_map f ev1).
      set_solver.
    - intros ev0 ev1 Hev0 Hev1 Heq1.
      pose proof (event_map_elem_of f ev0 s Hev0) as (ev & Hin & Hev).
      pose proof (event_map_elem_of f ev1 s Hev1) as (ev' & Hin' & Hev').
      destruct (event_map_inv f ev ev0 Hev) as (HevEq1 & HevEq2 & HevEq3).
      destruct (event_map_inv f ev' ev1 Hev') as (Hev'Eq1 & Hev'Eq2 & Hev'Eq3).
      assert (EV_Orig ev = EV_Orig ev') as HeqOrig by naive_solver.
      specialize (Hl2 ev ev' Hin Hin' HeqOrig).
      set_solver.
    - intros ev0 ev1 Hev0 Hev1 Heq.
      pose proof (event_map_elem_of f ev0 s Hev0) as (ev & Hin & Hev).
      pose proof (event_map_elem_of f ev1 s Hev1) as (ev' & Hin' & Hev').
      destruct (event_map_inv f ev ev0 Hev) as (HevEq1 & HevEq2 & HevEq3).
      destruct (event_map_inv f ev' ev1 Hev') as (Hev'Eq1 & Hev'Eq2 & Hev'Eq3).
      assert (get_evid ev = get_evid ev') as Heqg.
      { rewrite /get_evid. f_equal; first by naive_solver.
        rewrite /get_seqnum. naive_solver. }
      specialize (Hl3 ev ev' Hin Hin' Heqg).
      by subst.
    - intros ev0 ev1 Hev0 Hev1 Heq.
      pose proof (event_map_elem_of f ev0 s Hev0) as (ev & Hin & Hev).
      pose proof (event_map_elem_of f ev1 s Hev1) as (ev' & Hin' & Hev').
      destruct (event_map_inv f ev ev0 Hev) as (HevEq1 & HevEq2 & HevEq3).
      destruct (event_map_inv f ev' ev1 Hev') as (Hev'Eq1 & Hev'Eq2 & Hev'Eq3).
      assert (EV_Time ev = EV_Time ev') as HeqTime by naive_solver.
      specialize (Hl4 ev ev' Hin Hin' HeqTime).
      by subst.
    - intros ev Hev.
      pose proof (event_map_elem_of f ev s Hev) as (ev0 & Hin0 & Hev0).
      destruct (event_map_inv f ev0 ev Hev0) as (Heq1 & Heq2 & Heq3).
      rewrite -Heq2.
      by apply Hl5.
    - intros ev Hev.
      pose proof (event_map_elem_of f ev s Hev) as (ev0 & Hin0 & Hev0).
      destruct (event_map_inv f ev0 ev Hev0) as (Heq1 & Heq2 & Heq3).
      rewrite -Heq3 -Heq2.
      assert (get_seqnum ev = get_seqnum ev0) as -> by naive_solver.
      by apply Hl6.
    - intros ev Hev i sid Hsid Hle.
      pose proof (event_map_elem_of f ev s Hev) as (ev0 & Hin0 & Hev0).
      destruct (event_map_inv f ev0 ev Hev0) as (Heq1 & Heq2 & Heq3).
      rewrite -Heq3.
      assert (get_evid ev = get_evid ev0) as Heqg.
      { rewrite /get_evid. f_equal; first by naive_solver.
        rewrite /get_seqnum. naive_solver. }
      apply Hl7; naive_solver.
    - intros ev Hev.
      pose proof (event_map_elem_of f ev s Hev) as (ev0 & Hin0 & Hev0).
      destruct (event_map_inv f ev0 ev Hev0) as (Heq1 & Heq2 & Heq3).
      assert (get_seqnum ev = get_seqnum ev0) as -> by naive_solver.
      by apply Hl8.
    - intros i Hi.
      specialize (Hl9 i Hi) as [Hl9|Hl9].
      -- left. set_solver.
      -- right.
         destruct Hl9 as (m & Hm & Hmm).
         assert ((event_map f m) ∈ gset_map (event_map f) s ∧ EV_Orig ((event_map f m)) = i)
           as Hfm.
         {  split; first by set_solver.
             destruct (event_map_inv f m (event_map f m)) as (Heq1 & Heq2 & Heq3); first done.
             rewrite -Heq2.
             apply compute_maximum_correct in Hmm.
             -- destruct Hmm as (Hmm0 & Hmm1).
                set_solver.
             -- intros x y Hx Hy Ht. apply Hl4; set_solver. }
         assert (∃ m0 : Event Op', compute_maximum (hproj i (gset_map (event_map f) s)) = Some m0)
           as (m0 & Hm0).
         { apply (event_set_maximum_exists (gset_map (event_map f) s) i).
           - exists (event_map f m). apply Hfm.
           - intros ev0 ev1 Hev0 Hev1 Heq1.
             pose proof (event_map_elem_of f ev0 s Hev0) as (ev & Hin & Hev).
             pose proof (event_map_elem_of f ev1 s Hev1) as (ev' & Hin' & Hev').
             destruct (event_map_inv f ev ev0 Hev) as (HevEq1 & HevEq2 & HevEq3).
             destruct (event_map_inv f ev' ev1 Hev') as (Hev'Eq1 & Hev'Eq2 & Hev'Eq3).
             assert (EV_Orig ev = EV_Orig ev') as HeqOrig by naive_solver.
             specialize (Hl2 ev ev' Hin Hin' HeqOrig).
             set_solver.
           -  intros ev0 ev1 Hev0 Hev1 Heq.
              pose proof (event_map_elem_of f ev0 s Hev0) as (ev & Hin & Hev).
              pose proof (event_map_elem_of f ev1 s Hev1) as (ev' & Hin' & Hev').
              destruct (event_map_inv f ev ev0 Hev) as (HevEq1 & HevEq2 & HevEq3).
              destruct (event_map_inv f ev' ev1 Hev') as (Hev'Eq1 & Hev'Eq2 & Hev'Eq3).
              assert (EV_Time ev = EV_Time ev') as HeqTime by naive_solver.
              specialize (Hl4 ev ev' Hin Hin' HeqTime).
              by subst. }
         assert ((event_map f) <$> (compute_maximum (hproj i s)) = Some (event_map f m)) as Heq1.
         by rewrite Hmm.
         exists m0. split; last done.
         assert ( ∀ (X : gset (Event Op')) e, compute_maximum X = Some e → e ∈ X) as HeX.
         { intros X e Hmax.
           apply elem_of_compute_maximals.
           rewrite /compute_maximum in Hmax.
           apply elem_of_elements.
           destruct (elements (compute_maximals X)) as [|x [|]]; try naive_solver.
           set_solver.
         }
         pose proof (HeX _ m0 Hm0).
         set_solver.
    - intros ev0 ev1 Hev0 Hev1 Heq.
      pose proof (event_map_elem_of f ev0 s Hev0) as (ev & Hin & Hev).
      pose proof (event_map_elem_of f ev1 s Hev1) as (ev' & Hin' & Hev').
      destruct (event_map_inv f ev ev0 Hev) as (HevEq1 & HevEq2 & HevEq3).
      destruct (event_map_inv f ev' ev1 Hev') as (Hev'Eq1 & Hev'Eq2 & Hev'Eq3).
      assert (EV_Orig ev = EV_Orig ev') as HeqOrig by naive_solver.
      specialize (Hl10 ev ev' Hin Hin' HeqOrig).
      by subst.
    - intros ev Hev.
      pose proof (event_map_elem_of f ev s Hev) as (ev0 & Hin0 & Hev0).
      destruct (event_map_inv f ev0 ev Hev0) as (Heq1 & Heq2 & Heq3).
      specialize (Hl11 ev0 Hin0).
      assert (get_evid ev0 = get_evid ev) as Heqg.
      { rewrite /get_evid. f_equal; first by naive_solver.
        rewrite /get_seqnum. naive_solver. }
      rewrite Heqg in Hl11.
      set_solver.
    - intros ev0 ev1 Hev0 Hev1 Heq.
      pose proof (event_map_elem_of f ev0 s Hev0) as (ev & Hin & Hev).
      pose proof (event_map_elem_of f ev1 s Hev1) as (ev' & Hin' & Hev').
      destruct (event_map_inv f ev ev0 Hev) as (HevEq1 & HevEq2 & HevEq3).
      destruct (event_map_inv f ev' ev1 Hev') as (Hev'Eq1 & Hev'Eq2 & Hev'Eq3).
      set_solver.
  Qed.

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
