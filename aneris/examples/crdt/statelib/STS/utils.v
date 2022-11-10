(** TODO: get rid of the aneris resources here. **)
From aneris.aneris_lang Require Import lang resources.
From aneris.prelude Require Import gset_map.
From aneris.examples.crdt Require Import crdt_spec.
From aneris.examples.crdt.statelib.time Require Import time maximality.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.STS Require Import lst gst.

Section UsefulLemmas.
  Lemma vec_incl_in_list_union `{T: Type, !EqDecision T, !Countable T, n: nat}
    (v: vec (gset T) n) (o: fin n) :
    v !!! o ⊆ union_list v.
  Proof.
    apply elem_of_subseteq. intros elt Helt_in.
    apply elem_of_union_list.
    exists (v !!! o). split; last assumption.
    rewrite elem_of_vlookup.
    by exists o.
  Qed.

  Lemma union_empty_R `{T: Type, EqDecision T, Countable T} (g: gset T):
    g ∪ (∅: gset T) = g.
  Proof. set_solver. Qed.

  Lemma union_empty_L `{T: Type, EqDecision T, Countable T} (g: gset T):
    (∅: gset T) ∪ g = g.
  Proof. set_solver. Qed.
End UsefulLemmas.

Section Preambule.
  Context `{!CRDT_Params,
            Op: Type, !EqDecision Op, !Countable Op}.

  Lemma get_evid_valid_time (ev: @Event timestamp_time Op):
    ev.(EV_Orig) = (get_evid ev).1.
  Proof. reflexivity. Qed.

  Lemma get_deps_set_incl (s: gset (@Event timestamp_time Op)):
    dep_closed s →
    ∀ (eid: EvId), eid ∈ get_deps_set s → ∃ ev, ev ∈ s ∧ get_evid ev = eid.
  Proof.
    intros Hdc eid (ev & Hev_in & Heid_in)%elem_of_gset_flat_map_2.
    destruct (Hdc ev eid Hev_in Heid_in) as (ev' & ? & Heq).
    by exists ev'.
  Qed.

  Lemma get_deps_set_mon (s s': event_set Op):
    s ⊆ s' → get_deps_set s ⊆ get_deps_set s'.
  Proof.
    intros Hsub.
    apply elem_of_subseteq.
    intros eid (X & HX_in%elem_of_elements & Heid_in)%elem_of_union_list.
    apply elem_of_union_list.
    set_solver.
  Qed.

  Lemma get_deps_singleton (ev: Event Op) :
    get_deps_set {[ev]} = ev.(EV_Time).
  Proof.
    unfold get_deps_set.
    unfold gset_flat_map.
    rewrite gset_map_singleton elements_singleton.
    set_solver.
  Qed.

  Lemma get_evid_eq (ev: Event Op) (orig : RepId) (deps: SeqNum):
    get_evid ev = (orig, deps) → ev.(EV_Orig) = orig ∧ get_seqnum ev = deps.
  Proof.
    unfold get_evid. intros Heq.
    by apply pair_equal_spec in Heq as [-> ->].
  Qed.

  Lemma filter_set_mono (s s': gset EvId) (P: EvId → Prop) `{!(∀ x : EvId, Decision (P x))}:
    s ⊆ s' → filter P s ⊆ filter P s'.
  Proof. set_solver. Qed.

  Lemma event_set_seqnum_max (s: event_set Op) (orig: RepId) :
    ∀ (i: nat),
    dep_closed s →
    event_set_seqid_val s →
    (∀ ev, ev ∈ s → get_evid ev ∈ ev.(EV_Time)) →
    lt (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s))) i →
    (orig, i) ∉ get_deps_set s.
  Proof.
    intros i Hdc Hseqidval Heidin Hlt Himp.
    destruct (get_deps_set_incl s Hdc _ Himp) as (ev & Hev_in & [Hev_orig Hev_sid]%get_evid_eq).
    unfold get_seqnum in Hev_sid.
    assert (
    i < i)%nat; last lia.
    apply Nat.le_lt_trans
      with (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s)));
      last assumption.
    rewrite -Hev_sid Hev_orig.
    apply subseteq_size, filter_set_mono.
    rewrite -get_deps_singleton.
    by apply get_deps_set_mon, singleton_subseteq_l.
  Qed.

  Lemma event_set_evid_in_time (st: event_set Op) {ev: Event Op} (Hin: ev ∈ st) :
    event_set_orig_deps_seq st → event_set_seqnum_non_O st → get_evid ev ∈ ev.(EV_Time).
  Proof.
    intros Hseq HO. apply (Hseq ev Hin ev.(EV_Orig) (get_seqnum ev)); last done.
    assert (0%nat < get_seqnum ev)%nat; [by apply HO | lia ].
  Qed.

  Lemma fresh_event_orig (s: event_set Op) (op: Op) (orig: RepId):
    (fresh_event s op orig).(EV_Orig) = orig.
  Proof. reflexivity. Qed.

  Lemma event_set_get_seqnum (s: event_set Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    event_set_same_orig_comparable s
    → events_ext_time s
    → dep_closed s
    → event_set_orig_deps_seq s
    → event_set_seqnum_non_O s
    → get_seqnum fev =
        S (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s))).
  Proof.
    intros fev Hsame_orig Hext_t Hdc ??.
    rewrite/get_seqnum fresh_event_orig/fev/fresh_event.
    destruct (set_choose_or_empty (hproj orig s)) as [Hnon_empty | Hempty].
    - destruct (event_set_maximum_exists s orig) as (m & Hm);
      [ destruct Hnon_empty as [x [Hx_orig Hx_in]%elem_of_filter]; by exists x
        | assumption | assumption | ].
      rewrite Hm/=filter_union size_union;
        first (
          rewrite filter_singleton;
          [by rewrite size_singleton Nat.add_1_r | reflexivity]).
      apply disjoint_filter, disjoint_singleton_r.
      apply event_set_seqnum_max, le_n; try done.
      intros e He_in. by apply event_set_evid_in_time with s.
    - unfold hproj in Hempty.
      rewrite Hempty compute_maximum_empty'/= filter_union size_union.
      + rewrite filter_singleton; last reflexivity.  by rewrite size_singleton Nat.add_1_r.
      + replace (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s))
          with (∅: gset EvId);
          first by apply disjoint_empty_l.
        destruct (set_choose_or_empty (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s)))
          as [[x [Hx_orig Hx_in]%elem_of_filter]|]; last done.
        exfalso.
        assert (∃ x, x ∈ filter (λ ev : Event Op, EV_Orig ev = orig) s); last set_solver.
        destruct (get_deps_set_incl s Hdc x Hx_in) as (ev & Hev_in & Hev_eid).
        exists ev.
        apply elem_of_filter.
        by split; first rewrite -Hx_orig -Hev_eid.
  Qed.

  Lemma event_set_get_evid (s: event_set Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    event_set_same_orig_comparable s
    → events_ext_time s
    → dep_closed s
    → event_set_orig_deps_seq s
    → event_set_seqnum_non_O s
    → get_evid fev =
        (fin_to_nat orig,
        S (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s)))).
  Proof.
    intros fev Hsame_orig Hext_t Hdc ??.
    rewrite/get_evid/fev. f_equal.
    by rewrite event_set_get_seqnum.
  Qed.

  Lemma fresh_event_time_mon (s: event_set Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
      event_set_same_orig_comparable s
      → events_ext_time s
      → dep_closed s
      → event_set_orig_deps_seq s
      → event_set_seqnum_non_O s
      → event_set_seqid_val s
      → ∀ ev, ev ∈ s → ev <_t fev.
  Proof.
    intros fev Hsame_orig Hext_time Hdc ?? Hval ev Hev_in.
    rewrite/time/stlib_event_timed/fev/fresh_event/=.
    destruct (set_choose_or_empty
      (filter (λ ev0 : Event Op, EV_Orig ev0 = orig) s))
      as [(ev' & Hev'_in) | Hempty];
      last first.
    { rewrite Hempty compute_maximum_empty. split.
      - apply union_subseteq_l'.
        replace (EV_Time ev) with (get_deps_set {[ ev ]});
          first by apply get_deps_set_mon, singleton_subseteq_l.
        rewrite/get_deps_set/gset_flat_map gset_map_singleton elements_singleton.
        set_solver.
      - rewrite/ts_le.
        intros Himp.
        assert ((fin_to_nat orig, 1) ∈ EV_Time ev); first set_solver.
        destruct (Hdc ev (fin_to_nat orig, 1) Hev_in)
          as (ev' & Hev'_in & Hev'_orig); first assumption.
        assert (ev' ∈ (∅: event_set Op)); last done.
        rewrite -Hempty.
        apply elem_of_filter. split; last assumption.
        by rewrite (get_evid_valid_time ev')  Hev'_orig. }
    destruct (event_set_maximum_exists s orig) as (m & Hm).
    - exists ev'.
      by apply elem_of_filter in Hev'_in as [Horig Hs].
    - assumption.
    - assumption.
    - rewrite Hm.
      apply elem_of_subset. split.
      + intros e He_in. apply elem_of_union_l, elem_of_union_list. set_solver.
      + intros Himp.
        specialize Himp with (get_evid fev).
        assert(Hin:
          (get_evid fev)
            ∈ (get_deps_set s
               ∪
               ({[(fin_to_nat orig,
                S (size
                  (filter (λ eid : EvId, ((eid.1) = orig))
                    (get_deps_set s))))]})));
          first by apply elem_of_union_r, elem_of_singleton, event_set_get_evid.
        apply Himp in Hin. clear Himp.
        destruct (Hdc ev (get_evid fev)) as (e & He'_in & He'_eid); try done.
        rewrite/fev event_set_get_evid in He'_eid; try done.
        apply get_evid_eq in He'_eid as [Horig Himp].
        rewrite (Hval e He'_in) in Himp.
        assert (size (filter (λ v : EvId, v.1 = EV_Orig e) (EV_Time e)) < S (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s))))%nat; last lia.
        apply Nat.le_lt_trans with (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s))); last apply Nat.lt_succ_diag_r.
        rewrite Horig.
        apply subseteq_size, filter_set_mono.
        rewrite -get_deps_singleton.
        by apply get_deps_set_mon, singleton_subseteq_l.
  Qed.

  Lemma Gst_incl_orig' (g: Gst Op) (orig: fRepId) (ev: Event Op):
    Gst_Validity g → ev ∈ g.1 → ev.(EV_Orig) = fin_to_nat orig → ev ∈ g.2 !!! orig.
  Proof.
    intros Hv Hev_in Heq.
    destruct (VGst_incl_orig g Hv ev Hev_in) as (orig' & Horig' & hsfl).
    assert (orig = orig') as ->; last assumption.
    apply fin_to_nat_inj.
    by rewrite Horig'.
  Qed.

  Lemma event_set_proj_global_eq_local (g: Gst Op) (orig: fRepId):
    (∀ ev o, ev ∈ g.2 !!! o → ev ∈ g.1) → Gst_incl_orig g → hproj orig (g.2 !!! orig) = hproj orig g.1.
  Proof.
    intros Hincl Hincl'.
    apply set_eq. intros ev.
    split; intros [Hev_orig Hev_in]%elem_of_filter;
    apply elem_of_filter; (split; first assumption).
    - by apply Hincl with orig.
    - destruct (Hincl' ev Hev_in) as (i & Hi & Hi').
      assert (orig = i) as ->; last assumption.
      assert (fin_to_nat orig = fin_to_nat i);
        first by rewrite Hi -Hev_orig.
      by apply fin_to_nat_inj.
  Qed.

  Lemma event_set_get_seqnum_lt (s: event_set Op) (ev: Event Op) (orig: fRepId):
    event_set_seqid_val s →
    ev ∈ s →
    ev.(EV_Orig) = orig →
    get_seqnum ev <
             S (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s))).
  Proof.
    intros Hval Hev_in Hev_orig.
    rewrite Hval; last assumption.
    apply Nat.le_lt_trans with (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s)));
      last apply Nat.lt_succ_diag_r.
    apply subseteq_size.
    intros e [He_p He_in]%elem_of_filter.
    apply elem_of_filter. split.
    + by rewrite<- Hev_orig. 
    + apply elem_of_union_list. exists ev.(EV_Time).
      split; last assumption.
      by apply elem_of_elements, gset_map_correct1.
  Qed.

  Lemma fresh_event_not_eq_eid (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig : Event Op in
    Lst_Validity s
    → ∀ ev : Event Op, ev ∈ s → get_evid ev = get_evid fev → False.
  Proof.
    intros fev Hv ev Hev_in Heq_eid.
    apply get_evid_eq in Heq_eid as [Heq_orig Heq_seqnum]. simpl in *.
    assert (get_seqnum ev < get_seqnum fev).
    { rewrite event_set_get_seqnum;
        try by destruct Hv.
      apply event_set_get_seqnum_lt;
        try by destruct Hv. }
    lia.
  Qed.

  Lemma fresh_event_not_eq_eid_global (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig : Event Op in
    Gst_Validity g
    → ∀ ev : Event Op, ev ∈ g.1 → get_evid ev = get_evid fev → False.
  Proof.
    intros fev Hv ev Hev_in Heq_eid.
    apply get_evid_eq in Heq_eid as [Heq_orig Heq_seqnum]. simpl in *.
    assert (ev ∈ g.2 !!! orig);
      first by apply Gst_incl_orig'.
    apply (fresh_event_not_eq_eid (g.2 !!! orig) op orig (VGst_lhst_valid _ Hv orig) ev);
      first by apply Gst_incl_orig'.
    rewrite/get_evid Heq_orig fresh_event_orig. by f_equal.
  Qed.

  Lemma fresh_event_not_eq_t (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig : Event Op in
    Lst_Validity s
    → ∀ ev : Event Op, ev ∈ s → ev =_t fev → False.
  Proof.
    intros fev Hv ev Hev_in Heq_t.
    rewrite/fev/fresh_event/time/stlib_event_timed/= in Heq_t.
    destruct (set_choose_or_empty (hproj orig s))
      as [[x [Hx_orig Hx_in]%elem_of_filter] | Hneq].
    + destruct (event_set_maximum_exists s orig) as [m Hm];
      [ by exists x
      | by destruct Hv
      | by destruct Hv | ].
      rewrite Hm in Heq_t.
      clear Hm m x Hx_in Hx_orig.
      destruct (VLst_dep_closed _ Hv ev
        (fin_to_nat orig,
          S (size (filter (λ eid: EvId, eid.1 = orig) (get_deps_set s))))
        Hev_in) as (y & Hy_in & [Hy_orig Hy_sid]%get_evid_eq);
        first by (rewrite Heq_t; apply elem_of_union_r, elem_of_singleton).
      rewrite (VLst_seqid_val _ Hv) in Hy_sid; last assumption.
      assert (size (filter (λ v : EvId, v.1 = EV_Orig y) (EV_Time y)) < 
        S
         (size
            (filter (λ eid : EvId, eid.1 = orig)
               (get_deps_set s)))); last lia.
      apply Nat.le_lt_trans with (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s))); last apply Nat.lt_succ_diag_r.
      rewrite Hy_orig.
      apply subseteq_size, filter_set_mono.
      rewrite -get_deps_singleton.
      by apply get_deps_set_mon, singleton_subseteq_l.
    + unfold hproj in Hneq. rewrite Hneq compute_maximum_empty in Heq_t.
      destruct (VLst_dep_closed _
        Hv
        ev (fin_to_nat orig, 1)%nat Hev_in) as (ev' & Hev'_in & Hev'_eid);
        first set_solver.
      assert (ev' ∈ hproj orig s) as Himp.
      { apply elem_of_filter. split; last done.
          by apply get_evid_eq in Hev'_eid as []. }
      set_solver.
  Qed.

  Lemma fresh_event_not_eq_t_global (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig : Event Op in
    Gst_Validity g
    → ∀ ev : Event Op, ev ∈ g.1 → ev =_t fev → False.
  Proof.
    intros fev Hv ev Hev_in Heq_t.
    rewrite/fev/fresh_event/time/stlib_event_timed/= in Heq_t.
    destruct (set_choose_or_empty (hproj orig (g.2 !!! orig)))
      as [[x [Hx_orig Hx_in]%elem_of_filter] | Hneq].
    + destruct (event_set_maximum_exists (g.2 !!! orig) orig) as [m Hm];
      [ by exists x
      | by destruct (VGst_lhst_valid _ Hv orig)
      | by destruct (VGst_lhst_valid _ Hv orig) | ].
      rewrite Hm in Heq_t.
      clear Hm m x Hx_in Hx_orig.
      destruct (VLst_dep_closed _ (VGst_hst_valid _ Hv) ev
        (fin_to_nat orig,
          S (size (filter (λ eid: EvId, eid.1 = orig) (get_deps_set (g.2 !!! orig)))))
        Hev_in) as (y & Hy_in & [Hy_orig Hy_sid]%get_evid_eq);
        first by (rewrite Heq_t; apply elem_of_union_r, elem_of_singleton).
      rewrite (VLst_seqid_val _ (VGst_lhst_valid _ Hv orig)) in Hy_sid;
        last by apply Gst_incl_orig'.
      assert (size (filter (λ v : EvId, v.1 = EV_Orig y) (EV_Time y)) < 
        S
         (size
            (filter (λ eid : EvId, eid.1 = orig)
               (get_deps_set (g.2 !!! orig))))); last lia.
      apply Nat.le_lt_trans with (size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set (g.2 !!! orig)))); last apply Nat.lt_succ_diag_r.
      rewrite Hy_orig.
      apply subseteq_size, filter_set_mono.
      rewrite -get_deps_singleton.
      by apply get_deps_set_mon, singleton_subseteq_l, Gst_incl_orig'.
    + unfold hproj in Hneq. rewrite Hneq compute_maximum_empty in Heq_t.
      destruct (VLst_dep_closed _
        (VGst_hst_valid _ Hv)
        ev (fin_to_nat orig, 1)%nat Hev_in) as (ev' & Hev'_in & Hev'_eid);
        first set_solver.
      assert (ev' ∈ hproj orig (g.2 !!! orig)) as Himp.
      { apply elem_of_filter. split;
          last (apply Gst_incl_orig'; try done);
          by apply get_evid_eq in Hev'_eid as []. }
      set_solver.
  Qed.


  Lemma get_deps_set_proj (g: Gst Op) (orig: fRepId):
    Gst_Validity g
    → filter (λ ev : Event Op, EV_Orig ev = orig) (g.2 !!! orig) = ∅
    → filter (λ eid : EvId, eid.1 = orig) (get_deps_set (g.2 !!! orig)) = ∅.
  Proof.
    intros Hv Hempty. apply set_eq. intros x. split; last by intros?.
    intros [Horig Hin]%elem_of_filter.
    exfalso.
    apply get_deps_set_incl in Hin as (ev & Hev_orig & Hev_eid); last by destruct (VGst_lhst_valid _ Hv orig).
    destruct (filter_empty_not_elem_of_L _ _ ev Hempty); last assumption.
    destruct x. apply get_evid_eq in Hev_eid as [Horig' _].
    by rewrite Horig'.
  Qed.

  Lemma fresh_event_seqnum_non_O (s: Lst Op) (op: Op) (orig: fRepId):
    Lst_Validity s → 0 < get_seqnum (fresh_event s op orig).
  Proof.
    intros Hv.
    rewrite event_set_get_seqnum;
      try by destruct Hv.
    lia.
  Qed.

  Lemma fresh_event_proj_foreign
    (s: Lst Op) (op: Op) (i orig: RepId):
    orig ≠ i →
    (hproj i (s ∪ {[fresh_event s op orig]}) = hproj i s).
  Proof.
    intros Hneq.
    apply set_eq. intros x. split.
    - intros
        [Hx_orig [Hx_in | ->%elem_of_singleton]%elem_of_union]%elem_of_filter;
      [by apply elem_of_filter | ].
      by rewrite fresh_event_orig in Hx_orig.
    - intros [??]%elem_of_filter. apply elem_of_filter. split; first assumption.
      by apply elem_of_union_l.
  Qed.

  Lemma fresh_event_is_fresh (s: Lst Op) (f: fRepId) (op: Op):
    let fev := fresh_event s op f in
    Lst_Validity s →
      fev ∉ s.
  Proof.
    intros fev Hv Hin.
    by destruct (fresh_event_not_eq_t s op f Hv fev Hin).
  Qed.

  Lemma fresh_event_is_fresh_global (g: Gst Op) (f: fRepId) (op: Op):
    let fev := fresh_event (g.2 !!! f) op f in
    Gst_Validity g →
      fev ∉ g.1.
  Proof.
    intros fev Hv Hin.
    destruct (VGst_incl_orig _ Hv fev Hin) as (i & Heq & Hin').
    assert (i = f) as ->. { apply fin_to_nat_inj. by rewrite Heq. }
    by destruct (fresh_event_not_eq_t (g.2 !!! f) op f (VGst_lhst_valid _ Hv f) fev Hin').
  Qed.

  Lemma event_set_global_proj
    (g: Gst Op) (orig: fRepId):
    Gst_Validity g →
    hproj orig g.1 = hproj orig (g.2 !!! orig).
  Proof.
    intros Hv.
    apply set_eq. intros x.
    split;
      (intros [Hx_orig Hx_in]%elem_of_filter;
      apply elem_of_filter ;
      split; first assumption).
    - destruct (VGst_incl_orig _ Hv x Hx_in) as (i & Hi_eq & Hx_in').
      assert (i = orig) as ->; last assumption.
      apply fin_to_nat_inj. by rewrite Hi_eq.
    - apply VGst_incl_local; first assumption.
      by exists orig.
  Qed.

  Lemma evidin (e e': Event Op):
    e <_t e' → get_evid e ∈ EV_Time e → get_evid e ∈ EV_Time e'.
  Proof.
    unfold TM_lt, timestamp_time, ts_lt, ts_le, time, stlib_event_timed.
    intros [A _] B.
    apply A, B.
  Qed.


  Definition local_events (i: RepId) (s: event_set Op) : Prop :=
    ∀ e, e ∈ s → e.(EV_Orig) = i.
  Definition foreign_events (i: RepId) (s: event_set Op) : Prop :=
    ∀ e, e ∈ s → e.(EV_Orig) ≠ i.
End Preambule.

Section Useful.
  Context `{CRDT_Op: Type, !EqDecision CRDT_Op, !Countable CRDT_Op,
            !CRDT_Params}.

  Lemma foreign_local_filtered_inclusion
    (st_h__local h__foreign st'_h__local st'_h__sub: event_set CRDT_Op)
    (g: Lst CRDT_Op) :
    st'_h__local ∪ st'_h__sub ⊆_cc g →
    st_h__local ∪ h__foreign ⊆_cc g →
    Lst_Validity g →
    Lst_Validity (st_h__local ∪ h__foreign) →
    Lst_Validity (st'_h__local ∪ st'_h__sub) →
    ∀ (i : nat),
    filter
      (λ ev : Event CRDT_Op, EV_Orig ev = i)
      (st_h__local ∪ h__foreign ∪ (st'_h__local ∪ st'_h__sub))
      =
      filter
        (λ ev : Event CRDT_Op, EV_Orig ev = i)
        (st_h__local ∪ h__foreign)
  ∨ filter
    (λ ev : Event CRDT_Op, EV_Orig ev = i)
    (st_h__local ∪ h__foreign ∪ (st'_h__local ∪ st'_h__sub))
    =
    filter
      (λ ev : Event CRDT_Op, EV_Orig ev = i)
      (st'_h__local ∪ st'_h__sub).
  Proof.
    intros [Hs2 Hdc2] [Hs1 Hdc1] Hval Hv Hst'_validity i.
    pose proof (VLst_ext_time _ Hval) as Hext_t.
    pose proof (VLst_same_orig_comp _ Hval) as Hsoc.
    set s1 := st_h__local ∪ h__foreign.
    set s2 := st'_h__local ∪ st'_h__sub.
    set fs1 := filter (λ ev, ev.(EV_Orig) = i) s1.
    set fs2 := filter (λ ev, ev.(EV_Orig) = i) s2.
    destruct (decide (fs1 = ∅)) as [Heq1 | Hneq1];
    destruct (decide (fs2 = ∅)) as [Heq2 | Hneq2].
    - left.
      apply set_eq. intros x. split;
      intros [Hx_p [Hx_in|Hx_in]%elem_of_union]%elem_of_filter;
          exfalso; set_solver.
    - right.
      apply set_eq. intros x. split;
      intros [Hx_p [Hx_in|Hx_in]%elem_of_union]%elem_of_filter;
          try (exfalso; set_solver).
      + apply elem_of_filter. split; assumption.
      + apply elem_of_filter. split; first assumption.
        by apply elem_of_union_r, elem_of_union_l.
      + apply elem_of_filter. split; first assumption.
        by apply elem_of_union_r, elem_of_union_r.
    - left.
      apply set_eq. intros x. split;
      intros [Hx_p [Hx_in|Hx_in]%elem_of_union]%elem_of_filter;
          try (exfalso; set_solver).
      + apply elem_of_filter. split; assumption.
      + apply elem_of_filter. split; first assumption.
        by apply elem_of_union_l, elem_of_union_l.
      + apply elem_of_filter. split; first assumption.
        by apply elem_of_union_l, elem_of_union_r.
    - epose proof (iffLR (compute_maximum_non_empty fs1 _ _) Hneq1) as HH;
        destruct HH as (max1 & [Hmax1_in H1']%compute_maximum_correct); last first.
      { intros x y [Hx_p [Hx_in|Hx_in]%elem_of_union]%elem_of_filter
          [Hy_p [Hy_in|Hy_in]%elem_of_union]%elem_of_filter Heq.
        all: apply (VLst_ext_time _ Hv x y).
        all: try (apply elem_of_union_l; assumption).
        all: try (apply elem_of_union_r; assumption).
        all: assumption. }
      Unshelve.
      2: {  intros x y [Hx_p Hx_in%Hs1]%elem_of_filter [Hy_p Hy_in%Hs1]%elem_of_filter.
            apply Hsoc; [assumption | assumption |].
            by rewrite Hx_p Hy_p. }
      2: {  intros x y [Hx_p Hx_in%Hs1]%elem_of_filter [Hy_p Hy_in%Hs1]%elem_of_filter.
            apply Hext_t; assumption. }
      epose proof (iffLR (compute_maximum_non_empty fs2 _ _) Hneq2) as HH;
        destruct HH as (max2 & [Hmax2_in H2']%compute_maximum_correct); last first.
      { intros x y [Hx_p [Hx_in|Hx_in]%elem_of_union]%elem_of_filter
          [Hy_p [Hy_in|Hy_in]%elem_of_union]%elem_of_filter Heq.
        all: apply (VLst_ext_time _ Hst'_validity x y).
        all: try (apply elem_of_union_l; assumption).
        all: try (apply elem_of_union_r; assumption).
        all: assumption. }
      Unshelve.
      2,3: intros x y [Hx_p Hx_in%Hs2]%elem_of_filter [Hy_p Hy_in%Hs2]%elem_of_filter.
      2: apply Hsoc; [assumption | assumption |]; by rewrite Hx_p Hy_p.
      2: apply Hext_t; assumption.

      assert(max1 <_t max2 ∨ max1 =_t max2 ∨ max2 <_t max1) as [|[|]].
      + apply elem_of_filter in Hmax1_in as [Hmax1_i Hmax1_in].
        apply elem_of_filter in Hmax2_in as [Hmax2_i Hmax2_in].
        by epose proof (Hsoc max1 max2 _ _ _).
        Unshelve.
        by apply Hs1. by apply Hs2. by rewrite Hmax1_i Hmax2_i.
      + right.
        apply set_eq. intros x; split.
        * intros [Hx_p [Hx_in|Hx_in]%elem_of_union]%elem_of_filter;
            last set_solver.
          assert(Hmax2_in': max2 ∈ g).
          { apply Hs2.
            by apply elem_of_filter in Hmax2_in as [_ Hmax2_in]. }
          apply elem_of_filter. split; first assumption.
          apply (Hdc2 x max2 (Hs1 _ Hx_in) Hmax2_in'); last set_solver.
          simpl. simpl in H0.
          apply strict_include.
          by epose (ts_le_lt_trans (time x) (time max1) (time max2) _ H0).
          Unshelve.
          destruct (decide (max1 = x)) as [ -> | ]; first done.
          apply strict_include.
          by apply H1'; first set_solver.
        * intros [Hx_p Hx_in]%elem_of_filter.
          by apply elem_of_filter; split; [ | apply elem_of_union_r ].
      + right.
        apply set_eq. intros x; split.
        * intros [Hx_p [Hx_in|Hx_in]%elem_of_union]%elem_of_filter;
            last set_solver.
          apply elem_of_filter. split; first assumption.
          assert(Hmax2_in': max2 ∈ g).
          { apply Hs2.
            by apply elem_of_filter in Hmax2_in as [_ Hmax2_in]. }
          apply (Hdc2 x max2 (Hs1 _ Hx_in) Hmax2_in'); last set_solver.
          epose proof (Hext_t max1 max2 _ _ H0) as ->.
          destruct(decide (x = max2)) as [ -> | ]; first done.
          apply strict_include.
          apply H1'. set_solver.
          assumption.
          Unshelve.
          apply Hs1. by apply elem_of_filter in Hmax1_in as [_?].
          assumption.
        * intros [Hx_p Hx_in]%elem_of_filter.
          by apply elem_of_filter; split; [ | apply elem_of_union_r ].
      + left.
        apply set_eq. intros x; split.
        * intros [Hx_p [Hx_in|Hx_in]%elem_of_union]%elem_of_filter;
            first set_solver.
          assert(Hmax1_in': max1 ∈ g).
          { apply Hs1.
            by apply elem_of_filter in Hmax1_in as [_ Hmax1_in]. }
          apply elem_of_filter. split; first assumption.
          apply (Hdc1 x max1 (Hs2 _ Hx_in) Hmax1_in'); last set_solver.
          simpl. simpl in H0.
          apply strict_include.
          destruct(decide(x = max2)) as [ -> | ] ; first done.
          by epose (ts_lt_le_trans (time x) (time max2) (time max1) _ _).
          Unshelve.
          apply H2'. set_solver.
          assumption.
          by apply strict_include.
        * intros [Hx_p Hx_in]%elem_of_filter.
          by apply elem_of_filter; split; [ | apply elem_of_union_l ].
  Qed.


End Useful.

