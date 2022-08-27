From aneris.aneris_lang Require Import lang.
From stdpp Require Import gmap.
From aneris.prelude Require Import gset_map.
From aneris.examples.crdt Require Import crdt_spec.
From aneris.examples.crdt.statelib.time Require Import evtime maximality.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.STS Require Import lst gst utils.


Section Gst_mutator_local_valid.
  Context `{!CRDT_Params,
            Op: Type, !EqDecision Op, !Countable Op}.

  Lemma mutator_incl_local
    (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    Gst_incl_local (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).
  Proof.
    (** Use the definitin of a fresh event + it is added to the correspondin
     *  local state *)
    intros fev Hv ev.
    split.
    - simpl. intros [Hev_in | ->%elem_of_singleton]%elem_of_union.
      + destruct (iffLR (VGst_incl_local g Hv ev) Hev_in) as (i & Hi).
        exists i.
        destruct (decide (orig = i)) as [ -> | ].
        * rewrite vlookup_insert.
          by apply elem_of_union_l.
        * by rewrite vlookup_insert_ne; last assumption.
      + exists orig.
        rewrite vlookup_insert.
        by apply elem_of_union_r, elem_of_singleton.
    - intros (i & Hi).
      destruct (decide (orig = i)) as [-> | ?].
      + rewrite vlookup_insert in Hi. simpl.
        apply (elem_of_subseteq (g.2 !!! i ∪ {[fev]}) (g.1 ∪ {[fev]}));
          last assumption.
        intros x [Hx_in | -> %elem_of_singleton]%elem_of_union.
        * apply elem_of_union_l, (VGst_incl_local g Hv). by exists i.
        * by apply elem_of_union_r, elem_of_singleton.
      + simpl in *. rewrite vlookup_insert_ne in Hi; last assumption.
        apply elem_of_union_l, (VGst_incl_local g Hv ev).
        by exists i.
  Qed.

  Lemma mutator_incl_orig
    (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    Gst_incl_orig (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).
  Proof.
    (** Use the definitin of a fresh event + it is added to the correspondin
     *  local state *)
    intros fev Hv ev. simpl.
    intros [Hev_in | ->%elem_of_singleton]%elem_of_union.
    - destruct (VGst_incl_orig g Hv ev Hev_in) as (i & ? & Hi).
      exists i. split; first assumption.
      by destruct ( decide (orig = i)) as [-> |?];
        [rewrite vlookup_insert; apply elem_of_union_l
        | rewrite vlookup_insert_ne; last assumption].
    - exists orig. split; first apply (fresh_event_orig (g.2 !!! orig) op).
      rewrite vlookup_insert.
      by apply elem_of_union_r, elem_of_singleton.
  Qed.

  Lemma mutator_local_evid_mon_preservation (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s →
      event_set_evid_mon
        (s ∪ {[fev]}).
  Proof.
    (** Directly follows from the definitin of a fresh event *)
    intros fev Hv ev ev'. simpl.
    intros
      [Hev_in | Heq%elem_of_singleton]%elem_of_union
      [Hev'_in | Heq'%elem_of_singleton]%elem_of_union
      Heq_orig
      [Hle Hnle];
      [by apply (VLst_evid_mon _ Hv) | | | ].
    - split; first assumption.
      apply subseteq_size.
      intros eid [Heid Heid_in]%elem_of_filter.
      rewrite -Heq_orig elem_of_filter. split; first assumption.
      by apply elem_of_subseteq with ev.(EV_Time).
    - exfalso.
      apply Hnle, strict_include.
      rewrite Heq/fev.
      apply (fresh_event_time_mon s op orig);
        try by destruct Hv.
    - destruct Hnle. by rewrite Heq Heq'.
  Qed.

  Lemma mutator_evid_mon_preservation (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
      event_set_evid_mon
        (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    (** Directly follows from the definitin of a fresh event *)
    intros fev Hv ev ev'. simpl.
    intros
      [Hev_in | Heq%elem_of_singleton]%elem_of_union
      [Hev'_in | Heq'%elem_of_singleton]%elem_of_union
      Heq_orig
      [Hle Hnle];
      [by apply (VLst_evid_mon g.1 (VGst_hst_valid g Hv)) | | | ].
    - split; first assumption.
      apply subseteq_size.
      intros eid [Heid Heid_in]%elem_of_filter.
      rewrite -Heq_orig elem_of_filter. split; first assumption.
      by apply elem_of_subseteq with ev.(EV_Time).
    - exfalso.
      apply Hnle, strict_include.
      rewrite Heq/fev.
      apply (fresh_event_time_mon (g.2 !!! orig) op orig);
        try by destruct (VGst_lhst_valid _ Hv orig).
      apply (Gst_incl_orig' _ orig ev'); [exact Hv |exact Hev'_in |].
      by rewrite -Heq_orig Heq fresh_event_orig.
    - destruct Hnle. by rewrite Heq Heq'.
  Qed.

  Lemma mutator_ext_time_preservation (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    events_ext_time (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    (** Directly follows from the freshness of a fresh event *)
    intros fev Hv ev ev'. simpl.
    intros [Hev_in | ->%elem_of_singleton]%elem_of_union
      [Hev'_in | ->%elem_of_singleton]%elem_of_union Heq_t;
    [ by apply (VLst_ext_time g.1 (VGst_hst_valid g Hv)) | | | reflexivity];
    exfalso.
    - by apply (fresh_event_not_eq_t_global g op orig Hv ev).
    - by apply (fresh_event_not_eq_t_global g op orig Hv ev').
  Qed.

  Lemma empty_proj_is_empty (s: event_set Op) (orig: fRepId):
    Lst_Validity s →
    filter (λ ev : Event Op, ev.(EV_Orig) = orig) s = ∅ →
      size (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s)) = O.
  Proof.
    intros Hv Hempty.
    assert (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s) = ∅) as ->;
      last by rewrite size_empty.
    apply set_eq. intros x.
    split; last by intros?.
    intros [Hx_orig (ev & Hev_orig & Hev_x)%get_deps_set_incl]%elem_of_filter;
      last by apply (VLst_dep_closed _ Hv).
    assert (∃ m, compute_maximum
      (filter (λ ev : Event Op, EV_Orig ev = orig) s) = Some m) as (m & H').
    { apply event_set_maximum_exists.
      - exists ev. split; first assumption.
        rewrite /get_evid in Hev_x.
        by rewrite<- Hev_x in Hx_orig.
      - by apply (VLst_same_orig_comp _ Hv).
      - by apply (VLst_ext_time _ Hv). }
    by rewrite Hempty in H'.
  Qed.

  Lemma mutator_ext_evid_preservation (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    events_ext_evid (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    (** Directly follows from the freshness of a fresh event *)
    intros fev Hv ev ev'. simpl.
    intros
      [Hev_in | ->%elem_of_singleton]%elem_of_union
      [Hev'_in | ->%elem_of_singleton]%elem_of_union Heq_orig;
      [ by apply (VLst_ext_eqid g.1 (VGst_hst_valid g Hv)) | | | reflexivity ];
    exfalso.
    - by apply (fresh_event_not_eq_eid_global g op orig Hv ev).
    - by apply (fresh_event_not_eq_eid_global g op orig Hv ev').
   Qed.

  Lemma fresh_event_elem_of_time
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    ∀ eid: EvId, eid ∈ fev.(EV_Time) →
    Lst_Validity s → eid ∈ get_deps_set s ∨ eid = get_evid fev.
  Proof.
    (** Directly follows from the definition of a fresh event *)
    intros fev eid Heid_in Hv.
    rewrite /fev/fresh_event/= in Heid_in.
    destruct (set_choose_or_empty
      (filter (λ ev : Event Op, EV_Orig ev = orig) s))
      as [[e [He_orig He_in]%elem_of_filter] | Hempty].
    - destruct (event_set_maximum_exists s orig) as [m Hm].
      + exists e. by split.
      + by destruct Hv.
      + by destruct Hv.
      + rewrite Hm in Heid_in.
        apply elem_of_union in Heid_in as [Heid_in | ->%elem_of_singleton].
        * by left.
        * right.
          rewrite event_set_get_evid; by destruct Hv.
    - rewrite Hempty compute_maximum_empty' in Heid_in.
      apply elem_of_union in Heid_in as [Heid_in | ->%elem_of_singleton].
      * by left.
      * right.
        rewrite event_set_get_evid; try by destruct Hv. f_equal.
        by rewrite empty_proj_is_empty.
  Qed.

  Lemma mutator_local_dep_closed_preservation
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s → dep_closed (s ∪ {[fev]}).
  Proof.
    intros fev Hv ev eid [Hev_in | ->%elem_of_singleton]%elem_of_union Heid_in;
      last destruct
        (fresh_event_elem_of_time s op orig eid) as [Heid_in'|Heid_in'].
    - destruct (VLst_dep_closed _ Hv ev eid Hev_in Heid_in) as (e & He & Heid).
      exists e. by split; first apply elem_of_union_l.
    - assumption.
    - assumption.
    - destruct (get_deps_set_incl s (VLst_dep_closed _ Hv) eid Heid_in')
        as (x & Hx & Hx').
      exists x.
      by split; first apply elem_of_union_l.
    - exists fev.
      by split; first apply elem_of_union_r, elem_of_singleton.
  Qed.

  Lemma mutator_local_orig_lt_len_preservation
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s → event_set_orig_lt_len (s ∪ {[fev]}).
  Proof.
    intros fev Hv ev [Hev_in | ->%elem_of_singleton]%elem_of_union;
      first by apply (VLst_orig _ Hv).
    assert (EV_Orig fev < length CRDT_Addresses)%nat; last lia.
    apply fin_to_nat_lt.
  Qed.

  Lemma mutator_local_ext_evid
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s → events_ext_evid (s ∪ {[fev]}).
  Proof.
    intros fev Hv ev ev'. simpl.
    intros
      [Hev_in | ->%elem_of_singleton]%elem_of_union
      [Hev'_in | ->%elem_of_singleton]%elem_of_union Heq_orig;
      [ by apply (VLst_ext_eqid _ Hv) | | | reflexivity ];
    exfalso;
    [ by apply (fresh_event_not_eq_eid s op orig Hv ev)
    | apply (fresh_event_not_eq_eid s op orig Hv ev') ]; try done.
    all: by apply VGst_incl_local; last by exists orig.
  Qed.

  Lemma mutator_local_ext_time
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s → events_ext_time (s ∪ {[fev]}).
  Proof.
     intros fev Hv ev ev'. simpl.
      intros [Hev_in | ->%elem_of_singleton]%elem_of_union
        [Hev'_in | ->%elem_of_singleton]%elem_of_union Heq_t;
      [ by apply (VLst_ext_time _ Hv) | | | reflexivity];
      exfalso;
      [ by apply (fresh_event_not_eq_t s op orig Hv ev)
      | by apply (fresh_event_not_eq_t s op orig Hv ev') ].
  Qed.

  Lemma mutator_local_seqnum_val_preservation
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s → event_set_seqid_val (s ∪ {[fev]}).
  Proof.
    intros fev Hv ev [Hev_in | ->%elem_of_singleton]%elem_of_union;
      first by apply (VLst_seqid_val _ Hv).
    rewrite event_set_get_seqnum; try by destruct Hv.
    rewrite/fev/fresh_event/=.
    destruct (set_choose_or_empty
      (filter (λ ev, EV_Orig ev = orig) s))
      as [[e [He_orig He_in]%elem_of_filter] | Hempty].
    - destruct (event_set_maximum_exists s orig) as [m Hm].
      + exists e. by split.
      + by destruct Hv.
      + by destruct Hv.
      + rewrite Hm filter_union filter_singleton; last reflexivity.
        rewrite size_union; first by rewrite size_singleton Nat.add_1_r.
        apply disjoint_singleton_r.
        intros [Horig (ev & Hev_in & Hev_eid)%get_deps_set_incl]%elem_of_filter;
          last by destruct Hv.
        apply (fresh_event_not_eq_eid s op orig Hv ev Hev_in).
        rewrite /get_evid fresh_event_orig event_set_get_seqnum;
          by destruct Hv.
    - rewrite Hempty compute_maximum_empty'.
      rewrite filter_union filter_singleton; last reflexivity.
      rewrite size_union; first by rewrite size_singleton Nat.add_1_r.
      simpl.
      rewrite disjoint_singleton_r.
      intros [Horig (e & He_in & He_eid)%get_deps_set_incl]%elem_of_filter;
        last by destruct Hv.
      apply (filter_empty_not_elem_of_L _ s e Hempty); last assumption.
      by apply get_evid_eq in He_eid as [??].
  Qed.

  Lemma mutator_local_same_orig_comparable_preservation
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s →
    event_set_same_orig_comparable (s ∪ {[fev]}).
  Proof.
    intros fev Hv ev ev'. simpl.
    intros
      [Hev_in | ->%elem_of_singleton]%elem_of_union
      [Hev'_in | ->%elem_of_singleton]%elem_of_union Heq_orig.
    + by apply (VLst_same_orig_comp _ Hv).
    + left.
      apply fresh_event_time_mon; try by destruct Hv.
    + do 2 right.
      apply fresh_event_time_mon; try by destruct Hv.
    + by right; left.
  Qed.

  Lemma mutator_same_orig_comp_preservation (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    event_set_same_orig_comparable
      (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    intros fev Hv ev ev'. simpl.
      intros
        [Hev_in | ->%elem_of_singleton]%elem_of_union
        [Hev'_in | ->%elem_of_singleton]%elem_of_union Heq_orig.
      + by apply (VLst_same_orig_comp g.1 (VGst_hst_valid g Hv)).
      + left.
        apply fresh_event_time_mon; try by destruct (VGst_lhst_valid _ Hv orig).
        by apply (Gst_incl_orig' _ orig ev).
      + do 2 right.
        apply fresh_event_time_mon; try by destruct (VGst_lhst_valid _ Hv orig).
        by apply (Gst_incl_orig' _ orig ev').
      + by right; left.
  Qed.

  Lemma mutator_local_orig_max_len_preservation
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s →
    event_set_orig_max_len (s ∪ {[fev]}).
  Proof.
    intros fev Hv i Hlt.
    destruct (decide (i = orig)) as [-> | Hneq]; first last.
    (** TODO: simplify the proof of the first (well last) case. *)
    { simpl.
      rewrite fresh_event_proj_foreign; last done.
      destruct (decide (events.hproj i s = ∅)) as [? | Hnempty]; first by left.
      right.
      destruct (event_set_maximum_exists s i)
        as [m [[Hm_orig Hm_in]%elem_of_filter Hm_max]%compute_maximum_correct].
      + destruct (set_choose_L _ Hnempty) as (e & [??]%elem_of_filter).
        by exists e.
      + by apply (VLst_same_orig_comp _ Hv).
      + by apply (VLst_ext_time _ Hv).
      + exists m.
        split; first by apply elem_of_union_l.
        apply compute_maximum_correct.
        * intros x y [_ Hx_in]%elem_of_filter[_ Hy_in]%elem_of_filter.
          by apply (VLst_ext_time _ Hv x y).
        * split; first (apply elem_of_filter; split);
            [ assumption | assumption | ].
          intros ev [Hev_orig Hev_in]%elem_of_filter Hneq'.
          apply Hm_max; [by apply elem_of_filter | assumption].
      + intros x y [_ Hx_in]%elem_of_filter[_ Hy_in]%elem_of_filter.
        by apply (VLst_ext_time _ Hv x y). }
    right.
    destruct (event_set_maximum_exists (s ∪ {[ fev ]}) orig) as (m & Hm);
      last first.
    { exists m. simpl. split.
      - apply compute_maximum_correct in Hm
        as [[_ [Hin | Hin]%elem_of_union]%elem_of_filter _];
        [by apply elem_of_union_l |  by apply elem_of_union_r | ].
        intros x y
          [Hx_orig Hx_in]%elem_of_filter
          [Hy_orig Hy_in]%elem_of_filter.
        assert (s ⊆ s); first set_solver.
        assert (x ∈ (s ∪ {[ fev ]})).
        { apply elem_of_union in Hx_in as [Hx_in | ->%elem_of_singleton];
            last by apply elem_of_union_r, elem_of_singleton.
          by apply elem_of_union_l, (elem_of_subseteq s). }
        assert (y ∈ (s ∪ {[ fev ]})).
        { apply elem_of_union in Hy_in as [Hy_in | ->%elem_of_singleton];
            last by apply elem_of_union_r, elem_of_singleton.
          by apply elem_of_union_l, (elem_of_subseteq s). }
        apply (mutator_local_ext_time s op orig Hv x y); done.
      - rewrite -Hm.
        f_equal. }
      + pose proof (mutator_local_ext_time s op orig Hv) as p. simpl in *.
        intros e e' He_in He'_in.
        apply p;
        [ apply elem_of_union in He_in as [He_in | ->%elem_of_singleton]
        | apply elem_of_union in He'_in as [He'_in | ->%elem_of_singleton]].
        2, 4: by apply elem_of_union_r, elem_of_singleton.
        all: set_solver.
      + pose proof
          (mutator_local_same_orig_comparable_preservation s op orig Hv) as p.
        simpl in *.
        intros e e' He_in He'_in.
        apply p;
        [ apply elem_of_union in He_in as [He_in | ->%elem_of_singleton]
        | apply elem_of_union in He'_in as [He'_in | ->%elem_of_singleton]].
        2, 4: by apply elem_of_union_r, elem_of_singleton.
        all: set_solver.
      + exists fev.
        by split; first apply elem_of_union_r, elem_of_singleton, eq_refl.
  Qed.

  Lemma mutator_orig_max_len_preservation (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    event_set_orig_max_len
      (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    intros fev Hv i Hlt.
    destruct (decide (i = orig)) as [-> | Hneq]; first last.
    (** TODO: simplify the proof of the first (well last) case. *)
    { simpl.
      assert (events.hproj i (g.1 ∪ {[fev]}) = events.hproj i g.1) as ->.
      { apply set_eq. intros x. split.
        - intros
            [Hx_orig [Hx_in | ->%elem_of_singleton]%elem_of_union]%elem_of_filter;
            [by apply elem_of_filter | done].
        - intros [??]%elem_of_filter. apply elem_of_filter.
          split; [ assumption | by apply elem_of_union_l ]. }
      destruct (decide (events.hproj i g.1 = ∅)) as [? | Hnempty].
      - by left.
      - right.
        destruct (event_set_maximum_exists g.1 i)
          as [m [[Hm_orig Hm_in]%elem_of_filter Hm_max]%compute_maximum_correct].
        + destruct (set_choose_L _ Hnempty) as (e & [??]%elem_of_filter).
          by exists e.
        + by apply (VLst_same_orig_comp _ (VGst_hst_valid _ Hv)).
        + by apply (VLst_ext_time _ (VGst_hst_valid _ Hv)).
        + exists m.
          split; first by apply elem_of_union_l.
          apply compute_maximum_correct.
          * intros x y [_ Hx_in]%elem_of_filter[_ Hy_in]%elem_of_filter.
            by apply (VLst_ext_time _ (VGst_hst_valid _ Hv) x y).
          * split; first (apply elem_of_filter; split);
              [ assumption | assumption | ].
            intros ev [Hev_orig Hev_in]%elem_of_filter Hneq'.
            apply Hm_max; [by apply elem_of_filter | assumption].
        + intros x y [_ Hx_in]%elem_of_filter[_ Hy_in]%elem_of_filter.
          by apply (VLst_ext_time _ (VGst_hst_valid _ Hv) x y). }
    right.
    destruct (event_set_maximum_exists (g.2 !!! orig ∪ {[ fev ]}) orig)
      as (m & Hm); last first.
    { exists m. simpl. split.
      - apply compute_maximum_correct in Hm
        as [[_ [Hin | Hin]%elem_of_union]%elem_of_filter _];
        [ |  by apply elem_of_union_r | ].
        + apply elem_of_union_l.
          rewrite (VGst_ghst_lhsts_coh g Hv) elem_of_union_list.
          exists (g.2 !!! orig). split; last assumption.
          apply elem_of_vlookup.
          by exists orig.
        + intros x y
          [Hx_orig Hx_in]%elem_of_filter
          [Hy_orig Hy_in]%elem_of_filter.
          assert (g.2 !!! orig ⊆ g.1).
          { rewrite (VGst_ghst_lhsts_coh g Hv).
            apply vec_incl_in_list_union. }
          assert (x ∈ (g.1 ∪ {[ fev ]})).
          { apply elem_of_union in Hx_in as [Hx_in | ->%elem_of_singleton];
              last by apply elem_of_union_r, elem_of_singleton.
            by apply elem_of_union_l, (elem_of_subseteq (g.2 !!! orig)). }
          assert (y ∈ (g.1 ∪ {[ fev ]})).
          { apply elem_of_union in Hy_in as [Hy_in | ->%elem_of_singleton];
              last by apply elem_of_union_r, elem_of_singleton.
            by apply elem_of_union_l, (elem_of_subseteq (g.2 !!! orig)). }
          apply (mutator_ext_time_preservation g op orig Hv x y); done.
      - rewrite -Hm.
        f_equal.
        assert  (hproj orig (g.1 ∪ {[fev]}) = (hproj orig g.1) ∪ {[fev]}) as ->.
        { apply set_eq. intros x. split.
          - intros [Horig [Hin | ->%elem_of_singleton]%elem_of_union]%elem_of_filter.
            + by apply elem_of_union_l, elem_of_filter.
            + by apply elem_of_union_r, elem_of_singleton.
          - intros
              [[H_orig Hin]%elem_of_filter
              | ->%elem_of_singleton]%elem_of_union;
            apply elem_of_filter; split.
            + assumption.
            + by apply elem_of_union_l.
            + apply fresh_event_orig.
            + by apply elem_of_union_r, elem_of_singleton. }
        assert (hproj orig ((g.2 !!! orig) ∪ {[fev]})
          = (hproj orig (g.2 !!! orig)) ∪ {[fev]}) as ->.
        { apply set_eq. intros x. split.
          - intros
              [Horig [Hin | ->%elem_of_singleton]%elem_of_union]%elem_of_filter.
            + by apply elem_of_union_l, elem_of_filter.
            + by apply elem_of_union_r, elem_of_singleton.
          - intros
              [[H_orig Hin]%elem_of_filter
              | ->%elem_of_singleton]%elem_of_union;
            apply elem_of_filter; split.
            + assumption.
            + by apply elem_of_union_l.
            + apply fresh_event_orig.
            + by apply elem_of_union_r, elem_of_singleton. }
        rewrite (event_set_proj_global_eq_local g orig); first reflexivity.
        + intros ev o Hev.
          apply (VGst_incl_local _ Hv). by exists o.
        + by destruct Hv. }
      + pose proof (mutator_ext_time_preservation g op orig Hv) as p.
        simpl in *.
        intros e e' He_in He'_in.
        apply p;
        [ apply elem_of_union in He_in as [He_in | ->%elem_of_singleton]
        | apply elem_of_union in He'_in as [He'_in | ->%elem_of_singleton]].
        2, 4: by apply elem_of_union_r, elem_of_singleton.
        all: apply elem_of_union_l, (VGst_incl_local g Hv); by exists orig.
      + pose proof (mutator_same_orig_comp_preservation g op orig Hv) as p.
        simpl in *.
        intros e e' He_in He'_in.
        apply p;
        [ apply elem_of_union in He_in as [He_in | ->%elem_of_singleton]
        | apply elem_of_union in He'_in as [He'_in | ->%elem_of_singleton]].
        2, 4: by apply elem_of_union_r, elem_of_singleton.
        all: apply elem_of_union_l, (VGst_incl_local g Hv); by exists orig.
      + exists fev.
        by split; first apply elem_of_union_r, elem_of_singleton, eq_refl.
  Qed.

  Lemma mutator_dep_closed_preservation (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    dep_closed (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    - intros fev Hv ev eid. simpl.
      intros [Hev_in | ->%elem_of_singleton]%elem_of_union Heid_in.
      + destruct (VLst_dep_closed g.1 (VGst_hst_valid g Hv) ev eid)
          as (e' & He' & Heid); [assumption | assumption | ].
        exists e'. by split; [apply elem_of_union_l |].
      + rewrite /fev /fresh_event in Heid_in.
        simpl in *.
        destruct (compute_maximum
          (filter (λ ev : Event Op, EV_Orig ev = orig) (g.2 !!! orig))) eqn:E;
        apply elem_of_union in Heid_in as [Heid_in_old | ->%elem_of_singleton].
        * destruct
            (get_deps_set_incl (g.2 !!! orig)
              (VLst_dep_closed _ (VGst_lhst_valid g Hv orig) ) eid)
            as (ev & Hev_in & Hev_lkjk); first assumption.
          assert (∃ e' : Event Op, e' ∈ g.1  ∧ get_evid e' = eid)
            as (e' & He'_in & He'_eid).
          { apply get_deps_set_incl.
            - exact (VLst_dep_closed _ (VGst_hst_valid g Hv)).
            - apply (get_deps_set_mon (g.2 !!! orig) ); last assumption.
              apply elem_of_subseteq. intros ev' Hev'_in.
              apply (VGst_incl_local _ Hv ev'). by exists orig. }
          exists e'. by split; first apply elem_of_union_l.
        * exists fev.
          split; first by apply elem_of_union_r, elem_of_singleton.
          rewrite/get_evid fresh_event_orig. f_equal.
          rewrite/get_seqnum/fev/fresh_event E filter_union size_union. simpl;
            first by rewrite filter_singleton;
            first rewrite size_singleton Nat.add_1_r.
          simpl. apply disjoint_filter, disjoint_singleton_r.
          intros Himp.
          set sid : SeqNum := S (size
                (filter (λ eid : RepId * SeqNum, eid.1 = orig)
                   (get_deps_set (g.2 !!! orig)))).
          destruct (get_deps_set_incl
            (g.2 !!! orig)
            (VLst_dep_closed _ (VGst_lhst_valid _ Hv orig))
            (fin_to_nat orig, sid) Himp) as (ev & Hev_in & Hev_eid).
          assert (get_seqnum ev < sid)%nat.
          { destruct (event_set_seqnum_max (g.2 !!! orig) orig sid);
              try by destruct (VGst_lhst_valid _ Hv orig).
            apply lt_n_Sn. }
          apply get_evid_eq in Hev_eid as [_ Hsid]. lia.
        * destruct
            (get_deps_set_incl _ (VLst_dep_closed _
              (VGst_lhst_valid _ Hv orig)) eid Heid_in_old)
            as (ev & Hev_orig & Hev_sid).
          exists ev. split; last assumption.
          apply elem_of_union_l, (VGst_incl_local _ Hv).
          by exists orig.
        * exists fev. split; first by apply elem_of_union_r, elem_of_singleton.
          rewrite /fev/fresh_event/get_evid/get_seqnum E. f_equal. simpl.
          rewrite filter_union.
          replace
            (filter (λ eid : EvId, eid.1 = orig) (get_deps_set (g.2 !!! orig)))
            with (∅: gset EvId).
          --
            rewrite filter_singleton; last reflexivity.
            by rewrite union_empty_L size_singleton.
          --
            apply set_eq. intros x. split; first by intros?.
            intros [Hx_orig Hx_init]%elem_of_filter.
            exfalso.
            assert (∃ ev, ev ∈ (g.2 !!! orig) ∧ get_evid ev = x)
              as (ev & Hev_in & Hev_evid).
            { apply get_deps_set_incl; last assumption.
              exact (VLst_dep_closed _ (VGst_lhst_valid g Hv orig)). }
            assert (x ∈ EV_Time ev) as Hx_ev.
            { replace (EV_Time ev) with (get_deps ev); last reflexivity.
              rewrite -Hev_evid.
              by apply
                (VLst_evid_incl_event (g.2 !!! orig)
                  (VGst_lhst_valid g Hv orig) ev). }
            destruct (
              VLst_dep_closed (g.2 !!! orig)
                (VGst_lhst_valid g Hv orig)
                ev x
                Hev_in Hx_ev) as (e' & He'_in & He'_evid).
            destruct (event_set_maximum_exists (g.2 !!! orig) orig).
            ++
              exists e'. split; first assumption.
              by rewrite get_evid_valid_time He'_evid Hx_orig.
            ++
              apply (VLst_same_orig_comp (g.2 !!! orig)
                (VGst_lhst_valid g Hv orig)).
            ++
              apply (VLst_ext_time (g.2 !!! orig) (VGst_lhst_valid g Hv orig)).
            ++ by rewrite H0 in E.
  Qed.

  Lemma mutator_orig_lt_len_preservation
    (g: Gst Op) (op: Op) (orig: fRepId):
      let fev := fresh_event (g.2 !!! orig) op orig in
      Gst_Validity g →
      event_set_orig_lt_len
        (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
    Proof.
      intros fev Hv ev. simpl.
      intros [Hev_in | ->%elem_of_singleton]%elem_of_union.
      + by apply (VLst_orig g.1 (VGst_hst_valid g Hv)).
      + rewrite fresh_event_orig.
        assert (orig < length CRDT_Addresses)%nat; last lia.
        apply (fin_to_nat_lt orig).
    Qed.

  Lemma mutator_seqid_val_preservation
    (g: Gst Op) (op: Op) (orig: fRepId):
      let fev := fresh_event (g.2 !!! orig) op orig in
      Gst_Validity g →
      event_set_seqid_val
        (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    intros fev Hv ev. simpl.
    intros [Hev_in | Heq%elem_of_singleton]%elem_of_union.
    + by apply (VLst_seqid_val g.1 (VGst_hst_valid g Hv)).
    + reflexivity.
  Qed.

  Lemma mutator_seqnum_non_O_preservation
    (g: Gst Op) (op: Op) (orig: fRepId):
      let fev := fresh_event (g.2 !!! orig) op orig in
      Gst_Validity g →
      event_set_seqnum_non_O
        (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    intros fev Hv ev. simpl.
    intros [Hev | ->%elem_of_singleton]%elem_of_union;
      first by apply (VLst_seqnum_non_O _ (VGst_hst_valid _ Hv)).
    apply fresh_event_seqnum_non_O, (VGst_lhst_valid _ Hv orig).
  Qed.

  Lemma mutator_local_seqnum_non_O_preservation
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s →
    event_set_seqnum_non_O (s ∪ {[fev]}).
  Proof.
    intros fev Hv ev [Hev_in | ->%elem_of_singleton]%elem_of_union;
      first by apply (VLst_seqnum_non_O _ Hv).
    by apply fresh_event_seqnum_non_O.
  Qed.

  Lemma mutator_local_evid_incl_event
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s →
    event_set_evid_incl_event (s ∪ {[fev]}).
  Proof.
    intros fev Hv ev. simpl.
    intros [Hev_in | ->%elem_of_singleton]%elem_of_union;
      first by apply (VLst_evid_incl_event _ Hv).
    rewrite event_set_get_evid; try by destruct Hv.
    rewrite /fev/fresh_event/get_evid/get_seqnum/get_deps/=.
    destruct(compute_maximum
       (filter (λ ev : Event Op, EV_Orig ev = orig) s)) eqn:E; rewrite E.
    + by apply elem_of_union_r, elem_of_singleton.
    + apply elem_of_union_r, elem_of_singleton. f_equal.
      replace (filter (λ eid : EvId, eid.1 = orig) (get_deps_set s))
        with (∅: gset EvId);
        first by rewrite size_empty.
      apply set_eq. intros x.
      split; first by intros?.
      intros [Hx_orig (ev & Hev_orig & Hev_x)%get_deps_set_incl]%elem_of_filter;
        last by apply (VLst_dep_closed _ Hv).
      assert (∃ m, compute_maximum
        (filter (λ ev : Event Op, EV_Orig ev = orig) s) = Some m) as (m & H').
      { apply event_set_maximum_exists.
        - exists ev. split; first assumption.
          rewrite /get_evid in Hev_x.
          by rewrite<- Hev_x in Hx_orig.
        - by apply (VLst_same_orig_comp _ Hv).
        - by apply (VLst_ext_time _ Hv). }
      by rewrite H' in E.
  Qed.

  Lemma mutator_evid_incl_event_preservation
    (g: Gst Op) (op: Op) (orig: fRepId):
      let fev := fresh_event (g.2 !!! orig) op orig in
      Gst_Validity g →
      event_set_evid_incl_event
        (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    intros fev Hv ev. simpl.
    intros [Hev_in | ->%elem_of_singleton]%elem_of_union;
      first by apply (VLst_evid_incl_event _ (VGst_hst_valid _ Hv)).
    rewrite event_set_get_evid;
      try by destruct (VGst_lhst_valid _ Hv orig).
    rewrite /fev/fresh_event.
    destruct(compute_maximum
       (filter (λ ev : Event Op, EV_Orig ev = orig) (g.2 !!! orig))) eqn:E;
       simpl.
    + apply elem_of_union_r, elem_of_singleton. f_equal.
    + apply elem_of_union_r, elem_of_singleton. f_equal.
      replace
        (filter (λ eid : EvId, eid.1 = orig) (get_deps_set (g.2 !!! orig)))
        with (∅: gset EvId);
        first by rewrite size_empty.
      apply set_eq. intros x.
      split; first by intros?.
      intros [Hx_orig (ev & Hev_orig & Hev_x)%get_deps_set_incl]%elem_of_filter;
        last by apply (VLst_dep_closed _ (VGst_lhst_valid _ Hv orig)).
      assert (∃ m, compute_maximum
        (filter (λ ev : Event Op, EV_Orig ev = orig) (g.2 !!! orig)) = Some m)
        as (m & H').
      { apply event_set_maximum_exists.
        - exists ev. split; first assumption.
          rewrite /get_evid in Hev_x.
          by rewrite<- Hev_x in Hx_orig.
        - by apply (VLst_same_orig_comp _ (VGst_lhst_valid _ Hv orig)).
        - by apply (VLst_ext_time _ (VGst_lhst_valid _ Hv orig)). }
      by rewrite H' in E.
  Qed.

  Lemma event_set_get_seqnum_maximum
    (s: event_set Op) (orig: fRepId) (m: Event Op):
    Lst_Validity s →
      compute_maximum (filter (λ ev, ev.(EV_Orig) = orig) s) = Some m
      → get_seqnum m = size (filter (λ eid : EvId, eid.1 = orig)
                           (get_deps_set s)).
  Proof.
    intros Hv Hcm.
    apply compute_maximum_correct in Hcm
      as [[Hm_orig Hm_in]%elem_of_filter Hm_max];
      last first.
      { intros x y
          [Hxorig Hxin]%elem_of_filter [Hyorig Hyin]%elem_of_filter Heq_t.
        by apply (VLst_ext_time _ Hv). }
    rewrite/get_seqnum Hm_orig.
    assert (filter (λ eid : EvId, eid.1 = orig) (EV_Time m)
      = filter (λ eid : EvId, eid.1 = orig) (get_deps_set s)) as ->;
      last reflexivity.
    apply set_eq. intros x. split.
    + intros [Hx_orig Hx_in]%elem_of_filter.
      apply elem_of_filter. split; first assumption.
      apply elem_of_union_list.
      exists m.(EV_Time). split; last assumption.
      by apply elem_of_elements, gset_map_correct1.
    + intros [Hx_orig Hx_in]%elem_of_filter.
      apply elem_of_filter. split; first assumption.
      apply get_deps_set_incl in Hx_in as (ev & Hev_in & Hev_eid);
        last by destruct Hv.
      destruct (decide (ev = m)) as [-> |];
        first (rewrite -Hev_eid; by apply (VLst_evid_incl_event _ Hv)).
      assert (EV_Time ev ⊂ EV_Time m).
      { apply Hm_max; last assumption.
        apply elem_of_filter. split; last assumption.
        by rewrite -Hx_orig -Hev_eid. }
      assert (x ∈ EV_Time ev).
      { rewrite -Hev_eid. by apply (VLst_evid_incl_event _ Hv). }
      set_solver.
  Qed.

  Lemma mutator_local_orig_deps_seq_preservation
    (s: Lst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event s op orig in
    Lst_Validity s → event_set_orig_deps_seq (s ∪ {[fev]}).
  Proof.
    (** Informal proof:
      let eid = (rid, sid)
      if sid ≤ get_seqnum fev ∧ rid = orig, then
        - either sid < get_seqnum fev
          In which case, there should exist an event ev in s
          such that ev.seid = eid ⇒ ok
        - either eid = get_eid fev ⇒ exists fev *)
    intros fev Hv ev [Hev_in | ->%elem_of_singleton]%elem_of_union
      rid sid HltO [-> Hsle];
      first by apply (VLst_orig_deps_seq _ Hv).
    rewrite/fev/fresh_event/=.

    destruct
      (set_choose_or_empty (filter (λ ev : Event Op, EV_Orig ev = orig) s))
      as [[ev [Hev_orig Hev_in]%elem_of_filter] | Hempty]; last first.

    { rewrite Hempty compute_maximum_empty'.
      assert (get_seqnum fev = 1);
        first (
          (rewrite event_set_get_seqnum; try by destruct Hv);
          by rewrite empty_proj_is_empty).
      assert (sid = 1) as ->; first lia.
      by apply elem_of_union_r, elem_of_singleton. }

    destruct (event_set_maximum_exists s orig) as [m Hm];
      try (by destruct Hv); first by exists ev.
    rewrite Hm.

    pose proof Hm as Hm'.
    apply compute_maximum_correct in Hm
      as [[Hm_orig Hm_in]%elem_of_filter Hm_max]; last first.
    { intros x y
        [Hxorig Hxin]%elem_of_filter [Hyorig Hyin]%elem_of_filter Heq_t.
      by apply (VLst_ext_time _ Hv). }
    
    apply le_lt_or_eq in Hsle as [Hlt | ->];
      last (
        apply elem_of_union_r, elem_of_singleton; f_equal;
        rewrite event_set_get_seqnum; by destruct Hv).

    apply elem_of_union_l.

    assert (H': evid_le (fin_to_nat orig, sid) (get_evid m)).
    { split; first by rewrite Hm_orig.
      rewrite (event_set_get_seqnum_maximum s orig m Hv Hm').
      rewrite event_set_get_seqnum in Hlt; try by destruct Hv.
      lia. }

    pose proof (VLst_orig_deps_seq _ Hv m Hm_in orig sid HltO H').
    apply elem_of_union_list.
    exists m.(EV_Time). split; last assumption.
    by apply elem_of_elements, gset_map_correct1.
  Qed.

  Lemma mutator_orig_deps_seq_preservation
    (g: Gst Op) (op: Op) (orig: fRepId):
      let fev := fresh_event (g.2 !!! orig) op orig in
      Gst_Validity g →
      event_set_orig_deps_seq
        (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).1.
  Proof.
    intros fev Hv ev. simpl. intros [Hev_in | ->%elem_of_singleton]%elem_of_union
      rid sid HltO [-> Hsle];
      first by apply (VLst_orig_deps_seq _ (VGst_hst_valid _ Hv)).
    rewrite/fev/fresh_event/=.

    destruct
      (set_choose_or_empty
        (filter (λ ev : Event Op, EV_Orig ev = orig) (g.2 !!! orig)))
      as [[ev [Hev_orig Hev_in]%elem_of_filter] | Hempty]; last first.
    { rewrite Hempty compute_maximum_empty'.
      assert (get_seqnum fev = 1).
      - rewrite event_set_get_seqnum;
          try by destruct (VGst_lhst_valid _ Hv orig).
        rewrite empty_proj_is_empty; try done.
        exact (VGst_lhst_valid _ Hv orig).
      - assert (sid = 1) as ->; first lia.
        by apply elem_of_union_r, elem_of_singleton. }

    destruct (event_set_maximum_exists (g.2 !!! orig) orig) as [m Hm];
      try (by destruct (VGst_lhst_valid _ Hv orig)); first by exists ev.
    rewrite Hm.

    pose proof Hm as Hm'.
    apply compute_maximum_correct in Hm
      as [[Hm_orig Hm_in]%elem_of_filter Hm_max];
    last first.
    { intros x y
        [Hxorig Hxin]%elem_of_filter [Hyorig Hyin]%elem_of_filter Heq_t.
      by apply (VLst_ext_time _ (VGst_lhst_valid _ Hv orig)). }
    
    apply le_lt_or_eq in Hsle as [Hlt | ->];
      last (
        apply elem_of_union_r, elem_of_singleton; f_equal;
        rewrite event_set_get_seqnum; by destruct (VGst_lhst_valid _ Hv orig)).

    apply elem_of_union_l.

    assert (H': evid_le (fin_to_nat orig, sid) (get_evid m)).
    { split; first by rewrite Hm_orig.
      rewrite (event_set_get_seqnum_maximum
          (g.2 !!! orig) orig m (VGst_lhst_valid _ Hv orig) Hm').
      rewrite event_set_get_seqnum in Hlt;
        try by destruct (VGst_lhst_valid _ Hv orig). lia. }

    pose proof
      (VLst_orig_deps_seq
        _ (VGst_lhst_valid _ Hv orig) m Hm_in orig sid HltO H').
    apply elem_of_union_list.
    exists m.(EV_Time). split; last assumption.
    by apply elem_of_elements, gset_map_correct1.
  Qed.

  Lemma mutator_lhst_valid
    (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    Gst_lhst_valid (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).
  Proof.
    intros fev Hv i.
    destruct (decide (orig = i)) as [<- | Hneq];
    [ rewrite vlookup_insert | rewrite vlookup_insert_ne; last assumption ];
    last apply (VGst_lhst_valid g Hv i).
    pose proof (VGst_lhst_valid _ Hv orig) as Hold_valid.
    split.
    - by apply mutator_local_dep_closed_preservation.
    - by apply mutator_local_same_orig_comparable_preservation.
    - by apply mutator_local_ext_evid.
    - by apply mutator_local_ext_time.
    - by apply mutator_local_orig_lt_len_preservation.
    - by apply mutator_local_seqnum_val_preservation.
    - by apply mutator_local_orig_deps_seq_preservation.
    - by apply mutator_local_seqnum_non_O_preservation.
    - by apply mutator_local_orig_max_len_preservation.
    - by apply mutator_local_evid_mon_preservation.
    - by apply mutator_local_evid_incl_event.
    - intros ev ev'
      [Hev_in | ->%elem_of_singleton]%elem_of_union
      [Hev'_in | ->%elem_of_singleton]%elem_of_union
      Hin;
      [ by apply (VLst_evid_incl_time_le _ Hold_valid) | | | done ];
      last (apply fresh_event_time_mon; by destruct Hold_valid).
      exfalso.
      apply (VLst_dep_closed _ (VGst_lhst_valid _ Hv orig) _ _ Hev_in) in Hin
        as (ev' & ev'_orig & ev'_eid).
      apply mutator_ext_evid_preservation with g op orig in ev'_eid; try done.
      + apply (fresh_event_is_fresh (g.2 !!! orig) orig op (VGst_lhst_valid _ Hv orig)).
        by rewrite-/fev -ev'_eid.
      + simpl. by apply elem_of_union_l, gst_valid_inclusion with orig.
      + simpl. by apply elem_of_union_r, elem_of_singleton.
  Qed.

  Lemma mutator_hst_valid
    (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    Gst_hst_valid (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).
  Proof.
    intros fev Hv. split.
    - by apply mutator_dep_closed_preservation.
    - by apply mutator_same_orig_comp_preservation.
    - by apply mutator_ext_evid_preservation.
    - by apply mutator_ext_time_preservation.
    - by apply mutator_orig_lt_len_preservation.
    - by apply mutator_seqid_val_preservation.
    - by apply mutator_orig_deps_seq_preservation.
    - by apply mutator_seqnum_non_O_preservation.
    - by apply mutator_orig_max_len_preservation.
    - by apply mutator_evid_mon_preservation.
    - by apply mutator_evid_incl_event_preservation.
    - simpl.
      intros ev ev'
        [Hev_in | ->%elem_of_singleton ]%elem_of_union
        [Hev'_in | ->%elem_of_singleton ]%elem_of_union Hin; try done;
        first by apply (VLst_evid_incl_time_le _ (VGst_hst_valid _ Hv)).
      + 
        apply (VLst_dep_closed _ (VGst_hst_valid _ Hv) _ _ Hev_in) in Hin
          as (ev' & ev'_orig & ev'_eid).
        apply mutator_ext_evid_preservation with g op orig in ev'_eid; try done.
        * destruct (fresh_event_is_fresh_global g orig op Hv).
          by rewrite-/fev -ev'_eid.
        * simpl. by apply elem_of_union_l.
        * simpl. by apply elem_of_union_r, elem_of_singleton.
      + apply fresh_event_time_mon;
          try by destruct (VGst_lhst_valid _ Hv orig).
        destruct (mutator_local_dep_closed_preservation (g.2 !!! orig) op orig (VGst_lhst_valid _ Hv orig))
          with fev (get_evid ev')
          as (x & [Hx_in | ->%elem_of_singleton]%elem_of_union & Hx_evid).
        * by apply elem_of_union_r, elem_of_singleton.
        * assumption.
        * apply mutator_ext_evid_preservation with g op orig in Hx_evid as ->;
            simpl; try done;
            [by apply elem_of_union_l, gst_valid_inclusion with orig
            | by apply elem_of_union_l].
        * exfalso.
          assert (ev' ∈ g.1) as Htmp; first exact Hev'_in.
          epose (mutator_ext_evid_preservation g op orig Hv fev ev' _ _ Hx_evid).
          rewrite<- e in Hev'_in.
          exact (fresh_event_is_fresh_global g orig op Hv Hev'_in).
          Unshelve.
          by apply elem_of_union_r, elem_of_singleton.
          by apply elem_of_union_l.
  Qed.

  Lemma mutator_global_valid
    (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    Gst_Validity (g.1 ∪ {[fev]}, vinsert orig (g.2 !!! orig ∪ {[fev]}) g.2).
  Proof.
    intros fev Hv. split.
    - by apply mutator_incl_local.
    - by apply mutator_incl_orig.
    - by apply mutator_hst_valid.
    - by apply mutator_lhst_valid.
  Qed.

  Lemma fresh_events_mutator_global_maximals
    (g: Gst Op) (op: Op) (orig: fRepId):
    let fev := fresh_event (g.2 !!! orig) op orig in
    Gst_Validity g →
    fev ∈ Maximals (g.1 ∪ {[fev]}).
  Proof.
    intros fev Hv.
    apply Maximals_correct.
    split; first by apply elem_of_union_r, elem_of_singleton.
    intros e [He_in| ->%elem_of_singleton]%elem_of_union;
      last by apply TM_lt_irreflexive.
    intros Himp.
    assert (get_evid fev ∈ time fev).
    { apply (mutator_local_evid_incl_event (g.2 !!! orig) op orig
        (VGst_lhst_valid _ Hv orig) fev).
      by apply elem_of_union_r, elem_of_singleton. }
    assert (get_evid fev ∈ time e);
      first by apply Himp in H0.
    assert (Lst_Validity (g.1 ∪ {[fev]}));
      first exact (VGst_hst_valid _ (mutator_global_valid g op orig Hv)).
    destruct (VLst_dep_closed _ (VGst_hst_valid g Hv) e (get_evid fev) He_in H1)
        as (ev & Hev_in & Hgeteid).
    assert(Heq: ev = fev);
      first by apply (VLst_ext_eqid _ H2 ev fev);
        [ by apply elem_of_union_l
        | by apply elem_of_union_r, elem_of_singleton
        | assumption ].
    rewrite Heq in Hev_in.
    by apply (fresh_event_is_fresh_global g orig op Hv).
  Qed.

End Gst_mutator_local_valid.

