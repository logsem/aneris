From stdpp Require Import base countable list sets.
From aneris.aneris_lang Require Import lang.
From aneris.prelude Require Import time misc gset_map.
From aneris.examples.crdt.spec Require Import crdt_time crdt_events.
From aneris.examples.crdt.statelib.proof Require Import utils.
From aneris.examples.crdt.statelib.time Require Import time maximality.

Lemma set_choose_or_empty
  {A: Type} {EqDecision0 : EqDecision A} {H : Countable A}
         (X : gset A):
  (∃ x : A, x ∈ X) ∨ X = ∅.
Proof.
  generalize X. apply set_ind;
  [ intros?;set_solver | set_solver | ].
  intros ???[?|?]; left; exists x; set_solver.
Qed.

(** * Instantiation of Statelib events *)
Section Events.
  Context {Op: Type}.
  Context `{!EqDecision Op, !Countable Op}.
  
  Global Instance stlib_event_eqdec : EqDecision (Event Op).
  Proof. solve_decision. Defined.

  Global Instance stlib_event_timed : Timed (Event Op) := { time := EV_Time }.
End Events.


Section UsefulFunctions.
  Context `{Op: Type, !EqDecision Op, !Countable Op}.

  Definition get_seqnum (ev: Event Op) : SeqNum :=
    size (filter (λ eid: EvId, eid.1 = ev.(EV_Orig)) ev.(EV_Time)).

  Definition get_evid (ev: Event Op) : EvId :=
    (ev.(EV_Orig), get_seqnum ev).

  Definition depends_on  (ev ev': Event Op) := get_evid ev' ∈ ev.(EV_Time).

  Definition get_deps (e: Event Op): gset EvId := e.(EV_Time).
  Definition get_deps_set (s: event_set Op) : gset EvId :=
    gset_flat_map get_deps s.

  Definition fresh_event (s: event_set Op) (op: Op) (orig: RepId): Event Op :=
      {|
        EV_Op := op ;
        EV_Orig := orig ;
        EV_Time :=
          let seen_events := get_deps_set s in
          let new_event := (orig, S (size (filter (λ eid, eid.1 = orig) (get_deps_set s)))) in
          seen_events ∪ {[ new_event ]}
      |}.

  Definition hproj (i: RepId) (st: event_set Op) :=
    filter (λ ev, ev.(EV_Orig) = i) st.
End UsefulFunctions.



Section EventSets.
  Context `{Op: Type, !EqDecision Op, !Countable Op}.

  (* A set of events is `dep_closed` if it contains every causal dependency of
     every element of the set. *)
  Definition dep_closed (s : gset (Event Op)) : Prop :=
    ∀ (e: Event Op) (evid: EvId),
      e ∈ s →
      evid ∈ e.(EV_Time) →
      ∃ (e': Event Op), e' ∈ s ∧ get_evid e' = evid.

  Definition events_ext_evid (s: event_set Op) : Prop :=
    ∀ ev ev', ev ∈ s → ev' ∈ s → get_evid ev = get_evid ev' → ev = ev'.

  Definition events_ext_time (s: event_set Op) : Prop :=
    ∀ ev ev', ev ∈ s → ev' ∈ s → ev =_t ev' → ev = ev'.

  Definition event_set_same_orig_comparable (st: event_set Op) : Prop :=
    ∀ e e', e ∈ st → e' ∈ st → e.(EV_Orig) = e'.(EV_Orig) → e <_t e' ∨ e =_t e' ∨ e' <_t e.

  Definition event_set_orig_lt {i: nat} (st: event_set Op) : Prop :=
    ∀ ev, ev ∈ st → ev.(EV_Orig) < i.

  Definition event_set_orig_deps_seq (st: event_set Op) : Prop :=
    ∀ (e: Event Op),
      e ∈ st →
      ∀ (i: RepId) (sid: nat), O < sid → evid_le (i, sid) (get_evid e) →
      (i, sid) ∈ e.(EV_Time).

  Definition event_set_orig_max {nb: nat} (st: event_set Op) : Prop :=
    ∀ (i: RepId), i < nb
      → hproj i st = ∅ ∨ ∃ m, m ∈ st ∧ compute_maximum (hproj i st) = Some m.

  Definition event_set_evid_mon (st: event_set Op) : Prop :=
    ∀ ev ev', ev ∈ st → ev' ∈ st → ev.(EV_Orig) = ev'.(EV_Orig) →
      ev <_t ev' → evid_le (get_evid ev) (get_evid ev').

  Lemma dep_closed_union (s s' : gset (Event Op)) :
    dep_closed s -> dep_closed s' -> dep_closed (s ∪ s').
  Proof.
    intros Hdc Hdc'  ev eid [Hin|Hin]%elem_of_union Hdep;
    [ destruct (Hdc ev eid Hin Hdep)
        as (ev' & Hev'_in%(elem_of_union_l _ s s') & Heq)
    | destruct (Hdc' ev eid Hin Hdep)
        as (ev' & Hev'_in%(elem_of_union_r _ s s') & Heq) ];
    by exists ev'.
  Qed.
End EventSets.

Section Events.
  Context {Op: Type}.
  Context `{!EqDecision Op, !Countable Op}.

  Definition cc_impl : relation (gset (Event Op)) :=
    λ s s',
      ∀ (e e' : Event Op),
        e ∈ s' → e' ∈ s' →
        e ≤_t e' ->
        e' ∈ s →
        e ∈ s.

  Global Instance cc_impl_refl : Reflexive cc_impl.
  Proof.
    intros s e e' Hin Hin' Hlt Hin''.
    done.
  Qed.

  Definition cc_subseteq : relation (gset (Event Op)) :=
    λ s s', s ⊆ s' ∧ cc_impl s s'.

  Global Instance cc_subseteq_preorder : PreOrder cc_subseteq.
  Proof.
    split; constructor.
    - done.
    - rewrite /cc_impl. eauto.
    - destruct H as [H _].
      destruct H0 as [H0 _].
      set_solver.
    - destruct H as [Hsub Hy].
      destruct H0 as [Hsub' Hz].
      intros e e' Hin Hin' Hle Hinx.
      assert (e' ∈ y) as He'y by set_solver.
      assert (e ∈ y) as Hey.
      { apply (Hz e e'); auto. }
      apply (Hy e e'); auto.
  Qed.

  Lemma cc_subseteq_union h h1 h2 :
    cc_subseteq h1 h -> cc_subseteq h2 h -> cc_subseteq (h1 ∪ h2) h.
  Proof.
    intros [Hsub1 Hcc1] [Hsub2 Hcc2].
    split; [set_solver |].
    intros e e' Hin Hin' Hle [Hl | Hr]%elem_of_union.
    - apply elem_of_union_l.
      apply (Hcc1 e e'); auto.
    - apply elem_of_union_r.
      apply (Hcc2 e e'); auto.
  Qed.
End Events.

Global Arguments cc_subseteq {_ _ _}.



Section ComputeMaximumLemams.
  Context `{Op: Type, !EqDecision Op, !Countable Op}.

  Lemma event_set_maximum_exists (s: event_set Op) (orig: RepId):
    (∃ e, e ∈ s ∧ e.(EV_Orig) = orig)
      → event_set_same_orig_comparable s
      → events_ext_time s
      → ∃ m, compute_maximum (hproj orig s) = Some m.
  Proof.
    intros (e & He_in & He_orig) Hcomp Hext_t.
    unfold compute_maximum.
    destruct (set_choose_or_empty (compute_maximals (hproj orig s)))
      as [(m & [Hm_max [Hm_orig Hm_in]%elem_of_filter]%elem_of_filter) | Hnil].
    - assert (compute_maximals (hproj orig s) = {[ m ]}) as ->.
      { apply set_eq. intros n. split.
        - intros [[Hn_orig Hn_in]%elem_of_filter Hn_max]%compute_maximals_correct.
          apply elem_of_singleton.
          specialize Hn_max with m.
          destruct (Hcomp n m) as [H | [H | H]]; try done.
          + by rewrite Hn_orig Hm_orig.
          + by destruct Hn_max; first apply elem_of_filter.
          + by apply Hext_t.
          + by destruct (Hm_max n); first apply elem_of_filter.
        - intros ->%elem_of_singleton.
          apply elem_of_filter. by split; last apply elem_of_filter. }
      rewrite elements_singleton.
      by exists m.
    - rewrite set_eq -set_equiv compute_maximals_empty set_equiv -set_eq in Hnil.
      assert (He_in': e ∈ hproj orig s); first by apply elem_of_filter.
      set_solver.
  Qed.
End ComputeMaximumLemams.



Section UsefulLemmas.
  Context {Op: Type}.
  Context `{!EqDecision Op, !Countable Op}.

  Lemma maximals_union (X Y: event_set Op) (x: Event Op):
    x ∈ compute_maximals (X ∪ Y)
      → (x ∈ compute_maximals X ∨ x ∈ compute_maximals Y).
  Proof.
    intros Hx_in.
    assert (x ∈ compute_maximals (X ∪ Y))
      as [H|H]%elem_of_compute_maximals%elem_of_union;
      first assumption;
      [left|right];
      apply compute_maximals_spec in Hx_in as [Hin Hmax];
      apply compute_maximals_spec; (split; first assumption);
      intros y Hy;
      apply Hmax;
    set_solver.
  Qed.
End UsefulLemmas.

