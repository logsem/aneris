From stdpp Require Import gmap.
From aneris.prelude Require Import gset_map.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import vector_clock_proof.
From aneris.prelude Require Import time.
From aneris.examples.crdt.spec Require Import crdt_time.

(** * Logical events *)

Section Events.

  Context `{!Log_Time}.

  Record Event Op := { EV_Op : Op; EV_Orig : nat; EV_Time : Time }.

  Global Arguments EV_Op {_} _.
  Global Arguments EV_Orig {_} _.
  Global Arguments EV_Time {_} _.

  Global Instance Event_Timed Op : Timed (Event Op) := EV_Time.

  Global Instance Event_EqDecision Op `{!EqDecision Op} : EqDecision (Event Op).
  Proof. solve_decision. Qed.

  Global Instance Event_Countable Op `{!EqDecision Op} `{!Countable Op} : Countable (Event Op).
  Proof.
    apply (inj_countable'
              (λ ev, (ev.(EV_Op), ev.(EV_Orig), ev.(EV_Time)))
              (λ tp, {|EV_Op := tp.1.1; EV_Orig := tp.1.2; EV_Time := tp.2 |})).
    by intros [].
  Qed.

  Definition event_map {Op1 Op2} (f : Op1 → Op2) (ev : Event Op1) :=
    {| EV_Op := f ev.(EV_Op); EV_Orig := ev.(EV_Orig); EV_Time := ev.(EV_Time) |}.

  Notation event_set Op := (gset (Event Op)).

  Context Op `{!EqDecision Op} `{!Countable Op}.

  Definition causally_closed : relation (event_set Op) :=
    λ (s s' : event_set Op),
      ∀ (e e' : Event Op),
        e ∈ s' → e' ∈ s' →
        e ≤_t e' ->
        e' ∈ s →
        e ∈ s.

  Section Causally_Closed_Example.
    Context (e1 e2 : Event Op) (He1_l1 : e1 ≤_t e2).
    Context (S1 S2 : event_set Op) (Hcc : causally_closed S1 S2).

    Example causally_closed_ex :
      e1 ∈ S2 -> e2 ∈ S2 -> e2 ∈ S1 -> e1 ∈ S1.
    Proof.
      intros He1 He2 Hin.
      eapply (Hcc e1 e2); eauto.
    Qed.
  End Causally_Closed_Example.

  Definition causally_closed_subseteq : relation (event_set Op) :=
    λ (s s' : (event_set Op)), s ⊆ s' ∧ causally_closed s s'.

  Definition events_ext {Op'} `{!EqDecision Op'} `{!Countable Op'} (s : gset (Event Op')) :=
    ∀ e e', e ∈ s -> e' ∈ s -> e  =_t e' -> e = e'.

  Lemma events_ext_singleton (ev : Event Op) : events_ext {[ev]}.
  Proof.
    intros ?? ?%elem_of_singleton ?%elem_of_singleton; simplify_eq; done.
  Qed.

  Lemma events_ext_map {Op2} `{!EqDecision Op2} `{!Countable Op2} (f : Op → Op2) s :
    events_ext s → events_ext (gset_map (event_map f) s).
  Proof.
    intros Hext ? ? [e1 [-> He1]]%gset_map_correct2 [e2 [-> He2]]%gset_map_correct2 Hes.
    f_equal.
    apply Hext; done.
  Qed.

  Lemma events_ext_filter (P : Event Op → Prop) `{!∀ ev, Decision (P ev)} s :
    events_ext s → events_ext (filter P s).
  Proof.
    intros Hs ev ev'; rewrite !elem_of_filter; intros [? ?] [? ?] ?; apply Hs; done.
  Qed.

  Definition events_total_order (s : gset (Event Op)) :=
    ∀ e e', e ∈ s -> e' ∈ s -> e ≠ e' -> (EV_Orig e) = (EV_Orig e') -> (e <_t e' ∨ e' <_t e).

End Events.

Notation event_set Op := (gset (Event Op)).
Notation "s1 '⊆_cc' s2" := (causally_closed_subseteq _ s1 s2) (at level 70, no associativity).

Global Arguments events_ext {_ _ _ _} _.
Global Arguments events_total_order {_ _ _ _} _.
