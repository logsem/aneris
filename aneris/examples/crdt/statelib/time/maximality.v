From stdpp Require Import base gmap.
From aneris.prelude Require Import misc.
From aneris.examples.crdt.spec Require Import crdt_time.

Lemma set_choose_or_empty
  {A: Type} {EqDecision0 : EqDecision A} {H : Countable A}
         (X : gset A):
  (∃ x : A, x ∈ X) ∨ X = ∅.
Proof.
  generalize X. apply set_ind;
  [ intros?;set_solver | set_solver | ].
  intros ???[?|?]; left; exists x; set_solver.
Qed.

Section ComputeMaximals.
  Context {T: Type}.
  Context `{
      !EqDecision T, !Countable T,
      !Log_Time, !Timed T,
      !RelDecision TM_lt}.

  Definition compute_maximals (g: gset T): gset T :=
    filter
      (λ (x: T), set_Forall (λ (y: T), ¬  x <_t y) g) g.
  
  Definition compute_maximum (g: (gset T)): option T:=
    match elements (compute_maximals g) with
    | h :: [] => Some h
    | _ => None
    end.



  Lemma set_singleton_elements
    (X : gset T) (x: T):
    elements X = [x] ↔ X = {[x]}.
  Proof.
    split.
    - intros Helem.
      apply set_eq. intros y.
      split; intros Hy.
      + apply elem_of_elements.
        by rewrite elements_singleton, <-Helem, elem_of_elements.
      + apply elem_of_elements.
        by rewrite <-elem_of_elements, elements_singleton, <-Helem in Hy.
    - intros Helem. by rewrite Helem, elements_singleton.
  Qed.



  Lemma compute_maximals_correct
    (X : gset T): is_maximals X (compute_maximals X).
  Proof.
    pattern X. apply set_ind;
    [intros ???; set_solver |
      (split; [ set_solver | ]; by intros [? _]) |].
    intros y Y Hy Hmax.
    intros z. split; intros Hz.
    - apply elem_of_filter in Hz as [Hz_forall Hz_in].
      split; [ exact Hz_in |].
      intros t Hi_in. by apply Hz_forall.
    - apply elem_of_filter. split; by destruct Hz.
  Qed.

  (** The folliwing are usefull lemmas, most required for the proof of
    [compute_maximum_correct] (conferre below) *)
  Lemma elem_of_compute_maximals
    (X : gset T) (x: T):
    x ∈ compute_maximals X → x ∈ X.
  Proof. unfold compute_maximals. rewrite elem_of_filter. by intros [_ ?]. Qed.

  Lemma compute_maximals_spec_1 (g: gset T) (ev: T):
    ev ∈ (compute_maximals g) →
      ev ∈ g ∧ ∀ ev', (ev' ∈ g → ¬ ev <_t ev').
  Proof.
    intros Hev_in%elem_of_filter.
    by destruct Hev_in as [Hv_max Hev_in].
  Qed.

  Lemma compute_maximals_spec_2 (g: gset T) (ev: T):
    ev ∈ g → (∀ ev', (ev' ∈ g → ¬ ev <_t ev'))
      → ev ∈ (compute_maximals g).
  Proof.
    intros Hev_in Hev_max.
    apply elem_of_filter.
    split; [| exact Hev_in].
    intros x Hx_in. by apply Hev_max.
  Qed.

  Lemma compute_maximals_spec (g: gset T) (ev: T):
    ev ∈ (compute_maximals g) ↔ (ev ∈ g ∧ ∀ ev', (ev' ∈ g → ¬ ev <_t ev')).
  Proof.
    split.
    - apply compute_maximals_spec_1.
    - intros [??]; by apply compute_maximals_spec_2.
  Qed.


  Lemma find_one_maximal_in_compute_maximals
    (g: gset T) (x: T):
    x ∈ g
      → find_one_maximal (fun a => time a) TM_lt x (elements g)
        ∈ (compute_maximals g).
  Proof.
    (** TODO: remove this assertion *)
    assert (Hrex: ∀ a b, TM_lt a b → TM_lt b a → False);
      first apply TM_lt_exclusion.
    (**)
    intros Hxl.
    apply compute_maximals_spec_2;
      first by destruct ( find_one_maximal_eq_or_elem_of (fun a => time a) TM_lt x
        (elements g)) as [Hyp|Hyp%elem_of_elements]; first by rewrite Hyp.
    intros ev' Hev'l%elem_of_elements Hneg.
    by apply (find_one_maximal_maximal (fun a => time a) TM_lt TM_le
      TM_lt_TM_le TM_le_eq_or_lt TM_lt_irreflexive Hrex TM_le_lt_trans
      x (elements g) ev').
  Qed.

  Lemma compute_maximals_nin' (g: gset T) (x: T):
    g ≠ ∅ → x ∈ g →
    x ∉ compute_maximals g → ∃ y, y ∈ g ∧ ¬ y <_t x.
  Proof.
    intros Hnempty Hx_in Hx_nin.
    exists (find_one_maximal (λ a, time a) TM_lt x (elements g));
    pose (find_one_maximal_in_compute_maximals g x Hx_in) as Hfm;
    apply compute_maximals_correct in Hfm as [Hin Hmax].
    split; first assumption.
    by apply Hmax.
  Qed.

  Lemma compute_maximals_nin (g: gset T) (x: T):
    x ∉ (compute_maximals ({[x]} ∪ g))
    → compute_maximals ({[x]} ∪ g) = compute_maximals g.
  Proof.
    intros Hx_nin.
    assert (HnP: ¬ set_Forall (λ y, ¬ x <_t y) ({[x]} ∪ g)).
    { unfold compute_maximals in Hx_nin; rewrite elem_of_filter in Hx_nin.
      intros Hyp. apply Hx_nin.
      split; set_solver. }
    apply set_eq. intros y. split.
    - intros [[->%elem_of_singleton|Hy_in]%elem_of_union Hy_max]%compute_maximals_correct.
      + exfalso. destruct HnP. intros?. by apply Hy_max.
      + apply compute_maximals_correct. split; [ assumption |].
        intros z Hz_in. apply Hy_max. set_solver.
    - intros [Hy_in Hy_max]%compute_maximals_correct.
      apply compute_maximals_correct. split; [ set_solver |].
      intros ev [->%elem_of_singleton|Hev]%elem_of_union;
        [| by apply Hy_max].
      intros Himp.
      destruct  Hx_nin.
      apply compute_maximals_spec_2;
        first by apply elem_of_union_l, elem_of_singleton.
      intros e [->%elem_of_singleton | He_in]%elem_of_union;
        first by apply TM_lt_irreflexive.
      intros Hlt. apply (Hy_max e); first assumption.
      by apply TM_lt_trans with (time x).
  Qed.



  Lemma compute_maximals_empty (X: gset T):
    compute_maximals X ≡ ∅ ↔ X ≡ ∅.
  Proof.
    generalize X; apply set_ind; [(intros?; set_solver)|set_solver|].
    intros x Y Hw_nin HY_empty_iff. split; last set_solver.
    intros Hyp. exfalso.
    assert (H': x ∉ compute_maximals ({[x]} ∪ Y));
      try by rewrite Hyp.
    rewrite compute_maximals_nin in Hyp; try exact H'.
    apply H', elem_of_filter. 
    split; last set_solver.
    intros x'.
    intros [->%elem_of_singleton | Hx'_in]%elem_of_union.
    - by apply TM_lt_irreflexive.
    - by replace Y with (∅: gset T) in *; last set_solver.
  Qed.

  Lemma compute_maximals_bigger (g: gset T) (ev: T):
    ev ∈ g → ∃ maxev, maxev ∈ (compute_maximals g) ∧ ev ≤_t maxev.
  Proof.
    intros Hev_in.
    destruct (set_choose_or_empty g) as [eqn|eqn];
      last (apply compute_maximals_empty in Hev_in; set_solver).
    exists (find_one_maximal (fun a => time a) TM_lt ev (elements g)).
    split; first by apply find_one_maximal_in_compute_maximals.
    apply (find_one_maximal_rel (λ a, time a) TM_lt TM_le).
    apply TM_lt_TM_le.
  Qed.

  Lemma compute_maximum_correct:
    ∀ X : gset T,
      (∀ x y : T, x ∈ X → y ∈ X → x =_t y → x = y)
      → ∀ x : T, compute_maximum X = Some x ↔ is_maximum x X.
  Proof.
    intros g Hmaxeq x. split; intros Hmax.
    - unfold compute_maximum in Hmax.
      assert (Heq: compute_maximals g = {[x]}).
      { destruct (set_choose_or_empty (compute_maximals g)) as [eqn|eqn];
          last by rewrite eqn in Hmax.
        destruct (elements (compute_maximals g)) as [|h t] eqn:E1;
          [|destruct t eqn:E2]; try done.
        apply set_singleton_elements. by simplify_eq. } clear Hmax.
      assert (Hin: x ∈ g).
      { apply elem_of_compute_maximals. set_solver. }
      split; first assumption.
      intros t Htin Htne.
      destruct (compute_maximals_bigger g t Htin) as (y & Hyn & Hle_ty).
      rewrite Heq in Hyn. apply elem_of_singleton in Hyn. simplify_eq.
      by apply TM_le_eq_or_lt in Hle_ty as [Heq_ty| Hlt_ty];
      first by rewrite (Hmaxeq t x Htin Hin Heq_ty) in Htne.
    - unfold compute_maximum. destruct Hmax as [Hin Hlt].
      destruct (elements (compute_maximals g)) eqn: E.
      { apply elements_empty_inv in E.
        rewrite compute_maximals_empty in E. set_solver. }
      destruct l.
      * f_equal.
        assert (x ∈ compute_maximals g) as Hxin%elem_of_elements.
        { assert (t ∈ compute_maximals g)
            as [Ht_in Ht_max]%compute_maximals_correct;
            last assert (x = t) as ->.
          - apply elem_of_elements. rewrite E. apply elem_of_list_here.
          - destruct (decide(x = t)); first done.
            apply Hmaxeq; try done.
            destruct (Ht_max x Hin).
            by apply Hlt.
          - apply elem_of_elements. rewrite E. apply elem_of_list_here. }
        rewrite E in Hxin. set_solver.
      * exfalso. (** replace s ans s0 with x*)
        assert (H1: t ∈ elements (compute_maximals g)).
        { rewrite E. apply elem_of_list_here. }
        assert (H2: t0 ∈ elements (compute_maximals g)).
        { rewrite E. apply elem_of_list_further, elem_of_list_here. }
        destruct (compute_maximals_spec_1 g t)
          as [Hsing Hs]; first by apply elem_of_elements in H1.
        destruct (compute_maximals_spec_1 g t0)
          as [Hs0ing Hs0]; first by apply elem_of_elements in H2.
        apply (Hs x); first assumption.
        apply (Hlt t); first assumption.
        intros Hsx.
        apply (Hs0 x); first assumption.
        apply (Hlt t0); first assumption.
        intros Hs0x.
        simplify_eq.
        pose (NoDup_elements (compute_maximals g)) as Hyp.
        replace (elements (compute_maximals g)) with (x :: x :: l) in Hyp.
        apply NoDup_cons_1_1 in Hyp.
        apply Hyp, elem_of_list_here.
  Qed.



  Global Instance maximals_computing : Maximals_Computing T:=
    {|
        Maximals := λ g, compute_maximals g;
        Maximum := λ g, compute_maximum g;
        Maximals_correct := compute_maximals_correct;
        Maximum_correct := compute_maximum_correct |}.
End ComputeMaximals.

Section UsefulLemmas.
  Context {T: Type}.
  Context `{
      !EqDecision T, !Countable T,
      !Log_Time, !Timed T,
      !RelDecision TM_lt}.

  Lemma maximals_union (X Y: gset T) (x: T):
    x ∈ compute_maximals (X ∪ Y)
      → (x ∈ compute_maximals X ∨ x ∈ compute_maximals Y).
  Proof.
    intros Hx_in.
    assert (x ∈ compute_maximals (X ∪ Y))
      as [Hyp|Hyp]%elem_of_compute_maximals%elem_of_union;
      first assumption;
      [left|right];
      apply compute_maximals_spec in Hx_in as [Hin Hmax];
      apply compute_maximals_spec; (split; first assumption);
      intros y Hy;
      apply Hmax;
    set_solver.
  Qed.

  Lemma compute_maximum_empty:
    compute_maximum (∅: gset T) = None.
  Proof. reflexivity. Qed.

  Lemma compute_maximals_simgleton (t: T):
    compute_maximals ({[ t ]}: gset T) = ({[ t ]}: gset T).
  Proof.
    unfold compute_maximals.
    apply set_eq.
    intros x; split.
    - by intros [_ Hx_in]%elem_of_filter.
    - intros ->%elem_of_singleton.
      apply elem_of_filter; split.
      + intros y ->%elem_of_singleton. apply TM_lt_irreflexive.
      + by apply elem_of_singleton.
  Qed.

  Lemma compute_maximum_simgleton (t: T):
    compute_maximum {[ t ]} = Some t.
  Proof.
    unfold compute_maximum.
    by rewrite compute_maximals_simgleton, elements_singleton.
  Qed.

  Lemma compute_maximals_non_empty {X: gset T} {x: T}
    (_: x ∈ X): compute_maximals X ≠ ∅.
  Proof.
    intros Hcm_empty.
    pose proof (compute_maximals_empty X).
    set_solver.
  Qed.

  Lemma set_singleton_eq (X: gset T) (x: T):
    (x ∈ X ∧ (∀ y, y ∈ X → y = x)) ↔ X = {[ x ]}.
  Proof. set_solver. Qed.

  Lemma compute_maximum_non_empty (X: gset T):
    (∀ (x y: T), x ∈ X → y ∈ X → x <_t y ∨ x =_t y ∨ y <_t x)
    → (∀ (x y: T), x ∈ X → y ∈ X → x =_t y → x = y)
    → (X ≠ ∅ ↔ (∃ (m: T), compute_maximum X = Some m)).
  Proof.
    intros Hcomp Hext. split.
    - intros [m Hm_in]%set_choose_L.
      pose proof (compute_maximals_non_empty Hm_in) as [o [Ho_in Ho_max]%compute_maximals_correct]%set_choose_L.
      exists o.
      unfold compute_maximum.
      assert (compute_maximals X = {[ o ]}) as ->.
      { apply set_singleton_eq.
        split; first by apply compute_maximals_correct.
        intros n [Hn_in Hn_max]%compute_maximals_correct.
        pose proof (Hcomp o n Ho_in Hn_in) as [Himp | [Heq | Himp]].
        - exfalso. by apply (Ho_max n).
        - by apply Hext.
        - exfalso. by apply (Hn_max o). }
      by rewrite elements_singleton.
    - intros [m [Hm_in Hm_max]%compute_maximum_correct];
        first set_solver.
      exact Hext.
  Qed.

  Lemma compute_maximum_empty' `{!LeibnizEquiv (gset T)} :
    compute_maximum (∅: gset T) = None.
  Proof.
    unfold compute_maximum, compute_maximals.
    rewrite filter_empty_L; last assumption.
    by rewrite elements_empty.
  Qed.
End UsefulLemmas.

