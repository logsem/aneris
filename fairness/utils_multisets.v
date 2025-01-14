From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
(* From stdpp Require Import relations. *)
From trillium.fairness Require Import lemmas.

Ltac mss := multiset_solver. 

(* TODO: move *)
Section GmultisetUtils.
  Context `{Countable A}. 
  
  Lemma gmultiset_difference_exact (X Y: gmultiset A):
    X ∖ Y = X ∖ (X ∩ Y). 
  Proof using. clear. mss. Qed. 
  
  Lemma gmultiset_difference_twice (X Y Z: gmultiset A):
    X ∖ Y ∖ Z = X ∖ (Y ⊎ Z). 
  Proof using. clear. mss. Qed.
  
  Lemma gmultiset_cancel_l1 (X Y: gmultiset A):
    (X ⊎ Y) ∖ Y = X. 
  Proof using. clear. mss. Qed.
  
  Lemma gmultiset_cancel_l2 (X Y: gmultiset A):
    (X ⊎ Y) ∖ X = Y. 
  Proof using. clear. mss. Qed.
  
  Lemma gmultiset_difference_disjoint (X Y: gmultiset A)
    (DISJ: X ## Y):
    X ∖ Y = X.
  Proof using. clear -DISJ. mss. Qed. 
  
  Lemma gmultiset_split_exact (X Y: gmultiset A):
    X = (X ∖ Y) ⊎ (X ∩ Y). 
  Proof using. mss. Qed.

  Lemma gmultiset_disj_union_difference_split (X Y Z: gmultiset A):
    (X ⊎ Y) ∖ Z = X ∖ (Z ∖ Y) ⊎ Y ∖ Z.
  Proof using. mss. Qed. 

  Lemma gmultiset_split (X Y: gmultiset A):
    exists I X' Y', X = X' ⊎ I /\ Y = Y' ⊎ I /\ X' ## Y'.
  Proof using.
    set (I := X ∩ Y).
    exists I, (X ∖ I), (Y ∖ I). repeat split.
    1, 2: rewrite gmultiset_disj_union_comm; apply gmultiset_disj_union_difference; mss.
    mss. 
  Qed.

  Lemma scalar_mul_le `{Countable K} (s: gmultiset K) m n
    (LE: m <= n):
    m *: s ⊆ n *: s.
  Proof using.
    clear -LE. 
    apply Nat.le_sum in LE as [d ->]. mss.
  Qed.

  (* TODO: move *)
  Lemma gset_singleton_if_equiv (P: A -> Prop)
    `{forall k, Decision (P k)}:
    forall k, filter P ({[ k ]}: gset A) = if (decide (P k)) then {[ k ]} else ∅.
  Proof using.
    intros. destruct decide; set_solver.
  Qed.

  Lemma gmultiset_empty_no_elements:
    forall (g: gmultiset A), g = ∅ <-> forall k, ¬ k ∈ g.
  Proof using. mss. Qed.

  Lemma not_elem_of_multiplicity a (g: gmultiset A):
    a ∉ g ↔ multiplicity a g = 0.
  Proof using. mss. Qed.

  Lemma multiplicity_big_DU_set (D: gset A) (f: A -> nat):
    forall a, 
    multiplicity a ([^disj_union set] a ∈ D, f a *: {[+ a +]}) =
    if (decide (a ∈ D)) then (f a) else 0.
  Proof using.
    pattern D. apply set_ind; clear D. 
    { red. intros ???. set_solver. }
    { intros. rewrite big_opS_empty. set_solver. }
    intros d D FRESH IH a.
    rewrite big_opS_insert; [| done].
    rewrite multiplicity_disj_union. rewrite IH.
    rewrite multiplicity_scalar_mul multiplicity_singleton'.
    destruct decide, decide; [set_solver| ..]. 
    1, 2: rewrite decide_True; [| set_solver].
    3: rewrite decide_False; [| set_solver].
    all: subst; lia.
  Qed. 

  Lemma gmultiset_elem_of_weaken (x y: gmultiset A) k:
    k ∈ x ∖ y -> k ∈ x.
  Proof using. multiset_solver. Qed. 

  Section MultisetFilter.
    Context (P : A → Prop). 
    Context `{∀ x, Decision (P x)}. 

    Definition mset_filter (g: gmultiset A): gmultiset A :=
      list_to_set_disj $ filter P $ elements g. 

    Lemma mset_filter_spec g:
      forall a, a ∈ mset_filter g <-> a ∈ g /\ P a.
    Proof using.
      intros. rewrite /mset_filter.
      rewrite elem_of_list_to_set_disj elem_of_list_filter.
      rewrite gmultiset_elem_of_elements. tauto.
    Qed.

    Lemma mset_filter_empty:
      mset_filter ∅ = ∅. 
    Proof using. mss. Qed.

    Lemma mset_filter_disj_union x y:
      mset_filter (x ⊎ y) = mset_filter x ⊎ mset_filter y.
    Proof using.
      rewrite /mset_filter.
      rewrite -list_to_set_disj_app. rewrite -filter_app. 
      apply list_to_set_disj_perm. apply filter_Permutation.
      apply gmultiset_elements_disj_union.
    Qed.

    Lemma mset_filter_singleton a:
      mset_filter {[+ a +]} = if (decide (P a)) then {[+ a +]} else ∅.
    Proof using.
      rewrite /mset_filter. rewrite gmultiset_elements_singleton.
      rewrite filter_cons !filter_nil.
      destruct decide; mss.
    Qed. 

    Lemma mset_filter_multiplicity g (a: A):
      multiplicity a (mset_filter g) =
      if (decide (P a)) then multiplicity a g else 0.
    Proof using. 
      revert a. pattern g. apply gmultiset_ind; clear g. 
      { intros ?. rewrite mset_filter_empty multiplicity_empty.
        destruct decide; auto. }
      intros x g IH a.
      rewrite mset_filter_disj_union mset_filter_singleton.
      rewrite !multiplicity_disj_union. rewrite multiplicity_singleton'. 
      rewrite IH. 
      destruct (decide (P x)), (decide (P a)); try rewrite multiplicity_singleton'.
      - lia.
      - rewrite decide_False; [| by intros ->]. lia.
      - rewrite decide_False; [| by intros ->].
        rewrite multiplicity_empty. lia.
      - rewrite multiplicity_empty. lia.
    Qed.

    Lemma mset_filter_True g
      (FALSE: forall a, a ∈ g -> P a):
      mset_filter g = g.
    Proof using.
      apply gmultiset_eq. intros a.
      rewrite mset_filter_multiplicity.
      destruct (decide (a ∈ g)).
      { rewrite decide_True; eauto. }
      rewrite (proj1 (not_elem_of_multiplicity _ _) _); auto.
      destruct decide; done. 
    Qed.

    Lemma mset_filter_False g
      (FALSE: forall a, a ∈ g -> ¬ P a):
      mset_filter g = ∅.
    Proof using.
      destruct (decide (mset_filter g = ∅)) as [| NE]; [done| ]. 
      apply gmultiset_choose in NE as [? IN].
      apply mset_filter_spec in IN as [??]. set_solver.
    Qed. 

    Lemma mset_filter_subseteq_mono:
      Proper (subseteq ==> subseteq) mset_filter.
    Proof using.
      red. intros ????.
      rewrite !mset_filter_multiplicity.
      destruct decide; mss.
    Qed. 

    Lemma mset_filter_difference x y:
      mset_filter (x ∖ y) = mset_filter x ∖ mset_filter y.
    Proof using.
      apply gmultiset_eq. intros a.
      rewrite !multiplicity_difference !mset_filter_multiplicity !multiplicity_difference.
      destruct decide; mss. 
    Qed.

    Lemma mset_filter_mul_comm g n:
      mset_filter (n *: g) = n *: mset_filter g.
    Proof using.
      apply gmultiset_eq. intros ?.
      rewrite multiplicity_scalar_mul.
      rewrite !mset_filter_multiplicity.
      destruct decide; try mss. 
      by rewrite multiplicity_scalar_mul.
    Qed.

    Lemma mset_filter_sub g:
      mset_filter g ⊆ g.
    Proof using.
      do 2 red. intros. rewrite mset_filter_multiplicity.
      destruct decide; lia.
    Qed. 

  End MultisetFilter.

End GmultisetUtils.

Section MultisetOrder.
  Context `{Countable A}.
  Context (R: relation A).
  Context {PO: PartialOrder R}.

  (* reflexive version of Huet and Oppen definition *)
  Definition ms_le (X Y: gmultiset A) :=
    forall a, multiplicity a X > multiplicity a Y ->
    exists b, R a b /\ multiplicity b X < multiplicity b Y.

  Definition ms_lt := strict ms_le. 
  
  (* original Huet and Oppen definition *)
  Definition ms_lt' (X Y: gmultiset A) :=
    forall a, multiplicity a X > multiplicity a Y ->
    exists b, strict R a b /\ multiplicity b X < multiplicity b Y.

  Definition dominates_over (X Y: gmultiset A) :=
    forall y, y ∈ Y -> exists x, x ∈ X /\ strict R y x.

  Instance dominates_over_Proper: Proper (equiv ==> equiv ==> iff) dominates_over.
  Proof using. clear. intros ??????. mss. Qed.

  Lemma dominates_minus1 (X Y: gmultiset A) a
    (DOM': dominates_over (X ⊎ {[+ a +]}) (Y ⊎ {[+ a +]})):
    dominates_over X Y.
  Proof using PO.
    red. intros y Yy.
    red in DOM'.
    pose proof (DOM' y ltac:(mss)) as Dy.
    destruct Dy as (x & IN' & RR).
    apply gmultiset_elem_of_disj_union in IN' as [? | EQ].
    { eauto. }
    apply gmultiset_elem_of_singleton in EQ. subst.
    specialize (DOM' a ltac:(mss)) as (x & IN' & RR').    
    apply gmultiset_elem_of_disj_union in IN' as [? | EQ].
    2: { apply gmultiset_elem_of_singleton in EQ. subst.
         apply strict_spec_alt in RR'. tauto. }
    exists x. split; auto. etrans; eauto.
  Qed.

  Lemma gmultiset_difference_empty (X: gmultiset A):
    X ∖ ∅ = X.
  Proof using. clear. mss. Qed. 

  Lemma dominates_minus (X Y D: gmultiset A)
    (DOM': dominates_over (X ⊎ D) (Y ⊎ D)):
    dominates_over X Y.
  Proof using PO.
    generalize dependent X. generalize dependent Y. pattern D. apply gmultiset_ind.
    { intros ??. by rewrite !gmultiset_disj_union_right_id. }
    intros. eapply H0. eapply (dominates_minus1 _ _ x).
    eapply dominates_over_Proper; [..| apply DOM']; mss.
  Qed. 

  Definition ms_le_dm (M N: gmultiset A) :=
    exists X Y, X ⊆ N /\ M = (N ∖ X) ⊎ Y /\ dominates_over X Y. 

  Lemma ms_le_equiv X Y:
    ms_le X Y <-> (ms_lt' X Y \/ X = Y).
  Proof using PO.
    rewrite /ms_le /ms_lt'. split.
    - intros LE.
      destruct (decide (X = Y)) as [-> | ?]; [tauto| ].
      left. intros a GTa.
      specialize (LE _ GTa). destruct LE as (b & Rab & LEb).
      destruct (decide (a = b)).
      { subst. lia. }
      exists b. split; [| done]. 
      split; auto. intros ?. edestruct PO; eauto.
    - intros [LT | ->].
      2: { lia. }
      intros a GTa.
      specialize (LT _ GTa). destruct LT as (b & Rab & LTb).
      eexists. repeat split; eauto. apply Rab.
  Qed.

  Lemma ms_le_equiv'    
    X Y:
    ms_le X Y <-> ms_le_dm X Y.
  Proof using PO.
    rename X into M, Y into N.
    set mu := @multiplicity A _ _. 
    set (D := dom M ∪ dom N). 
    rewrite /ms_le /ms_le_dm. split.
    - intros LE.
      set (X := [^ disj_union set] a ∈ D, (mu a N - mu a M) *: {[+ a +]}).
      set (Y := [^ disj_union set] a ∈ D, (mu a M - mu a N) *: {[+ a +]}).
      exists X, Y. repeat split.
      + subst X.
        do 2 red. intros. rewrite multiplicity_big_DU_set.
        subst mu. destruct decide; lia. 
      + subst X Y. apply gmultiset_eq. intros a.
        rewrite multiplicity_disj_union.
        rewrite multiplicity_difference.
        rewrite !multiplicity_big_DU_set.
        subst mu. destruct decide; try lia.
        subst D. 
        rewrite !(proj1 (not_elem_of_multiplicity _ _)); [lia| ..].
        all: intros ?%gmultiset_elem_of_dom; set_solver.
      + intros y Yy.
        subst Y. rewrite elem_of_multiplicity in Yy.
        rewrite multiplicity_big_DU_set in Yy. destruct decide; [| lia].
        pose proof Yy. 
        apply Nat.lt_add_lt_sub_r in Yy. apply LE in Yy as (x&?&GT).
        exists x. split.
        2: { apply strict_spec_alt. split; auto. intros ->.
             subst mu. lia. }
        subst X. do 2 red. rewrite multiplicity_big_DU_set.
        subst mu. 
        rewrite decide_True; [lia| ]. subst D. apply elem_of_union. right.
        apply gmultiset_elem_of_dom. do 2 red. lia.
    - intros LE a LT.  
      assert (∃ X Y, X ⊆ N ∧ M = N ∖ X ⊎ Y ∧
                     dominates_over X Y /\
                     X ## Y).
      { destruct LE as (X & Y & SUB & -> & GT).
        apply gmultiset_disj_union_difference in SUB. remember (N ∖ X) as U.
        subst N. clear HeqU.
        set (V := X ∩ Y).
        exists (X ∖ V), (Y ∖ V).
        repeat split.
        - mss.
        - apply gmultiset_eq. intros b.
          repeat rewrite ?multiplicity_disj_union ?multiplicity_difference ?multiplicity_intersection.
          subst V. subst mu. lia.
        - subst V. 
          pose proof (gmultiset_split_exact X Y) as EQX.
          pose proof (gmultiset_split_exact Y X) as EQY. 
          rewrite gmultiset_difference_exact in EQX.
          rewrite gmultiset_difference_exact in EQY.
          rewrite EQX in GT. rewrite {3}EQY in GT.
          rewrite (gmultiset_intersection_comm Y _) in GT.
          eapply dominates_minus; eauto.
        - mss. }
      clear LE. destruct H0 as (X & Y & SUB & -> & GT & DISJ).
      apply gmultiset_disj_union_difference in SUB. remember (N ∖ X) as U.
      subst N. clear HeqU.
      rewrite !multiplicity_disj_union in LT.
      specialize (GT a). destruct GT as (x & INx & R'ax).
      { apply elem_of_multiplicity. lia. }
      eexists. split; [apply R'ax| ].
      rewrite !multiplicity_disj_union.
      rewrite elem_of_multiplicity in INx. 
      enough (multiplicity x Y = 0); [lia| ].
      apply not_elem_of_multiplicity. intros ?%DISJ; eauto.
  Qed.

  Global Instance ms_le_PreOrder: PreOrder ms_le.
  Proof using PO.
    split.
    { red. intros g. apply ms_le_equiv. tauto. }
    red. intros M N P. 

    rewrite !ms_le_equiv'.
    rewrite /ms_le_dm. intros (B1&L1&SUB1&->&DOM1) (B2&L2&SUB2&->&DOM2).

    exists (B2 ⊎ (B1 ∖ L2)), (L1 ⊎ (L2 ∖ B1)). repeat split.
    { mss. }
    { mss. }
    red. intros y [IN1 | IN2']%gmultiset_elem_of_disj_union.
    2: { specialize (DOM2 y ltac:(mss)) as (?&?&?). mss. }
    red in DOM1. specialize (DOM1 _ IN1) as (x & B1x & Ryx).
    destruct (decide (x ∈ L2)) as [L2x| ]; [| mss].
    specialize (DOM2 _ L2x) as (z & B2z & Rxz).
    exists z. split; [mss| ]. etrans; eauto.
  Qed.

  (* Lemma ms_le_minus (X Y D: gmultiset A) *)
  (*   (DOM': ms_le (X ⊎ D) (Y ⊎ D)): *)
  (*   ms_le X Y. *)
  (* Proof using PO. *)
  (*   apply ms_le_equiv' in DOM'. *)
  (*   destruct DOM' as (B1&L1&SUB1&EQ&DOM1).  *)
    
  

  Lemma empty_ms_le X: ms_le ∅ X.
  Proof using.
    red. intros ?. rewrite multiplicity_empty. lia.
  Qed.

  Lemma ms_le_empty X: ms_le X ∅ <-> X = ∅. 
  Proof using.
    clear PO. 
    destruct (decide (X = ∅)) as [->| NEQ].
    { split; [done| ]. intros. apply empty_ms_le. }
    split; [| done]. intros LE.
    apply gmultiset_choose in NEQ as [x IN].
    red in LE. setoid_rewrite multiplicity_empty in LE. 
    specialize (LE x ltac:(by apply elem_of_multiplicity)).
    destruct LE as (?&?&?). lia.
  Qed.

  (* TODO: move *)
  Lemma gmultiset_subseteq_empty (X: gmultiset A):
    X ⊆ ∅ <-> X = ∅.
  Proof using. clear. mss. Qed.  

  (* TODO: refactor! *)
  Global Instance ms_le_AntiSymm: AntiSymm eq ms_le.
  Proof using PO.
    red. intros X Y.

    intros LE1 LE2.
    set (same_muls a := multiplicity a X = multiplicity a Y). 
    destruct (decide (Forall same_muls (elements (X ⊎ Y)))).
    { apply gmultiset_eq. intros.
      destruct (decide (x ∈ X ⊎ Y)).
      - pattern x. eapply List.Forall_forall; eauto.
        apply elem_of_list_In, gmultiset_elem_of_elements. mss.
      - etrans; [| symmetry]; apply not_elem_of_multiplicity; mss. }

    apply not_Forall_Exists in n; [| solve_decision].
    apply List.Exists_exists in n as (a & IN & NEQ). red in NEQ.


    assert (exists (B: gmultiset A) (d: A),
               multiplicity d X ≠ multiplicity d Y /\
               B ⊆ mset_filter (not ∘ same_muls) (X ⊎ Y) /\
               forall b, b ∈ B -> strict R b d) as (B & d & NEQd & SUB & LTd).
    { exists ∅, a. repeat split; try mss. }
    clear dependent a.
    remember (size (mset_filter (not ∘ same_muls) (X ⊎ Y)) - size B) as n.
    generalize dependent B. generalize dependent d. induction n.
    { intros.
      symmetry in Heqn. apply Nat.sub_0_le in Heqn.
      pose proof SUB as SIZE%gmultiset_subseteq_size.
      apply gmultiset_disj_union_difference in SUB.
      rewrite SUB in Heqn, SIZE. rewrite gmultiset_size_disj_union in Heqn, SIZE.
      assert (size (mset_filter (not ∘ same_muls) (X ⊎ Y) ∖ B) = 0) by lia.
      apply gmultiset_size_empty_iff in H0.
      rewrite gmultiset_empty_no_elements in H0.

    assert (exists h, h ∈ X ⊎ Y /\ strict R d h /\ ¬ same_muls h) as (h1 & DOMh1 & Rdh1 & NEQh1).
    { apply not_eq in NEQd as [LT | LT]. 
      - specialize (LE2 _ LT) as (h&?&?). exists h. repeat split.
        + apply elem_of_multiplicity. rewrite multiplicity_disj_union. lia.
        + done.
        + intros ?.
          eapply partial_order_anti_symm in H1; eauto. specialize (H1 H3).
          subst. lia.
        + rewrite /same_muls. lia.
      - specialize (LE1 _ LT) as (h&?&?). exists h. repeat split.
        + apply elem_of_multiplicity. rewrite multiplicity_disj_union. lia.
        + done.
        + intros ?.
          eapply partial_order_anti_symm in H1; eauto. specialize (H1 H3).
          subst. lia.
        + rewrite /same_muls. lia. }

    assert (h1 ∈ mset_filter (not ∘ same_muls) (X ⊎ Y)) as IN1.
    { by apply mset_filter_spec. }
    apply gmultiset_disj_union_difference' in IN1.

    assert (h1 ∉ B) as NINh1.
    { intros INh. specialize (LTd _ INh).
      rewrite strict_spec in LTd. apply proj2 in LTd.
      destruct LTd. apply Rdh1. }

    destruct (H0 h1).
    mss. }
    
    intros. 

    assert (exists h, h ∈ X ⊎ Y /\ strict R d h /\ ¬ same_muls h) as (h1 & DOMh1 & Rdh1 & NEQh1).
    { apply not_eq in NEQd as [LT | LT]. 
      - specialize (LE2 _ LT) as (h&?&?). exists h. repeat split.
        + apply elem_of_multiplicity. rewrite multiplicity_disj_union. lia.
        + done.
        + intros ?.
          eapply partial_order_anti_symm in H0; eauto. specialize (H0 H2).
          subst. lia.
        + rewrite /same_muls. lia.
      - specialize (LE1 _ LT) as (h&?&?). exists h. repeat split.
        + apply elem_of_multiplicity. rewrite multiplicity_disj_union. lia.
        + done.
        + intros ?.
          eapply partial_order_anti_symm in H0; eauto. specialize (H0 H2).
          subst. lia.
        + rewrite /same_muls. lia. }
    assert (exists h2, h2 ∈ X ⊎ Y /\ strict R h1 h2 /\ ¬ same_muls h2) as (h2 & DOMh2 & Rh12 & NEQh2).
    { apply not_eq in NEQh1 as [LT | LT]. 
      - specialize (LE2 _ LT) as (h&?&?). exists h. repeat split.
        + apply elem_of_multiplicity. rewrite multiplicity_disj_union. lia.
        + done.
        + intros ?.
          eapply partial_order_anti_symm in H0; eauto. specialize (H0 H2).
          subst. lia.
        + rewrite /same_muls. lia.
      - specialize (LE1 _ LT) as (h&?&?). exists h. repeat split.
        + apply elem_of_multiplicity. rewrite multiplicity_disj_union. lia.
        + done.
        + intros ?.
          eapply partial_order_anti_symm in H0; eauto. specialize (H0 H2).
          subst. lia.
        + rewrite /same_muls. lia. }

    assert (h1 ∈ mset_filter (not ∘ same_muls) (X ⊎ Y)) as IN1.
    { by apply mset_filter_spec. }
    apply gmultiset_disj_union_difference' in IN1.

    assert (h1 ∉ B) as NINh1.
    { intros INh. specialize (LTd _ INh).
      rewrite strict_spec in LTd. apply proj2 in LTd.
      destruct LTd. apply Rdh1. }
    
    assert (h2 ∈ mset_filter (not ∘ same_muls) (X ⊎ Y)) as IN2.
    { by apply mset_filter_spec. }
    (* apply gmultiset_disj_union_difference' in IN2. *)

    assert (h2 ∉ B) as NINh2.
    { intros INh. specialize (LTd _ INh).
      rewrite strict_spec in LTd. apply proj2 in LTd.
      destruct LTd. trans h1; [apply Rdh1 | apply Rh12]. }
    
    specialize (IHn h2 ltac:(done) (B ⊎ {[+ h1 +]})). specialize_full IHn.
    { rewrite IN1. mss. }
    { intros ?. rewrite gmultiset_elem_of_disj_union gmultiset_elem_of_singleton.
      intros [IN | ->]; try done.
      trans d.
      { by apply LTd. }
      trans h1; [apply Rdh1 | apply Rh12]. }
    { rewrite IN1. rewrite !gmultiset_size_disj_union !gmultiset_size_singleton.
      rewrite IN1 in Heqn. rewrite !gmultiset_size_disj_union !gmultiset_size_singleton in Heqn. lia. }
    done. 
  Qed.

  Lemma no_ms_lt_empty X: ¬ ms_lt X ∅. 
  Proof using PO.
    intros [LE NE]%strict_spec_alt. apply ms_le_empty in LE. done.
  Qed. 

  (* TODO: generalize, move *)
  Lemma multiset_difference_empty (X: gmultiset A):
    X ∖ ∅ = X. 
  Proof using. clear R PO. mss. Qed. 

  Lemma ms_le_sub X Y (SUB: X ⊆ Y):
    ms_le X Y. 
  Proof using.
    clear PO. 
    red. mss. 
  Qed.

  Lemma ms_le_diff X Y:
    ms_le (X ∖ Y) X.
  Proof using.
    red. intros ?. rewrite multiplicity_difference. lia.
  Qed.

  Lemma ms_le_disj_union X1 Y1 X2 Y2
    (LE1: ms_le X1 Y1) (LE2: ms_le X2 Y2):
    ms_le (X1 ⊎ X2) (Y1 ⊎ Y2).
  Proof using PO.
    apply ms_le_equiv'. apply ms_le_equiv' in LE1, LE2. red in LE1, LE2.
    destruct LE1 as (B1 & S1 & IN1 & -> & LT1), LE2 as (B2 & S2 & IN2 & -> & LT2).
    red. exists (B1 ⊎ B2), (S1 ⊎ S2). repeat split.
    - mss.
    - mss.
    - intros ? [I1 | I2]%gmultiset_elem_of_disj_union.
      + destruct (LT1 _ I1) as (b1 & INB1 & R1). mss.
      + destruct (LT2 _ I2) as (b2 & INB2 & R2). mss.
  Qed.

  Lemma ms_le_lt_disj_union X1 Y1 X2 Y2
    (LE1: ms_lt X1 Y1) (LE2: ms_le X2 Y2):
    ms_lt (X1 ⊎ X2) (Y1 ⊎ Y2).
  Proof using PO.
    eapply strict_transitive_r.
    { eapply ms_le_disj_union; [reflexivity| ]. eauto. }
    apply strict_spec_alt. split. 
    { apply ms_le_disj_union; try done. apply LE1. }
    intros ?. apply strict_spec_alt in LE1. destruct LE1 as [LE NEQ].
    destruct NEQ. mss.
  Qed. 
  
  Global Instance ms_le_Proper:
     Proper (equiv ==> equiv ==> iff) ms_le.
  Proof using. clear PO. red. intros ??????. mss. Qed. 

  Global Instance ms_lt_Proper:
     Proper (equiv ==> equiv ==> iff) ms_lt.
  Proof using. clear PO. red. intros ??????. mss. Qed. 

  Lemma big_opS_ms_le `{Countable B} f g (X: gset B)
    (LE: forall x, ms_le (f x) (g x)):
    ms_le ([^op set] x ∈ X, f x) ([^op set] x ∈ X, g x).
  Proof using PO.
    pattern X. apply set_ind_L; clear X.
    { rewrite !big_opS_empty. apply empty_ms_le. }
    intros. rewrite !big_opS_insert; auto. simpl. rewrite !gmultiset_op.
    apply ms_le_disj_union; eauto.
  Qed. 

  Lemma ms_le_exchange X u v n 
    (INu: u ∈ X)
    (LTuv: strict R v u):
    ms_le (X ∖ {[+ u +]} ⊎ n *: {[+ v +]}) X.
  Proof using PO.
    apply gmultiset_disj_union_difference' in INu.
    remember (X ∖ {[+ u +]}) as V.
    rewrite gmultiset_disj_union_comm in INu. 
    rewrite INu. clear INu HeqV X.
    eapply ms_le_disj_union; [reflexivity| ..].
    red. intros ?. rewrite multiplicity_scalar_mul !multiplicity_singleton'.
    destruct (decide (a = v)) as [->|?]; [| lia].
    intros. eexists. split; [apply LTuv| ].
    rewrite multiplicity_scalar_mul !multiplicity_singleton'.
    rewrite decide_False.
    2: { intros ->. apply LTuv. done. }
    rewrite decide_True; [lia| done].
  Qed.  

End MultisetOrder.


Section MultisetDefs.
  Context `{Countable A}.

  Section MultisetMap.
    Context `{Countable B}. 
    Context (f: A -> B). 

    Definition mset_map (g: gmultiset A): gmultiset B :=
      list_to_set_disj $ fmap f $ elements g.

    Lemma elem_of_mset_map (g: gmultiset A):
      forall b, b ∈ mset_map g <-> exists a, f a = b /\ a ∈ g.
    Proof using.
      intros. rewrite /mset_map.
      rewrite elem_of_list_to_set_disj.
      rewrite elem_of_list_fmap.
      apply exist_proper. intros ?. apply ZifyClasses.and_morph; [done| ].
      apply gmultiset_elem_of_elements.
    Qed. 
  
    Lemma mset_map_empty:
      mset_map ∅ = ∅. 
    Proof using. mss. Qed. 
  
    Lemma mset_map_disj_union (X Y: gmultiset A):
      mset_map (X ⊎ Y) = mset_map X ⊎ mset_map Y.
    Proof using.
      apply gmultiset_eq. intros.
      rewrite /mset_map. rewrite -list_to_set_disj_app -fmap_app.       
      f_equal. apply list_to_set_disj_perm. f_equiv. 
      apply gmultiset_elements_disj_union.
    Qed.

    Lemma mset_map_sub (X Y: gmultiset A)
      (SUB: X ⊆ Y):
      mset_map X ⊆ mset_map Y.
    Proof using.
      apply gmultiset_disj_union_difference in SUB. rewrite SUB.
      rewrite mset_map_disj_union. mss.
    Qed. 

    Lemma mset_map_sub_diff (X Y: gmultiset A)
      (SUB: Y ⊆ X):
      mset_map (X ∖ Y) = mset_map X ∖ mset_map Y.
    Proof using.
      apply gmultiset_disj_union_difference in SUB.
      rewrite SUB. remember (X ∖ Y) as V. clear HeqV SUB.
      rewrite mset_map_disj_union. 
      rewrite !gmultiset_cancel_l2. mss. 
    Qed. 
      
    Lemma mset_map_singleton (x: A):
      mset_map {[+ x +]} = {[+ f x +]}.
    Proof using.
      rewrite /mset_map. rewrite gmultiset_elements_singleton.
      rewrite list_fmap_singleton. mss.
    Qed. 

    Lemma mset_map_mul (X: gmultiset A) (n: nat):
      mset_map (n *: X) = n *: (mset_map X). 
    Proof using.
      induction n.
      { rewrite !gmultiset_scalar_mul_0. mss. }
      rewrite !gmultiset_scalar_mul_S_r. rewrite mset_map_disj_union. 
      by rewrite IHn.
    Qed. 

  End MultisetMap.


  Lemma mset_filter_disj_union_disj (P Q: A -> Prop) g
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
    (DISJ: forall a, ¬ (P a /\ Q a)):
    mset_filter (fun a => P a \/ Q a) g = mset_filter P g ⊎ mset_filter Q g.
  Proof using.
    apply gmultiset_eq. intros a.
    rewrite multiplicity_disj_union !mset_filter_multiplicity.
    destruct (decide (P a)), (decide (Q a)).
    - edestruct DISJ; eauto.
    - rewrite decide_True; [done| ]. tauto.  
    - rewrite decide_True; [done| ]. tauto.
    - rewrite decide_False; [done| ]. tauto.
  Qed.

  Lemma mset_filter_equiv (P Q: A -> Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
    (EQUIV: ∀ x, P x ↔ Q x):
    forall g, mset_filter P g = mset_filter Q g.
  Proof using.
    intros. rewrite /mset_filter. erewrite list_filter_iff; eauto.
  Qed. 

  Lemma mset_filter_subseteq_mono_strong (P Q: A -> Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
    (g: gmultiset A)
    (IMPL: ∀ x, x ∈ g -> P x -> Q x):
    mset_filter P g ⊆ mset_filter Q g.
  Proof using.
    intros. red. red. intros x. 
    destruct (decide (x ∈ g)).
    2: { trans 0; [| lia].
         edestruct Nat.le_gt_cases as [LE | LT]; [apply LE| ].
         destruct n. apply elem_of_multiplicity.
         rewrite mset_filter_multiplicity in LT.
         destruct (decide (P x)); [done| lia]. }  
         
    rewrite !mset_filter_multiplicity.
    destruct (decide (P x)); [| lia].
    rewrite decide_True; [lia| ].
    by apply IMPL. 
  Qed. 

End MultisetDefs.
