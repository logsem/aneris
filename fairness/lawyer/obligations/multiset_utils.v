From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
(* From stdpp Require Import relations. *)

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

End GmultisetUtils.

Section MultisetOrder.
  Context `{Countable A}.
  Context (R: relation A).
  Context (PO: PartialOrder R).   

  (* reflexive version of Huet and Oppen definition *)
  Definition ms_le (X Y: gmultiset A) :=
    forall a, multiplicity a X > multiplicity a Y ->
    exists b, R a b /\ multiplicity b X < multiplicity b Y.

  Definition ms_lt := strict ms_le. 
  
  (* original Huet and Oppen definition *)
  Definition ms_lt' (X Y: gmultiset A) :=
    forall a, multiplicity a X > multiplicity a Y ->
    exists b, strict R a b /\ multiplicity b X < multiplicity b Y.

  Definition ms_le_dm (M N: gmultiset A) :=
    exists X Y, X ⊆ N /\ M = (N ∖ X) ⊎ Y /\ (forall y, y ∈ Y -> exists x, x ∈ X /\ strict R y x). 

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

  Lemma empty_ms_le X: ms_le ∅ X.
  Proof using.
    red. intros ?. rewrite multiplicity_empty. lia.
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

  (* TODO: should be a part of PartialOrder proof *)
  Lemma ms_le_refl X:
    ms_le X X.
  Proof using.
  Admitted. 
    

  Lemma ms_le_diff X Y:
    ms_le (X ∖ Y) X.
  Proof using.
    red. intros ?. rewrite multiplicity_difference. lia.
  Qed.

  Notation "'mlt' x X" := (multiplicity x X) (at level 20).
  (* Context `{∀ x y, Decision (R x y)}.  *)

  Lemma ms_le_equiv'    
    X Y:
    ms_le X Y <-> ms_le_dm X Y.
  Proof using.
  (*   rewrite /ms_le /ms_le_dm. split. *)
  (*   - rename X into M, Y into N. *)
  (*     (* intros LE. *) *)
  (*     (* set (M__max :=  *) *)
  (*     destruct (decide (M = ∅)) as [-> | NE]. *)
  (*     { intros. exists N, ∅. mss. }  *)
      
  (*     assert (exists m, m ∈ M /\ maximal R m M). *)
  (*     { enough (exists m, m ∈ (dom M) /\ maximal R m (dom M)). *)
  (*       2: { unshelve eapply minimal_exists_L; try by apply _. *)
  (*            intros E. destruct NE. admit. } *)
  (*       destruct H1 as (m & DOM & MAX). *)
  (*       exists m. split. *)
  (*       { eapply gmultiset_elem_of_dom; eauto. } *)
  (*       red. red. simpl. intros. apply MAX; eauto. *)
  (*       eapply gmultiset_elem_of_dom; eauto. } *)

  (*     destruct H1 as (m & Mm & MAXm).  *)
  (*     intros LE.       *)

      
  (*     exists ((mset_filter (fun a => R m a) N) ∖ M), ((mset_filter (fun a => ¬ R m a) M) ∖ N). *)
  (*     repeat split. *)
  (*     + admit. *)
  (*     + apply gmultiset_eq. intros a. *)
  (*       destruct (decide (R m a)). *)
  (*       * rewrite multiplicity_disj_union. *)
          
      
             
  (*            apply gmultiset_eq. intros. rewrite multiplicity_empty. *)
  (*            destruct (multiplicity x M) eqn:FF; [done| ]. *)
             
  (*            intros ?%dom_empty_L.  *)
  (*       - apply _.  *)

      
  (*     generalize dependent N. pattern M. apply gmultiset_ind. *)
  (*     { intros. exists N, ∅. mss. } *)
  (*     clear M. intros m M IH N' LE. *)

  (*     assert (exists n, n ∈ N' /\ R m n) as (n & N'n & Rmn). *)
  (*     { admit. } *)

  (*     pose proof (gmultiset_disj_union_difference' _ _ N'n) as EQ. *)
  (*     rewrite EQ. rewrite EQ in LE.  *)
  (*     remember (N' ∖ {[+ n +]}) as N. clear HeqN. clear N' N'n EQ. *)

  (*     setoid_rewrite multiplicity_disj_union in LE. *)
  (*     setoid_rewrite multiplicity_singleton' in LE.  *)

      
      
  (*     specialize (IH N). destruct IH. *)
  (*     { intros. *)
  (*       specialize (LE a). *)
        
  (*       destruct (decide (a = n)). *)
  (*       { subst. *)
  (*         rewrite decide_False in LE; [| admit]. *)
  (*         simpl in LE.  *)
        
  (*       destruct (decide (a = n)). *)
  (*       { specialize (LE term+) *)

  (*         subst. *)

  (*         lia.  *)
      
      
  (*     destruct (decide (m ∈ N)). *)
  (*     2: { specialize (IH N). destruct IH. *)
  (*          { intros. specialize (LE a). destruct LE as (b & ab & LT).  *)
  (*            { rewrite multiplicity_disj_union. lia. } *)
  (*            rewrite multiplicity_disj_union in LT. *)
  (*            rewrite multiplicity_singleton' in LT.  *)
  (*            eexists. split; eauto.  *)
             
      
  (*     specialize (IH (N ∖ {[+ m +]})). *)
  (*     destruct IH.  *)
  (*     { intros a GT.  *)
  (*       destruct (decide *)
  (*     intros LE.  *)
  Admitted.

  Lemma ms_le_disj_union X1 Y1 X2 Y2
    (LE1: ms_le X1 Y1) (LE2: ms_le X2 Y2):
    ms_le (X1 ⊎ X2) (Y1 ⊎ Y2).
  Proof using.
    clear PO. 
    apply ms_le_equiv'. apply ms_le_equiv' in LE1, LE2. red in LE1, LE2.
    destruct LE1 as (B1 & S1 & IN1 & -> & LT1), LE2 as (B2 & S2 & IN2 & -> & LT2).
    red. exists (B1 ⊎ B2), (S1 ⊎ S2). repeat split.
    - mss.
    - mss.
    - intros ? [I1 | I2]%gmultiset_elem_of_disj_union.
      + destruct (LT1 _ I1) as (b1 & INB1 & R1). mss.
      + destruct (LT2 _ I2) as (b2 & INB2 & R2). mss.
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
  Proof using.
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
    eapply ms_le_disj_union; [apply ms_le_refl| ..].
    red. intros ?. rewrite multiplicity_scalar_mul !multiplicity_singleton'.
    destruct (decide (a = v)) as [->|?]; [| lia].
    intros. eexists. split; [apply LTuv| ].
    rewrite multiplicity_scalar_mul !multiplicity_singleton'.
    rewrite decide_False.
    2: { intros ->. apply LTuv. done. }
    rewrite decide_True; [lia| done].
  Qed.  
      
  Global Instance ms_le_PreOrder: PreOrder ms_le.
  Proof using. Admitted.

  Global Instance ms_le_AntiSymm: AntiSymm eq ms_le.
  Proof using.
    red. intros ?? LE1 LE2.
    red in LE1, LE2. apply gmultiset_eq. intros a.
    (* TODO: consider the maximal element with differing multiplicity *)
    (* destruct (Nat.lt_trichotomy (multiplicity a x) (multiplicity a y)) as [?|[?|?]]; eauto. *)
    (* - specialize (LE2 _ H0). *)
  Admitted.

  Goal PartialOrder ms_le.
    esplit; apply _.
  Defined. 

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

    Lemma mset_filter_False g
      (FALSE: forall a, a ∈ g -> ¬ P a):
      mset_filter g = ∅.
    Proof using.
      destruct (decide (mset_filter g = ∅)) as [| NE]; [done| ]. 
      apply gmultiset_choose in NE as [? IN].
      apply mset_filter_spec in IN as [??]. set_solver.
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

  End MultisetFilter.
  
End MultisetDefs.
