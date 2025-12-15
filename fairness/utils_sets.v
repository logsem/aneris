From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From fairness Require Export utils_logic utils_maps.
From iris.algebra Require Import gset.

Section SetMapProperties.
  
  Lemma set_map_compose_gset {A1 A2 A3: Type}
    `{EqDecision A1} `{EqDecision A2} `{EqDecision A3}
    `{Countable A1} `{Countable A2} `{Countable A3}
    (f: A2 -> A3) (g: A1 -> A2) (m: gset A1):
    set_map (f ∘ g) m (D:=gset _) = set_map f (set_map g m (D:= gset _)).
  Proof using.
    set_solver. 
  Qed. 
  
  Lemma elem_of_map_inj_gset {A B} 
    `{EqDecision A} `{Countable A}
    `{EqDecision B} `{Countable B}
    (f: A -> B) (m: gset A) (a: A) (INJ: Inj eq eq f):
    a ∈ m <-> f a ∈ set_map f m (D := gset _).
  Proof using.
    split; [apply elem_of_map_2| ].
    intros IN. apply elem_of_map_1 in IN as (a' & EQ & IN).
    apply INJ in EQ. congruence. 
  Qed.
    
End SetMapProperties.



Section Powerset.
  Context {K: Type}.
  Context `{Countable K}. 
  
  (** it's easier to perform recursion on lists *)

  Fixpoint powerlist (l: list K): gset (gset K) :=
    match l with
    | [] => {[ ∅ ]}
    | k :: l' => let p' := powerlist l' in
                 p' ∪ (set_map (fun s => {[ k ]} ∪ s) p')
    end. 
  
  Definition powerset (s: gset K): gset (gset K) :=
    powerlist (elements s).
    
  Lemma powerlist_nil l:
    ∅ ∈ powerlist l.
  Proof. induction l; set_solver. Qed.

  Instance powerlist_perm_Proper:
    Proper (Permutation ==> eq) powerlist.
  Proof.
    induction 1; csimpl; auto; cycle -1.
    1, 2: congruence. 
    rewrite -!union_assoc_L. f_equal. 
    rewrite !set_map_union_L.
    rewrite !union_assoc_L. f_equal.
    { set_solver. }
    rewrite -!set_map_compose_gset. apply leibniz_equiv.
    f_equiv. red. simpl. set_solver.
  Qed.

  Lemma powerset_spec s:
    forall e, e ⊆ s <-> e ∈ powerset s. 
  Proof. 
    intros. rewrite /powerset.
    revert e. pattern s. apply set_ind.
    { intros ?? EQUIV. apply leibniz_equiv_iff in EQUIV. by rewrite EQUIV. }
    { rewrite elements_empty. simpl.
      setoid_rewrite elem_of_singleton.
      intros. set_solver. }
    clear s. intros k s NIN IND e.
    rewrite elements_disj_union; [| set_solver].
    rewrite elements_singleton. simpl.
    rewrite !elem_of_union elem_of_map.
    repeat setoid_rewrite <- IND.
    erewrite ex_det_iff with (a := e ∖ {[ k ]}).
    2: { set_solver. }
    destruct (decide (k ∈ e)); set_solver. 
  Qed.              
          
End Powerset.


Lemma set_filter_equiv:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (P_EQ: forall x, P1 x <-> P2 x)
    (c1 c2: C)
    (EQUIV: c1 ≡ c2),
    filter P1 c1 = filter P2 c2.
Proof. set_solver. Qed.

Lemma set_filter_and:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (c: C),
    filter P1 (filter P2 c) = filter (fun x => P1 x /\ P2 x) c.
Proof. set_solver. Qed. 

Lemma set_filter_comm:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A}
    {LL: LeibnizEquiv C}
    {FS: FinSet A C}
    (P1 P2 : A → Prop)
    (DEC1: ∀ x : A, Decision (P1 x)) (DEC2: ∀ x : A, Decision (P2 x))
    (c: C),
    filter P1 (filter P2 c) = filter P2 (filter P1 c). 
Proof. set_solver. Qed. 

Lemma filter_singleton_if:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} 
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C
    → ∀ (P : A → Prop) {H7 : ∀ x : A, Decision (P x)} (x : A),
        filter P ({[x]} : C) ≡ if decide (P x) then {[x]} else ∅.
Proof. intros. destruct decide; set_solver. Qed. 

Lemma elements_list_to_set_disj `{Countable A} (l: list A):
  elements $ (list_to_set_disj l: gmultiset A) ≡ₚ l.
Proof using.
  clear. induction l.
  { done. }
  simpl. rewrite gmultiset_elements_disj_union.
  simpl. rewrite gmultiset_elements_singleton.
  rewrite IHl. done.
Qed. 

Lemma gset_filter_subseteq_mono_strong `{Countable A} (P Q: A -> Prop)
  `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
  (g: gset A)
  (IMPL: ∀ x, x ∈ g -> P x -> Q x):
  filter P g ⊆ filter Q g.
Proof using. clear -IMPL. set_solver. Qed. 

Lemma gset_filter_True `{Countable K} (g: gset K)
  (P: K -> Prop)
  `{∀ x, Decision (P x)}
  (TRUE: forall k, k ∈ g -> P k):
  filter P g = g.
Proof using. clear -TRUE. set_solver. Qed. 

Lemma GSet_inj_equiv:
  ∀ `{Countable K}, Inj equiv equiv (@GSet K _ _).
Proof using. solve_proper. Qed.

Lemma GSet_Proper: 
  ∀ `{Countable K}, Proper (equiv ==> equiv) (@GSet K _ _).
Proof using. solve_proper. Qed.

Lemma gset_not_elem_of_equiv_not_empty_L:
  ∀ {A : Type} `{Countable A},
  ∀ (X : gset A), X ≠ ∅ ↔ (exists x : A, x ∈ X).
Proof.
  intros. split.
  - by apply set_choose_L.
  - set_solver. 
Qed. 

Lemma length_size `{Countable K} (g: gset K):
  length (elements g) = size g.
Proof.
  rewrite -{2}(list_to_set_elements_L g).
  rewrite size_list_to_set; [done| ]. apply NoDup_elements.
Qed.


Section FlattenGset.
  Context `{Countable K}. 
  
  (* TODO: find existing? *)
  Definition flatten_gset (ss: gset (gset K)): gset K :=
    list_to_set (concat (map elements (elements ss))).

  Lemma flatten_gset_spec (ss: gset (gset K)):
    forall k, k ∈ flatten_gset ss <-> exists s, s ∈ ss /\ k ∈ s.
  Proof.
    intros. rewrite /flatten_gset.
    rewrite elem_of_list_to_set.
    rewrite elem_of_list_In in_concat.
    setoid_rewrite in_map_iff. 
    repeat setoid_rewrite <- elem_of_list_In.
    split.
    - intros (?&(l&<-&?)&?). exists l. set_solver.
    - intros (s&?&?). exists (elements s). set_solver. 
  Qed. 
    
  Lemma flatten_gset_disjoint (ss: gset (gset K)) s':
    flatten_gset ss ## s' <-> forall s, s ∈ ss -> s ## s'.
  Proof.
    repeat setoid_rewrite elem_of_disjoint. setoid_rewrite flatten_gset_spec.
    set_solver.
  Qed.

  Lemma flatten_gset_union (S1 S2: gset (gset K)):
    flatten_gset (S1 ∪ S2) = flatten_gset S1 ∪ flatten_gset S2.
  Proof.
    rewrite /flatten_gset. set_solver.
  Qed. 

  Lemma flatten_gset_singleton (S: gset K):
    flatten_gset {[ S ]} = S. 
  Proof.
    rewrite /flatten_gset. rewrite elements_singleton. set_solver. 
  Qed. 

  Lemma flatten_gset_empty: flatten_gset ∅ = (∅: gset K).
  Proof using. set_solver. Qed. 
 
End FlattenGset.

Section GsetPick.
  Context `{Countable K}.

  Definition gset_pick  (g: gset K) :=
    let l := elements g in
    match l with 
    | [] => None
    | e :: _ => Some e
    end.   
  
  Lemma gset_pick_None (g: gset K):
    gset_pick g = None <-> g = ∅.
  Proof.
    rewrite /gset_pick. destruct (elements g) eqn:E.
    - apply elements_empty_inv in E. apply leibniz_equiv_iff in E. done.
    - split; [done| ]. intros ->. simpl in E. set_solver.
  Qed. 
  
  Lemma gset_pick_is_Some (g: gset K):
    is_Some (gset_pick g) <-> g ≠ ∅.
  Proof.
    rewrite -not_eq_None_Some. apply not_iff_compat, gset_pick_None. 
  Qed. 
  
  Lemma gset_pick_Some (g: gset K) k:
    gset_pick g = Some k -> k ∈ g. 
  Proof.
    rewrite /gset_pick. destruct elements eqn:E; [done| ].
    intros [=->]. apply elem_of_elements. rewrite E. constructor. 
  Qed.   
  
  Lemma gset_pick_singleton (k: K):
    gset_pick {[ k ]} = Some k.
  Proof.
    rewrite /gset_pick. rewrite elements_singleton. done.
  Qed. 

  Lemma flatten_gset_map_img_gtg_empty `{Countable K'} (ts: gset K'):
    flatten_gset $ map_img $ gset_to_gmap ∅ ts = (∅: gset K).
  Proof using.
    clear. 
    pattern ts. apply set_ind; clear ts.
    { red. intros ????. set_solver. }
    { done. }
    intros. rewrite gset_to_gmap_union_singleton.
    rewrite map_img_insert_L. rewrite delete_notin.
    2: { by apply lookup_gset_to_gmap_None. }
    rewrite flatten_gset_union flatten_gset_singleton. set_solver.
  Qed.

End GsetPick.


Section ExtractSomes.
  Context {A: Type}.

  Definition extract_Somes (l: list (option A)): list A :=
    flat_map (from_option (fun a => [a]) []) l.

  Lemma extract_Somes_spec (l: list (option A)):
    forall a, In (Some a) l <-> In a (extract_Somes l).
  Proof. 
    intros. rewrite /extract_Somes.
    rewrite in_flat_map_Exists.
    rewrite List.Exists_exists. simpl.
    erewrite ex_det_iff with (a := Some a). 
    2: { intros ? [? ?]. destruct a'; try done.
         simpl in H0. set_solver. }
    simpl. set_solver.
  Qed.

  Context `{Countable A}. 

  Definition extract_Somes_gset (s: gset (option A)): gset A :=
    list_to_set ∘ extract_Somes ∘ elements $ s. 
  
  Lemma extract_Somes_gset_spec (s: gset (option A)):
    forall a, Some a ∈ s <-> a ∈ (extract_Somes_gset s).
  Proof. 
    intros. rewrite /extract_Somes_gset.
    rewrite elem_of_list_to_set. 
    rewrite elem_of_list_In. rewrite -extract_Somes_spec.
    rewrite -elem_of_list_In. rewrite elem_of_elements.
    done. 
  Qed.

  Lemma extract_Somes_gset_inv (s: gset (option A)):
    set_map Some (extract_Somes_gset s) = s ∖ {[ None ]}.
  Proof. 
    apply set_eq. intros ?. rewrite elem_of_map.
    setoid_rewrite <- extract_Somes_gset_spec.
    rewrite elem_of_difference not_elem_of_singleton.
    split; [intros (?&->&?) | intros [??]]. 
    - set_solver.
    - destruct x; eauto. done.
  Qed. 

  Lemma extract_Somes_gset_singleton (ok: option A):
    extract_Somes_gset {[ ok ]} = match ok with | Some k => {[ k ]} | None => ∅ end.
  Proof using.
    destruct ok; try set_solver.
    apply set_eq. intros ?. rewrite <- extract_Somes_gset_spec.
    set_solver.
  Qed.

End ExtractSomes.


Lemma gset_to_gmap_singleton `{Countable K} {B: Type} (b: B) (k: K):
  gset_to_gmap b {[ k ]} = {[ k := b ]}.
Proof.
  rewrite /gset_to_gmap. simpl. rewrite map_fmap_singleton. done.
Qed. 

Lemma set_Forall_subseteq {A C : Type} `{ElemOf A C}
  (P: A → Prop) (x y: C)
  (SUB: y ⊆ x):
  set_Forall P x -> set_Forall P y.
Proof using. clear -SUB. set_solver. Qed.      


Section SetMax.

  Definition set_max (X: gset nat): nat :=
    list_max $ elements $ X.

  Lemma set_max_spec X n:
    set_max X ≤ n ↔ set_Forall (λ k, k ≤ n) X.
  Proof using.
    rewrite /set_max. rewrite list_max_le.
    by rewrite set_Forall_elements.
  Qed.

  (* TODO: does it exist already? *)
  Lemma list_max_elems X:
    forall x, x ∈ X -> x <= list_max X.
  Proof using.
    induction X.
    { set_solver. }
    intros x. rewrite elem_of_cons. intros [->|?]; simpl. 
    - lia.
    - etrans; [| apply Nat.le_max_r]. eauto.
  Qed.

  Lemma set_max_elems X:
    forall x, x ∈ X -> x <= set_max X.
  Proof using.
    intros x IN. rewrite /set_max.
    apply list_max_elems. by apply elem_of_elements.
  Qed.

  Lemma set_max_singleton x:
    set_max {[ x ]} = x.
  Proof using.
    rewrite /set_max. rewrite elements_singleton. simpl. lia.
  Qed.   

End SetMax.


Lemma set_seq_uniq2 s l1 l2:
  (set_seq s l1: gset nat) = set_seq s l2 <-> l1 = l2.
Proof using.
  split; [| congruence]. 
  intros EQ. rewrite set_eq in EQ.
  repeat setoid_rewrite elem_of_set_seq in EQ.
  destruct (Nat.lt_trichotomy l1 l2) as [LT | [? | LT]]; try done.
  - specialize (EQ (s + l1)). lia.
  - specialize (EQ (s + l2)). lia.
Qed.
