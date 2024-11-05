From iris.algebra Require Import gmap gset.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Import quantifiers finitary.
(* From stdpp Require Import finitary. *)

(* TODO: move these lemmas to appropriate places *)

Section gmap.
  Context `{!EqDecision K, !Countable K}.

  Definition max_gmap (m: gmap K nat) : nat :=
    map_fold (λ k v r, v `max` r) 0 m.

  Lemma max_gmap_spec m:
    map_Forall (λ _ v, v <= max_gmap m) m.
  Proof.
    induction m using map_ind; first done.
    apply map_Forall_insert =>//. rewrite /max_gmap map_fold_insert //.
    - split; first lia. intros ?? Hnotin. specialize (IHm _ _ Hnotin). simpl in IHm.
      unfold max_gmap in IHm. lia.
    - intros **. lia.
  Qed.

  Lemma gmap_disj_op_union:
    ∀ {A : cmra} (m1 m2 : gmap K A),
      map_disjoint m1 m2 -> m1 ⋅ m2 = m1 ∪ m2. 
  Proof using. 
    intros. apply map_eq. intros.
    rewrite lookup_op lookup_union.
    destruct (m1 !! i) eqn:L1, (m2 !! i) eqn:L2; try done.
    eapply map_disjoint_spec in H; done.
  Qed.

End gmap.

(* TODO: upstream*)
Lemma map_img_insert_L :
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} 
    {H1 : ∀ A : Type, Empty (M A)} {H2 : ∀ A : Type, PartialAlter K A (M A)} 
    {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, FinMapToList K A (M A)} 
    {EqDecision0 : EqDecision K}
  ,
    FinMap K M
    → ∀ {A SA : Type} {H7 : ElemOf A SA} {H8 : Empty SA} 
        {H9 : Singleton A SA} {H10 : Union SA} {H11 : Intersection SA} 
        {H12 : Difference SA}
        {LE: LeibnizEquiv SA}
    ,
      Set_ A SA
      → ∀ (m : M A) (i : K) (x : A),
        map_img (<[i:=x]> m) = ({[x]}: SA) ∪ map_img (delete i m).
Proof.
  intros. apply leibniz_equiv. apply map_img_insert. 
Qed.  


Section Disjoint.

  Lemma disjoint_subseteq:
    ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C}
      {H2 : Union C} {H3 : Intersection C} {H4 : Difference C},
      `{Set_ A C} → ∀ X1 X2 Y1 Y2: C, X1 ⊆ Y1 -> X2 ⊆ Y2 → Y1 ## Y2 -> X1 ## X2.
  Proof. intros. set_solver. Qed.

End Disjoint.

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
    (f: A -> B) (m: gset A) (a: A) (INJ: injective f):
    a ∈ m <-> f a ∈ set_map f m (D := gset _).
  Proof using.
    split; [apply elem_of_map_2| ].
    intros IN. apply elem_of_map_1 in IN as (a' & EQ & IN).
    apply INJ in EQ. congruence. 
  Qed.
    
End SetMapProperties.


(* TODO: find existing? *)
Section LogicHelpers.

  Lemma ex2_comm {A B: Type} (P: A -> B -> Prop):
    (exists (a: A) (b: B), P a b) <-> (exists (b: B) (a: A), P a b).
  Proof. 
    split; intros (?&?&?); eauto. 
  Qed. 

  Lemma iff_and_impl_helper {A B: Prop} (AB: A -> B):
    A /\ B <-> A.
  Proof. tauto. Qed.     

  Lemma iff_True_helper {A: Prop}:
    (A <-> True) <-> A.
  Proof. tauto. Qed.     

  Lemma iff_False_helper {A: Prop}:
    (A <-> False) <-> ¬ A.
  Proof. tauto. Qed.

  Lemma ex_and_comm {T: Type} (A: Prop) (B: T -> Prop):
    (exists t, A /\ B t) <-> A /\ exists t, B t.
  Proof. split; intros (?&?&?); eauto. Qed.

  Lemma ex_prod {A B: Type} (P: A * B -> Prop):
    (exists ab, P ab) <-> (exists a b, P (a, b)).
  Proof.
    split.
    - intros [[??] ?]. eauto.
    - intros (?&?&?). eauto.
  Qed. 

  Lemma ex_prod' {A B: Type} (P: A -> B -> Prop):
    (exists a b, P a b) <-> (exists ab, P ab.1 ab.2).
  Proof.
    split.
    - intros (?&?&?). eexists (_, _). eauto.
    - intros [[??] ?]. eauto.
  Qed.

  Lemma ex_proper3 {A B C: Prop} (P Q: A -> B -> C -> Prop)
    (EQUIV: forall a b c, P a b c <-> Q a b c):
    (exists a b c, P a b c) <-> (exists a b c, Q a b c).
  Proof.
    set_solver.
  Qed. 

  Lemma ex_det_iff {A: Type} (P: A -> Prop) a
    (DET: forall a', P a' -> a' = a):
    (exists a', P a') <-> P a.
  Proof. 
    split; [| by eauto].
    intros [? ?]. erewrite <- DET; eauto.
  Qed. 

  Lemma iff_and_pre {A B C: Prop}
    (BC: A -> (B <-> C)):
    A /\ B <-> A /\ C.
  Proof using. tauto. Qed.

  Lemma curry_uncurry_prop {A B C: Prop}:
    (A -> B -> C) <-> (A /\ B -> C).
  Proof. tauto. Qed. 

  Lemma forall_eq_gen {A: Type} (P: A -> Prop):
    forall a, P a <-> (forall a', a' = a -> P a').
  Proof. set_solver. Qed. 

End LogicHelpers.


Section Powerset.
  Context {K: Type}.
  Context `{Countable K}. 
  
  (* it's easier to perform recursion on lists *)
  (* TODO: another name? *)
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




Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).

Lemma dom_domain_restrict `{Countable X} {A} (f: gmap X A) (R: gset X):
  R ⊆ dom f ->
  dom  (f ⇂ R) = R.
Proof.
  intros ?. apply dom_filter_L.
  intros i; split; [|set_solver].
  intros Hin. assert (Hin': i ∈ dom f) by set_solver.
  apply elem_of_dom in Hin' as [??]. set_solver.
Qed.

(* TODO: generalize *)
Lemma dom_filter_sub {K V: Type} `{Countable K} (m: gmap K V)
  (ks: gset K):
  dom (filter (λ '(k, _), k ∈ ks) m) ⊆ ks.
Proof.
  apply elem_of_subseteq.
  intros ? IN. rewrite elem_of_dom in IN. destruct IN as [? IN].
  apply map_filter_lookup_Some in IN. apply IN.
Qed. 

(* TODO: generalize, upstream *)
Lemma dom_filter_comm {K A: Type} `{Countable K}
  (P: K -> Prop) `{∀ x : K, Decision (P x)}:
  forall (m: gmap K A), dom (filter (fun '(k, _) => P k) m) = filter P (dom m).
Proof.
  intros. apply leibniz_equiv. apply dom_filter. intros.
  rewrite elem_of_filter elem_of_dom.
  rewrite /is_Some. split; [intros [?[??]] | intros [? [??]]]; eauto.
Qed.


Lemma dom_domain_restrict_union_l `{Countable X} {A} (f: gmap X A) R1 R2:
  R1 ∪ R2 ⊆ dom f ->
  dom (f ⇂ R1) = R1.
Proof.
  intros ?. apply dom_domain_restrict. set_solver.
Qed.
Lemma dom_domain_restrict_union_r `{Countable X} {A} (f: gmap X A) R1 R2:
  R1 ∪ R2 ⊆ dom f ->
  dom (f ⇂ R2) = R2.
Proof.
  intros ?. apply dom_domain_restrict. set_solver.
Qed.

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


Section bigop_utils.
  Context `{Monoid M o}.
  Context `{Countable K}.

  Lemma big_opMS (g: gset K) (P: K -> M):
    ([^ o set] x ∈ g, P x) ≡ [^ o map] x ↦ y ∈ (mapset_car g), P x.
  Proof.
    rewrite big_opS_elements /elements /gset_elements /mapset_elements.
    rewrite big_opM_map_to_list.
    destruct g as [g]. simpl. rewrite big_opL_fmap.
    f_equiv.
  Qed.
End bigop_utils.

Section bigop_utils.
  Context `{Countable K} {A : cmra}.
  Implicit Types m : gmap K A.
  Implicit Types i : K.

  Lemma gset_to_gmap_singletons (a : A) (g : gset K):
    ([^op set] x ∈ g, {[x := a]}) ≡ gset_to_gmap a g.
  Proof.
    rewrite big_opMS.
    rewrite -(big_opM_singletons (gset_to_gmap a g)).
    rewrite /gset_to_gmap big_opM_fmap //.
  Qed.

  (* TODO: upstream *)
  Lemma big_opM_fmap_singletons
    {B: cmra} (m : gmap K A) (f: A -> B)
    (LE: LeibnizEquiv B):
    ([^ op map] k↦x ∈ m, f <$> {[k := x]}) = (f <$> m: gmap K B).
  Proof.
    intros. pattern m. apply map_ind.
    { rewrite big_opM_empty fmap_empty. done. }
    intros. 
    rewrite insert_union_singleton_l.
    apply leibniz_equiv.
    rewrite big_opM_union.
    2: { by apply map_disjoint_singleton_l_2. }
    rewrite H1. rewrite big_opM_singleton.
    rewrite map_fmap_union. rewrite !map_fmap_singleton /=.
    apply leibniz_equiv_iff. apply gmap_disj_op_union.
    apply map_disjoint_singleton_l_2. rewrite lookup_fmap H0. done.
  Qed.

  (* TODO: upstream *)
  Lemma big_opM_insert_delete':
  ∀ {M : ofe} {o : M → M → M} {Monoid0 : Monoid o}
    {B : Type} 
    (f : K → B → M) (m : gmap K B) (i : K) (x : B),
    m !! i = Some x ->
    ([^ o map] k↦y ∈ m, f k y)
    ≡ o (f i x) ([^ o map] k↦y ∈ delete i m, f k y).
  Proof.
    intros. rewrite -big_opM_insert_delete.
    symmetry. eapply big_opM_insert_override; eauto.
  Qed.
  
End bigop_utils.

Section map_utils.
  Context `{Countable K, Countable V, EqDecision K}.

  Definition maps_inverse_match (m: gmap K V) (m': gmap V (gset K)) :=
    ∀ (k: K) (v: V), m !! k = Some v <-> ∃ (ks: gset K), m' !! v = Some ks ∧ k ∈ ks.

  Lemma no_locale_empty M M' ρ ζ:
    maps_inverse_match M M' ->
    M' !! ζ = Some ∅ ->
    M !! ρ ≠ Some ζ.
  Proof.
    intros Hinv Hem contra.
    destruct (Hinv ρ ζ) as [Hc _]. destruct (Hc contra) as (?&?&?).
    by simplify_eq.
  Qed.

  Lemma maps_inverse_bij M M' ρ X1 X2 ζ ζ':
    maps_inverse_match M M' ->
    M' !! ζ = Some X1 -> ρ ∈ X1 ->
    M' !! ζ' = Some X2 -> ρ ∈ X2 ->
    ζ = ζ'.
  Proof.    intros Hinv Hζ Hρ Hζ' Hρ'.
    assert (M !! ρ = Some ζ); first by apply Hinv; eexists; done.
    assert (M !! ρ = Some ζ'); first by apply Hinv; eexists; done.
    congruence.
  Qed.

  Lemma maps_inverse_match_exact (v: V) (S: gset K):
    maps_inverse_match (gset_to_gmap v S) {[v := S]}.
  Proof.
    red. intros. rewrite lookup_gset_to_gmap_Some. split.
    - intros [? ->]. eexists. split; eauto. apply lookup_singleton.
    - intros [? [[? ->]%lookup_singleton_Some ?]]. done.
  Qed.    
  
  Lemma maps_inverse_match_uniq1 (m1 m2: gmap K V) (m': gmap V (gset K))
    (M1: maps_inverse_match m1 m') (M2: maps_inverse_match m2 m'):
    m1 = m2.
  Proof.
    red in M1, M2. apply map_eq. intros.
    destruct (m1 !! i) eqn:L1.
    - pose proof (proj1 (M1 _ _) L1) as EQ.
      pose proof (proj2 (M2 _ _) EQ).
      congruence.
    - destruct (m2 !! i) eqn:L2; [| done].
      pose proof (proj1 (M2 _ _) L2) as EQ.
      pose proof (proj2 (M1 _ _) EQ).
      congruence.
  Qed.

  Lemma maps_inverse_match_subseteq (m1 m2: gmap K V) (m1' m2': gmap V (gset K))
    (M1: maps_inverse_match m1 m1') (M2: maps_inverse_match m2 m2')
    (SUB: dom m1' ⊆ dom m2')
    (INCL: forall v S1 S2, m1' !! v = Some S1 -> m2' !! v = Some S2 -> S1 ⊆ S2):
    m1 ⊆ m2.
  Proof.
    red in M1, M2. apply map_subseteq_spec. intros.
    specialize (proj1 (M1 _ _) H1) as [? [L1 ?]]. 
    apply M2.
    specialize (SUB x (elem_of_dom_2 _ _ _ L1)).
    apply elem_of_dom in SUB as [? ?].
    eexists. split; eauto. set_solver.
  Qed. 

  Lemma mim_in_1 (m: gmap K V) (m': gmap V (gset K)) k v
    (MIM: maps_inverse_match m m')
    (DOM: m !! k = Some v):
      v ∈ dom m'.
  Proof.
    red in MIM.
    pose proof (proj1 (MIM _ _) DOM) as (?&?&?).
    apply elem_of_dom. set_solver.
  Qed. 

  Lemma mim_in_2 (m: gmap K V) (m': gmap V (gset K)) k v
    (MIM: maps_inverse_match m m')
    (IN: k ∈ default ∅ (m' !! v)):
      k ∈ dom m.
  Proof.
    red in MIM.
    destruct (m' !! v) eqn:TM.
    2: { done. }
    simpl in IN.
    specialize (MIM k v). apply proj2 in MIM.
    eapply elem_of_dom. eexists.
    apply MIM. eauto. 
  Qed. 

  Lemma mim_lookup_helper
    (tm: gmap V (gset K)) (m: gmap K V)
    R ζ
    (MIM: maps_inverse_match m tm)
    (NE: R ≠ ∅)
    (DOM: ∀ ρ, m !! ρ = Some ζ ↔ ρ ∈ R):
    tm !! ζ = Some R.
  Proof. 
    apply finitary.set_choose_L' in NE as [k INR].
    pose proof (proj2 (DOM k) INR) as MAP.
    red in MIM. specialize MIM with (v := ζ). 
    pose proof (proj1 (MIM _ ) MAP) as (R' & TM' & IN').
    rewrite TM'. f_equal.
    apply set_eq. clear dependent k. intros k.
    rewrite <- DOM. rewrite TM' in MIM. split.
    - intros IN'. apply MIM. eauto.
    - intros ?%MIM. set_solver.
  Qed. 

  Lemma mim_neg m tm
    (MIM: maps_inverse_match m tm):
    ∀ (k: K), m !! k = None <-> forall g, k ∉ default ∅ (tm !! g).
  Proof. 
    intros. red in MIM. specialize (MIM k). split.
    - intros MAP. intros g IN.
      destruct (tm !! g) eqn:TM; set_solver.
    - intros NIN. destruct (m !! k) eqn:MAP; [| done].
      pose proof (proj1 (MIM v) eq_refl) as (?&?&?).
      specialize (NIN v). rewrite H1 in NIN. set_solver.
  Qed. 

End map_utils.

Section fin_map_dom.
Context `{FinMapDom K M D}.
Lemma dom_empty_iff {A} (m : M A) : dom m ≡ ∅ ↔ m = ∅.
Proof.
  split; [|intros ->; by rewrite dom_empty].
  intros E. apply map_empty. intros. apply not_elem_of_dom.
  rewrite E. set_solver.
Qed.

Section leibniz.
  Context `{!LeibnizEquiv D}.
  Lemma dom_empty_iff_L {A} (m : M A) : dom m = ∅ ↔ m = ∅.
  Proof. unfold_leibniz. apply dom_empty_iff. Qed.
End leibniz.
End fin_map_dom.

Section map_imap.
  Context `{Countable K}.
  Lemma map_imap_dom_inclusion {A B} (f : K → A → option B) (m : gmap K A) :
    dom (map_imap f m) ⊆ dom m.
  Proof.
    intros i [k Hk]%elem_of_dom. rewrite map_lookup_imap in Hk.
    destruct (m !! i) eqn:?; last done.
    rewrite elem_of_dom. by eexists.
  Qed.
  Lemma map_imap_dom_eq {A B} (f : K → A → option B) (m : gmap K A) :
    (forall k a, k ∈ dom m -> is_Some (f k a)) ->
    dom (map_imap f m) = dom m.
  Proof.
    rewrite -leibniz_equiv_iff. intros HisSome i. split.
    - intros [x Hx]%elem_of_dom. rewrite map_lookup_imap in Hx.
      apply elem_of_dom. destruct (m !! i) eqn:Heq; eauto.
      by simpl in Hx.
    - intros [x Hx]%elem_of_dom.
      rewrite elem_of_dom map_lookup_imap Hx /=. apply HisSome, elem_of_dom. eauto.
  Qed.
End map_imap.

(* TODO: upstream *)
(* Lemma not_elem_of_equiv_not_empty_L: *)
(* ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} *)
(*   {H2 : Union C}, *)
(*   SemiSet A C → LeibnizEquiv C → *)
(*   ∀ X : C, X ≠ ∅ ↔ (exists x : A, x ∈ X). *)
Lemma gset_not_elem_of_equiv_not_empty_L:
  ∀ {A : Type} `{Countable A},
  ∀ (X : gset A), X ≠ ∅ ↔ (exists x : A, x ∈ X).
Proof.
  intros. split.
  - by apply set_choose_L.
  - set_solver. 
Qed. 

(* TODO: already exists somewhere? *)
Lemma Decision_iff_impl (P Q: Prop) (PQ: P <-> Q) (DEC_P: Decision P):
  Decision Q. 
Proof using. 
  destruct DEC_P; [left | right]; tauto. 
Qed.  

Instance ex_fin_dec {T: Type} (P: T -> Prop) (l: list T)
  (DEC: forall a, Decision (P a))
  (IN: forall a, P a -> In a l):
  Decision (exists a, P a).
Proof.
  destruct (Exists_dec P l) as [EX|NEX].
  - left. apply List.Exists_exists in EX as (?&?&?). eauto.
  - right. intros [a Pa]. apply NEX.
    apply List.Exists_exists. eexists. split; eauto.
Qed. 


Lemma fmap_flat_map {A B C: Type} (f : A → list B) (g: B -> C) (l : list A):
  g <$> (flat_map f l) = flat_map ((fmap g) ∘ f) l.
Proof.
  induction l; [done| ].
  simpl. rewrite fmap_app. congruence.
Qed.

(* TODO: upstream *)
Lemma concat_NoDup {A: Type} (ll : list (list A)):
  (forall i l, ll !! i = Some l -> NoDup l) ->
  (forall i j li lj, i ≠ j -> ll !! i = Some li -> ll !! j = Some lj -> li ## lj) ->
  NoDup (concat ll).
Proof.
  induction ll.
  { constructor. }
  intros. simpl. apply NoDup_app. repeat split.
  { apply (H 0). done. }
  2: { apply IHll.
       - intros. apply (H (S i)). done.
       - intros. apply (H0 (S i) (S j)); auto. }
  intros. intros [lx [INlx INx]]%elem_of_list_In%in_concat.
  apply elem_of_list_In, elem_of_list_lookup_1 in INlx as [ix IX].
  eapply (H0 0 (S ix)).
  - lia.
  - simpl. reflexivity.
  - simpl. apply IX.
  - eauto.
  - by apply elem_of_list_In.
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

Section TmapDisj.
  Context `{Countable K} `{Countable V}. 

  Definition tmap_disj (tm: gmap K (gset V)) :=
    forall (k1 k2: K) (S1 S2: gset V) (NEQ: k1 ≠ k2),
      tm !! k1 = Some S1 -> tm !! k2 = Some S2 -> S1 ## S2.

  Lemma forall_prod_helper {A B: Type} (P: A -> B -> Prop):
    (forall a b, P a b) <-> (forall ab: A * B, P ab.1 ab.2).
  Proof.
    split; [by eauto|]. intros PP ??.
    apply (PP (a, b)).
  Qed.    
  
  Global Instance tmap_disj_dec tm: Decision (tmap_disj tm).
  Proof.
    set pairs := let d := elements (dom tm) in
                 k1 ← d; k2 ← d;
                 if (decide (k1 = k2)) then [] else [(k1, k2)]. 
    set alt := Forall (fun '(k1, k2) => (default ∅ (tm !! k1)) ## (default ∅ (tm !! k2))) pairs.
    apply Decision_iff_impl with (P := alt); [| solve_decision].
    rewrite /alt. rewrite Forall_forall. 
    rewrite /pairs.
    repeat setoid_rewrite elem_of_list_bind.
    repeat setoid_rewrite elem_of_elements.
    rewrite /tmap_disj.
    repeat setoid_rewrite elem_of_dom.
    rewrite forall_prod_helper. apply forall_proper. intros [k1 k2]. simpl.
    erewrite ex_det_iff with (a := k1).
    2: { intros ?. erewrite ex_det_iff with (a := k2).
         2: { intros ?. destruct decide; set_solver. }
         destruct decide; set_solver. }
    erewrite ex_det_iff with (a := k2).
    2: { intros ?. destruct decide; set_solver. }
    destruct decide; [set_solver| ].
    destruct (tm !! k1), (tm !! k2); set_solver.
  Qed. 

End TmapDisj.

Require Import ClassicalFacts.

Lemma min_prop_dec_impl (P: nat -> Prop) (DEC: forall n, Decision (P n)):
  ∀ n, P n → {m | Minimal P m}.
Proof.
  intros n Pn.

  assert (forall p, p <= n + 1 -> ({m | Minimal P m} + {forall k, k < p -> ¬ P k})) as MIN'.
  2: { destruct (MIN' (n + 1)); eauto. edestruct n0; eauto. lia. }

  induction p.
  { intros. right. lia. }
  intros. destruct IHp; [lia| auto| ].
  rewrite Nat.add_1_r in H. apply le_S_n in H. 
  destruct (DEC p).
  - left. exists p. split; auto. intros.
    destruct (decide (p <= k)); auto.
    destruct (n0 k); auto. lia.
  - right. intros. destruct (decide (k = p)); [congruence| ].
    apply n0. lia.
Qed. 

Definition Minimal_pos (P: positive → Prop) (n : positive) :=
  P n ∧ (∀ k, P k → Pos.le n k). 

Lemma min_prop_dec_impl_pos (P: positive -> Prop) (DEC: forall n, Decision (P n)):
  ∀ n, P n → {m: positive | Minimal_pos P m }.
Proof.
  intros n Pn.
  epose proof (min_prop_dec_impl (P ∘ Pos.of_nat) _ (Pos.to_nat n)) as [m [Pm MINm]].
  { red. by rewrite Pos2Nat.id. }
  exists (Pos.of_nat m). split; auto.
  intros.
  specialize (MINm (Pos.to_nat k) ltac:(red; by rewrite Pos2Nat.id)). 
  lia. 
Qed.

From stdpp Require Import namespaces coPset. 
Section CoPsetOrdering.
  
  Definition coPset_least (C: coPset) (INF: ¬ set_finite C) : positive :=
    let c := coPpick C in
    let m := min_prop_dec_impl_pos (fun p => p ∈ C) _ c (coPpick_elem_of _ INF) in
    proj1_sig m.

  Lemma coPset_least_spec (C: coPset) (INF: ¬ set_finite C):
    Minimal_pos (fun p => p ∈ C) (coPset_least C INF).
  Proof.
    rewrite /coPset_least.
    by destruct min_prop_dec_impl_pos.
  Qed.

  Lemma coPset_least_in (C: coPset) (INF: ¬ set_finite C):
    coPset_least C INF ∈ C. 
  Proof.
    apply coPset_least_spec. 
  Qed.

  Local Lemma coPset_sub1_helper (C: coPset) (INF: ¬ set_finite C) (m: positive):
    ¬ set_finite (C ∖ {[ m ]}).
  Proof.
    apply coPset_infinite_finite. apply difference_infinite.
    - by apply coPset_infinite_finite.
    - apply singleton_finite.
  Qed. 

  Fixpoint coPset_nth (C: coPset) (INF: ¬ set_finite C) (n: nat): positive :=
    let m := coPset_least C INF in
    match n with
    | 0 => m
    | S n => coPset_nth (C ∖ {[ m ]}) (coPset_sub1_helper C INF m) n
    end.

  Definition ns_nth (ns: namespace) :=
    coPset_nth (↑ns) (nclose_infinite ns). 

  Lemma coPset_nth_in C INF i:
    coPset_nth C INF i ∈ C. 
  Proof.
    remember (coPset_nth C INF i) as c. generalize dependent c. 
    generalize dependent C. induction i.
    { simpl. intros. subst. apply coPset_least_in. }
    simpl. intros.
    specialize (IHi _ _ _ Heqc).
    set_solver.
  Qed. 

  Lemma coPset_nth_disj_neq C1 C2 INF1 INF2 n1 n2
    (DISJ: C1 ## C2):
    coPset_nth C1 INF1 n1 ≠ coPset_nth C2 INF2 n2.
  Proof. 
    pose proof (coPset_nth_in _ INF1 n1).
    pose proof (coPset_nth_in _ INF2 n2) as IN2. 
    intros EQ. rewrite -EQ in IN2. set_solver.
  Qed. 

  Lemma coPset_nth_next_lt C INF i:
    (coPset_nth C INF i < coPset_nth C INF (S i))%positive.
  Proof using.
    remember (coPset_nth C INF i) as m. remember (coPset_nth C INF (S i)) as m'.
    generalize dependent C. generalize dependent m. generalize dependent m'.
    induction i.
    { simpl. intros.
      pose proof (coPset_least_spec C INF).
      assert (m' ∈ C) as IN'.
      { subst m'. eapply elem_of_weaken; [apply coPset_least_in| ]. set_solver. }
      red in H. apply proj2 in H. specialize (H m' IN').
      rewrite -Heqm in H. apply Positive_as_OT.le_lteq in H as [? | ?]; [lia| ].
      rewrite -Heqm in Heqm'.
      pose proof (coPset_least_in _ (coPset_sub1_helper C INF m)).
      set_solver. }
    intros.
    pose proof (coPset_sub1_helper C INF (coPset_least C INF)) as INF'.
    eapply IHi; eauto.
  Qed.

  Lemma coPset_nth_lt C INF i j (LT: i < j):
    (coPset_nth C INF i < coPset_nth C INF j)%positive.
  Proof.
    apply Nat.lt_exists_pred in LT as (? & -> & LE).
    apply Nat.le_sum in LE as [d ->]. 
    induction d.
    { rewrite Nat.add_0_r. apply coPset_nth_next_lt. }
    etrans; eauto.
    eapply Positive_as_OT.lt_le_trans; [apply coPset_nth_next_lt| ].
    apply Positive_as_OT.le_lteq. right. f_equal. lia.
  Qed.     

  Lemma coPset_nth_inj (C: coPset) (INF: ¬ set_finite C):
    Inj eq eq (coPset_nth C INF).
  Proof.
    red. intros i j EQ.
    destruct (Nat.lt_trichotomy i j) as [LT|[?|LT]]; auto.
    all: apply (coPset_nth_lt C INF) in LT; lia.
  Qed.

  Lemma coPset_nth_surj (C: coPset) (INF: ¬ set_finite C):
    forall p, p ∈ C -> exists n, p = coPset_nth C INF n. 
  Proof.
    intros p INp. 
    remember (coPset_least C INF) as m.
    remember (Pos.to_nat p - Pos.to_nat m) as d.
    generalize dependent m. generalize dependent C.
    pattern d. apply lt_wf_ind. clear d. intros d IH.     
    destruct (decide (d = 0)) as [-> | NZ]. 
    { simpl. intros. symmetry in Heqd. apply Nat.sub_0_le in Heqd.
      apply Pos2Nat.inj_le in Heqd.
      apply Positive_as_OT.le_lteq in Heqd as [LT | ->].
      2: { by exists 0. }
      pose proof (coPset_least_spec C INF). rewrite -Heqm in H.
      red in H. apply proj2 in H. specialize (H _ INp). 
      lia. }
    intros.
    set (m' := coPset_least (C ∖ {[ m ]}) (coPset_sub1_helper C INF m)).
    assert (m' ∈ C ∖ {[ m ]}) as IN'.
    { subst m'. apply coPset_least_in. }
    assert (Pos.to_nat p - Pos.to_nat m' < d) as LT'.
    { subst d. enough (Pos.to_nat m < Pos.to_nat m'); [lia| ].
      apply Pos2Nat.inj_lt.
      subst m m'. apply (coPset_nth_lt C INF 0 1). lia. }
    assert (p ∈ C ∖ {[m]}) as IN''.
    { apply elem_of_difference. split; auto.
      apply not_elem_of_singleton. intros ->. lia. }
    specialize (IH (Pos.to_nat p - Pos.to_nat m') LT' _ (coPset_sub1_helper C INF m) IN''
               _ ltac:(done) ltac:(done)).
    destruct IH as [n' EQ']. exists (S n'). simpl. set_solver.
  Qed.

End CoPsetOrdering.


Lemma ns_ndot_disj' (ns: namespace) (i: nat):
  ns ≠ ns .@ i.
Proof using.
  intros EQ.
  pose proof (coPpick_elem_of (↑ ns .@ (i + 1)) (nclose_infinite _)) as IN.
  pose proof IN as IN'. rewrite {2}EQ in IN'.
  apply nclose_subseteq in IN'.
  edestruct @ndot_ne_disjoint; [| apply IN | apply IN'].
  lia. 
Qed.   

(* TODO: can be proved simpler if we could unfold ndot *)
Lemma ns_ndot_diff_not_subseteq (ns: namespace) (i j: nat)
  (NEQ: i ≠ j):
  (↑ (ns .@ i): coPset) ⊈ ↑ (ns .@ j).
Proof.
  intros EQ.
  pose proof (coPpick_elem_of (↑ ns .@ i) (nclose_infinite _)) as IN1.
  edestruct @ndot_ne_disjoint; [| apply IN1 | ].
  2: { apply EQ. done. }  
  done. 
Qed. 

Lemma ns_ndot_disj (ns: namespace) (i j: nat)
  (NEQ: i ≠ j):
  ns .@ i ≠ ns .@ j.
Proof using.
  intros EQ. edestruct (ns_ndot_diff_not_subseteq ns); eauto.
  by rewrite EQ.
Qed. 

Lemma gset_to_gmap_singleton `{Countable K} {B: Type} (b: B) (k: K):
  gset_to_gmap b {[ k ]} = {[ k := b ]}.
Proof.
  rewrite /gset_to_gmap. simpl. rewrite map_fmap_singleton. done.
Qed. 


Ltac add_case C name :=
  match goal with
  | |- ?G => assert (C -> G) as name
  end.


Section Arithmetic.

  Lemma even_succ_negb n: Nat.even (S n) = negb $ Nat.even n.
  Proof. by rewrite Nat.even_succ Nat.negb_even. Qed.

  Lemma odd_succ_negb n: Nat.odd (S n) = negb $ Nat.odd n.
  Proof. by rewrite Nat.odd_succ Nat.negb_odd. Qed.

  Lemma even_plus1_negb n: Nat.even (n + 1) = negb $ Nat.even n.
  Proof. by rewrite Nat.add_1_r even_succ_negb. Qed. 

  Lemma odd_plus1_negb n: Nat.odd (n + 1) = negb $ Nat.odd n.
  Proof. by rewrite Nat.add_1_r odd_succ_negb. Qed.

  Lemma even_odd_False n : Nat.even n → Nat.odd n → False.
  Proof.
    intros Heven Hodd. rewrite -Nat.negb_odd in Heven.
    apply Is_true_true_1 in Heven.
    apply Is_true_true_1 in Hodd.
    by rewrite Hodd in Heven.
  Qed.
  
  Lemma even_not_odd n : Nat.even n → ¬ Nat.odd n.
  Proof. intros Heven Hodd. by eapply even_odd_False. Qed.
  
  Lemma odd_not_even n : Nat.odd n → ¬ Nat.even n.
  Proof. intros Heven Hodd. by eapply even_odd_False. Qed.
  
  Lemma even_or_odd n: Nat.even n \/ Nat.odd n.
  Proof. 
    destruct (decide (Nat.even n)) as [| O]; auto.
    apply negb_prop_intro in O. rewrite Nat.negb_even in O. tauto.
  Qed.

End Arithmetic.
