From stdpp Require Import base.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Export utils_logic.
From iris.algebra Require Import gmap gset agree.
From trillium.prelude Require Import finitary.

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

  Lemma map_split {A: Type} (m: gmap K A) k:
    m = from_option (singletonM k) ∅ (m !! k) ∪ delete k m.
  Proof using.
    apply map_eq. intros k'.
    destruct (decide (k' = k)) as [->|?].
    - destruct (m !! k) eqn:KTH.
      + simpl. rewrite lookup_union_l'.
        all: by rewrite lookup_singleton.
      + simpl. rewrite lookup_union_r; [| done].
        by rewrite lookup_delete.
    - rewrite lookup_union_r.
      2: { destruct (m !! k); [| set_solver]. 
           by rewrite lookup_singleton_ne. } 
      by rewrite lookup_delete_ne.
  Qed.
  
  Lemma lookup_map_singleton {A: Type} (k: K) (a: A) k':
    ({[ k := a ]}: gmap K A) !! k' = if (decide (k' = k)) then Some a else None.
  Proof using.
    destruct decide; subst.
    - apply lookup_singleton.
    - by apply lookup_singleton_ne.
  Qed. 

  Lemma map_fold_union
    {V B: Type}
    (m1 m2: gmap K V)
    (f: K → V → B → B)
    (b0: B)
    (DISJ: map_disjoint m1 m2)
    (ASSOC: forall a b c d e, f a b (f c d e) = f c d (f a b e))
    :
    map_fold f b0 (m1 ∪ m2) = map_fold f (map_fold f b0 m1) m2.
  Proof using.
    clear -DISJ ASSOC.
    revert DISJ. pattern m2. apply map_ind; clear m2.
    { rewrite map_union_empty. rewrite map_fold_empty. done. }
    intros ??? NOI IH DISJ. rewrite map_union_comm; [| set_solver].
    rewrite -insert_union_l. simpl.
    rewrite map_fold_insert_L.
    3: { rewrite lookup_union_r; [| done].
         apply not_elem_of_dom. intros IN.
         apply map_disjoint_dom in DISJ.
         set_solver. }
    2: { done. }
    apply map_disjoint_dom in DISJ. specialize (IH ltac:(apply map_disjoint_dom; set_solver)).
    rewrite map_union_comm in IH.
    2: { apply map_disjoint_dom. set_solver. }
    rewrite IH.
    rewrite map_fold_insert_L; done.
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


Lemma gmap_filter_or `{Countable K} {A: Type} (P1 P2: K * A -> Prop)
  `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)}
  (m: gmap K A):
  filter (fun x => P1 x \/ P2 x) m = filter P1 m ∪ filter P2 m.
Proof using.
  clear.
  apply map_eq. intros k.
  destruct (m !! k) eqn:KTH.
  2: { etrans; [| symmetry].
       { eapply map_filter_lookup_None. tauto. }
       apply lookup_union_None_2; eapply map_filter_lookup_None; tauto. }
  destruct (decide (P1 (k, a))).
  { erewrite map_filter_lookup_Some_2; eauto.
    erewrite lookup_union_Some_l; eauto. eapply map_filter_lookup_Some; eauto. }
  erewrite lookup_union_r; eauto.
  2: { eapply map_filter_lookup_None. set_solver. }
  destruct (decide (P2 (k, a))).
  { erewrite map_filter_lookup_Some_2; eauto.      
    symmetry. apply map_filter_lookup_Some_2; eauto. }
  etrans; [| symmetry]; eapply map_filter_lookup_None; set_solver.
Qed.

Section MapsInverseMatch.
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

End MapsInverseMatch.

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


Section TmapDisj.
  Context `{Countable K} `{Countable V}. 

  Definition tmap_disj (tm: gmap K (gset V)) :=
    forall (k1 k2: K) (S1 S2: gset V) (NEQ: k1 ≠ k2),
      tm !! k1 = Some S1 -> tm !! k2 = Some S2 -> S1 ## S2.

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


Lemma map_nat_agree_valid {A: ofe} (m: gmap nat A):
  ✓ ((to_agree <$> m): gmapUR nat (agreeR A)).
Proof using.
  red. intros k.
  destruct lookup eqn:LL; [| done].
  apply lookup_fmap_Some in LL. 
  destruct LL as (a&<-&?). 
  done.
Qed.
