From Coq Require Import Sorting.Permutation List.
From Coq Require Import Classes.Morphisms.
Import ListNotations.

(** Adapted from Arthur Correnson's proof: *)
(**     https://github.com/acorrenson/multiset *)
(** * A minimalist and self contained formalization of multiset ordering *)

Section MSO.

(** ** Definitions *)

(** We start with a base type [A] equiped with a binary relation [lt] *)
Context {A : Type} {lt : A -> A -> Prop}.

(** We suppose that [A] has a decidable equality *)
Context {eq_dec : forall (x y : A), { x = y } + { x <> y }}.

Definition equ (L1 L2 : list A) :=
  Permutation L1 L2.
Infix "≡" := (Permutation) (at level 80).
Infix "=?" := (eq_dec) (at level 80).

(** We extend [lt] to a binary relation on lists *)
(*     Intuitively [lt_ext1 L1 L2] iff L1 is obtained  *)
(*     from L2 by removing an element and *)
(*     replacing it by a list of smaller ones *)
(* *)
Inductive lt_ext1 (L1 L2 : list A) : Prop :=
  | lt_ext1_intro x X Y :
    L1 ≡ Y ++ X ->
    L2 ≡ x::X ->
    (forall y, In y Y -> lt y x) ->
    lt_ext1 L1 L2.

(** Removing one occurence of [x] in [L] *)
Fixpoint remove (L : list A) (x : A) :=
  match L with
  | [] => []
  | y::L =>
    if x =? y then L else y::remove L x
  end.

(** [remove] is compatible with permutations *)
#[global]
Instance remove_morphism: Proper (equ ==> eq ==> equ) remove.
Proof.
  intros L1 L2 Heq a ? <-.
  induction Heq; simpl.
  - reflexivity.
  - destruct (eq_dec a x) as [->|Hne]; auto.
    now rewrite IHHeq.
  - destruct (eq_dec a x) as [->|Hne1].
    destruct (eq_dec x y) as [->|Hne2]; try easy.
    destruct (eq_dec a y) as [->|Hne2]; try easy.
    constructor.
  - now rewrite IHHeq1, IHHeq2.
Qed.

Lemma remove_head:
  forall a L, L ≡ remove (a::L) a.
Proof.
  intros; simpl.
  now destruct (eq_dec a a).
Qed.

(** ** Proof that [lt_ext1] is well founded *)

Theorem lt_ext1_inv:
  forall L1 L2 a,
    lt_ext1 L1 (a::L2) ->
    exists X,
      (L1 ≡ a::X /\ lt_ext1 X L2) \/
      (L1 ≡ X ++ L2 /\ forall x, In x X -> lt x a).
Proof.
  intros L1 L2 a H.
  inversion H as [b X Y HXY Heq HY].
  destruct (eq_dec a b) as [->|Hne].
  - apply Permutation_cons_inv in Heq.
    exists Y. right. now rewrite Heq.
  - pose proof (Heq' := remove_morphism _ _ Heq b b eq_refl).
    simpl in Heq'.
    destruct (eq_dec b b) as [_|]; try easy.
    destruct (eq_dec b a) as [->|_]; try easy.
    rewrite <- Heq' in HXY.
    exists (Y ++ remove L2 b).
    left. split.
  + rewrite HXY.
    fold ([a] ++ remove L2 b).
    fold ([a] ++ (Y ++ remove L2 b)).
    apply Permutation_app_swap_app.
  + econstructor; eauto.
    rewrite <- Heq' in Heq.
    eapply Permutation_cons_inv.
    rewrite Heq. econstructor.
Qed.

#[global]
Instance lt_ext1_morphism:
  Proper (equ ==> equ ==> iff) lt_ext1.
Proof.
  intros X1 X2 HX Y1 Y2 HY. split.
  - intros H. inversion H. econstructor.
    rewrite <- HX. apply H0.
    rewrite <- HY. apply H1.
    auto.
  - intros H. inversion H. econstructor.
    rewrite HX. apply H0.
    rewrite HY. apply H1.
    auto.
Qed.

Lemma helper_1:
  forall (L1 : list A) (a : A),
    (forall b L2, lt b a -> Acc lt_ext1 L2 -> Acc lt_ext1 (b::L2)) ->
    (forall L2, lt_ext1 L2 L1 -> Acc lt_ext1 (a::L2)) ->
    Acc lt_ext1 L1 ->
    Acc lt_ext1 (a::L1).
Proof.
  intros * H1 H2 Hacc.
  constructor. intros N [M' [HN1 | HN2]]%lt_ext1_inv.
  - destruct HN1 as [H3 H4].
    rewrite H3. apply H2, H4.
  - destruct HN2 as [H3 H4].
    rewrite H3. clear H3.
    induction M'; simpl in *; auto.
Qed.

Lemma helper_2:
  forall a,
    (forall (b : A) (M : list A), lt b a -> Acc lt_ext1 M -> Acc lt_ext1 (b::M)) ->
    forall M, Acc lt_ext1 M -> Acc lt_ext1 (a::M).
Proof.
  intros * H M HM.
  induction HM as [M' H1 H2].
  apply helper_1; auto.
  now constructor.
Qed.

Lemma helper_3:
  forall (a : A) (M : list A),
    Acc lt a -> Acc lt_ext1 M -> Acc lt_ext1 (a::M).
Proof.
  intros a M Ha.
  induction Ha as [b H1 H2] in M |-*.
  intros HM. apply helper_2; auto.
Qed.

Lemma well_founded_lt_ext1:
    well_founded lt ->
    well_founded lt_ext1.
Proof.
  intros * Hwf M.
  induction M.
  - constructor. intros M' Hl.
    inversion Hl as [X Y a H1 H2 H3].
    now apply Permutation_nil_cons in H2.
  - apply helper_3; auto.
Qed.

End MSO.

Require Import Relation_Operators.

(* (* TODO: move *) *)
(* Lemma clos_trans_ind1: *)
(*   ∀ (A : Type) (R : relation A) (P : A → A → Prop), *)
(*     (∀ x y : A, R x y → P x y) *)
(*     → (∀ x y z : A, *)
(*          clos_trans A R x y → P x y → clos_trans A R y z → P y z → P x z) *)
(*       → ∀ x a : A, clos_trans A R x a → P x a *)



From stdpp Require Import gmultiset.
From trillium.fairness.lawyer.obligations Require Import multiset_utils.
From iris.proofmode Require Import tactics.
Require Import Coq.Program.Wf.
From trillium.fairness Require Import utils.

(* TODO: move *)
Global Instance clos_trans_1n_proper_impl {A: Type} (R: relation A)
  (E: relation A)
  {REFL_E: Reflexive E}
  (PR: Proper (E ==> E ==> impl) R):
  Proper (E ==> E ==> impl) (clos_trans_1n _ R).
Proof using.
  red. intros x1 x2 Ex y1 y2 Ey. intros TR.
  generalize dependent x2. generalize dependent y2.
  induction TR.
  + intros. econstructor. eapply PR; [..| apply H]; done.
  + intros y2 Ez x2 Ex.
    rename x into x1.
    rename y2 into z2. rename z into z1.
    rename y into y1.
    eapply PR in H; eauto.     
    specialize (IHTR _ Ez).
    specialize (IHTR _ ltac:(reflexivity)).
    eapply t1n_trans; eauto.
Qed.

(* (* TODO: move *) *)
(* Inductive clos_refl {A: Type} (R: relation A) (E: relation A) (x: A) : A -> Prop := *)
(* | r_step (y:A) : R x y -> clos_refl x y *)
(* | r_refl (Exy: E x y) : clos_refl x y. *)

  
(* TODO: move *)
Global Instance clos_trans_1n_proper_iff {A: Type} (R: relation A)
  (E: relation A)
  {SYM_E: Symmetric E}
  {REFL_E: Reflexive E}
  (PR: Proper (E ==> E ==> iff) R):
  Proper (E ==> E ==> iff) (clos_trans_1n _ R).
Proof using.
  red.
  assert (Proper (E ==> E ==> impl) R).
  { intros ???????. symmetry in H, H0. 
    eapply PR; eauto. }
  intros x1 x2 Ex y1 y2 Ey. split; intros. 
  - eapply clos_trans_1n_proper_impl; eauto. 
  - symmetry in Ex, Ey. eapply clos_trans_1n_proper_impl; eauto.
Qed. 

(* (* TODO: move *) *)
(* Global Instance clos_trans_n1_proper_impl {A: Type} (R: relation A) *)
(*   (E: relation A) *)
(*   {REFL_E: Reflexive E} *)
(*   (PR: Proper (E ==> E ==> impl) R): *)
(*   Proper (E ==> E ==> impl) (clos_trans_n1 _ R). *)
(* Proof using. *)
(*   red. intros x1 x2 Ex y1 y2 Ey. intros TR. *)
(*   generalize dependent x2. generalize dependent y2. *)
(*   induction TR. *)
(*   + intros. econstructor. eapply PR; [..| apply H]; done. *)
(*   + intros y2 Ez x2 Ex. *)
(*     rename x into x1. *)
(*     rename y2 into z2. rename z into z1. *)
(*     rename y into y1. *)
(*     eapply PR in H; eauto.      *)
(*     specialize (IHTR _ Ez). *)
(*     specialize (IHTR _ ltac:(reflexivity)). *)
(*     eapply t1n_trans; eauto. *)
(* Qed. *)

(* (* TODO: move *) *)
(* Global Instance clos_trans_n1_proper_iff {A: Type} (R: relation A) *)
(*   (E: relation A) *)
(*   {SYM_E: Symmetric E} *)
(*   {REFL_E: Reflexive E} *)
(*   (PR: Proper (E ==> E ==> iff) R): *)
(*   Proper (E ==> E ==> iff) (clos_trans_n1 _ R). *)
(* Proof using. *)
(*   red. *)
(*   assert (Proper (E ==> E ==> impl) R). *)
(*   { intros ???????. symmetry in H, H0.  *)
(*     eapply PR; eauto. } *)
(*   intros x1 x2 Ex y1 y2 Ey. split; intros.  *)
(*   - eapply clos_trans_n1_proper_impl; eauto. *)
(*   - symmetry in Ex, Ey. eapply clos_trans_1n_proper_impl; eauto. *)
(* Qed.  *)

Lemma clos_trans_tn1_t1n_iff {A : Type} (R : relation A) (x y : A):
  clos_trans_n1 A R x y ↔ clos_trans_1n A R x y.
Proof using.
  by rewrite -Operators_Properties.clos_trans_t1n_iff Operators_Properties.clos_trans_tn1_iff.
Qed. 

(* Lemma clos_trans_n1_opt {A: Type} (R: relation A) x y z *)
(*   (CR1': clos_trans_n1 _ R x y \/ x = y) *)
(*   (R2: R y z): *)
(*   clos_trans_n1 _ R x z. *)
(* Proof using. *)
(*   destruct CR1'. *)
(*   - eapply tn1_trans; eauto. *)
(*   - subst. eapply tn1_step; eauto. *)
(* Qed.  *)
                        

(* (* TODO: move *) *)
(* Global Instance clos_refl_proper_iff {A: Type} (R: relation A) *)
(*   (E: relation A) *)
(*   {SYM_E: Symmetric E} *)
(*   {TRANS_E: Transitive E} *)
(*   (PR: Proper (E ==> E ==> iff) R): *)
(*   Proper (E ==> E ==> iff) (clos_refl _ R). *)
(* Proof using. *)
(*   red. *)
(*   intros x1 x2 Ex y1 y2 Ey. split; intros. *)
(*   - inversion H; subst. *)
(*     + left. eapply PR; eauto. *)
(*     + left. symmetry in Ex, Ey. *)
(*       eapply PR; [apply Ex| ..]; eauto. *)
(*   - inversion H; subst. *)
(*     + clear REFL_E. left. eapply PR; eauto. *)
(*     + left.  *)
(*       eapply PR; [apply Ex| ..]; eauto. *)
(* Qed.  *)

Section GmultisetLtWf.
  Context `{Countable A}. 
  Context (R: relation A).
  Context {PO: PartialOrder R}.

  Let llt := (@lt_ext1 A (strict R)).
  Definition lt_ext: relation (list A) := clos_trans_1n _ llt. 

  Lemma lt_ext_wf: wf lt_ext.
  Proof using. Admitted.

  Lemma lt_ext1_frame (L B D: list A)
    (LT: llt L B):
    llt (L ++ D) (B ++ D).
  Proof using.
    inversion LT.
    eapply lt_ext1_intro with (x := x) (X := X ++ D) (Y := Y); eauto.
    - rewrite H0. by rewrite app_assoc.
    - by rewrite H1.
  Qed.

  Lemma lt_ext_frame L B D
    (LT: lt_ext L B):
    lt_ext (L ++ D) (B ++ D).
  Proof using.
    pattern L, B.
    eapply clos_trans_1n_ind; [..| apply LT]; clear dependent L B.
    { intros. apply t1n_step. by apply lt_ext1_frame. }
    intros L M B LT1_LM LT_MB IH.
    apply lt_ext1_frame with (D := D) in LT1_LM.
    eapply t1n_trans; eauto.
  Qed.

  (* TODO: move *)
  Lemma empty_dominates_over (L: gmultiset A)
    (DOM: dominates_over R ∅ L):
    L = ∅.
  Proof using.
    clear PO. 
    destruct (decide (L = ∅)) as [| NE]; [done| ].
    apply gmultiset_choose in NE as [a IN].
    specialize (DOM _ IN). set_solver.
  Qed.

  Lemma lt_ext1_cons a l:
    llt l (a :: l).
  Proof using.
    eapply lt_ext1_intro with (Y := []); eauto; done.
  Qed.

  Lemma dominates_over_1 x Y:
    dominates_over R {[+ x +]} Y <-> llt (elements Y) [x].
  Proof using.
    clear PO. 
    rewrite /dominates_over /llt. split.
    - intros. eapply lt_ext1_intro with (X := nil).
      + by rewrite app_nil_r.
      + reflexivity.
      + intros. apply elem_of_list_In in H1.
        rewrite gmultiset_elem_of_elements in H1. set_solver.
    - intros [?] **. eexists. split.
      { apply gmultiset_elem_of_singleton. reflexivity. }
      destruct X.
      2: { apply Permutation_length_1_inv in H1. done. }
      apply Permutation_length_1 in H1. subst.
      rewrite app_nil_r in H0.
      apply H2. apply elem_of_list_In. rewrite -H0.
      by apply gmultiset_elem_of_elements.
  Qed. 

  (* Lemma lt_ext1_extend (L B: list A) (l b: A) *)
  (*   (LT: llt L B) *)
  (*   (Rlb: R l b) *)
  (*   (INb: b ∈ B): *)
  (*   llt (l :: L) B. *)
  (* Proof using. *)
  (*   inversion LT. *)
  (*   destruct (decide (x = b)) as [-> | NEQ]. *)
  (*   - eapply lt_ext1_intro with (x := x) (X := X ++ D) (Y := Y); eauto. *)


  (*   eapply lt_ext1_intro with (x := x) (X := X ++ D) (Y := Y); eauto. *)
  (*   - rewrite H0. by rewrite app_assoc. *)
  (*   - by rewrite H1. *)
  (* Qed. *)


  (* TODO: move *)
  Definition flatten_mset `{Countable K} (ss: gmultiset (gmultiset K)): gmultiset K :=
    list_to_set_disj (concat (map elements (elements ss))).

  Lemma flatten_mset_spec `{Countable K} ss:
    forall (k: K), k ∈ flatten_mset ss <-> exists s, s ∈ ss /\ k ∈ s.
  Proof.
    intros. rewrite /flatten_mset.
    rewrite elem_of_list_to_set_disj. 
    rewrite elem_of_list_In in_concat.
    setoid_rewrite in_map_iff. 
    repeat setoid_rewrite <- elem_of_list_In.
    split.
    - intros (?&(l&<-&?)&?).
      apply gmultiset_elem_of_elements in H1, H2. 
      eauto. 
    - intros (s&?&?). exists (elements s).
      split; [eexists; split| ]; eauto; by apply gmultiset_elem_of_elements. 
  Qed.

  Lemma flatten_mset_empty `{Countable K}: flatten_mset (∅: gmultiset (gmultiset K)) = ∅.
  Proof using. mss. Qed. 

  (* Lemma flatten_mset_disj_union `{Countable K} (S1 S2: gset (gmultiset K)): *)
  (*   flatten_mset (S1 ⊎ S2) = flatten_mset S1 ⊎ flatten_mset S2. *)
  (* Proof. *)
  (*   rewrite /flatten_gset. set_solver. *)
  (* Qed.  *)

  (* TODO: move*)
  Lemma list_to_set_disj_elements `{Countable K} (g: gmultiset K):
    list_to_set_disj (elements g) = g.
  Proof using.
    clear.
    pattern g. apply gmultiset_ind; clear g.
    { simpl. done. }
    intros a g EQ. rewrite gmultiset_elements_disj_union.
    rewrite gmultiset_elements_singleton.
    rewrite list_to_set_disj_app. mss.
  Qed.

  (* TODO: move*)
  Lemma elements_list_to_set_disj `{Countable K} (l: list K):
    elements $ (list_to_set_disj l: gmultiset K) ≡ₚ l.
  Proof using.
    clear. induction l.
    { done. }
    simpl. rewrite gmultiset_elements_disj_union.
    simpl. rewrite gmultiset_elements_singleton.
    rewrite IHl. done.
  Qed. 

  Lemma flatten_mset_singleton `{Countable K} (S: gmultiset K):
    flatten_mset {[+ S +]} = S. 
  Proof.
    rewrite /flatten_mset.
    rewrite gmultiset_elements_singleton. simpl. rewrite app_nil_r.
    apply list_to_set_disj_elements. 
  Qed.

  Section MapImgMs.
    Context `{Countable K, Countable A}.

    Definition map_img_ms (m: gmap K (gmultiset A)): gmultiset A :=
      list_to_set_disj $ concat ((elements ∘ snd) <$> (map_to_list m)).

    Lemma map_img_ms_empty: map_img_ms ∅ = ∅.
    Proof using. mss. Qed.

    Lemma gmultiset_elements_equiv (m1 m2: gmultiset A):
      m1 = m2 <-> elements m1 ≡ₚ elements m2.
    Proof using.
      clear dependent R.
      split; [set_solver| ].
      revert m2. pattern m1. apply gmultiset_ind; clear m1.
      { intros. rewrite gmultiset_elements_empty in H2.
        apply Permutation_nil in H2.
        by apply gmultiset_elements_empty_inv in H2. }
      intros k aa IH m2 EQUIV.
      rewrite gmultiset_elements_disj_union in EQUIV.
      rewrite gmultiset_elements_singleton in EQUIV. simpl in EQUIV.
      assert (k ∈ m2) as IN.
      { apply (elem_of_Permutation_proper k), proj1 in EQUIV.
        specialize (EQUIV ltac:(left)). by apply gmultiset_elem_of_elements. }
      apply gmultiset_disj_union_difference' in IN.
      rewrite IN in EQUIV.
      rewrite gmultiset_elements_disj_union in EQUIV.
      rewrite gmultiset_elements_singleton in EQUIV. simpl in EQUIV.
      apply Permutation_cons_inv in EQUIV.
      specialize (IH _ EQUIV). rewrite IH. mss.
    Qed.

    Lemma map_img_ms_multiplicity m a:
      multiplicity a (map_img_ms m) = map_fold (fun _ v acc => multiplicity a v + acc) 0 m.
    Proof using.
      pattern m. apply map_ind; clear m.
      { rewrite map_img_ms_empty. rewrite map_fold_empty. done. }
      intros b vv m FRESH IH.
      rewrite /map_img_ms.
      rewrite map_to_list_insert; [| done]. simpl.
      rewrite list_to_set_disj_app multiplicity_disj_union.
      rewrite IH.
      rewrite map_fold_insert_L; [..| done].
      2: { lia. }
      by rewrite list_to_set_disj_elements.
    Qed. 

  (* TODO: move *)
  Lemma map_split `{Countable K} {V: Type} (m: gmap K V) k:
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

    Lemma gmultiset_union_disj_union (X Y: gmultiset A)
      (DISJ: X ## Y):
      X ∪ Y = X ⊎ Y.
    Proof using. clear -DISJ. mss. Qed.

    (* TODO: move *)
    Lemma map_fold_union `{Countable K}
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
      rewrite map_fold_insert_L.
      3: { done. }
      2: { done. }
      done.
    Qed. 

    Lemma map_img_ms_union m1 m2
      (DISJ: m1 ##ₘ m2):
      map_img_ms (m1 ∪ m2) = map_img_ms m1 ⊎ map_img_ms m2.
    Proof using.
      apply gmultiset_eq. intros.
      rewrite multiplicity_disj_union.
      rewrite !map_img_ms_multiplicity.
      rewrite map_fold_union; try done.
      2: { lia. }
      remember (map_fold (λ (_ : K) (v : gmultiset A) (acc : nat), multiplicity x v + acc) 0 m1) as t.
      clear -m2. pattern m2. apply map_ind; clear m2.
      { rewrite !map_fold_empty. lia. }
      intros. rewrite !map_fold_insert_L; done || lia.
    Qed.

    Lemma map_img_ms_singleton k g:
      map_img_ms {[k := g]} = g.
    Proof using.
      rewrite /map_img_ms. simpl. rewrite map_to_list_singleton.
      simpl. rewrite app_nil_r. apply list_to_set_disj_elements.
    Qed. 

    Lemma map_img_ms_insert k aa m:
      map_img_ms (<[ k := aa ]> m) = map_img_ms m ∖ default ∅ (m !! k) ⊎ aa.
    Proof using.
      clear R PO llt. 
      apply gmultiset_eq. intros a.
      rewrite {1 2}(map_split m k).
      rewrite !insert_union_l. 
      rewrite !map_img_ms_union.
      2: { apply map_disjoint_dom. destruct lookup; set_solver. }
      2: { apply map_disjoint_dom. destruct lookup; set_solver. }
      rewrite !multiplicity_disj_union.
      replace (map_img_ms (from_option (singletonM k) ∅ (m !! k))) with (default ∅ (m !! k)).
      2: { destruct lookup; try set_solver. simpl.
           symmetry. apply map_img_ms_singleton. }
      rewrite gmultiset_cancel_l2. 
      destruct lookup; simpl.
      - rewrite insert_singleton. rewrite map_img_ms_singleton. lia.
      - rewrite insert_empty. rewrite map_img_ms_singleton. lia.
   Qed.      
    
  End MapImgMs.


  Definition g2m (g: gset A): gmultiset A := list_to_set_disj $ elements g. 

  Lemma g2m_empty: g2m ∅ = ∅.
  Proof using. mss. Qed.

  Lemma g2m_elements g: elements (g2m g) ≡ₚ elements g.
  Proof using.
    rewrite /g2m. by rewrite elements_list_to_set_disj.
  Qed.     

  (* TODO: move *)
  Lemma dominates_over_empty (X: gmultiset A):
    dominates_over R X ∅.
  Proof using. clear. set_solver. Qed.

  (* Lemma lt_ext_a L1 B1 L2 B2 *)
  (*   (LT1: lt_ext L1 B1) *)
  (*   (LT2: lt_ext L2 B2): *)
  (*   lt_ext (L1 ++ B1) (L2 ++ B2). *)
  (* Proof using. *)
  (* lt_ext *)

  Definition mmap_disj `{Countable K, Countable V} (tm: gmap K (gmultiset V)) :=
    forall (k1 k2: K) (S1 S2: gmultiset V) (NEQ: k1 ≠ k2),
      tm !! k1 = Some S1 -> tm !! k2 = Some S2 -> S1 ## S2.

  Definition clos_refl_perm R: relation (list A) :=
    (Relation_Operators.union _ R (@Permutation A)). 


  Lemma build_steps (U: gmap A (gmultiset A))
    (DOM1: forall b, dominates_over R {[+ b +]} (default ∅ (U !! b)))
    (DISJ: mmap_disj U):
    clos_refl_perm lt_ext 
      (elements $ map_img_ms U)
      (elements $ dom U)
  .
  Proof using.
    revert DOM1 DISJ. pattern U. apply map_ind; clear U.  
    { rewrite dom_empty_L map_img_ms_empty. by right. }
    intros b aa U FRESH IH DOM DISJ.
    rewrite map_img_ms_insert. 
    
    rewrite dom_insert_L.
    rewrite /clos_refl_perm /Relation_Operators.union. 
    rewrite elements_union_singleton.
    2: { by apply not_elem_of_dom. }

    assert (∀ b, dominates_over R {[+ b +]} (default ∅ (U !! b))).
    { intros b'. destruct (U !! b') as [aa'| ] eqn:B'; simpl. 
      2: { apply dominates_over_empty. }
      specialize (DOM b'). rewrite lookup_insert_ne in DOM; [| intros ->; congruence].
      by rewrite B' in DOM. }
    
    assert (mmap_disj U).
    { red. intros. eapply DISJ; [apply NEQ| ..]; rewrite lookup_insert_ne; eauto; intros ->; congruence. }

    left. 
    specialize (IH ltac:(eauto) ltac:(eauto)).
    eapply clos_trans_1n_proper_iff.
    3: by apply lt_ext1_morphism.
    1, 2: by apply _.
    { red. rewrite gmultiset_elements_disj_union. 
      apply Permutation_app_comm. }
    { reflexivity. }
    apply clos_trans_tn1_t1n_iff. 

    assert (llt (elements aa) [b]).
    { specialize (DOM b). red in DOM. rewrite lookup_insert in DOM. simpl in DOM.
      by apply dominates_over_1. }
    assert (llt (elements (aa) ++ elements (dom U)) (b :: elements (dom U))).
    { replace (b :: elements (dom U)) with ([b] ++ elements (dom U)) by done. 
      by apply lt_ext1_frame. }

    rewrite FRESH. simpl. rewrite gmultiset_difference_empty. 

    red in IH. destruct IH.
    - eapply tn1_trans; eauto.
      apply clos_trans_tn1_t1n_iff.
      do 2 rewrite (Permutation_app_comm (elements aa)).
      eapply lt_ext_frame; eauto.
    - eapply tn1_step. rewrite H4. 
      replace (b :: elements (dom U)) with ([b] ++ elements (dom U)) by done.
      by apply lt_ext1_frame.
  Qed.

  Global Instance lt_ext_trans: Transitive lt_ext.
  Proof using.
    red. intros ???.
    rewrite /lt_ext. 
    rewrite -!Operators_Properties.clos_trans_t1n_iff.
    intros. eapply t_trans; eauto.
  Qed. 

  Global Instance clos_refl_perm_lt_ext_trans:
    Transitive (clos_refl_perm lt_ext).
  Proof using.
    red. rewrite /clos_refl_perm /Relation_Operators.union. intros.
    destruct H0, H1. 
    - left. etrans; eauto.
    - left. by rewrite -H1. 
    - left. by rewrite H0.
    - right. etrans; eauto.
  Qed.

  Lemma lt_ext_crt_subseteq (X Y: gmultiset A)
    (SUB: X ⊆ Y):
    clos_refl_perm lt_ext (elements X) (elements Y).
  Proof using.
    apply gmultiset_disj_union_difference in SUB. remember (Y ∖ X) as D.
    clear HeqD. subst. pattern D. apply gmultiset_ind; clear D.
    { rewrite gmultiset_disj_union_right_id. by right. }
    intros. etrans; eauto.
    rewrite (gmultiset_disj_union_comm {[+ _ +]}). rewrite gmultiset_disj_union_assoc.
    left. apply t1n_step.  
    rewrite (gmultiset_elements_disj_union _ {[+ _ +]}) gmultiset_elements_singleton.
    rewrite Permutation_app_comm. simpl.
    apply lt_ext1_cons.
  Qed.

  Lemma g2m_multiplicity g a:
    multiplicity a (g2m g) = if (decide (a ∈ g)) then 1 else 0.
  Proof using.
    clear llt R PO. 
    rewrite /g2m.
    destruct (decide (a ∈ g)).
    - assert (g = {[ a ]} ∪ g ∖ {[ a ]}).
      { apply set_eq. intros.
        rewrite elem_of_union elem_of_singleton elem_of_difference.
        destruct (decide (x ∈ g)), (decide (x = a)); subst; set_solver. }
      rewrite H0. rewrite elements_disj_union; [| set_solver].
      rewrite list_to_set_disj_app. rewrite multiplicity_disj_union.
      rewrite elements_singleton. simpl. rewrite gmultiset_disj_union_right_id.
      rewrite multiplicity_singleton. 
      rewrite (proj1 (not_elem_of_multiplicity _ _)); [lia| ].
      rewrite elem_of_list_to_set_disj. set_solver.
    - rewrite (proj1 (not_elem_of_multiplicity _ _)); [lia| ].
      rewrite elem_of_list_to_set_disj. set_solver.
  Qed.
      
  Lemma gmultiset_disjoint_symm (X Y: gmultiset A):
    X ## Y <-> Y ## X.
  Proof using. clear llt R PO. mss. Qed.

  Lemma disj_union_disjoint (X Y Z: gmultiset A):
    X ⊎ Y ## Z <-> X ## Z /\ Y ## Z.
  Proof using. clear llt R PO. mss. Qed.

  Lemma gmultiset_singleton_disjoint (X: gmultiset A) (a: A):
    {[+ a +]} ## X <-> a ∉ X. 
  Proof using. clear llt R PO. mss. Qed.

  Lemma dominates_over_lt_ext_crt L B
    (* (DISJ: L ## B) *)
    (DOM: dominates_over R B L):
    clos_refl_perm lt_ext (elements L) (elements B).
  Proof using.
    assert (exists (ds: gmap A (gmultiset A)), dom ds ⊆ dom B /\ map_img_ms ds = L /\ (forall b, dominates_over R {[+ b +]} (default ∅ (ds !! b))) /\ mmap_disj ds) as (ds & SUB_B & IMG & DOMds & DISJ). 
     { clear -DOM.
      revert DOM. pattern L. apply gmultiset_ind; clear L.
      { intros. exists ∅. repeat split; try set_solver. done. }
      intros a L IH DOM'.
      assert (dominates_over R B L).
      { red. intros. eapply DOM'. set_solver. }
      specialize (IH ltac:(eauto)).
      
      destruct IH as (ds & SUB & IMG & DOM & DISJ).
      destruct (decide (map_Exists (fun k v => a ∈ v) ds)).
      2: { 
        red in DOM'. specialize (DOM' a ltac:(mss)). destruct DOM' as (b & Bb & Rab).
        exists (<[ b := default ∅ (ds !! b) ⊎ {[+ a +]} ]> ds).
        repeat split.
        - rewrite dom_insert_L. apply union_subseteq. split; auto.
        apply singleton_subseteq_l. by apply gmultiset_elem_of_dom.
        - rewrite map_img_ms_insert.
          rewrite IMG.
          destruct lookup eqn:DSb; simpl; [| mss].
          enough (g ⊆ L).
          { mss. }
          subst L. rewrite {1}(map_split ds b). rewrite DSb. simpl.
          rewrite map_img_ms_union.
          2: { apply map_disjoint_dom; set_solver. }
          rewrite map_img_ms_singleton. mss.
        - intros c. red. intros v.
          destruct (decide (c = b)) as [-> | NEQ].
          { rewrite lookup_insert. simpl.
            rewrite gmultiset_elem_of_disj_union.
            repeat setoid_rewrite gmultiset_elem_of_singleton.
            intros [IN | ->]; eexists; split; eauto. 
            destruct (ds !! b) eqn:DSb; [| set_solver].
            simpl in IN.
            specialize (DOM b). rewrite DSb in DOM. simpl in DOM.
            red in DOM. specialize (DOM _ IN). set_solver. }
          rewrite lookup_insert_ne; [| done].
          setoid_rewrite gmultiset_elem_of_singleton.
          intros IN; eexists; split; eauto. 
          destruct (ds !! c) eqn:DSc; [| set_solver].
          simpl in IN.
          specialize (DOM c). rewrite DSc in DOM. simpl in DOM.
          red in DOM. specialize (DOM _ IN). set_solver.
        - red. intros ?????.
          assert (forall k Sk, k ≠ b -> ds !! k = Some Sk -> default ∅ (ds !! b) ## Sk).
          { intros. destruct (ds !! b) eqn:DSb; simpl; [| mss].
            eapply DISJ; [apply not_eq_sym| ..]; eauto. } 
        
          destruct (decide (k1 = b)), (decide (k2 = b)); subst; try done. 
          all: try rewrite lookup_insert; simpl.
          all: repeat try (rewrite lookup_insert_ne; [| done]).
          + intros [=] ?. subst. apply disj_union_disjoint. split; eauto.
            apply gmultiset_singleton_disjoint. intros ?.
            destruct n. eexists. eauto.
          + intros ? [=]. subst. apply gmultiset_disjoint_symm.
            apply disj_union_disjoint. split; eauto.
            apply gmultiset_singleton_disjoint. intros ?.
            destruct n. eexists. eauto.
          + intros. eapply DISJ; [apply NEQ| ..]; eauto. }

      destruct m as (b & aas & DSb & INa).
      exists (<[ b := aas ⊎ {[+ a +]} ]> ds).
        repeat split.
        - rewrite dom_insert_L. apply union_subseteq. split; auto.
          apply singleton_subseteq_l.
          apply SUB. eapply elem_of_dom; eauto. 
        - rewrite map_img_ms_insert.
          rewrite IMG. rewrite DSb. simpl.  
          enough (aas ⊆ L).
          { mss. }
          subst L. rewrite {1}(map_split ds b). rewrite DSb. simpl.
          rewrite map_img_ms_union.
          2: { apply map_disjoint_dom; set_solver. }
          rewrite map_img_ms_singleton. mss.
        - intros c. red. intros v.
          destruct (decide (c = b)) as [-> | NEQ].
          { rewrite lookup_insert. simpl.
            rewrite gmultiset_elem_of_disj_union.
            repeat setoid_rewrite gmultiset_elem_of_singleton.
            intros [IN | ->]; eexists; split; eauto.
            + simpl in IN.
              specialize (DOM b). rewrite DSb in DOM. simpl in DOM.
              red in DOM. specialize (DOM _ IN). set_solver.
            + specialize (DOM b). rewrite DSb in DOM. simpl in DOM.
              red in DOM. specialize (DOM _ INa). set_solver. }
          rewrite lookup_insert_ne; [| done].
          setoid_rewrite gmultiset_elem_of_singleton.
          intros IN; eexists; split; eauto. 
          destruct (ds !! c) eqn:DSc; [| set_solver].
          simpl in IN.
          specialize (DOM c). rewrite DSc in DOM. simpl in DOM.
          red in DOM. specialize (DOM _ IN). set_solver.
        - red. intros ?????.
          assert (forall k Sk, k ≠ b -> ds !! k = Some Sk -> aas ## Sk).
          { intros. eapply DISJ; [apply not_eq_sym| ..]; eauto. } 
          assert (forall k Sk, k ≠ b -> ds !! k = Some Sk -> a ∈ Sk -> False).
          { mss. } 
        
          destruct (decide (k1 = b)), (decide (k2 = b)); subst; try done. 
          all: try rewrite lookup_insert; simpl.
          all: repeat try (rewrite lookup_insert_ne; [| done]).
          + intros [=] ?. subst. apply disj_union_disjoint. split; eauto.
            apply gmultiset_singleton_disjoint. intros ?. eauto. 
          + intros ? [=]. subst. apply gmultiset_disjoint_symm.
            apply disj_union_disjoint. split; eauto.
            apply gmultiset_singleton_disjoint. intros ?. eauto. 
          + intros. eapply DISJ; [apply NEQ| ..]; eauto. }
    rewrite -IMG. etrans. 
    { by apply build_steps. }
    trans (elements $ g2m (dom ds)). 
    2: { apply lt_ext_crt_subseteq.         
         do 2 red. intros. rewrite g2m_multiplicity.
         destruct (decide (elem_of _ _)); [| lia].
         apply SUB_B in e. apply gmultiset_elem_of_dom in e.
         rewrite elem_of_multiplicity in e. lia. }         
         
    right. rewrite g2m_elements. done.
  Qed. 

  Lemma ms_lt_ext X Y
    (LT: ms_lt R X Y):
    lt_ext (elements X) (elements Y).
  Proof using PO.
    apply strict_spec_alt in LT as [LE NEQ].
    apply ms_le_equiv' in LE; [| done].
    red in LE. destruct LE as (B & L & IN & -> & DOM).
    apply gmultiset_disj_union_difference in IN.
    remember (Y ∖ B) as D. clear HeqD. subst Y.
    assert (L ≠ B) as NEQ' by mss. clear NEQ.
    rewrite gmultiset_disj_union_comm.
    rewrite !gmultiset_elements_disj_union. apply lt_ext_frame.

    apply dominates_over_lt_ext_crt in DOM. destruct DOM; eauto.
    destruct NEQ'. eapply gmultiset_elements_equiv; eauto. 
  Qed.

  Theorem ms_lt_wf (WF: wf (strict R)):
    wf (ms_lt R).
  Proof using PO.
    eapply wf_projected with (f := elements); [| apply lt_ext_wf].
    intros. by apply ms_lt_ext.
  Qed. 


End GmultisetLtWf.
