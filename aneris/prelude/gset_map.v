From Coq.ssr Require Import ssreflect.
From stdpp Require Import gmap functions.

(* TODO: outphase this; [set_map] already exists in std++, a few lemmas need
   upstreaming *)
Section gset_map.
  Context `{EqDecision A, !Countable A, !EqDecision B, !Countable B}.

  Definition gset_map (f : A → B) (g : gset A) : gset B :=
    list_to_set (f <$> elements g).

  Lemma gset_map_empty f : gset_map f ∅ = ∅.
  Proof. by rewrite /gset_map elements_empty /=. Qed.

  Lemma gset_map_singleton f a : gset_map f {[a]} = {[f a]}.
  Proof. by rewrite /gset_map elements_singleton /= right_id_L. Qed.

  Lemma gset_map_union f g g' :
    gset_map f (g ∪ g') = gset_map f g ∪ gset_map f g'.
  Proof.
    revert g'.
    pattern g.
    match goal with |- ?F g => simpl; apply (set_ind_L F) end; set_solver.
  Qed.

  Lemma gset_map_not_elem_of f g `{!Inj (=) (=) f} :
    ∀ a, a ∉ g → (f a) ∉ gset_map f g.
  Proof.
    pattern g.
    match goal with |- ?F g => simpl; apply (set_ind_L F) end; set_solver.
  Qed.

  Lemma gset_map_correct1 f g : ∀ a, a ∈ g → (f a) ∈ gset_map f g.
  Proof.
    pattern g.
    match goal with |- ?F g => simpl; apply (set_ind_L F) end; set_solver.
  Qed.

  Lemma gset_map_correct2 f g : ∀ b, b ∈ gset_map f g → ∃ a, b = f a ∧ a ∈ g.
  Proof.
    pattern g.
    match goal with |- ?F g => simpl; apply (set_ind_L F) end; set_solver.
  Qed.

  Lemma gset_map_fn_insert_ne x f g y :
    x ∉ g → gset_map (<[x:=y]> f) g = gset_map f g.
  Proof.
    rewrite /gset_map. unfold_leibniz. intros ??.
    rewrite !elem_of_list_to_set !elem_of_list_fmap.
    split.
    - intros [? [H' ?%elem_of_elements]].
      rewrite fn_lookup_insert_ne in H'; set_solver.
    - intros [x' [? ?%elem_of_elements]]. exists x'.
      rewrite fn_lookup_insert_ne; set_solver.
  Qed.

  (* TODO: upstream? *)
  Lemma gset_map_intersection f `{!Inj (=) (=) f} X Y :
    gset_map f (X ∩ Y) = gset_map f X ∩ gset_map f Y.
  Proof. set_solver. Qed.

  (* TODO: upstream? *)
  Lemma gset_map_size X f `{!Inj (=) (=) f} :
    size (gset_map f X) = size X.
  Proof.
    induction X using set_ind_L; [done|].
    rewrite gset_map_union gset_map_singleton.
    rewrite !size_union; [set_solver|set_solver|].
    rewrite IHX !size_singleton //.
  Qed.

  Lemma gset_map_disj_union X Y f `{!Inj (=) (=) f} :
    X ## Y →
    gset_map f X ## gset_map f Y.
  Proof. set_solver. Qed.

  Lemma gset_map_const_nonempty X f y :
    X ≠ ∅ → (∀ x, x ∈ X → f x = y) → gset_map f X = {[y]}.
  Proof.
    move=> + Hf.
    induction X using set_ind_L; [done|].
    intros ?.
    rewrite gset_map_union gset_map_singleton Hf; [set_solver|].
    destruct (decide (X = ∅)); simplify_eq.
    { rewrite gset_map_empty union_empty_r_L //. }
    rewrite IHX //; set_solver.
  Qed.

End gset_map.

Section gset_flat_map.
  Context `{EqDecision A, !Countable A, !EqDecision B, !Countable B}.

  Definition gset_flat_map (f : A → gset B) (g : gset A) : gset B :=
    ⋃ elements (gset_map f g).

  Lemma gset_flat_map_empty f : gset_flat_map f ∅ = ∅.
  Proof. by rewrite /gset_flat_map elements_empty. Qed.

  Lemma elem_of_gset_flat_map_1 f g a b :
    a ∈ g → b ∈ f a → b ∈ gset_flat_map f g.
  Proof.
    intros ??. rewrite /gset_flat_map elem_of_union_list.
    exists (f a). rewrite elem_of_elements.
    split; [|done].
    by apply gset_map_correct1.
  Qed.

  Lemma gset_flat_map_union f X Y `{!Inj (=) (=) f} :
    X ## Y →
    gset_flat_map f (X ∪ Y) = gset_flat_map f X ∪ gset_flat_map f Y.
  Proof.
    intros Hdisj.
    rewrite /gset_flat_map gset_map_union.
    rewrite elements_disj_union //; [by eapply gset_map_disj_union|].
    rewrite union_list_app_L //.
  Qed.

  Lemma elem_of_gset_flat_map_2 f g b :
    b ∈ gset_flat_map f g → ∃ a, a ∈ g ∧ b ∈ f a.
  Proof.
    rewrite /gset_flat_map elem_of_union_list.
    intros [b' [H%elem_of_elements%gset_map_correct2 ?]].
    destruct H as [? [-> ?]]. eauto.
  Qed.

  Lemma elem_of_gset_flat_map_fn_insert_1 f g a b X :
    a ∈ g →
    b ∈ X →
    b ∈ gset_flat_map (<[a := X]> f) g.
  Proof.
    intros ??. eapply elem_of_gset_flat_map_1; [done|].
    by rewrite fn_lookup_insert.
  Qed.

  Lemma elem_of_gset_flat_map_fn_insert_2 f g a b b' :
    b ∈ gset_flat_map f g →
    b ∈ gset_flat_map (<[a := {[b']} ∪ f a]> f) g.
  Proof.
    intros [a' [? ?]]%elem_of_gset_flat_map_2.
    eapply elem_of_gset_flat_map_1; [done|].
    destruct (decide (a = a')); simplify_eq.
    - rewrite fn_lookup_insert. set_solver.
    - rewrite fn_lookup_insert_ne //.
  Qed.

  Lemma gset_flat_map_insert_2_inv m m' f a X :
    m ∈ gset_flat_map (<[a:={[m']} ∪ f a]> f) X →
    m = m' ∨ m ∈ gset_flat_map f X.
  Proof.
    intros Hmap.
    apply elem_of_gset_flat_map_2 in Hmap as (a' & ? & Hin).
    destruct (decide (a = a')); simplify_eq.
    - rewrite fn_lookup_insert in Hin.
      apply elem_of_union in Hin as [?%elem_of_singleton_1 |]; [by left|].
      right. by eapply elem_of_gset_flat_map_1.
    - rewrite fn_lookup_insert_ne in Hin; [done|].
      right. by eapply elem_of_gset_flat_map_1.
  Qed.

  Lemma gset_flat_map_f_empty (f : A → gset B)  X :
    (∀ x, x ∈ X → f x = ∅) → gset_flat_map f X = ∅.
  Proof.
    induction X using set_ind_L.
    { intros ?. apply gset_flat_map_empty. }
    intros Hf.
    rewrite /gset_flat_map.
    rewrite gset_map_union gset_map_singleton.
    rewrite Hf; [set_solver|].
    destruct (decide (X = (∅ : gset A))); simplify_eq.
    { rewrite gset_map_empty. rewrite union_empty_r_L.
      rewrite elements_singleton union_list_singleton_L //. }
    rewrite (gset_map_const_nonempty _ _ ∅); [done|set_solver|].
    set_unfold; by intros ? [|].
  Qed.

End gset_flat_map.

Section elements.
  Context `{Countable A, Countable B}.

  (* TODO: upstream? *)
  Lemma elements_fmap (f : A → B) `{!Inj (=) (=) f} (X : gset A) :
    f <$> elements X ≡ₚ elements (gset_map f X).
  Proof.
    induction X using set_ind_L; [done|].
    rewrite gset_map_union.
    rewrite ?elements_disj_union.
    { set_solver. }
    { apply gset_map_disj_union; set_solver. }
    rewrite gset_map_singleton !elements_singleton.
    rewrite fmap_app list_fmap_singleton IHX //.
  Qed.

End elements.

Section fn_to_gmap.
  Context `{EqDecision A, !Countable A, B : Type}.

  Definition fn_to_gmap (X : gset A) (f : A → B) : gmap A B :=
    set_to_map (λ a, (a, f a)) X.

  Global Instance gmap_fn_inj (f : A → B) : Inj (=) (=) (λ a : A, (a, f a)).
  Proof. by intros ?? [=]. Qed.

  Lemma fn_to_gmap_dom (X : gset A) (f : A → B) : dom (fn_to_gmap X f) = X.
  Proof.
    rewrite /fn_to_gmap /= /set_to_map dom_list_to_map_L.
    apply set_eq; intros x.
    rewrite elem_of_list_to_set elem_of_list_fmap.
    setoid_rewrite elem_of_list_fmap. setoid_rewrite elem_of_elements.
    split.
    - by intros (?&?&?&?&?); subst.
    - intros; eexists (_,_); eauto.
  Qed.

  Lemma lookup_fn_to_gmap (x : A) (X : gset A) (f : A → B) (y : B) :
    fn_to_gmap X f !! x = Some y ↔ f x = y ∧ x ∈ X.
  Proof.
    rewrite /fn_to_gmap lookup_set_to_map //.
    split.
    - intros (?&?&?); simplify_eq; done.
    - intros [<- ?]; eauto.
  Qed.

  Lemma lookup_fn_to_gmap_1 (x : A) (X : gset A) (f : A → B) (y : B) :
    fn_to_gmap X f !! x = Some y → f x = y.
  Proof. apply lookup_fn_to_gmap. Qed.

  Lemma lookup_fn_to_gmap_2 (x : A) (X : gset A) (f : A → B) (y : B) :
    x ∈ X → f x = y → fn_to_gmap X f !! x = Some y.
  Proof. by intros; apply lookup_fn_to_gmap. Qed.

  Lemma lookup_fn_to_gmap_2' (x : A) (X : gset A) (f : A → B):
    x ∈ X → fn_to_gmap X f !! x = Some (f x).
  Proof. by intros; apply lookup_fn_to_gmap. Qed.

  Lemma lookup_fn_to_gmap_not_in (x : A) (X : gset A) (f : A → B) :
    x ∉ X ↔ fn_to_gmap X f !! x = None.
  Proof.
    rewrite /fn_to_gmap /set_to_map -not_elem_of_list_to_map.
    rewrite elem_of_list_fmap.
    setoid_rewrite elem_of_list_fmap. setoid_rewrite elem_of_elements.
    split.
    - by intros ? (?&?&?&?&?); simplify_eq/=.
    - intros Hnot ?; apply Hnot; eexists (_, _); eauto.
  Qed.

  Lemma lookup_fn_to_gmap_not_in1 (x : A) (X : gset A) (f : A → B) :
    x ∉ X → fn_to_gmap X f !! x = None.
  Proof. apply lookup_fn_to_gmap_not_in. Qed.

  Lemma lookup_fn_to_gmap_not_in2 (x : A) (X : gset A) (f : A → B) :
    fn_to_gmap X f !! x = None → x ∉ X.
  Proof. apply lookup_fn_to_gmap_not_in. Qed.

  Lemma fn_to_gmap_insert (x : A) (y : B) (X : gset A) (f : A → B) :
    x ∈ X → fn_to_gmap X (<[x:=y]>f) = <[x:=y]>(fn_to_gmap X f).
  Proof.
    intros ?. rewrite /fn_to_gmap.
    apply map_eq. intros x'.
    destruct (decide (x = x')) as [<-|].
    - rewrite lookup_insert lookup_set_to_map //.
      exists x. split; [done|]. f_equal.
      apply fn_lookup_insert.
    - rewrite lookup_insert_ne //.
      rewrite /set_to_map.
      destruct (decide (x' ∈ X)).
      + rewrite !(elem_of_list_to_map_1' _ x' (f x')) //; [| |set_solver..].
        * intros ? (?&?&?)%elem_of_list_fmap. simplify_eq.
          rewrite fn_lookup_insert_ne //.
        * apply elem_of_list_fmap. exists x'.
          rewrite fn_lookup_insert_ne; set_solver.
      + rewrite !not_elem_of_list_to_map_1; set_solver.
  Qed.

  Lemma fn_to_gmap_eq_fns (X : gset A) (f g : A → B) :
    (∀ x, x ∈ X → f x = g x) → fn_to_gmap X f = fn_to_gmap X g.
  Proof.
    intros Heq; apply map_eq; intros x.
    destruct (decide (x ∈ X)).
    - rewrite !lookup_fn_to_gmap_2'; [done|done|].
      rewrite Heq; done.
    - rewrite !lookup_fn_to_gmap_not_in1; done.
  Qed.

  Lemma const_fn_to_gmap (X : gset A) (f : A → B) (y : B) :
    (∀ x, f x = y) → fn_to_gmap X f = gset_to_gmap y X.
  Proof.
    intros Heq; apply map_eq; intros x.
    destruct (decide (x ∈ X)).
    - rewrite lookup_fn_to_gmap_2'; first done.
      rewrite Heq.
      rewrite lookup_gset_to_gmap option_guard_True; done.
    - rewrite lookup_fn_to_gmap_not_in1; first done.
      rewrite lookup_gset_to_gmap option_guard_False; done.
  Qed.

  Lemma fn_to_gmap_singleton (f : A → B) (x : A) :
    fn_to_gmap {[x]} f = {[x := f x]}.
  Proof.
    rewrite /fn_to_gmap /set_to_map.
    rewrite elements_singleton list_fmap_singleton //.
  Qed.

  Context `{Countable B}.

  Lemma fn_to_gmap_disj_union (f : A → B) (X Y : gset A) :
    X ## Y →
    fn_to_gmap (X ∪ Y) f = fn_to_gmap X f ∪ fn_to_gmap Y f.
  Proof.
    rewrite /fn_to_gmap /set_to_map => ?.
    rewrite -list_to_map_app.
    apply list_to_map_proper.
    { rewrite -list_fmap_compose.
      eapply NoDup_fmap; [by intros ??|].
      apply NoDup_elements. }
    rewrite elements_fmap gset_map_union.
    rewrite elements_disj_union.
    { apply gset_map_disj_union; [|set_solver]. apply _. }
    rewrite !elements_fmap //.
  Qed.

End fn_to_gmap.

Fixpoint list_to_gmap_go (i : nat) [A B] (f : A → B) (l : list A) : gmap nat B :=
  match l with
  | nil => ∅
  | a :: l' => <[i := f a]> (list_to_gmap_go (S i) f l')
  end.

Notation list_to_gmap := (list_to_gmap_go 0).

Section list_to_gmap.
  Context {A B} (f : A → B).

  Lemma list_to_gmap_go_nil i : list_to_gmap_go i f [] = ∅.
  Proof. done. Qed.

  Lemma list_to_gmap_nil : list_to_gmap f [] = ∅.
  Proof. done. Qed.

  Lemma list_to_gmap_go_cons i a l :
    list_to_gmap_go i f (a :: l) = <[i := f a]> (list_to_gmap_go (S i) f l).
  Proof. done. Qed.

  Lemma list_to_gmap_go_lookup i j l :
    i ≤ j → list_to_gmap_go i f l !! j = option_map f (l !! (j - i)).
  Proof.
    revert i j; induction l as [|a l IHl]; intros i j Hij.
    { rewrite /= lookup_empty //. }
    rewrite /=.
    destruct (decide (i = j)) as [->|].
    { rewrite Nat.sub_diag lookup_insert //. }
    rewrite lookup_insert_ne //.
    destruct (j - i) as [|k] eqn:Heq; first lia.
    replace k with (j - S i) by lia.
    apply IHl; lia.
  Qed.

  Lemma list_to_gmap_lookup j l : list_to_gmap f l !! j = option_map f (l !! j).
  Proof. rewrite -{2}(Nat.sub_0_r j); apply (list_to_gmap_go_lookup 0); lia. Qed.

  Lemma list_to_gmap_go_lookup_lt i j locs :
    j < i → list_to_gmap_go i f locs !! j = None.
  Proof.
    revert i j; induction locs as [|a l IHl]; intros i j Hij.
    { rewrite /= lookup_empty //. }
    rewrite /=.
    rewrite lookup_insert_ne; first lia.
    apply IHl; lia.
  Qed.

  Lemma list_to_gmap_go_insert i j l a :
    i ≤ j →
    j < i + length l →
    <[j := f a]> (list_to_gmap_go i f l) = list_to_gmap_go i f (<[j - i := a]>l).
  Proof.
    revert i j; induction l as [|b l IHl]; intros i j Hij Hj.
    { simpl in *; lia. }
    rewrite /=.
    destruct (decide (i = j)) as [->|].
    { rewrite insert_insert Nat.sub_diag //. }
    simpl in *.
    rewrite insert_commute; first lia.
    destruct (j - i) as [|k] eqn:Heq; first lia.
    replace k with (j - S i) by lia.
    rewrite /= IHl; [lia|lia|done].
  Qed.

  Lemma list_to_gmap_insert j a l :
    j < length l → <[j := f a]> (list_to_gmap f l) = list_to_gmap f (<[j := a]>l).
  Proof. rewrite -{3}(Nat.sub_0_r j); apply (list_to_gmap_go_insert 0); lia. Qed.

End list_to_gmap.

#[global] Instance gset_map_injective `{Countable K} `{Countable U}
         (f : K → U) `{Inj K U (=) (=) f} :
  Inj (=) (=) (gset_map f).
Proof.
  intros X Y Heq.
  apply set_eq.
  intros x.
  split; intros Hx.
  - apply (gset_map_correct1 f) in Hx.
    rewrite Heq in Hx.
    apply gset_map_correct2 in Hx as [a [Heq' Hx]].
    simplify_eq.
    done.
  - apply (gset_map_correct1 f) in Hx.
    rewrite -Heq in Hx.
    apply gset_map_correct2 in Hx as [a [Heq' Hx]].
    simplify_eq.
    done.
Qed.
Global Arguments list_to_gmap_go : simpl never.
