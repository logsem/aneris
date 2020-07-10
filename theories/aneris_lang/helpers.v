From stdpp Require Export gmap.

Section map_Filter.
  Context `{FinMap K M}.
  Context {A} (P : K * A → Prop) `{!∀ x, Decision (P x)}.
  Implicit Types m : M A.

  Lemma map_filter_lookup_None_insert i x m:
    filter P m !! i = None →
    ¬ P (i,x) →
    filter P (<[i:=x]> m) = filter P m.
  Proof.
    intros HNone Hneg.
    apply map_eq. intros j. apply option_eq; intros y.
    destruct (decide (j = i)) as [->|?].
    - split; intro.
      + rewrite map_filter_lookup_Some in H8. destruct H8 as [? Hc].
        rewrite lookup_insert in H8; simplify_eq. contradiction.
      + rewrite H8 in HNone. simplify_eq.
    - by rewrite !map_filter_lookup_Some, lookup_insert_ne.
  Qed.

End map_Filter.

Section fin_map_dom.
  Context `{FinMapDom K M D}.
  Context `{!LeibnizEquiv D}.

  Lemma dom_insert_Some {A} (m : M A) i (x y : A) :
    m !! i = Some x →
    dom D (<[i:=y]> m) = dom D m.
  Proof.
    intros.
    rewrite dom_insert_L.
    apply subseteq_union_1_L, elem_of_subseteq_singleton,
    elem_of_dom; eauto.
  Qed.

End fin_map_dom.
