From stdpp Require Export sets. 
From iris.proofmode Require Import tactics.


Section GsetProd.
  Context `{Countable K, Countable T}. 

  Fixpoint list_prod (ks: list K) (ts: list T): list (K * T) :=
    match ks with 
    | [] => []
    | k :: ks => map (pair k) ts ++ list_prod ks ts
    end.

  Lemma list_prod_spec (ks: list K) (ts: list T):
    forall k t, (k, t) ∈ list_prod ks ts <-> k ∈ ks /\ t ∈ ts.
  Proof using.
    induction ks.
    { intros. set_solver. }
    intros. simpl. rewrite elem_of_app elem_of_cons.
    rewrite IHks.
    rewrite elem_of_list_In in_map_iff. setoid_rewrite <- elem_of_list_In.
    set_solver.
  Qed. 

  Definition gset_prod (k: gset K) (t: gset T): gset (K * T) :=
    list_to_set (list_prod (elements k) (elements t)). 

  Lemma gset_prod_spec (k: gset K) (t: gset T):
    forall p, p ∈ gset_prod k t <-> p.1 ∈ k /\ p.2 ∈ t.
  Proof using.
    intros [??]. rewrite /gset_prod.
    rewrite elem_of_list_to_set. rewrite list_prod_spec.
    by rewrite !elem_of_elements.
  Qed. 

End GsetProd.

