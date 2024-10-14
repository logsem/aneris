From stdpp Require Export sets. 
From iris.proofmode Require Import tactics.


Section GsetProd.
  Context `{Countable K, Countable T}. 

  (* TODO: move / find implementation *)
  Definition gset_prod (k: gset K) (t: gset T): gset (K * T).
  Admitted.

  Lemma gset_prod_spec (k: gset K) (t: gset T):
    forall p, p ∈ gset_prod k t <-> p.1 ∈ k /\ p.2 ∈ t.
  Proof using. Admitted.

End GsetProd.
