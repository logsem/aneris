From iris.proofmode Require Import proofmode coq_tactics.
From lawyer.nonblocking.logrel Require Export persistent_pred logrel substitutions valid_client.
From lawyer.nonblocking Require Export pwp. 
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
From heap_lang Require Import heap_lang_defs sswp_logic tactics lang notation. 


(* TODO: the restriction to RecV is reasonable,
   but is only needed for premise of head_redex_unique.
   What changes if (m a) is not reducible (i.e. m ≠ RecV)? *)
Lemma call_unique (f x: binder) (b: expr)
  (m := RecV f x b)
  (K1 K2: ectx heap_lang) (a1 a2: val)
  (EQ: ectx_language.fill K1 (m a1) = ectx_language.fill K2 (m a2)):
  K1 = K2 /\ a1 = a2.
Proof using.
  subst m. 
  eapply head_redex_unique with (σ := Build_state ∅ ∅) in EQ as [K_EQ APP_EQ].
  2, 3: by (red; do 3 eexists; eapply BetaS; eauto).
  by inversion APP_EQ.
Qed.
  
