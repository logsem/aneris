From iris.algebra Require Import
     agree auth excl gmap frac_auth excl_auth updates local_updates csum.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional. 
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.



Lemma last_of_none_empty_list_is_some {A : Type} (l : list A) :
    l ≠ [] → ∃ v, Some v = last (l).
  Proof.
    induction l.
    1 : done.
    destruct l; set_solver.
  Qed.

  Lemma last_in {A : Type} (l : list A) (a : A) :
    last l  = Some a → In a l.
  Proof.
    intros Hyp.
    induction l as [ | h l IH]; first inversion Hyp.
    destruct l.
    - inversion Hyp.
      set_solver.
    - inversion Hyp as [Hyp'].
      apply IH in Hyp'.
      set_solver.
  Qed.

  
