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
From aneris.examples.snapshot_isolation.proof Require Import model.

Definition hist_to_we (h : list write_event) := last h.

Definition to_hist (h : list write_event) : list val :=
  (λ e, e.(we_val)) <$> h.

Lemma to_hist_prefix_mono hw hw' :
  hw `prefix_of` hw' →  to_hist hw `prefix_of` to_hist hw'.
Proof.
  intros Hp.
  generalize dependent hw'.
  induction hw as [|x l]; intros hw' Hp.
  - by apply prefix_nil.
  - destruct hw' as [|x' l'].
    -- by apply prefix_nil_not in Hp.
    -- simplify_eq /=.
       assert (x = x') as -> by by apply prefix_cons_inv_1 in Hp.
       apply prefix_cons.
       apply IHl.
       by apply prefix_cons_inv_2 in Hp.
Qed.  
Definition socket_address_to_str (sa : socket_address) : string :=
    match sa with SocketAddressInet ip p => ip +:+ (string_of_pos p) end.


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

  Lemma list_later_in {A : Type} (l l1 l2: list A) (a a' : A) :
   l ++ [a] = l1 ++ a' :: l2 → a ∈ a' :: l2.
  Proof.
   intro Hyp.
   generalize dependent l.
   induction l1; intros l Hyp.
   - simpl in Hyp.
     rewrite -Hyp.
     set_solver.
   - simpl in Hyp.
     destruct l as [| h t].
     + inversion Hyp as [[Heq Habs]].
       by apply app_cons_not_nil in Habs.
     + simpl in Hyp.
       inversion Hyp as [[Heq Heq']].
       by eapply IHl1.
  Qed.
