From iris.proofmode Require Import tactics.
From iris.base_logic Require Import own. 
From stdpp Require Import namespaces. 
From iris.algebra Require Import auth (* gmap  *)(* gset *) excl (* gmultiset big_op mono_nat *).
(* From fairness Require Import (* fairness *) locales_helpers utils. *)
From lawyer.counter Require Import counter_model.


Class CounterPreGS Σ := {
    cnt_pre_st :: inG Σ (authUR (excl' natO));
}.

Class CounterGS Σ := {
    cnt_pre :: CounterPreGS Σ;
    cnt_val: gname;
}.

Definition auth_cnt_is `{CounterGS Σ} n: iProp Σ :=
  own cnt_val (● (Excl' n)).

Definition frag_cnt_is `{CounterGS Σ} n: iProp Σ :=
  own cnt_val (◯ (Excl' n)).

Definition cnt_msi `{CounterGS Σ} (c: cnt_st): iProp Σ :=
  auth_cnt_is c
. 

Definition cnt_Σ: gFunctors := #[
 GFunctor (authUR (excl' natO))
].

Global Instance cnt_Σ_pre:
  ∀ Σ, subG cnt_Σ Σ → CounterPreGS Σ.
Proof using. solve_inG. Qed.


Section ResourcesFacts.
  Context `{CounterGS Σ}.

  Lemma auth_frag_cnt_agree n m:
    auth_cnt_is n -∗ frag_cnt_is m -∗ ⌜ m = n ⌝.
  Proof using.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %[SUB ?]%auth_both_valid_discrete.
    by apply Excl_included, leibniz_equiv in SUB. 
  Qed.

End ResourcesFacts.
