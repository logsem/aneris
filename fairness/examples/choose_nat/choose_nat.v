From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.

Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.

Import derived_laws_later.bi.

Set Default Proof Using "Type".

Definition decr_loop_prog : val :=
  rec: "go" "n" :=
    if: "n" = #0 then #() else "go" ("n" - #1).

Definition choose_nat_prog : val :=
  λ: <>,
     let: "n" := ChooseNat + #1 in
     decr_loop_prog "n".

Inductive CN := Start | N (n : nat).

#[global] Instance CN_eqdec: EqDecision CN.
Proof. solve_decision. Qed.

#[global] Instance YN_countable: Countable CN.
Proof. Admitted.

#[global] Instance YN_inhabited: Inhabited CN.
Proof. exact (populate Start). Qed.

Inductive cntrans: CN -> option unit -> CN -> Prop :=
| start_trans n : cntrans Start (Some ()) (N n)
| decr_trans n : cntrans (N $ S n) (Some ()) (N n)
.

Definition cn_live_roles (cn : CN) : gset unit :=
  match cn with
  | Start => {[ () ]}
  | N n => match n with
           | 0 => ∅
           | S n => {[ () ]}
           end
  end.

Lemma live_spec_holds:
     forall s ρ s', cntrans s (Some ρ) s' -> ρ ∈ cn_live_roles s.
Proof. intros [] ρ s'; [set_solver|]. destruct n; [|set_solver]. inversion 1. Qed.

Definition the_cn_fair_model : FairModel.
Proof.
  refine({|
            fmstate := CN;
            fmrole := unit;
            fmtrans := cntrans;
            live_roles := cn_live_roles;
            fm_live_spec := live_spec_holds;
          |}).
Defined.

Definition the_model : LiveModel heap_lang the_cn_fair_model :=
  {| fuel_limit (x: fmstate the_cn_fair_model) := 40 %nat |}.

Section proof.
  Context `{!heapGS Σ the_cn_fair_model the_model}.

  Lemma decr_loop_spec tid (n:nat) :
    {{{ has_fuel tid () 6 ∗ frag_free_roles_are ∅ ∗ frag_model_is (N (S n)) }}}
      decr_loop_prog #(S n) @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(Hf & Hr & Hm) HΦ".
    iInduction n as [|n] "IHn".
    { wp_lam. wp_pures. wp_lam. wp_pures.
      iApply (@wp_lift_pure_step_no_fork_singlerole_take_step
              _ the_cn_fair_model _ _
              (N 1) (N 0) tid _ _ 0 3 _ _ _ _ ())=> /=;
        [done|set_solver|lia|constructor|].
      do 3 iModIntro.
      rewrite has_fuel_fuels.
      iFrame.
      iIntros "Hm Hr Hf".
      destruct (decide (() ∈ ∅)); [set_solver|].
      wp_pures. by iApply "HΦ". }
    wp_lam.
    rewrite fmap_insert fmap_empty. (* Sigh.. *)
    wp_pures.
    rewrite fmap_insert fmap_empty. (* Sigh.. *)
    wp_pures.
    rewrite fmap_insert fmap_empty. (* Sigh.. *)
    iApply (@wp_lift_pure_step_no_fork_singlerole_take_step
              _ the_cn_fair_model _ _
              (N $ S $ S n) (N $ S n) tid _ _ 3 6 _ _ _ _ ())=> /=;
      [done|done|set_solver|lia|constructor|].
    do 3 iModIntro.
    rewrite has_fuel_fuels.
    iFrame.    
    iIntros "Hm Hr Hf".
    wp_pures.
    replace (Z.of_nat (S $ S n) - 1)%Z with (Z.of_nat $ S n) by lia.
    destruct (decide (() ∈ {[()]})); [|set_solver].
    rewrite has_fuel_fuels.
    by iApply ("IHn" with "Hf Hr Hm").
  Qed.

  Lemma choose_nat_spec tid :
    {{{ has_fuel tid () 2 ∗ frag_free_roles_are ∅ ∗ frag_model_is Start }}}
      choose_nat_prog #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(Hf & Hr & Hm) HΦ".
    wp_lam.
    wp_bind ChooseNat.
    iApply (wp_choose_nat_nostep _ _ _ {[() := 0]} with "[Hf]").
    { set_solver. }
    { rewrite -has_fuel_fuels_S has_fuel_fuels. done. }
    iIntros "!>" (n) "Hf".
    iApply (@wp_lift_pure_step_no_fork_singlerole_take_step
              _ the_cn_fair_model _ _
              Start (N $ S n) tid _ _ 0 8 _ _ _ _ ())=> /=;
      [done|done|set_solver|lia|constructor|].
    do 3 iModIntro.
    rewrite has_fuel_fuels.
    iFrame.
    iIntros "Hm Hr Hf".
    destruct (decide (() ∈ {[()]})); [|set_solver].
    wp_pures.
    replace (Z.of_nat n + 1)%Z with (Z.of_nat $ S n) by lia.
    iApply (decr_loop_spec with "[Hm Hr Hf]").
    { rewrite has_fuel_fuels. iFrame. }
    done.
  Qed.

End proof.    
