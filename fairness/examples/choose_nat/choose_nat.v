From iris.proofmode Require Import tactics.
From stdpp Require Import finite.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
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

  Lemma decr_loop_spec tid (n:nat) f :
    6 ≤ f → f ≤ 40 →
    {{{ has_fuel tid () f ∗ frag_free_roles_are ∅ ∗ frag_model_is (N (S n)) }}}
      decr_loop_prog #(S n) @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Hle1 Hle2 Φ) "(Hf & Hr & Hm) HΦ".
    iInduction n as [|n] "IHn".
    { wp_lam. wp_pures. wp_lam. wp_pures.
      iApply (@wp_lift_pure_step_no_fork_singlerole_take_step
              _ the_cn_fair_model _ _
              (N 1) (N 0) tid _ _ (f - 6) (f - 3) _ _ _ _ ())=> /=;
        [done|set_solver|lia|constructor|].
      do 3 iModIntro.
      rewrite has_fuel_fuels.
      replace (f - 1 - 1 - 1 - 1 - 1 - 1) with (f - 6) by lia.
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
              (N $ S $ S n) (N $ S n) tid _ _ (f - 3) f _ _ _ _ ())=> /=;
      [done|done|set_solver|lia|constructor|].
    do 3 iModIntro.
    rewrite has_fuel_fuels.
    replace (f - 1 - 1 - 1) with (f - 3) by lia.
    iFrame.    
    iIntros "Hm Hr Hf".
    wp_pures.
    replace (Z.of_nat (S $ S n) - 1)%Z with (Z.of_nat $ S n) by lia.
    destruct (decide (() ∈ {[()]})); [|set_solver].
    rewrite has_fuel_fuels.
    by iApply ("IHn" with "Hf Hr Hm").
  Qed.

  Lemma choose_nat_spec tid f :
    8 ≤ f → f ≤ 40 →
    {{{ has_fuel tid () f ∗ frag_free_roles_are ∅ ∗ frag_model_is Start }}}
      choose_nat_prog #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Hle1 Hle2 Φ) "(Hf & Hr & Hm) HΦ".
    wp_lam.
    wp_bind ChooseNat.
    iApply (wp_choose_nat_nostep _ _ _ {[() := (f - 2)]} with "[Hf]").
    { set_solver. }
    { rewrite -has_fuel_fuels_S has_fuel_fuels.
      replace (S (f - 2)) with (f - 1) by lia. done. }
    iIntros "!>" (n) "Hf".
    iApply (@wp_lift_pure_step_no_fork_singlerole_take_step
              _ the_cn_fair_model _ _
              Start (N $ S n) tid _ _ (f - 2) f _ _ _ _ ())=> /=;
      [done|done|set_solver|lia|constructor|].
    do 3 iModIntro.
    rewrite has_fuel_fuels.
    iFrame.
    iIntros "Hm Hr Hf".
    destruct (decide (() ∈ {[()]})); [|set_solver].
    wp_pures.
    replace (Z.of_nat n + 1)%Z with (Z.of_nat $ S n) by lia.
    rewrite -has_fuel_fuels.
    iApply (decr_loop_spec with "[$Hm $Hr $Hf]"); [lia|lia|].
    done.
  Qed.

End proof.    

#[local] Instance the_model_terminates :
  FairTerminatingModel the_cn_fair_model.
Proof. Admitted. 

#[local] Instance proof_irrel_trans s x :
  ProofIrrel ((let '(s', ℓ) := x in cntrans s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma model_finitary s :
  Finite { '(s', ℓ) | cntrans s ℓ s'}.
Proof. Admitted.

Theorem choose_nat_terminates
        (extr : extrace) (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [choose_nat_prog #()]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  eapply (simulation_adequacy_terminate_ftm (Mdl := the_cn_fair_model) (heapΣ the_cn_fair_model) NotStuck _ Start ∅) =>//.
  { eapply valid_state_evolution_finitary_fairness.
    intros ?. simpl. apply (model_finitary s1). }
  iIntros (HGS) "!> Hm Hr Hs !>".
  simpl.
  replace (∅ ∖ {[()]}) with (∅:gset unit) by set_solver.
  rewrite -fmap_gset_to_gmap.
  rewrite /gset_to_gmap. simpl.
  repeat rewrite fmap_insert.
  repeat rewrite fmap_empty.
  rewrite -has_fuel_fuels.
  iApply (choose_nat_spec with "[$Hm $Hr $Hs]"); [simpl;lia|simpl;lia|].
  eauto.
Qed.
