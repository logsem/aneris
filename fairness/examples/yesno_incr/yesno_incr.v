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

Definition incr_loop : val :=
  rec: "incr_loop" "l" "n" :=
    (if: CAS "l" "n" ("n"+#1)
     then "incr_loop" "l" ("n" + #2)
     else "incr_loop" "l" "n").

Definition start : val :=
  λ: "l",
    let: "x" := !"l" in
    (Fork (incr_loop "l" "x") ;;
    Fork (incr_loop "l" ("x"+#1))).

(** * Definition of the model! *)

Inductive YN := Y | No.

#[global] Instance YN_eqdec: EqDecision YN.
Proof. solve_decision. Qed.

#[global] Instance YN_countable: Countable YN.
Proof.
  refine ({|
             encode yn := match yn with Y => 1 | No => 2 end;
             decode p := match p with 1 => Some Y | 2 => Some No | _ => None end;
         |})%positive.
  intros yn. by destruct yn.
Qed.

#[global] Instance YN_inhabited: Inhabited YN.
Proof. exact (populate Y). Qed.

Inductive yntrans: nat -> option YN -> nat -> Prop :=
| yes_trans n : Nat.even n → yntrans n (Some Y) (S n)
| yes_fail n : Nat.odd n → yntrans n (Some Y) n
| no_trans n : Nat.odd n → yntrans n (Some No) (S n)
| no_fail n : Nat.even n → yntrans n (Some No) n
.

Definition yn_live_roles : gset YN := {[ No; Y ]}.

Lemma live_spec_holds :
  forall s ρ s', yntrans s (Some ρ) s' -> ρ ∈ yn_live_roles.
Proof.
  intros n yn n' Htrans. rewrite /yn_live_roles.
  inversion Htrans; simplify_eq; try set_solver; try lia; destruct n'; try set_solver; lia.
Qed.

Definition the_fair_model: FairModel.
Proof.
  refine({|
            fmstate := nat;
            fmrole := YN;
            fmtrans := yntrans;
            live_roles _ := yn_live_roles;
            fm_live_spec := live_spec_holds;
          |}).
Defined.

Definition the_model: LiveModel heap_lang the_fair_model :=
  {|
    lm_fl (x: fmstate the_fair_model) := 61%nat;
  |}.

(** The CMRAs we need. *)
Class yesnoG Σ := YesnoG {
  yes_name: gname;
  no_name: gname;
  yesno_n_G :> inG Σ (excl_authR natO);
  yesno_f_G :> inG Σ (excl_authR boolO);
 }.
Class yesnoPreG Σ := {
  yesno_PreG :> inG Σ (excl_authR natO);
  yesno_f_PreG :> inG Σ (excl_authR boolO);
 }.
Definition yesnoΣ : gFunctors :=
  #[ heapΣ the_fair_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

Global Instance subG_yesnoΣ {Σ} : subG yesnoΣ Σ → yesnoPreG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ the_model, !yesnoG Σ}.
  Let Ns := nroot .@ "yes_no".

  Definition yes_at (n: nat) := own yes_name (◯E n).
  Definition no_at (n: nat) := own no_name (◯E n).

  Definition auth_yes_at (n: nat) := own yes_name (●E n).
  Definition auth_no_at (n: nat) := own no_name (●E n).

  Lemma they_agree γ (N M: nat):
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma yes_agree N M:
    yes_at N -∗ auth_yes_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.
  Lemma no_agree N M:
    no_at N -∗ auth_no_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.

  Lemma they_update γ (N M P: nat):
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma yes_update P N M:
     auth_yes_at M ∗ yes_at N ==∗ auth_yes_at P ∗ yes_at P.
  Proof. apply they_update. Qed.
  Lemma no_update P N M:
     auth_no_at M ∗ no_at N ==∗ auth_no_at P ∗ no_at P.
  Proof. apply they_update. Qed.

  Lemma they_finished_update γ (N M P: bool):
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.

  Definition yesno_inv_inner n :=
    (∃ N,
          frag_free_roles_are ∅ ∗
          frag_model_is N ∗ n ↦ #N ∗
          (if (Nat.even N)
           then auth_yes_at N ∗ auth_no_at (N+1)
           else auth_yes_at (N+1) ∗ auth_no_at N))%I.
  Definition yesno_inv n := inv Ns (yesno_inv_inner n).

  Lemma yes_go_spec tid n (N: nat) f (Hf: f > 40):
    {{{ yesno_inv n ∗ has_fuel tid Y f ∗ yes_at N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#Hinv & Hf & Hyes) Hk".
    wp_lam.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    destruct (Nat.even M) eqn:Heqn; iDestruct "Hauths" as "[>Hay >Han]".
    - iDestruct (yes_agree with "Hyes Hay") as "%Heq".
      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_suc_step_singlerole _ tid (Y: fmrole the_fair_model) _ 55%nat _
                                             M (M + 1)
             with "[$]"); eauto.
      { by do 3 f_equiv. }
      { simpl. lia. }
      { rewrite Nat.add_1_r. econstructor. eauto. }
      iModIntro.
      iIntros "!> (Hb & Hmod & HFR & Hf)".
      iMod (yes_update (M + 2) with "[$]") as "[Hay Hyes]".
      iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
      { iNext. iExists _. iFrame. rewrite Nat2Z.inj_add.
        subst. iFrame.
        rewrite Nat.add_1_r.
        rewrite Nat.even_succ.
        rewrite -Nat.negb_even. rewrite Heqn. simpl. iFrame.
        rewrite Nat.add_1_r.
        replace (S (S N)) with (N + 2) by lia. iFrame. }
      iModIntro. rewrite decide_True; last first.
      { set_solver. }
      rewrite has_fuel_fuels.
      wp_pures.
      replace (Z.of_nat N + 2)%Z with (Z.of_nat (N + 2)) by lia.
      iApply ("Hg" with "[] [Hyes Hf] [$]"); last first.
      { iFrame "∗#". rewrite has_fuel_fuels.
        subst. iFrame. }
      iPureIntro; lia.
    - iDestruct (yes_agree with "Hyes Hay") as "%Heq". rewrite -> Heq in *.
      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (Y: fmrole the_fair_model) _ 50%nat _
                                             M M
             with "[$]"); eauto.
      { intros Hne. simplify_eq. lia. }
      { simpl. lia. }
      { econstructor. rewrite -Nat.negb_even. rewrite Heqn. done. }
      iIntros "!>!> (Hb & Hmod & HFR & Hf)".
      iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
      { iNext. simplify_eq. iExists _. iFrame.
        subst. iFrame.
        rewrite Nat.add_1_r. rewrite Heqn. iFrame. }
      rewrite decide_True; last first.
      { set_solver. }
      iModIntro.
      wp_pures.
      rewrite -has_fuel_fuels.
      iApply ("Hg" with "[] [Hyes Hf] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.

  Lemma no_go_spec tid n (N: nat) f (Hf: f > 40):
    {{{ yesno_inv n ∗ has_fuel tid No f ∗ no_at N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#Hinv & Hf & Hno) Hk".
    wp_lam.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    destruct (Nat.even M) eqn:Heqn; iDestruct "Hauths" as "[>Hay >Han]"; last first.
    - iDestruct (no_agree with "Hno Han") as "%Heq".
      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_suc_step_singlerole _ tid (No: fmrole the_fair_model) _ 55%nat _
                                             M (S M)
               with "[$]"); eauto.
      { by do 3 f_equiv. }
      { simpl. lia. }
      { econstructor. rewrite -Nat.negb_even. rewrite Heqn. done. }
      iModIntro.
      iIntros "!> (Hb & Hmod & HFR & Hf)".
      iMod (no_update (M + 2) with "[$]") as "[Han Hno]".
      iMod ("Hclose" with "[Hmod Hay Han Hb HFR]").
      { iNext. iExists _. iFrame. subst.
        rewrite Nat.add_1_r.
        rewrite Nat.even_succ.
        rewrite -Nat.negb_even. rewrite Heqn. simpl. iFrame.
        rewrite Nat.add_1_r.
        replace (S (S N)) with (N + 2) by lia.
        iFrame.
        iEval (rewrite -Nat.add_1_r).
        rewrite Nat2Z.inj_add.
        iFrame. }
      iModIntro. rewrite decide_True; last first.
      { set_solver. }
      rewrite has_fuel_fuels.
      wp_pures.
      rewrite -has_fuel_fuels.
      replace (Z.of_nat N + 2)%Z with (Z.of_nat (N + 2)) by lia.
      iApply ("Hg" with "[] [Hno Hf] [$]"); last first.
      { iFrame "∗#". simplify_eq. done. }
      iPureIntro; lia.
    - iDestruct (no_agree with "Hno Han") as "%Heq". rewrite -> Heq in *.
      rewrite -has_fuel_fuels. simplify_eq.
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (No: fmrole the_fair_model) _ 50%nat _
                                             M M
             with "[$]"); eauto.
      { intros Hneq. simplify_eq. lia. }
      { simpl. lia. }
      { econstructor. eauto. }
      iIntros "!>!> (Hb & Hmod & HFR & Hf)".
      iMod ("Hclose" with "[Hmod Hb Hay Han HFR]").
      { iNext. simplify_eq. iExists _. iFrame.
        rewrite Heqn. iFrame. }
      rewrite decide_True; last first.
      { set_solver. }
      iModIntro.
      wp_pures.
      rewrite -has_fuel_fuels.
      iApply ("Hg" with "[] [Hno Hf] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.

  Definition role_frag (yn : YN) : nat → iProp Σ :=
    match yn with
    | Y => yes_at
    | No => no_at
    end.

  Lemma incr_loop_spec tid n (N : nat) f (Hf: f > 40) (yn : YN) :
    {{{ yesno_inv n ∗ has_fuel tid yn f ∗ (role_frag yn) N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Hyn) Hk".
    destruct yn.
    - iApply (yes_go_spec with "[$Hf $Hyn]"); [lia|done|done].
    - iApply (no_go_spec with "[$Hf $Hyn]"); [lia|done|done].
  Qed.

End proof.

Section proof_start.
  Context `{!heapGS Σ the_model, !yesnoG Σ}.
  Let Ns := nroot .@ "yes_no".

  Lemma start_spec tid n N1 N2 f (Hf: f > 60) :
    {{{ yesno_inv n ∗ has_fuels tid {[ Y := f; No := f ]} ∗
        yes_at N1 ∗ no_at N2 }}}
      start #n @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "(#Hinv & Hf & Hyes_at & Hno_at) HΦ". unfold start.
    wp_pures.
    wp_bind (Load _).
    iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    iIntros "!>".
    wp_load.
    iIntros "!>".
    destruct (Nat.even M) eqn:Heven.
    - iDestruct "Hauths" as "[Hyes Hno]".
      iDestruct (yes_agree with "Hyes_at Hyes") as %<-.
      iDestruct (no_agree with "Hno_at Hno") as %<-.
      iMod ("Hclose" with "[-Hf Hyes_at Hno_at HΦ]") as "_".
      { iIntros "!>". iExists _. iFrame. rewrite Heven. iFrame. }
      iIntros "!>". wp_pures. wp_bind (Fork _).
      rewrite has_fuels_gt_1; last solve_fuel_positive.
      iApply (wp_fork_nostep _ tid _ _ _ {[ No ]} {[ Y ]} {[Y := _; No := _]}
               with "[Hyes_at] [- Hf] [Hf]");
        [ set_solver | by apply insert_non_empty | | | |
          rewrite !fmap_insert fmap_empty // ]; [set_solver | |].
      { iIntros (tid') "!> Hf".
        rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite -has_fuel_fuels.
        iApply (incr_loop_spec with "[Hyes_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?". }
      iIntros "!> Hf".
      iIntros "!>".
      rewrite map_filter_insert_not; last set_solver.
      rewrite map_filter_insert_True; last set_solver.
      rewrite map_filter_empty insert_empty.
      wp_pures.
      rewrite has_fuels_gt_1; last solve_fuel_positive.
      iApply (wp_fork_nostep _ tid _ _ _ ∅ {[ No ]} {[No := _]} with "[Hno_at] [HΦ] [Hf]");
        [ set_solver | by apply insert_non_empty | | | |
          rewrite !fmap_insert fmap_empty // ]; [set_solver| |].
      + iIntros (tid') "!> Hf".
        rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite -has_fuel_fuels.
        wp_pures.
        rewrite -has_fuel_fuels.
        replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
        iApply (incr_loop_spec with "[Hno_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?".
    + iIntros "!> Hf".
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty.
        iApply "HΦ". iModIntro.
        iDestruct "Hf" as "[Hf _]".
        by rewrite dom_empty_L.
    - iDestruct "Hauths" as "[Hyes Hno]".
      iDestruct (yes_agree with "Hyes_at Hyes") as %<-.
      iDestruct (no_agree with "Hno_at Hno") as %<-.
      iMod ("Hclose" with "[-Hf Hyes_at Hno_at HΦ]") as "_".
      { iIntros "!>". iExists _. iFrame. rewrite Heven. iFrame. }
      iIntros "!>". wp_pures. wp_bind (Fork _).
      rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite insert_commute; [|done].
      iApply (wp_fork_nostep _ tid _ _ _ {[ Y ]} {[ No ]} {[No := _; Y := _]}
               with "[Hno_at] [- Hf] [Hf]");
        [ set_solver | by apply insert_non_empty | | | |
          rewrite !fmap_insert fmap_empty // ]; [set_solver | |].
      { iIntros (tid') "!> Hf".
        rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite -has_fuel_fuels.
        iApply (incr_loop_spec with "[Hno_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?". }
      iIntros "!> Hf".
      iIntros "!>".
      rewrite map_filter_insert_not; last set_solver.
      rewrite map_filter_insert_True; last set_solver.
      rewrite map_filter_empty insert_empty.
      wp_pures.
      rewrite has_fuels_gt_1; last solve_fuel_positive.
      iApply (wp_fork_nostep _ tid _ _ _ ∅ {[ Y ]} {[Y := _]} with "[Hyes_at] [HΦ] [Hf]");
        [ set_solver | by apply insert_non_empty | | | |
          rewrite !fmap_insert fmap_empty // ]; [set_solver| |].
      + iIntros (tid') "!> Hf".
        rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite -has_fuel_fuels.
        wp_pures.
        rewrite -has_fuel_fuels.
        replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
        iApply (incr_loop_spec with "[Hyes_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?".
      + iIntros "!> Hf".
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty.
        iApply "HΦ". iModIntro.
        iDestruct "Hf" as "[Hf _]".
        by rewrite dom_empty_L.
  Qed.

End proof_start.
