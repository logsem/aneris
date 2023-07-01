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

Inductive EO := ρEven | ρOdd.

#[global] Instance EO_eqdec: EqDecision EO.
Proof. solve_decision. Qed.

#[global] Instance EO_countable: Countable EO.
Proof.
  refine ({|
             encode eo := match eo with ρEven => 1 | ρOdd => 2 end;
             decode p := match p with 1 => Some ρEven | 2 => Some ρOdd | _ => None end;
         |})%positive.
  intros eo. by destruct eo.
Qed.

#[global] Instance EO_inhabited: Inhabited EO.
Proof. exact (populate ρEven). Qed.

Inductive eotrans: nat -> option EO -> nat -> Prop :=
| even_trans n : Nat.even n → eotrans n (Some ρEven) (S n)
| even_fail n : Nat.odd n → eotrans n (Some ρEven) n
| no_trans n : Nat.odd n → eotrans n (Some ρOdd) (S n)
| no_fail n : Nat.even n → eotrans n (Some ρOdd) n
.

Definition eo_live_roles : gset EO := {[ ρOdd; ρEven ]}.

Lemma live_spec_holds :
  forall s ρ s', eotrans s (Some ρ) s' -> ρ ∈ eo_live_roles.
Proof.
  intros n eo n' Htrans. rewrite /eo_live_roles.
  inversion Htrans; simplify_eq; try set_solver; try lia; destruct n'; try set_solver; lia.
Qed.

Definition the_fair_model: FairModel.
Proof.
  refine({|
            fmstate := nat;
            fmrole := EO;
            fmtrans := eotrans;
            live_roles _ := eo_live_roles;
            fm_live_spec := live_spec_holds;
          |}).
Defined.

Definition the_model: LiveModel heap_lang the_fair_model :=
  {|
    lm_fl (x: fmstate the_fair_model) := 61%nat;
  |}.

(** The CMRAs we need. *)
Class evenoddG Σ := EvenoddG {
  even_name: gname;
  odd_name: gname;
  evenodd_n_G :> inG Σ (excl_authR natO);
 }.
Class evenoddPreG Σ := {
  evenodd_PreG :> inG Σ (excl_authR natO);
 }.
Definition evenoddΣ : gFunctors :=
  #[ heapΣ the_fair_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

Global Instance subG_evenoddΣ {Σ} : subG evenoddΣ Σ → evenoddPreG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ the_model, !evenoddG Σ}.
  Let Ns := nroot .@ "even_odd".

  Definition even_at (n: nat) := own even_name (◯E n).
  Definition odd_at (n: nat) := own odd_name (◯E n).

  Definition auth_even_at (n: nat) := own even_name (●E n).
  Definition auth_odd_at (n: nat) := own odd_name (●E n).

  Lemma they_agree γ (N M: nat):
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma even_agree N M:
    even_at N -∗ auth_even_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.
  Lemma odd_agree N M:
    odd_at N -∗ auth_odd_at M -∗ ⌜ M = N ⌝.
  Proof. apply they_agree. Qed.

  Lemma they_update γ (N M P: nat):
    own γ (●E N) ∗ own γ (◯E M) ==∗ own γ (●E P) ∗ own γ (◯E P).
  Proof.
    rewrite -!own_op. iApply own_update. apply excl_auth_update.
  Qed.
  Lemma even_update P N M:
     auth_even_at M ∗ even_at N ==∗ auth_even_at P ∗ even_at P.
  Proof. apply they_update. Qed.
  Lemma odd_update P N M:
     auth_odd_at M ∗ odd_at N ==∗ auth_odd_at P ∗ odd_at P.
  Proof. apply they_update. Qed.

  Definition evenodd_inv_inner n :=
    (∃ N,
          frag_free_roles_are ∅ ∗
          frag_model_is N ∗ n ↦ #N ∗
          (if (Nat.even N)
           then auth_even_at N ∗ auth_odd_at (N+1)
           else auth_even_at (N+1) ∗ auth_odd_at N))%I.
  Definition evenodd_inv n := inv Ns (evenodd_inv_inner n).

  Lemma even_go_spec tid n (N: nat) f (Hf: f > 40):
    {{{ evenodd_inv n ∗ has_fuel tid ρEven f ∗ even_at N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#Hinv & Hf & Heven) Hk".
    wp_lam.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    destruct (Nat.even M) eqn:Heqn; iDestruct "Hauths" as "[>Hay >Han]".
    - iDestruct (even_agree with "Heven Hay") as "%Heq".
      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_suc_step_singlerole _ tid (ρEven: fmrole the_fair_model) _ 55%nat _
                                             M (M + 1)
             with "[$]"); eauto.
      { by do 3 f_equiv. }
      { simpl. lia. }
      { rewrite Nat.add_1_r. econstructor. eauto. }
      iModIntro.
      iIntros "!> (Hb & Hmod & HFR & Hf)".
      iMod (even_update (M + 2) with "[$]") as "[Hay Heven]".
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
      iApply ("Hg" with "[] [Heven Hf] [$]"); last first.
      { iFrame "∗#". rewrite has_fuel_fuels.
        subst. iFrame. }
      iPureIntro; lia.
    - iDestruct (even_agree with "Heven Hay") as "%Heq". rewrite -> Heq in *.
      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (ρEven: fmrole the_fair_model) _ 50%nat _
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
      iApply ("Hg" with "[] [Heven Hf] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.

  Lemma odd_go_spec tid n (N: nat) f (Hf: f > 40):
    {{{ evenodd_inv n ∗ has_fuel tid ρOdd f ∗ odd_at N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).
    iIntros (Φ) "(#Hinv & Hf & Hodd) Hk".
    wp_lam.
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    destruct (Nat.even M) eqn:Heqn; iDestruct "Hauths" as "[>Hay >Han]"; last first.
    - iDestruct (odd_agree with "Hodd Han") as "%Heq".
      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_suc_step_singlerole _ tid (ρOdd: fmrole the_fair_model) _ 55%nat _
                                             M (S M)
               with "[$]"); eauto.
      { by do 3 f_equiv. }
      { simpl. lia. }
      { econstructor. rewrite -Nat.negb_even. rewrite Heqn. done. }
      iModIntro.
      iIntros "!> (Hb & Hmod & HFR & Hf)".
      iMod (odd_update (M + 2) with "[$]") as "[Han Hodd]".
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
      iApply ("Hg" with "[] [Hodd Hf] [$]"); last first.
      { iFrame "∗#". simplify_eq. done. }
      iPureIntro; lia.
    - iDestruct (odd_agree with "Hodd Han") as "%Heq". rewrite -> Heq in *.
      rewrite -has_fuel_fuels. simplify_eq.
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (ρOdd: fmrole the_fair_model) _ 50%nat _
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
      iApply ("Hg" with "[] [Hodd Hf] [$]"); last first.
      { iFrame "∗#". }
      iPureIntro; lia.
  Qed.

  Definition role_frag (eo : EO) : nat → iProp Σ :=
    match eo with
    | ρEven => even_at
    | ρOdd => odd_at
    end.

  Lemma incr_loop_spec tid n (N : nat) f (Hf: f > 40) (eo : EO) :
    {{{ evenodd_inv n ∗ has_fuel tid eo f ∗ (role_frag eo) N }}}
      incr_loop #n #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & Heo) Hk".
    destruct eo.
    - iApply (even_go_spec with "[$Hf $Heo]"); [lia|done|done].
    - iApply (odd_go_spec with "[$Hf $Heo]"); [lia|done|done].
  Qed.

End proof.

Section proof_start.
  Context `{!heapGS Σ the_model, !evenoddG Σ}.
  Let Ns := nroot .@ "even_odd".

  Lemma start_spec tid n N1 N2 f (Hf: f > 60) :
    {{{ evenodd_inv n ∗ has_fuels tid {[ ρEven := f; ρOdd := f ]} ∗
        even_at N1 ∗ odd_at N2 }}}
      start #n @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "(#Hinv & Hf & Heven_at & Hodd_at) HΦ". unfold start.
    wp_pures.
    wp_bind (Load _).
    iApply wp_atomic.
    iInv Ns as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
    iIntros "!>".
    wp_load.
    iIntros "!>".
    destruct (Nat.even M) eqn:Heven.
    - iDestruct "Hauths" as "[Heven Hodd]".
      iDestruct (even_agree with "Heven_at Heven") as %<-.
      iDestruct (odd_agree with "Hodd_at Hodd") as %<-.
      iMod ("Hclose" with "[-Hf Heven_at Hodd_at HΦ]") as "_".
      { iIntros "!>". iExists _. iFrame. rewrite Heven. iFrame. }
      iIntros "!>". wp_pures. wp_bind (Fork _).
      rewrite has_fuels_gt_1; last solve_fuel_positive.
      iApply (wp_fork_nostep _ tid _ _ _ {[ ρOdd ]} {[ ρEven ]} {[ρEven := _; ρOdd := _]}
               with "[Heven_at] [- Hf] [Hf]");
        [ set_solver | by apply insert_non_empty | | | |
          rewrite !fmap_insert fmap_empty // ]; [set_solver | |].
      { iIntros (tid') "!> Hf".
        rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite -has_fuel_fuels.
        iApply (incr_loop_spec with "[Heven_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?". }
      iIntros "!> Hf".
      iIntros "!>".
      rewrite map_filter_insert_not; last set_solver.
      rewrite map_filter_insert_True; last set_solver.
      rewrite map_filter_empty insert_empty.
      wp_pures.
      rewrite has_fuels_gt_1; last solve_fuel_positive.
      iApply (wp_fork_nostep _ tid _ _ _ ∅ {[ ρOdd ]} {[ρOdd := _]} with "[Hodd_at] [HΦ] [Hf]");
        [ set_solver | by apply insert_non_empty | | | |
          rewrite !fmap_insert fmap_empty // ]; [set_solver| |].
      + iIntros (tid') "!> Hf".
        rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite -has_fuel_fuels.
        wp_pures.
        rewrite -has_fuel_fuels.
        replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
        iApply (incr_loop_spec with "[Hodd_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?".
    + iIntros "!> Hf".
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty.
        iApply "HΦ". iModIntro.
        iDestruct "Hf" as "[Hf _]".
        by rewrite dom_empty_L.
    - iDestruct "Hauths" as "[Heven Hodd]".
      iDestruct (even_agree with "Heven_at Heven") as %<-.
      iDestruct (odd_agree with "Hodd_at Hodd") as %<-.
      iMod ("Hclose" with "[-Hf Heven_at Hodd_at HΦ]") as "_".
      { iIntros "!>". iExists _. iFrame. rewrite Heven. iFrame. }
      iIntros "!>". wp_pures. wp_bind (Fork _).
      rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite insert_commute; [|done].
      iApply (wp_fork_nostep _ tid _ _ _ {[ ρEven ]} {[ ρOdd ]} {[ρOdd := _; ρEven := _]}
               with "[Hodd_at] [- Hf] [Hf]");
        [ set_solver | by apply insert_non_empty | | | |
          rewrite !fmap_insert fmap_empty // ]; [set_solver | |].
      { iIntros (tid') "!> Hf".
        rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite -has_fuel_fuels.
        iApply (incr_loop_spec with "[Hodd_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?". }
      iIntros "!> Hf".
      iIntros "!>".
      rewrite map_filter_insert_not; last set_solver.
      rewrite map_filter_insert_True; last set_solver.
      rewrite map_filter_empty insert_empty.
      wp_pures.
      rewrite has_fuels_gt_1; last solve_fuel_positive.
      iApply (wp_fork_nostep _ tid _ _ _ ∅ {[ ρEven ]} {[ρEven := _]} with "[Heven_at] [HΦ] [Hf]");
        [ set_solver | by apply insert_non_empty | | | |
          rewrite !fmap_insert fmap_empty // ]; [set_solver| |].
      + iIntros (tid') "!> Hf".
        rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite -has_fuel_fuels.
        wp_pures.
        rewrite -has_fuel_fuels.
        replace (Z.of_nat M + 1)%Z with (Z.of_nat (M + 1)) by lia.
        iApply (incr_loop_spec with "[Heven_at $Hf]"); [lia|iFrame "#∗"|].
        by iIntros "!>?".
      + iIntros "!> Hf".
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty.
        iApply "HΦ". iModIntro.
        iDestruct "Hf" as "[Hf _]".
        by rewrite dom_empty_L.
  Qed.

End proof_start.
