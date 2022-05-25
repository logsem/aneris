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

Definition yes_go : val :=
  rec: "yes_go" "n" "b" :=
    (if: CAS "b" #true #false
      then "n" <- !"n" - #1
       else #());;
    if: #0 < !"n"
      then "yes_go" "n" "b"
      else #().

Definition yes : val :=
  λ: "N" "b",
    let: "n" := Alloc "N" in
    yes_go "n" "b".

Definition no_go : val :=
  rec: "no_go" "n" "b" :=
    (if: CAS "b" #false #true
      then "n" <- !"n" - #1
       else #());;
    if: #0 < !"n"
      then "no_go" "n" "b"
      else #().

Definition no : val :=
  λ: "N" "b",
    let: "n" := Alloc "N" in
    no_go "n" "b".

Definition start : val :=
  λ: "N",
    let: "b" := Alloc #true in
    (Fork (yes "N" "b") ;;
    Fork (no "N" "b")).

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

Inductive yntrans: nat*bool*bool*bool -> option YN -> nat*bool*bool*bool -> Prop :=
| yes_trans n: (n > 0)%nat ->yntrans (n, true, true, true) (Some Y) (n, false, true, true) (* < *)
| yes_fail n: (n > 0)%nat ->yntrans (n, false, true, true) (Some Y) (n, false, true, true) (* ≤ *)
| no_trans n: yntrans (S n, false, true, true) (Some No) (n, true, true, true) (* < *)
| no_trans_end yf: yntrans (1, false, yf, true) (Some No) (0, true, yf, true) (* < *)
| no_fail n: yntrans (n, true, true, true) (Some No) (n, true, true, true) (* ≤ *)
| yes_finish N B nf: (N ≤ 1) -> yntrans (N, B, true, nf) (Some Y) (N, B, false, nf) (* < *)
| no_finish B yf: yntrans (0, B, yf, true) (Some No) (0, B, yf, false). (* < *)

Lemma live_spec_holds:
     forall s ρ s', yntrans s (Some ρ) s' -> ρ ∈ (match s with
                | (_, _, yf, nf) => (if yf then {[ Y ]} else ∅) ∪ (if nf then {[ No ]} else ∅)
              end: gset YN).
Proof.
  intros [[[n ?] yf] nf] yn [[[??] ?] ?] Htrans.
  inversion Htrans; set_solver.
Qed.

Definition the_model: FairModel.
Proof.
  refine({|
            fmstate := nat * bool * bool * bool;
            fmrole := YN;
            fmtrans := yntrans;
            live_roles nb :=
              match nb with
              | (_, _, yf, nf) => (if yf then {[ Y ]} else ∅) ∪ (if nf then {[ No ]} else ∅)
              end;
            fuel_limit _ := 45%nat;
            fm_live_spec := live_spec_holds;
          |}).
  intros ρ' [[[? ?] ?] ?] ρ [[[? ?] ?] ?] Htrans Hin Hneq.
  inversion Htrans; destruct ρ; try set_solver.
Defined.


(** The CMRAs we need. *)
Class yesnoG Σ := YesnoG {
  yes_name: gname;
  no_name: gname;
  yes_f_name: gname;
  no_f_name: gname;
  yesno_n_G :> inG Σ (excl_authR natO);
  yesno_f_G :> inG Σ (excl_authR boolO);
 }.
Class yesnoPreG Σ := {
  yesno_PreG :> inG Σ (excl_authR natO);
  yesno_f_PreG :> inG Σ (excl_authR boolO);
 }.
Definition yesnoΣ : gFunctors :=
  #[ heapΣ the_model; GFunctor (excl_authR natO) ; GFunctor (excl_authR boolO) ].

Global Instance subG_yesnoΣ {Σ} : subG yesnoΣ Σ → yesnoPreG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ the_model, !yesnoG Σ}.
  Let Ns := nroot .@ "yes_no".

  Definition yes_at (n: nat) := own yes_name (◯E n).
  Definition no_at (n: nat) := own no_name (◯E n).

  Definition auth_yes_at (n: nat) := own yes_name (●E n).
  Definition auth_no_at (n: nat) := own no_name (●E n).

  Definition yes_finished (b: bool) := own yes_f_name (◯E b).
  Definition no_finished (b: bool) := own no_f_name (◯E b).

  Definition auth_yes_finished (b: bool) := own yes_f_name (●E b).
  Definition auth_no_finished (b: bool) := own no_f_name (●E b).

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

  Lemma they_finished_agree γ (N M: bool):
    own γ (◯E N) -∗ own γ (●E M) -∗ ⌜ M = N ⌝.
  Proof.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. by apply excl_auth_agree_L.
  Qed.
  Lemma yes_finished_agree N M:
    yes_finished N -∗ auth_yes_finished M -∗ ⌜ M = N ⌝.
  Proof. apply they_finished_agree. Qed.
  Lemma no_finished_agree N M:
    no_finished N -∗ auth_no_finished M -∗ ⌜ M = N ⌝.
  Proof. apply they_finished_agree. Qed.

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
  Lemma yes_finished_update P N M:
     auth_yes_finished M ∗ yes_finished N ==∗ auth_yes_finished P ∗ yes_finished P.
  Proof. apply they_finished_update. Qed.
  Lemma no_finished_update P N M:
     auth_no_finished M ∗ no_finished N ==∗ auth_no_finished P ∗ no_finished P.
  Proof. apply they_finished_update. Qed.

  Definition yesno_inv_inner b :=
    (∃ N B yf nf,
          ⌜((N > 1 ∨ (N > 0 ∧ B = true)) -> yf = true) ∧ (N > 0 -> nf = true)⌝ ∗
          auth_yes_finished yf ∗ auth_no_finished nf ∗
          frag_model_is (N, B, yf, nf) ∗ b ↦ #B ∗
                           if B
                           then auth_yes_at N ∗ auth_no_at N
                           else auth_yes_at (N-1)%nat ∗ auth_no_at N)%I.
  Definition yesno_inv b := inv Ns (yesno_inv_inner b).

  Lemma yes_go_spec tid n b (N: nat) f (Hf: f > 17):
    {{{ yesno_inv b ∗ has_fuel tid Y f ∗ n ↦ #N ∗ ⌜N > 0⌝ ∗ yes_at N ∗ yes_finished true }}}
      yes_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).

    iIntros (Φ) "(#Hinv & Hf & HnN & %HN & Hyes & Hyesf) Hk". unfold yes_go.

    wp_pures.
    wp_bind (CmpXchg _ _ _).

    assert (∀ s, Atomic s (CmpXchg #b #true #false)).
                   { apply _. }

    iApply wp_atomic.

    iInv Ns as (M B yf nf) "(>[%Htrue %Htrue'] & >Hayesf & >Hanof & >Hmod & >Bb & Hauths)" "Hclose".
    iDestruct (yes_finished_agree with "Hyesf Hayesf") as %->.
    destruct B; iDestruct "Hauths" as "[>Hay >Han]".
    - iDestruct (yes_agree with "Hyes Hay") as "%Heq". rewrite -> Heq in *. clear Heq.
      rewrite (Htrue' HN).
      (* TODO *)
      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_suc_step_singlerole _ tid (Y: fmrole the_model) _ 30%nat
                                             (N, true, true, true) (N, false, true, true)
             with "[$]"); eauto.
      { simpl. lia. }
      { econstructor. lia. }
      iModIntro.
      iIntros "!> (Hb & Hmod & Hf)".
      iMod (yes_update (N-1) with "[$]") as "[Hay Hyes]".
      iMod ("Hclose" with "[Hmod Hb Hay Han Hanof Hayesf]").
      { iNext. iExists N, false, true, true. iFrame. iPureIntro; intros; lia. }
      simpl.

      destruct N as [|N]; first lia. rewrite decide_True; last first.
      { destruct N; set_solver. }

      iModIntro.

      rewrite has_fuel_fuels.
      wp_pures.
      wp_load.
      wp_pures.
      wp_store.
      wp_pures.
      wp_load.
      wp_pures.

      destruct (decide (0 < S N - 1)) as [Heq|Heq].
      + rewrite bool_decide_eq_true_2 //; last lia.
        wp_pure _.

        rewrite -has_fuel_fuels.
        iApply ("Hg" with "[] [Hyes HnN Hf Hyesf] [$]"); last first.
        { iFrame "∗#". iSplit; last (iPureIntro; lia).
          replace (#(S N - 1)%nat) with (#(S N - 1)); first done.
          do 2 f_equal. lia. }
        iPureIntro; lia.
      + rewrite bool_decide_eq_false_2 //; last lia.
        have ->: N = 0 by lia. simpl.

        clear M. clear Htrue Htrue' nf.

        iApply wp_atomic.
        iInv Ns as (M B yf nf) "(>[%Htrue %Htrue'] & >Hayesf & >Hanof & >Hmod & >Hb & Hauths)" "Hclose".

        destruct B as [|].
        * iDestruct "Hauths" as "[>Hay >Hano]".
          iDestruct (yes_agree with "Hyes Hay") as %->.
          iDestruct (yes_finished_agree with "Hyesf Hayesf") as %->.

          iApply (wp_lift_pure_step_no_fork_singlerole_take_step
                    ((0, true, true, nf): fmstate the_model) (0, true, false, nf) _ _ _ _ 0
                 ); eauto.
          { set_solver. }
          { lia. }
          { econstructor. lia. }

          rewrite -has_fuel_fuels.
          iFrame. iModIntro.
          iMod (yes_finished_update false with "[$]") as "[Hayesf Hyesf]".
          iModIntro. iNext. iModIntro.
          iIntros "Hmod".

          rewrite -wp_value.
          have Hnotin: Y ∉ live_roles the_model (0, true, false, nf).
          { destruct nf; simpl; set_solver. }
          rewrite decide_False //. iIntros "Hccl".

          iMod ("Hclose" with "[Hmod Hb Hay Hano Hanof Hayesf]").
          { iNext. iExists 0, true, false, nf. iFrame. iPureIntro; lia. }
          iModIntro. iApply ("Hk" with "Hccl").

        * iDestruct "Hauths" as "[>Hay >Hano]".
          iDestruct (yes_agree with "Hyes Hay") as %Heq'.
          iDestruct (yes_finished_agree with "Hyesf Hayesf") as %->.

          iApply (wp_lift_pure_step_no_fork_singlerole_take_step
                    ((M, false, true, nf): fmstate the_model) (M, false, false, nf) _ _ _ _ 0
                 ); eauto.
          { set_solver. }
          { lia. }
          { econstructor. lia. }

          rewrite -has_fuel_fuels.
          iFrame. iModIntro.
          iMod (yes_finished_update false with "[$]") as "[Hayesf Hyesf]".
          iModIntro. iNext. iModIntro.
          iIntros "Hmod".

          rewrite -wp_value.
          have Hnotin: Y ∉ live_roles the_model (0, true, false, nf).
          { destruct nf; simpl; set_solver. }
          rewrite decide_False //. iIntros "Hccl".

          iMod ("Hclose" with "[Hmod Hb Hay Hano Hanof Hayesf]").
          { iNext. iExists M, false, false, nf. iFrame. iPureIntro; split; intros. { lia. }
            apply Htrue'. lia. }
          iModIntro. iApply ("Hk" with "Hccl").

    - iDestruct (yes_agree with "Hyes Hay") as "%Heq". rewrite -> Heq in *.
      have HM: M > 0 by lia.
      rewrite (Htrue' HM).

      rewrite -has_fuel_fuels.
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (Y: fmrole the_model) _ 30%nat
                                             (M, false, true, true) (M, false, true, true)
             with "[$]"); eauto.
      { simpl. lia. }
      { econstructor. lia. }
      iIntros "!>!> (Hb & Hmod & Hf)".
      (* iMod (yes_update (N-1) with "[$]") as "[Hay Hyes]". *)
      iMod ("Hclose" with "[Hmod Hb Hay Han Hanof Hayesf]").
      { iNext. iExists M, false, true, true. rewrite Heq. iFrame. iPureIntro; intros; lia. }
      simpl.

      destruct N as [|N]; first lia. rewrite decide_True; last first.
      { destruct N; set_solver. }

      rewrite has_fuel_fuels.
      iModIntro.
      wp_pures.
      wp_load.
      do 2 wp_pure _.

      rewrite -has_fuel_fuels.
      iApply ("Hg" with "[] [Hyes HnN Hf Hyesf] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Qed.

  Lemma yes_spec tid b (N: nat) f (Hf: f > 25):
    {{{ yesno_inv b ∗ has_fuel tid Y f ∗ ⌜N > 0⌝ ∗ yes_at N ∗ yes_finished true }}}
      yes #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & %HN & Hyes & Hyesf) Hk". unfold yes.

    wp_pures.
    wp_bind (Alloc _).

    rewrite has_fuels_gt_1; last by solve_fuel_positive.

    iApply (wp_alloc_nostep _ _ _ _ {[Y := _]}%nat with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite fmap_insert fmap_empty. done. }
    iNext. iIntros (n) "(HnN & _ & Hf)".
    rewrite -has_fuel_fuels.

    wp_pures.

    rewrite -has_fuel_fuels.

    iApply (yes_go_spec with "[-Hk]"); try iFrame.
    { lia. }
    { iFrame "Hinv". done. }
  Qed.

  Lemma no_go_spec tid n b (N: nat) f (Hf: f > 17):
    {{{ yesno_inv b ∗ has_fuel tid No f ∗ n ↦ #N ∗ ⌜N > 0⌝ ∗ no_at N ∗ no_finished true }}}
      no_go #n #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iLöb as "Hg" forall (N f Hf).

    iIntros (Φ) "(#Hinv & Hf & HnN & %HN & Hno & Hnof) Hk". unfold no_go.

    wp_pures.

    wp_bind (CmpXchg _ _ _).

    rewrite -has_fuel_fuels.

    iApply wp_atomic.
    iInv Ns as (M B yf nf) "(>[%Htrue %Htrue'] & >Hayesf & >Hanof & >Hmod & >Bb & Hauths)" "Hclose".
    iDestruct (no_finished_agree with "Hnof Hanof") as %->.
    destruct B; iDestruct "Hauths" as "[>Hay >Han]"; last first.
    - iDestruct (no_agree with "Hno Han") as "%H". rewrite -> H in *. clear H.
      iApply (wp_cmpxchg_suc_step_singlerole _ tid (No: fmrole the_model) _ 30%nat
                                             (N, false, yf, true) (N-1, true, yf, true)
             with "[$]"); eauto.
      { simpl. lia. }
      { simpl. destruct N as [|N]; first lia. rewrite /= Nat.sub_0_r.
        destruct yf; first econstructor. destruct N as [|N]; try econstructor.
        by have ?: false = true by lia. }

      iModIntro.
      iIntros "!> (Hb & Hmod & Hf)".
      iMod (no_update (N-1) with "[$]") as "[Han Hno]".
      iMod ("Hclose" with "[Hmod Hb Hay Han Hanof Hayesf]").
      { iNext. iExists (N-1), true, yf, true. iFrame. iPureIntro; intros; split; last lia.
        intros. apply Htrue. lia. }
      simpl.

      destruct N as [|N]; first lia. rewrite decide_True; last first.
      { destruct N; set_solver. }

      iModIntro.
      wp_pures.
      wp_load.
      wp_pures.
      wp_store.
      wp_pures.
      wp_load.
      wp_pures.

      destruct (decide (0 < S N - 1)) as [Heq|Heq].
      + rewrite bool_decide_eq_true_2 //; last lia.

        wp_pure _.

        rewrite -has_fuel_fuels.
        iApply ("Hg" with "[] [Hno HnN Hf Hnof] [$]"); last first.
        { iFrame "∗#". iSplit; last (iPureIntro; lia).
          replace (#(S N - 1)%nat) with (#(S N - 1)); first done.
          do 2 f_equal. lia. }
        iPureIntro; lia.
      + rewrite bool_decide_eq_false_2 //; last lia.
        have ->: N = 0 by lia. simpl.

        clear M. clear Htrue Htrue' yf.

        iApply wp_atomic.
        iInv Ns as (M B yf nf) "(>[%Htrue %Htrue'] & >Hayesf & >Hanof & >Hmod & >Hb & Hauths)" "Hclose".

        destruct B as [|].
        * iDestruct "Hauths" as "[>Hay >Han]".
          iDestruct (no_agree with "Hno Han") as %->.
          iDestruct (no_finished_agree with "Hnof Hanof") as %->.

          rewrite -has_fuel_fuels.
          iApply (wp_lift_pure_step_no_fork_singlerole_take_step
                    ((0, true, yf, true): fmstate the_model) (0, true, yf, false) _ _ _ _ 0
                 ); eauto.
          { set_solver. }
          { lia. }
          { econstructor. }
          iFrame. iModIntro.
          iMod (no_finished_update false with "[$]") as "[Hanof Hnof]".
          iModIntro. iNext. iModIntro.
          rewrite -wp_value.

          have Hnotin: No ∉ live_roles the_model (0, true, yf, false).
          { destruct yf; simpl; set_solver. }
          rewrite decide_False //. iIntros "Hmod".

          iMod ("Hclose" with "[- Hk]").
          { iNext. iExists 0, true, yf, false. iFrame. iPureIntro; lia. }
          iIntros "Hccl". iModIntro. iApply ("Hk" with "Hccl").
        * iDestruct "Hauths" as "[>Hay >Hano]".
          iDestruct (no_agree with "Hno Hano") as %->.
          iDestruct (no_finished_agree with "Hnof Hanof") as %->.

          rewrite -has_fuel_fuels.
          iApply (wp_lift_pure_step_no_fork_singlerole_take_step
                    ((0, false, yf, true): fmstate the_model) (0, false, yf, false) _ _ _ _ 0
                 ); eauto.
          { set_solver. }
          { lia. }
          { econstructor. }
          iFrame. iModIntro.

          iMod (no_finished_update false with "[$]") as "[Hanof Hnof]".
          iModIntro. iNext. iModIntro. iIntros "Hmod".

          have Hnotin: No ∉ live_roles the_model (0, false, yf, false).
          { destruct yf; simpl; set_solver. }
          rewrite decide_False //. iIntros "Hccl".

          rewrite -wp_value.
          iMod ("Hclose" with "[-Hk Hccl]").
          { iNext. iExists 0, false, yf, false. iFrame. iPureIntro; split; intros; lia. }
          iModIntro. iApply ("Hk" with "Hccl").

    - iDestruct (no_agree with "Hno Han") as "%H". rewrite -> H in *.
      have HM: M > 0 by lia.
      (* rewrite (Htrue' HM). *)
      iApply (wp_cmpxchg_fail_step_singlerole _ tid (No: fmrole the_model) _ 30%nat
                                             (N, true, yf, true) (N, true, yf, true)
             with "[$]"); eauto.
      { simpl. lia. }
      { rewrite Htrue; last by right; lia. econstructor. }
      iModIntro. iIntros "!> (Hb & Hmod & Hf)".
      (* iMod (yes_update (N-1) with "[$]") as "[Hay Hyes]". *)
      iMod ("Hclose" with "[Hmod Hb Hay Han Hanof Hayesf]").
      { iNext. iExists N, true, yf, true. iFrame. iPureIntro; intros. split=>//. }
      simpl.

      destruct N as [|N]; first lia. rewrite decide_True; last first.
      { destruct N; set_solver. }

      iModIntro.
      wp_pures.
      wp_load.
      do 2 wp_pure _.

      rewrite -has_fuel_fuels.
      iApply ("Hg" with "[] [-Hk] [$]"); last first.
      { iFrame "∗#". iPureIntro; lia. }
      iPureIntro; lia.
  Qed.

  Lemma no_spec tid b (N: nat) f (Hf: f > 25):
    {{{ yesno_inv b ∗ has_fuel tid No f ∗ ⌜N > 0⌝ ∗ no_at N ∗ no_finished true }}}
      no #N #b @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof.
    iIntros (Φ) "(#Hinv & Hf & %HN & Hyes & Hyesf) Hk". unfold no.

    wp_pures.
    wp_bind (Alloc _).

    rewrite has_fuels_gt_1; last by solve_fuel_positive.

    iApply (wp_alloc_nostep _ _ _ _ {[No := _]}%nat with "[Hf]").
    { apply map_non_empty_singleton. }
    { rewrite fmap_insert fmap_empty. done. }
    iNext. iIntros (n) "(HnN & _ & Hf)".
    rewrite -has_fuel_fuels.

    wp_pures.

    rewrite -has_fuel_fuels.

    iApply (no_go_spec with "[-Hk]"); try iFrame.
    { lia. }
    { iFrame "Hinv". done. }
  Qed.
End proof.


Section proof_start.
  Context `{!heapGS Σ the_model, !yesnoPreG Σ}.
  Let Ns := nroot .@ "yes_no".

  Lemma start_spec tid (N: nat) f (Hf: f > 40):
    {{{ frag_model_is (N, true, true, true) ∗
        has_fuels tid {[ Y := f; No := f ]} ∗ ⌜N > 0⌝ }}}
      start #N @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using All.
    iIntros (Φ) "[Hst [Hf %HN]] Hkont". unfold start.

    wp_pures.

    wp_bind (Alloc _).
    iApply (wp_alloc_nostep _ _ _ _ {[Y := _; No := _]} with "[Hf]").
    { apply insert_non_empty. }
    { rewrite has_fuels_gt_1; last solve_fuel_positive.
      rewrite !fmap_insert fmap_empty //. }

    iIntros "!>" (l) "(Hl & _ & Hf)".

    wp_pures.

    (* Allocate the invariant. *)
    iMod (own_alloc (●E N  ⋅ ◯E N)) as (γ_yes_at) "[Hyes_at_auth Hyes_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E N  ⋅ ◯E N)) as (γ_no_at) "[Hno_at_auth Hno_at]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E true  ⋅ ◯E true)) as (γ_yes_fin) "[Hyes_fin_auth Hyes_fin]".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (own_alloc (●E true  ⋅ ◯E true)) as (γ_no_fin) "[Hno_fin_auth Hno_fin]".
    { apply auth_both_valid_2; eauto. by compute. }

    pose (the_names := {|
     yes_name := γ_yes_at;
     yes_f_name := γ_yes_fin;
     no_name := γ_no_at;
     no_f_name := γ_no_fin;
    |}).

    iApply fupd_wp.
    iMod (inv_alloc Ns _ (yesno_inv_inner l) with "[-Hkont Hf Hyes_at Hno_at Hyes_fin Hno_fin]") as "#Hinv".
    { iNext. unfold yesno_inv_inner. iExists N, true, true, true.
      iSplit; first done. iFrame. }
    iModIntro.

    wp_bind (Fork _).
    rewrite has_fuels_gt_1; last solve_fuel_positive.
    iApply (wp_fork_nostep _ tid _ _ _ {[ No ]} {[ Y ]} {[Y := _; No := _]}
             with "[Hyes_at Hyes_fin] [- Hf] [Hf]");
      [ set_solver | by apply insert_non_empty |  | | | rewrite !fmap_insert fmap_empty // ];
      [set_solver | |].
    { iIntros (tid') "!> Hf". iApply (yes_spec with "[-]"); last first.
      + by eauto.
      + rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_insert_not; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite has_fuel_fuels. by iFrame "#∗".
      + lia. }

    iIntros "!> Hf".
    rewrite map_filter_insert_not; last set_solver.
    rewrite map_filter_insert_True; last set_solver.
    rewrite map_filter_empty insert_empty.

    iModIntro.
    wp_pures.

    rewrite has_fuels_gt_1; last solve_fuel_positive.
    iApply (wp_fork_nostep _ tid _ _ _ ∅ {[ No ]} {[No := _]} with "[Hno_at Hno_fin] [Hkont] [Hf]");
      [ set_solver | by apply insert_non_empty |  | | | rewrite !fmap_insert fmap_empty // ];
      [set_solver | |].
    { iIntros (tid') "!> Hf". iApply (no_spec with "[-]"); last first.
      + by eauto.
      + rewrite map_filter_insert_True; last set_solver.
        rewrite map_filter_empty insert_empty.
        rewrite has_fuel_fuels. by iFrame "#∗".
      + lia. }

    iNext. iIntros "[Hf _]".
    iApply "Hkont". iModIntro. iApply (equiv_wand with "Hf"). do 2 f_equiv.
    rewrite dom_empty_iff_L map_filter_empty_iff.
    intros ???. set_solver.
  Qed.
End proof_start.
