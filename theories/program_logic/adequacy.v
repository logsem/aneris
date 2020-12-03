From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import wsat.
From aneris.program_logic Require Export weakestpre.
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxilary results. *)
Section adequacy.
Context `{!irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ {{ Φ }})%I.

Definition config_wp : iProp Σ :=
  (□ ∀ σ1 κ σ2 κs nt,
        ⌜config_step σ1 κ σ2⌝ →
        state_interp σ1 (κ ++ κs) nt ={⊤}[∅]▷=∗ state_interp σ2 κs nt).

Lemma wp_step s e1 σ1 κ κs e2 σ2 efs nt Φ :
  prim_step e1 σ1 κ e2 σ2 efs →
  state_interp σ1 (κ ++ κs) nt -∗ WP e1 @ s; ⊤ {{ Φ }} ={⊤}[∅]▷=∗
    state_interp σ2 κs (nt + length efs) ∗ WP e2 @ s; ⊤ {{ Φ }} ∗
    wptp s efs (replicate (length efs) fork_post).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (?) "Hσ H".
  rewrite (val_stuck e1 σ1 κ e2 σ2 efs) //.
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)".
  iMod ("H" $! e2 σ2 efs with "[//]") as "H".
  by rewrite Nat.add_comm big_sepL2_replicate_r.
Qed.

Lemma wptp_step s es1 es2 κ κs σ1 σ2 Φs nt :
  step (es1,σ1) κ (es2, σ2) →
  config_wp -∗
  state_interp σ1 (κ ++ κs) nt -∗ wptp s es1 Φs -∗
  ∃ nt', |={⊤}[∅]▷=> state_interp σ2 κs (nt + nt') ∗
         wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  iIntros (Hstep) "Hcfgwp Hσ Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep|]; simplify_eq/=.
  - iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
    iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
    iExists _. iMod (wp_step with "Hσ Ht") as "H"; first done.
    iIntros "!> !>". iMod "H" as "($ & He2 & Hefs)". iIntros "!>".
    rewrite -(assoc_L app) -app_comm_cons. iFrame.
  - iExists 0.
    iMod ("Hcfgwp" with "[] Hσ") as "Hσ"; first done.
    iModIntro; iNext; iMod "Hσ"; iModIntro.
    rewrite right_id_L Nat.add_0_r; iFrame.
Qed.

Lemma wptp_steps s n es1 es2 κs κs' σ1 σ2 Φs nt :
  nsteps n (es1, σ1) κs (es2, σ2) →
  config_wp -∗ state_interp σ1 (κs ++ κs') nt -∗ wptp s es1 Φs
  ={⊤}[∅]▷=∗^n ∃ nt',
    state_interp σ2 κs' (nt + nt') ∗ wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  revert nt es1 es2 κs κs' σ1 σ2 Φs.
  induction n as [|n IH]=> nt es1 es2 κs κs' σ1 σ2 Φs /=.
  { inversion_clear 1; iIntros "? ? ?"; iExists 0=> /=.
    rewrite Nat.add_0_r right_id_L. by iFrame. }
  iIntros (Hsteps) "#Hcfgwp Hσ He". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iDestruct (wptp_step with "[] Hσ He") as (nt') ">H"; [done|done|]; simplify_eq.
  iIntros "!> !>". iMod "H" as "(Hσ & He)". iModIntro.
  iApply (step_fupdN_wand with "[Hσ He]"); first by iApply (IH with "[] Hσ He").
  iDestruct 1 as (nt'') "[??]".
  rewrite -Nat.add_assoc -(assoc_L app) -replicate_plus.
  by eauto with iFrame.
Qed.

Lemma wp_not_stuck κs nt e σ Φ :
  state_interp σ κs nt -∗ WP e {{ Φ }} ={⊤}=∗ ⌜not_stuck e σ⌝.
Proof.
  rewrite wp_unfold /wp_pre /not_stuck. iIntros "Hσ H".
  destruct (to_val e) as [v|] eqn:?; first by eauto.
  iSpecialize ("H" $! σ [] κs with "Hσ"). rewrite sep_elim_l.
  iMod (fupd_plain_mask with "H") as %?; eauto.
Qed.

Lemma wptp_strong_adequacy Φs κs' s n es1 es2 κs σ1 σ2 nt:
  nsteps n (es1, σ1) κs (es2, σ2) →
  config_wp -∗ state_interp σ1 (κs ++ κs') nt -∗
  wptp s es1 Φs ={⊤}[∅]▷=∗^(S n) ∃ nt',
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝ ∗
    state_interp σ2 κs' (nt + nt') ∗
    [∗ list] e;Φ ∈ es2;Φs ++ replicate nt' fork_post, from_option Φ True (to_val e).
Proof.
  iIntros (Hstep) "#Hcfgwp Hσ He". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps with "[] Hσ He") as "Hwp"; [done|done|].
  iApply (step_fupdN_wand with "Hwp").
  iDestruct 1 as (nt') "(Hσ & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ e2, s = NotStuck → e2 ∈ es2 → not_stuck e2 σ2 ⌝%I
    (state_interp σ2 κs' (nt + nt') ∗ wptp s es2 (Φs ++ replicate nt' fork_post))%I
    with "[$Hσ $Ht]") as "(%&Hσ&Hwp)".
  { iIntros "(Hσ & Ht)" (e' -> He').
    move: He' => /(elem_of_list_split _ _)[?[?->]].
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ?) "[? Hwp]".
    iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
    iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto. }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iExists _. iSplitR; first done. iFrame "Hσ".
  iApply big_sepL2_fupd.
  iApply (big_sepL2_impl with "Hwp").
  iIntros "!#" (? e Φ ??) "Hwp".
  destruct (to_val e) as [v2|] eqn:He2'; last done.
  apply of_to_val in He2' as <-. iApply (wp_value_inv' with "Hwp").
Qed.
End adequacy.

(** Iris's generic adequacy result *)
Theorem wp_strong_adequacy Σ Λ `{!invPreG Σ} es σ1 n κs t2 σ2 φ :
  (∀ `{Hinv : !invG Σ},
    ⊢ |={⊤}=> ∃
         (s: stuckness)
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI σ1 κs 0 ∗
       ([∗ list] e;Φ ∈ es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = es' ++ t2' ⌝ -∗
         (* es' corresponds to the initial threads *)
         ⌜ length es' = length es ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         ([∗ list] e;Φ ∈ es';Φs, from_option Φ True (to_val e)) -∗
         (* For all forked-off threads that are done, their postcondition
            [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_intro_mask'] or [fupd_mask_weaken] to introduce the
         fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
  iMod Hwp as (s stateI Φ fork_post) "(#Hcfgwp & Hσ & Hwp & Hφ)".
  iDestruct (big_sepL2_length with "Hwp") as %Hlen1.
  iApply step_fupd_intro; [done|]; iModIntro.
  iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "[-Hφ]").
  { iApply (@wptp_strong_adequacy _ _ (IrisG _ _ Hinv stateI fork_post) _ []
    with "[] [Hσ] Hwp"); eauto; by rewrite right_id_L. }
  iDestruct 1 as (nt' ?) "(Hσ & Hval) /=".
  iDestruct (big_sepL2_app_inv_r with "Hval") as (es' t2' ->) "[Hes' Ht2']".
  iDestruct (big_sepL2_length with "Ht2'") as %Hlen2.
  rewrite replicate_length in Hlen2; subst.
  iDestruct (big_sepL2_length with "Hes'") as %Hlen3.
  iApply fupd_plain_mask_empty.
  iApply ("Hφ" with "[//] [%] [//] Hσ Hes'"); [congruence|].
  by rewrite big_sepL2_replicate_r // big_sepL_omap.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) := {
  adequate_result t2 σ2 v2 :
   rtc erased_step ([e1], σ1) (of_val v2 :: t2, σ2) → φ v2 σ2;
  adequate_not_stuck t2 σ2 e2 :
   s = NotStuck →
   rtc erased_step ([e1], σ1) (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ t2 σ2,
    rtc erased_step ([e1], σ1) (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had t2 σ2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

Corollary wp_adequacy Σ Λ `{!invPreG Σ} s e σ φ :
  (∀ `{Hinv : !invG Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv (λ σ κs _, stateI σ κs) fork_post in
       config_wp ∗ stateI σ κs ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as (stateI fork_post) "(Hcfgwp & Hσ & Hwp)".
  iExists s, (λ σ κs _, stateI σ κs), [(λ v, ⌜φ v⌝%I)], fork_post => /=.
  iIntros "{$Hcfgwp $Hσ $Hwp} !>" (e2 t2' -> ? ?) "_ H _".
  iApply fupd_mask_weaken; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.

Corollary wp_invariance Σ Λ `{!invPreG Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invG Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       config_wp ∗ stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hcfgwp & Hσ & Hwp & Hφ)".
  iExists s, stateI, [(λ _, True)%I], fork_post => /=.
  iIntros "{$Hcfgwp $Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_weaken; first set_solver.
Qed.
