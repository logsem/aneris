(** The "lifting lemmas" in this file serve to lift the rules of the operational
semantics to the program logic. *)

From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
Set Default Proof Using "Type".

Section lifting.
Context `{!irisG Λ M Σ}.
Implicit Types s : stuckness.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types σ : state Λ.
Implicit Types δ : mstate M.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.

Lemma wp_lift_step_fupdN s E Φ e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗
    state_interp extr atr ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅}▷=∗^(S $ trace_length extr) |={∅,E}=>
     ∃ δ2 ℓ,
       state_interp
         (trace_extend extr (Some ζ) (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2))
         (trace_extend atr ℓ δ2) ∗
        WP e2 @ s; ζ; E {{ Φ }} ∗
        [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
           {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->.
  iIntros "H" (exre atr K tp1 tp2 σ1 Hexvald Hlocale Hexe) "Hsi".
  iMod ("H" with "[//] [//] [//] Hsi") as "[$ H]".
  iIntros "!#" (e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as "H".
  iModIntro; iNext.
  iApply "H".
Qed.

Lemma wp_lift_step_fupd s E Φ e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗
    state_interp extr atr ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅}=∗ ▷ |={∅,E}=>
     ∃ δ2 ℓ,
       state_interp
         (trace_extend extr (Some ζ) (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2))
         (trace_extend atr ℓ δ2) ∗
        WP e2 @ s; ζ; E {{ Φ }} ∗
        [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
           {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
    intros ?. rewrite -wp_lift_step_fupdN; [|done]. simpl. do 26 f_equiv.
    rewrite -step_fupdN_intro; [|done]. rewrite -bi.laterN_intro. auto.
Qed.

Lemma wp_lift_stuck E Φ e ζ:
  to_val e = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ ectx_fill K e :: tp2, σ)⌝ →
    state_interp extr atr ={E,∅}=∗ ⌜stuck e σ⌝)
  ⊢ WP e @ ζ; E ?{{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre=>->.
  iIntros "H" (ex atr K tp1 tp2 σ Hexvalid Hlocale  Hex) "Hsi".
  iMod ("H" with "[//] [//] Hsi") as %[? Hirr].
  iModIntro. iSplit; first done.
  iIntros (e2 σ2 efs ?). by case: (Hirr e2 σ2 efs).
 Qed.

(** Derived lifting lemmas. *)
Lemma wp_lift_step s E Φ e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗
    state_interp extr atr ={E,∅}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      ∃ δ2 ℓ, 
        state_interp
          (trace_extend extr (Some ζ) (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      WP e2 @ s; ζ; E {{ Φ }} ∗
      [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
         {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd; [done|]. iIntros (?????????) "Hsi".
  iMod ("H" with "[//] [//] [//] Hsi") as "[$ H]".
  iIntros "!> * % !> !>". by iApply "H".
Qed.

Lemma wp_lift_pure_step_no_fork
      `{!AllowsPureStep M Σ} `{!Inhabited (state Λ)} s E E' Φ e1 ζ:
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 e2 σ2 efs, prim_step e1 σ1 e2 σ2 efs → σ2 = σ1 ∧ efs = []) →
  (|={E}[E']▷=> ∀ e2 efs σ, ⌜prim_step e1 σ e2 σ efs⌝ → WP e2 @ s; ζ; E {{ Φ }})
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). destruct s; eauto using reducible_not_val. }
  iIntros (ex atr K tp1 tp2 σ1 Hexvalid Hex Hloc) "Hsi". iMod "H".
  iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit.
  { iPureIntro. destruct s; done. }
  iNext. iIntros (e2 σ2 efs ?).
  destruct (Hstep σ1 e2 σ2 efs) as (<- & ->); auto.
  iMod "Hclose" as "_". iMod "H".
  iMod (allows_pure_step with "Hsi") as "Hsi"; [done|done|done| |].
  { econstructor 1; [done| |by apply fill_step]; by rewrite app_nil_r. }
  rewrite !app_nil_r.
  iModIntro.
  iDestruct ("H" with "[//]") as "H".
  iFrame. simplify_eq.
  iExists (trace_last atr), pure_label; iSplit; eauto.
Qed.

Lemma wp_lift_pure_stuck `{!Inhabited (state Λ)} E Φ e :
  (∀ σ, stuck e σ) →
  ⊢ WP e @ E ?{{ Φ }}.
Proof.
  iIntros (Hstuck). iApply wp_lift_stuck.
  - destruct(to_val e) as [v|] eqn:He; last done.
    rewrite -He. by case: (Hstuck inhabitant).
  - iIntros (ex atr K ? tp1 tp2 σ) "_".
    iMod (fupd_mask_subseteq ∅) as "_"; first set_solver; eauto.
Qed.

(* Atomic steps don't need any mask-changing business here, one can
   use the generic lemmas here. *)
Lemma wp_lift_atomic_step_fupd {s E1 E2 Φ} e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 e1 = ζ⌝ →
    state_interp extr atr ={E1}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E1}[E2]▷=∗
      ∃ δ2 ℓ, 
        state_interp
          (trace_extend extr (Some ζ) (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
           {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (?) "H".
  iApply (wp_lift_step_fupd s E1 _ e1); first done.
  iIntros (ex atr K tp1 tp2 σ1 Hvalidex ? Hloc) "Hsi".
  iMod ("H" with "[//] [//] [] Hsi") as "[$ H]".
  { iPureIntro. by erewrite <-locale_fill. }
  iMod (fupd_mask_subseteq ∅) as "Hclose"; first set_solver.
  iIntros "!>" (e2 σ2 efs ?). iMod "Hclose" as "_".
  iMod ("H" $! e2 σ2 efs with "[#]") as "H"; [done|].
  iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver|]. iIntros "!> !>".
  iMod "Hclose" as "_". iMod "H" as (st' ℓ) "(? & HQ & $)".
  destruct (to_val e2) eqn:?; last by iExFalso.
  iModIntro; iExists _, _.
  iFrame.
  iApply wp_value; last done. by apply of_to_val.
Qed.

Lemma wp_lift_atomic_step {s E Φ} e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 e1 = ζ⌝ →
    state_interp extr atr ={E}=∗
    ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ∃ δ2 ℓ, 
        state_interp
          (trace_extend extr (Some ζ) (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
           {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?????????) "?". iMod ("H" with "[//] [//] [//] [$]") as "[$ H]".
  iIntros "!> *". iIntros (Hstep) "!> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_det_step_no_fork
      `{!AllowsPureStep M Σ} `{!Inhabited (state Λ)} {s E E' Φ} e1 e2 ζ:
  (∀ σ1, if s is NotStuck then reducible e1 σ1 else to_val e1 = None) →
  (∀ σ1 e2' σ2 efs', prim_step e1 σ1 e2' σ2 efs' →
    σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> WP e2 @ s; ζ; E {{ Φ }}) ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork s E E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (e' efs' σ (?&->&?)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd
      `{!AllowsPureStep M Σ} `{!Inhabited (state Λ)} s E E' ζ e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  (|={E}[E']▷=>^n WP e2 @ s; ζ; E {{ Φ }}) ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  iApply wp_lift_pure_det_step_no_fork.
  - intros σ. specialize (Hsafe σ). destruct s; eauto using reducible_not_val.
  - done.
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later
      `{!AllowsPureStep M Σ} `{!Inhabited (state Λ)} s E ζ e1 e2 φ n Φ :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 @ s; ζ; E {{ Φ }} ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.
End lifting.
