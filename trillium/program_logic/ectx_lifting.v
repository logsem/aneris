(** Some derived lemmas for ectx-based languages *)
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export
     ectx_language weakestpre lifting.
Set Default Proof Using "Type".

Section wp.
Context {Λ : ectxLanguage} `{!irisG Λ M Σ} {Hinh : Inhabited (state Λ)}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Hint Resolve head_prim_reducible head_reducible_prim_step : core.
Local Definition reducible_not_val_inhabitant e :=
  reducible_not_val e inhabitant.
Hint Resolve reducible_not_val_inhabitant : core.
Hint Resolve head_stuck_stuck : core.

Lemma wp_lift_head_step_fupd {s E Φ} e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗
    state_interp extr atr ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={∅}=∗ ▷ |={∅,E}=>
      ∃ δ2 ℓ,
        state_interp
          (trace_extend extr (inl ζ) (tp1 ++ fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      WP e2 @ s; ζ; E {{ Φ }} ∗
      [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
         {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_step_fupd=>//.
  iIntros (ex atr K tp1 tp2 σ1 Hexvalid hex Hloc) "Hsi".
  iMod ("H" with "[//] [//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by destruct s; eauto.
  iIntros (e2 σ2 efs ?).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_head_step {s E Φ} e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ fill K e1 :: tp2, σ1)⌝ →
    state_interp extr atr ={E,∅}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={∅,E}=∗
      ∃ δ2 ℓ, 
        state_interp
          (trace_extend extr (inl ζ) (tp1 ++ fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      WP e2 @ s; ζ; E {{ Φ }} ∗
      [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
         {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_head_step_fupd; [done|]. iIntros (?????????) "?".
  iMod ("H" with "[//] [//] [$]") as "[$ H]".
  iIntros "!>" (e2 σ2 efs ?) "!> !>".
  iApply "H"; done.
Qed.

Lemma wp_lift_head_stuck E Φ e ζ:
  to_val e = None →
  sub_redexes_are_values e →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ fill K e :: tp2, σ)⌝ →
    state_interp extr atr ={E,∅}=∗ ⌜head_stuck e σ⌝)
  ⊢ WP e @ ζ; E ?{{ Φ }}.
Proof.
  iIntros (??) "H". iApply wp_lift_stuck; first done.
  iIntros (????????) "Hsi". iMod ("H" with "[] [] Hsi") as "%"; by auto.
Qed.

Lemma wp_lift_pure_head_stuck E Φ e :
  to_val e = None →
  sub_redexes_are_values e →
  (∀ σ, head_stuck e σ) →
  ⊢ WP e @ E ?{{ Φ }}.
Proof using Hinh.
  iIntros (?? Hstuck). iApply wp_lift_head_stuck; [done|done|].
  iIntros (???????) "_". iMod (fupd_mask_subseteq ∅) as "_"; first set_solver.
  auto; done.
Qed.

Lemma wp_lift_atomic_head_step_fupd {s E1 E2 Φ} e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 e1 = ζ⌝ →
    state_interp extr atr ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E1}[E2]▷=∗
      ∃ δ2 ℓ,
        state_interp
          (trace_extend extr (inl ζ) (tp1 ++ fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
         {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step_fupd; [done|].
  iIntros (?????????) "Hsi". iMod ("H" with "[//] [//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by destruct s; auto.
  iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step {s E Φ} e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 e1 = ζ⌝ →
    state_interp extr atr ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
      ∃ δ2 ℓ, 
        state_interp
          (trace_extend extr (inl ζ) (tp1 ++ fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      from_option Φ False (to_val e2) ∗
      [∗ list] i ↦ef ∈ efs, WP ef @ s; locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef; ⊤
         {{ fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) }})
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_step; eauto.
  iIntros (?????????) "Hsi". iMod ("H" with "[//] [//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by destruct s; auto. iNext. iIntros (e2 σ2 efs Hstep).
  iApply "H"; eauto.
Qed.

Lemma wp_lift_atomic_head_step_no_fork_fupd {s E1 E2 Φ} e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 e1 = ζ⌝ →
    state_interp extr atr ={E1}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E1}[E2]▷=∗
      ∃ δ2 ℓ,
        ⌜efs = [] ⌝∗
        state_interp
          (trace_extend extr (inl ζ) (tp1 ++ fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step_fupd; [done|].
  iIntros (?????????) "Hsi".
  iMod ("H" with "[//] [//] [//] Hsi") as "[$ H]".
  iModIntro.
  iIntros (v2 σ2 efs Hstep).
  iMod ("H" $! v2 σ2 efs with "[# //]") as "H".
  iIntros "!> !>". iMod "H" as (st' ℓ) "(-> & ? & ?) /=".
  iModIntro; iExists _, _.
  iFrame.
Qed.

Lemma wp_lift_atomic_head_step_no_fork {s E Φ} e1 ζ:
  to_val e1 = None →
  (∀ (extr : execution_trace Λ) (atr : auxiliary_trace M) K tp1 tp2 σ1,
    ⌜valid_exec extr⌝ -∗
    ⌜trace_ends_in extr (tp1 ++ fill K e1 :: tp2, σ1)⌝ →
    ⌜locale_of tp1 e1 = ζ⌝ →
    state_interp extr atr ={E}=∗
    ⌜head_reducible e1 σ1⌝ ∗
    ▷ ∀ e2 σ2 efs, ⌜head_step e1 σ1 e2 σ2 efs⌝ ={E}=∗
       ∃ δ2 ℓ, 
         ⌜efs = []⌝ ∗ state_interp
          (trace_extend extr (inl ζ) (tp1 ++ fill K e2 :: tp2 ++ efs, σ2))
          (trace_extend atr ℓ δ2) ∗
      from_option Φ False (to_val e2))
  ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof.
  iIntros (?) "H". iApply wp_lift_atomic_head_step; eauto.
  iIntros (?????????) "Hsi".
  iMod ("H" with "[//] [//] [//] Hsi") as "[$ H]".
  iModIntro.
  iNext; iIntros (v2 σ2 efs Hstep).
  iMod ("H" $! v2 σ2 efs with "[//]") as (st' ℓ) "(-> & ? & ?) /=".
  iModIntro; iExists _, _.
  iFrame.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork
      `{!AllowsPureStep M Σ}  {s E E' Φ} e1 e2 ζ:
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={E}[E']▷=> WP e2 @ s; ζ; E {{ Φ }}) ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -(wp_lift_pure_det_step_no_fork e1 e2); eauto.
  destruct s; by auto.
Qed.

Lemma wp_lift_pure_det_head_step_no_fork'
      `{!AllowsPureStep M Σ} {s E Φ} e1 e2 ζ:
  to_val e1 = None →
  (∀ σ1, head_reducible e1 σ1) →
  (∀ σ1 e2' σ2 efs',
    head_step e1 σ1 e2' σ2 efs' → σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  ▷ WP e2 @ s; ζ; E {{ Φ }} ⊢ WP e1 @ s; ζ; E {{ Φ }}.
Proof using Hinh.
  intros. rewrite -[(WP e1 @ s; _; _ {{ _ }})%I]wp_lift_pure_det_head_step_no_fork //.
  rewrite -step_fupd_intro //.
Qed.
End wp.
