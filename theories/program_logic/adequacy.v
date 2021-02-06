From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic.lib Require Import wsat.
From aneris.prelude Require Import quantifiers iris_extraction.
From aneris.program_logic Require Export weakestpre traces.

Set Default Proof Using "Type".
Import uPred.

(* move *)
Lemma step_tp_length {Λ} c κ c' :
  step (Λ := Λ) c κ c' → length c.1 ≤ length c'.1.
Proof.
  inversion 1; simplify_eq; last done.
  rewrite !app_length /= !app_length; lia.
Qed.

Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ {{ Φ }})%I.
Notation posts_of t Φs :=
  ([∗ list] vΦ ∈
    (omap (λ x, (λ v, (v, x.2)) <$> to_val x.1)
          (zip_with (λ x y, (x, y)) t Φs)), vΦ.2 vΦ.1)%I.

Definition config_wp `{!irisG Λ AS Σ} : iProp Σ :=
  □ ∀ σ1 δ1 κ σ2 κs nt,
        ⌜config_step σ1 κ σ2⌝ →
        state_interp σ1 δ1 κs nt ={⊤}[∅]▷=∗
          ∃ δ2, ⌜valid_state_evolution AS σ1 δ1 κ σ2 δ2⌝ ∗
                 state_interp σ2 δ2 (κs ++ κ) nt.

Instance config_wp_persistent `{!irisG Λ AS Σ} : Persistent config_wp.
Proof. apply _. Qed.

Typeclasses Opaque config_wp.

(* the guarded definition of simulation. *)
Definition Gsim_pre Σ {Λ} (AS : AuxState Λ) (s : stuckness)
           (φ : execution_trace Λ → auxiliary_trace AS → Prop)
           (gsim : execution_trace Λ -d> auxiliary_trace AS -d> iPropO Σ) :
  execution_trace Λ -d> auxiliary_trace AS -d> iPropO Σ :=
  (λ ex atr,
   ▷ (⌜valid_system_trace AS ex atr⌝ ∧
      ⌜φ ex atr⌝ ∧
      ∀ c c' κ δ,
        ⌜exec_ends_in ex c⌝ →
        ⌜auxtr_ends_in atr δ⌝ →
        ⌜step c κ c'⌝ →
        ▷ ▷ (∃ δ', ⌜valid_state_evolution AS c.2 δ κ c'.2 δ'⌝ ∧
                 gsim (exec_extend ex κ c') (auxtr_extend atr δ'))))%I.

Local Instance Gsim_pre_contractive Σ M Λ s φ :
  Contractive (@Gsim_pre Σ M Λ s φ).
Proof.
  rewrite /Gsim_pre=> n wp wp' HGsm ex sm.
  repeat (f_contractive || f_equiv); repeat (apply dist_S; try apply HGsm).
Qed.

Definition Gsim Σ {Λ} (AS : AuxState Λ) (s : stuckness)
           (φ : execution_trace Λ → auxiliary_trace AS → Prop) :
  execution_trace Λ → auxiliary_trace AS → iProp Σ :=
  fixpoint (Gsim_pre Σ AS s φ).

Instance is_except_0_wptp {Σ} Λ AS s φ ex sm:
  IsExcept0 (@Gsim Σ Λ AS s φ ex sm).
Proof.
  rewrite /IsExcept0; iIntros "H".
  rewrite /Gsim (fixpoint_unfold (Gsim_pre _ _ _ _) _ _).
  iMod "H".
  iApply "H"; done.
Qed.

Global Instance Gsim_plain Σ M {Λ} s φ ex sm : Plain (@Gsim Σ M Λ s φ ex sm).
Proof.
  rewrite /Plain.
  iIntros "H".
  iLöb as "IH" forall (ex sm).
  rewrite /Gsim (fixpoint_unfold (Gsim_pre _ _ _ _) _ _).
  rewrite {3 5}/Gsim_pre.
  iApply later_plainly_1; iNext.
  iDestruct "H" as "(#H1 & #H2 & H)".
  iSplit; first (iClear "IH H"; iModIntro; done).
  iSplit; first (iClear "IH H"; iModIntro; done).
  iIntros (c ? ? ? ? ? ?).
  iDestruct ("H" with "[] [] []") as "H"; [done|done|done|].
  do 2 (iApply later_plainly_1; iNext).
  iDestruct "H" as (δ') "(#Hst' & H)".
  iExists _.
  iSplitR; first by iClear "IH"; iModIntro.
  iApply "IH"; done.
Qed.

Section adequacy_helper_lemmas.
  Context `{!irisG Λ AS Σ}.

  Lemma wp_take_step s n δ Φ e1 σ1 κ e2 σ2 efs κs :
    prim_step e1 σ1 κ e2 σ2 efs →
    state_interp σ1 δ κs n -∗
    WP e1 @ s; ⊤ {{ v, Φ v } } ={⊤}[∅]▷=∗
    ∃ δ', ⌜valid_state_evolution AS σ1 δ κ σ2 δ'⌝ ∗
      state_interp σ2 δ' (κs ++ κ) (length efs + n) ∗
      WP e2 @ s; ⊤ {{ v, Φ v } } ∗
      ([∗ list] ef ∈ efs, WP ef @ s; ⊤ {{ v, fork_post v }}).
  Proof.
    iIntros (Hstp) "HSI Hwp".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e1) eqn:He1.
    { erewrite val_stuck in He1; done. }
    iMod ("Hwp" with "HSI") as "[Hs Hwp]".
    iMod ("Hwp" with "[]") as "Hwp"; first done.
    iModIntro; iNext.
    iMod "Hwp" as (δ') "(% & ? & ? & ?)".
    iModIntro; iExists _; iFrame; done.
  Qed.

  Lemma wp_not_stuck e σ κs s Φ n δ :
    state_interp σ δ κs n -∗
    WP e @ s; ⊤ {{ v, Φ v }} ={⊤}=∗
    state_interp σ δ κs n ∗
    WP e @ s; ⊤ {{ v, Φ v }} ∗
    ⌜s = NotStuck → not_stuck e σ⌝.
  Proof.
    iIntros "HSI Hwp".
    rewrite /not_stuck assoc.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "[HSI Hwp]".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e) eqn:He.
    - iModIntro; iPureIntro; eauto.
    - iApply fupd_plain_mask.
      iMod ("Hwp" $! _ _ [] with "HSI") as "[Hs Hwp]".
      iModIntro; destruct s; [iDestruct "Hs" as %?|]; eauto.
  Qed.

  Lemma wptp_not_stuck t σ κs s Φs n δ :
    state_interp σ δ κs n -∗ wptp s t Φs ={⊤}=∗
    state_interp σ δ κs n ∗ wptp s t Φs ∗
    ⌜∀ e, e ∈ t → s = NotStuck → not_stuck e σ⌝.
  Proof.
    iIntros "HSI Ht".
    rewrite assoc.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "[HSI Ht]".
    iIntros (e He).
    apply elem_of_list_split in He as (t1 & t2 & ->).
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2') "[-> [Ht1 Het2]]".
    iDestruct (big_sepL2_cons_inv_l with "Het2") as (Φ Φs2) "[-> [He Ht2]]".
    iMod (wp_not_stuck with "HSI He") as "(_ & _ & ?)"; done.
  Qed.

  Lemma wp_of_val_post e s Φ :
    WP e @ s; ⊤ {{ v, Φ v }} ={⊤}=∗
    from_option Φ True (to_val e) ∗
    (from_option Φ True (to_val e) -∗ WP e @ s; ⊤ {{ v, Φ v }}).
  Proof.
    iIntros "Hwp".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e) eqn:He.
    - iMod "Hwp"; simpl; iFrame; auto.
    - iModIntro.
      iSplit; first done.
      iIntros "_"; done.
  Qed.

  Lemma wptp_app s t1 Φs1 t2 Φs2 :
    wptp s t1 Φs1 -∗ wptp s t2 Φs2 -∗ wptp s (t1 ++ t2) (Φs1 ++ Φs2).
  Proof.
    iIntros "H1 H2"; iApply (big_sepL2_app with "[H1] [H2]"); eauto.
  Qed.

  Lemma wptp_cons s e Φ t Φs :
    WP e @ s; ⊤ {{v, Φ v}} -∗ wptp s t Φs -∗ wptp s (e :: t) (Φ :: Φs).
  Proof. iIntros "? ?"; rewrite big_sepL2_cons; iFrame. Qed.

  Lemma wptp_of_val_post t s Φs :
    wptp s t Φs ={⊤}=∗ posts_of t Φs ∗ (posts_of t Φs -∗ wptp s t Φs).
  Proof.
    iIntros "Ht"; simpl.
    iInduction t as [|e t IHt] "IH" forall (Φs); simpl.
    { iDestruct (big_sepL2_nil_inv_l with "Ht") as %->; eauto. }
    iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs') "[-> [He Ht]] /=".
    iMod (wp_of_val_post with "He") as "[Hpost Hback]".
    iMod ("IH" with "Ht") as "[Ht Htback]".
    iModIntro.
    destruct (to_val e); simpl.
    - iFrame.
      iIntros "[Hpost Htpost]".
      iSplitL "Hpost Hback"; [iApply "Hback"|iApply "Htback"]; iFrame.
    - iFrame.
      iIntros "Hefspost".
      iSplitL "Hback"; [iApply "Hback"|iApply "Htback"]; iFrame; done.
  Qed.

  Lemma take_step s Φs c κ c' κs δ :
    step c κ c' →
    config_wp -∗
    state_interp c.2 δ κs (length c.1) -∗
    wptp s c.1 Φs  ={⊤}[∅]▷=∗
    ⌜∀ e2, s = NotStuck → e2 ∈ c'.1 → not_stuck e2 c'.2⌝ ∗
    ∃ δ', ⌜valid_state_evolution AS c.2 δ κ c'.2 δ'⌝ ∗
      state_interp c'.2 δ' (κs ++ κ) (length c'.1) ∗
      posts_of c'.1 (Φs ++ replicate (length c'.1 - length c.1) fork_post) ∗
      (posts_of c'.1 (Φs ++ replicate (length c'.1 - length c.1) fork_post) -∗
        wptp s c'.1 (Φs ++ replicate (length c'.1 - length c.1) fork_post)).
  Proof.
    iIntros (Hstep) "config_wp HSI Hc1".
    inversion Hstep as
        [e1 σ1 e2 σ2 efs t1 t2 -> -> Hpstep|σ1 σ2 t -> -> Hcfgstep].
    - rewrite /=.
      replace (length (t1 ++ e2 :: t2 ++ efs) - length (t1 ++ e1 :: t2)) with
          (length efs); last first.
      { rewrite !app_length /= !app_length; lia. }
      iDestruct (big_sepL2_app_inv_l with "Hc1") as
          (Φs1 Φs2') "[-> [Ht1 Het2]]".
      iDestruct (big_sepL2_cons_inv_l with "Het2") as (Φ Φs2) "[-> [He Ht2]]".
      iMod (wp_take_step with "HSI He") as "He"; [done|].
      iModIntro; iNext.
      iMod "He" as (δ') "(% & HSI & He2 & Hefs) /=".
      rewrite -(big_sepL2_replicate_r efs fork_post
                 (λ _ e Φ, WP e @ s; ⊤ {{v, Φ v}})%I); last reflexivity.
      iMod (wptp_not_stuck with "HSI Hefs") as "[HSI [Hefs %]]".
      iMod (wptp_not_stuck with "HSI Ht1") as "[HSI [Ht1 %]]".
      iMod (wptp_not_stuck with "HSI Ht2") as "[HSI [Ht2 %]]".
      iMod (wp_not_stuck with "HSI He2") as "[HSI [He2 %]]".
      iDestruct (wptp_app with "Ht2 Hefs") as "Ht2efs".
      iDestruct (wptp_cons with "He2 Ht2efs") as "He2t2efs".
      iDestruct (wptp_app with "Ht1 He2t2efs") as "Hc2".
      iMod (wptp_of_val_post with "Hc2") as "[Hc2posts Hc2back]".
      iModIntro; simpl in *.
      iSplit.
      { iPureIntro; set_solver. }
      iExists δ'.
      iSplit; first done.
      rewrite [length efs + _]Nat.add_comm.
      rewrite -app_length -!assoc_L /= !app_length /=.
      iFrame.
    - rewrite /= !Nat.sub_diag /= app_nil_r.
      rewrite /config_wp.
      iMod ("config_wp" with "[] HSI") as "Hcfg"; first done.
      iModIntro; iNext; iMod "Hcfg" as (δ2) "[% HSI]".
      iMod (wptp_not_stuck with "HSI Hc1") as "[HSI [Hc1 %]]".
      iMod (wptp_of_val_post with "Hc1") as "[Hc1posts Hc1back]".
      iModIntro.
      iSplit; first by auto.
      iExists δ2; iSplit; first done.
      iFrame.
  Qed.

End adequacy_helper_lemmas.

Theorem wp_strong_adequacy_helper Σ Λ AS `{!invPreG Σ}
        (s: stuckness) (φ : execution_trace Λ → auxiliary_trace AS → Prop)
        e1 σ1 δ :
  (∀ `{Hinv : !invG Σ},
    ⊢ |={⊤}=> ∃
         (stateI : state Λ → (aux_state AS) → list (observation Λ) → nat →
                   iProp Σ)
         (Φ fork_post : val Λ → iProp Σ),
       let _ : irisG Λ AS Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI σ1 δ [] 1 ∗
       WP e1 @ s; ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace Λ) (atr : auxiliary_trace AS)
            δ' c κs,
         ⌜valid_system_trace AS ex atr⌝ -∗
         ⌜exec_starts_in ex ([e1], σ1)⌝ -∗
         ⌜auxtr_starts_in atr δ⌝ -∗
         ⌜exec_ends_in ex c⌝ -∗
         ⌜auxtr_ends_in atr δ'⌝ -∗
         ⌜∀ ex' atr',
            exec_contract ex ex' → auxtr_contract atr atr' → φ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         stateI c.2 δ' κs (length c.1) -∗
         posts_of c.1 (Φ :: replicate (length c.1 - 1) fork_post) -∗
         |={⊤, ∅}=> ⌜φ ex atr⌝)) →
  ⊢ Gsim Σ AS s φ (singleton_exec ([e1], σ1)) (singleton_auxtr δ).
Proof.
  intros Hwp.
  iMod wsat_alloc as (Hinv) "[Hw HE]".
  iPoseProof Hwp as "Hwp".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("Hwp" with "[$Hw $HE]") as ">[Hw [HE Hwp']]".
  iClear "Hwp".
  iDestruct "Hwp'" as (stateI Φ fork_post) "(#config_wp & HSI & Hwp & Hstep)".
  clear Hwp.
  set (IrisG Λ AS Σ Hinv stateI fork_post).
  iAssert (∃ ex atr c1 δ1 κs,
              ⌜singleton_exec ([e1], σ1) = ex⌝ ∗
              ⌜singleton_auxtr δ = atr⌝ ∗
              ⌜([e1], σ1) = c1⌝ ∗
              ⌜δ = δ1⌝ ∗
              ⌜length c1.1 ≥ 1⌝ ∗
              stateI c1.2 δ1 κs (length c1.1) ∗
              wptp s c1.1 (Φ :: replicate (length c1.1 - 1) fork_post))%I
    with "[HSI Hwp]" as "Hex".
  { iExists (singleton_exec ([e1], σ1)), (singleton_auxtr δ), ([e1], σ1), δ;
      simpl; auto 10 with iFrame. }
  iDestruct "Hex" as (ex atr c1 δ1 κs Hexsing Hatrsing Hc1 Hδ1 Hlen) "[HSI Htp]".
  assert
    (valid_system_trace AS ex atr ∧
     exec_starts_in ex ([e1], σ1) ∧
     exec_ends_in ex c1 ∧
     auxtr_starts_in atr δ ∧
     auxtr_ends_in atr δ1 ∧
     (∀ ex' atr',
            exec_contract ex ex' → auxtr_contract atr atr' → φ ex' atr'))
    as Hextras.
  { rewrite -Hexsing -Hatrsing -Hc1 -Hδ1.
    split; first apply valid_system_trace_singletons.
    repeat (split; first done).
    intros ? ? ?%not_exec_contract_singleton; done. }
  clear Hc1 Hδ1.
  rewrite Hexsing Hatrsing; clear Hexsing Hatrsing.
  iLöb as "IH" forall (ex atr c1 δ1 κs Hextras Hlen) "HSI Htp".
  destruct Hextras as (Hexatr & Hex & Hc1 & Hatr & Hδ1 & Hφ).
  rewrite {2}/Gsim (fixpoint_unfold (Gsim_pre _ _ _ _) _ _).
  iSplit; first done.
  iPoseProof (wptp_not_stuck with "[$HSI] Htp") as "Htp".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("Htp" with "[$Hw $HE]") as ">(Hw & HE & HSI & Htp & %)".
  iPoseProof (wptp_of_val_post with "Htp") as "Htp".
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("Htp" with "[$Hw $HE]") as ">(Hw & HE & Hpost & Hback)".
  iAssert (▷ ⌜φ ex atr⌝)%I as "#Hφ".
  { iMod ("Hstep" with "[] [] [] [] [] [] [] HSI Hpost [$Hw $HE]")
      as ">(Hw & HE & %)"; auto. }
  iDestruct ("Hback" with "Hpost") as "Htp".
  iNext; iSplit; first done.
  iDestruct "Hφ" as %Hφ'.
  iIntros (c c' κ δ' Hc Hδ' Hstep).
  pose proof (exec_ends_in_inj ex c c1 Hc Hc1); simplify_eq.
  pose proof (auxtr_ends_in_inj atr δ1 δ' Hδ1 Hδ'); simplify_eq.
  iPoseProof (take_step with "config_wp HSI Htp") as "Hstp"; first done.
  rewrite uPred_fupd_eq /uPred_fupd_def.
  iMod ("Hstp" with "[$Hw $HE]") as ">(Hw & HE & Hstp)".
  iNext.
  iMod ("Hstp" with "[$Hw $HE]") as ">(Hw & HE & % & H)".
  iDestruct "H" as (δ'') "(% & HSI & Hpost & Hback)"; simpl in *.
  rewrite -!replicate_plus.
  pose proof (step_tp_length _ _ _ Hstep).
  replace (length c1.1 - 1 + (length c'.1 - length c1.1)) with
      (length c'.1 - 1); last lia.
  iAssert (▷ ⌜φ (exec_extend ex κ c') (auxtr_extend atr δ'')⌝)%I as "#Hextend'".
  { iMod ("Hstep" with "[] [] [] [] [] [] [] HSI Hpost [$Hw $HE]")
      as ">(Hw & HE & %)"; iPureIntro; last done.
    - eapply valid_system_trace_extend; eauto.
    - eapply exec_extend_starts_in; eauto.
    - eapply auxtr_extend_starts_in; eauto.
    - eapply exec_extend_ends_in; eauto.
    - eapply auxtr_extend_ends_in; eauto.
    - intros ? ? ->%exec_contract_of_extend ->%auxtr_contract_of_extend; done.
    - done. }
  iDestruct ("Hback" with "Hpost") as "Htp".
  iNext.
  iExists _; iSplit; first done.
  iApply ("IH" with "[] [] Hw HE Hstep HSI"); [|iPureIntro; lia|by iFrame].
  iPureIntro; split_and!.
  - eapply valid_system_trace_extend; eauto.
  - eapply exec_extend_starts_in; eauto.
  - eapply exec_extend_ends_in; eauto.
  - eapply auxtr_extend_starts_in; eauto.
  - eapply auxtr_extend_ends_in; eauto.
  - intros ? ? ->%exec_contract_of_extend ->%auxtr_contract_of_extend; done.
Qed.

Definition monotone {A} (Ψ : (A → Prop) → (A → Prop)) :=
  ∀ (P Q : A → Prop), (∀ x, P x → Q x) → ∀ x, Ψ P x → Ψ Q x.

Definition GFX {A} (Ψ : (A → Prop) → (A → Prop)) : A → Prop :=
  λ x, ∃ P, P x ∧ (∀ x, P x → Ψ P x).

Lemma GFX_post_fixpoint {A} (Ψ : (A → Prop) → (A → Prop)) :
  monotone Ψ → ∀ x, GFX Ψ x → Ψ (GFX Ψ) x.
Proof.
  intros Hmono x (P & HP & HΨP).
  eapply Hmono; [|by apply HΨP].
  intros; exists P; split; auto.
Qed.

Lemma GFX_fixpoint {A} (Ψ : (A → Prop) → (A → Prop)) :
  monotone Ψ → ∀ x, Ψ (GFX Ψ) x ↔ GFX Ψ x.
Proof.
  intros Hmono x; split.
  - intros HΨ.
    exists (Ψ (GFX Ψ)); split; first done.
    intros ? ?; eapply Hmono; last done.
    apply GFX_post_fixpoint; done.
  - apply GFX_post_fixpoint; done.
Qed.

Definition simulation_pre {Λ AS}
           (φ : execution_trace Λ → auxiliary_trace AS → Prop)
           (pure_wptp : execution_trace Λ → auxiliary_trace AS → Prop) :
  execution_trace Λ → auxiliary_trace AS → Prop :=
  λ ex atr,
  valid_system_trace AS ex atr ∧
  φ ex atr ∧
  ∀ c c' κ δ,
    exec_ends_in ex c →
    auxtr_ends_in atr δ →
    step c κ c' →
    ∃ δ', valid_state_evolution AS c.2 δ κ c'.2 δ' ∧
           pure_wptp (exec_extend ex κ c') (auxtr_extend atr δ').

Local Definition simulation_pre_curried {Λ AS}
      (φ : execution_trace Λ → auxiliary_trace AS → Prop) :
  (execution_trace Λ * auxiliary_trace AS → Prop) →
  (execution_trace Λ * auxiliary_trace AS → Prop) :=
  λ ψ (exatr : execution_trace Λ * auxiliary_trace AS),
  (simulation_pre φ (λ ex atr, ψ (ex, atr)) exatr.1 exatr.2).

Lemma simulation_pre_curried_mono {Λ AS}
      (φ : execution_trace Λ → auxiliary_trace AS → Prop) :
  monotone (simulation_pre_curried φ).
Proof.
  intros P Q HPQ [ex atr] (?&?&HP); repeat (split; first done).
  intros ? ? ? ? ? ? ?.
  edestruct HP as (?&?&?); eauto.
Qed.

Definition simulation {Λ AS}
           (φ : execution_trace Λ → auxiliary_trace AS → Prop) :=
  λ ex atr, GFX (simulation_pre_curried φ) (ex, atr).

Lemma simulation_unfold {Λ AS}
      (φ : execution_trace Λ → auxiliary_trace AS → Prop) ex atr :
  simulation φ ex atr ↔ simulation_pre φ (simulation φ) ex atr.
Proof.
  symmetry; rewrite /simulation /=.
  apply (λ H, GFX_fixpoint (simulation_pre_curried φ) H (_, _)).
  apply simulation_pre_curried_mono.
Qed.

Definition valid_state_evolution_finitary {Λ} (AS : AuxState Λ) :=
  ∀ c δ κ c',
    smaller_card (sig (λ δ', valid_state_evolution AS c δ κ c' δ')) nat.

Theorem wp_strong_adequacy Λ AS Σ `{!invPreG Σ}
        (s: stuckness)
        (φ : execution_trace Λ → auxiliary_trace AS → Prop)
        e1 σ1 δ :
  valid_state_evolution_finitary AS →
  (∀ `{Hinv : !invG Σ},
    ⊢ |={⊤}=> ∃
         (stateI : state Λ → aux_state AS → list (observation Λ) → nat → iProp Σ)
         (Φ fork_post : val Λ → iProp Σ),
       let _ : irisG Λ AS Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI σ1 δ [] 1 ∗
       WP e1 @ s; ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace Λ) (atr : auxiliary_trace AS)
            δ' c κs,
         ⌜valid_system_trace AS ex atr⌝ -∗
         ⌜exec_starts_in ex ([e1], σ1)⌝ -∗
         ⌜auxtr_starts_in atr δ⌝ -∗
         ⌜exec_ends_in ex c⌝ -∗
         ⌜auxtr_ends_in atr δ'⌝ -∗
         ⌜∀ ex' atr',
            exec_contract ex ex' → auxtr_contract atr atr' → φ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         stateI c.2 δ' κs (length c.1) -∗
         posts_of c.1 (Φ :: replicate (length c.1 - 1) fork_post) -∗
         |={⊤, ∅}=> ⌜φ ex atr⌝)) →
  simulation φ (singleton_exec ([e1], σ1)) (singleton_auxtr δ).
Proof.
  intros Hsc Hwptp%wp_strong_adequacy_helper; last done.
  exists (λ exatr, ⊢ Gsim Σ AS s φ exatr.1 exatr.2); split; first done.
  clear Hwptp.
  intros [ex atr] Hgsim; simpl.
  revert Hgsim.
  rewrite {1}/Gsim (fixpoint_unfold (Gsim_pre _ _ _ _) _ _); intros Hgsim;
    simpl in *.
  revert Hgsim; rewrite extract_later; intros Hgsim.
  apply extract_and in Hgsim as [Hvlt Hgsim].
  revert Hvlt; rewrite extract_pure; intros Hvlt.
  split; first done.
  apply extract_and in Hgsim as [Hφ Hgsim].
  revert Hφ; rewrite extract_pure; intros Hφ.
  split; first done.
  intros c c' κ δ' Hsmends Hsimends Hstep.
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim c).
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim c').
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim κ).
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim δ').
  apply (extract_impl ⌜_⌝) in Hgsim; last by apply extract_pure.
  apply (extract_impl ⌜_⌝) in Hgsim; last by apply extract_pure.
  apply (extract_impl ⌜_⌝) in Hgsim; last by apply extract_pure.
  revert Hgsim; rewrite !extract_later; intros Hgsim.
  apply extract_exists_alt in Hgsim as [δ'' Hgsim]; last done.
  exists δ''.
  revert Hgsim.
  rewrite !extract_and.
  rewrite !extract_pure; done.
Qed.

Lemma simulation_simulates {Λ AS} e σ δ φ :
  simulation
    (Λ := Λ) (AS := AS) φ (singleton_exec ([e], σ)) (singleton_auxtr δ) →
  ∀ ex, exec_starts_in ex ([e], σ) → valid_exec ex →
    ∃ atr, simulation φ ex atr.
Proof.
  intros Hsm ex Hexstr Hex.
  induction Hex as [|? ? ? ? ? ? ? IHex].
  - apply singleton_exec_starts_in_inv in Hexstr as ->.
    exists (singleton_auxtr δ); eauto using valid_system_trace_singletons.
  - destruct IHex as [atr Hsim].
    { eapply exec_extend_starts_in_inv; eauto. }
    rewrite -> simulation_unfold in Hsim.
    destruct Hsim as (Hvlt & Hφ & Hsim).
    edestruct @valid_system_trace_ends_in as (_& δ' &_&?); eauto.
    edestruct Hsim as (?&?&?); eauto.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) : Prop := {
  adequate_result ex t2 σ2 v2 :
    valid_exec ex →
   exec_starts_in ex ([e1], σ1) →
   exec_ends_in ex (of_val v2 :: t2, σ2) →
   φ v2 σ2;
  adequate_not_stuck ex t2 σ2 e2 :
   s = NotStuck →
   valid_exec ex →
   exec_starts_in ex ([e1], σ1) →
   exec_ends_in ex (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ ex t2 σ2,
      valid_exec ex →
      exec_starts_in ex ([e1], σ1) →
      exec_ends_in ex (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) ex t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  valid_exec ex →
  exec_starts_in ex ([e1], σ1) →
   exec_ends_in ex (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, erased_step (t2, σ2) (t3, σ3).
Proof.
  intros Had ? ? ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had ex t2 σ2 e2)
    as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3, κ; econstructor; eauto.
Qed.

Local Definition wp_adequacy_relation Λ AS s (φ : val Λ → Prop)
           (ex : execution_trace Λ) (atr : @auxiliary_trace Λ AS) : Prop :=
  ∀ c, exec_ends_in ex c →
       (∀ v2 t2', c.1 = of_val v2 :: t2' → φ v2) ∧
       (∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2).

Local Lemma wp_adequacy_relation_adequacy {Λ AS} s e σ δ φ :
  simulation
    (wp_adequacy_relation Λ AS s φ)
    (singleton_exec ([e], σ))
    (singleton_auxtr δ) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hsm; apply adequate_alt.
  intros ex t2 σ2 Hex Hexstr Hexend.
  eapply simulation_simulates in Hex as [atr Hatr]; eauto.
  rewrite -> simulation_unfold in Hatr.
  destruct Hatr as (Hvlt & Hψ & Hatr).
  apply (Hψ (t2, σ2)); done.
Qed.

Corollary wp_adequacy Λ AS Σ `{!invPreG Σ} s e σ δ φ :
  valid_state_evolution_finitary AS →
  (∀ `{Hinv : !invG Σ},
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → aux_state AS → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ AS Σ :=
           IrisG _ _ _ Hinv (λ σ δ κs _, stateI σ δ κs) fork_post in
       config_wp ∗ stateI σ δ [] ∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros ? Hwp; apply (wp_adequacy_relation_adequacy (AS := AS) _ _ _ δ).
  apply (wp_strong_adequacy Λ AS Σ s); first done.
  iIntros (?) "".
  iMod Hwp as (stateI fork_post) "(config_wp & HSI & Hwp)".
  iModIntro; iExists _, _, _; iFrame.
  iIntros (ex atr δ' c κs Hvlt Hexs Hatrs Hexe Hatre Hψ Hnst) "HSI Hposts".
  iApply fupd_mask_weaken; first done.
  iIntros (c' Hc').
  assert (c' = c) as -> by by eapply exec_ends_in_inj.
  iSplit; last done.
  iIntros (v2 t2 ->); rewrite /= to_of_val /=.
  iDestruct "Hposts" as "[% ?]"; done.
Qed.

Local Definition wp_invariance_relation Λ AS e1 σ1 t2 σ2 (φ : Prop)
           (ex : execution_trace Λ) (atr : @auxiliary_trace Λ AS) : Prop :=
  exec_starts_in ex ([e1], σ1) → exec_ends_in ex (t2, σ2) → φ.

Local Lemma wp_invariance_relation_invariance {Λ AS} e1 σ1 δ1 t2 σ2 φ :
  simulation
    (wp_invariance_relation Λ AS e1 σ1 t2 σ2 φ)
    (singleton_exec ([e1], σ1))
    (singleton_auxtr δ1) →
  ∀ ex,
    valid_exec ex →
    exec_starts_in ex ([e1], σ1) →
    exec_ends_in ex (t2, σ2) →
    φ.
Proof.
  intros Hsm ex Hex Hexstr Hexend.
  eapply simulation_simulates in Hsm as [atr Hatr]; eauto.
  rewrite -> simulation_unfold in Hatr.
  destruct Hatr as (Hvlt & Hψ & Hatr).
  apply Hψ; done.
Qed.

Corollary wp_invariance Λ AS Σ `{!invPreG Σ} s e1 σ1 δ1 t2 σ2 φ :
  valid_state_evolution_finitary AS →
  (∀ `{Hinv : !invG Σ},
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → aux_state AS → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ AS Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗ stateI σ1 δ1 [] 1 ∗ WP e1 @ s; ⊤ {{ _, True }} ∗
       (∀ δ2 κs, stateI σ2 δ2 κs (length t2) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  ∀ ex,
    valid_exec ex →
    exec_starts_in ex ([e1], σ1) →
    exec_ends_in ex (t2, σ2) →
    φ.
Proof.
  intros ? Hwp.
  apply (wp_invariance_relation_invariance _ _ δ1).
  apply (wp_strong_adequacy Λ AS Σ s); first done.
  iIntros (?) "".
  iMod Hwp as (stateI fork_post) "(config_wp & HSI & Hwp & Hφ)".
  iModIntro; iExists _, _, _; iFrame.
  iIntros (ex atr δ' c κs Hvlt Hexs Hatrs Hexe Hatre Hψ Hnst) "HSI Hposts".
  rewrite /wp_invariance_relation.
  iAssert ((∀ _ : exec_starts_in ex ([e1], σ1) ∧ exec_ends_in ex (t2, σ2),
                 |={⊤}=> ⌜φ⌝)%I) with "[HSI Hφ]" as "H".
  { iIntros ([? ?]).
    assert (c = (t2, σ2)) as -> by by eapply exec_ends_in_inj.
    iDestruct ("Hφ" with "HSI") as (E) "Hφ".
    iDestruct (fupd_plain_mask with "Hφ") as ">Hφ"; done. }
  rewrite -fupd_plain_forall'.
  iMod "H".
  iApply fupd_mask_weaken; first done.
  iIntros (Hexs' Hexe'); iApply "H"; done.
Qed.
