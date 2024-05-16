From iris.proofmode Require Import base proofmode classes.
From iris.base_logic.lib Require Export fancy_updates.
From trillium.program_logic Require Export language traces.
(* From trillium.bi Require Export weakestpre. *)
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness.
(* From trillium.fairness.heap_lang Require Import lang heap_lang_defs. *)
(* From iris.prelude Require Import options. *)
(* From iris.base_logic Require Export gen_heap. *)


Class EWp (Λ : language) (M: FairModel) (PROP A : Type) :=
  ewp : A → coPset -> fmrole M -> expr Λ → (val Λ → PROP) → PROP.
Arguments ewp {_ _ _ _ _} _ _ _ _%E _%I.
#[global] Instance: Params (@ewp) 9 := {}.


Section ewp_def.
  Context `{!irisG Λ AS Σ}. 
  Context `{PI: state Λ -> iProp Σ}. 
  Context {M: FairModel}
    {MSI: fmstate M -> iProp Σ}
    {step_restr: fmstate M -> fmstate M -> Prop}. 

Definition ewp_pre
  (* `{EM: ExecutionModel heap_lang M__G} `{hGS: @heapGS Σ _ EM} *)
  (* `{invGS_gen HasNoLc Σ} *)
  (s : stuckness)
    (ewp : coPset -d> fmrole M -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> fmrole M -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E ρ e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None =>
      (* ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS) K tp1 tp2 σ1, *)
      ∀ σ1 δ1,
      (* ⌜valid_exec extr⌝ -∗ *)
      (* ⌜locale_of tp1 (ectx_fill K e1) = ζ⌝ -∗ *)
      (* ⌜trace_ends_in extr (tp1 ++ ectx_fill K e1 :: tp2, σ1)⌝ -∗ *)
      (* state_interp extr atr *)
      PI σ1 -∗ ▷ MSI δ1
      ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs,
         ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅}▷=∗ |={∅,E}=>
         (* ∃ δ2 ℓ, *)
        ∃ δ2, 
           (* state_interp *)
           (*   (trace_extend extr (Some ζ) (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2)) *)
           (*   (trace_extend atr ℓ δ2) *)
           PI σ2 ∗ MSI δ2 ∗ ⌜ fmtrans _ δ1 (Some ρ) δ2 ⌝ ∗ ⌜ step_restr δ1 δ2 ⌝ ∗ 
           ewp E ρ e2 Φ ∗
           (* [∗ list] i ↦ ef ∈ efs, *)
           (*    wp ⊤ (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef) ef *)
           (*      (fork_post (locale_of (tp1 ++ ectx_fill K e1 :: tp2 ++ (take i efs)) ef)) *)
           ⌜ efs = [] ⌝
  end%I.

#[local] Instance ewp_pre_contractive s : Contractive (ewp_pre s).
Proof.
  rewrite /ewp_pre=> n wp wp' Hwp E e1 ζ Φ /=.
  do 27 (f_contractive || f_equiv).
  apply Hwp. 
Qed.

Definition ewp_def : EWp Λ M (iProp Σ) stuckness :=
  λ s : stuckness, fixpoint (ewp_pre s).

Definition ewp_aux : seal (@ewp_def). Proof. by eexists. Qed.
Definition ewp' := ewp_aux.(unseal).
Arguments ewp' {Λ AS Σ _}.
#[global] Existing Instance ewp'.
(* Lemma ewp_eq : @ewp Λ M (iProp Σ) stuckness _ = ewp_def. *)
(* Proof. rewrite -ewp_aux.(seal_eq) //. Qed. *)
Lemma ewp_eq : ewp = ewp_def.
Proof. rewrite -ewp_aux.(seal_eq) //. Qed.

End ewp_def.

Section wp.
Context `{!irisG Λ AS Σ}.
Context {PI: state Λ -> iProp Σ}. 
Context {M: FairModel}
    {MSI: fmstate M -> iProp Σ}
    {step_restr: fmstate M -> fmstate M -> Prop}.

Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.
Implicit Types ρ : fmrole M. 

Notation "'EWP' e @ s ; ρ ; E {{ Φ } }" := (ewp s E ρ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e @ s ; ρ ; E {{ v , Q } }" := (ewp s E ρ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  s ;  ρ ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.

Local Instance EWp_inst: EWp Λ M (iProp Σ) stuckness.
unshelve eapply ewp'.
3: apply step_restr. 2: apply MSI. 1: apply PI.
Defined. 

(* Weakest pre *)
Lemma ewp_unfold s E e ρ Φ :
  EWP e @ s; ρ; E {{ Φ }} ⊣⊢ ewp_pre s (ewp (PROP:=iProp Σ) s) E ρ e Φ (PI := PI) (MSI := MSI) (step_restr := step_restr).
Proof. rewrite ewp_eq. apply (fixpoint_unfold (ewp_pre s)). Qed.

#[global] Instance ewp_ne s E ζ e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (ewp (PROP:=iProp Σ) s E ζ e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !ewp_unfold /ewp_pre /=.
  do 27 (f_contractive || f_equiv).
  rewrite IH; [done|lia|]. intros v. eapply dist_lt; eauto.
Qed.
#[global] Instance ewp_proper s E ζ e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (ewp (PROP:=iProp Σ) s E ζ e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply ewp_ne=>v; apply equiv_dist.
Qed.
#[global] Instance ewp_contractive s E ζ e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (ewp (PROP:=iProp Σ) s E ζ e).
Proof.
  intros He Φ Ψ HΦ. rewrite !ewp_unfold /ewp_pre He /=.
  do 27 (f_contractive || f_equiv).
  done. 
Qed.

Lemma ewp_value' s E ζ Φ v : Φ v ⊢ EWP of_val v @ s; ζ; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite ewp_unfold /ewp_pre to_of_val. auto. Qed.
Lemma ewp_value_inv' s E ζ Φ v : EWP of_val v @ s; ζ; E {{ Φ }} ={E}=∗ Φ v.
Proof. by rewrite ewp_unfold /ewp_pre to_of_val. Qed.

Lemma ewp_strong_mono s1 s2 E1 E2 ζ e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  EWP e @ s1; ζ; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ EWP e @ s2; ζ; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e ζ E1 E2 HE Φ Ψ).
  rewrite !ewp_unfold /ewp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  (* iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hloc Hexe) "Hsi". *)
  iIntros (σ1 δ1) "PI MSI".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[$] [$]") as "[% H]".
  iModIntro. iSplit; [by iPureIntro; destruct s1, s2|].
  iIntros (e2 σ2 efs Hstep). simpl.
  iMod ("H" with "[//]") as "H". iIntros "!> !>".
  iMod "H" as "H". iIntros "!>".

  iMod "H". iMod "Hclose". iModIntro.
  iDestruct "H" as (?) "(?&?&?&?&H&?)". iExists _. iFrame.
  iApply ("IH" with "[] H"); auto.
Qed.

Lemma fupd_ewp s E ζ e Φ : (|={E}=> EWP e @ s; ζ; E {{ Φ }}) ⊢ EWP e @ s; ζ; E {{ Φ }}.
Proof.
  rewrite ewp_unfold /ewp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iMod "H". iApply "H"; done.
Qed.
Lemma ewp_fupd s E ζ e Φ : EWP e @ s; ζ; E {{ v, |={E}=> Φ v }} ⊢ EWP e @ s; ζ; E {{ Φ }}.
Proof. iIntros "H". iApply (ewp_strong_mono s s E with "H"); auto. Qed.

(* Class AllowsStuttering := { *)
(*   stuttering_label: mlabel AS; *)
(*   allows_stuttering : *)
(*     ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS) c δ oζ, *)
(*       valid_exec extr → *)
(*       trace_ends_in extr c → *)
(*       trace_ends_in atr δ → *)
(*       locale_step c oζ c → *)
(*       state_interp extr atr ==∗ *)
(*       state_interp (trace_extend extr oζ c) (trace_extend atr stuttering_label δ); *)
(*   }. *)

(* Class AllowsPureStep := { *)
(*   pure_label: mlabel AS; *)
(*   allows_pure_step : *)
(*     ∀ (extr : execution_trace Λ) (atr : auxiliary_trace AS)  tp tp' σ δ oζ, *)
(*       valid_exec extr → *)
(*       trace_ends_in extr (tp, σ) → *)
(*       trace_ends_in atr δ → *)
(*       locale_step (tp, σ) oζ (tp', σ) → *)
(*       state_interp extr atr ==∗ *)
(*       state_interp (trace_extend extr oζ (tp', σ)) (trace_extend atr pure_label δ); *)
(*   }. *)

(* #[global] Instance AllowsPureStep_AllowsStuttering : *)
(*   AllowsPureStep → AllowsStuttering. *)
(* Proof. *)
(*   intros Haps. refine ({| stuttering_label := pure_label |}). *)
(*   iIntros (extr atr [tp σ] δ oζ ? ? ? ?) "Hsi". *)
(*   iApply allows_pure_step; done. *)
(* Qed. *)

(* Lemma wp_stuttering_atomic s E1 E2 ζ e Φ *)
(*       `{!AllowsStuttering} *)
(*       `{!StutteringAtomic (stuckness_to_atomicity s) e} : *)
(*   (|={E1,E2}=> WP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}. *)
(* Proof. *)
(*   iIntros "H". *)
(*   iLöb as "IH". *)
(*   rewrite {2}(wp_unfold s E1 e) /wp_pre. *)
(*   rewrite !(wp_unfold s E2 e) /wp_pre. *)
(*   destruct (to_val e) as [v|] eqn:He. *)
(*   { by iDestruct "H" as ">>> $". } *)
(*   iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi". *)
(*   iAssert ((|={E1}=> ⌜match s with *)
(*                       | NotStuck => reducible e σ1 *)
(*                       | MaybeStuck => True *)
(*                       end⌝ ∗ *)
(*             state_interp extr atr ∗ _)%I) with "[H Hsi]" as *)
(*       ">(Hnstuck & Hsi & H)". *)
(*   { iApply fupd_plain_keep_l. *)
(*     iSplitR; last (iFrame "Hsi"; iExact "H"). *)
(*     iIntros "[Hsi H]". *)
(*     iApply fupd_plain_mask. *)
(*     iMod "H". *)
(*     iMod ("H" with "[//] [//] [//] Hsi") as "[? _]". *)
(*     iModIntro; done. } *)
(*   iPoseProof (fupd_mask_intro_subseteq E1 ∅ True%I with "[]") as "Hmsk"; *)
(*     [set_solver|done|]. *)
(*   iMod "Hmsk". *)
(*   iModIntro. *)
(*   iSplitL "Hnstuck"; first done. *)
(*   iIntros (e2 σ2 efs Hstep). *)
(*   destruct (stutteringatomic _ _ _ _ Hstep) as [(?&?&?)|Hs]; simplify_eq/=. *)
(*   - iModIntro; iNext. *)
(*     iMod (allows_stuttering with "Hsi") as "Hsi"; [done|done|done| |]. *)
(*     { econstructor 1; [done| |by apply fill_step]; by rewrite app_nil_r. } *)
(*     iIntros "!>". iApply step_fupdN_intro; [done|]. iIntros "!>". *)
(*     iMod "Hmsk" as "_"; iModIntro. *)
(*     rewrite app_nil_r. *)
(*     iExists (trace_last atr), stuttering_label; iFrame "Hsi". *)
(*     iSplitL; last done. *)
(*     iApply "IH"; done. *)
(*   - iClear "IH". *)
(*     iMod "Hmsk" as "_". *)
(*     iMod "H". iMod ("H" with "[//] [//] [//] Hsi") as "[_ H]". *)
(*     iMod ("H" with "[//]") as "H". iIntros "!>!>". *)
(*     iMod "H" as "H". iIntros "!>". *)
(*     iApply (step_fupdN_wand with "[H]"); first by iApply "H". *)
(*     iIntros "H". *)
(*     iMod "H" as (δ2 ℓ) "(Hσ & H & Hefs)". destruct s. *)
(*     + rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2. *)
(*       * iDestruct "H" as ">> H". *)
(*         iModIntro; iExists _, _. *)
(*         iFrame. *)
(*         rewrite !wp_unfold /wp_pre He2; done. *)
(*       * iMod ("H" with "[] [] [] [$]") as "[H _]". *)
(*         { iPureIntro. eapply extend_valid_exec; [done|done|]. *)
(*           econstructor; [done|done|]. *)
(*           apply fill_step; done. } *)
(*         { by erewrite <-locale_fill_step. } *)
(*         { done. } *)
(*         iDestruct "H" as %(? & ? & ? & ?%Hs); done. *)
(*     + destruct Hs as [v <-%of_to_val]. *)
(*       rewrite !wp_unfold /wp_pre to_of_val. *)
(*       iMod "H" as ">H"; iModIntro. *)
(*       iExists _, _. *)
(*       rewrite !wp_unfold /wp_pre to_of_val. *)
(*       eauto with iFrame. *)
(* Qed. *)

(* Lemma wp_stutteringatomic_take_step *)
(*       s E1 E2 ζ e Φ *)
(*       `{!AllowsStuttering} *)
(*       `{!StutteringAtomic (stuckness_to_atomicity s) e} : *)
(*   TCEq (to_val e) None → *)
(*   (|={E1,E2}=> *)
(*    ∀ extr atr c1 δ1 ζ', *)
(*      ⌜trace_ends_in extr c1⌝ -∗ *)
(*      ⌜trace_ends_in atr δ1⌝ -∗ *)
(*      ⌜ζ = ζ'⌝ -∗ *)
(*      state_interp extr atr ={E2}=∗ *)
(*      ∃ Q R, *)
(*        state_interp extr atr ∗ *)
(*        (∀ c2 δ2 ℓ, *)
(*            ∃ δ', *)
(*            state_interp *)
(*              (trace_extend extr (Some ζ') c2) *)
(*              (trace_extend atr ℓ δ2) ∗ Q ={E2}=∗ *)
(*            state_interp *)
(*              (trace_extend extr (Some ζ') c2) *)
(*              (trace_extend atr stuttering_label δ') ∗ R) ∗ *)
(*        (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗ *)
(*    WP e @ s; ζ; E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}. *)
(* Proof. *)
(*   iIntros (He) "H". *)
(*   iLöb as "IH". *)
(*   rewrite {2}wp_unfold /wp_pre He. *)
(*   iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi". *)
(*   iAssert ((|={E1}=> ⌜match s with *)
(*                       | NotStuck => reducible e σ1 *)
(*                       | MaybeStuck => True *)
(*                       end⌝ ∗ *)
(*             state_interp extr atr ∗ _)%I) with "[H Hsi]" as *)
(*       ">(Hnstuck & Hsi & H)". *)
(*   { iApply fupd_plain_keep_l. *)
(*     iSplitR; last (iFrame "Hsi"; iExact "H"). *)
(*     iIntros "[Hsi H]". *)
(*     iApply fupd_plain_mask. *)
(*     iMod "H". *)
(*     iMod ("H" with "[//] [//] [//] Hsi") as (Q R) "[Hsi (_&_&H)]". *)
(*     rewrite !wp_unfold /wp_pre He. *)
(*     iMod ("H" with "[] [] [] Hsi") as "[? _]"; done. } *)
(*   iMod (fupd_mask_intro_subseteq E1 ∅ True%I with "[]") as "Hmsk"; *)
(*     [set_solver|done|]. *)
(*   iModIntro. *)
(*   iSplit; first done. *)
(*   iIntros (e2 σ2 efs Hstep). *)
(*   pose proof Hstep as  [(?&?&?)|HSA]%stutteringatomic; simplify_eq/=. *)
(*   - iModIntro; iNext. *)
(*     iMod (allows_stuttering with "Hsi") as "Hsi"; [done|done|done| |]. *)
(*     { econstructor 1; [done| |by apply fill_step]; by rewrite app_nil_r. } *)
(*     iIntros "!>". iApply step_fupdN_intro; [done|]. iIntros "!>". *)
(*     iMod "Hmsk" as "_"; iModIntro. *)
(*     rewrite app_nil_r. *)
(*     iExists (trace_last atr), stuttering_label; iFrame "Hsi". *)
(*     iSplitL; last done. *)
(*     iApply "IH"; done. *)
(*   - iMod "Hmsk" as "_". *)
(*     iMod ("H" with "[//] [//] [//] Hsi") as ">H". *)
(*     iDestruct "H" as (Q R) "(Hsi & Hupdate & Htrans & H)". *)
(*     rewrite (wp_unfold s E2 e) /wp_pre He. *)
(*     iMod ("Htrans" with "Hsi") as "(Hsi & HQ)". *)
(*     iMod ("H" with "[//] [//] [//] Hsi") as "[_ H]". *)
(*     iMod ("H" with "[//]") as "H". iIntros "!>!>". *)
(*     iMod "H" as "H". iIntros "!>". *)
(*     iApply (step_fupdN_wand with "[H]"); first by iApply "H". *)
(*     iIntros "H". *)
(*     iMod "H" as (δ3 ℓ) "(Hsi & H & Hefs)". *)
(*     iDestruct ("Hupdate" $! (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2) δ3 ℓ) *)
(*       as (δ') "Hupdate". *)
(*     iMod ("Hupdate" with "[$HQ $Hsi]") as "(Hsi & HR)". *)
(*     destruct s. *)
(*     + rewrite (wp_unfold _ E2 e2); rewrite /wp_pre. *)
(*       destruct (to_val e2) as [v2|] eqn:He2. *)
(*       * iDestruct ("H" with "HR") as ">> H". *)
(*         iModIntro; iExists _, _; iFrame. *)
(*         rewrite -(of_to_val _ _ He2) -wp_value'; done. *)
(*       * iMod ("H" with "[] [] [] Hsi") as "[% _]"; try done. *)
(*         { iPureIntro. eapply extend_valid_exec; [done|done|]. *)
(*           econstructor; [done|done|]. *)
(*           apply fill_step; done. } *)
(*         { by erewrite locale_fill_step. } *)
(*         exfalso; simpl in *; eapply not_reducible; eauto. *)
(*     + simpl in *. *)
(*       destruct HSA as [v <-%of_to_val]. *)
(*       iMod (wp_value_inv' with "H HR") as ">H". *)
(*       iModIntro. iExists _, _. *)
(*       iFrame "Hsi Hefs". by iApply wp_value'. *)
(* Qed. *)

Lemma ewp_atomic s E1 E2 ρ e Φ
      `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> EWP e @ s; ρ; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ EWP e @ s; ρ; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite (ewp_unfold s E1 e) /ewp_pre.
  rewrite !(ewp_unfold s E2 e) /ewp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  (* iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale exe) "Hsi". *)
  iIntros (σ1 δ1) "PI MSI".
  iMod "H".
  iMod ("H" with "PI MSI") as "[% H]".
  iModIntro.
  iSplit; first by iPureIntro.
  iIntros (e2 σ2 efs Hstep).
  pose proof (atomic _ _ _ _ Hstep) as Hs; simplify_eq/=.
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "H". iIntros "!>".
  (* iApply (step_fupdN_wand with "[H]"); first by iApply "H". *)
  (* iIntros "H". *)
  iMod "H" as (δ2) "(PI & MSI & STEP & RESTR & H & Hefs)". destruct s.
  - rewrite !ewp_unfold /ewp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> H".
      iModIntro; iExists _.
      iFrame.
      rewrite !ewp_unfold /ewp_pre He2; done.
    + iMod ("H" with "[$] [$]") as "[H BAR]"; try done.
      (* { iPureIntro. eapply extend_valid_exec; [done|done|]. *)
      (*   econstructor; [done|done|]. *)
      (*   apply fill_step; done. } *)
      (* { by erewrite <-locale_fill_step. } *)
      iDestruct "H" as %(? & ? & ? & ?%Hs); done.
  - destruct Hs as [v <-%of_to_val].
    rewrite !ewp_unfold /ewp_pre to_of_val.
    iMod "H" as ">H"; iModIntro.
    iExists _.
    rewrite !ewp_unfold /ewp_pre to_of_val.
    eauto with iFrame.
Qed.

(* Lemma wp_atomic_take_step *)
(*       s E1 E2 ζ e Φ *)
(*       `{!Atomic (stuckness_to_atomicity s) e} : *)
(*   TCEq (to_val e) None → *)
(*   (|={E1,E2}=> *)
(*    ∀ extr atr c1 δ1 ζ', *)
(*      ⌜trace_ends_in extr c1⌝ -∗ *)
(*      ⌜trace_ends_in atr δ1⌝ -∗ *)
(*      ⌜ζ = ζ'⌝ -∗ *)
(*      state_interp extr atr ={E2}=∗ *)
(*      ∃ Q R, *)
(*        state_interp extr atr ∗ *)
(*        (∀ c2 δ2 ℓ, *)
(*            ∃ δ' ℓ', *)
(*            state_interp *)
(*              (trace_extend extr (Some ζ') c2) *)
(*              (trace_extend atr ℓ δ2) ∗ Q ={E2}=∗ *)
(*            state_interp *)
(*              (trace_extend extr (Some ζ') c2) *)
(*              (trace_extend atr ℓ' δ') ∗ R) ∗ *)
(*        (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗ *)
(*    WP e @ s; ζ; E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @ s; ζ; E1 {{ Φ }}. *)
(* Proof. *)
(*   iIntros (He) "H". *)
(*   rewrite wp_unfold /wp_pre He. *)
(*   iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi". *)
(*   iMod ("H" with "[//] [//] [//] Hsi") as ">H". *)
(*   iDestruct "H" as (Q R) "(Hsi & Hupdate & Htrans & H)". *)
(*   rewrite (wp_unfold s E2 e) /wp_pre He. *)
(*   iMod ("Htrans" with "Hsi") as "(Hsi & HQ)". *)
(*   iMod ("H" with "[//] [//] [//] Hsi") as "[% H]". *)
(*   iModIntro. *)
(*   iSplit; first by iPureIntro. *)
(*   iIntros (e2 σ2 efs Hstep). *)
(*   pose proof (atomic _ _ _ _ Hstep) as Hs; simplify_eq/=. *)
(*   iMod ("H" with "[//]") as "H". iIntros "!>!>". *)
(*   iMod "H" as "H". iIntros "!>". *)
(*   iApply (step_fupdN_wand with "[H]"); first by iApply "H". *)
(*   iIntros "H". *)
(*   iMod "H" as (δ3 ℓ) "(Hsi & H & Hefs)". *)
(*   iDestruct ("Hupdate" $! (tp1 ++ ectx_fill K e2 :: tp2 ++ efs, σ2) δ3 ℓ) *)
(*       as (δ' ℓ') "Hupdate". *)
(*   iMod ("Hupdate" with "[$HQ $Hsi]") as "(Hsi & HR)". *)
(*   destruct s. *)
(*   - rewrite (wp_unfold _ E2 e2); rewrite /wp_pre. *)
(*     destruct (to_val e2) as [v2|] eqn:He2. *)
(*     + iDestruct ("H" with "HR") as ">> H". *)
(*       iModIntro; iExists _,_; iFrame. *)
(*       rewrite -(of_to_val _ _ He2) -wp_value'; done. *)
(*     + iMod ("H" with "[] [] [] Hsi") as "[% _]"; try done. *)
(*       { iPureIntro. eapply extend_valid_exec; [done|done|]. *)
(*         econstructor; [done|done|]. *)
(*         apply fill_step; done. } *)
(*       { by erewrite <-locale_fill_step. } *)
(*       exfalso; simpl in *; eapply not_reducible; eauto. *)
(*   - simpl in *. *)
(*     destruct Hs as [v <-%of_to_val]. *)
(*     iMod (wp_value_inv' with "H HR") as ">H". *)
(*     iModIntro. iExists _, _. *)
(*     iFrame "Hsi Hefs". by iApply wp_value'. *)
(* Qed. *)

(** In this stronger version of [wp_step_fupdN], the masks in the *)
(*    step-taking fancy update are a bit weird and somewhat difficult to *)
(*    use in practice. Hence, we prove it for the sake of completeness, *)
(*    but [wp_step_fupdN] is just a little bit weaker, suffices in *)
(*    practice and is easier to use. *)

(*    See the statement of [wp_step_fupdN] below to understand the use of *)
(*    ordinary conjunction here. *)
(* TODO (Egor): this version is almost useless with EWP *)
Lemma ewp_step_fupdN_strong n s ζ E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (⌜n ≤ 1⌝) ∧
  ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
    EWP e @ s; ζ; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  EWP e @ s; ζ; E1 {{ Φ }}.
Proof.
  destruct n as [|n].
  { iIntros (_ ?) "/= [_ [HP Hwp]]".
    iApply (ewp_strong_mono with "Hwp"); [done..|].
    iIntros (v) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
  rewrite !ewp_unfold /ewp_pre /=. iIntros (-> ?) "H".
  (* iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hσ". *)
  iIntros (σ1 δ1) "PI MSI".
  (* destruct (decide (n ≤ trace_length extr)) as [Hn|Hn]; first last. *)
  (* { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. } *)
  iDestruct "H" as "[% [>HP Hwp]]".
  assert (n = 0) as -> by lia. 
  iMod ("Hwp" with "[$] [$]") as "[$ H]". iMod "HP".
  iIntros "!>" (e2 σ2 efs Hstep). iMod ("H" $! e2 σ2 efs with "[% //]") as "H".
  iIntros "!>!>". iMod "H". iMod "HP". iModIntro.

    iMod "H" as "H". iDestruct "H" as (δ2) "(PI & MSI & STEP & RESTR & H & Hefs)".
    iMod "HP". iModIntro. iExists _. iFrame. 
    iApply (ewp_strong_mono with "H"); [done|set_solver|].
    iIntros (v) "HΦ". iApply ("HΦ" with "HP").
Qed.

Lemma ewp_step_fupdN n s ζ E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (⌜n ≤ 1⌝) ∧
  ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
    EWP e @ s; ζ; E2 {{ v, P ={E1}=∗ Φ v }}) -∗
  EWP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (??) "H". iApply (ewp_step_fupdN_strong with "[H]"); [done|].
  iApply (bi.and_mono_r with "H"). apply bi.sep_mono_l. iIntros "HP".
  iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
  iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
  { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
  iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
  iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
  by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
Qed.
Lemma ewp_step_fupd s E1 E2 ζ e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ EWP e @ s; ζ; E2 {{ v, P ={E1}=∗ Φ v }} -∗ EWP e @ s; ζ; E1 {{ Φ }}.
Proof.
  iIntros (??) "HR H".
  iApply (ewp_step_fupdN_strong 1 _ _ E1 E2 with "[-]"); [done|..]. iSplit.
  - auto with lia.
  - iFrame "H". iMod "HR" as "$". auto.
Qed.

Lemma ewp_bind K s E ζ e Φ :
  EWP e @ s; ζ; E {{ v, EWP ectx_fill K (of_val v) @ s; ζ; E {{ Φ }} }} ⊢
  EWP ectx_fill K e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e ζ Φ). rewrite ewp_unfold /ewp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_ewp. }
  rewrite ewp_unfold /ewp_pre fill_not_val; last done.
  (* iIntros (extr atr K' tp1 tp2 σ1 Hexvalid Hlocale Hexe) "Hsi". *)
  iIntros (σ1 δ1) "PI MSI".
  (* iMod ("H" $! _ _ (ectx_comp K' K) with "[//] [] [] [$]") as "[% H]". *)
  iMod ("H" $! _ _ with "[$] [$]") as "[% H]".
  (* { rewrite ectx_comp_comp; done. } *)
  (* { rewrite ectx_comp_comp; done. } *)
  iModIntro; iSplit.
  { iPureIntro. destruct s; first apply reducible_fill; done. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv K e σ1 e2 σ2 efs) as (e2'&->&?);
    [done|done|].
  iMod ("H" with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "H". iIntros "!>".
  iMod "H" as (δ2) "(PI & MSI & STEP & RESTR & H & Hefs)".
  (* rewrite !ectx_comp_comp. *)
  iModIntro; iExists δ2.
  iFrame. by iApply "IH".
Qed.

(** * Derived rules *)
Lemma ewp_mono s E ζ e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → EWP e @ s; ζ; E {{ Φ }} ⊢ EWP e @ s; ζ; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (ewp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma ewp_stuck_mono s1 s2 E ζ e Φ :
  s1 ⊑ s2 → EWP e @ s1; ζ; E {{ Φ }} ⊢ EWP e @ s2; ζ; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (ewp_strong_mono with "H"); auto. Qed.
(* Lemma wp_stuck_weaken s E ζ e Φ : *)
(*   EWP e @ s; ζ; E {{ Φ }} ⊢ EWP e @ ζ; E ?{{ Φ }}. *)
(* Proof. apply wp_stuck_mono. by destruct s. Qed. *)
Lemma ewp_mask_mono s E1 E2 ζ e Φ : E1 ⊆ E2 → EWP e @ s; ζ; E1 {{ Φ }} ⊢ EWP e @ s; ζ; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (ewp_strong_mono with "H"); auto. Qed.
#[global] Instance ewp_mono' s E ζ e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (ewp (PROP:=iProp Σ) s E ζ e).
Proof. by intros Φ Φ' ?; apply ewp_mono. Qed.
#[global] Instance ewp_flip_mono' s E ζ e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (ewp (PROP:=iProp Σ) s E ζ e).
Proof. by intros Φ Φ' ?; apply ewp_mono. Qed.

Lemma ewp_value s E Φ  ζ e v : IntoVal e v → Φ v ⊢ EWP e @ s; ζ; E {{ Φ }}.
Proof. intros <-. by apply ewp_value'. Qed.
Lemma ewp_value_fupd' s E ζ Φ v : (|={E}=> Φ v) ⊢ EWP of_val v @ s; ζ; E {{ Φ }}.
Proof. intros. by rewrite -ewp_fupd -ewp_value'. Qed.
Lemma ewp_value_fupd s E Φ ζ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ EWP e @ s; ζ;  E {{ Φ }}.
Proof. intros. rewrite -ewp_fupd -ewp_value //. Qed.
Lemma ewp_value_inv s E Φ ζ e v : IntoVal e v → EWP e @ s; ζ; E {{ Φ }} ={E}=∗ Φ v.
Proof. intros <-. by apply ewp_value_inv'. Qed.

Lemma ewp_frame_l s E ζ e Φ R : R ∗ EWP e @ s; ζ; E {{ Φ }} ⊢ EWP e @ s; ζ; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (ewp_strong_mono with "H"); auto with iFrame. Qed.
Lemma ewp_frame_r s E ζ e Φ R : EWP e @ s; ζ; E {{ Φ }} ∗ R ⊢ EWP e @ s; ζ; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (ewp_strong_mono with "H"); auto with iFrame. Qed.

Lemma ewp_frame_step_l s E1 E2 ζ e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ EWP e @ s; ζ; E2 {{ Φ }} ⊢ EWP e @ s; ζ; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (ewp_step_fupd with "Hu"); try done.
  iApply (ewp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma ewp_frame_step_r s E1 E2 ζ e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  EWP e @ s; ζ; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ EWP e @ s; ζ; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(EWP _ @ _; _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply ewp_frame_step_l.
Qed.
Lemma ewp_frame_step_l' s E ζ e Φ R :
  TCEq (to_val e) None → ▷ R ∗ EWP e @ s; ζ; E {{ Φ }} ⊢ EWP e @ s; ζ; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (ewp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma ewp_frame_step_r' s E ζ e Φ R :
  TCEq (to_val e) None → EWP e @ s; ζ; E {{ Φ }} ∗ ▷ R ⊢ EWP e @ s; ζ; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (ewp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma ewp_wand s E ζ e Φ Ψ :
  EWP e @ s; ζ; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ EWP e @ s; ζ; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (ewp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma ewp_wand_l s E ζ e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ EWP e @ s; ζ; E {{ Φ }} ⊢ EWP e @ s; ζ; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (ewp_wand with "Hwp H"). Qed.
Lemma ewp_wand_r s E ζ e Φ Ψ :
  EWP e @ s; ζ; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ EWP e @ s; ζ; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (ewp_wand with "Hwp H"). Qed.
Lemma ewp_frame_wand_l s E ζ e Q Φ :
  Q ∗ EWP e @ s; ζ; E {{ v, Q -∗ Φ v }} -∗ EWP e @ s; ζ; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (ewp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

(* Lemma ewp_notstuck_post_dis_dichotomy E ρ e Φ σ δ: *)
(*   (∀ v δ, Φ v -∗ MSI δ -∗ ⌜ ¬ role_enabled_model ρ δ ⌝) -∗ *)
(*   EWP e @ NotStuck; ρ; E {{ Φ }} -∗ *)
(*   PI σ -∗ *)
(*   MSI δ -∗ *)
(*   |={E}=> ⌜ is_Some (to_val e) /\ ¬ role_enabled_model ρ δ \/ to_val e = None /\ role_enabled_model ρ δ ⌝. *)
(* Proof. *)
(*   iIntros "DIS EWP PI MSI". *)
(*   rewrite ewp_unfold /ewp_pre. *)
(*   destruct (to_val e). *)
(*   { iMod "EWP". iModIntro. iLeft. iSplit; try done.     *)
(*     iApply ("DIS" with "[$] [$]"). } *)
(*   destruct (decide (role_enabled_model ρ δ)). *)
(*   { iPureIntro. tauto. } *)
(*   iSpecialize ("EWP" with "PI MSI"). *)
(*   iMod "EWP" as "[%RED STEP]". *)
(*   destruct RED as (?&?&?&?). *)
(*   iSpecialize ("STEP" with "[//]").  *)
  

End wp.

(* #[global] Arguments AllowsStuttering {_} _ _ {_}. *)
(* #[global] Arguments AllowsPureStep {_} _ _ {_}. *)

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisG Λ AS Σ}.
  Context {PI: state Λ -> iProp Σ}. 
  Context {M: FairModel}
    {MSI: fmstate M -> iProp Σ}
    {step_restr: fmstate M -> fmstate M -> Prop}.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

Notation "'EWP' e @ s ; ρ ; E {{ Φ } }" := (ewp s E ρ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e @ s ; ρ ; E {{ v , Q } }" := (ewp s E ρ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  s ;  ρ ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.

(* Local Instance EWp_inst: EWp Λ M (iProp Σ) stuckness. *)
(* unshelve eapply ewp'. *)
(* 3: apply step_restr. 2: apply MSI. 1: apply PI. *)
(*   Defined.  *)
(* #[global] Existing Instance EWp_inst. *)

  (* TODO: figure out the proper way *)
  Let ewp'_instance_helper := ewp' (PI := PI) (MSI := MSI) (step_restr := step_restr).  
  Existing Instance ewp'_instance_helper. 

  #[global] Instance frame_ewp p s E ζ e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (EWP e @ s; ζ; E {{ Φ }}) (EWP e @ s; ζ; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite ewp_frame_l. apply ewp_mono, HR. Qed.

  #[global] Instance is_except_0_ewp s E ζ e Φ : IsExcept0 (EWP e @ s; ζ; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ewp -except_0_fupd -fupd_intro. Qed.

  #[global] Instance elim_modal_bupd_ewp p s E ζ e P Φ :
    ElimModal True p false (|==> P) P (EWP e @ s; ζ; E {{ Φ }}) (EWP e @ s; ζ; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_ewp.
  Qed.

  #[global] Instance elim_modal_fupd_ewp p s E ζ e P Φ :
    ElimModal True p false (|={E}=> P) P (EWP e @ s; ζ; E {{ Φ }}) (EWP e @ s; ζ; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_ewp.
  Qed.

  (* #[global] Instance elim_modal_fupd_ewp_stutteringatomic p s E1 E2 ζ e P Φ : *)
  (*   AllowsStuttering AS Σ → *)
  (*   StutteringAtomic (stuckness_to_atomicity s) e → *)
  (*   ElimModal True p false (|={E1,E2}=> P) P *)
  (*           (EWP e @ s; ζ; E1 {{ Φ }}) (EWP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }})%I. *)
  (* Proof. *)
  (*   intros. by rewrite /ElimModal bi.intuitionistically_if_elim *)
  (*     fupd_frame_r bi.wand_elim_r wp_stuttering_atomic. *)
  (* Qed. *)

  #[global] Instance add_modal_fupd_ewp s E ζ e P Φ :
    AddModal (|={E}=> P) P (EWP e @ s; ζ; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_ewp. Qed.

  (* #[global] Instance elim_acc_wp_stuttering {X} E1 E2 ζ α β γ e s Φ : *)
  (*   AllowsStuttering AS Σ → *)
  (*   StutteringAtomic (stuckness_to_atomicity s) e → *)
  (*   ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1) *)
  (*           α β γ (EWP e @ s; ζ; E1 {{ Φ }}) *)
  (*           (λ x, EWP e @ s; ζ; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I. *)
  (* Proof. *)
  (*   intros ? ? _. *)
  (*   iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]". *)
  (*   iApply (wp_wand with "(Hinner Hα)"). *)
  (*   iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose". *)
  (* Qed. *)

  #[global] Instance elim_modal_fupd_ewp_atomic p s E1 E2 ζ e P Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (EWP e @ s; ζ; E1 {{ Φ }}) (EWP e @ s; ζ; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r ewp_atomic.
  Qed.

  #[global] Instance elim_acc_ewp_atomic {X} E1 E2 ζ α β γ e s Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (EWP e @ s; ζ; E1 {{ Φ }})
            (λ x, EWP e @ s; ζ; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (ewp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  #[global] Instance elim_acc_ewp_nonatomic {X} E ζ α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (EWP e @ s; ζ; E {{ Φ }})
            (λ x, EWP e @ s; ζ; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply ewp_fupd.
    iApply (ewp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.


Section ewp_to_wp.
  Context `{!irisG Λ M__G Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types ζ : locale Λ.

  Context {PI: state Λ -> iProp Σ}. 
  Context {M: FairModel}
    {MSI: fmstate M -> iProp Σ}
    {step_restr: fmstate M -> fmstate M -> Prop}.

  Notation "'EWP' e @ s ; ρ ; E {{ Φ } }" := (ewp s E ρ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e @ s ; ρ ; E {{ v , Q } }" := (ewp s E ρ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  s ;  ρ ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.

  (* (* TODO: figure out the proper way *) *)
  (* TODO: figure out the proper way *)
  Let ewp'_instance_helper := ewp' (PI := PI) (MSI := MSI) (step_restr := step_restr).  
  Existing Instance ewp'_instance_helper. 


  (* (* TODO: does that exist somewhere? *) *)
  Definition update_locale (tp: list (expr Λ)) (τ: locale Λ) (e: expr Λ): list (expr Λ).
  Proof using.
  Admitted.

  Lemma update_locale_replace tp1 e τ tp2 e'
    (Hloc : locale_of tp1 e = τ):
    update_locale (tp1 ++ e :: tp2) τ e' = tp1 ++ e' :: tp2.
  Proof using. Admitted. 

  Lemma update_locale_dom `{EqDecision (locale Λ)} tp τ e'
    (IN: is_Some (from_locale tp τ)):
    forall τ', is_Some (from_locale tp τ') <-> is_Some (from_locale (update_locale tp τ e') τ').
  Proof. Admitted. 

  Definition restores_TI `{EqDecision (locale Λ)} τ ρ: iProp Σ :=
    (∀ e (extr: execution_trace Λ) mtr K,
        let (tp, σ) := trace_last extr in
        (* let δ := trace_last mtr in *)        
        ⌜ from_locale tp τ = Some (ectx_fill K e) ⌝ -∗
        state_interp extr mtr -∗
        ∃ δ, PI σ ∗ MSI δ ∗ 
        (∀ σ' δ' e', ⌜ prim_step e σ e' σ' [] ⌝ -∗ ⌜ fmtrans _ δ (Some ρ) δ' ⌝ -∗ ⌜ step_restr δ δ' ⌝ -∗ PI σ' -∗ MSI δ' -∗
         ∃ st__G' l__G,
         let tp' := update_locale tp τ (ectx_fill K e') in
         state_interp (trace_extend extr (Some τ) (tp', σ')) (trace_extend mtr l__G st__G'))). 

  Lemma ewp_to_wp `{EqDecision (locale Λ)} `{EqDecision (expr Λ)} s E ρ e Φ τ:
    □ restores_TI τ ρ ⊢ EWP e @ s; ρ; E {{ Φ }} -∗ WP e @ s; τ; E {{ Φ }}.
  Proof.
    iIntros "#RESTORE EWP". 
    iLöb as "IH" forall (e Φ).
    rewrite !wp_unfold /wp_pre.
    destruct (to_val e) as [v|] eqn:?.
    { rewrite !ewp_unfold /ewp_pre. rewrite Heqo. done. }
    iIntros (extr atr K tp1 tp2 σ1 Hexvalid Hloc Hexe) "Hsi".
    rewrite !ewp_unfold /ewp_pre. rewrite Heqo.
    
    (* iPoseProof ("RESTORE" $! _ _ _ _ with "[$]") as "foo".  *)
    iPoseProof ("RESTORE" $! e extr atr K) as "-#restore".
    pose proof (last_eq_trace_ends_in _ _ Hexe) as LASTe. rewrite LASTe.
    iSpecialize ("restore" with "[] [$]").
    { iPureIntro.
      erewrite <- from_locale_from_Some.
      { f_equal. done. }
      list_simplifier.
      eapply prefixes_from_spec. set_solver. }    
    iDestruct "restore" as (δ) "(PI & MSI & restore)".
    iSpecialize ("EWP" with "[$] [$]").
    iMod "EWP" as "[% EWP]".
    iModIntro. iSplitL ""; [done| ].
    iIntros (e' σ2 efs) "%STEP".

    (* TODO: a quicker way? *)
    iSpecialize ("EWP" with "[//]").
    rewrite -Nat.add_1_l. rewrite step_fupdN_add. iMod "EWP". iModIntro.
    iNext. iMod "EWP". iModIntro.
    iApply step_fupdN_intro; [done| ]. iNext.

    iMod "EWP" as (δ2) "(PI & MSI & %MSTEP & %RESTR & H & %)". subst efs. iModIntro.
    iSpecialize ("restore" with "[//] [//] [//] [$] [$]").
    rewrite big_opL_nil. 
    iDestruct "restore" as (st__G l__G) "TI".
    iExists _, _. iSplitL "TI".
    - rewrite app_nil_r. iFrame. by rewrite update_locale_replace.
    - iSplitR ""; [| done]. by iApply "IH".
  Qed. 

End ewp_to_wp. 


