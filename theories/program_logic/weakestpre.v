From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Export fancy_updates.
From aneris.program_logic Require Export language traces.
(* FIXME: If we import iris.bi.weakestpre earlier texan triples do not
   get pretty-printed correctly. *)
From aneris.bi Require Export weakestpre.

Class irisG (Λ : language) (AS : AuxState Λ) (Σ : gFunctors) := IrisG {
  iris_invG :> invG Σ;

  (** The state interpretation is an invariant that should hold in between each
  step of reduction. Here [Λstate] is the global state, [list Λobservation] are
  the remaining observations, and [nat] is the number of forked-off threads
  (not the total number of threads, which is one higher because there is always
  a main thread). *)
  state_interp : execution_trace Λ → auxiliary_trace AS → iProp Σ;

  (** A fixed postcondition for any forked-off thread. For most languages, e.g.
  heap_lang, this will simply be [True]. However, it is useful if one wants to
  keep track of resources precisely, as in e.g. Iron. *)
  fork_post : val Λ → iProp Σ;

}.
Global Opaque iris_invG.

Definition wp_pre `{!irisG Λ AS Σ} (s : stuckness)
    (wp : coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ) :
    coPset -d> expr Λ -d> (val Λ -d> iPropO Σ) -d> iPropO Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ extr atr tp σ1 δ1,
      ⌜trace_ends_in extr (tp, σ1)⌝ -∗
      ⌜trace_ends_in atr δ1⌝ -∗
      state_interp extr atr ={E,∅}=∗
       ⌜if s is NotStuck then reducible e1 σ1 else True⌝ ∗
       ∀ e2 σ2 efs K `{!LanguageCtx K} tp1 tp2,
         ⌜tp = tp1 ++ K e1 :: tp2⌝ -∗
         ⌜prim_step e1 σ1 e2 σ2 efs⌝ ={∅}=∗ ▷ |={∅,E}=>
         ∃ δ2, ⌜valid_state_evolution extr atr (tp1 ++ K e2 :: tp2, σ2) δ2⌝ ∗
           state_interp
             (trace_extend extr (tp1 ++ K e2 :: tp2, σ2))
             (trace_extend atr δ2) ∗
           wp E e2 Φ ∗
           [∗ list] i ↦ ef ∈ efs, wp ⊤ ef fork_post
  end%I.

Local Instance wp_pre_contractive `{!irisG Λ AS Σ} s : Contractive (wp_pre s).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 Φ /=.
  destruct to_val; first done.
  repeat apply bi.forall_ne =>?.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{!irisG Λ AS Σ} : Wp Λ (iProp Σ) stuckness :=
  λ s : stuckness, fixpoint (wp_pre s).
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := wp_aux.(unseal).
Arguments wp' {Λ AS Σ _}.
Existing Instance wp'.
Lemma wp_eq `{!irisG Λ AS Σ} : wp = @wp_def Λ AS Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section wp.
Context `{!irisG Λ AS Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : expr Λ.

(* Weakest pre *)
Lemma wp_unfold s E e Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ wp_pre s (wp (PROP:=iProp Σ) s) E e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp_ne s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  destruct to_val; first by f_equiv; apply HΦ.
  repeat apply bi.forall_ne =>?.
  repeat ((f_contractive || f_equiv); try apply IH); eauto.
  eapply dist_le; eauto with lia.
Qed.
Global Instance wp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp (PROP:=iProp Σ) s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.
Global Instance wp_contractive s E e n :
  TCEq (to_val e) None →
  Proper (pointwise_relation _ (dist_later n) ==> dist n) (wp (PROP:=iProp Σ) s E e).
Proof.
  intros He Φ Ψ HΦ. rewrite !wp_unfold /wp_pre He.
  repeat apply bi.forall_ne =>?.
  by repeat (f_contractive || f_equiv).
Qed.

Lemma wp_value' s E Φ v : Φ v ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre to_of_val. auto. Qed.
Lemma wp_value_inv' s E Φ v : WP of_val v @ s; E {{ Φ }} ={E}=∗ Φ v.
Proof. by rewrite wp_unfold /wp_pre to_of_val. Qed.

Lemma wp_strong_mono s1 s2 E1 E2 e Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (extr atr tp σ1 δ1 Hexe Hatre) "Hsi".
  iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
  iMod ("H" with "[//] [//] [$]") as "[% H]".
  iModIntro. iSplit; [by iPureIntro; destruct s1, s2|].
  iIntros (e2 σ2 efs K ? tp1 tp2 -> Hstep).
  iMod ("H" with "[//] [//] [//]") as "H". iIntros "!> !>".
  iMod "H" as (δ2) "(Hsv & Hσ & H & Hefs)".
  iMod "Hclose" as "_". iModIntro.
  iExists δ2. iSplit; first done.
  iFrame "Hσ". iSplitR "Hefs".
  - iApply ("IH" with "[//] H HΦ").
  - iApply (big_sepL_impl with "Hefs"); iIntros "!>" (k ef _).
    iIntros "H". iApply ("IH" with "[] H"); auto.
Qed.

Lemma fupd_wp s E e Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (extr atr tp σ1 δ1 Hexe Hatre) "Hsi". iMod "H".
  iApply ("H" with "[] [] Hsi"); done.
Qed.
Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

Class AllowsStuttering :=
  allows_stuttering :
    ∀ extr atr c δ,
      trace_ends_in extr c →
      trace_ends_in atr δ →
      state_interp extr atr ==∗
      state_interp (trace_extend extr c) (trace_extend atr δ).

Lemma wp_stuttering_atomic s E1 E2 e Φ
      `{!AllowsStuttering}
      `{!StutteringAtomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H".
  iLöb as "IH".
  rewrite {2}(wp_unfold s E1 e) /wp_pre.
  rewrite !(wp_unfold s E2 e) /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (extr atr tp σ1 δ1 Hexe Hatre) "Hsi".
  iAssert ((|={E1}=> ⌜match s with
                      | NotStuck => reducible e σ1
                      | MaybeStuck => True
                      end⌝ ∗
            state_interp extr atr ∗ _)%I) with "[H Hsi]" as
      ">(Hnstuck & Hsi & H)".
  { iApply fupd_plain_keep_l.
    iSplitR; last (iFrame "Hsi"; iExact "H").
    iIntros "[Hsi H]".
    iApply fupd_plain_mask.
    iMod "H".
    iMod ("H" with "[//] [//] Hsi") as "[? _]".
    iModIntro; done. }
  iPoseProof (fupd_mask_intro_subseteq E1 ∅ True%I with "[]") as "Hmsk";
    [set_solver|done|].
  iMod "Hmsk".
  iModIntro.
  iSplitL "Hnstuck"; first done.
  iIntros (e2 σ2 efs  K ? tp1 tp2 ->Hstep).
  destruct (stutteringatomic _ _ _ _ Hstep) as [(?&?&?)|Hs]; simplify_eq/=.
  - iModIntro; iNext.
    iMod (allows_stuttering with "Hsi") as "Hsi"; [done|done|].
    iMod "Hmsk" as "_"; iModIntro.
    iExists δ1; iFrame "Hsi".
    iSplitR; first by iPureIntro; apply pure_step_evolution_valid.
    iSplitL; last done.
    iApply "IH"; done.
  - iClear "IH".
    iMod "Hmsk" as "_".
    iMod "H". iMod ("H" with "[//] [//] Hsi") as "[_ H]".
    iMod ("H" with "[//] [//] [//]") as "H". iIntros "!>!>".
    iMod "H" as (δ2) "(% & Hσ & H & Hefs)". destruct s.
    + rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      * iDestruct "H" as ">> H".
        iModIntro; iExists _; iSplitR; first done.
        iFrame.
        rewrite !wp_unfold /wp_pre He2; done.
      * iMod ("H" with "[] [] [$]") as "[H _]"; [done|done|].
        iDestruct "H" as %(? & ? & ? & ?%Hs); done.
    + destruct Hs as [v <-%of_to_val].
      rewrite !wp_unfold /wp_pre to_of_val.
      iMod "H" as ">H"; iModIntro.
      iExists _; iSplitR; first done.
      rewrite !wp_unfold /wp_pre to_of_val.
      eauto with iFrame.
Qed.

Lemma wp_stutteringatomic_take_step
      s E1 E2 e Φ
      `{!AllowsStuttering}
      `{!StutteringAtomic (stuckness_to_atomicity s) e} :
  TCEq (to_val e) None →
  (|={E1,E2}=>
   ∀ extr atr c1 δ1,
     ⌜trace_ends_in extr c1⌝ -∗
     ⌜trace_ends_in atr δ1⌝ -∗
     state_interp extr atr ={E2}=∗
     ∃ δ' Q R,
       state_interp extr atr ∗
       (∀ c2 δ2,
           state_interp
             (trace_extend extr c2)
             (trace_extend atr δ2) ∗
           ⌜valid_state_evolution extr atr c2 δ2⌝ ∗ Q ={E2}=∗
             ⌜valid_state_evolution extr atr c2 δ'⌝ ∗
             state_interp
               (trace_extend extr c2)
               (trace_extend atr δ') ∗ R) ∗
       (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗
   WP e @ s; E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He) "H".
  iLöb as "IH".
  rewrite {2}wp_unfold /wp_pre He.
  iIntros (extr atr tp σ1 δ1 Hexe Hatre) "Hsi".
  iAssert ((|={E1}=> ⌜match s with
                      | NotStuck => reducible e σ1
                      | MaybeStuck => True
                      end⌝ ∗
            state_interp extr atr ∗ _)%I) with "[H Hsi]" as
      ">(Hnstuck & Hsi & H)".
  { iApply fupd_plain_keep_l.
    iSplitR; last (iFrame "Hsi"; iExact "H").
    iIntros "[Hsi H]".
    iApply fupd_plain_mask.
    iMod "H".
    iMod ("H" with "[//] [//] Hsi") as (δ' Q R) "[Hsi (_&_&H)]".
    rewrite !wp_unfold /wp_pre He.
    iMod ("H" with "[] [] Hsi") as "[? _]"; done. }
  iMod (fupd_mask_intro_subseteq E1 ∅ True%I with "[]") as "Hmsk";
    [set_solver|done|].
  iModIntro.
  iSplit; first done.
  iIntros (e2 σ2 efs K ? tp1 tp2 -> Hstep).
  pose proof Hstep as  [(?&?&?)|HSA]%stutteringatomic; simplify_eq/=.
  - iModIntro; iNext.
    iMod (allows_stuttering with "Hsi") as "Hsi"; [done|done|].
    iMod "Hmsk" as "_"; iModIntro.
    iExists δ1; iFrame "Hsi".
    iSplitR; first by iPureIntro; apply pure_step_evolution_valid.
    iSplitL; last done.
    iApply "IH"; done.
  - iMod "Hmsk" as "_".
    iMod ("H" with "[//] [//] Hsi") as ">H".
    iDestruct "H" as (δ' Q R) "(Hsi & Hupdate & Htrans & H)".
    rewrite (wp_unfold s E2 e) /wp_pre He.
    iMod ("Htrans" with "Hsi") as "(Hsi & HQ)".
    iMod ("H" with "[//] [//] Hsi") as "[_ H]".
    iMod ("H" with "[//] [//] [//]") as "H". iIntros "!>!>".
    iMod "H" as (δ3) "(Hδ3 & Hsi & H & Hefs)".
    iMod ("Hupdate" with "[$HQ $Hsi $Hδ3]") as "(Hδ2 & Hsi & HR)".
    destruct s.
    + rewrite (wp_unfold _ E2 e2); rewrite /wp_pre.
      destruct (to_val e2) as [v2|] eqn:He2.
      * iDestruct ("H" with "HR") as ">> H".
        iModIntro; iExists _; iFrame.
        rewrite -(of_to_val _ _ He2) -wp_value'; done.
      * iMod ("H" with "[] [] Hsi") as "[% _]"; [done|done|].
        exfalso; simpl in *; eapply not_reducible; eauto.
    + simpl in *.
      destruct HSA as [v <-%of_to_val].
      iMod (wp_value_inv' with "H HR") as ">H".
      iModIntro. iExists _; iSplit; first done.
      iFrame "Hsi Hefs". by iApply wp_value'.
Qed.

Lemma wp_atomic s E1 E2 e Φ
      `{!Atomic (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H".
  rewrite (wp_unfold s E1 e) /wp_pre.
  rewrite !(wp_unfold s E2 e) /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (extr atr tp σ1 δ1 exe Hatre) "Hsi".
  iMod "H".
  iMod ("H" with "[//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by iPureIntro.
  iIntros (e2 σ2 efs K ? tp1 tp2 -> Hstep).
  pose proof (atomic _ _ _ _ Hstep) as Hs; simplify_eq/=.
  iMod ("H" with "[//] [//] [//]") as "H". iIntros "!>!>".
  iMod "H" as (δ2) "(% & Hσ & H & Hefs)". destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> H".
      iModIntro; iExists _; iSplitR; first done.
      iFrame.
      rewrite !wp_unfold /wp_pre He2; done.
    + iMod ("H" with "[] [] [$]") as "[H _]"; [done|done|].
      iDestruct "H" as %(? & ? & ? & ?%Hs); done.
  - destruct Hs as [v <-%of_to_val].
    rewrite !wp_unfold /wp_pre to_of_val.
    iMod "H" as ">H"; iModIntro.
    iExists _; iSplitR; first done.
    rewrite !wp_unfold /wp_pre to_of_val.
    eauto with iFrame.
Qed.

Lemma wp_atomic_take_step
      s E1 E2 e Φ
      `{!Atomic (stuckness_to_atomicity s) e} :
  TCEq (to_val e) None →
  (|={E1,E2}=>
   ∀ extr atr c1 δ1,
     ⌜trace_ends_in extr c1⌝ -∗
     ⌜trace_ends_in atr δ1⌝ -∗
     state_interp extr atr ={E2}=∗
     ∃ δ' Q R,
       state_interp extr atr ∗
       (∀ c2 δ2,
           state_interp
             (trace_extend extr c2)
             (trace_extend atr δ2) ∗
           ⌜valid_state_evolution extr atr c2 δ2⌝ ∗ Q ={E2}=∗
             ⌜valid_state_evolution extr atr c2 δ'⌝ ∗
             state_interp
               (trace_extend extr c2)
               (trace_extend atr δ') ∗ R) ∗
       (state_interp extr atr ={E2}=∗ state_interp extr atr ∗ Q) ∗
   WP e @ s; E2 {{ v, R ={E2,E1}=∗ Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros (He) "H".
  rewrite wp_unfold /wp_pre He.
  iIntros (extr atr tp σ1 δ1 Hexe Hatre) "Hsi".
  iMod ("H" with "[//] [//] Hsi") as ">H".
  iDestruct "H" as (δ' Q R) "(Hsi & Hupdate & Htrans & H)".
  rewrite (wp_unfold s E2 e) /wp_pre He.
  iMod ("Htrans" with "Hsi") as "(Hsi & HQ)".
  iMod ("H" with "[//] [//] Hsi") as "[% H]".
  iModIntro.
  iSplit; first by iPureIntro.
  iIntros (e2 σ2 efs K ? tp1 tp2 -> Hstep).
  pose proof (atomic _ _ _ _ Hstep) as Hs; simplify_eq/=.
  iMod ("H" with "[//] [//] [//]") as "H". iIntros "!>!>".
  iMod "H" as (δ3) "(Hδ3 & Hsi & H & Hefs)".
  iMod ("Hupdate" with "[$HQ $Hsi $Hδ3]") as "(Hδ2 & Hsi & HR)".
  destruct s.
  - rewrite (wp_unfold _ E2 e2); rewrite /wp_pre.
    destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct ("H" with "HR") as ">> H".
      iModIntro; iExists _; iFrame.
      rewrite -(of_to_val _ _ He2) -wp_value'; done.
    + iMod ("H" with "[] [] Hsi") as "[% _]"; [done|done|].
      exfalso; simpl in *; eapply not_reducible; eauto.
  - simpl in *.
    destruct Hs as [v <-%of_to_val].
    iMod (wp_value_inv' with "H HR") as ">H".
    iModIntro. iExists _; iSplit; first done.
    iFrame "Hsi Hefs". by iApply wp_value'.
Qed.

Lemma wp_step_fupd s E1 E2 e P Φ :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (extr atr tp σ1 δ1 Hexe Hatre) "Hsi".
  iMod "HR". iMod ("H" with "[//] [//] [$]") as "[$ H]".
  iIntros "!>" (e2 σ2 efs K ? tp1 tp2 -> Hstep).
  iMod ("H" $! e2 σ2 efs with "[//] [//] [% //]") as "H".
  iIntros "!>!>". iMod "H" as (δ2) "(Hsv & Hσ & H & Hefs)".
  iMod "HR". iModIntro; iExists δ2; iSplit; first done. iFrame "Hσ Hefs".
  iApply (wp_strong_mono s s E2 with "H"); [done..|].
  iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_bind K `{!LanguageCtx K} s E e Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val; last done.
  iIntros (extr atr tp σ1 δ1 Hexe Hatre) "Hsi".
  iMod ("H" with "[//] [//] [$]") as "[% H]".
  iModIntro; iSplit.
  { iPureIntro. destruct s; first apply reducible_fill; done. }
  iIntros (e2 σ2 efs K' ? tp1 tp2 -> Hstep).
  destruct (fill_step_inv (K := K) e σ1 e2 σ2 efs) as (e2'&->&?); [done|done|].
  iMod ("H" $! e2' σ2 efs (λ e, K' (K e)) with "[] [//] [//]") as "H".
  { iPureIntro; apply _. }
  iIntros "!>!>".
  iMod "H" as (δ2) "(Hsv & Hσ & H & Hefs)".
  iModIntro; iExists δ2; iSplit; first done.
  iFrame "Hσ Hefs". by iApply "IH".
Qed.

(** * Derived rules *)
Lemma wp_mono s E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E e Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E e Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 e Φ : E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
Global Instance wp_flip_mono' s E e :
  Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. by apply wp_value'. Qed.
Lemma wp_value_fupd' s E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd s E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.
Lemma wp_value_inv s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ={E}=∗ Φ v.
Proof. intros <-. by apply wp_value_inv'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  TCEq (to_val e) None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  TCEq (to_val e) None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  TCEq (to_val e) None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_frame_wand_l s E e Q Φ :
  Q ∗ WP e @ s; E {{ v, Q -∗ Φ v }} -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
  iIntros (v) "HΦ". by iApply "HΦ".
Qed.

End wp.

Global Arguments AllowsStuttering {_} _ _ {_}.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisG Λ AS Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_stutteringatomic p s E1 E2 e P Φ :
    AllowsStuttering AS Σ →
    StutteringAtomic (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_stuttering_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp_stuttering {X} E1 E2 α β γ e s Φ :
    AllowsStuttering AS Σ →
    StutteringAtomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? ? _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_atomic.
  Qed.

  Global Instance elim_acc_wp_atomic {X} E1 E2 α β γ e s Φ :
    Atomic (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) True (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ? _.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
