From iris.algebra Require Import auth gmap frac agree coPset gset frac_auth ofe.
From iris.base_logic Require Export own gen_heap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris.program_logic Require Import weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Export
     helpers lang notation tactics network resources_lemmas.
From stdpp Require Import fin_maps gmap.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : aneris_to_val _ = Some _ |- _ => apply to_base_aneris_val in H
  | H : ground_lang.head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1);
     inversion H; subst; clear H
  | H: socket_step _ ?e _ _ _ _ _ _ _ |- _ =>
    try (is_var e; fail 1);
     inversion H; subst; clear H
         end.

Local Ltac solve_exec_safe :=
  intros;
  repeat match goal with
         | H: _ ∧ _ |- _ => destruct H as [??]
         end;
  simplify_eq;
  do 3 eexists; eapply (LocalStepPureS _ ∅); econstructor; eauto.
Local Ltac solve_exec_puredet :=
  simpl; intros; inv_head_step;
  first (by repeat match goal with
                   | H: _ ∧ _ |- _ => destruct H as [??]; simplify_eq
                   | H : to_val _ = Some _ |- _ =>
                     rewrite to_of_val in H; simplify_eq
                   end);
  try by match goal with
         | H : socket_step _ _ _ _ _ _ _ _ _ |- _ =>
           inversion H
         end.
Local Ltac solve_pure_exec :=
  simplify_eq; rewrite /PureExec; intros;
  apply nsteps_once, pure_head_step_pure_step;
  constructor; [solve_exec_safe | solve_exec_puredet].

Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Section lifting_network_local.
  Context `{distG Σ}.

  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : aneris_val → iProp Σ.
  Implicit Types efs : list aneris_expr.
  Implicit Types σ : state.

  Local Transparent IsNode.

  (** Weakest Precondition rules for Network-aware steps *)

(** Fork *)
  Lemma wp_fork n k E e Φ :
    ▷ Φ (mkVal n #()) ∗ ▷ WP (mkExpr n e) @ k; ⊤ {{ _, True }} ⊢
    WP (mkExpr n (Fork e)) @ k; E {{ Φ }}.
  Proof.
    iIntros "[HΦ He]". iApply wp_lift_atomic_head_step; [done|].
    iIntros (σ1 κ κs m) "Hσ !>". iSplit.
    - iPureIntro. eexists; solve_exec_safe.
    - iIntros (? ? ? ?). inv_head_step. iFrame. done.
  Qed.

(** Heap *)
Lemma wp_alloc n k E v :
  {{{ ▷ IsNode n }}} (mkExpr n (Alloc (Val v))) @ k; E
  {{{ l, RET (mkVal n #l); l ↦[n] v }}}.
Proof.
  iIntros (Φ) ">Hn HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? ? ?) "H !>"; simpl in *.
  iDestruct "H" as (m Hloch) "(Hsicoh & Hmaps & HlocS & Hrest)".
  rewrite /IsNode. iDestruct "Hn" as (γ's) "Hn".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps with "HlocS") as %[h Hninss];
    first by apply Hninm.
  iSplitR.
  { iPureIntro. do 4 eexists. eapply LocalStepS; eauto. }
  iIntros (v2 σ2 efs Hstep); inv_head_step. iFrame.
  destruct γ's as [γh γs]; iSplitR; auto; iFrame. iNext.
  iDestruct (node_local_state with "[HlocS]") as "(Hl & HlocS)";
    first done; iFrame.
  iDestruct "Hl" as (h' S' Hh Hs) "(Hn' & Hheap & Hsockets)";
    rewrite Hh in Hninss; simplify_eq; simpl.
  iMod (@gen_heap_alloc with "[Hheap]")
    as "(Hheap & Hl & Hlm)"; eauto.
  iDestruct (map_local_state_i_update_heaps with "HlocS") as "HlocS".
  iModIntro. iSplitR "HΦ Hl Hn".
  + iExists m; iFrame.
    iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; simpl.
    { iExists _,_. simpl in *; iFrame; simpl. iPureIntro.
      by rewrite lookup_insert. }
    iFrame. rewrite /gnames_coherence.
    rewrite (dom_insert_Some (D:=gset ip_address) _ _ h) /= //.
    iDestruct "Hrest" as "(HFP & HCoh & Hrest)".
    iSplit; first done. iSplitL "HFP".
    *  iDestruct "HFP" as (Fiu Piu) "((% & % & % & %) & HFP)".
       iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto.
       ddeq n ip; set_solver. set_solver.
    * iApply (network_coherence_later with "[$HCoh $Hrest]").
  + iApply "HΦ". iExists _. iFrame.
Qed.

Lemma wp_load n k E l q v :
  {{{ ▷ l ↦[n]{q} v }}}
    (mkExpr n (Load #l)) @ k; E
  {{{ RET (mkVal n v); l ↦[n]{q} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n') "Hσ !>".
  iDestruct "Hσ" as (m Hlcoh) "(Hsic & Hmaps & HlocS & Hrest)".
  iDestruct "Hl" as ([γh γs]) "(Hn & Hl)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps _ _ _ _ Hninm with "HlocS") as %[h Hninss].
  iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS)";
    first done; iFrame.
  iDestruct "Hloc" as (h' S' Hheap Hsockets) "(Hn' & Hheap & Hsockets)".
  iDestruct (@gen_heap_valid with "Hheap Hl") as %?. iSplit.
  { iPureIntro. do 4 eexists. eapply LocalStepS; eauto. eapply LoadS; eauto. }
  iIntros (e2 σ2 efs Hstep). inv_head_step.
  iFrame. iNext; iModIntro; iSplit => //=.
  iSplitR "HΦ Hl Hn".
  + iExists m; iFrame.
    iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; eauto.
    { iExists h',S'; iFrame; auto. }
    { rewrite insert_id; last auto. iFrame.
      iSplit; first by rewrite /gnames_coherence.
    iDestruct "Hrest" as "(HFP & HCoh & Hrest)".
    iSplitL "HFP".
    *  iDestruct "HFP" as (Fiu Piu) "((% & % & % & %) & HFP)".
       iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto.
       ddeq n ip; set_solver. set_solver.
    * iApply (network_coherence_later with "[$HCoh $Hrest]"). }
  + iApply "HΦ". iExists _. iFrame.
Qed.


Lemma wp_store n k E l v' v :
  {{{ ▷ l ↦[n] v' }}}
    (mkExpr n (Store #l (Val v))) @ k; E
  {{{ RET (mkVal n #()); l ↦[n] v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n') "Hσ !>".
  iDestruct "Hσ" as (m Hlcoh) "(Hsic & Hmaps & HlocS & Hrest)".
  iDestruct "Hl" as ([γh γs]) "(Hn & Hl)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps _ _ _ _ Hninm with "HlocS") as %[h Hninss].
  iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
    first done; iFrame.
  iDestruct "Hloc" as (h' S' Hheap Hsockets) "(Hn' & Hheap & Hsockets)".
  rewrite Hheap in Hninss; simplify_eq.
  iDestruct (@gen_heap_valid with "Hheap Hl") as %?.
  iSplit.
  { iPureIntro; do 4 eexists. eapply LocalStepS; eauto.
     eapply StoreS; eauto. }
  iIntros (v2 σ2 efs Hstep); inv_head_step. iFrame; iNext.
  iMod (gen_heap_update with "Hheap Hl")
    as "(Hheap & Hl)".
  iFrame. iModIntro. iSplit=>//.
  iSplitR "HΦ Hl Hn".
  iExists m; iFrame.
  iDestruct (map_local_state_i_update_heaps with "HlocS") as "HlocS".
  iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; eauto.
     iExists (<[l:=_]>h),S'.
    iFrame; iSplit; iPureIntro;
      [ apply lookup_insert | auto ].
    iFrame. iSplit. rewrite /gnames_coherence.
    rewrite (dom_insert_Some (D:=gset ip_address) _ _ h) /= //.
    iDestruct "Hrest" as "(HFP & HCoh & Hrest)".
    iSplitL "HFP".
    *  iDestruct "HFP" as (Fiu Piu) "((% & % & % & %) & HFP)".
       iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto.
       ddeq n ip; set_solver. set_solver.
    * iApply (network_coherence_later with "[$HCoh $Hrest]").
    * iApply "HΦ". iExists _. iFrame.
Qed.

Lemma wp_cas_fail n k E l q v' v1 v2 :
  v' ≠ v1 →
  {{{ ▷ l ↦[n]{q} v' }}}
    (mkExpr n (CAS #l (Val v1) (Val v2))) @ k; E
  {{{ RET (mkVal n #false); l ↦[n]{q} v' }}}.
Proof.
  iIntros (Heq Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n') "Hσ !>".
  iDestruct "Hσ" as (m Hlcoh) "(Hsic & Hmaps & HlocS & Hrest)".
  iDestruct "Hl" as ([γh γs]) "(Hn & Hl)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps _ _ _ _ Hninm with "HlocS") as %[h Hninss].
  iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
    first done; iFrame.
  iDestruct "Hloc" as (h' S' Hheap Hsockets) "(Hn' & Hheap & Hsockets)".
  iDestruct (@gen_heap_valid with "Hheap Hl") as %?. iSplit.
  { iPureIntro; do 4 eexists. eapply LocalStepS; eauto. eapply CasFailS; eauto. }
  iIntros (v2' σ2 efs Hstep); inv_head_step.
  iFrame; iNext; iModIntro; iSplit=>//; iSplitR "HΦ Hl Hn".
  + iExists m; iFrame.
    iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; eauto.
    { iExists h',S'; iFrame; auto. }
    rewrite insert_id; last auto. iFrame.
      iSplit; first by rewrite /gnames_coherence.
    iDestruct "Hrest" as "(HFP & HCoh & Hrest)".
    iSplitL "HFP".
    *  iDestruct "HFP" as (Fiu Piu) "((% & % & % & %) & HFP)".
       iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto.
       ddeq n ip; set_solver. set_solver.
    * iApply (network_coherence_later with "[$HCoh $Hrest]").
  + iApply "HΦ". iExists _. iFrame.
Qed.


Lemma wp_cas_suc n k E l v1 v2 :
  {{{ ▷ l ↦[n] v1 }}}
    (mkExpr n (CAS #l (Val v1) (Val v2))) @ k; E
  {{{ RET (mkVal n #true); l ↦[n] v2 }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 κ κs n') "Hσ !>".
  iDestruct "Hσ" as (m Hlcoh) "(Hsic & Hmaps & HlocS & Hrest)".
  iDestruct "Hl" as ([γh γs]) "(Hn & Hl)".
  iDestruct (node_in_map with "Hn Hmaps") as %Hninm.
  iDestruct (node_in_state_heaps _ _ _ _ Hninm with "HlocS") as %[h Hninss].
  iDestruct (node_local_state with "[HlocS]") as "(Hloc & HlocS) ";
    first done; iFrame.
  iDestruct "Hloc" as (h' S' Hheap Hsockets) "(Hn' & Hheap & Hsockets)".
  iDestruct (@gen_heap_valid with "Hheap Hl") as %?. iSplit.
  { iPureIntro; do 4 eexists. eapply LocalStepS; eauto. eapply CasSucS; eauto. }
  iIntros (v2' σ2 efs Hstep); inv_head_step. iFrame; iNext.
  iMod (gen_heap_update with "Hheap Hl") as "(Hheap & Hl)".
  iFrame. iModIntro. iSplit=>//.
   iSplitR "HΦ Hl Hn".
  - iExists m; iFrame.
    iDestruct (map_local_state_i_update_heaps with "HlocS") as "HlocS".
    iDestruct (node_local_state_rev with "[Hn' Hheap Hsockets] HlocS")
      as "HX"; first done; eauto.
    iExists (<[l:=_]>h),S'.
    iFrame; iSplit; iPureIntro;
      [ apply lookup_insert | auto ].
    iFrame. rewrite /gnames_coherence.
    rewrite (dom_insert_Some (D:=gset ip_address) _ _ h) /= //.
    iSplit; first done.
    iDestruct "Hrest" as "(HFP & HCoh & Hrest)".
    iSplitL "HFP".
    *  iDestruct "HFP" as (Fiu Piu) "((% & % & % & %) & HFP)".
       iExists Fiu, Piu. simpl. iFrame. iPureIntro. repeat split; try eauto.
       ddeq n ip; set_solver. set_solver.
    * iApply (network_coherence_later with "[$HCoh $Hrest]").
  - iApply "HΦ". iExists _. iFrame.
Qed.

End lifting_network_local.
