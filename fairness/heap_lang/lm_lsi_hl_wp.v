From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.prelude Require Import classical_instances.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.fairness Require Export fairness fuel partial_ownership lm_steps_gen.
From trillium.program_logic Require Import ectx_lifting.
From trillium.fairness.heap_lang Require Export heap_lang_defs. 
From trillium.fairness.heap_lang Require Import tactics notation.

Set Default Proof Using "Type".

Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).


Section lifting.
Context `{Countable G}.
Context `{EM: ExecutionModel heap_lang M}.   
Context `{hGS: @heapGS Σ _ EM}.
Context `{iLM:LiveModel G iM LSI}.
Context `{PMPP: @PartialModelPredicatesPre G _ _ Σ iM}.
Context {relies_on: locale heap_lang -> G -> iProp Σ}.

Let eGS := heap_fairnessGS. 

Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types tid : nat.


(* TODO: fix notations *)
Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).
Notation " τ '⤞' g" := (relies_on τ g) (at level 20). 

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
(* Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core. *)

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _) => apply alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Notation "'LSGn' Einvs" := (LM_steps_gen_nofork Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := eGS) (relies_on := relies_on)) (at level 10). 
Notation "'LSG' Einvs" := (LM_steps_gen Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := eGS) (relies_on := relies_on)) (at level 10). 

Lemma wp_lift_pure_step_no_fork tid g E E' Einvs Φ e1 e2 fs ϕ:
  LSI_fuel_independent (LSI := LSI) ->
  fs ≠ ∅ ->
  PureExec ϕ 1 e1 e2 ->
  ϕ ->
  (* (PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := eGS)) *)
  LSGn Einvs
    ∗
  (|={E}[E']▷=> tid ⤞ g ∗ has_fuels_S g fs ∗ (tid ⤞ g -∗ has_fuels g fs -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using. 
  intros PRES NnO Hpe Hϕ.
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hϕ). by apply nsteps_once_inv in Hpe. }
  iIntros "[#PMP H]". iApply wp_lift_step; eauto.
  { destruct Hps as [Hred _]. specialize (Hred inhabitant). eapply reducible_not_val; eauto. }
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  
  iMod "H". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "H" as "(RON & Hfuels & Hkont)".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(%&Hgh&Hmi)".

  (* TODO: get rid of iDestruct? *)
  iDestruct (update_no_step_enough_fuel_keep_gen with "PMP RON") as "HH"; eauto. 
  { by intros X%dom_empty_inv_L. }
  { econstructor =>//; by apply fill_step. }
  iMod ("HH" with "Hfuels Hmi") as "H".

  iModIntro.
  iDestruct ("H") as (δ2 ℓ Hvse) "(RON & Hfuels & Hmi)".
  iExists δ2, ℓ.
  rewrite /state_interp /=.
  rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
  iSplitR; [done| ]. iSplitL; [| done]. 
  iApply ("Hkont" with "RON"). iApply (has_fuels_proper with "Hfuels") =>//.
  rewrite map_filter_id //. intros ?? ?%elem_of_dom_2; set_solver.
Qed.

(* TODO: restore if needed *)
Lemma wp_lift_pure_step_no_fork_remove_role
  rem s tid g E E' Einvs Φ e1 e2
  (fs: gmap (fmrole iM) nat)
  ϕ:
  fs ≠ ∅ ->
  rem ⊆ dom fs →
  rem ∩ live_roles _ s = ∅ →
  PureExec ϕ 1 e1 e2 ->
  ϕ ->
  fuel_drop_preserves_LSI s rem (LSI := LSI) ->
  LSGn Einvs ∗
  (|={E}[E']▷=> partial_model_is s ∗ tid ⤞ g ∗ has_fuels_S g fs ∗
                 (partial_model_is s -∗ tid ⤞ g -∗ (has_fuels g (fs ⇂ (dom fs ∖ rem))) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using.
  intros NnO Hincl Hdisj Hpe Hϕ PRES. 
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hϕ). by apply nsteps_once_inv in Hpe. }
  iIntros "[#LSGn H]". iApply wp_lift_step; eauto.
  { destruct Hps as [Hred _]. specialize (Hred inhabitant). eapply reducible_not_val; eauto. }
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  iMod "H". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "H" as "(Hmod & RON & Hfuels & Hkont)".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(%&Hgh&Hmi)".

  iDestruct (update_no_step_enough_fuel_drop_gen with "LSGn RON") as "HH"; eauto. 
  { by intros X%dom_empty_inv_L. }
  { by rewrite intersection_comm_L. }
  { econstructor =>//; by apply fill_step. }
  iMod ("HH" with "Hfuels Hmod Hmi") as "H".

  iDestruct ("H") as (δ2 ℓ EV) "(RON & Hfuels & Hmod & Hmi)".
  iExists δ2, ℓ.
  rewrite /state_interp /=.
  rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
  iModIntro.
  repeat iSplit; last done.
  - iPureIntro. done. 
  - iApply ("Hkont" with "[$] [$] [$]").
Qed.

Lemma wp_lift_pure_step_no_fork' fs tid g E E' Einvs Φ e1 e2:
  LSI_fuel_independent (LSI := LSI) ->
  fs ≠ ∅ ->
  PureExec True 1 e1 e2 ->
  LSGn Einvs ∗ (|={E}[E']▷=> tid ⤞ g ∗ has_fuels_S g fs ∗ (tid ⤞ g -∗ (has_fuels g fs) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using.
  intros. by iApply wp_lift_pure_step_no_fork.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole tid g E E' Einvs Φ e1 e2 ρ f φ:
  LSI_fuel_independent (LSI := LSI) ->
  PureExec φ 1 e1 e2 -> φ ->
  LSGn Einvs ∗ (|={E}[E']▷=> tid ⤞ g ∗ has_fuel g ρ (S f) ∗ (tid ⤞ g -∗ (has_fuel g ρ f) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using. 
  iIntros (???) "H". rewrite has_fuel_fuels_S.
  iApply (wp_lift_pure_step_no_fork {[ ρ := f ]} {[ρ]}); eauto; last first.
  rewrite has_fuel_fuels //. apply map_non_empty_singleton.
Qed.


Lemma wp_lift_pure_step_no_fork_take_step_stash s1 s2 tid g E E' Einvs fs1 fs2 fr1 fr_stash Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  Einvs ⊆ E ->
  valid_new_fuelmap (LM := iLM) fs1 fs2 s1 s2 ρ ->
  live_roles iM s2 ∖ live_roles iM s1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2 →
  fr_stash ⊆ dom fs1 →
  live_roles iM s1 ∩ (fr_stash ∖ {[ρ]}) = ∅ → 
  dom fs2 ∩ fr_stash = ∅ ->
  iM.(fmtrans) s1 (Some ρ) s2 ->
  model_step_preserves_LSI s1 ρ s2 fs1 fs2 (LSI := LSI) ->
  LSGn Einvs ∗ (|={E}[E']▷=> partial_model_is s1 ∗ tid ⤞ g ∗ has_fuels g fs1 ∗ partial_free_roles_are fr1 ∗
                 (partial_model_is s2 -∗ partial_free_roles_are (fr1 ∖ (live_roles iM s2 ∖ (live_roles iM s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash)
                  -∗ tid ⤞ g -∗ has_fuels g fs2 -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using.
  iIntros (Hpe Hφ Hinvs Hval Hfr ??? Htrans PRES).
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hφ). by apply nsteps_once_inv in Hpe. }
  iIntros "[PMP Hkont]".

  iApply wp_lift_step; eauto.
  { destruct (pure_step_safe _ e2 Hps inhabitant) as (?&?&?&?). by eapply val_stuck. }

  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  iMod "Hkont". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "Hkont" as "(Hmod&RON&Hfuels&Hfr&Hkont)".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(%&Hgh&Hmi)". simpl.

  (* iDestruct (update_step_still_alive _ _ _ _ σ1 σ1 with "PMP Hfuels Hmod Hmi Hfr") as "H"; eauto. *)
  iDestruct (update_step_still_alive_gen _ _ _ _ σ1 σ1 with "PMP RON Hfuels Hmod [Hmi] Hfr") as "H"; eauto.
  2: { rewrite Hexend. iFrame. }
  { econstructor =>//. by apply fill_step. }
  (* { rewrite Hmeq. apply Hval. } *)
  iMod (fupd_mask_mono with "H") as "H"; [apply Hinvs| ]. 

  iModIntro. iDestruct "H" as (δ2 ℓ Hvse) "(RON&Hfuels&Hmod&Hmi&Hfr)".
  iExists δ2, ℓ.
  rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
  repeat iSplit; [done| .. | done]. 
  by iSpecialize ("Hkont" with "Hmod Hfr RON Hfuels").
Qed. 

Lemma wp_lift_pure_step_no_fork_take_step s1 s2 tid g E E' Einvs fs1 fs2 fr1 Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  Einvs ⊆ E ->  
  valid_new_fuelmap (LM := iLM) fs1 fs2 s1 s2 ρ ->
  live_roles iM s2 ∖ live_roles iM s1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2 →
  iM.(fmtrans) s1 (Some ρ) s2 ->
  model_step_preserves_LSI s1 ρ s2 fs1 fs2 (LSI := LSI) ->
  LSGn Einvs ∗
  (|={E}[E']▷=> partial_model_is s1 ∗ tid ⤞ g ∗ has_fuels g fs1 ∗ partial_free_roles_are fr1 ∗
                 (partial_model_is s2 -∗ partial_free_roles_are (fr1 ∖ (live_roles iM s2 ∖ (live_roles iM s1 ∪ dom fs1 ∩ dom fs2)))
                  -∗ tid ⤞ g -∗ (has_fuels g fs2 -∗ WP e2 @ tid; E {{ Φ }})))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using.
  iIntros.
  iApply wp_lift_pure_step_no_fork_take_step_stash.
  5: { apply empty_subseteq. }
  all: eauto. 
  1, 2: set_solver.
  by rewrite union_empty_r_L.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole_take_step s1 s2 tid g E E' Einvs
  (f1 f2: nat) fr Φ e1 e2 ρ φ
  (fs2 := if decide (ρ ∈ live_roles iM s2) then {[ ρ := f2 ]} else ∅ )
  :
  PureExec φ 1 e1 e2 -> φ ->
  Einvs ⊆ E ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (f2 ≤ iLM.(lm_fl) s2)%nat -> iM.(fmtrans) s1 (Some ρ) s2 ->
  model_step_preserves_LSI s1 ρ s2 {[ ρ := f1 ]} fs2 (LSI := LSI) ->
  LSGn Einvs ∗ (|={E}[E']▷=> partial_model_is s1 ∗ partial_free_roles_are fr ∗ tid ⤞ g ∗ has_fuel g ρ f1 ∗
   (partial_model_is s2 -∗ partial_free_roles_are fr -∗ tid ⤞ g -∗ (if decide (ρ ∈ live_roles iM s2) then has_fuel g ρ f2 else (g ↦M ∅) ) -∗
                               WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using.
  iIntros (Hpe Hφ Hinvs Hroles Hfl Hmdl PRES).
  rewrite has_fuel_fuels.
  iIntros "[LSGn H]".
  iApply (wp_lift_pure_step_no_fork_take_step _ _ _ _ _ _ _ {[ρ := f1]} fs2 fr  with "[LSGn H]"); eauto.
  - subst fs2. repeat split.
    + intros ?. rewrite decide_True //. rewrite lookup_singleton //=. 
    + destruct (decide (ρ ∈ live_roles _ s2)); set_solver.
    + set_solver.
    + intros ρ' Hdom. destruct (decide (ρ ∈ live_roles iM s2)); set_solver.
    + intros ρ' Hneq Hin. destruct (decide (ρ ∈ live_roles iM s2)); set_solver.
    + destruct (decide (ρ ∈ live_roles iM s2)); set_solver.
    + destruct (decide (ρ ∈ live_roles iM s2)); set_solver.
  - set_solver.
  - iFrame. iMod "H". do 2 iModIntro. iMod "H" as "(Hmod&Hfr&RON&Hfuels&Hkont)". iModIntro.
    iFrame "Hmod RON Hfr Hfuels". iIntros "Hmod Hfr RON Hfuels". iApply ("Hkont" with "Hmod [Hfr] [RON] [Hfuels]").
    + iApply partial_free_roles_are_Proper; [| by iFrame].
      set_solver.
    + done. 
    + destruct (decide (ρ ∈ live_roles iM s2)).
      * rewrite -has_fuel_fuels //.
      * iDestruct "Hfuels" as "[Hf _]". rewrite dom_empty_L //.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole' tid g E E' Einvs Φ e1 e2 ρ f:
  LSI_fuel_independent (LSI := LSI) ->
  PureExec True 1 e1 e2 ->
  LSGn Einvs ∗ (|={E}[E']▷=> tid ⤞ g ∗ has_fuel g ρ (S f) ∗ (tid ⤞ g -∗ (has_fuel g ρ f) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using.
  iIntros (??) "H". rewrite has_fuel_fuels_S.
  iApply (wp_lift_pure_step_no_fork' {[ ρ := f ]} {[ρ]}); auto; last first.
  rewrite has_fuel_fuels //. apply map_non_empty_singleton.
Qed.

(* Let has_fuels_actual := has_fuels (PMPP := ActualOwnershipPartialPre).  *)
(* Let has_fuels_partial := has_fuels (PMPP := PMPP). *)
(* Let has_fuels_S_partial := has_fuels_S (PMPP := PMPP). *)

(* Unset Printing Notations. *)
(* Set Printing Implicit.  *)
(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork_nostep s tid g E Einvs e Φ R1 R2
  (fs: gmap (fmrole iM) nat) (Hdisj: R1 ## R2) (Hnemp: fs ≠ ∅):
  fuel_reorder_preserves_LSI (LSI := LSI) ->
  R1 ∪ R2 = dom fs ->
  LSG Einvs ∗ (∀ tid' g', ▷ (tid' ⤞ g' ∗ has_fuels g' (fs ⇂ R2) -∗
                WP e @ s; tid'; ⊤ {{ _, partial_mapping_is {[ g' := ∅ ]}  }})
  ) -∗
     ▷ (tid ⤞ g ∗ has_fuels g (fs ⇂ R1) ={E}=∗ Φ (LitV LitUnit)) -∗
     tid ⤞ g -∗ has_fuels_S g fs -∗ WP Fork e @ s; tid; E {{ Φ }}.
Proof using.
  iIntros (? Hunioneq) "[PMP He] HΦ RON Htid". iApply wp_lift_atomic_head_step; [done|].
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".

  (* iPoseProof (update_fork_split_gen R1 R2 _ *)
  (*      (tp1 ++ ectx_language.fill K (Val $ LitV LitUnit) :: tp2 ++ [e]) fs _ _ _ _ e _ σ1 with "PMP Htid Hmi") *)
  
  iMod (update_fork_split_gen R1 R2 _
       (tp1 ++ ectx_language.fill K (Val $ LitV LitUnit) :: tp2 ++ [e]) fs _ _ _ _ e _ σ1 with "PMP RON Htid Hmi")
    as (δ2 ? ?) "(RON2 & Hfuels2 & RON1 & Hfuels1 & Hterm & Hσ & %Hvse)" => //.
  { rewrite -Hloc. rewrite -(language.locale_fill _ _ K). econstructor 1 =>//.
    apply fill_step, head_prim_step. econstructor. }
  { list_simplifier. exists (tp1 ++ fill K #() :: tp2). split; first by list_simplifier.
    rewrite !app_length //=. }
  iModIntro. iSplit.
  { iPureIntro; first by eauto. }

  iNext.
  iIntros (e2 σ2 efs Hstep).
  have [-> [-> ->]] : σ2 = σ1 ∧ efs = [e] ∧ e2 = Val $ LitV LitUnit by inv_head_step.
  iMod ("HΦ" with "[RON1 Hfuels1]") as "HΦ"; [by iFrame| ].   
  iModIntro. iExists δ2, ℓ. iFrame.
  rewrite Hexend /=. iFrame "Hsi".
  iSplit; first by iPureIntro.
  iSplit; [|done].
  simpl. 

  list_simplifier.
  iApply (wp_strong_mono with "[Hfuels2 RON2 He] [Hterm]").
  1, 2: by reflexivity.
  { iApply "He". iFrame. }
  iIntros. iModIntro.
  by iApply "Hterm". 
Qed.

Lemma wp_fork_nostep_alt s tid g E Einvs e Φ
  (fs1 fs2: gmap (fmrole iM) nat)
  (DISJ: fs1 ##ₘ fs2)
  (NE: fs1 ∪ fs2 ≠ ∅):
  fuel_reorder_preserves_LSI (LSI := LSI) ->
  LSG Einvs ∗ (∀ tid' g', ▷ (tid' ⤞ g' -∗ has_fuels g' fs2 -∗
                WP e @ s; tid'; ⊤ {{ _, partial_mapping_is {[ g' := ∅ ]}  }})
  ) -∗
     ▷ (tid ⤞ g ∗ has_fuels g fs1 ={E}=∗ Φ (LitV LitUnit)) -∗
     tid ⤞ g -∗ has_fuels_S g (fs1 ∪ fs2) -∗ WP Fork e @ s; tid; E {{ Φ }}.
Proof using.
  iIntros (?) "[PMP FORK] FUEL1 FUEL".
  iApply (wp_fork_nostep with "[PMP FORK] [FUEL1]").
  { by eapply map_disjoint_dom_1. }
  1, 2, 3: set_solver.
  3: done. 
  { iFrame. iIntros (? ?). iNext. iIntros "[RON FUEL]". iApply ("FORK" with "[$]").
    iApply has_fuels_proper; [reflexivity| | iFrame].
    rewrite map_union_comm; auto.
    by apply leibniz_equiv_iff, gmap_filter_disj_id. }
  iNext. iIntros "[RON FUEL]". iApply "FUEL1". iFrame. 
  iApply has_fuels_proper; [reflexivity| | iFrame].
  by apply leibniz_equiv_iff, gmap_filter_disj_id.
Qed.


Lemma wp_allocN_seq_nostep s tid g E Einvs v n fs:
  LSI_fuel_independent (LSI := LSI) ->
  fs ≠ ∅ ->
  0 < n →
  LSGn Einvs ⊢
  {{{ tid ⤞ g ∗ has_fuels_S g fs }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; tid; E
  {{{ l, RET LitV (LitLoc l); tid ⤞ g ∗ has_fuels g fs ∗ [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof using.
  iIntros (? HnO Hn) "#PMP".
  iIntros (Φ). iModIntro. iIntros "[RON HfuelS] HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iModIntro; iSplit; [by eauto| ]. 
  iIntros (e2 σ2 efs Hstep). iNext.
  inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hsi")
    as "(Hsi & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id ?Hexend; auto with lia. }
  iMod (update_no_step_enough_fuel_keep_gen _ _ with "PMP RON HfuelS Hmi") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hmi)" =>//.
  { by intros ?%dom_empty_inv_L. }
  (* { set_solver. } *)
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists δ2, ℓ.
  rewrite Hexend //=. iFrame "Hmi Hsi".
  repeat iSplit =>//.
  iApply "HΦ". iFrame. iSplitL "Hfuel".
  { iApply (has_fuels_proper with "Hfuel") =>//.
    rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver. }
  iApply big_sepL_sep. iSplitL "Hl".
  + by iApply heap_array_to_seq_mapsto.
  + iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma wp_alloc_nostep s tid g E Einvs v fs :
  LSI_fuel_independent (LSI := LSI) ->
  fs ≠ ∅ ->
  LSGn Einvs ⊢ {{{ tid ⤞ g ∗ has_fuels_S g fs }}} Alloc (Val v) @ s; tid; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ ∗ tid ⤞ g ∗ has_fuels g fs }}}.
Proof using. 
  iIntros (??) "#PMP". iModIntro. iIntros (Φ) "[RON HfuelS] HΦ".
  iApply (wp_allocN_seq_nostep with "PMP [RON HfuelS]"); auto with lia.
  2: by iFrame.
  { done. }
  iIntros "!>" (l) "/= (? & ? & ? & _)". rewrite loc_add_0. by iApply "HΦ"; iFrame.
Qed.

Lemma wp_choose_nat_nostep s tid g E Einvs fs :
  LSI_fuel_independent (LSI := LSI) ->
  fs ≠ ∅ ->
  LSGn Einvs ⊢ {{{ tid ⤞ g ∗ has_fuels_S g fs }}}
    ChooseNat @ s; tid; E
  {{{ (n:nat), RET LitV (LitInt n); tid ⤞ g ∗ has_fuels g fs }}}.
Proof using. 
  iIntros (??). iIntros "#PMP". iModIntro. iIntros (Φ) "[RON HfuelS] HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iModIntro; iSplit; eauto.
  (* TODO: Improve this so we hide the (arbitrary) choice of `n` *)
  Unshelve. 2: apply O.
  iIntros (e2 σ2 efs Hstep). iNext.
  inv_head_step.
  iMod (update_no_step_enough_fuel_keep_gen _ _ with "PMP RON HfuelS Hmi") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hmi)" =>//.
  { by intros ?%dom_empty_inv_L. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists δ2, ℓ.
  rewrite Hexend //=. iFrame "Hmi Hsi".
  repeat iSplit =>//.
  iApply "HΦ". iFrame. 
  iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.

Lemma wp_load_nostep s tid g E Einvs l q v fs:
  LSI_fuel_independent (LSI := LSI) ->
  fs ≠ ∅ ->
  LSGn Einvs ⊢ {{{ ▷ l ↦{q} v ∗ tid ⤞ g ∗ has_fuels_S g fs }}} Load (Val $ LitV $ LitLoc l) @ s; tid; E {{{ RET v; l ↦{q} v ∗ tid ⤞ g ∗ has_fuels g fs }}}.
Proof using. 
  iIntros (??). iIntros "#PMP". iModIntro. iIntros (Φ) "[>Hl [RON HfuelS]] HΦ". 
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iMod (update_no_step_enough_fuel_keep_gen _ _ with "PMP RON HfuelS Hmi") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hmod)" =>//.
  { by intros ?%dom_empty_inv_L. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists _,_.
  rewrite Hexend //=. iFrame "Hsi Hmod".
  do 2 (iSplit=>//).
  iApply "HΦ". iFrame. iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.

Lemma wp_store_nostep s tid g E Einvs l v' v fs:
  LSI_fuel_independent (LSI := LSI) ->
  fs ≠ ∅ ->
  LSGn Einvs ⊢ {{{ ▷ l ↦ v' ∗ tid ⤞ g ∗ has_fuels_S g fs }}}
    Store (Val $ LitV (LitLoc l)) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ tid ⤞ g ∗ has_fuels g fs }}}.
Proof using. 
  iIntros (??). iIntros "#PMP". iModIntro. iIntros (Φ) "[>Hl [RON HfuelS]] HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod (update_no_step_enough_fuel_keep_gen _ _ with "PMP RON HfuelS Hmi") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hmod)" =>//.
  { by intros ?%dom_empty_inv_L. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists _,_.
  rewrite Hexend //=. iFrame "Hsi Hmod".
  do 2 (iSplit=>//).
  iApply "HΦ". iFrame. iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.


(* TODO: clean up all those similar lemmas *)
Lemma wp_store_step_keep s tid g ρ (fs1 fs2: gmap (fmrole iM) nat) fr fr_stash s1 s2 E Einvs l v' v
  (INVS: Einvs ⊆ E)
  (STEP: fmtrans iM s1 (Some ρ) s2)
  (VFM: valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := iLM))
  (LR : live_roles iM s2 ∖ live_roles iM s1 ⊆ fr ∪ dom fs1 ∩ dom fs2) 
  (STASH : fr_stash ⊆ dom fs1) 
  (NSL : live_roles iM s1 ∩ (fr_stash ∖ {[ρ]}) = ∅)
  (NOS2 : dom fs2 ∩ fr_stash = ∅)
  (PRES: model_step_preserves_LSI s1 ρ s2 fs1 fs2 (LSI := LSI)):
  LSGn Einvs ⊢
  {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ tid ⤞ g ∗  ▷ has_fuels g fs1 ∗
      ▷ partial_free_roles_are fr}}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ partial_model_is s2 ∗ tid ⤞ g ∗ has_fuels g fs2 ∗
                        partial_free_roles_are (fr ∖ (live_roles _ s2 ∖ (live_roles _ s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash)}}}. 
Proof using. 
  iIntros "#PMP !#" (Φ) "(>Hl & >Hst & RON & >Hfuel1 & Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto.
  iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.

  rewrite Hexend.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iDestruct (update_step_still_alive_gen _ _ _ _ _ _ _ s2 _
            (fs2)
            _ _ _ _ _ fr_stash
            with "PMP RON Hfuel1 Hst Hmi Hfr") as
    "UPD".
  
  all: eauto.
  { destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//. }
  iMod (fupd_mask_mono with "UPD") as(δ2 ℓ) "(%Hvse & RON & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
  iModIntro; iExists δ2, ℓ. iSplit.
  { iPureIntro. simpl in *. split =>//. }
  iFrame.
  iSplit; first done.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_store_step_singlerole_keep s tid g ρ (f1 f2: nat) s1 s2 E Einvs l v' v :
  Einvs ⊆ E ->
  f2 ≤ iLM.(lm_fl) s2 -> fmtrans iM s1 (Some ρ) s2 ->
  (ρ ∉ live_roles iM s2 -> (f2 < f1)%nat ) -> (* TODO: check Zombie case in must_decrease *)
  live_roles _ s2 ⊆ live_roles _ s1 ->
  model_step_preserves_LSI s1 ρ s2 {[ ρ := f1 ]} {[ ρ := f2 ]} (LSI := LSI) ->
  LSGn Einvs ⊢ {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ tid ⤞ g ∗ ▷ has_fuel g ρ f1
        (* ∗ ▷ partial_free_roles_are fr *)
  }}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ partial_model_is s2 ∗
                          (* partial_free_roles_are fr ∗ *)
      tid ⤞ g ∗ has_fuel g ρ f2 }}}. 
Proof using.
  iIntros (Hinvs Hfl Htrans Hdecr ? PRES).
  iIntros "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & RON & >Hfuel1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto.
  iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite has_fuel_fuels Hexend.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod partial_free_roles_empty as "Hfr". 
  iDestruct (update_step_still_alive_gen _ _ _ _ _ _ _ s2 _
            ({[ ρ := f2 ]})
            _ _ _ _ _ ∅
            with "PMP RON Hfuel1 Hst Hmi Hfr") as "UPD". 
  all: eauto.
  1-4: set_solver. 
  - destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles iM s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; first (intros ρ' Hin; set_solver).
      split; set_solver.
    + (* repeat (split; set_solver). *)
      repeat split. 
      1, 3-6: set_solver. 
      * intros. rewrite !lookup_singleton. simpl. apply Nat.lt_le_incl. tauto. 
      * apply fm_live_spec in Htrans. set_solver.
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hst & Hfr & Hmod)"; [done |]. 
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame.
    iSplit; first done.
    iApply "HΦ". iFrame.
    rewrite has_fuel_fuels //.
Qed.

Lemma wp_store_step_singlerole s tid g ρ (f1 f2: nat) s1 s2 E Einvs l v' v
  (fs2 := if decide (ρ ∈ live_roles iM s2) then {[ ρ := f2 ]} else ∅):
  Einvs ⊆ E ->
  f2 ≤ iLM.(lm_fl) s2 -> fmtrans iM s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  model_step_preserves_LSI s1 ρ s2 {[ ρ := f1 ]} fs2 (LSI := LSI) ->
  LSGn Einvs ⊢ {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ tid ⤞ g ∗ ▷ has_fuel g ρ f1}}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ partial_model_is s2 ∗ 
      tid ⤞ g ∗ (if decide (ρ ∈ live_roles iM s2) then has_fuel g ρ f2 else g ↦M ∅ ∗ partial_free_roles_are {[ ρ ]}) }}}.
Proof using.
  iIntros (Hinvs Hfl Htrans ? PRES). iIntros "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & RON & >Hfuel1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  (* iAssert (⌜ ρ ∉ fr ⌝)%I as %FRρ'. *)
  (* { rewrite has_fuel_fuels.  *)
  (*   iDestruct (partial_free_roles_fuels_disj with "[$] [$] [$]") as %?. *)
  (*   set_solver. } *)
  iSplit; first by rewrite Hexend // in Hheap;  eauto.
  iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite has_fuel_fuels Hexend.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod partial_free_roles_empty as "Hfr". 
  iDestruct (update_step_still_alive_gen _ _ _ _ _ _ _ s2 _
            (if decide (ρ ∈ live_roles iM s2) then {[ ρ := f2 ]} else ∅)
            _ _ _ _ _ ({[ ρ ]} ∖ live_roles _ s2)
            with "PMP RON Hfuel1 Hst Hmi Hfr")
    as "UPD".
  all: eauto. 
  1-3: set_solver.
  { destruct (decide (ρ ∈ live_roles iM s2)); set_solver. }
  - destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles iM s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; first (intros ρ' Hin; set_solver).
      split; set_solver.
    + repeat (split; set_solver).
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame.
    iSplit; first done.
    iApply "HΦ". iFrame.    
    destruct (decide (ρ ∈ live_roles iM s2)).
    + rewrite has_fuel_fuels //.
    + do 2 (rewrite difference_disjoint; [| set_solver]). rewrite union_empty_l. 
      iDestruct "Hfuel" as "[Hf _]". rewrite dom_empty_L //. iFrame. 
Qed.


Lemma wp_cmpxchg_fail_step_singlerole s tid g ρ (f1 f2: nat) fr s1 s2 E Einvs l q v' v1 v2
  (fs2 := if decide (ρ ∈ live_roles iM s2) then {[ ρ := f2 ]} else ∅):
  Einvs ⊆ E ->
  v' ≠ v1 → vals_compare_safe v' v1 → f2 ≤ iLM.(lm_fl) s2 -> iM.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  model_step_preserves_LSI s1 ρ s2 {[ ρ := f1 ]} fs2 (LSI := LSI) ->
  LSGn Einvs ⊢ {{{ ▷ l ↦{q} v' ∗ ▷ partial_model_is s1 ∗ ▷ tid ⤞ g ∗ ▷ has_fuel g ρ f1 ∗ ▷ partial_free_roles_are fr }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' ∗ partial_model_is s2 ∗ partial_free_roles_are fr ∗
      tid ⤞ g ∗ (if decide (ρ ∈ live_roles iM s2) then has_fuel g ρ f2 else g ↦M ∅ ) }}}.
Proof using.
  iIntros (Hinvs ?? Hfl Htrans ? PRES) "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & RON & >Hfuel1 & > Hfr) HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite bool_decide_false //.
  rewrite has_fuel_fuels Hexend.
  iDestruct (update_step_still_alive_gen _ _ _ _ _ _ _ _ _ fs2
            with "PMP RON Hfuel1 Hst Hmi Hfr") as "UPD". 
  2: { apply empty_subseteq. }
  all: eauto.
  1-3: set_solver. 
  - destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles iM s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; first (intros ρ' Hin; set_solver).
      split; set_solver.
    + repeat (split; set_solver).
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
    rewrite -> bool_decide_eq_false_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame.
    iSplit; first done. iApply "HΦ". iFrame.
    (* replace (fr ∖ (live_roles iM s2 ∖ live_roles iM s1)) with fr; [iFrame|set_solver]. *)
    (* rewrite union_empty_r_L.  *)
    iSplitL "Hmod".
    { iApply partial_free_roles_are_Proper; [| by iFrame]. set_solver. }
    destruct (decide (ρ ∈ live_roles iM s2)).
    + rewrite has_fuel_fuels //.
    + iDestruct "Hfuel" as "[Hf _]". rewrite dom_empty_L //. 
Qed.

Lemma wp_cmpxchg_suc_step_singlerole_keep_dead s tid g ρ (f1 f2: nat) fr s1 s2 E Einvs l v' v1 v2:
  Einvs ⊆ E ->
  ρ ∉ live_roles _ s2 →
  v' = v1 → vals_compare_safe v' v1 → f2 < f1 -> iM.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  model_step_preserves_LSI s1 ρ s2 {[ ρ := f1 ]} {[ ρ := f2 ]} (LSI := LSI) ->
  LSGn Einvs ⊢ {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ tid ⤞ g ∗ ▷ has_fuel g ρ f1 ∗ ▷ partial_free_roles_are fr }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 ∗ partial_model_is s2 ∗ partial_free_roles_are fr ∗
      tid ⤞ g ∗ has_fuel g ρ f2 }}}.
Proof using.
  iIntros (Hinvs ??? Hfl Htrans ? PRES) "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & RON & >Hfuel1 & >Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  rewrite has_fuel_fuels Hexend.
  iDestruct (update_step_still_alive_gen _ _ _ _ _ _ _ _ _ {[ ρ := f2 ]} with "PMP RON Hfuel1 Hst Hmi Hfr") as "UPD". 
  2: { apply empty_subseteq. }
  all: eauto. 
  1-3: set_solver.
  - apply head_locale_step; econstructor =>//.
  - repeat (split; try done).
    2-5: set_solver. 
    + intros ??. rewrite !lookup_singleton /=. lia.
    + rewrite dom_singleton singleton_subseteq_l. simplify_eq.
      destruct (decide (ρ ∈ live_roles _ s1)); set_solver.
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
    rewrite -> bool_decide_eq_true_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame. iSplit; first done. iApply "HΦ". iFrame.
    iSplitL "Hmod".
    { iApply partial_free_roles_are_Proper; [| by iFrame]. set_solver. }
    by rewrite has_fuel_fuels.
Qed.

Lemma wp_cmpxchg_suc_step_singlerole s tid g ρ (f1 f2: nat) fr s1 s2 E Einvs l v' v1 v2
  (fs2 := if decide (ρ ∈ live_roles iM s2) then {[ ρ := f2 ]} else ∅):
  Einvs ⊆ E ->
  v' = v1 → vals_compare_safe v' v1 → f2 ≤ iLM.(lm_fl) s2 -> iM.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  model_step_preserves_LSI s1 ρ s2 {[ ρ := f1 ]} fs2 (LSI := LSI) ->
  LSGn Einvs ⊢ {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ tid ⤞ g ∗ ▷ has_fuel g ρ f1 ∗ ▷ partial_free_roles_are fr }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 ∗ partial_model_is s2 ∗ partial_free_roles_are fr ∗
      tid ⤞ g ∗ (if decide (ρ ∈ live_roles iM s2) then has_fuel g ρ f2 else g ↦M ∅ ) }}}.
Proof using.
  iIntros (Hinvs ?? Hfl Htrans ? PRES) "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & RON & >Hfuel1 & >Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. 
  inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  rewrite has_fuel_fuels Hexend.
  iDestruct (update_step_still_alive_gen _ _ _ _ _ _ _ _ _ fs2
            with "PMP RON Hfuel1 Hst Hmi Hfr") as "UPD". 
  2: { apply empty_subseteq. }
  all: eauto. 
  1-3: set_solver.
  - destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles iM s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; set_solver.
    + repeat (split; set_solver).
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "(%Hvse & RON & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
    rewrite -> bool_decide_eq_true_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame. iSplit; first done. iApply "HΦ". rewrite union_empty_r_L. iFrame.    
    iSplitL "Hmod".
    { iApply partial_free_roles_are_Proper; [| by iFrame]. set_solver. }

    destruct (decide (ρ ∈ live_roles iM s2)).
    + rewrite has_fuel_fuels //. 
    + iDestruct "Hfuel" as "[Hf _]". rewrite dom_empty_L //. 
Qed.

End lifting.
