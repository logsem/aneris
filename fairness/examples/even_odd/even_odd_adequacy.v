From Paco Require Import paco1 paco2 pacotac.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang tactics simulation_adequacy.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness Require Import trace_utils.
From trillium.fairness.examples.even_odd Require Import even_odd.
From stdpp Require Import finite.

(** Helper lemmas for working with even and odd *)

Lemma even_odd_False n : Nat.even n → Nat.odd n → False.
Proof.
  intros Heven Hodd. rewrite -Nat.negb_odd in Heven.
  apply Is_true_true_1 in Heven.
  apply Is_true_true_1 in Hodd.
  by rewrite Hodd in Heven.
Qed.

Lemma even_not_odd n : Nat.even n → ¬ Nat.odd n.
Proof. intros Heven Hodd. by eapply even_odd_False. Qed.

Lemma odd_not_even n : Nat.odd n → ¬ Nat.even n.
Proof. intros Heven Hodd. by eapply even_odd_False. Qed.

(** The model is finitely branching *)

Definition steppable n : list (nat * option EO) :=
  n' ← [S n; n];
  ℓ ← [Some ρEven; Some ρOdd];
  mret (n', ℓ).

#[local] Instance proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in eotrans s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma model_finitary s:
  Finite { '(s', ℓ) | eotrans s ℓ s'}.
Proof.
  assert (H: forall A (y x: A) xs, (y = x ∨ y ∈ xs) -> y ∈ x::xs) by set_solver.
  eapply (in_list_finite (steppable s)).
  intros [n w] Htrans.
  inversion Htrans; try (repeat (rewrite ?Nat.sub_0_r; simpl;
    eapply H; try (by left); right); done).
Qed.

(** Proof that any fair execution of model visits all natural numbers *)

Definition evenodd_mtrace : Type := mtrace the_fair_model.

Definition evenodd_mdl_progress (tr : evenodd_mtrace) :=
  ∀ i, ∃ n, pred_at tr n (λ s _, s = i).

Definition evenodd_mdl_mono (tr : evenodd_mtrace) :=
  ∀ n, ∃ i, pred_at tr n (λ s _, s = i) ∧
            pred_at tr (S n) (λ s _, ∃ j, s = j ∧ i ≤ j).

Lemma evenodd_mdl_always_live ρ n (mtr : evenodd_mtrace) :
  infinite_trace mtr →
  pred_at mtr n
          (λ (δ : the_fair_model) (_ : option (option (fmrole the_fair_model))),
             role_enabled_model ρ δ).
Proof.
  intros Hinf. specialize (Hinf n) as [mtr' Hafter].
  rewrite /pred_at Hafter /role_enabled_model.
  destruct mtr'; destruct ρ; set_solver.
Qed.

Lemma evenodd_mdl_always_eventually_scheduled ρ (mtr : evenodd_mtrace) :
  infinite_trace mtr → fair_model_trace ρ mtr →
  ∀ n, ∃ m, pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)).
Proof.
  intros Hinf Hfair n.
  apply (evenodd_mdl_always_live ρ n mtr) in Hinf.
  specialize (Hfair n Hinf) as [m [Hfair | Hfair]].
  - rewrite /pred_at in Hfair. destruct (after (n + m) mtr); [|done].
    rewrite /role_enabled_model in Hfair. destruct t; destruct ρ; set_solver.
  - by exists m.
Qed.

Lemma evenodd_mdl_noprogress_Even i n (mtr : evenodd_mtrace) :
  infinite_trace mtr → mtrace_valid mtr → (trfirst mtr) = i → Nat.even i →
  (∀ m, m < n → pred_at mtr m (λ _ l, l ≠ Some (Some ρEven))) →
  pred_at mtr n (λ s _, s = i).
Proof.
  intros Hinf Hvalid Hfirst Heven Hne.
  induction n as [|n IHn].
  { rewrite /pred_at. destruct mtr; done. }
  simpl in *.
  assert (∀ m : nat, m < n → pred_at mtr m (λ _ l, l ≠ Some (Some ρEven))) as Hne'.
  { intros. apply Hne. lia. }
  specialize (IHn Hne'). rewrite /pred_at in IHn.
  destruct (after n mtr) as [mtr'|] eqn:Hafter; rewrite Hafter in IHn; [|done].
  rewrite /pred_at. replace (S n) with (n + 1) by lia.
  rewrite after_sum'. rewrite Hafter. specialize (Hinf (n+1)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf.
  destruct mtr'; [by apply is_Some_None in Hinf|].
  eapply mtrace_valid_after in Hvalid; [|done].
  assert (ℓ ≠ Some ρEven) as Hneq.
  { assert (n < S n) by lia. specialize (Hne n H). rewrite /pred_at in Hne.
    rewrite Hafter in Hne. intros ->. apply Hne. done. }
  pinversion Hvalid. simplify_eq. inversion H1; simplify_eq.
  - by apply even_not_odd in Heven.
  - by destruct mtr'.
Qed.

Lemma evenodd_mdl_noprogress_Odd i n (mtr : evenodd_mtrace) :
  infinite_trace mtr → mtrace_valid mtr → (trfirst mtr) = i → Nat.odd i →
  (∀ m, m < n → pred_at mtr m (λ _ l, l ≠ Some (Some ρOdd))) →
  pred_at mtr n (λ s _, s = i).
Proof.
  intros Hinf Hvalid Hfirst Hodd Hne.
  induction n as [|n IHn].
  { rewrite /pred_at. destruct mtr; done. }
  simpl in *.
  assert (∀ m : nat, m < n → pred_at mtr m (λ _ l, l ≠ Some (Some ρOdd))) as Hne'.
  { intros. apply Hne. lia. }
  specialize (IHn Hne'). rewrite /pred_at in IHn.
  destruct (after n mtr) as [mtr'|] eqn:Hafter; rewrite Hafter in IHn; [|done].
  rewrite /pred_at. replace (S n) with (n + 1) by lia.
  rewrite after_sum'. rewrite Hafter. specialize (Hinf (n+1)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf.
  destruct mtr'; [by apply is_Some_None in Hinf|].
  eapply mtrace_valid_after in Hvalid; [|done].
  assert (ℓ ≠ Some ρOdd) as Hneq.
  { assert (n < S n) by lia. specialize (Hne n H). rewrite /pred_at in Hne.
    rewrite Hafter in Hne. intros ->. apply Hne. done. }
  pinversion Hvalid. simplify_eq. inversion H1; simplify_eq.
  - by apply odd_not_even in Hodd.
  - by destruct mtr'.
Qed.

Theorem evenodd_mdl_progresses_Even i (mtr : evenodd_mtrace) :
  infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = i → Nat.even i →
  ∃ m, pred_at mtr m (λ s _, s = S i).
Proof.
  intros Hinf Hvalid Hfair Hfirst Heven.
  specialize (Hfair ρEven).
  pose proof (evenodd_mdl_always_eventually_scheduled ρEven mtr Hinf Hfair 0) as Hsched.
  simpl in *. apply trace_eventually_until in Hsched as [m [Hsched Hschedne]].
  rewrite /pred_at in Hsched.
  destruct (after m mtr) as [mtr'|] eqn:Hafter; last first.
  { rewrite Hafter in Hsched. done. }
  rewrite Hafter in Hsched.
  destruct mtr'; [done|].
  simplify_eq.
  assert (s = trfirst mtr) as ->.
  { eapply evenodd_mdl_noprogress_Even in Hschedne; [|done..].
    rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. }
  eapply mtrace_valid_after in Hvalid; [|done].
  pinversion Hvalid; simplify_eq. inversion H1; simplify_eq.
  - exists (m + 1).
    rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl.
    destruct mtr'; simpl in *; simplify_eq; done.
  - by apply even_not_odd in Heven.
Qed.

Theorem evenodd_mdl_progresses_Odd i (mtr : evenodd_mtrace) :
  infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = i → Nat.odd i →
  ∃ m, pred_at mtr m (λ s _, s = S i).
Proof.
  intros Hinf Hvalid Hfair Hfirst Hodd.
  specialize (Hfair ρOdd).
  pose proof (evenodd_mdl_always_eventually_scheduled ρOdd mtr Hinf Hfair 0) as Hsched.
  simpl in *. apply trace_eventually_until in Hsched as [m [Hsched Hschedne]].
  rewrite /pred_at in Hsched.
  destruct (after m mtr) as [mtr'|] eqn:Hafter; last first.
  { rewrite Hafter in Hsched. done. }
  rewrite Hafter in Hsched.
  destruct mtr'; [done|].
  simplify_eq.
  assert (s = trfirst mtr) as ->.
  { eapply evenodd_mdl_noprogress_Odd in Hschedne; [|done..].
    rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. }
  eapply mtrace_valid_after in Hvalid; [|done].
  pinversion Hvalid; simplify_eq. inversion H1; simplify_eq.
  - exists (m + 1).
    rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl.
    destruct mtr'; simpl in *; simplify_eq; done.
  - by apply odd_not_even in Hodd.
Qed.

Theorem evenodd_mdl_progresses (mtr : evenodd_mtrace) :
  infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = 0 →
  evenodd_mdl_progress mtr.
Proof.
  intros Hinf Hvalid Hfair Hfirst i.
  induction i as [|i IHi].
  { exists 0. rewrite /pred_at. rewrite /trfirst in Hfirst. simpl.
    destruct mtr; done. }
  destruct IHi as [n Hpred].
  rewrite /pred_at in Hpred.
  destruct (after n mtr) as [mtr'|] eqn:Hafter; [|done].
  eapply infinite_trace_after'' in Hinf; [|done].
  eapply mtrace_valid_after in Hvalid; [|done].
  destruct (Nat.even i) eqn:Heqn.
  - assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ mtr') as Hfair'.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst mtr' = i) as Hfirst'.
    { rewrite /trfirst. destruct mtr'; done. }
    pose proof (evenodd_mdl_progresses_Even i mtr' Hinf Hvalid Hfair' Hfirst')
      as [m Hpred']; [by eauto|].
    exists (n + m).
    rewrite pred_at_sum. rewrite Hafter. done.
  - assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ mtr') as Hfair'.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst mtr' = i) as Hfirst'.
    { rewrite /trfirst. destruct mtr'; done. }
    pose proof (evenodd_mdl_progresses_Odd i mtr' Hinf Hvalid Hfair' Hfirst')
      as [m Hpred']; [by rewrite -Nat.negb_even Heqn|].
    exists (n + m).
    rewrite pred_at_sum. rewrite Hafter. done.
Qed.

Theorem evenodd_mdl_is_mono (mtr : evenodd_mtrace) :
  infinite_trace mtr → mtrace_valid mtr → (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = 0 →
  evenodd_mdl_mono mtr.
Proof.
  intros Hinf Hvalid Hfair Hfirst n.
  pose proof (Hinf n) as [mtr' Hafter].
  destruct mtr' as [|s l mtr'].
  { pose proof (Hinf (S n)) as [mtr'' Hafter'].
    replace (S n) with (n + 1) in Hafter' by lia.
    rewrite after_sum' in Hafter'. rewrite Hafter in Hafter'. done. }
  exists s.
  rewrite /pred_at. rewrite Hafter.
  split; [done|].
  replace (S n) with (n + 1) by lia.
  rewrite after_sum'. rewrite Hafter. simpl.
  eapply mtrace_valid_after in Hvalid; [|done].
  punfold Hvalid. inversion Hvalid as [|??? Htrans]. simplify_eq.
  inversion Htrans; simplify_eq.
  - destruct mtr'.
    + exists (S s); split; [done|lia].
    + exists (S s); split; [done|lia].
  - destruct mtr'.
    + exists s; done.
    + exists s; done.
  - destruct mtr'.
    + exists (S s); split; [done|lia].
    + exists (S s); split; [done|lia].
  - destruct mtr'.
    + exists s; done.
    + exists s; done.
Qed.

(** Proof that fair progress is preserved through auxiliary trace *)

Definition evenodd_aux_progress (auxtr : auxtrace the_model) :=
  ∀ i, ∃ n, pred_at auxtr n (λ s l, (λ s' _, s' = i) (ls_under s) (l ≫= Ul)).

Lemma evenodd_mtr_aux_progress_preserved
      (mtr : mtrace the_fair_model)
      (auxtr : auxtrace the_model) :
  upto_stutter ls_under Ul auxtr mtr →
  evenodd_mdl_progress mtr → evenodd_aux_progress auxtr.
Proof.
  intros Hstutter Hmtr n. specialize (Hmtr n).
  by apply (trace_eventually_stutter_preserves
              ls_under Ul auxtr mtr (λ s' _, s' = n)).
Qed.

Definition evenodd_aux_mono (auxtr : auxtrace the_model) :=
  ∀ n, ∃ i, pred_at auxtr n (λ s l, (λ s' _, s' = i) (ls_under s) (l ≫= Ul)) ∧
            pred_at auxtr (S n) (λ s l, (λ s' _, ∃ j, s' = j ∧ i ≤ j) (ls_under s) (l ≫= Ul)).

Lemma evenodd_mtr_aux_mono_preserved (mtr : mtrace the_fair_model)
      (auxtr : auxtrace the_model) :
  upto_stutter ls_under Ul auxtr mtr →
  evenodd_mdl_mono mtr → evenodd_aux_mono auxtr.
Proof.
  intros Hstutter Hmtr n.
  revert auxtr mtr Hstutter Hmtr.
  induction n as [|n IHn]; intros auxtr mtr Hstutter Hmtr.
  { punfold Hstutter; [|apply upto_stutter_mono].
    induction Hstutter as
      [|auxtr mtr s ℓ Hℓ Hauxtr_first Hmtr_first CIHstutter IHstutter|
      auxtr mtr s ℓ δ ρ Hs Hℓ CIHstutter].
    - by destruct (Hmtr 0) as [? [? Hmtr']].
    - simplify_eq.
      destruct (IHstutter Hmtr) as [i [Hpred ?]].
      rewrite /pred_at in Hpred. simpl in *.
      exists i. rewrite /pred_at. simpl.
      destruct auxtr as [|s' ℓ' auxtr']; [done|].
      rewrite /trfirst in Hauxtr_first. split; [by simplify_eq|].
      exists i. simplify_eq. lia.
    - simplify_eq.
      destruct (Hmtr 0) as [i [Hpred1 Hpred2]].
      rewrite /pred_at in Hpred1. simpl in *.
      exists i.
      rewrite /pred_at. split; [done|].
      rewrite /pred_at in Hpred2. simpl in *.
      destruct CIHstutter as [CIHstutter|?]; [|done].
      punfold CIHstutter; [|apply upto_stutter_mono].
      induction CIHstutter as
        [|mtr auxtr ??? Hauxtr_first Hmtr_first ? IHstutter|];
        [done| |by simplify_eq].
      specialize (IHstutter Hmtr Hpred2).
      destruct mtr.
      * destruct IHstutter as [j [Hj1 Hj2]]. exists j. by simplify_eq.
      * destruct IHstutter as [j [Hj1 Hj2]]. exists j. by simplify_eq. }
  punfold Hstutter; [|apply upto_stutter_mono].
  induction Hstutter as
    [|auxtr mtr s ℓ Hℓ Hauxtr_first Hmtr_first CIHstutter IHstutter|
      auxtr mtr s ℓ δ ρ Hs Hℓ CIHstutter].
  + by destruct (Hmtr 0) as [? [? Hmtr']].
  + simplify_eq. setoid_rewrite pred_at_S. eapply IHn; [by apply paco2_fold|done].
  + simplify_eq. destruct CIHstutter as [CIHstutter|?]; [|done].
    assert (evenodd_mdl_mono mtr) as Hmtr'.
    { intros m. specialize (Hmtr (S m)). by setoid_rewrite pred_at_S in Hmtr. }
    destruct (IHn auxtr mtr CIHstutter Hmtr') as [i [Hpred1 Hpred2]].
    exists i. by rewrite !pred_at_S.
Qed.

(** Proof that progress is preserved between auxilary and execution trace,
 for a specific ξ *)

Definition evenodd_ex_progress (l:loc) (extr : heap_lang_extrace) :=
  ∀ (i:nat), ∃ n, pred_at extr n (λ s _, heap s.2 !! l = Some #i).

Definition evenodd_ex_mono (l:loc) (extr : heap_lang_extrace) :=
  ∀ n, ∃ (i:nat),
    pred_at extr n (λ s _, heap s.2 !! l = Some #i) ∧
    pred_at extr (S n) (λ s _, ∃ (j:nat), heap s.2 !! l = Some #j ∧ i ≤ j).

Definition ξ_evenodd_model_match (l : loc) (c : cfg heap_lang) (δ : the_fair_model) :=
  ∃ (N:nat), heap c.2 !! l = Some #N ∧ δ = N.

Definition ξ_evenodd_no_val_steps (c : cfg heap_lang) :=
  (Forall (λ e, is_Some $ to_val e) c.1 → False) ∧
  Forall (λ e, not_stuck e c.2) c.1.

Definition ξ_evenodd (l : loc) (c : cfg heap_lang) (δ : the_fair_model) :=
  ξ_evenodd_no_val_steps c ∧ ξ_evenodd_model_match l c δ.

Definition ξ_evenodd_trace (l : loc) (extr : execution_trace heap_lang)
           (auxtr : finite_trace the_fair_model (option EO)) :=
  ξ_evenodd l (trace_last extr) (trace_last auxtr).

(* TODO: This could be simplified to use [ξ_evenodd_model_match] *)
Lemma evenodd_aux_ex_progress_preserved l (extr : heap_lang_extrace) (auxtr : auxtrace the_model) :
  traces_match labels_match (λ c (δ:the_model), ξ_evenodd l c δ) locale_step
  (lm_ls_trans the_model) extr auxtr →
  evenodd_aux_progress auxtr → evenodd_ex_progress l extr.
Proof.
  intros Hξ Hauxtr n. specialize (Hauxtr n).
  rewrite /pred_at in Hauxtr. destruct Hauxtr as [m Hauxtr].
  destruct (after m auxtr) as [auxtr'|] eqn:Heqn; [|done].
  eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
  exists m. rewrite /pred_at. rewrite Hafter'.
  inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
  - destruct Hξ as (?&n&?&?). by simplify_eq.
  - destruct Hξ as (?&n&?&?). by simplify_eq.
Qed.

Lemma evenodd_aux_ex_mono_preserved l (extr : heap_lang_extrace) (auxtr : auxtrace the_model) :
  traces_match labels_match (λ c (δ:the_model), ξ_evenodd l c δ) locale_step
  (lm_ls_trans the_model) extr auxtr →
  evenodd_aux_mono auxtr → evenodd_ex_mono l extr.
Proof.
  intros Hξ Hauxtr n. specialize (Hauxtr n).
  destruct Hauxtr as [i Hauxtr].
  exists i.
  split.
  - destruct Hauxtr as [Hauxtr _].
    rewrite /pred_at in Hauxtr.
    destruct (after n auxtr) as [auxtr'|] eqn:Heqn; [|done].
    eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
    rewrite /pred_at. rewrite Hafter'.
    inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
    + destruct Hξ as (?&i&?&?). by simplify_eq.
    + destruct Hξ as (?&i&?&?). by simplify_eq.
  - destruct Hauxtr as [_ Hauxtr].
    rewrite /pred_at in Hauxtr.
    destruct (after (S n) auxtr) as [auxtr'|] eqn:Heqn; [|done].
    eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
    rewrite /pred_at. rewrite Hafter'.
    inversion Hextr' as [?? Hξ|??????? Hξ]; simplify_eq.
    + destruct Hauxtr as [j [<- Hle]].
      destruct Hξ as (?&j&?&?). exists j. by simplify_eq.
    + destruct Hauxtr as [j [<- Hle]].
      destruct Hξ as (?&j&?&?). exists j. by simplify_eq.
Qed.

Instance the_model_mstate_countable : EqDecision (mstate the_model).
Proof. intros x y. apply make_decision. Qed.
Instance the_model_mlabel_countable : EqDecision (mlabel the_model).
Proof. solve_decision. Qed.

(** Proof that program refines model up to ξ_evenodd *)

Lemma evenodd_sim l :
  continued_simulation
    (sim_rel_with_user the_model (ξ_evenodd_trace l))
    (trace_singleton ([start #l], {| heap := {[l:=#0]};  used_proph_id := ∅ |}))
    (trace_singleton (initial_ls (LM := the_model) 0 0)).
Proof.
  assert (evenoddPreG evenoddΣ) as HPreG'.
  { apply _. }
  assert (heapGpreS evenoddΣ the_model) as HPreG.
  { apply _. }
  eapply (strong_simulation_adequacy
            evenoddΣ _ NotStuck _ _ _ ∅); [|set_solver|].
  { eapply rel_finitary_sim_rel_with_user_sim_rel.
    eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl. apply (model_finitary s1). }
  iIntros (?) "!> [Hσ (Hs & Hr & Hf)]".
  iMod (own_alloc (●E 0  ⋅ ◯E 0))%nat as (γ_even_at) "[Heven_at_auth Heven_at]".
  { apply auth_both_valid_2; eauto. by compute. }
  iMod (own_alloc (●E 1  ⋅ ◯E 1))%nat as (γ_odd_at) "[Hodd_at_auth Hodd_at]".
  { apply auth_both_valid_2; eauto. by compute. }
  pose (the_names := {|
   even_name := γ_even_at;
   odd_name := γ_odd_at;
  |}).
  iAssert (|==> frag_free_roles_are ∅)%I as "-#FR".
  { rewrite /frag_free_roles_are. iApply own_unit. }
  iMod "FR" as "FR". 

  iMod (inv_alloc (nroot .@ "even_odd") _ (evenodd_inv_inner l) with "[Hσ Hs Hr Heven_at_auth Hodd_at_auth FR]") as "#Hinv".
  { iNext. unfold evenodd_inv_inner. iExists 0.
    replace (∅ ∖ live_roles the_fair_model 0) with
      (∅:gset (fmrole the_fair_model)) by set_solver.
    rewrite /eo_live_roles big_sepM_singleton. by iFrame. }
  iModIntro.
  iSplitL.
  { simpl. rewrite /eo_live_roles.
    replace (gset_to_gmap 61 {[ρOdd; ρEven]}) with
      ({[ρEven := 61; ρOdd := 61]} : gmap _ _); last first.
    { rewrite /gset_to_gmap. simpl.
      rewrite !map_fmap_union. rewrite !map_fmap_singleton.
      rewrite map_union_comm; last first.
      { rewrite map_disjoint_singleton_l.
        by rewrite lookup_insert_ne. }
      by rewrite -!insert_union_l left_id. }
    iApply (start_spec with "[$Hf $Heven_at $Hodd_at $Hinv]"); [lia|].
    by iIntros "!>?". }
  iIntros (extr auxtr c) "_ _ _ %Hends _ %Hnstuck [_ [Hσ Hδ]] Hposts".
  iInv "Hinv" as (M) "(>HFR & >Hmod & >Hn & _)" "Hclose".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (gen_heap_valid with "Hσ Hn") as %Hn.
  iDestruct (model_state_interp_tids_smaller with "Hδ") as %Hsmaller.
  iDestruct "Hδ" as (Mζ ?) "(Hf&HM&HFR_auth&%Hinverse&%Hlocales&Hδ&%Hdom)".
  iDestruct (model_agree with "Hδ Hmod") as %Hn'.
  iSplitL; last first.
  { iPureIntro. exists M. split; [done|]. rewrite -Hn'. by destruct auxtr. }
  rewrite /trace_ends_in in Hends.
  rewrite Hends.
  iSplit.
  - iIntros "%Hall".
    rewrite !big_sepL_omap !big_sepL_zip_with=> /=.
    iAssert ([∗ list] k↦x ∈ c.1, k ↦M ∅)%I with "[Hposts]" as "Hposts".
    { destruct c as [es σ]=> /=.
      iApply (big_sepL_impl with "Hposts").
      iIntros "!>" (k x HSome) "Hk".
      assert (is_Some (to_val x)) as [v Hv].
      { by eapply (Forall_lookup_1 (λ e : expr, is_Some (to_val e))). }
      rewrite Hv. destruct k; [done|]. destruct es; [done|].
      simpl in *. rewrite drop_0. rewrite list_lookup_fmap.
      erewrite prefixes_from_lookup; [|done].
      simpl. rewrite /locale_of. rewrite take_length.
      assert (k < length es).
      { apply lookup_lt_is_Some_1. by eauto. }
      by replace (k `min` length es) with k by lia. }
    iAssert (⌜∀ i, i < length c.1 → Mζ !! i = Some ∅⌝)%I as "%HMζ".
    { iIntros (i Hlen).
      assert (is_Some $ c.1 !! i) as [e HSome].
      { by apply lookup_lt_is_Some_2. }
      iDestruct (big_sepL_delete with "Hposts") as "[Hpost _]"; [done|].
      by iDestruct (frag_mapping_same with "HM Hpost") as "?". }
    assert (dom Mζ = list_to_set $ locales_of_list c.1).
    { rewrite Hends in Hlocales. apply set_eq.
      intros x. rewrite elem_of_dom.
      rewrite elem_of_list_to_set.
      split.
      - intros HSome.
        destruct (decide (x ∈ locales_of_list c.1)) as [|Hnin]; [done|].
        apply Hlocales in Hnin.
        destruct HSome as [??]. simplify_eq.
      - intros Hin. exists ∅. apply HMζ.
        rewrite locales_of_list_indexes in Hin.
        rewrite /indexes in Hin.
        apply elem_of_lookup_imap_1 in Hin as (i&?&->&HSome).
        by apply lookup_lt_is_Some_1. }
    assert (ls_mapping (trace_last auxtr) = ∅) as Hmapping.
    { apply map_eq. intros i. rewrite lookup_empty.
      destruct (ls_mapping (trace_last auxtr) !! i) as [ζ|] eqn:Heqn; [|done].
      pose proof Heqn as [e He]%Hsmaller.
      assert (Mζ !! ζ = Some ∅) as Hζ.
      { apply HMζ.
        apply from_locale_lookup in He.
        rewrite Hends in He.
        by apply lookup_lt_is_Some_1. }
      eapply (no_locale_empty _ _ i) in Hζ; [|done].
      by simplify_eq. }
    assert (live_roles _ M = ∅) as Hlive.
    { cut (live_roles the_fair_model M ⊆ ∅); [by set_solver|].
      etrans.
      - eapply (ls_mapping_dom (M:=the_fair_model)).
      - erewrite Hmapping. done. }
    rewrite /live_roles in Hlive. simpl in *.
    rewrite /eo_live_roles in Hlive. set_solver.
  - iPureIntro.
    apply Forall_forall.
    intros e He. by apply Hnstuck.
Qed.

CoInductive extrace_maximal {Λ} : extrace Λ → Prop :=
| extrace_maximal_singleton c :
  (∀ oζ c', ¬ locale_step c oζ c') → extrace_maximal ⟨c⟩
| extrace_maximal_cons c oζ tr :
  locale_step c oζ (trfirst tr) ->
  extrace_maximal tr →
  extrace_maximal (c -[oζ]-> tr).

Lemma extrace_maximal_valid {Λ} (extr : extrace Λ) :
  extrace_maximal extr → extrace_valid extr.
Proof.
  revert extr. cofix IH. intros extr Hmaximal. inversion Hmaximal.
  - constructor 1.
  - constructor 2; [done|by apply IH].
Qed.

Lemma extrace_maximal_after {Λ} n (extr extr' : extrace Λ) :
  extrace_maximal extr → after n extr = Some extr' → extrace_maximal extr'.
Proof.
  revert extr extr'. induction n; intros extr extr' Hafter Hvalid.
  { destruct extr'; simpl in *; by simplify_eq. }
  simpl in *. destruct extr; [done|]. eapply IHn; [|done]. by inversion Hafter.
Qed.

Lemma infinite_trace_no_val_steps extr auxtr :
  extrace_maximal extr →
  traces_match
    (labels_match (LM:=the_model))
    (λ c _ , ξ_evenodd_no_val_steps c) locale_step
    (lm_ls_trans the_model) extr auxtr →
  infinite_trace extr.
Proof.
  intros Hmaximal Hmatch.
  intros n. induction n as [|n IHn]; [done|].
  destruct IHn as [extr' Hafter].
  apply traces_match_flip in Hmatch.
  eapply traces_match_after in Hmatch; [|done].
  destruct Hmatch as [auxtr' [Hafter' Hmatch]].
  replace (S n) with (n + 1) by lia.
  rewrite after_sum'.
  rewrite Hafter.
  apply traces_match_first in Hmatch.
  destruct Hmatch as [Hξ1 Hξ2].
  eapply extrace_maximal_after in Hmaximal; [|done].
  inversion Hmaximal as [? Hnstep|]; simplify_eq; [|done].
  assert (∃ oζ c', locale_step c oζ c') as Hstep; last first.
  { exfalso. destruct Hstep as (?&?&Hstep). by eapply Hnstep. }
  apply not_Forall_Exists in Hξ1; [|apply _].
  apply Exists_exists in Hξ1 as [e [Hξ11 Hξ12]].
  rewrite Forall_forall in Hξ2.
  specialize (Hξ2 e Hξ11) as [|Hred]; [done|].
  destruct Hred as (e' & σ' & es' & Hred).
  apply elem_of_list_split in Hξ11 as (es1&es2&Hes).
  destruct c; simpl in *.
  eexists (Some _), _.
  econstructor; eauto. simpl in *.
  by f_equiv.
Qed.

(** Proof that the execution trace satisfies the liveness properties *)
Theorem evenodd_ex_liveness (l:loc) (extr : heap_lang_extrace) :
  extrace_maximal extr →
  (∀ tid, fair_ex tid extr) →
  trfirst extr = ([start #l], {| heap := {[l:=#0]}; used_proph_id := ∅ |}) →
  evenodd_ex_progress l extr ∧ evenodd_ex_mono l extr.
Proof.
  intros Hmaximal Hfair Hfirst.
  pose proof Hmaximal as Hvalid%extrace_maximal_valid.
  pose proof (evenodd_sim l) as Hsim.
  assert (∃ iatr,
             valid_inf_system_trace
               (continued_simulation (sim_rel_with_user the_model (ξ_evenodd_trace l)))
               (trace_singleton (trfirst extr))
               (trace_singleton (initial_ls (LM:=the_model) 0 0))
               (from_trace extr)
               iatr) as [iatr Hiatr].
  { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
    Unshelve.
    - rewrite Hfirst. done.
    - eapply from_trace_preserves_validity; eauto; first econstructor. }
  assert (∃ (auxtr : auxtrace the_model),
             traces_match labels_match
               (live_tids /2\ (ξ_evenodd l))
               locale_step
               the_model.(lm_ls_trans) extr auxtr) as [auxtr Hmatch_strong].
  { exists (to_trace (initial_ls (LM := the_model) 0 0 ) iatr).
    eapply (valid_inf_system_trace_implies_traces_match_strong
              (continued_simulation (sim_rel_with_user the_model (ξ_evenodd_trace l)))); eauto.
    - intros ? ? Hξ%continued_simulation_rel. by destruct Hξ as [[_ Hξ] _].
    - intros ? ? Hξ%continued_simulation_rel. by destruct Hξ as [[Hξ _] _].
    - intros extr' auxtr' Hξ%continued_simulation_rel.
      destruct Hξ as [_ [Hξ1 Hξ2]].
      split; [done|].
      destruct Hξ2 as [n [Hξ21 Hξ22]].
      exists n. split; [done|]. by destruct auxtr'.
    - by apply from_trace_spec.
    - by apply to_trace_spec. }
  assert (exaux_traces_match extr auxtr) as Hmatch.
  { eapply traces_match_impl; [done| |done]. by intros ??[??]. }
  assert (auxtrace_valid auxtr) as Hstutter.
  { by eapply exaux_preserves_validity. }
  apply can_destutter_auxtr in Hstutter.
  destruct Hstutter as [mtr Hupto].
  assert (infinite_trace extr) as Hinf.
  { eapply infinite_trace_no_val_steps; [done|].
    eapply traces_match_impl; [done| |apply Hmatch_strong].
    by intros s1 s2 [_ [? _]]. }
  pose proof (fairness_preserved extr auxtr Hinf Hmatch Hfair) as Hfairaux.
  have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  pose proof (fairness_preserved extr auxtr Hinf Hmatch Hfair) as Hfair'.
  pose proof (upto_stutter_fairness auxtr mtr Hupto Hfair') as Hfair''.
  assert (infinite_trace mtr) as Hinf''.
  { eapply upto_stutter_infinite_trace; [done|].
    by eapply traces_match_infinite_trace. }
  assert (mtrace_valid mtr) as Hvalid''.
  { eapply upto_preserves_validity; [done|].
    by eapply exaux_preserves_validity. }
  assert (trfirst mtr = 0) as Hfirst''.
  { apply traces_match_first in Hmatch_strong.
    destruct Hmatch_strong as [_ [_ [n [Hσ Hmdl]]]].
    rewrite Hfirst in Hσ. simpl in *. rewrite lookup_insert in Hσ.
    simplify_eq. punfold Hupto; [|by apply upto_stutter_mono'].
    assert (0 = ls_under (trfirst auxtr)) as Hσ' by lia.
    inversion Hupto; simplify_eq;
    by rewrite Hσ'. }
  split.
  - pose proof (evenodd_mdl_progresses mtr Hinf'' Hvalid'' Hfair'' Hfirst'')
      as Hprogress.
    eapply (evenodd_aux_ex_progress_preserved l _ auxtr).
    { eapply traces_match_impl; [done| |apply Hmatch_strong]. by intros ??[??]. } 
    by eapply evenodd_mtr_aux_progress_preserved.
  - pose proof (evenodd_mdl_is_mono mtr Hinf'' Hvalid'' Hfair'' Hfirst'')
      as Hmono.
    eapply (evenodd_aux_ex_mono_preserved l _ auxtr).
    { eapply traces_match_impl; [done| |apply Hmatch_strong]. by intros ??[??]. }     by eapply evenodd_mtr_aux_mono_preserved.
Qed.
