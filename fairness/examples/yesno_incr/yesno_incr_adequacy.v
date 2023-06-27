From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness Require Import trace_utils.
From trillium.fairness.examples.yesno_incr Require Import yesno_incr3.

From stdpp Require Import finite.


(* The model is finitely branching *)
Definition steppable n : list (nat * option YN) :=
  n' ← [S n; n];
  ℓ ← [Some Y; Some No];
  mret (n', ℓ).

#[local] Instance proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in yntrans s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma model_finitary s:
  Finite { '(s', ℓ) | yntrans s ℓ s'}.
Proof.
  assert (H: forall A (y x: A) xs, (y = x ∨ y ∈ xs) -> y ∈ x::xs) by set_solver.
  eapply (in_list_finite (steppable s)).
  intros [n w] Htrans.
  inversion Htrans; try (repeat (rewrite ?Nat.sub_0_r; simpl;
    eapply H; try (by left); right); done).
Qed.

Definition yesno_mtrace : Type := mtrace the_fair_model.

Definition yesno_mdl_progress (tr : yesno_mtrace) :=
  ∀ n, ∃ m, pred_at tr m (λ s _, s = n).

Lemma yesno_mdl_alwayslive ρ n (mtr : yesno_mtrace) :
  infinite_trace mtr →
  pred_at mtr n
          (λ (δ : the_fair_model) (_ : option (option (fmrole the_fair_model))),
             role_enabled_model ρ δ).
Proof.
  intros Hinf.
  specialize (Hinf n) as [mtr' Hafter].
  rewrite /pred_at. rewrite Hafter.
  rewrite /role_enabled_model.
  destruct mtr'; destruct ρ; set_solver.
Qed.

Lemma yesno_mdl_scheduled ρ (mtr : yesno_mtrace) :
  infinite_trace mtr →
  fair_model_trace ρ mtr →
  ∀ n, ∃ m, pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)).
Proof.
  intros Hinf Hfair n.
  apply (yesno_mdl_alwayslive ρ n mtr) in Hinf.
  specialize (Hfair n Hinf) as [m [Hfair | Hfair]].
  - rewrite /pred_at in Hfair.
    destruct (after (n + m) mtr); [|done].
    rewrite /role_enabled_model in Hfair. destruct t; destruct ρ; set_solver.
  - by exists m.
Qed.

(* Lemma yesno_mdl_scheduled ρ (mtr : yesno_mtrace) : *)
(*   (* (∀ ρ, fair_model_trace ρ mtr) → *) *)
(*   ∀ n, ∃ m, pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)). *)
(* Proof. *)


From Paco Require Import paco1 paco2 pacotac.

(* TODO: move to fairness.v *)
Lemma mtrace_valid_after `{M : FairModel} (mtr mtr' : mtrace M) k :
  after k mtr = Some mtr' → mtrace_valid mtr → mtrace_valid mtr'.
Proof.
  revert mtr mtr'.
  induction k; intros mtr mtr' Hafter Hvalid.
  { destruct mtr'; simpl in *; by simplify_eq. }
  punfold Hvalid.
  inversion Hvalid as [|??? Htrans Hval']; simplify_eq.
  eapply IHk; [done|].
  by inversion Hval'.
Qed.

Lemma even_odd_False n : Nat.even n → Nat.odd n → False.
Proof.
  intros Heven Hodd. rewrite -Nat.negb_odd in Heven.
  apply Is_true_true_1 in Heven.
  apply Is_true_true_1 in Hodd.
  rewrite Hodd in Heven.
  done.
Qed.

Lemma even_not_odd n : Nat.even n → ¬ Nat.odd n.
Proof. intros Heven Hodd. by eapply even_odd_False. Qed.

Lemma odd_not_even n : Nat.odd n → ¬ Nat.even n.
Proof. intros Heven Hodd. by eapply even_odd_False. Qed.

Lemma yesno_mdl_noprogress_Y n m (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (trfirst mtr) = n →
  Nat.even n →
  (∀ m0 : nat,
     m0 < m → pred_at mtr m0
             (λ _ l, l ≠ Some (Some Y))) →
  pred_at mtr m (λ s _, s = n).
Proof.
  intros Hinf Hvalid Hfirst Heven Hne.
  induction m.
  { rewrite /pred_at. destruct mtr; done. }
  simpl in *.
  assert (∀ m0 : nat,
          m0 < m
          → pred_at mtr m0
              (λ _ l, l ≠ Some (Some Y)))
    as Hne'.
  { intros. apply Hne. lia. }
  specialize (IHm Hne').
  rewrite /pred_at in IHm.
  destruct (after m mtr) eqn:Hafter; rewrite Hafter in IHm; [|done].
  rewrite /pred_at. replace (S m) with (m + 1) by lia.
  rewrite after_sum'. rewrite Hafter. simpl.
  specialize (Hinf (m+1)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf.
  destruct t; [by apply is_Some_None in Hinf|].
  eapply mtrace_valid_after in Hvalid; [|done].
  assert (ℓ ≠ Some Y) as Hneq.
  { assert (m < S m) by lia. specialize (Hne m H). rewrite /pred_at in Hne.
    rewrite Hafter in Hne. intros ->. apply Hne. done. }
  pinversion Hvalid. simplify_eq. inversion H1; simplify_eq.
  - by apply even_not_odd in Heven.
  - by destruct t.
Qed.

(* Trivial *)
Lemma yesno_mdl_noprogress_No n m (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (trfirst mtr) = n →
  Nat.odd n →
  (∀ m0 : nat,
     m0 < m → pred_at mtr m0
             (λ _ (l : option (option YN)),
                l ≠ Some (Some No))) →
  pred_at mtr m (λ s _, s = n).
Proof.
  intros Hinf Hvalid Hfirst Hodd Hne.
  induction m.
  { rewrite /pred_at. destruct mtr; done. }
  simpl in *.
  assert (∀ m0 : nat,
          m0 < m
          → pred_at mtr m0
              (λ _ l, l ≠ Some (Some No)))
    as Hne'.
  { intros. apply Hne. lia. }
  specialize (IHm Hne').
  rewrite /pred_at in IHm.
  destruct (after m mtr) eqn:Hafter; rewrite Hafter in IHm; [|done].
  rewrite /pred_at. replace (S m) with (m + 1) by lia.
  rewrite after_sum'. rewrite Hafter. simpl.
  specialize (Hinf (m+1)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf.
  destruct t; [by apply is_Some_None in Hinf|].
  eapply mtrace_valid_after in Hvalid; [|done].
  assert (ℓ ≠ Some No) as Hneq.
  { assert (m < S m) by lia. specialize (Hne m H). rewrite /pred_at in Hne.
    rewrite Hafter in Hne. intros ->. apply Hne. done. }
  pinversion Hvalid. simplify_eq. inversion H1; simplify_eq.
  - by apply odd_not_even in Hodd.
  - by destruct t.
Qed.

Theorem yesno_mdl_progresses_Y n (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = n →
  Nat.even n →
  ∃ m, pred_at mtr m (λ s _, s = S n).
Proof.
  intros Hinf Hvalid Hfair Hfirst Heven.
  specialize (Hfair Y).
  pose proof (yesno_mdl_scheduled Y mtr Hinf Hfair 0) as Hsched.
  simpl in *.
  apply trace_eventually_until in Hsched as [m [Hsched Hschedne]].
  rewrite /pred_at in Hsched.
  destruct (after m mtr) eqn:Hafter; last first.
  { rewrite Hafter in Hsched. done. }
  rewrite Hafter in Hsched.
  destruct t; [done|].
  simplify_eq.
  assert (s = trfirst mtr) as ->.
  { eapply yesno_mdl_noprogress_Y in Hschedne; [|done..].
    rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. }
  eapply mtrace_valid_after in Hvalid; [|done].
  pinversion Hvalid; simplify_eq. inversion H1; simplify_eq.
  - exists (m + 1).
    rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl.
    destruct t; simpl in *; simplify_eq; done.
  - by apply even_not_odd in Heven.
Qed.

Theorem yesno_mdl_progresses_No n (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = n →
  Nat.odd n →
  ∃ m, pred_at mtr m (λ s _, s = S n).
Proof.
  intros Hinf Hvalid Hfair Hfirst Hodd.
  specialize (Hfair No).
  pose proof (yesno_mdl_scheduled No mtr Hinf Hfair 0) as Hsched.
  simpl in *.
  apply trace_eventually_until in Hsched as [m [Hsched Hschedne]].
  rewrite /pred_at in Hsched.
  destruct (after m mtr) eqn:Hafter; last first.
  { rewrite Hafter in Hsched. done. }
  rewrite Hafter in Hsched.
  destruct t; [done|].
  simplify_eq.
  assert (s = trfirst mtr) as ->.
  { eapply yesno_mdl_noprogress_No in Hschedne; [|done..].
    rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. }
  eapply mtrace_valid_after in Hvalid; [|done].
  pinversion Hvalid; simplify_eq. inversion H1; simplify_eq.
  - exists (m + 1).
    rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl.
    destruct t; simpl in *; simplify_eq; done.
  - by apply odd_not_even in Hodd.
Qed.

Lemma infinite_trace_after'' {S T} n (tr tr' : trace S T) :
  after n tr = Some tr' → infinite_trace tr → infinite_trace tr'.
Proof.
  intros Hafter Hinf m. specialize (Hinf (n+m)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf. done.
Qed.

Theorem yesno_mdl_progresses (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = 0 →
  yesno_mdl_progress mtr.
Proof.
  intros Hinf Hvalid Hfair Hfirst n.
  induction n as [|n IHn].
  { exists 0. rewrite /pred_at. rewrite /trfirst in Hfirst. simpl.
    destruct mtr; done. }
  destruct IHn as [m Hpred].
  rewrite /pred_at in Hpred.
  destruct (after m mtr) eqn:Hafter; [|done].
  eapply infinite_trace_after'' in Hinf; [|done].
  eapply mtrace_valid_after in Hvalid; [|done].
  destruct (Nat.even n) eqn:Heqn.
  - assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ t) as Hfair'.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst t = n) as Hfirst'.
    { rewrite /trfirst. destruct t; done. }
    pose proof (yesno_mdl_progresses_Y n t Hinf Hvalid Hfair' Hfirst')
      as [m' Hpred']; [by eauto|].
    exists (m + m').
    rewrite pred_at_sum. rewrite Hafter. done.
  - assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ t) as Hfair'.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst t = n) as Hfirst'.
    { rewrite /trfirst. destruct t; done. }
    pose proof (yesno_mdl_progresses_No n t Hinf Hvalid Hfair' Hfirst')
      as [m' Hpred']; [by rewrite -Nat.negb_even Heqn|].
    exists (m + m').
    rewrite pred_at_sum. rewrite Hafter. done.
Qed.

Lemma trace_eventually_cons {S T} s l (tr : trace S T) P :
  trace_eventually tr P → trace_eventually (s -[l]-> tr) P.
Proof. intros [n HP]. by exists (Datatypes.S n). Qed.

(* Definition yesno_aux_progress n b (auxtr : auxtrace the_model) := *)
(*   trace_eventually auxtr (ls_under ∘ (λ s _, s = (n,b))). *)
Lemma trace_eventually_stutter_preserves `(LM : LiveModel Λ FM)
      (mtr : mtrace FM)
      (auxtr : auxtrace LM) P :
  upto_stutter ls_under Ul auxtr mtr →
  trace_eventually mtr P →
  trace_eventually auxtr (λ s l, P (ls_under s) (l ≫= Ul)).
Proof.
  intros Hstutter [n Heventually].
  revert mtr auxtr Hstutter Heventually.
  induction n as [|n IHn]; intros mtr auxtr Hstutter Heventually.
  - punfold Hstutter; [|apply upto_stutter_mono].
    induction Hstutter.
    + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl in *. done.
    + destruct (IHHstutter Heventually) as [n Heventually'].
      exists (1 + n). rewrite /pred_at. rewrite after_sum'. simpl.
      done.
    + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl.
      simplify_eq. rewrite H0. done.
  - punfold Hstutter; [|apply upto_stutter_mono].
    induction Hstutter.
    + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl in *. done.
    + destruct (IHHstutter Heventually) as [n' Heventually'].
      exists (1 + n'). rewrite /pred_at. rewrite after_sum'. simpl.
      done.
    + apply trace_eventually_cons.
      assert (pred_at str n P) as Heventually'.
      { rewrite /pred_at in Heventually.
        simpl in *. done. }
      eapply IHn; [|done].
      rewrite /upaco2 in H1. destruct H1; [done|done].
Qed.

(* TODO: better definition *)
Definition yesno_aux_progress (auxtr : auxtrace the_model) :=
  ∀ n, ∃ m, pred_at auxtr m (λ s l, (λ s' _, s' = n) (ls_under s) (l ≫= Ul)).

Lemma yesno_mtr_aux_progress_preserved
      (mtr : mtrace the_fair_model)
      (auxtr : auxtrace the_model) :
  upto_stutter ls_under Ul auxtr mtr →
  yesno_mdl_progress mtr → yesno_aux_progress auxtr.
Proof.
  intros Hstutter Hmtr.
  intros n. apply (trace_eventually_stutter_preserves _ mtr auxtr (λ s' _, s' = n)).
  - done.
  - apply Hmtr.
Qed.

(* Defining this requires exposing the location in the state *)
(* Definition yesno_ex_progress (tr : heap_lang_extrace) := *)
(*   ∀ n b, ∃ m, pred_at tr m (λ s _, s.2 !! ??? = Some ???). *)
Definition yesno_ex_progress (l:loc) (tr : heap_lang_extrace) :=
  ∀ (n:nat), ∃ m, pred_at tr m (λ s _, heap s.2 !! l = Some #n).

Definition ξ_yesno' (l : loc) (extr : execution_trace heap_lang)
           (auxtr : finite_trace the_fair_model (option YN)) :=
  ∃ (N:nat), heap (trace_last extr).2 !! l = Some #N ∧ (trace_last auxtr) = N.

Definition ξ_yesno (l : loc) (extr : heap_lang_extrace) (auxtr : auxtrace the_model) :=
  ∀ n, ∃ (N:nat),
    pred_at extr n (λ σ _, heap σ.2 !! l = Some #N) ∧
    pred_at auxtr n (λ δ _, ls_under δ = N).

Lemma yesno_aux_ex_progress_preserved l (extr : heap_lang_extrace) (auxtr : auxtrace the_model) :
  ξ_yesno l extr auxtr → yesno_aux_progress auxtr → yesno_ex_progress l extr.
Proof.
  intros Hξ Hauxtr.
  intros n.
  specialize (Hauxtr n).
  destruct Hauxtr as [m Hauxtr].
  exists m.
  destruct (Hξ m) as [N [Hextr' Hauxtr']].
  rewrite /pred_at.
  rewrite /pred_at in Hauxtr.
  rewrite /pred_at in Hauxtr'.
  rewrite /pred_at in Hextr'.
  destruct (after m auxtr); [|done].
  destruct (after m extr); [|done].
  destruct t; destruct t0; by simplify_eq.
Qed.

(* TODO: move *)
Lemma traces_match_infinite_trace {L1 L2 S1 S2: Type}
      (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop)
      (trans2: S2 -> L2 -> S2 -> Prop) tr1 tr2 :
  traces_match Rℓ Rs trans1 trans2 tr1 tr2 → infinite_trace tr1 → infinite_trace tr2.
Proof.
  intros Hmatch Hinf n.
  specialize (Hinf n) as [tr' Hafter].
  apply traces_match_flip in Hmatch.
  by eapply traces_match_after in Hafter as [tr'' [Hafter' _]].
Qed.

Lemma upto_stutter_infinite_trace {St S' L L': Type} (Us: St -> S') (Ul: L -> option L')
 tr1 tr2 :
  upto_stutter Us Ul tr1 tr2 → infinite_trace tr1 → infinite_trace tr2.
Proof.
  intros Hstutter Hinf n.
  revert tr1 tr2 Hstutter Hinf.
  induction n as [|n IHn]; intros tr1 tr2 Hstutter Hinf.
  - punfold Hstutter. apply upto_stutter_mono.
  - punfold Hstutter; [|apply upto_stutter_mono].
    induction Hstutter.
    + specialize (Hinf (1 + n)).
      rewrite after_sum' in Hinf. simpl in *. apply is_Some_None in Hinf. done.
    + apply IHHstutter.
      intros m. specialize (Hinf (1 + m)).
      rewrite after_sum' in Hinf. simpl in *. done.
    + simpl. eapply (IHn btr str); [by destruct H1|].
      intros m. specialize (Hinf (1 + m)).
      rewrite after_sum' in Hinf. simpl in *. done.
Qed.

Lemma rel_finitary_sim_rel_with_user_sim_rel `{LM:LiveModel Λ Mdl}
      `{EqDecision (mstate LM)} `{EqDecision (mlabel LM)}
      `{Countable (locale Λ)} ξ :
  rel_finitary (sim_rel LM) → rel_finitary (sim_rel_with_user LM ξ).
Proof.
  intros Hrel. eapply rel_finitary_impl; [|done]. by intros ex aux [Hsim _].
Qed.

(* TODO *)
Instance the_model_mstate_countable : EqDecision (mstate the_model).
Proof. Admitted.

Instance the_model_mlabel_countable : EqDecision (mlabel the_model).
Proof. Admitted.

(** Derive that program is related to model by
    [sim_rel_with_user cn_model (ξ_cn l) using Trillium adequacy *)
Lemma yesno_incr_sim l :
  continued_simulation
    (sim_rel_with_user the_model (ξ_yesno' l))
    (trace_singleton ([start #l],
                        {| heap := {[l:=#0]};
                           used_proph_id := ∅ |}))
    (trace_singleton (initial_ls (LM := the_model) 0 0)).
Proof.
  assert (yesnoPreG yesnoΣ) as HPreG'.
  { apply _. }
  assert (heapGpreS yesnoΣ the_model) as HPreG.
  { apply _. }
  eapply (strong_simulation_adequacy
            yesnoΣ _ NotStuck _ _ _ ∅); [|set_solver|].
  { eapply rel_finitary_sim_rel_with_user_sim_rel.
    eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl. apply (model_finitary s1). }
  iIntros (?) "!> Hσ Hs Hr Hf".
  iMod (own_alloc (●E 0  ⋅ ◯E 0))%nat as (γ_yes_at) "[Hyes_at_auth Hyes_at]".
  { apply auth_both_valid_2; eauto. by compute. }
  iMod (own_alloc (●E 1  ⋅ ◯E 1))%nat as (γ_no_at) "[Hno_at_auth Hno_at]".
  { apply auth_both_valid_2; eauto. by compute. }
  pose (the_names := {|
   yes_name := γ_yes_at;
   no_name := γ_no_at;
  |}).
  iMod (inv_alloc (nroot .@ "yes_no") _ (yesno_inv_inner l) with "[Hσ Hs Hr Hyes_at_auth Hno_at_auth]") as "#Hinv".
  { iNext. unfold yesno_inv_inner. iExists 0.
    replace (∅ ∖ live_roles the_fair_model 0) with
      (∅:gset (fmrole the_fair_model)) by set_solver.
    simpl. rewrite /yn_live_roles.
    iFrame.
    rewrite big_sepM_singleton. iFrame. }
  iModIntro.
  iSplitL.
  { simpl. rewrite /yn_live_roles.
    replace (gset_to_gmap 61 {[No; Y]}) with
      ({[Y := 61; No := 61]} : gmap _ _); last first.
    { rewrite /gset_to_gmap. simpl.
      rewrite !map_fmap_union. rewrite !map_fmap_singleton.
      rewrite map_union_comm; last first.
      { rewrite map_disjoint_singleton_l.
        by rewrite lookup_insert_ne. }
      rewrite -!insert_union_l.
      rewrite left_id. done. }
    iApply (start_spec with "[$Hf $Hyes_at $Hno_at $Hinv]"); [lia|].
    by iIntros "!>?". }
  iIntros (extr auxtr c) "??????[?[Hσ Hδ]]".
  iInv "Hinv" as (M) "(>HFR & >Hmod & >Hn & Hauths)" "Hclose".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (gen_heap_valid with "Hσ Hn") as %Hn.
  iDestruct "Hδ" as (??) "(?&?&?&?&?&Hδ&?)".
  iDestruct (model_agree with "Hδ Hmod") as %Hn'.
  iPureIntro. exists M. split; [done|].
  rewrite -Hn'. by destruct auxtr.
Qed.

Theorem yesno_ex_progresses (l:loc) (extr : heap_lang_extrace) :
  extrace_valid extr →
  (∀ tid, fair_ex tid extr) →
  (trfirst extr).1 = [start #l] →
  yesno_ex_progress l extr.
Proof.
Admitted.
