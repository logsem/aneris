From Paco Require Import paco1 paco2 pacotac.
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

(* TODO: Move prerequisites *)

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

(** Proof that any fair execution of model guarantees progress *)
Definition yesno_mtrace : Type := mtrace the_fair_model.

Definition yesno_mdl_progress (tr : yesno_mtrace) :=
  ∀ n, ∃ m, pred_at tr m (λ s _, s = n).

Lemma yesno_mdl_always_live ρ n (mtr : yesno_mtrace) :
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

Lemma yesno_mdl_always_eventually_scheduled ρ (mtr : yesno_mtrace) :
  infinite_trace mtr →
  fair_model_trace ρ mtr →
  ∀ n, ∃ m, pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)).
Proof.
  intros Hinf Hfair n.
  apply (yesno_mdl_always_live ρ n mtr) in Hinf.
  specialize (Hfair n Hinf) as [m [Hfair | Hfair]].
  - rewrite /pred_at in Hfair.
    destruct (after (n + m) mtr); [|done].
    rewrite /role_enabled_model in Hfair. destruct t; destruct ρ; set_solver.
  - by exists m.
Qed.

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
  pose proof (yesno_mdl_always_eventually_scheduled Y mtr Hinf Hfair 0) as Hsched.
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
  pose proof (yesno_mdl_always_eventually_scheduled No mtr Hinf Hfair 0) as Hsched.
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

(** Proof that fair progress is preserved through auxiliary trace *)

(* TODO: Better definition *)
Definition yesno_aux_progress (auxtr : auxtrace the_model) :=
  ∀ n, ∃ m, pred_at auxtr m (λ s l, (λ s' _, s' = n) (ls_under s) (l ≫= Ul)).

Lemma yesno_mtr_aux_progress_preserved
      (mtr : mtrace the_fair_model)
      (auxtr : auxtrace the_model) :
  upto_stutter ls_under Ul auxtr mtr →
  yesno_mdl_progress mtr → yesno_aux_progress auxtr.
Proof.
  intros Hstutter Hmtr n. specialize (Hmtr n).
  by apply (trace_eventually_stutter_preserves
              ls_under Ul auxtr mtr (λ s' _, s' = n)).
Qed.

(** Proof that progress is preserved between auxilary and execution trace,
 for a specific ξ *)

Definition yesno_ex_progress (l:loc) (tr : heap_lang_extrace) :=
  ∀ (n:nat), ∃ m, pred_at tr m (λ s _, heap s.2 !! l = Some #n).

Definition ξ_yesno_model_match (l : loc) (c : cfg heap_lang) (δ : the_fair_model) :=
  ∃ (N:nat), heap c.2 !! l = Some #N ∧ δ = N.

Definition ξ_yesno_no_val_steps (c : cfg heap_lang) (δ : the_fair_model) :=
  (Forall (λ e, is_Some $ to_val e) c.1 → False) ∧
  Forall (λ e, not_stuck e c.2) c.1.

(* Definition ξ_yesno_steps (l : loc) (c : cfg heap_lang) (δ : the_fair_model) := *)
(*   Forall (λ e, is_Some $ to_val e) c.1 → False. *)

Definition ξ_yesno (l : loc) (c : cfg heap_lang) (δ : the_fair_model) :=
  ξ_yesno_no_val_steps c δ ∧ ξ_yesno_model_match l c δ.

Definition ξ_yesno_trace (l : loc) (extr : execution_trace heap_lang)
           (auxtr : finite_trace the_fair_model (option YN)) :=
  ξ_yesno l (trace_last extr) (trace_last auxtr).

Lemma yesno_aux_ex_progress_preserved l (extr : heap_lang_extrace) (auxtr : auxtrace the_model) :
  traces_match labels_match (λ c δ, live_tids c δ ∧ ξ_yesno l c δ) locale_step
  (lm_ls_trans the_model) extr auxtr →
  yesno_aux_progress auxtr → yesno_ex_progress l extr.
Proof.
  intros Hξ Hauxtr.
  intros n.
  specialize (Hauxtr n).
  rewrite /pred_at in Hauxtr.
  destruct Hauxtr as [m Hauxtr].
  destruct (after m auxtr) eqn:Heqn; [|done].
  eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
  exists m. rewrite /pred_at. rewrite Hafter'.
  inversion Hextr'; simplify_eq.
  - destruct H as [? [? [n [? ?]]]]. simplify_eq. done.
  - destruct H0 as [? [? [n [? ?]]]]. simplify_eq. done.
Qed.

Instance the_model_mstate_countable : EqDecision (mstate the_model).
Proof. intros x y. apply make_decision. Qed.
Instance the_model_mlabel_countable : EqDecision (mlabel the_model).
Proof. solve_decision. Qed.

(** Proof that program refines model up to ξ_yesno *)

Definition indexes {A} (xs : list A) :=
  imap (λ i _, i) xs.


Lemma locales_of_list_from_indexes (es' es : list expr) :
  locales_of_list_from es' es = imap (λ i _, length es' + i) es.
Proof. Admitted.

Lemma locales_of_list_indexes (es : list expr) :
  locales_of_list es = indexes es.
Proof. apply locales_of_list_from_indexes. Qed.

Lemma yesno_incr_sim l :
  continued_simulation
    (sim_rel_with_user the_model (ξ_yesno_trace l))
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
  iIntros (extr auxtr c) "_ _ _ %Hends _ %Hnstuck [_ [Hσ Hδ]] Hposts".
  iInv "Hinv" as (M) "(>HFR & >Hmod & >Hn & _)" "Hclose".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (gen_heap_valid with "Hσ Hn") as %Hn.
  iDestruct (model_state_interp_tids_smaller with "Hδ") as %Hsmaller.   iDestruct "Hδ" as (??) "(Hf&HM&HFR_auth&%Hinverse&%Hlocales&Hδ&%Hdom)".
  iDestruct (model_agree with "Hδ Hmod") as %Hn'.
  iSplitL; last first.
  { iPureIntro.
    exists M. split; [done|].
    rewrite -Hn'. by destruct auxtr. }
  rewrite /trace_ends_in in Hends.
  rewrite Hends.

  iSplit.
  - iIntros "%Hall".
    rewrite !big_sepL_omap.
    rewrite !big_sepL_zip_with.
    simpl.
    iAssert ([∗ list] k↦x ∈ c.1, k ↦M ∅)%I with "[Hposts]" as "Hposts".
    {
      destruct c as [es σ]=> /=.
      iApply (big_sepL_impl with "Hposts").
      iIntros "!>" (k x HSome) "Hk".
      simpl in *.
      assert (is_Some (to_val x)) as [v Hv].
      { by eapply (Forall_lookup_1 (λ e : expr, is_Some (to_val e))). }
      rewrite Hv.
      destruct k; [done|].
      simpl.
      destruct es; [done|].
      simpl in *.
      rewrite drop_0.
      rewrite list_lookup_fmap.
      erewrite prefixes_from_lookup; [|done].
      simpl.
      rewrite /locale_of.
      rewrite take_length.
      assert (k < length es).
      { apply lookup_lt_is_Some_1. by eauto. }
      replace (k `min` length es) with k by lia.
      done.
    }
    iAssert (⌜∀ i, i < length c.1 → M0 !! i = Some ∅⌝)%I as "%HM0".
    {
      iIntros (i Hlen).
      assert (is_Some $ c.1 !! i) as [e HSome].
      { by apply lookup_lt_is_Some_2. }
      iDestruct (big_sepL_delete with "Hposts") as "[Hpost _]"; [done|].
      by iDestruct (frag_mapping_same with "HM Hpost") as "H".
    }
    assert (dom M0 = list_to_set $ locales_of_list c.1).
    {
      rewrite Hends in Hlocales.
      apply set_eq.
      intros x. rewrite elem_of_dom.
      rewrite elem_of_list_to_set.
      split.
      - intros HSome.
        destruct (decide (x ∈ locales_of_list c.1))
          as [|Hnin]; [done|].
        apply Hlocales in Hnin.
        destruct HSome as [??]. simplify_eq.
      - intros Hin.
        exists ∅.
        apply HM0.
        rewrite locales_of_list_indexes in Hin.
        rewrite /indexes in Hin.
        apply elem_of_lookup_imap_1 in Hin as (i&?&->&HSome).
        by apply lookup_lt_is_Some_1.
    }
    assert (ls_mapping (trace_last auxtr) = ∅) as Hmapping.
    { apply map_eq.
      intros i.
      rewrite lookup_empty.
      destruct (ls_mapping (trace_last auxtr) !! i) as [ζ|]
        eqn:Heqn; [|done].
      pose proof Heqn as [e He]%Hsmaller.
      assert (M0 !! ζ = Some ∅) as Hζ.
      { apply HM0.
        apply from_locale_lookup in He.
        rewrite Hends in He.
        by apply lookup_lt_is_Some_1. }
      eapply (no_locale_empty _ _ i) in Hζ; [|done].
      by simplify_eq. }
    assert (live_roles _ M = ∅).
    { cut (live_roles the_fair_model M ⊆ ∅); [by set_solver|].
      etrans.
      - eapply (ls_mapping_dom (M:=the_fair_model)).
      - erewrite Hmapping. done. }
    rewrite /live_roles in H0. simpl in *.
    rewrite /yn_live_roles in H0. set_solver.
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
  revert extr. cofix IH.
  intros extr Hmaximal.
  inversion Hmaximal.
  - constructor 1.
  - constructor 2; [done|by apply IH].
Qed.

Lemma extrace_maximal_after {Λ} n (extr extr' : extrace Λ) :
  extrace_maximal extr → after n extr = Some extr' → extrace_maximal extr'.
Proof.
  revert extr extr'.
  induction n; intros extr extr' Hafter Hvalid.
  { destruct extr'; simpl in *; by simplify_eq. }
  simpl in *.
  destruct extr; [done|].
  eapply IHn; [|done].
  by inversion Hafter.
Qed.

(** Proof that execution trace actually progresses *)
Theorem yesno_ex_progresses (l:loc) (extr : heap_lang_extrace) :
  extrace_maximal extr →
  (∀ tid, fair_ex tid extr) →
  trfirst extr = ([start #l],
                        {| heap := {[l:=#0]};
                           used_proph_id := ∅ |}) →
  yesno_ex_progress l extr.
Proof.
  intros Hmaximal Hfair Hfirst.
  pose proof Hmaximal as Hvalid%extrace_maximal_valid.
  pose proof (yesno_incr_sim l) as Hsim.

  assert (∃ iatr,
             valid_inf_system_trace
               (continued_simulation (sim_rel_with_user the_model (ξ_yesno_trace l)))
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
               (live_tids /2\ (ξ_yesno l))
               locale_step
               the_model.(lm_ls_trans) extr auxtr) as [auxtr Hmatch_strong].
  { exists (to_trace (initial_ls (LM := the_model) 0 0 ) iatr).
    eapply (valid_inf_system_trace_implies_traces_match_strong
              (continued_simulation (sim_rel_with_user the_model (ξ_yesno_trace l)))); eauto.
    - intros ? ? ?%continued_simulation_rel. by destruct H as [[_ H] _].
    - intros ? ? ?%continued_simulation_rel. by destruct H as [[H _] _].
    - intros extr' auxtr' ?%continued_simulation_rel.
      destruct H as [_ [H1 H2]].
      split; [done|].
      destruct H2 as [n [H21 H22]].
      exists n. split; [done|]. by destruct auxtr'.
    - by apply from_trace_spec.
    - by apply to_trace_spec. }

  assert (exaux_traces_match extr auxtr) as Hmatch.
  { eapply traces_match_impl; [| |done].
    - done.
    - by intros ?? [? ?]. }
  have Hstutter:=Hmatch.
  apply can_destutter_auxtr in Hstutter; last first.
  { intros ?? Hstep. inversion Hstep. done. }
  destruct Hstutter as [mtr Hupto].

  clear Hiatr.

  assert (infinite_trace extr) as Hinf.
  {
    intros n.
    induction n; [done|].
    destruct IHn as [extr' Hafter].
    apply traces_match_flip in Hmatch_strong.
    eapply traces_match_after in Hmatch_strong; [|done].
    destruct Hmatch_strong as [auxtr' [Hafter' Hmatch_strong]].
    replace (S n) with (n + 1) by lia.
    rewrite after_sum'.
    rewrite Hafter.
    apply traces_match_first in Hmatch_strong.
    destruct Hmatch_strong as [_ [[Hξ1 Hξ2] _]].
    eapply extrace_maximal_after in Hmaximal; [|done].
    inversion Hmaximal; simplify_eq; [|done].

    assert (∃ oζ c', locale_step c oζ c') as Hstep; last first.
    { exfalso. destruct Hstep as (?&?&Hstep). by eapply H. }

    apply not_Forall_Exists in Hξ1; [|apply _].
    apply Exists_exists in Hξ1 as [e [Hξ11 Hξ12]].
    rewrite Forall_forall in Hξ2.
    specialize (Hξ2 e Hξ11) as [|Hred]; [done|].

    destruct Hred as (e' & σ' & es' & Hred).

    apply elem_of_list_split in Hξ11 as (es1&es2&Hes).

    destruct c; simpl in *.

    eexists (Some _), _.
    econstructor; eauto. simpl in *.
    f_equiv. done.
  }

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

  pose proof (yesno_mdl_progresses mtr Hinf'' Hvalid'' Hfair'' Hfirst'')
    as Hprogress.

  eapply (yesno_aux_ex_progress_preserved l _ auxtr); [done|].
  by eapply yesno_mtr_aux_progress_preserved.
Qed.
