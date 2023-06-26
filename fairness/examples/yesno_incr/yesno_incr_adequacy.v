From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness Require Import trace_utils.
From trillium.fairness.examples.yesno_incr Require Import yesno_incr.

From stdpp Require Import finite.

(* The model is finitely branching *)
Definition steppable '(n, w): list ((nat * bool) * option YN) :=
  n' ← [S n; n];
  w' ← [w; negb w];
  ℓ ← [Some Y; Some No];
  mret ((n', w'), ℓ).

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
  ∀ n b, ∃ m, pred_at tr m (λ s _, s = (n,b)).

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

Lemma yesno_mdl_noprogress_Y n m (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (trfirst mtr) = (n, true) →
  (∀ m0 : nat,
     m0 < m → pred_at mtr m0
             (λ (_ : nat * bool) (l : option (option YN)),
                l ≠ Some (Some Y))) →
  pred_at mtr m (λ s _, s = (n, true)).
Proof.
  intros Hinf Hvalid Hfirst Hne.
  induction m.
  { rewrite /pred_at. destruct mtr; done. }
  simpl in *.
  assert (∀ m0 : nat,
          m0 < m
          → pred_at mtr m0
              (λ (_ : nat * bool) (l : option (option YN)), l ≠ Some (Some Y)))
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
  all: rewrite /trfirst in H; destruct t; simplify_eq; try done.
Qed.

Lemma yesno_mdl_noprogress_No n m (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (trfirst mtr) = (n, false) →
  (∀ m0 : nat,
     m0 < m → pred_at mtr m0
             (λ (_ : nat * bool) (l : option (option YN)),
                l ≠ Some (Some No))) →
  pred_at mtr m (λ s _, s = (n, false)).
Proof.
  intros Hinf Hvalid Hfirst Hne.
  induction m.
  { rewrite /pred_at. destruct mtr; done. }
  simpl in *.
  assert (∀ m0 : nat,
          m0 < m
          → pred_at mtr m0
              (λ (_ : nat * bool) (l : option (option YN)), l ≠ Some (Some No)))
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
  all: rewrite /trfirst in H; destruct t; simplify_eq; try done.
Qed.

Theorem yesno_mdl_progresses_Y n (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = (n, true) →
  ∃ m, pred_at mtr m (λ s _, s = (n, false)).
Proof.
  intros Hinf Hvalid Hfair Hfirst.
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
  assert (s = (n,true)) as ->.
  { eapply yesno_mdl_noprogress_Y in Hschedne; [|done..].
    rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. }
  eapply mtrace_valid_after in Hvalid; [|done].
  pinversion Hvalid; simplify_eq. inversion H1; simplify_eq.
  exists (m + 1).
  rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl.
  destruct t; simpl in *; simplify_eq; done.
Qed.

Theorem yesno_mdl_progresses_No n (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = (n, false) →
  ∃ m, pred_at mtr m (λ s _, s = (S n, true)).
Proof.
  intros Hinf Hvalid Hfair Hfirst.
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
  assert (s = (n,false)) as ->.
  { eapply yesno_mdl_noprogress_No in Hschedne; [|done..].
    rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. }
  eapply mtrace_valid_after in Hvalid; [|done].
  pinversion Hvalid; simplify_eq. inversion H1; simplify_eq.
  exists (m + 1).
  rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl.
  destruct t; simpl in *; simplify_eq; done.
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
  (trfirst mtr) = (0, true) →
  yesno_mdl_progress mtr.
Proof.
  intros Hinf Hvalid Hfair Hfirst n.
  induction n as [|n IHn]; intros b.
  { destruct b.
    - exists 0. rewrite /pred_at. rewrite /trfirst in Hfirst. simpl.
      destruct mtr; done.
    - by apply yesno_mdl_progresses_Y. }
  destruct b.
  - destruct (IHn false) as [m Hpred].
    rewrite /pred_at in Hpred.
    destruct (after m mtr) eqn:Hafter; [|done].
    eapply infinite_trace_after'' in Hinf; [|done].
    eapply mtrace_valid_after in Hvalid; [|done].
    assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ t) as Hfair'.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst t = (n, false)) as Hfirst'.
    { rewrite /trfirst. destruct t; done. }
    pose proof (yesno_mdl_progresses_No n t Hinf Hvalid Hfair' Hfirst')
      as [m' Hpred'].
    exists (m + m').
    rewrite pred_at_sum. rewrite Hafter. done.
  - destruct (IHn false) as [m Hpred].
    rewrite /pred_at in Hpred.
    destruct (after m mtr) eqn:Hafter; [|done].
    eapply infinite_trace_after'' in Hinf; [|done].
    eapply mtrace_valid_after in Hvalid; [|done].
    assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ t) as Hfair'.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst t = (n, false)) as Hfirst'.
    { rewrite /trfirst. destruct t; done. }
    pose proof (yesno_mdl_progresses_No n t Hinf Hvalid Hfair' Hfirst')
      as [m' Hpred'].
    rewrite /pred_at in Hpred'.
    destruct (after m' t) eqn:Hafter'; [|done].
    eapply infinite_trace_after'' in Hinf; [|done].
    eapply mtrace_valid_after in Hvalid; [|done].
    assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ t0) as Hfair''.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst t0 = (S n, true)) as Hfirst''.
    { rewrite /trfirst. destruct t0; done. }
    pose proof (yesno_mdl_progresses_Y (S n) t0 Hinf Hvalid Hfair'' Hfirst'')
      as [m'' Hpred''].
    exists (m + m' + m'').
    rewrite pred_at_sum. rewrite after_sum'. rewrite Hafter. rewrite Hafter'.
    done.
Qed.

(* Definition yesno_mdl_progress' n b (mtr : yesno_mtrace) := *)
(*   trace_eventually mtr (λ s _, s = (n,b)). *)


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
  ∀ n b, ∃ m, pred_at auxtr m (λ s l, (λ s' _, s' = (n,b)) (ls_under s) (l ≫= Ul)).

Lemma yesno_mtr_aux_progress_preserved
      (mtr : mtrace the_fair_model)
      (auxtr : auxtrace the_model) :
  upto_stutter ls_under Ul auxtr mtr →
  yesno_mdl_progress mtr → yesno_aux_progress auxtr.
Proof.
  intros Hstutter Hmtr.
  intros n b. apply (trace_eventually_stutter_preserves _ mtr auxtr (λ s' _, s' = (n,b))).
  - done.
  - apply Hmtr.
Qed.

(* Defining this requires exposing the location in the state *)
(* Definition yesno_ex_progress (tr : heap_lang_extrace) := *)
(*   ∀ n b, ∃ m, pred_at tr m (λ s _, s.2 !! ??? = Some ???). *)
Definition yesno_ex_progress (tr : heap_lang_extrace) :=
  False.

Lemma yesno_aux_ex_progress_preserved (auxtr : auxtrace the_model) (extr : heap_lang_extrace) :
  yesno_aux_progress auxtr → yesno_ex_progress extr.
Proof. Admitted.

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

(* TODO: Prove/Move *)
Lemma upto_stutter_after' {St S' L L': Type} (Us: St -> S') (Ul: L -> option L')
      {btr str} n {btr'} :
  upto_stutter Us Ul btr str →
  after n btr = Some btr' →
  ∃ str', after n str = Some str'.
Proof.
  intros Hstutter Hafter.
  induction n as [|n IHn].
Admitted.

Lemma upto_stutter_infinite_trace {St S' L L': Type} (Us: St -> S') (Ul: L -> option L')
 tr1 tr2 :
  upto_stutter Us Ul tr1 tr2 → infinite_trace tr1 → infinite_trace tr2.
Proof.
  intros Hmatch Hinf n. specialize (Hinf n) as [tr' Hafter].
  by eapply upto_stutter_after' in Hafter as [tr'' Hafter'].
Qed.

Theorem yesno_ex_progresses (extr : heap_lang_extrace) :
  extrace_valid extr →
  (∀ tid, fair_ex tid extr) →
  (trfirst extr).1 = [start #()] →
  yesno_ex_progress extr.
Proof.
  intros Hvalid Hfair Hfirst.
  assert (heapGpreS yesnoΣ the_model) as HPreG.
  { apply _. }
  pose proof (simulation_adequacy_model_trace yesnoΣ the_model NotStuck
                                  ∅ (start #()) (0, true) extr Hvalid Hfirst) =>//.
  assert (rel_finitary (sim_rel the_model)) as Hfin.
  { eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl. apply (model_finitary s1). }
  assert (live_roles the_fair_model (0, true) ≠ ∅) as Hneq.
  { set_solver. }
  assert ((∀ heapGS0 : heapGS yesnoΣ the_model,
         ⊢ |={⊤}=>
             frag_model_is (0, true) -∗
             frag_free_roles_are (∅ ∖ live_roles the_fair_model (0, true)) -∗
             has_fuels 0
               (gset_to_gmap (lm_fl the_model (0, true))
                  (live_roles the_fair_model (0, true))) ={⊤}=∗
             WP start #() @0 {{ _, 0 ↦M ∅ }})) as Hwp.
  { iIntros (?) "!> Hmdl Hfree Hfuel !>".
    replace (∅ ∖ live_roles the_fair_model (0, true)) with
      (∅:gset (fmrole the_fair_model)) by set_solver.
    simpl. rewrite /yn_live_roles.
    replace (gset_to_gmap 61 {[No; Y]}) with
      ({[Y := 61; No := 61]} : gmap _ _); last first.
    { rewrite /gset_to_gmap. simpl.
      rewrite !map_fmap_union. rewrite !map_fmap_singleton.
      rewrite map_union_comm; last first.
      { rewrite map_disjoint_singleton_l.
        by rewrite lookup_insert_ne. }
      rewrite -!insert_union_l.
      rewrite left_id. done. }
    iApply (start_spec with "[$Hmdl $Hfree $Hfuel]"); [lia|].
    by iIntros "!>?". }
  destruct (H Hfin Hneq Hwp) as [auxtr [mtr [Hmatch Hstutter]]].
  (* TODO: Prove from ??? - Likely need to lift adequacy to derive from post conditions *)
  assert (infinite_trace extr) as Hinf by admit.
  pose proof (fairness_preserved extr auxtr Hinf Hmatch Hfair) as Hfair'.
  pose proof (upto_stutter_fairness auxtr mtr Hstutter Hfair') as Hfair''.
  assert (infinite_trace mtr) as Hinf''.
  { eapply upto_stutter_infinite_trace; [done|].
    by eapply traces_match_infinite_trace. }
  assert (mtrace_valid mtr) as Hvalid''.
  { eapply upto_preserves_validity; [done|].
    by eapply exaux_preserves_validity. }
  assert (trfirst mtr = (0, true)) as Hfirst''.
  { admit. }
  pose proof (yesno_mdl_progresses mtr Hinf'' Hvalid'' Hfair'' Hfirst'') as Hprogress.
  eapply (yesno_aux_ex_progress_preserved auxtr).
  by eapply yesno_mtr_aux_progress_preserved.
Admitted.
