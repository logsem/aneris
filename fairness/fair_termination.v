From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export fairness fairness_finiteness.
From stdpp Require Import option.
From Paco Require Import pacotac.

(* TODO: See if we can generalise the notion of fair terminating traces *)
Definition mtrace_fairly_terminating {Mdl : FairModel} (mtr : mtrace Mdl) :=
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  terminating_trace mtr.

Definition auxtrace_fairly_terminating {Λ} {Mdl : FairModel}
           {LM : LiveModel Λ Mdl} (auxtr : auxtrace LM) :=
  auxtrace_valid (LM:=LM) auxtr →
  (∀ ρ, fair_aux ρ auxtr) →
  terminating_trace auxtr.

Definition extrace_fairly_terminating {Λ} `{Countable (locale Λ)}
           (extr : extrace Λ) :=
  extrace_valid extr →
  (∀ tid, fair_ex tid extr) →
  terminating_trace extr.

Class FairTerminatingModel (Mdl: FairModel) := {
  ftm_leq: relation Mdl;
  ftm_order: PartialOrder ftm_leq;
  ftm_wf: wf (strict ftm_leq);

  ftm_decreasing_role: Mdl -> fmrole Mdl;
  ftm_decr:
    ∀ (s: Mdl), (∃ ρ' s', fmtrans _ s ρ' s') -> ftm_decreasing_role s ∈ live_roles _ s ∧
      ∀ s', (fmtrans _ s (Some (ftm_decreasing_role s)) s' -> (strict ftm_leq) s' s);
  ftm_decreasing_role_preserved:
    ∀ (s s': Mdl) ρ',
      (fmtrans _ s ρ' s' -> ρ' ≠ Some (ftm_decreasing_role s) ->
      ftm_decreasing_role s = ftm_decreasing_role s');
  ftm_notinc:
    ∀ (s: Mdl) ρ s', (fmtrans _ s ρ s' -> ftm_leq s' s);
}.

Arguments ftm_leq {_ _}.
Arguments ftm_wf {_ _}.
Arguments ftm_decr {_ _}.
Arguments ftm_decreasing_role {_ _}.

#[global] Existing Instance ftm_order.

Notation ftm_lt := (strict ftm_leq).
Local Infix "<" := ftm_lt.
Local Infix "≤" := ftm_leq.

Lemma ftm_trans' `{FairTerminatingModel Mdl} a b c:
  a < b -> b ≤ c -> a < c.
Proof.
  intros [H1 H1'] H2.
  split; first transitivity b=>//.
  intro contra. apply H1'.
  suffices ->: b = a by reflexivity.
  eapply anti_symm; last done; [typeclasses eauto | by (transitivity c)].
Qed.

Lemma fair_terminating_traces_terminate_rec `{FairTerminatingModel Mdl}
      (s0: Mdl) (mtr: mtrace Mdl):
  (trfirst mtr) ≤ s0 ->
  mtrace_valid mtr ->
  (∀ ρ, fair_model_trace ρ mtr) ->
  terminating_trace mtr.
Proof.
  revert mtr. induction s0 as [s0 IH] using (well_founded_ind ftm_wf).
  intros mtr Hleq Hval Hfair.
  destruct mtr as [|s ℓ mtr'] eqn:Heq; first by eexists 1.
  destruct (ftm_decr (trfirst mtr)) as (Hlive & Htrdec).
  { exists ℓ, (trfirst mtr'). punfold Hval. inversion Hval; subst; done. }
  rewrite <- Heq in *. clear s ℓ Heq.
  destruct (Hfair (ftm_decreasing_role (trfirst mtr)) 0) as [n Hev];
    first by rewrite /pred_at /=; destruct mtr.
  revert mtr Hval Hleq Hfair Hlive IH Hev Htrdec. induction n as [| n IHn];
    intros mtr Hval Hleq Hfair Hlive IH Hev Htrdec.
  - simpl in *. rewrite /pred_at /= in Hev.
    destruct Hev as [Hev|Hev]; first by destruct mtr; done.
    destruct mtr; first done. injection Hev => ->.
    apply terminating_trace_cons.
    eapply IH =>//; eauto.
    + eapply ftm_trans' =>//. apply Htrdec.
      punfold Hval. inversion Hval; simplify_eq; simpl in *; simplify_eq; done.
    + punfold Hval. inversion Hval; simplify_eq.
      destruct H4; done.
  - simpl in *. destruct mtr; first (exists 1; done).
    rewrite -> !pred_at_S in Hev.
    punfold Hval; inversion Hval as [|??? Htrans Hval']; simplify_eq.
    destruct Hval' as [Hval'|]; last done.
    destruct (decide (ℓ = Some (ftm_decreasing_role s))) as [-> | Hnoteq].
    + apply terminating_trace_cons. eapply IH=>//; eauto.
      eapply ftm_trans' =>//; apply Htrdec. simpl. destruct Hval;done.
    + destruct mtr as [|s' ℓ' mtr''] eqn:Heq; first by eexists 2.
      destruct (ftm_decr (trfirst mtr)) as (Hlive' & Htrdec').
      { exists ℓ', (trfirst mtr''). punfold Hval'; inversion Hval'; subst; done. }
      apply terminating_trace_cons. eapply IHn=>//; eauto.
      * etransitivity; eauto. eapply ftm_notinc =>//.
      * simplify_eq. eapply Hlive'.
      * erewrite <- ftm_decreasing_role_preserved =>//.
      * intros s'' Htrans''. eapply ftm_decr; eauto.
Qed.

Theorem fair_terminating_traces_terminate `{FairTerminatingModel Mdl} :
  ∀ (mtrace : @mtrace Mdl), mtrace_fairly_terminating mtrace.
Proof. intros ???. eapply fair_terminating_traces_terminate_rec=>//. Qed.

Theorem continued_simulation_fair_termination
        `{FairTerminatingModel FM} `(LM:LiveModel Λ FM) `{Countable (locale Λ)}
        (ξ : execution_trace Λ → auxiliary_trace LM → Prop) a1 r1 extr :
  (* TODO: This is required for destruttering - Not sure why *)
  (∀ c c', locale_step (Λ := Λ) c None c' -> False) →
  (* The relation must capture that live tids correspond *)
  (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
     ξ ex atr -> live_tids (LM:=LM) (trace_last ex) (trace_last atr)) ->
  (* The relation must capture that the traces evolve fairly *)
  (forall (ex: execution_trace Λ) (atr: auxiliary_trace LM),
     ξ ex atr -> valid_state_evolution_fairness ex atr) →
  continued_simulation
    ξ ({tr[trfirst extr]}) ({tr[initial_ls a1 r1]}) →
  extrace_fairly_terminating extr.
Proof.
  intros Hstep Hlive Hvalid Hsim Hvex.
  destruct (infinite_or_finite extr) as [Hinf|]; [|by intros ?].
  assert (∃ iatr,
             valid_inf_system_trace
               (continued_simulation ξ)
               (trace_singleton (trfirst extr))
               (trace_singleton (initial_ls a1 r1))
               (from_trace extr)
               iatr) as [iatr Hiatr].
  { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
    Unshelve.
    - done.
    - eapply from_trace_preserves_validity; eauto; first econstructor. }
  assert (∃ (auxtr : auxtrace LM), exaux_traces_match extr auxtr)
    as [auxtr Hmatch].
  { exists (to_trace (initial_ls a1 r1) iatr).
    eapply (valid_inf_system_trace_implies_traces_match
              (continued_simulation ξ)); eauto.
    - intros ? ? ?%continued_simulation_rel. by apply Hlive.
    - intros ? ? ?%continued_simulation_rel. by apply Hvalid.
    - by apply from_trace_spec.
    - by apply to_trace_spec. }
  intros Hfair.
  assert (Hstutter := Hmatch).
  apply can_destutter_auxtr in Hstutter; [|done].
  destruct Hstutter as [mtr Hupto].
  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair.
  have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  eapply exaux_preserves_termination; [apply Hmatch|].
  eapply upto_stutter_finiteness =>//.
  apply fair_terminating_traces_terminate=>//.
Qed.
