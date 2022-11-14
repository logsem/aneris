From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export fairness.
From stdpp Require Import option.
From Paco Require Import pacotac.

(* TODO: See if we can generalise the notion of fair terminating traces *)
Definition mtrace_fairly_terminating {Mdl : FairModel} (mtr : mtrace Mdl) :=
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  terminating_trace mtr.

Definition extrace_fairly_terminating {Λ} `{Countable (locale Λ)}
           (extr : extrace Λ) :=
  extrace_valid extr →
  (∀ tid, fair_ex tid extr) →
  terminating_trace extr.

Class FairTerminatingModel (Mdl: FairModel) := {
  ftm_leq: relation Mdl;
  ftm_order: PreOrder ftm_leq;
  ftm_wf: wf (strict ftm_leq);

  ftm_decreasing_role: Mdl -> fmrole Mdl;
  ftm_decr:
    ∀ (s: Mdl), (∃ ρ' s', fmtrans _ s ρ' s') ->
                ftm_decreasing_role s ∈ live_roles _ s ∧
                ∀ s', (fmtrans _ s (Some (ftm_decreasing_role s)) s' ->
                       (strict ftm_leq) s' s);
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
  (* TODO: Why do we need to extract this manually? *)
  assert (EqDecision Mdl) by apply Mdl.(fmstate_eqdec).
  destruct (decide (b = c)) as [->|Heq]; [done|].
  split; [by etransitivity|].
  intros H'. apply H1'.
  by etransitivity.
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
