(* From trace_program_logic.program_logic Require Export adequacy. *)
(* From trace_program_logic.fairness Require Export fairness. *)
From trillium.fairness Require Export fairness.
From stdpp Require Import option.
From Paco Require Import pacotac.


Definition fairly_terminating (Mdl: FairModel) :=
  ∀ (mtr: @mtrace Mdl),
    mtrace_valid mtr ->
    (∀ ρ, fair_model_trace ρ mtr) ->
    terminating_trace mtr.

Definition active_state {Mdl: FairModel} (s: Mdl) :=
  ∃ ρ_ s_, fmtrans _ s ρ_ s_. 

Class FairTerminatingModelSimple (Mdl: FairModel) := {
  ftms_leq: relation Mdl;
  ftms_order: PartialOrder ftms_leq;
  ftms_wf: wf (strict ftms_leq);

  ftms_active_dec: forall (s: Mdl), Decision (active_state s);
  ftms_exists_lt_next: ∀ (s: Mdl) (ACTIVE: active_state s),
      ∃ (ρ: fmrole Mdl),
        ρ ∈ live_roles _ s /\
        forall s' (STEPρ: fmtrans _ s (Some ρ) s'), strict ftms_leq s' s;

  ftms_notinc:
    ∀ (s: Mdl) ρ s', (fmtrans _ s ρ s' -> ftms_leq s' s);

  ftms_state_dec_eq: EqDecision Mdl;
}.

Arguments ftms_leq {_ _}.
Arguments ftms_wf {_ _}.
Arguments ftms_exists_lt_next {_ _}.
Arguments ftms_active_dec {_}.

Existing Instance ftms_order.

Notation ftms_lt := (strict ftms_leq).
Local Infix "<" := ftms_lt.
Local Infix "≤" := ftms_leq.

Lemma ftms_trans' `{FairTerminatingModelSimple Mdl} a b c:
  a < b -> b ≤ c -> a < c.
Proof.
  intros [H1 H1'] H2.
  split; first transitivity b=>//.
  intro contra. apply H1'.
  suffices ->: b = a by reflexivity.
  eapply anti_symm; last done; [typeclasses eauto | by (transitivity c)].
Qed.

Lemma ftms_le_lt_eq `{FairTerminatingModelSimple Mdl} a b:
  a ≤ b <-> (a < b \/ a = b).
Proof.
  destruct (ftms_state_dec_eq a b) as [-> | LT].
  { split; [tauto | done]. }
  unfold ftms_lt. split; intros. 
  - left. split; auto. intros LE.
    eapply partial_order_anti_symm in H0. intuition.
  - destruct H0; try done. apply H0.
Qed. 

Lemma termination_head_helper `{FairTerminatingModelSimple Mdl}
      (mtr: mtrace Mdl)
      (VALID: mtrace_valid mtr):
  terminating_trace mtr \/ (exists ρ s', fmtrans _ (trfirst mtr) ρ s') /\ forall s, mtr <> ⟨ s ⟩.
Proof.
  punfold VALID. inversion VALID. 
  { left. red. by exists 1. }
  right. eauto.
Qed.

(* Lemma mtrans_valid_cons `{FairTerminatingModelSimple Mdl} s ρ (mtr: mtrace (Mdl := Mdl)) *)
(*   (VALID': mtrace_valid (s -[ Some ρ ]-> mtr)): *)
(*   mtrace_valid mtr.  *)
(* Proof.  *)
(*   punfold VALID'. inversion VALID'. subst.  *)
(*   red. red in H4. tauto. *)
(* Qed. *)

Lemma simple_fair_terminating_traces_terminate_rec `{FairTerminatingModelSimple Mdl}
      (s0: Mdl) (mtr: mtrace Mdl):
  (trfirst mtr) ≤ s0 ->
  mtrace_valid mtr ->
  (∀ ρ, fair_model_trace ρ mtr) ->
  terminating_trace mtr.
Proof.
  revert mtr. induction s0 as [s0 IH] using (well_founded_ind ftms_wf).
  intros mtr Hleq Hval Hfair.
    
  destruct mtr as [|s ℓ mtr']; first by eexists 1. simpl in *.
  destruct (ftms_active_dec _ s) as [ACT | INACT]. 
  2: { punfold Hval. inversion Hval. subst. 
       destruct INACT. red. eauto. }
  
  apply ftms_exists_lt_next in ACT as (ρ & LIVE & STEPSρ).

  pose proof (Hfair ρ 0) as POINT. 
  destruct POINT as [m POINT]; [done| ]. simpl in POINT.
  
  generalize dependent ρ.
  generalize dependent s. generalize dependent ℓ. generalize dependent mtr'.
  induction m as [| m' IHm'].
  { intros. unfold pred_at in POINT. simpl in POINT. destruct POINT as [Nρ | EQ]. 
    { by destruct Nρ. }
    punfold Hval. inversion Hval; subst. rename H2 into STEP, H4 into VALID'. 
    inversion EQ.
    destruct H0 as [[=->] [=->]]. 
    (* subst ℓ. *)
    (* clear EQ. *)
    apply terminating_trace_cons.
    eapply IH.
    2: { apply PreOrder_Reflexive. }
    { eapply ftms_trans'; eauto. }
    { subst. red. red in VALID'. tauto. }
    intros; eapply fair_by_cons; eauto; apply Hfair. }  
  
  intros. destruct mtr'.
  { red. by exists 2. }
  punfold Hval. inversion Hval; subst. rename H2 into STEP, H4 into VALID'.
  clear Hval. simpl in *. 

  apply terminating_trace_cons.
  assert (∀ ρ, fair_model_trace ρ (s1 -[ ℓ0 ]-> mtr')) as Hfair'.
  { intros; eapply fair_by_cons; eauto; apply Hfair. }

  pose proof (ftms_notinc _ _ _ STEP) as LE'%ftms_le_lt_eq. destruct LE' as [LT | ->].
  2: { eapply IHm'; eauto. red. red in VALID'. tauto. }

  eapply (IH s1); eauto.
  { eapply ftms_trans'; eauto. }
  { simpl. done. }
  red. red in VALID'. tauto.
Qed.

Section SFTTF.
  From trillium.fairness Require Import fair_termination.

  Theorem simple_fair_terminating_traces_terminate `{FairTerminatingModelSimple Mdl}:
    ∀ (mtrace : @mtrace Mdl), mtrace_fairly_terminating mtrace.
  Proof. 
    intros ???. 
    eapply simple_fair_terminating_traces_terminate_rec=>//. 
  Qed.

End SFTTF. 
