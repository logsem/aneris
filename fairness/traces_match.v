From iris.proofmode Require Import tactics.
From trillium Require Import language.
From fairness Require Import inftraces fairness. 


Section TracesMatch.
  Context `{Λ: language}.
  Context `{M: Model}. 

  Let model_trace := trace (mstate M) (mlabel M).

  Context (evolution_pred: cfg Λ -> olocale Λ → cfg Λ → 
                           M → mlabel M → M -> Prop). 

  Context (state_rel: cfg Λ -> mstate M -> Prop).
  Context (lbl_rel: olocale Λ -> mlabel M -> Prop).
  Hypothesis (LBL_REL_EV: forall c1 oζ c2 δ1 ℓ δ2,
                 evolution_pred c1 oζ c2 δ1 ℓ δ2 ->
                 lbl_rel oζ ℓ).
  Hypothesis (STEP_EV: forall c1 oζ c2 δ1 ℓ δ2,
                 evolution_pred c1 oζ c2 δ1 ℓ δ2 ->
                 mtrans δ1 ℓ δ2).

  Definition exaux_traces_match:
    extrace Λ → model_trace → Prop :=
    traces_match lbl_rel
      state_rel
      locale_step
      (@mtrans M).

  Lemma valid_inf_system_trace_implies_traces_match_strong'
        (φ : execution_trace Λ -> auxiliary_trace M -> Prop)
        ex atr iex iatr progtr (auxtr : model_trace):
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace M),
        φ ex atr -> state_rel (trace_last ex) (trace_last atr)) ->
    (forall (ex: execution_trace Λ) (oζ: olocale Λ) (c: cfg Λ) 
       (atr: auxiliary_trace M) (ℓ: mlabel M) (δ: mstate M),
        φ (ex :tr[ oζ ]: c) (atr :tr[ ℓ ]: δ) -> 
        evolution_pred (trace_last ex) oζ c (trace_last atr) ℓ δ) ->
    exec_trace_match ex iex progtr ->
    exec_trace_match atr iatr auxtr ->
    valid_inf_system_trace φ ex atr iex iatr ->
    traces_match lbl_rel
                 state_rel
                 locale_step
                 (@mtrans M) progtr auxtr.
  Proof.
    intros Hφ1 Hφ2.
    revert ex atr iex iatr auxtr progtr. cofix IH.
    intros ex atr iex iatr auxtr progtr Hem Ham Hval.
    inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq.
    - inversion Hem; inversion Ham. econstructor; eauto.
      pose proof (Hφ1 ex atr Hphi).
      by simplify_eq. 
    - inversion Hem; inversion Ham. subst.
      pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
      specialize (Hφ2 _ _ _ _ _ _ Hphi') as STEP.
      econstructor.
      + eapply LBL_REL_EV; eauto.
      + eauto.
      + match goal with
        | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + match goal with
        | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq
        end; eapply STEP_EV; eauto.
      + eapply IH; eauto.
  Qed.


  Definition valid_state_evolution_fairness
             (extr : execution_trace Λ) (auxtr : auxiliary_trace M) :=
    match extr, auxtr with
    | (extr :tr[oζ]: (es, σ)), auxtr :tr[ℓ]: δ =>
        evolution_pred (trace_last extr) oζ (es, σ) (trace_last auxtr) ℓ δ
    | _, _ => True
    end.

  (* TODO: this should already be covered by .._strong' lemma above *)
  Lemma valid_inf_system_trace_implies_traces_match
        (φ : execution_trace Λ -> auxiliary_trace M -> Prop)
        ex atr iex iatr progtr (auxtr : model_trace):
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace M),
        φ ex atr -> state_rel (trace_last ex) (trace_last atr)) ->
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace M),
        φ ex atr -> valid_state_evolution_fairness ex atr) ->
    exec_trace_match ex iex progtr ->
    exec_trace_match atr iatr auxtr ->
    valid_inf_system_trace φ ex atr iex iatr ->
    traces_match lbl_rel
                 state_rel
                 locale_step
                 (@mtrans M) progtr auxtr. 
  Proof.
    intros. eapply valid_inf_system_trace_implies_traces_match_strong'; eauto.
    intros. apply H0 in H4. red in H4. by destruct c. 
  Qed. 


End TracesMatch.
