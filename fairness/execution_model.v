From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium Require Import language.
From trillium.program_logic Require Import traces weakestpre.
From trillium.fairness Require Import inftraces fairness. 

Class ExecutionModel (Λ: language) (M: Model) := {

    (* TODO: how to express that these two are typeclasses themselves? *)
    em_preGS: gFunctors -> Set;
    em_GS: gFunctors -> Set;
    em_Σ: gFunctors;
    em_Σ_subG: forall Σ, subG em_Σ Σ -> em_preGS Σ;

    em_valid_evolution_step:
    olocale Λ → cfg Λ → mstate M → mlabel M → mstate M → Prop;

    (* em_fork_post {Σ} *)
    em_thread_post {Σ} `{em_GS Σ}
    : locale Λ ->
      (* val -> *)
      iProp Σ;
    em_msi {Σ} `{em_GS Σ}: cfg Λ -> mstate M -> iProp Σ;
    
    em_init_resource {Σ: gFunctors} `{em_GS Σ}: mstate M → iProp Σ;
    (* TODO: currently we assume that postconditions of all threads coincide *)
    (* em_init_thread_post {Σ}: locale Λ -> val -> iProp Σ; *)
    em_is_init_st: cfg Λ -> mstate M -> Prop;
    
    em_initialization Σ `{ePreGS: em_preGS Σ}: 
    forall (s1: mstate M) (σ: cfg Λ)
      (INIT_ST: em_is_init_st σ s1),
      ⊢ (|==> ∃ eGS: em_GS Σ, @em_init_resource _ eGS s1 ∗ @em_msi _ eGS σ s1)
}.

Section EMDefinitions.
  Context `{EM: ExecutionModel Λ M}. 

  Definition em_valid_state_evolution_fairness
    (extr : execution_trace Λ) (auxtr: auxiliary_trace M) :=
    match extr, auxtr with
    | (extr :tr[oζ]: σ), auxtr :tr[ℓ]: δ =>
        (* labels_match (LM:=LM) oζ ℓ ∧ LM.(lm_ls_trans) (trace_last auxtr) ℓ δ ∧ *)
        (* tids_smaller es δ *)
      em_valid_evolution_step oζ σ (trace_last auxtr) ℓ δ
    | _, _ => True
    end.

  (* TODO: where is that needed? *)
  Definition valid_lift_fairness
    (φ: execution_trace Λ -> auxiliary_trace M -> Prop)
    (extr : execution_trace Λ) (auxtr : auxiliary_trace M) :=
    em_valid_state_evolution_fairness extr auxtr ∧ φ extr auxtr.

End EMDefinitions.


(* Section TracesMatch. *)
(*   Context `{EM: ExecutionModel Λ M}. *)

(*   Let auxtrace := trace (mstate M) (mlabel M). *)

(*   Context (state_rel: cfg Λ -> mstate M -> Prop). *)
(*   Context (lbl_rel: olocale Λ -> mlabel M -> Prop). *)
(*   Hypothesis (LBL_REL_EM: forall oζ σ δ1 ℓ δ2, *)
(*                  em_valid_evolution_step oζ σ δ1 ℓ δ2 -> *)
(*                  lbl_rel oζ ℓ). *)
(*   Hypothesis (STEP_EM: forall oζ σ δ1 ℓ δ2, *)
(*                  em_valid_evolution_step oζ σ δ1 ℓ δ2 -> *)
(*                  mtrans δ1 ℓ δ2). *)

(*   Definition exaux_traces_match: *)
(*     extrace Λ → auxtrace → Prop := *)
(*     traces_match lbl_rel *)
(*       state_rel *)
(*       locale_step *)
(*       (@mtrans M). *)

(*   (* TODO: Why do we need explicit [LM] here? *) *)
(*   Lemma valid_inf_system_trace_implies_traces_match_strong *)
(*         (φ : execution_trace Λ -> auxiliary_trace M -> Prop) *)
(*         (ψ : _ → _ → Prop) *)
(*         ex atr iex iatr progtr (auxtr : auxtrace): *)
(*     (forall (ex: execution_trace Λ) (atr: auxiliary_trace M), *)
(*         φ ex atr -> state_rel (trace_last ex) (trace_last atr)) -> *)
(*     (forall (ex: execution_trace Λ) (atr: auxiliary_trace M), *)
(*         φ ex atr -> em_valid_state_evolution_fairness ex atr) -> *)
(*     (∀ extr auxtr, φ extr auxtr → ψ (trace_last extr) (trace_last auxtr)) → *)
(*     exec_trace_match ex iex progtr -> *)
(*     exec_trace_match atr iatr auxtr -> *)
(*     valid_inf_system_trace φ ex atr iex iatr -> *)
(*     traces_match lbl_rel *)
(*                  (λ σ δ, state_rel σ δ ∧ ψ σ δ) *)
(*                  locale_step *)
(*                  (@mtrans M) progtr auxtr. *)
(*   Proof. *)
(*     intros Hφ1 Hφ2 Hφψ. *)
(*     revert ex atr iex iatr auxtr progtr. cofix IH. *)
(*     intros ex atr iex iatr auxtr progtr Hem Ham Hval. *)
(*     inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq. *)
(*     - inversion Hem; inversion Ham. econstructor; eauto. *)
(*       pose proof (Hφ1 ex atr Hphi). *)
(*       split; [by simplify_eq|]. simplify_eq. by apply Hφψ. *)
(*     - inversion Hem; inversion Ham. subst. *)
(*       pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'. *)
(*       specialize (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as STEP. *)
(*       red in STEP. *)
(*       econstructor. *)
(*       + eapply LBL_REL_EM; eauto. *)
(*       + eauto. *)
(*       + match goal with *)
(*         | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq *)
(*         end; done. *)
(*       + match goal with *)
(*         | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq *)
(*         end; eapply STEP_EM; eauto. *)
(*       + eapply IH; eauto. *)
(*   Qed. *)

(*   (* TODO: Why do we need explicit [LM] here? *) *)
(*   Lemma valid_inf_system_trace_implies_traces_match *)
(*         (φ: execution_trace Λ -> auxiliary_trace M -> Prop) *)
(*         ex atr iex iatr progtr (auxtr : auxtrace): *)
(*     (forall (ex: execution_trace Λ) (atr: auxiliary_trace M), *)
(*         φ ex atr -> state_rel (trace_last ex) (trace_last atr)) -> *)
(*     (forall (ex: execution_trace Λ) (atr: auxiliary_trace M), *)
(*         φ ex atr -> em_valid_state_evolution_fairness ex atr) -> *)
(*     exec_trace_match ex iex progtr -> *)
(*     exec_trace_match atr iatr auxtr -> *)
(*     valid_inf_system_trace φ ex atr iex iatr -> *)
(*     exaux_traces_match progtr auxtr. *)
(*   Proof. *)
(*     intros Hφ1 Hφ2. *)
(*     revert ex atr iex iatr auxtr progtr. cofix IH. *)
(*     intros ex atr iex iatr auxtr progtr Hem Ham Hval. *)
(*     inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq. *)
(*     - inversion Hem; inversion Ham. econstructor; eauto. *)
(*       pose proof (Hφ1 ex atr Hphi). *)
(*       by simplify_eq. *)
(*     - inversion Hem; inversion Ham. subst. *)
(*       pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'. *)
(*       specialize (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as STEP. *)
(*       red in STEP. *)
(*       econstructor. *)
(*       + eauto. *)
(*       + eauto. *)
(*       + match goal with *)
(*         | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq *)
(*         end; done. *)
(*       + match goal with *)
(*         | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq *)
(*         end; eapply STEP_EM; eauto. *)
(*       + eapply IH; eauto. *)
(*   Qed. *)

(* End TracesMatch. *)
