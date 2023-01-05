From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.fairness Require Export inftraces.

Record FairModel : Type := {
  fmstate: Type;
  fmstate_eqdec: EqDecision fmstate;
  fmstate_inhabited: Inhabited fmstate;

  fmrole: Type;
  fmrole_eqdec: EqDecision fmrole;
  fmrole_countable: Countable fmrole;
  fmrole_inhabited: Inhabited fmrole;

  fmtrans: fmstate → fmrole → fmstate → Prop;
  fmfairness : trace fmstate fmrole → Prop;
  fmfairness_preserved : ∀ mtr mtr' k, after k mtr = Some mtr' →
                                       fmfairness mtr → fmfairness mtr';

  live_roles: fmstate → gset fmrole;
  fm_live_spec: ∀ s ρ s', fmtrans s ρ s' → ρ ∈ live_roles s;
}.

#[global] Existing Instance fmstate_eqdec.
#[global] Existing Instance fmstate_inhabited.
#[global] Existing Instance fmrole_eqdec.
#[global] Existing Instance fmrole_countable.
#[global] Existing Instance fmrole_inhabited.

Definition fair_model_to_model (FM : FairModel) : Model :=
  {|
    mstate := fmstate FM;
    mlabel := fmrole FM;
    mtrans := fmtrans FM;
  |}.

(* Basically, soundness of the logic and the lemmas above tell us that we have a program
   trace and a model trace which are related by traces_match labels_math!

   We now prove that this relation transports the properties we care about; the first
   place of which is fairness.
 *)

(* Definition of fairness for both kinds of traces *)

Definition extrace Λ := trace (cfg Λ) (ex_label Λ).

(* This should not be necessary *)
Close Scope Z_scope.

Definition trace_implies {S L} (P Q : S → option L → Prop) (tr : trace S L) : Prop :=
  ∀ n, pred_at tr n P → ∃ m, pred_at tr (n+m) Q.

Lemma trace_implies_after {S L : Type} (P Q : S → option L → Prop) tr tr' k :
  after k tr = Some tr' →
  trace_implies P Q tr → trace_implies P Q tr'.
Proof.
  intros Haf Hf n Hp.
  have Hh:= Hf (k+n).
  have Hp': pred_at tr (k + n) P.
  { rewrite (pred_at_sum _ k) Haf /= //. }
  have [m Hm] := Hh Hp'. exists m.
  by rewrite <- Nat.add_assoc, !(pred_at_sum _ k), Haf in Hm.
Qed.

Lemma trace_implies_cons {S L : Type} (P Q : S → option L → Prop) s l tr :
  trace_implies P Q (s -[l]-> tr) → trace_implies P Q tr.
Proof. intros H. by eapply (trace_implies_after _ _ (s -[l]-> tr) tr 1). Qed.

Lemma pred_at_or {S L : Type} (P1 P2 : S → option L → Prop) tr n :
  pred_at tr n (λ s l, P1 s l ∨ P2 s l) ↔
  pred_at tr n P1 ∨
  pred_at tr n P2.
Proof.
  split.
  - revert tr.
    induction n as [|n IHn]; intros tr Htr.
    + destruct tr; [done|].
      rewrite !pred_at_0. rewrite !pred_at_0 in Htr.
      destruct Htr as [Htr | Htr]; [by left|by right].
    + destruct tr; [done|by apply IHn].
  - revert tr.
    induction n as [|n IHn]; intros tr Htr.
    + destruct tr; [done|].
      rewrite !pred_at_0 in Htr. rewrite !pred_at_0.
      destruct Htr as [Htr | Htr]; [by left|by right].
    + by destruct tr; [by destruct Htr as [Htr|Htr]|apply IHn].
Qed.

Section exec_trace.
  Context {Λ : language}.
  Context `{EqDecision (locale Λ)}.

  Definition locale_enabled (ζ : locale Λ) (c: cfg Λ) :=
    ∃ e, from_locale c.1 ζ = Some e ∧ to_val e = None.

  Definition live_ex_label (ζ : ex_label Λ) (c : cfg Λ) : Prop :=
    match ζ with
    | inl ζ => locale_enabled ζ c
    | inr ζ => config_enabled ζ c.2
    end.

  Definition fair_scheduling_ex ζ : extrace Λ → Prop :=
    trace_implies (λ c _, live_ex_label ζ c)
                  (λ c otid, ¬ live_ex_label ζ c ∨ otid = Some ζ).

  Lemma fair_scheduling_ex_after ζ tr tr' k:
    after k tr = Some tr' →
    fair_scheduling_ex ζ tr → fair_scheduling_ex ζ tr'.
  Proof. destruct ζ; apply trace_implies_after. Qed.

  Lemma fair_scheduling_ex_cons ζ c ζ' r:
    fair_scheduling_ex ζ (c -[ζ']-> r) → fair_scheduling_ex ζ r.
  Proof. destruct ζ; apply trace_implies_cons. Qed.

  CoInductive extrace_valid: extrace Λ → Prop :=
  | extrace_valid_singleton c: extrace_valid ⟨c⟩
  | extrace_valid_cons c oζ tr:
      locale_step c oζ (trfirst tr) →
      extrace_valid tr →
      extrace_valid (c -[oζ]-> tr).

  Lemma to_trace_preserves_validity ex iex:
    extrace_valid (to_trace (trace_last ex) iex) → valid_exec ex →
    valid_inf_exec ex iex.
  Proof.
    revert ex iex. cofix CH. intros ex iex Hexval Hval.
    rewrite (trace_unfold_fold (to_trace _ _)) in Hexval.
    destruct iex as [|[??] iex]; first by econstructor. cbn in Hexval.
    inversion Hexval. simplify_eq.
    econstructor; try done.
    - by destruct iex as [|[??]?].
    - apply CH; eauto. econstructor; try done. by destruct iex as [|[??]?].
  Qed.

  Lemma from_trace_preserves_validity (extr: extrace Λ) ex:
    extrace_valid extr →
    valid_exec ex →
    trace_last ex = trfirst extr →
    valid_inf_exec ex (from_trace extr).
  Proof.
    revert ex extr. cofix CH. intros ex extr Hexval Hval Heq.
    rewrite (inflist_unfold_fold (from_trace extr)). destruct extr as [c|c tid tr]; cbn;
     first by econstructor.
    inversion Hexval; simplify_eq; econstructor; eauto. apply CH; eauto.
      by econstructor.
  Qed.

  Lemma from_trace_preserves_validity_singleton (extr: extrace Λ):
    extrace_valid extr →
    valid_inf_exec (trace_singleton (trfirst extr)) (from_trace extr).
  Proof.
    intros ?. eapply from_trace_preserves_validity; eauto. econstructor.
  Qed.

End exec_trace.

Definition mtrace (M:FairModel) := trace (M.(fmstate)) (M.(fmrole)).

Section model_traces.
  Context `{M: FairModel}.

  Definition role_enabled_model ρ (s: M.(fmstate)) := ρ ∈ M.(live_roles) s.

  Definition fair_scheduling_mtr ρ : mtrace M → Prop :=
    trace_implies (λ δ _, role_enabled_model ρ δ)
                  (λ δ ℓ, ¬ role_enabled_model ρ δ ∨ ℓ = Some ρ).

  Lemma fair_scheduling_mtr_after ℓ tr tr' k:
    after k tr = Some tr' →
    fair_scheduling_mtr ℓ tr → fair_scheduling_mtr ℓ tr'.
  Proof. apply trace_implies_after. Qed.

  Lemma fair_scheduling_mtr_cons ℓ δ ℓ' r:
    fair_scheduling_mtr ℓ (δ -[ℓ']-> r) → fair_scheduling_mtr ℓ r.
  Proof. apply trace_implies_cons. Qed.

  Lemma fair_scheduling_mtr_cons_forall δ ℓ' r:
    (∀ ℓ, fair_scheduling_mtr ℓ (δ -[ℓ']-> r)) → (∀ ℓ, fair_scheduling_mtr ℓ r).
  Proof. intros Hℓ ℓ. eapply trace_implies_cons. apply Hℓ. Qed.

  Definition fair_scheduling mtr := ∀ ρ, fair_scheduling_mtr ρ mtr.
  Definition mtrace_fair mtr := fair_scheduling mtr ∧ M.(fmfairness) mtr.

  Inductive mtrace_valid_ind (mtrace_valid_coind: mtrace M → Prop) :
    mtrace M → Prop :=
  | mtrace_valid_singleton δ: mtrace_valid_ind _ ⟨δ⟩
  | mtrace_valid_cons δ ℓ tr:
      fmtrans _ δ ℓ (trfirst tr) →
      mtrace_valid_coind tr →
      mtrace_valid_ind _ (δ -[ℓ]-> tr).
  Definition mtrace_valid := paco1 mtrace_valid_ind bot1.

  Lemma mtrace_valid_mono :
    monotone1 mtrace_valid_ind.
  Proof.
    unfold monotone1. intros x0 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve mtrace_valid_mono : paco.

End model_traces.

Global Hint Resolve mtrace_valid_mono : paco.
