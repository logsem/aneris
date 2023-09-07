From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.fairness Require Export inftraces.

Record FairModel : Type := {
  fmstate:> Type;
  fmstate_eqdec: EqDecision fmstate;
  fmstate_inhabited: Inhabited fmstate;

  fmrole: Type;
  fmrole_eqdec: EqDecision fmrole;
  fmrole_countable: Countable fmrole;
  fmrole_inhabited: Inhabited fmrole;

  fmtrans: fmstate -> option fmrole -> fmstate -> Prop;

  live_roles: fmstate -> gset fmrole;
  fm_live_spec: forall s ρ s', fmtrans s (Some ρ) s' -> ρ ∈ live_roles s;
}.

#[global] Existing Instance fmrole_eqdec.
#[global] Existing Instance fmrole_countable.
#[global] Existing Instance fmrole_inhabited.
#[global] Existing Instance fmstate_inhabited.

(* Basically, soundness of the logic and the lemmas above tell us that we have a program
   trace and a model trace which are related by traces_match labels_math!

   We now prove that this relation transports the properties we care about; the first
   place of which is fairness.
 *)

(* Definition of fairness for both kinds of traces *)

Section GeneralizedFairness.
  Context {S L: Type}.
  Context (locale_prop: L -> S -> Prop). 

  Definition fair_by (ζ: L) (otr: trace S (option L)): Prop :=
    forall n, pred_at otr n (λ c _, locale_prop ζ c) ->
         ∃ m, pred_at otr (n+m) (λ c _, ¬ locale_prop ζ c)
              ∨ pred_at otr (n+m) (λ _ otid, otid = Some (Some ζ)).

  Lemma fair_by_after ζ tr tr' k:
    after k tr = Some tr' ->
    fair_by ζ tr -> fair_by ζ tr'.
  Proof.
    intros Haf Hf n Hp.
    have Hh:= Hf (k+n).
    have Hp': pred_at tr (k + n) (λ (c : S) (_ : option $ option L), locale_prop ζ c).
    { rewrite (pred_at_sum _ k) Haf /= //. }
    have [m Hm] := Hh Hp'. exists m.
    by rewrite <- Nat.add_assoc, !(pred_at_sum _ k), Haf in Hm.
  Qed.

  Lemma fair_by_cons (tid: L) (c: S) (tid' : option L) (r : trace S (option L)):
      fair_by tid (c -[ tid' ]-> r) → fair_by tid r.
  Proof. intros H. by eapply (fair_by_after tid (c -[tid']-> r) r 1). Qed.

  (* Lemma fair_model_trace_cons_forall δ ℓ' r: *)
  Lemma fair_by_cons_forall δ ℓ' r:
    (∀ ℓ, fair_by ℓ (δ -[ℓ']-> r)) -> (∀ ℓ, fair_by ℓ r).
  Proof. eauto using fair_by_cons. Qed.

  (* TODO: try to unify validity lemmas by generalizing over step relation *)
  
End GeneralizedFairness.

Definition extrace Λ := trace (cfg Λ) (olocale Λ).

Section exec_trace.
  Context {Λ : language}.
  Context `{EqDecision (locale Λ)}.

  Definition locale_enabled (ζ : locale Λ) (c: cfg Λ) :=
    ∃ e, from_locale c.1 ζ = Some e ∧ to_val e = None.

  Definition fair_ex ζ (extr: extrace Λ): Prop :=
    fair_by locale_enabled ζ extr. 

  CoInductive extrace_valid: extrace Λ -> Prop :=
  | extrace_valid_singleton c: extrace_valid ⟨c⟩
  | extrace_valid_cons c oζ tr:
      locale_step c oζ (trfirst tr) ->
      extrace_valid tr →
      extrace_valid (c -[oζ]-> tr).

  Lemma to_trace_preserves_validity ex iex:
    extrace_valid (to_trace (trace_last ex) iex) -> valid_exec ex -> valid_inf_exec ex iex.
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
    extrace_valid extr ->
    valid_exec ex ->
    trace_last ex = trfirst extr ->
    valid_inf_exec ex (from_trace extr).
  Proof.
    revert ex extr. cofix CH. intros ex extr Hexval Hval Heq.
    rewrite (inflist_unfold_fold (from_trace extr)). destruct extr as [c|c tid tr]; cbn;
     first by econstructor.
    inversion Hexval; simplify_eq; econstructor; eauto. apply CH; eauto.
      by econstructor.
  Qed.

  Lemma from_trace_preserves_validity_singleton (extr: extrace Λ):
    extrace_valid extr ->
    valid_inf_exec (trace_singleton (trfirst extr)) (from_trace extr).
  Proof.
    intros ?. eapply from_trace_preserves_validity; eauto. econstructor.
  Qed.

End exec_trace.

Definition mtrace (M:FairModel) := trace M (option M.(fmrole)).

Section model_traces.
  Context `{M: FairModel}.

  Definition role_enabled_model ρ (s: M) := ρ ∈ M.(live_roles) s.

  Definition fair_model_trace ρ (mtr: mtrace M): Prop  :=
    fair_by role_enabled_model ρ mtr. 

  Inductive mtrace_valid_ind (mtrace_valid_coind: mtrace M -> Prop) :
    mtrace M -> Prop :=
  | mtrace_valid_singleton δ: mtrace_valid_ind _ ⟨δ⟩
  | mtrace_valid_cons δ ℓ tr:
      fmtrans _ δ ℓ (trfirst tr) ->
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

  Lemma mtrace_valid_after (mtr mtr' : mtrace M) k :
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

  Lemma mtrace_valid_tail s l (tr: mtrace M)
    (VALID': mtrace_valid (s -[l]-> tr)):
    mtrace_valid tr.
  Proof. by eapply mtrace_valid_after with (k := 1); eauto. Qed.

End model_traces.


Definition FM_strong_lr (FM: FairModel) :=
  forall st ρ, ρ ∈ live_roles FM st <-> exists st', fmtrans FM st (Some ρ) st'.


Global Hint Resolve fair_by_cons: core.
Global Hint Resolve mtrace_valid_mono : paco.
