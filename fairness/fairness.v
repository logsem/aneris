From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.fairness Require Export inftraces trace_lookup.

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

Definition fair_model_model `(FM : FairModel) : Model := {|
    mstate := fmstate FM;
    mlabel := option (fmrole FM);
    mtrans := fmtrans FM;
|}.


#[global] Existing Instance fmrole_eqdec.
#[global] Existing Instance fmrole_countable.
#[global] Existing Instance fmrole_inhabited.
#[global] Existing Instance fmstate_inhabited.

(* Basically, soundness of the logic and the lemmas above tell us that we have a program
   trace and a model trace which are related by traces_match labels_math!

   We now prove that this relation transports the properties we care about; the first
   place of which is fairness.
 *)

(* Definition of fairness for all kinds of traces *)
Section GeneralizedFairness.
  Context {S L T: Type}.
  Context (locale_prop: T -> S -> Prop).
  Context (does_step: T -> S -> option (L * S) -> Prop).

  Definition fairness_sat_gen (t: T) (s: S) (step: option (L * S)) :=
    ¬ locale_prop t s \/ does_step t s step. 

  Definition fair_by_gen (t: T) (otr: trace S L): Prop :=
    forall n, pred_at otr n (λ c _, locale_prop t c) ->
         exists m s step, otr !! (n + m) = Some (s, step) /\ fairness_sat_gen t s step. 

  Lemma fair_by_gen_after t tr tr' k:
    after k tr = Some tr' ->
    fair_by_gen t tr -> fair_by_gen t tr'.
  Proof.
    intros Haf Hf n Hp.
    have Hh:= Hf (k+n).
    have Hp': pred_at tr (k + n) (λ (c : S) (_ : option L), locale_prop t c).
    { rewrite (pred_at_sum _ k) Haf /= //. }
    have [m Hm] := Hh Hp'.
    destruct Hm as (s & step & STEP & SAT). 
    do 3 eexists. split; eauto.
    erewrite trace_lookup_after; eauto.
    rewrite Nat.add_assoc. eauto. 
  Qed.

  Lemma fair_by_gen_cons (t: T) (c: S) (tid' : L) (r : trace S L):
      fair_by_gen t (c -[ tid' ]-> r) → fair_by_gen t r.
  Proof. intros H. by eapply (fair_by_gen_after t (c -[tid']-> r) r 1). Qed.

  (* Lemma fair_model_trace_cons_forall δ ℓ' r: *)
  Lemma fair_by_gen_cons_forall δ ℓ' r:
    (∀ ℓ, fair_by_gen ℓ (δ -[ℓ']-> r)) -> (∀ ℓ, fair_by_gen ℓ r).
  Proof. eauto using fair_by_gen_cons. Qed.

End GeneralizedFairness.


Section LocaleFairness.
  (* This is in fact a case of fair_by_gen with a simpler does_step relation,
     but formalizing it would require some routine work to adjust all the proofs.
     TODO: actually do it *)
  Context {S L T: Type}.
  Context (locale_prop: T -> S -> Prop).
  Context (does_step: T -> L -> Prop).

  Definition fairness_sat (t: T) (s: S) (ol: option L) :=
    ¬ locale_prop t s \/ exists ℓ, ol = Some ℓ /\ does_step t ℓ. 

  Definition fair_by (t: T) (otr: trace S L): Prop :=
    forall n, pred_at otr n (λ c _, locale_prop t c) ->
         exists m, pred_at otr (n + m) (fairness_sat t). 

  Lemma fair_by_after t tr tr' k:
    after k tr = Some tr' ->
    fair_by t tr -> fair_by t tr'.
  Proof.
    intros Haf Hf n Hp.
    have Hh:= Hf (k+n).
    have Hp': pred_at tr (k + n) (λ (c : S) (_ : option L), locale_prop t c).
    { rewrite (pred_at_sum _ k) Haf /= //. }
    have [m Hm] := Hh Hp'. exists m.
    red. by rewrite <- Nat.add_assoc, !(pred_at_sum _ k), Haf in Hm.
  Qed.

  Lemma fair_by_cons (t: T) (c: S) (tid' : L) (r : trace S L):
      fair_by t (c -[ tid' ]-> r) → fair_by t r.
  Proof. intros H. by eapply (fair_by_after t (c -[tid']-> r) r 1). Qed.

  (* Lemma fair_model_trace_cons_forall δ ℓ' r: *)
  Lemma fair_by_cons_forall δ ℓ' r:
    (∀ ℓ, fair_by ℓ (δ -[ℓ']-> r)) -> (∀ ℓ, fair_by ℓ r).
  Proof. eauto using fair_by_cons. Qed.

  (* TODO: try to unify validity lemmas by generalizing over step relation *)
  
End LocaleFairness.

Definition extrace Λ := trace (cfg Λ) (olocale Λ).

Section exec_trace.
  Context {Λ : language}.
  Context `{EqDecision (locale Λ)}.

  Definition locale_enabled (ζ : locale Λ) (c: cfg Λ) :=
    ∃ e, from_locale c.1 ζ = Some e ∧ to_val e = None.

  Definition tid_match (ζ : locale Λ) (oζ': olocale Λ) :=
    oζ' = Some ζ. 

  Definition fair_ex ζ (extr: extrace Λ): Prop :=
    fair_by locale_enabled tid_match ζ extr. 

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

Section TraceValid.
  Context {St L: Type}.
  Context (trans: St -> L -> St -> Prop). 

  Let traceM := trace St L. 

  Inductive trace_valid_ind (trace_valid_coind: traceM -> Prop) :
    traceM -> Prop :=
  | trace_valid_singleton δ: trace_valid_ind _ ⟨δ⟩
  | trace_valid_cons δ ℓ tr:
      trans δ ℓ (trfirst tr) ->
      trace_valid_coind tr →
      trace_valid_ind _ (δ -[ℓ]-> tr).

  Definition trace_valid := paco1 trace_valid_ind bot1.

  Lemma trace_valid_mono :
    monotone1 trace_valid_ind.
  Proof.
    unfold monotone1. intros x0 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve trace_valid_mono : paco.

  Lemma trace_valid_after (mtr mtr' : traceM) k :
    after k mtr = Some mtr' → trace_valid mtr → trace_valid mtr'.
  Proof.
    revert mtr mtr'.
    induction k; intros mtr mtr' Hafter Hvalid.
    { destruct mtr'; simpl in *; by simplify_eq. }
    punfold Hvalid.
    inversion Hvalid as [|??? Htrans Hval']; simplify_eq.
    eapply IHk; [done|].
    by inversion Hval'.
  Qed.

  Lemma trace_valid_tail s l (tr: traceM)
    (VALID': trace_valid (s -[l]-> tr)):
    trace_valid tr.
  Proof. by eapply trace_valid_after with (k := 1); eauto. Qed.

  Lemma trace_valid_cons_inv (tr: trace St L) s l
    (VALID: trace_valid (s -[l]-> tr)):
    trace_valid tr /\ trans s l (trfirst tr). 
  Proof using.
    punfold VALID. inversion VALID. subst.
    pclearbot. done. 
  Qed.

End TraceValid.


Definition mtrace (M:FairModel) := trace M (option M.(fmrole)).

Section model_traces.
  Context `{M: FairModel}.

  Definition role_enabled_model ρ (s: M) := ρ ∈ M.(live_roles) s.

  Definition role_match (ρ : fmrole M) (oρ': option $ fmrole M) :=
    oρ' = Some ρ. 

  Definition fair_model_trace ρ (mtr: mtrace M): Prop  :=
    fair_by role_enabled_model role_match ρ mtr. 

  Definition mtrace_valid := trace_valid (fmtrans M). 

End model_traces.


Definition FM_strong_lr (FM: FairModel) :=
  forall st ρ, ρ ∈ live_roles FM st <-> exists st', fmtrans FM st (Some ρ) st'.


Global Hint Resolve fair_by_cons: core.
Global Hint Resolve trace_valid_mono : paco.
