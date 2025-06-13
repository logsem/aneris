From stdpp Require Import option countable gmap ssreflect.
From Paco Require Import paco1 paco2 pacotac.
From fairness Require Export inftraces trace_lookup utils.
From trillium.program_logic Require Export traces.
From trillium.program_logic Require Import language adequacy.

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


(** Definition of fairness for all kinds of traces *)
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

  Lemma fair_by_gen_cons_forall δ ℓ' r:
    (∀ ℓ, fair_by_gen ℓ (δ -[ℓ']-> r)) -> (∀ ℓ, fair_by_gen ℓ r).
  Proof. eauto using fair_by_gen_cons. Qed.

  Definition fair_by_gen'
    (t: T) (otr: trace S L) :=
    forall n, from_option (locale_prop t) False (otr S!! n) ->
    exists m s' step, otr !! (n + m) = Some (s', step) /\
                  fairness_sat_gen t s' step.

  Definition fair_by_gen'_strong
    (t: T) (otr: trace S L) :=
    forall n, from_option (locale_prop t) False (otr S!! n) ->
    exists m s' step, otr !! (n + m) = Some (s', step) /\
                  fairness_sat_gen t s' step /\
                  (forall k sk stepk, n <= k < n + m -> otr !! k = Some (sk, stepk) ->
                                 ¬ fairness_sat_gen t sk stepk).   

  Lemma fair_by_gen_equiv:
    forall (t: T) (otr: trace S L),
      fair_by_gen t otr <-> fair_by_gen' t otr.
  Proof.
    intros. rewrite /fair_by_gen /fair_by_gen'.    
    apply forall_proper. intros n.
    repeat setoid_rewrite pred_at_trace_lookup.
    apply Morphisms_Prop.iff_iff_iff_impl_morphism.
    2: { done. }
    destruct (otr S!! n); simpl; set_solver.
  Qed.

  Lemma fair_by_gen'_strong_equiv
    `{forall t s, Decision (locale_prop t s)} `{forall t s step, Decision (does_step t s step)}:
    forall (t: T) (otr: trace S L), fair_by_gen' t otr <-> fair_by_gen'_strong t otr.
  Proof. 
    intros. rewrite /fair_by_gen'_strong /fair_by_gen'. split.
    2: { intros FAIR ? EN. specialize (FAIR _ EN) as (?&?&?&?&?&?). eauto. }
    intros FAIR ? EN. specialize (FAIR _ EN) as [m_ STEP].
    pattern m_ in STEP. eapply min_prop_dec in STEP.
    2: { intros k. destruct (otr !! (n + k)) as [[s step]| ] eqn:K.
         2: { right. set_solver. }
         eapply Decision_iff_impl.
         { rewrite ex_det_iff; [rewrite ex_det_iff| ]; [reflexivity| ..].
           - intros ? [[=] ?]. subst. reflexivity.
           - intros ? (?& [=] & ?). subst. reflexivity. }
         apply and_dec; try solve_decision.
         by left. }
    clear dependent m_. destruct STEP as (m & (?&?&?&?) & MINm).
    do 3 eexists. repeat split; eauto.
    intros k * [LE LT] KTH. intros SAT.
    apply Nat.le_sum in LE as [d ->]. 
    specialize (MINm d ltac:(eauto)). lia.
  Qed.

End GeneralizedFairness.

Global Instance fair_by_gen_Proper {S L T: Type}:
  Proper ((eq ==> eq ==> iff) ==> (eq ==> eq ==> eq ==> iff) ==> eq ==> eq ==> iff) 
    (@fair_by_gen S L T).
Proof.
  intros ?? LOC_IFF ?? STEP_IFF.
  red. intros ?? ->. red. intros ?? ->.
  rewrite /fair_by_gen.
  apply forall_proper. intros.
  erewrite pred_at_iff.
  2: { intros. eapply LOC_IFF; reflexivity. }
  apply Morphisms_Prop.iff_iff_iff_impl_morphism; [reflexivity| ].
  repeat (apply exist_proper; intros).
  apply Morphisms_Prop.and_iff_morphism; [done| ].
  rewrite /fairness_sat_gen. 
  apply Morphisms_Prop.or_iff_morphism.
  - apply not_iff_compat, LOC_IFF; reflexivity.
  - apply STEP_IFF; reflexivity. 
Qed. 


Section LocaleFairness.
  (** TODO: this is in fact a case of fair_by_gen with a simpler does_step relation,
      but formalizing it would require some routine work to adjust all the proofs. *)
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

  Lemma fair_by_cons_forall δ ℓ' r:
    (∀ ℓ, fair_by ℓ (δ -[ℓ']-> r)) -> (∀ ℓ, fair_by ℓ r).
  Proof. eauto using fair_by_cons. Qed.

  Definition fair_by' (t: T) (otr: trace S L) :=
    forall n, from_option (locale_prop t) False (otr S!! n) ->
    exists m s', otr S!! (n + m) = Some s' /\
             fairness_sat t s' (otr L!! (n + m)).

  Definition fair_by'_strong (t: T) (otr: trace S L) :=
    forall n, from_option (locale_prop t) False (otr S!! n) ->
    exists m, ClassicalFacts.Minimal 
           (fun d => exists s', otr S!! (n + d) = Some s' /\ fairness_sat t s' (otr L!! (n + d))) m.

  Lemma fair_by_equiv:
    forall (t: T) (otr: trace S L), fair_by t otr <-> fair_by' t otr.
  Proof.
    intros. rewrite /fair_by /fair_by'.
    apply forall_proper. intros n.
    repeat setoid_rewrite pred_at_trace_lookup.
    apply Morphisms_Prop.iff_iff_iff_impl_morphism; [| done].    
    destruct (otr S!! n); simpl; set_solver.
  Qed.

  Global Instance fairness_sat_dec
    `{forall t s, Decision (locale_prop t s)}
    `{forall t l, Decision (does_step t l)}:
    forall t s ol, Decision (fairness_sat t s ol).
  Proof using.
    intros. rewrite /fairness_sat.
    destruct (decide (locale_prop t s)) as [EN| ]; [| left; tauto]. 
    destruct ol as [l| ]; [| right; set_solver].
    destruct (decide (does_step t l)).
    - left. eauto.
    - right. set_solver.
  Qed.

  Lemma fair_by'_strenghten
    `{forall t s ol, Decision (fairness_sat t s ol)}:
    forall (t: T) (otr: trace S L), fair_by' t otr <-> fair_by'_strong t otr.
  Proof using.
    intros. rewrite /fair_by' /fair_by'_strong.
    apply forall_proper. intros n.
    apply impl_iff_intro. intros Pn. destruct (otr S!! n) eqn:NTH; [| done].
    simpl in Pn.
    split.
    2: { intros (?&?&?). eauto. }
    intros [m EX]. pattern m in EX. apply min_prop_dec_impl in EX.
    { destruct EX. eauto. }
    intros i. destruct (otr S!! (n + i)) eqn:NEXT.
    2: { right. set_solver. }
    destruct (decide (fairness_sat t s0 (otr L!! (n + i)))).
    - left. eauto.
    - right. set_solver.
  Qed.

  Definition weakly_fair (t: T) (tr: trace S L) :=
    forall n,
      is_Some (tr S!! n) ->
      (** using True as default to support finite traces *)
      (forall k, n <= k -> from_option (locale_prop t) True (tr S!! k)) ->
    exists m ℓ, tr L!! (n + m) = Some ℓ /\ does_step t ℓ. 

  Require Import Coq.Logic.Classical.
  
  Lemma fair_by'_weakly_fair τ tr:
    fair_by' τ tr <-> weakly_fair τ tr.
  Proof using.
    rewrite /fair_by' /weakly_fair. apply forall_proper. intros n.
    split.
    - intros FAIR [δ NTH] ALW.
      pose proof (ALW n ltac:(lia)) as ENn. rewrite NTH /= in ENn.
      rewrite NTH in FAIR. ospecialize (FAIR ltac:(done)).
      destruct FAIR as (d & δ' & MTH & SAT).
      destruct SAT as [DIS | STEP]; [| by eauto].
      specialize (ALW (n + d) ltac:(lia)). by rewrite MTH in ALW.
    - intros FAIR.
      destruct (tr S!! n) as [δ | ] eqn:NTH; [| done]. simpl in *.
      intros ENn. specialize (FAIR ltac:(done)).
      destruct (classic (∀ k, n ≤ k → from_option (locale_prop τ) True (tr S!! k))).
      { specialize (FAIR H). destruct FAIR as (m & ℓ & MTHl & STEP).
        pose proof MTHl as [[? MTH] _]%mk_is_Some%label_lookup_states.
        do 2 eexists. split; eauto. right. eauto. }
      apply not_forall_exists_not in H as [m DIS].
      apply imply_to_and in DIS as [LE DIS].
      destruct (tr S!! m) as [? | ] eqn:MTH; [| done]. simpl in *.
      apply Nat.le_sum in LE as [? ->].
      do 2 eexists. split; eauto.
      by left.
  Qed.

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

  Definition extrace_fairly_terminating (extr : extrace Λ) :=
    extrace_valid extr →
    (∀ tid, fair_ex tid extr) →
    terminating_trace extr.

End exec_trace.


Definition mtrace (M:FairModel) := trace M (option M.(fmrole)).

Section model_traces.
  Context `{M: FairModel}.

  Definition role_enabled_model ρ (s: M) := ρ ∈ M.(live_roles) s.

  Global Instance rem_dec: forall ρ st, Decision (role_enabled_model ρ st).
  Proof. 
    intros. rewrite /role_enabled_model. solve_decision.
  Qed.

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
