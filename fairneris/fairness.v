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


Lemma traces_match_flip {S1 S2 L1 L2}
      (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop)
      (trans2: S2 -> L2 -> S2 -> Prop)
      tr1 tr2 :
  traces_match Rℓ Rs trans1 trans2 tr1 tr2 ↔
  traces_match (flip Rℓ) (flip Rs) trans2 trans1 tr2 tr1.
Proof.
  split.
  - revert tr1 tr2. cofix CH.
    intros tr1 tr2 Hmatch. inversion Hmatch; simplify_eq.
    { by constructor. }
    constructor; [done..|].
    by apply CH.
  - revert tr1 tr2. cofix CH.
    intros tr1 tr2 Hmatch. inversion Hmatch; simplify_eq.
    { by constructor. }
    constructor; [done..|].
    by apply CH.
Qed.

Lemma traces_match_traces_implies {S1 S2 L1 L2}
      (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop)
      (trans2: S2 -> L2 -> S2 -> Prop)
      (P1 Q1 : S1 → option L1 → Prop)
      (P2 Q2 : S2 → option L2 → Prop)
      tr1 tr2 :
  traces_match Rℓ Rs trans1 trans2 tr1 tr2 →
  (∀ s1 s2 oℓ1 oℓ2, Rs s1 s2 →
                    match oℓ1, oℓ2 with
                    | Some ℓ1, Some ℓ2 => Rℓ ℓ1 ℓ2
                    | None, None => True
                    | _, _ => False
                    end →
                    P2 s2 oℓ2 → P1 s1 oℓ1) →
  (∀ s1 s2 oℓ1 oℓ2, Rs s1 s2 →
                    match oℓ1, oℓ2 with
                    | Some ℓ1, Some ℓ2 => Rℓ ℓ1 ℓ2
                    | None, None => True
                    | _, _ => False
                    end → Q1 s1 oℓ1 → Q2 s2 oℓ2) →
  trace_implies P1 Q1 tr1 → trace_implies P2 Q2 tr2.
Proof.
  intros Hmatch HP HQ Htr1.
  intros n Hpred_at.
  rewrite /pred_at in Hpred_at.
  assert (traces_match (flip Rℓ)
                       (flip Rs)
                       trans2 trans1
                       tr2 tr1) as Hmatch'.
  { by rewrite -traces_match_flip. }
  destruct (after n tr2) as [tr2'|] eqn:Htr2eq; [|done].
  eapply (traces_match_after) in Hmatch as (tr1' & Htr1eq & Hmatch); [|done].
  specialize (Htr1 n).
  rewrite {1}/pred_at in Htr1.
  rewrite Htr1eq in Htr1.
  destruct tr1' as [|s ℓ tr']; inversion Hmatch; simplify_eq; try by done.
  - assert (P1 s None) as HP1 by by eapply (HP _ _ _ None).
    destruct (Htr1 HP1) as [m Htr1'].
    exists m. rewrite pred_at_sum. rewrite pred_at_sum in Htr1'.
    destruct (after n tr1) as [tr1'|] eqn:Htr1eq'; [|done].
    eapply (traces_match_after) in Hmatch' as (tr2' & Htr2eq' & Hmatch'); [|done].
    rewrite Htr2eq'.
    rewrite /pred_at.
    rewrite /pred_at in Htr1'.
    destruct (after m tr1') as [tr1''|] eqn:Htr1eq''; [|done].
    eapply (traces_match_after) in Hmatch' as (tr2'' & Htr2eq'' & Hmatch''); [|done].
    rewrite Htr2eq''.
    destruct tr1''; inversion Hmatch''; simplify_eq; try by done.
    + by eapply (HQ _ _ None None).
    + by (eapply (HQ _ _ (Some _) _)).
  - assert (P1 s (Some ℓ)) as HP1 by by (eapply (HP _ _ _ (Some _))).
    destruct (Htr1 HP1) as [m Htr1'].
    exists m. rewrite pred_at_sum. rewrite pred_at_sum in Htr1'.
    destruct (after n tr1) as [tr1'|] eqn:Htr1eq'; [|done].
    eapply (traces_match_after) in Hmatch' as (tr2' & Htr2eq' & Hmatch'); [|done].
    rewrite Htr2eq'.
    rewrite /pred_at.
    rewrite /pred_at in Htr1'.
    destruct (after m tr1') as [tr1''|] eqn:Htr1eq''; [|done].
    eapply (traces_match_after) in Hmatch' as (tr2'' & Htr2eq'' & Hmatch''); [|done].
    rewrite Htr2eq''.
    destruct tr1''; inversion Hmatch''; simplify_eq; try by done.
    + by eapply (HQ _ _ None None).
    + by (eapply (HQ _ _ (Some _) _)).
Qed.


(* TODO: Move this *)
Lemma traces_match_after_None {S1 S2 L1 L2}
      (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop)
      (trans2: S2 -> L2 -> S2 -> Prop)
      tr1 tr2 n :
  traces_match Rℓ Rs trans1 trans2 tr1 tr2 ->
  after n tr2 = None ->
  after n tr1 = None.
Proof.
  revert tr1 tr2.
  induction n; intros tr1 tr2; [done|].
  move=> /= Hm Ha.
  destruct tr1; first by inversion Hm.
  inversion Hm; simplify_eq. by eapply IHn.
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
