From trillium.program_logic Require Export adequacy.
From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.

Require Import
        Coq.Relations.Relation_Definitions
        Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Wf_nat.

Record FairModel : Type := {
  fmstate:> Type;
  fmstate_inhabited: Inhabited fmstate;

  fmrole: Type;
  fmrole_eqdec: EqDecision fmrole;
  fmrole_countable: Countable fmrole;
  fmrole_inhabited: Inhabited fmrole;

  fmtrans: fmstate -> option fmrole -> fmstate -> Prop;

  live_roles: fmstate -> gset fmrole;
  fm_live_spec:
     forall s ρ s', fmtrans s (Some ρ) s' -> ρ ∈ live_roles s;
  fm_live_preserved:
     forall ρ' s ρ s', fmtrans s (Some ρ) s' -> ρ' ∈ live_roles s -> ρ ≠ ρ' ->  ρ' ∈ live_roles s';
  fuel_limit: fmstate -> nat;
}.
Arguments fuel_limit {_}.

#[global] Existing Instance fmrole_eqdec.
#[global] Existing Instance fmrole_countable.
#[global] Existing Instance fmrole_inhabited.
#[global] Existing Instance fmstate_inhabited.

Section fairness.
  Context {Λ : language}.
  Context `{Countable (locale Λ)}.

  Record LiveState (M: FairModel) := MkLiveState {
    ls_under:> M.(fmstate);

    ls_fuel: gmap M.(fmrole) nat;
    ls_fuel_dom: M.(live_roles) ls_under ⊆ dom ls_fuel;

    ls_mapping: gmap M.(fmrole) (locale Λ); (* maps roles to thread id *)

    ls_same_doms: dom ls_mapping = dom ls_fuel;
  }.

  Arguments ls_under {_}.
  Arguments ls_fuel {_}.
  Arguments ls_fuel_dom {_}.
  Arguments ls_mapping {_}.
  Arguments ls_same_doms {_}.

  Lemma ls_mapping_dom M (m: LiveState M):
    M.(live_roles) m.(ls_under) ⊆ dom m.(ls_mapping).
  Proof. rewrite ls_same_doms. apply ls_fuel_dom. Qed.

  Inductive FairLabel {Roles} :=
  | Take_step: Roles -> locale Λ -> FairLabel
  | Silent_step: locale Λ -> FairLabel
  | Config_step: FairLabel
  .

  Definition less (x y: option nat) :=
    match x, y with
    | Some x, Some y => x < y
    | _, _ => False
    end.

  Inductive must_decrease {M: FairModel} (ρ': M.(fmrole)) (oρ: option M.(fmrole)) (a b: LiveState M):
    olocale Λ -> Prop :=
  | Same_tid tid (Hneqρ: Some ρ' ≠ oρ) (Hsametid: Some tid = (ls_mapping a) !! ρ'):
      must_decrease ρ' oρ a b (Some tid)
  | Change_tid otid (Hneqtid: a.(ls_mapping) !! ρ' ≠ b.(ls_mapping) !! ρ')
               (Hissome: is_Some (b.(ls_mapping) !! ρ')):
    must_decrease ρ' oρ a b otid
  | Zombie otid (Hismainrole: oρ = Some ρ') (Hnotalive: ρ' ∉ live_roles _ b) (Hnotdead: ρ' ∈ dom b.(ls_fuel)):
    must_decrease ρ' oρ a b otid
  .

  Definition oleq a b :=
    match a, b with
    | Some x, Some y => x ≤ y
    | _, _ => False
    end.

  Definition oless a b :=
    match a, b with
    | Some x, Some y => x < y
    | _, _ => False
    end.

  Lemma oleq_oless a b: oless a b -> oleq a b.
  Proof.
    destruct a; destruct b=>//. unfold oless, oleq. lia.
  Qed.

  Definition fuel_decr {M: FairModel} (tid: olocale Λ) (oρ: option M.(fmrole)) (a b: LiveState M) :=
    forall ρ', ρ' ∈ dom a.(ls_fuel) -> ρ' ∈ dom b.(ls_fuel) →
          must_decrease ρ' oρ a b tid
          -> oless (b.(ls_fuel) !! ρ') (a.(ls_fuel) !! ρ').

  Definition fuel_must_not_incr {M: FairModel} oρ (a b: LiveState M) :=
    ∀ ρ', ρ' ∈ dom a.(ls_fuel) -> Some ρ' ≠ oρ ->
          (oleq ((ls_fuel b) !! ρ') ((ls_fuel a) !! ρ')
                ∨ (ρ' ∉ dom b.(ls_fuel) ∧ ρ' ∉ M.(live_roles) a.(ls_under))).

  Definition ls_trans {M} (a: LiveState M) ℓ (b: LiveState M): Prop :=
    match ℓ with
    | Take_step ρ tid =>
      M.(fmtrans) a (Some ρ) b
      ∧ a.(ls_mapping) !! ρ = Some tid
      ∧ fuel_decr (Some tid) (Some ρ) a b
      ∧ fuel_must_not_incr (Some ρ) a b
      ∧ (ρ ∈ live_roles _ b -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ (∀ ρ, ρ ∈ dom b.(ls_fuel) ∖ dom a.(ls_fuel) -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ dom b.(ls_fuel) ∖ dom a.(ls_fuel) ⊆ live_roles _ b ∖ live_roles _ a
    | Silent_step tid =>
      (∃ ρ, a.(ls_mapping) !! ρ = Some tid)
      ∧ fuel_decr (Some tid) None a b
      ∧ fuel_must_not_incr None a b
      ∧ dom b.(ls_fuel) ⊆ dom a.(ls_fuel)
      ∧ a.(ls_under) = b.(ls_under)
    | Config_step =>
      M.(fmtrans) a None b
      ∧ fuel_decr None None a b
      ∧ fuel_must_not_incr None a b
      ∧ (∀ ρ, ρ ∈ M.(live_roles) b ∖ M.(live_roles) a -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ False (* TODO: add support for config steps later! *)
    end.

  Definition fair_model M: Model := {|
    mstate := LiveState M;
    mlabel  := @FairLabel M.(fmrole);
    mtrans := ls_trans;
  |}.

  Definition tids_smaller {M: FairModel} (c : list (expr Λ)) (δ: LiveState M) :=
    ∀ ρ ζ, δ.(ls_mapping) !! ρ = Some ζ -> is_Some (from_locale c ζ).

  Program Definition initial_ls {M: FairModel} (s0: M) (ζ0: locale Λ): LiveState M :=
    {| ls_under := s0;
       ls_fuel := gset_to_gmap (fuel_limit s0) (M.(live_roles) s0);
       ls_mapping := gset_to_gmap ζ0 (M.(live_roles) s0);
    |}.
  Next Obligation. intros ???. apply reflexive_eq. rewrite dom_gset_to_gmap //. Qed.
  Next Obligation. intros ???. apply reflexive_eq. rewrite !dom_gset_to_gmap //. Qed.

  Definition labels_match {M} (oζ : olocale Λ) (ℓ : @FairLabel (M.(fmrole))) :=
    match oζ, ℓ with
    | None, Config_step => True
    | Some ζ, Silent_step ζ' => ζ = ζ'
    | Some ζ, Take_step ρ ζ' => ζ = ζ'
    | _, _ => False
    end.

  Delimit Scope trace_scope with trace.

  CoInductive trace (S L: Type) :=
  | tr_singl (s: S)
  | tr_cons (s: S) (ℓ: L) (r: trace S L).

  Bind Scope trace_scope with trace.

  Arguments tr_singl {_} {_}, _.
  Arguments tr_cons {_} {_} _ _ _%trace.
  Notation "⟨ s ⟩" := (tr_singl s) : trace_scope.
  Notation "s -[ ℓ ]->  r" := (tr_cons s ℓ r) (at level 33) : trace_scope.
  Open Scope trace.

  Lemma trace_unfold_fold {S L} (tr: trace S L) :
    tr = match tr with
         | ⟨s⟩ => ⟨s⟩
         | s -[ℓ]-> rest => s -[ℓ]-> rest
         end.
  Proof. destruct tr; trivial. Qed.

  Definition trfirst {S L} (tr: trace S L): S :=
    match tr with
    | ⟨s⟩ => s
    | s -[ℓ]-> r => s
    end.

  Section after.
    Context {St L: Type}.

    Fixpoint after (n: nat) (t: trace St L) : option (trace St L):=
      match n with
      | 0 => Some t
      | Datatypes.S n =>
        match t with
        | ⟨ s ⟩ => None
        | s -[ ℓ ]-> xs => after n xs
        end
      end.

    Definition pred_at (tr: trace St L) (n: nat) (P: St -> option L -> Prop): Prop :=
      match after n tr with
      | None => False
      | Some ⟨s⟩ => P s None
      | Some (s -[ℓ]-> _) => P s (Some ℓ)
      end.

    Lemma after_sum m: forall k (tr: trace St L),
        after (k+m) tr =
        match after m tr with
        | None => None
        | Some tr' => after k tr'
        end.
    Proof.
      induction m.
      - intros k tr. by have ->: k+0=k by lia.
      - intros k tr. simpl.
        have -> /=: (k + S m) = S (k+m) by lia.
        destruct tr as [s|s l r]; simpl; auto.
    Qed.

    Lemma after_sum' m: forall k (tr: trace St L),
        after (k+m) tr =
        match after k tr with
        | None => None
        | Some tr' => after m tr'
        end.
    Proof. intros. rewrite Nat.add_comm. apply after_sum. Qed.

    Lemma pred_at_sum P n m tr:
      pred_at tr (n + m) P <->
      match after n tr with
      | None => False
      | Some tr' => pred_at tr' m P
      end.
    Proof.
      rewrite /pred_at after_sum'.
        by destruct (after n tr).
    Qed.

    Lemma pred_at_sum' P n m tr:
      pred_at tr (n + m) P <->
      match after m tr with
      | None => False
      | Some tr' => pred_at tr' n P
      end.
    Proof.
      rewrite /pred_at after_sum.
        by destruct (after m tr).
    Qed.

    Lemma pred_at_0 s ℓ r P:
      pred_at (s -[ℓ]-> r) 0 P <-> P s (Some ℓ).
    Proof. by unfold pred_at. Qed.

    Lemma pred_at_S s ℓ r n P:
      pred_at (s -[ℓ]-> r) (S n) P <-> pred_at r n P.
    Proof. by unfold pred_at. Qed.

    Definition infinite_trace tr :=
      forall n, is_Some (after n tr).

    Definition terminating_trace tr :=
      ∃ n, after n tr = None.

    Lemma terminating_trace_cons s ℓ tr:
      terminating_trace tr -> terminating_trace (s -[ℓ]-> tr).
    Proof. intros [n Hterm]. by exists (1+n). Qed.

    Lemma infinite_trace_after n tr:
      infinite_trace tr -> match after n tr with
                          | None => False
                          | Some tr' => infinite_trace tr'
                          end.
    Proof.
      intros Hinf. have [tr' Htr'] := (Hinf n). rewrite Htr'.
      intros m.
      have Hnm := Hinf (n+m). rewrite after_sum' Htr' // in Hnm.
    Qed.

    Lemma infinite_cons s ℓ r:
      infinite_trace (s -[ℓ]-> r) -> infinite_trace r.
    Proof.
      intros Hinf n. specialize (Hinf (1+n)).
      rewrite (after_sum' _ 1) // in Hinf.
    Qed.
  End after.
End fairness.

Arguments ls_under {_ _}.
Arguments ls_fuel {_ _}.
Arguments ls_fuel_dom {_ _}.
Arguments ls_mapping {_ _}.
Arguments ls_mapping_dom {_ _}.

Delimit Scope trace_scope with trace.
Arguments tr_singl {_} {_}, _.
Arguments tr_cons {_} {_} _ _ _%trace.
Notation "⟨ s ⟩" := (tr_singl s) : trace_scope.
Notation "s -[ ℓ ]->  r" := (tr_cons s ℓ r) (at level 33) : trace_scope.
Open Scope trace.

Section simulation.
  Context {L1 L2 S1 S2: Type}.
  Context (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop).
  Context (trans1: S1 -> L1 -> S1 -> Prop).
  Context (trans2: S2 -> L2 -> S2 -> Prop).

  CoInductive traces_match : trace S1 L1 -> trace S2 L2 -> Prop :=
  | trace_match_singl s1 s2: Rs s1 s2 -> traces_match ⟨ s1 ⟩ ⟨ s2 ⟩
  | trace_match_cons s1 ℓ1 r1 s2 ℓ2 r2 : Rℓ ℓ1 ℓ2 -> Rs s1 s2 ->
                                         trans1 s1 ℓ1 (trfirst r1) ->
                                         trans2 s2 ℓ2 (trfirst r2) ->
                                         traces_match r1 r2 ->
                                         traces_match (s1 -[ℓ1]-> r1) (s2 -[ℓ2]-> r2).

  Lemma traces_match_after tr1 tr2 n tr2':
    traces_match tr1 tr2 ->
    after n tr2 = Some tr2' ->
    (exists tr1', after n tr1 = Some tr1' ∧ traces_match tr1' tr2').
  Proof.
    revert tr1 tr2.
    induction n; intros tr1 tr2.
    { simpl. intros. exists tr1. simplify_eq. done. }
    move=> /= Hm Ha. destruct tr2 as [|s ℓ tr2''] eqn:Heq; first done.
    destruct tr1; first by inversion Hm.
    inversion Hm; simplify_eq. by eapply IHn.
  Qed.

  Lemma traces_match_first tr1 tr2:
    traces_match tr1 tr2 ->
    Rs (trfirst tr1) (trfirst tr2).
  Proof. intros Hm. inversion Hm; done. Qed.

End simulation.

Section execs_and_traces.
  Context {S L: Type}.

  CoInductive exec_trace_match: finite_trace S L -> inflist (L * S) -> trace S L -> Prop :=
  | exec_trace_match_singl ft s: trace_last ft = s -> exec_trace_match ft infnil ⟨s⟩
  | exec_trace_match_cons ft s ℓ ift tr:
      exec_trace_match (trace_extend ft ℓ s) ift tr ->
      exec_trace_match ft (infcons (ℓ, s) ift) (trace_last ft -[ℓ]-> tr).

  CoFixpoint to_trace (s: S) (il: inflist (L * S)) : trace S L :=
    match il with
    | infnil => ⟨ s ⟩
    | infcons (ℓ, s') rest => s -[ℓ]-> (to_trace s' rest)
    end.

  Lemma to_trace_spec (fl: finite_trace S L) (il: inflist (L * S)):
    exec_trace_match fl il (to_trace (trace_last fl) il).
  Proof.
    revert fl il. cofix CH. intros s il.
    rewrite (trace_unfold_fold (to_trace _ il)). destruct il as [| [ℓ x]?]; simpl in *.
    - by econstructor.
    - econstructor. have ->: x = trace_last (trace_extend s ℓ x) by done.
      apply CH.
  Qed.

  Lemma to_trace_singleton s (il: inflist (L * S)):
    exec_trace_match (trace_singleton s) il (to_trace s il).
  Proof. apply to_trace_spec. Qed.

  CoFixpoint from_trace (tr: trace S L): inflist (L * S) :=
    match tr with
    | ⟨ s ⟩ => infnil
    | s -[ℓ]-> tr' => infcons (ℓ, trfirst tr') (from_trace tr')
    end.

  Lemma from_trace_spec (fl: finite_trace S L) (tr: trace S L):
    trace_last fl = trfirst tr ->
    exec_trace_match fl (from_trace tr) tr.
  Proof.
    revert fl tr. cofix CH. intros fl tr Heq.
    rewrite (inflist_unfold_fold (from_trace tr)). destruct tr; simpl in *.
    - by econstructor.
    - rewrite -Heq. econstructor. apply CH; done.
  Qed.

End execs_and_traces.

(* Basically, soundness of the logic and the lemmas above tell us that we have a program
   trace and a model trace which are related by traces_match labels_math!

   We now prove that this relation transports the properties we care about; the first
   place of which is fairness.
 *)

(* Definition of fairness for both kinds of traces *)


Definition extrace {Λ} := trace (cfg Λ) (olocale Λ).

Section exec_trace.
  Context {Λ : language}.
  Context `{EqDecision (locale Λ)}.

  Definition locale_enabled (ζ : locale Λ) (c: cfg Λ) :=
    ∃ e, from_locale c.1 ζ = Some e ∧ to_val e = None.

  Definition fair_ex ζ (extr: @extrace Λ): Prop :=
    forall n, pred_at extr n (λ c _, locale_enabled ζ c) ->
         ∃ m, pred_at extr (n+m) (λ c _, ¬locale_enabled ζ c)
              ∨ pred_at extr (n+m) (λ _ otid, otid = Some (Some ζ)).

  Lemma fair_ex_after ζ tr tr' k:
    after k tr = Some tr' ->
    fair_ex ζ tr -> fair_ex ζ tr'.
  Proof.
    intros Haf Hf n Hp.
    have Hh:= Hf (k+n).
    have Hp': pred_at tr (k + n) (λ (c : cfg Λ) (_ : option (olocale Λ)), locale_enabled ζ c).
    { rewrite (pred_at_sum _ k) Haf /= //. }
    have [m Hm] := Hh Hp'. exists m.
    by rewrite <- Nat.add_assoc, !(pred_at_sum _ k), Haf in Hm.
  Qed.

  Lemma fair_ex_cons tid c tid' r:
    fair_ex tid (c -[tid']-> r) -> fair_ex tid r.
  Proof. intros H. by eapply (fair_ex_after tid (c -[tid']-> r) r 1). Qed.

  CoInductive extrace_valid: extrace (Λ := Λ) -> Prop :=
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

  Lemma from_trace_preserves_validity (extr: extrace) ex:
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

  Lemma from_trace_preserves_validity_singleton (extr: extrace):
    extrace_valid extr ->
    valid_inf_exec (trace_singleton (trfirst extr)) (from_trace extr).
  Proof.
    intros ?. eapply from_trace_preserves_validity; eauto. econstructor.
  Qed.

End exec_trace.


Definition auxtrace {Λ: language} {M: FairModel} := trace (@LiveState Λ M) (@FairLabel Λ M.(fmrole)).

Section aux_trace.
  Context {Λ: language}.
  Context {M: FairModel}.

  Definition role_enabled ρ (δ: @LiveState Λ M) := ρ ∈ M.(live_roles) δ.

  Definition fair_aux ρ (auxtr: auxtrace): Prop  :=
    forall n, pred_at auxtr n (λ δ _, role_enabled ρ δ) ->
         ∃ m, pred_at auxtr (n+m) (λ δ _, ¬role_enabled ρ δ)
              ∨ pred_at auxtr (n+m) (λ _ ℓ, ∃ tid, ℓ = Some (Take_step ρ tid)).

  Lemma fair_aux_after ρ auxtr n auxtr':
    fair_aux ρ auxtr ->
    after n auxtr = Some auxtr' ->
    fair_aux ρ auxtr'.
  Proof.
    rewrite /fair_aux => Hfair Hafter m Hpa.
    specialize (Hfair (n+m)).
    rewrite -> (pred_at_sum _ n) in Hfair. rewrite Hafter in Hfair.
    destruct (Hfair Hpa) as (p&Hp).
    exists (p). by rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n), Hafter in Hp.
  Qed.

  CoInductive auxtrace_valid: @auxtrace Λ M -> Prop :=
  | auxtrace_valid_singleton δ: auxtrace_valid ⟨δ⟩
  | auxtrace_valid_cons δ ℓ tr:
      ls_trans δ ℓ (trfirst tr) ->
      auxtrace_valid tr →
      auxtrace_valid (δ -[ℓ]-> tr).

  Lemma auxtrace_valid_forall (tr: auxtrace) :
    auxtrace_valid tr ->
    ∀ n, match after n tr with
         | Some ⟨ _ ⟩ | None => True
         | Some (δ -[ℓ]-> tr') => ls_trans δ ℓ (trfirst tr')
         end.
  Proof.
    intros Hval n. revert tr Hval. induction n as [|n]; intros tr Hval;
      destruct (after _ tr) as [trn|] eqn: Heq =>//; simpl in Heq;
      simplify_eq; destruct trn =>//; inversion Hval; simplify_eq; try done.
    specialize (IHn _ H0) (* TODO *). rewrite Heq in IHn. done.
  Qed.

End aux_trace.

(* Adapted from Arthur Azevedo De Amorim *)
Section lex_ind.
 Section Lexicographic.

   Variables (A B : Type) (leA : relation A) (leB : relation B).

   Inductive lexprod : A * B -> A * B -> Prop :=
   | left_lex  : forall x x' y y', leA x x' -> lexprod (x, y) (x', y')
   | right_lex : forall x y y',    leB y y' -> lexprod (x, y) (x, y').

   Theorem wf_trans :
     transitive _ leA ->
     transitive _ leB ->
     transitive _ lexprod.
   Proof.
     intros tA tB [x1 y1] [x2 y2] [x3 y3] H.
     inversion H; subst; clear H.
     - intros H.
       inversion H; subst; clear H; apply left_lex; now eauto.
    - intros H.
    inversion H; subst; clear H.
    + now apply left_lex.
    + now apply right_lex; eauto.
    Qed.

    Theorem wf_lexprod :
    well_founded leA ->
    well_founded leB ->
    well_founded lexprod.
    Proof.
      intros wfA wfB [x y]. generalize dependent y.
      induction (wfA x) as [x _ IHx]; clear wfA.
      intros y.
      induction (wfB y) as [y _ IHy]; clear wfB.
      constructor.
      intros [x' y'] H.
      now inversion H; subst; clear H; eauto.
    Qed.

 End Lexicographic.

 Definition lt_lex : relation (nat * nat) := fun '(x, y) '(x', y') =>
                                            x < x' ∨ (x = x' ∧ y <= y').

 #[global] Instance lt_lex_partial_order : @PartialOrder (nat * nat) lt_lex.
 Proof.
   constructor.
   + constructor.
     * move=> [x y]. right; split; reflexivity.
     * move=> [x1 y1] [x2 y2] [x3 y3] [H1|H1] [H2|H2]; unfold lt_lex; lia.
   + move=> [x1 y1] [x2 y2] [?|[??]] [H2|[??]]; f_equal; try lia.
 Qed.

 Definition myrel : relation (nat * nat) :=
    lexprod _ _ lt lt.

 Lemma lex_ind:
   ∀ (n : nat*nat) (P : nat*nat → Prop),
     (∀ n0 : nat*nat, (∀ m : nat*nat, (strict lt_lex) m n0 → P m) → P n0) → P n.
 Proof.
   assert (well_founded myrel) as Hwf.
   { apply wf_lexprod; apply lt_wf. }
   induction n using (well_founded_ind Hwf).
   intros P HI. apply HI =>//. intros m [Ha Hb].
   apply H =>//. destruct n as [n1 n2]; destruct m as [m1 m2].
   unfold strict, lt_lex in *.
   destruct Ha as [Ha | [Ha1 Ha2]].
   - constructor 1. done.
    - rewrite Ha1. constructor 2. lia.
 Qed.

End lex_ind.

Ltac SS :=
  epose proof ls_fuel_dom;
  (* epose proof ls_mapping_dom; *)
  set_solver.

Section fairness_preserved.
  Context {M: FairModel}.
  Context {Λ: language}.
  Context `{Countable (locale Λ)}.

  Definition live_tids (c: cfg Λ) (δ: LiveState M): Prop :=
    (∀ ρ ζ, δ.(ls_mapping (Λ := Λ)) !! ρ = Some ζ -> is_Some (from_locale c.1 ζ)) ∧
    ∀ ζ e, from_locale c.1 ζ = Some e -> (to_val e ≠ None) ->
             ∀ ρ, δ.(ls_mapping) !! ρ ≠ Some ζ.

  Notation exaux_traces_match :=
    (@traces_match (olocale Λ)
                   (fair_model M).(mlabel)
                   (cfg Λ)
                   (LiveState M)
                   labels_match
                   live_tids
                   locale_step
                   ls_trans
    ).

  Lemma exaux_preserves_validity extr auxtr:
    exaux_traces_match extr auxtr ->
    auxtrace_valid auxtr.
  Proof.
    revert extr auxtr. cofix CH. intros extr auxtr Hmatch.
    inversion Hmatch; first by constructor.
    constructor =>//. by eapply CH.
  Qed.

  Lemma exaux_preserves_termination extr auxtr:
    exaux_traces_match extr auxtr ->
    terminating_trace auxtr ->
    terminating_trace extr.
  Proof.
    intros Hmatch [n HNone].
    revert extr auxtr Hmatch HNone. induction n as [|n IHn]; first done.
    intros extr auxtr Hmatch HNone.
    replace (S n) with (1 + n) in HNone =>//.
    rewrite (after_sum' _ 1) in HNone.
    destruct auxtr as [s| s ℓ auxtr'];
      first by inversion Hmatch; simplify_eq; exists 1.
    simpl in HNone.
    inversion Hmatch; simplify_eq.
    apply terminating_trace_cons.
    eapply IHn =>//.
  Qed.

  Lemma traces_match_labels {tid ℓ c δ rex raux}:
    exaux_traces_match (c -[Some tid]-> rex) (δ -[ℓ]-> raux) ->
    ((∃ ρ, ℓ = Take_step ρ tid) ∨ (ℓ = Silent_step tid)).
  Proof.
    intros Hm. inversion Hm as [|?????? Hlab]; simplify_eq.
    destruct ℓ; eauto; inversion Hlab; simplify_eq; eauto.
  Qed.

  Lemma mapping_live_role (δ: LiveState M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_mapping (Λ := Λ) δ !! ρ).
  Proof. rewrite -elem_of_dom ls_same_doms. SS. Qed.
  Lemma fuel_live_role (δ: LiveState M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_fuel (Λ := Λ) δ !! ρ).
  Proof. rewrite -elem_of_dom. SS. Qed.

  Local Hint Resolve mapping_live_role: core.
  Local Hint Resolve fuel_live_role: core.

  Lemma match_locale_enabled extr auxtr ζ ρ:
    exaux_traces_match extr auxtr ->
    ls_mapping (trfirst auxtr) !! ρ = Some ζ ->
    locale_enabled ζ (trfirst extr).
  Proof.
    intros Hm Hloc.
    rewrite /locale_enabled. have [HiS Hneqloc] := traces_match_first _ _ _ _ _ _ Hm.
    have [e Hein] := (HiS _ _ Hloc). exists e. split; first done.
    destruct (to_val e) eqn:Heqe =>//.
    exfalso. specialize (Hneqloc ζ e Hein). rewrite Heqe in Hneqloc.
    have Hv: Some v ≠ None by []. by specialize (Hneqloc Hv ρ).
  Qed.

  Lemma pred_first_aux (tr: auxtrace) (P: @LiveState Λ M -> Prop):
    match tr with
    | ⟨ s ⟩ | s -[ _ ]-> _ => P s
    end <-> P (trfirst tr).
  Proof. destruct tr; done. Qed.

  Lemma pred_first_ex (tr: extrace) (P: cfg Λ -> Prop):
    match tr with
    | ⟨ s ⟩ | s -[ _ ]-> _ => P s
    end <-> P (trfirst tr).
  Proof. destruct tr; done. Qed.

  Local Hint Resolve match_locale_enabled: core.
  Local Hint Resolve pred_first_aux: core.
  Local Hint Resolve pred_first_ex: core.

  Definition fairness_induction_stmt ρ fm f m ζ extr auxtr δ c :=
      (infinite_trace extr ->
       (forall ζ, fair_ex ζ extr) ->
       fm = (f, m) ->
       exaux_traces_match extr auxtr ->
       c = trfirst extr -> δ = trfirst auxtr ->
       δ.(ls_fuel) !! ρ = Some f ->
       δ.(ls_mapping) !! ρ = Some ζ ->
       (pred_at extr m (λ c _, ¬locale_enabled ζ c) ∨ pred_at extr m (λ _ oζ, oζ = Some (Some ζ))) ->
      ∃ M, pred_at auxtr M (λ δ _, ¬role_enabled ρ δ)
           ∨ pred_at auxtr M (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0))).

  Local Lemma case1 ρ f m (extr' : @extrace Λ) auxtr' δ ℓ :
    (∀ m0 : nat * nat,
         strict lt_lex m0 (f, m)
         → ∀ (f m: nat) (ζ: locale Λ) (extr : extrace) (auxtr : auxtrace)
             (δ : LiveState M) (c : cfg Λ), fairness_induction_stmt ρ m0 f m ζ extr auxtr δ c) ->
    (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) ->
    exaux_traces_match extr' auxtr' ->
    infinite_trace extr' ->
    ls_fuel δ !! ρ = Some f ->
    (∀ ζ, fair_ex ζ extr') ->
    ∃ M0 : nat,
      pred_at (δ -[ ℓ ]-> auxtr') M0
              (λ δ0 _, ¬ role_enabled ρ δ0)
      ∨ pred_at (δ -[ ℓ ]-> auxtr') M0
                (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
    Proof.
      intros IH Hdec Hmatch Hinf Hsome Hfair.
      unfold oless in Hdec.
      simpl in *.
      rewrite -> Hsome in *.
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq.
      - destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
        { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. }
        have [ζ' Hζ'] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.

        have Hloc'en: pred_at extr' 0 (λ (c : cfg Λ) (_ : option (olocale Λ)),
                          locale_enabled ζ' c).
        { rewrite /pred_at /= pred_first_ex. eauto. }

        have [p Hp] := (Hfair ζ' 0 Hloc'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ (δ0 : LiveState M) _, ¬ role_enabled ρ δ0)
                                  ∨ pred_at auxtr' M0 (λ (_ : LiveState M) ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ p _ extr'); eauto.
          Unshelve. unfold strict, lt_lex. specialize (Hdec ltac:(by eapply elem_of_dom_2)). lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
      - exists 1. left. rewrite /pred_at /=. rewrite /role_enabled.
        destruct auxtr' =>/=.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
    Qed.

  Lemma fairness_preserved_ind ρ:
    ∀ fm f m ζ (extr: @extrace Λ) (auxtr: auxtrace) δ c,
      fairness_induction_stmt ρ fm f m ζ extr auxtr δ c.
  Proof.
    induction fm as [fm IH] using lex_ind.
    intros f m ζ extr auxtr δ c Hexinfin Hfair -> Htm -> -> Hfuel Hmapping Hexen.
    destruct extr as [|c ζ' extr'] eqn:Heq.
    { have [??] := Hexinfin 1. done. }
    have Hfair': (forall ζ, fair_ex ζ extr').
    { intros. by eapply fair_ex_cons. }
    destruct auxtr as [|δ ℓ auxtr']; first by inversion Htm.
    destruct (decide (ρ ∈ live_roles M δ)) as [Hρlive|]; last first.
    { exists 0. left. unfold pred_at. simpl. intros contra. eauto. }
    destruct (decide (Some ζ = ζ')) as [Hζ|Hζ].
    - rewrite <- Hζ in *.
      destruct (traces_match_labels Htm) as [[ρ' ->]| ->]; last first.
      + inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        unfold ls_trans in Hls.
        destruct Hls as (? & Hlsdec & Hlsincr).
        unfold fuel_decr in Hlsdec.
        have Hmustdec: must_decrease ρ None δ (trfirst auxtr') (Some ζ).
        { constructor; eauto. }
        eapply case1 =>//.
        * move=> Hinfuel; apply Hlsdec => //; first set_solver.
        * eapply infinite_cons =>//.
      + (* Three cases:
           (1) ρ' = ρ and we are done
           (2) ρ' ≠ ρ but they share the same ρ -> ρ decreases
           (3) ρ' ≠ ρ and they don't have the same tid ->
           impossible because tid and the label must match! *)
        inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        destruct (decide (ρ = ρ')) as [->|Hρneq].
        { exists 0. right. rewrite /pred_at /=. eauto. }
        destruct Hls as (?&Hsame&Hdec&Hnotinc&_).
        rewrite -Hsame /= in Hmapping.
        have Hmustdec: must_decrease ρ (Some ρ') δ (trfirst auxtr') (Some ζ).
        { constructor; eauto; congruence. }
        (* Copy and paste begins here *)
        eapply case1 =>//; last by eauto using infinite_cons.
        intros Hinfuels. apply Hdec =>//. SS.
    - (* Another thread is taking a step. *)
      destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
      { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. }
      have [ζ'' Hζ''] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.
      destruct (decide (ζ = ζ'')) as [<-|Hchange].
      + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f.
        { destruct ζ' as [ζ'|]; last first; simpl in *.
          - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ; try done. destruct Hls as [_ [_ [Hnoninc _]]].
            have HnotNone: Some ρ ≠ None by congruence.
            specialize (Hnoninc ρ ltac:(SS) HnotNone).
            unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
            destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
            eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
            apply elem_of_dom_2 in Heq. set_solver.
          - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
            + destruct Hls as (?&?&?&Hnoninc&?).
              unfold fuel_must_not_incr in Hnoninc.
              have Hneq: Some ρ ≠ Some ρ0 by congruence.
              specialize (Hnoninc ρ ltac:(SS) Hneq).
              unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
              eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
              apply elem_of_dom_2 in Heq. set_solver.
            + destruct Hls as (?&?&Hnoninc&?).
              unfold fuel_must_not_incr in Hnoninc.
              have Hneq: Some ρ ≠ None by congruence.
              specialize (Hnoninc ρ ltac:(SS) Hneq).
              unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
              eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
              apply elem_of_dom_2 in Heq. set_solver. }

        unfold fair_ex in *.
        have Hζ'en: pred_at extr' 0 (λ (c : cfg Λ) _, locale_enabled ζ c).
        { rewrite /pred_at /= pred_first_ex. inversion Htm; eauto. }
        destruct m as [| m'].
        { rewrite -> !pred_at_0 in Hexen. destruct Hexen as [Hexen|Hexen].
          - exfalso. apply Hexen. unfold locale_enabled. by eapply (match_locale_enabled _ _ _ _ Htm).
          - simplify_eq. }

        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0)
                        ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ m' _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
      + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' < f.
        { destruct ζ' as [ζ'|]; last first; simpl in *.
          - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ; try done. destruct Hls as [_ [Hdec _]].
            unfold fuel_decr in Hdec.
            have Hmd: must_decrease ρ None δ (trfirst auxtr') None.
            { econstructor. congruence. rewrite Hζ''. eauto. }
            specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
            unfold oleq in Hdec. rewrite Hfuel in Hdec.
            destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done].
          - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
            simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
            + destruct Hls as (?&?&Hdec&?&?).
              unfold fuel_decr in Hdec. simplify_eq.
              have Hmd: must_decrease ρ (Some ρ0) δ (trfirst auxtr') (Some ζ0).
              { econstructor 2. congruence. rewrite Hζ''; eauto. }
              specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
              unfold oleq in Hdec. rewrite Hfuel in Hdec.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done].
            + destruct Hls as (?&Hdec&_).
              unfold fuel_decr in Hdec. simplify_eq.
              have Hmd: must_decrease ρ None δ (trfirst auxtr') (Some ζ0).
              { econstructor 2. congruence. rewrite Hζ''; eauto. }
              specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
              unfold oleq in Hdec. rewrite Hfuel in Hdec.
              destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done]. }

        unfold fair_ex in *.
        have: pred_at extr' 0 (λ c _, locale_enabled ζ'' c).
        { rewrite /pred_at /= pred_first_ex. inversion Htm; eauto. }
        have Hζ'en: pred_at extr' 0 (λ c _, locale_enabled ζ'' c).
        { rewrite /pred_at /= pred_first_ex. inversion Htm; eauto. }
        have [p Hp] := (Hfair' ζ'' 0 Hζ'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0)
                        ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ p _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
  Qed.

  Theorem fairness_preserved (extr: @extrace Λ) (auxtr: auxtrace):
    infinite_trace extr ->
    exaux_traces_match extr auxtr ->
    (forall ζ, fair_ex ζ extr) -> (forall ρ, fair_aux ρ auxtr).
  Proof.
    intros Hinfin Hmatch Hex ρ n Hn.
    unfold pred_at in Hn.
    destruct (after n auxtr) as [tr|] eqn:Heq =>//.
    setoid_rewrite pred_at_sum. rewrite Heq.
    have Hen: role_enabled ρ (trfirst tr) by destruct tr.
    have [ζ Hζ] : is_Some((trfirst tr).(ls_mapping) !! ρ) by eauto.
    have [f Hfuel] : is_Some((trfirst tr).(ls_fuel) !! ρ) by eauto.
    have Hex' := Hex ζ n.
    have [tr1' [Heq' Htr]] : exists tr1', after n extr = Some tr1' ∧ exaux_traces_match tr1' tr
     by eapply traces_match_after.
    have Hte: locale_enabled ζ (trfirst tr1').
    { rewrite /locale_enabled. have [HiS Hneqζ] := traces_match_first _ _ _ _ _ _ Htr.
      have [e Hein] := (HiS _ _ Hζ). exists e. split; first done.
      destruct (to_val e) eqn:Heqe =>//.
      exfalso. specialize (Hneqζ ζ e Hein). rewrite Heqe in Hneqζ.
      have HnotNull: Some v ≠ None by []. specialize (Hneqζ HnotNull ρ). done. }
    setoid_rewrite pred_at_sum in Hex'. rewrite Heq' in Hex'.
    have Hpa: pred_at extr n (λ c _, locale_enabled ζ c).
    { unfold pred_at. rewrite Heq'. destruct tr1'; eauto. }
    destruct (Hex' Hpa) as [m Hm].
    have ?: infinite_trace tr1'.
    { have Hinf := infinite_trace_after n extr Hinfin. by rewrite Heq' in Hinf. }
    eapply (fairness_preserved_ind ρ _ f m ζ _ tr); eauto.
    intros ?. by eapply fair_ex_after.
  Qed.

  Tactic Notation "inv" open_constr(P) := match goal with
                | [H: P |- _] => inversion H; clear H; simplify_eq
                                          end.

  Definition valid_state_evolution_fairness
             (extr : execution_trace Λ) (auxtr : auxiliary_trace (fair_model M)) :=
    match extr, auxtr with
    | (extr :tr[oζ]: (es, σ)), auxtr :tr[ℓ]: δ =>
        labels_match oζ ℓ ∧ ls_trans (trace_last auxtr) ℓ δ ∧ tids_smaller es δ
    | _, _ => True
    end.

  Definition valid_lift_fairness
             (φ: execution_trace Λ -> auxiliary_trace (fair_model M) -> Prop)
             (extr : execution_trace Λ) (auxtr : auxiliary_trace (fair_model M)) :=
    valid_state_evolution_fairness extr auxtr ∧ φ extr auxtr.

  Lemma valid_inf_system_trace_implies_traces_match
        (φ: execution_trace Λ -> auxiliary_trace (fair_model M) -> Prop)
        ex atr iex iatr progtr auxtr:
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace (fair_model M)),
        φ ex atr -> live_tids (trace_last ex) (trace_last atr)) ->
    (forall (ex: execution_trace Λ) (atr: auxiliary_trace (fair_model M)),
        φ ex atr -> valid_state_evolution_fairness ex atr) ->
    exec_trace_match ex iex progtr ->
    exec_trace_match atr iatr auxtr ->
    @valid_inf_system_trace _ (fair_model M) φ ex atr iex iatr ->
    exaux_traces_match progtr auxtr.
  Proof.
    intros Hφ1 Hφ2.
    revert ex atr iex iatr auxtr progtr. cofix IH.
    intros ex atr iex iatr auxtr progtr Hem Ham Hval.
    inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq.
    - inversion Hem; inversion Ham. econstructor; eauto.
      pose proof (Hφ1 ex atr Hphi). congruence.
    - inversion Hem; inversion Ham. subst.
      pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
      destruct (Hφ2 (ex :tr[ oζ ]: (l, σ')) (atr :tr[ ℓ ]: δ') Hphi') as (?&?&?).
      econstructor; eauto.
      + match goal with
        | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
      + match goal with
        | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq
        end; done.
  Qed.
End fairness_preserved.

#[global] Program Instance add_monoid: Monoid Nat.add :=
  {| monoid_unit := 0 |}.
Next Obligation. intros ???. apply Nat.add_assoc. Qed.
Next Obligation. intros ??. apply Nat.add_comm. Qed.
Next Obligation. intros ?. done. Qed.

Section addition_monoid.
  Context `{Countable K}.

  Lemma big_addM_leq_forall (X Y: gmap K nat):
    (∀ k, k ∈ dom X -> oleq (X !! k) (Y !! k)) ->
    ([^ Nat.add map] k ↦ x ∈ X, x) ≤ ([^ Nat.add map] k ↦ y ∈ Y, y).
  Proof.
    revert Y.
    induction X as [|k v X HXk IH] using map_ind.
    { intros Y Hx. rewrite big_opM_empty /=. lia. }
    intros Y Hx. rewrite big_opM_insert //.
    have Hol: oleq (<[k:=v]> X !! k) (Y !! k) by apply Hx; set_solver.
    rewrite lookup_insert in Hol.
    destruct (Y!!k) as [v'|] eqn:Heq; last done.
    rewrite (big_opM_delete _ Y k v') //.
    apply plus_le_compat=>//.
    apply IH=> k' Hin.
    have ?: k ≠ k'.
    { intros ->. apply elem_of_dom in Hin. rewrite HXk in Hin. by destruct Hin. }
    rewrite -(lookup_insert_ne X k k' v) // (lookup_delete_ne Y k) //.
    apply Hx. set_solver.
  Qed.
End addition_monoid.

Section dec_unless.
  Context {St S' L L': Type}.
  Context (Us: St -> S').
  Context (Ul: L -> option L').

  Definition dec_unless Ψ (tr: trace St L) :=
    ∀ n, match after n tr with
         | Some ⟨ _ ⟩ | None => True
         | Some (s -[ℓ]-> tr') =>
           (∃ ℓ', Ul ℓ = Some ℓ') ∨
           (Ψ (trfirst tr') < Ψ s ∧ Us s = Us (trfirst tr'))
         end.

  Lemma dec_unless_next Ψ s ℓ tr (Hdec: dec_unless Ψ (s -[ℓ]-> tr)): dec_unless Ψ tr.
  Proof.
    intros n. specialize (Hdec (n+1)). rewrite (after_sum 1) // in Hdec.
  Qed.

End dec_unless.

Section fuel_dec_unless.
  Context `{Mdl: FairModel}.
  Context `{Λ: language}.
  Context `{Countable (locale Λ)}.

  Notation exaux_traces_match :=
    (@traces_match (olocale Λ)
                   (fair_model Mdl).(mlabel)
                   (cfg Λ)
                   (LiveState Mdl)
                   labels_match
                   live_tids
                   locale_step
                   ls_trans
    ).

  Definition Ul (ℓ: (@fair_model Λ Mdl).(mlabel)) :=
    match ℓ with
    | Take_step ρ _ => Some (Some ρ)
    | _ => None
    end.

  Definition Ψ (δ: LiveState Mdl) :=
    size δ.(ls_fuel) + [^ Nat.add map] ρ ↦ f ∈ δ.(ls_fuel (Λ := Λ)), f.

  Lemma fuel_dec_unless (extr: extrace) (auxtr: auxtrace) :
    (∀ c c', locale_step (Λ := Λ) c None c' -> False) ->
    exaux_traces_match extr auxtr ->
    dec_unless ls_under Ul Ψ auxtr.
  Proof.
    intros Hcl Hval n. revert extr auxtr Hval. induction n; intros extr auxtr Hval; last first.
    { edestruct (after (S n) auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
      simpl in Heq;
      simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.
      inversion Hval as [|?????????? Hmatch]; simplify_eq =>//.
      specialize (IHn _ _ Hmatch). rewrite Heq // in IHn. }
    edestruct (after 0 auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
    simpl in Heq; simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.

    inversion Hval as [|c tid extr' ?? ? Hlm Hsteps Hstep Htrans Hmatch]; simplify_eq =>//.
    destruct ℓ as [| tid' |];
      [left; eexists; done| right |destruct tid; by [| exfalso; eapply Hcl]].
    destruct Htrans as (Hne&Hdec&Hni&Hincl&Heq). rewrite -> Heq in *. split; last done.
    destruct tid as [tid|]; last done.
    rewrite <- Hlm in *.

    destruct (decide (dom $ ls_fuel δ = dom $ ls_fuel (trfirst auxtr'))) as [Hdomeq|Hdomneq].
    - destruct Hne as [ρ Hρtid].

      assert (ρ ∈ dom $ ls_fuel δ) as Hin by rewrite -ls_same_doms elem_of_dom //.
      pose proof Hin as Hin'. pose proof Hin as Hin''.
      apply elem_of_dom in Hin as [f Hf].
      rewrite Hdomeq in Hin'. apply elem_of_dom in Hin' as [f' Hf'].
      rewrite /Ψ -!size_dom Hdomeq.
      apply Nat.add_lt_mono_l.

      rewrite /Ψ (big_opM_delete (λ _ f, f) (ls_fuel (trfirst _)) ρ) //.
      rewrite (big_opM_delete (λ _ f, f) (ls_fuel  δ) ρ) //.
      apply Nat.add_lt_le_mono.
      { rewrite /fuel_decr in Hdec. specialize (Hdec ρ). rewrite Hf Hf' /= in Hdec.
        apply Hdec; [set_solver | set_solver | by econstructor]. }

      apply big_addM_leq_forall => ρ' Hρ'.
      rewrite dom_delete_L in Hρ'.
      have Hρneqρ' : ρ ≠ ρ' by set_solver.
      rewrite !lookup_delete_ne //.
      destruct (decide (ρ' ∈ dom δ.(ls_fuel))) as [Hin|Hnotin]; last set_solver.
      rewrite /fuel_must_not_incr in Hni.
      destruct (Hni ρ' ltac:(done) ltac:(done)); [done|set_solver].
    - assert (size $ ls_fuel (trfirst auxtr') < size $ ls_fuel δ).
      { rewrite -!size_dom. apply subset_size. set_solver. }
      apply Nat.add_lt_le_mono =>//.
      apply big_addM_leq_forall => ρ' Hρ'.
      destruct (Hni ρ' ltac:(set_solver) ltac:(done)); [done|set_solver].
  Qed.
End fuel_dec_unless.

Section destuttering.
  Context {St S' L L': Type}.
  Context (Us: St -> S').
  Context (Ul: L -> option L').

  Inductive upto_stutter_ind (upto_stutter_coind: trace St L -> trace S' L' -> Prop):
    trace St L -> trace S' L' -> Prop :=
  | upto_stutter_singleton s:
      upto_stutter_ind upto_stutter_coind ⟨s⟩ ⟨Us s⟩
  | upto_stutter_stutter btr str s ℓ:
      Ul ℓ = None ->
      (* (Us s = Us (trfirst btr) -> (or something like this...?) *)
      Us s = Us (trfirst btr) ->
      Us s = trfirst str ->
      upto_stutter_ind upto_stutter_coind btr str ->
      upto_stutter_ind upto_stutter_coind (s -[ℓ]-> btr) str
  | upto_stutter_step btr str s ℓ s' ℓ':
      Us s = s' ->
      Ul ℓ = Some ℓ' ->
      upto_stutter_coind btr str ->
      upto_stutter_ind upto_stutter_coind (s -[ℓ]-> btr) (s' -[ℓ']-> str).

  Definition upto_stutter := paco2 upto_stutter_ind bot2.

  Lemma upto_stutter_mono :
    monotone2 (upto_stutter_ind).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono : paco.

  Lemma upto_stutter_after {btr str} n {str'}:
    upto_stutter btr str ->
    after n str = Some str' ->
    ∃ n' btr', after n' btr = Some btr' ∧ upto_stutter btr' str'.
  Proof.
    have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
    { intros P [x ?]. by exists (S x). }
    revert btr str str'. induction n as [|n IH]; intros btr str str' Hupto Hafter.
    { injection Hafter => <-. clear Hafter. exists 0, btr. done. }
    revert str' Hafter. punfold Hupto. induction Hupto as
        [s|btr str s ℓ HUl HUs1 HUs2 Hind IHH|btr str s ℓ s' ℓ' ?? Hind].
    - intros str' Hafter. done.
    - intros str' Hafter.
      apply Hw. simpl. by apply IHH.
    - intros str' Hafter. simpl in Hafter.
      apply Hw. simpl. eapply IH =>//.
      by destruct Hind.
  Qed.

  Lemma upto_stutter_after_None {btr str} n:
    upto_stutter btr str ->
    after n str = None ->
    ∃ n', after n' btr = None.
  Proof.
    have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
    { intros P [x ?]. by exists (S x). }
    revert btr str. induction n as [|n IH]; intros btr str Hupto Hafter.
    { exists 0. done. }
    revert Hafter. punfold Hupto. induction Hupto as
        [s|btr str s ℓ HUl HUs1 HUs2 Hind IHH|btr str s ℓ s' ℓ' ?? Hind].
    - intros Hafter. by exists 1.
    - intros Hafter.
      apply Hw. simpl. by apply IHH.
    - intros Hafter. simpl in Hafter.
      apply Hw. simpl. eapply IH =>//.
      by destruct Hind.
  Qed.

  Program Fixpoint destutter_once_step N Ψ (btr: trace St L) :
    Ψ (trfirst btr) < N →
    dec_unless Us Ul Ψ btr →
    S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'}) :=
    match N as n return
          Ψ (trfirst btr) < n →
          dec_unless Us Ul Ψ btr →
          S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'})
    with
    | O => λ Hlt _, False_rect _ (Nat.nlt_0_r _ Hlt)
    | S N' =>
      λ Hlt Hdec,
      match btr as z return btr = z → S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'}) with
      | tr_singl s => λ _, inl (Us s)
      | tr_cons s l btr' =>
        λ Hbtreq,
        match Ul l as z return Ul l = z → S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'}) with
        | Some l' => λ _, inr (Us s, l', exist _ btr' _)
        | None => λ HUll, destutter_once_step N' Ψ btr' _ _
        end eq_refl
      end eq_refl
    end.
  Next Obligation.
  Proof.
    intros _ Ψ btr N' Hlt Hdec s l btr' -> l' HUll; simpl.
    eapply dec_unless_next; done.
  Qed.
  Next Obligation.
  Proof.
    intros _ Ψ btr N' Hlt Hdec s l btr' -> HUll; simpl in *.
    pose proof (Hdec 0) as [[? ?]|[? ?]]; [congruence|lia].
  Qed.
  Next Obligation.
  Proof.
    intros _ Ψ btr N' Hlt Hdec s l btr' -> HUll; simpl.
    eapply dec_unless_next; done.
  Qed.

  CoFixpoint destutter_gen Ψ N (btr: trace St L) :
    Ψ (trfirst btr) < N ->
    dec_unless Us Ul Ψ btr → trace S' L' :=
    λ Hlt Hdec,
    match destutter_once_step N Ψ btr Hlt Hdec with
    | inl s' => tr_singl s'
    | inr (s', l', z) => tr_cons s' l' (destutter_gen Ψ  (S (Ψ (trfirst $ proj1_sig z)))
                                                 (proj1_sig z) (Nat.lt_succ_diag_r _) (proj2_sig z))
    end.

  Definition destutter Ψ (btr: trace St L) :
    dec_unless Us Ul Ψ btr → trace S' L' :=
    λ Hdec,
    destutter_gen Ψ (S (Ψ (trfirst btr))) btr (Nat.lt_succ_diag_r _) Hdec.

  Lemma destutter_same_Us N Ψ btr Hlt Hdec:
    match destutter_once_step N Ψ btr Hlt Hdec with
    | inl s' | inr (s', _, _) => Us (trfirst btr) = s'
    end.
  Proof.
    revert btr Hlt Hdec. induction N as [|N]; first lia.
    intros btr Hlt Hdec. simpl.
    destruct btr as [s|s ℓ btr']; first done.
    generalize (destutter_once_step_obligation_1 Ψ (s -[ ℓ ]-> btr') N
                Hlt Hdec s ℓ btr' eq_refl).
    generalize (destutter_once_step_obligation_2 Ψ (s -[ ℓ ]-> btr') N Hlt Hdec s ℓ btr' eq_refl).
    generalize (destutter_once_step_obligation_3 Ψ (s -[ ℓ ]-> btr') N Hlt Hdec s ℓ btr' eq_refl).
    intros HunlessNone HltNone HdecSome.
    destruct (Ul ℓ) as [ℓ'|] eqn:Heq; cbn; first done.
    unfold dec_unless in Hdec.
    destruct (Hdec 0) as [[??]|[? Hsame]]; first congruence.
    rewrite Hsame. apply IHN.
  Qed.

  Lemma destutter_spec_ind N Ψ (btr: trace St L) (Hdec: dec_unless Us Ul Ψ btr)
    (Hlt: Ψ (trfirst btr) < N):
    upto_stutter btr (destutter_gen Ψ N btr Hlt Hdec).
  Proof.
    revert N btr Hlt Hdec.
    pcofix CH. pfold.
    induction N.
    { intros; lia. }
    intros btr Hlt Hdec.
    rewrite (trace_unfold_fold (destutter_gen _ _ _ _ _)).
    destruct btr as [s|s ℓ btr'].
    { simpl in *. econstructor. }
    cbn.
    generalize (destutter_once_step_obligation_1 Ψ (s -[ ℓ ]-> btr') N
                Hlt Hdec s ℓ btr' eq_refl).
    generalize (destutter_once_step_obligation_2 Ψ (s -[ ℓ ]-> btr') N Hlt Hdec s ℓ btr' eq_refl).
    generalize (destutter_once_step_obligation_3 Ψ (s -[ ℓ ]-> btr') N Hlt Hdec s ℓ btr' eq_refl).
    intros HunlessNone HltNone HdecSome.
    destruct (Ul ℓ) as [ℓ'|] eqn:Heq; cbn.
    - econstructor 3 =>//. right. apply (CH (S (Ψ $ trfirst btr'))).
    - econstructor 2=>//.
      + destruct (Hdec 0) as [[??]|[??]];congruence.
      + have ?: Us s = Us (trfirst btr').
        { destruct (Hdec 0) as [[??]|[? Hsame]]; congruence. }
        have HH := destutter_same_Us N Ψ btr' (HltNone eq_refl) (HunlessNone eq_refl).
        destruct (destutter_once_step N Ψ btr' (HltNone eq_refl) (HunlessNone eq_refl)) as
            [|[[??][??]]]eqn:Heq'; simpl in *; congruence.
      + rewrite -trace_unfold_fold.
        specialize (IHN btr' (HltNone eq_refl) (HunlessNone eq_refl)).
        match goal with
          [H : context[upto_stutter_ind]  |- ?Y] => let X := type of H in
                          suffices <-: X <-> Y; first done
        end.
        f_equiv.
        rewrite {1}(trace_unfold_fold (destutter_gen _ _ _ _ _)) /= -trace_unfold_fold //.
  Qed.

  Lemma destutter_spec Ψ (btr: trace St L) (Hdec: dec_unless Us Ul Ψ btr):
    upto_stutter btr (destutter Ψ btr Hdec).
  Proof. eapply destutter_spec_ind. Qed.

  Lemma can_destutter Ψ (btr: trace St L) (Hdec: dec_unless Us Ul Ψ btr):
    ∃ str, upto_stutter btr str.
  Proof. exists (destutter Ψ btr Hdec). apply destutter_spec. Qed.

End destuttering.

Section destuttering_auxtr.
  Context {Mdl: FairModel}.
  Context {Λ: language}.
  Context `{Countable (locale Λ)}.

  Notation exaux_traces_match :=
    (@traces_match (olocale Λ)
                   (fair_model Mdl).(mlabel)
                   (cfg Λ)
                   (LiveState Mdl)
                   labels_match
                   live_tids
                   locale_step
                   ls_trans
    ).

  Definition upto_stutter_auxtr :=
    upto_stutter (@ls_under Λ Mdl) (Ul (Mdl := Mdl) (Λ := Λ)).

  Lemma can_destutter_auxtr extr auxtr:
    (∀ c c', locale_step (Λ := Λ) c None c' -> False) ->
    exaux_traces_match extr auxtr ->
    ∃ mtr, upto_stutter_auxtr auxtr mtr.
  Proof.
    intros ??. eapply can_destutter.
    eapply fuel_dec_unless =>//.
  Qed.

End destuttering_auxtr.

Section model_traces.
  Context {Mdl: FairModel}.
  Context {Λ: language}.
  Context `{Countable (locale Λ)}.

  Definition mtrace := trace Mdl (option Mdl.(fmrole)).

  Definition role_enabled_model ρ (s: Mdl) := ρ ∈ Mdl.(live_roles) s.

  Definition fair_model_trace ρ (mtr: mtrace): Prop  :=
    forall n, pred_at mtr n (λ δ _, role_enabled_model ρ δ) ->
         ∃ m, pred_at mtr (n+m) (λ δ _, ¬role_enabled_model ρ δ)
              ∨ pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)).

  Lemma fair_model_trace_after ℓ tr tr' k:
    after k tr = Some tr' ->
    fair_model_trace ℓ tr -> fair_model_trace ℓ tr'.
  Proof.
    intros Haf Hf n Hp.
    have Hh:= Hf (k+n).
    have Hp': pred_at tr (k + n) (λ δ _, role_enabled_model ℓ δ).
    { rewrite (pred_at_sum _ k) Haf /= //. }
    have [m Hm] := Hh Hp'. exists m.
    by rewrite <- Nat.add_assoc, !(pred_at_sum _ k), Haf in Hm.
  Qed.

  Lemma fair_model_trace_cons ℓ δ ℓ' r:
    fair_model_trace ℓ (δ -[ℓ']-> r) -> fair_model_trace ℓ r.
  Proof. intros Hfm. by eapply (fair_model_trace_after ℓ _ r 1) =>//. Qed.

  Lemma fair_model_trace_cons_forall δ ℓ' r:
    (∀ ℓ, fair_model_trace ℓ (δ -[ℓ']-> r)) -> (∀ ℓ, fair_model_trace ℓ r).
  Proof. eauto using fair_model_trace_cons. Qed.

  Inductive mtrace_valid_ind (mtrace_valid_coind: mtrace -> Prop): mtrace -> Prop :=
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

  Lemma upto_stutter_mono' :
    monotone2 (upto_stutter_ind (@ls_under Λ Mdl) (@Ul Mdl Λ)).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_preserves_validity auxtr mtr:
    upto_stutter_auxtr auxtr mtr ->
    auxtrace_valid (Λ := Λ) auxtr ->
    mtrace_valid mtr.
  Proof.
    revert auxtr mtr. pcofix CH. intros auxtr mtr Hupto Hval.
    punfold Hupto.
    induction Hupto as [| |btr str δ ????? IH].
    - pfold. constructor.
    - apply IHHupto. inversion Hval. assumption.
    - pfold; constructor=>//.
      + subst. inversion Hval as [| A B C Htrans E F ] =>//. subst. unfold ls_trans in *.
        destruct ℓ; try done. simpl in *. simplify_eq.
        destruct Htrans as [??].
        have <- //: ls_under $ trfirst btr = trfirst str.
        { destruct IH as [IH|]; last done. punfold IH. inversion IH =>//. }
      + right. eapply CH.
        { destruct IH =>//. }
        subst. by inversion Hval.
  Qed.

End model_traces.

Global Hint Resolve fair_model_trace_cons: core.
Global Hint Resolve fair_model_trace_cons: core.

Section upto_stutter_preserves_fairness_and_terminaison.
  Context {Mdl: FairModel}.
  Context {Λ: language}.
  Context `{Countable (locale Λ)}.


  Notation upto_stutter_aux := (upto_stutter (ls_under (Λ := Λ)) (Ul (Λ := Λ))).

  Lemma upto_stutter_mono'' : (* TODO fix this proliferation *)
    monotone2 (upto_stutter_ind (@ls_under Λ Mdl) (@Ul Mdl Λ)).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_stutter_fairness_0 ρ auxtr (mtr: @mtrace Mdl):
    upto_stutter_aux auxtr mtr ->
    (* role_enabled_model ρ (trfirst mtr) -> *)
    (∃ n, pred_at auxtr n (λ δ _, ¬role_enabled (Λ := Λ) ρ δ)
          ∨ pred_at auxtr n (λ _ ℓ, ∃ ζ, ℓ = Some (Take_step ρ ζ))) ->
    ∃ m, pred_at mtr m (λ δ _, ¬role_enabled_model ρ δ)
         ∨ pred_at mtr m (λ _ ℓ, ℓ = Some $ Some ρ).
    Proof.
      intros Hupto (* Hre *) [n Hstep].
      revert auxtr mtr Hupto (* Hre *) Hstep.
      induction n as [|n]; intros auxtr mtr Hupto (* Hre *) Hstep.
      - punfold Hupto. inversion Hupto; simplify_eq.
        + destruct Hstep as [Hpa|[??]]; try done.
          exists 0. left. rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
        + rewrite -> !pred_at_0 in Hstep. exists 0.
          destruct Hstep as [Hstep| [tid Hstep]]; [left|right].
          * rewrite /pred_at /=. destruct mtr; simpl in *; try congruence.
          * exfalso. injection Hstep => Heq. rewrite -> Heq in *.
            unfold Ul in *. congruence.
        + rewrite -> !pred_at_0 in Hstep. exists 0.
          destruct Hstep as [Hstep| [tid Hstep]]; [left|right].
          * rewrite /pred_at //=.
          * rewrite /pred_at //=. injection Hstep. intros Heq. simplify_eq.
            unfold Ul in *. congruence.
      - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
        + destruct Hstep as [?|?]; done.
        + rewrite -> !pred_at_S in Hstep.
          eapply IHn; eauto.
          by pfold.
        + destruct (decide (ℓ' = Some ρ)).
          * simplify_eq.
            exists 0. right. rewrite pred_at_0 //.
          * have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
            { intros P [x ?]. by exists (S x). }
            apply Hw. setoid_rewrite pred_at_S.
            eapply IHn; eauto.
            { destruct IH as [|]; done. }
    Qed.

  Lemma upto_stutter_fairness auxtr (mtr: @mtrace Mdl):
    upto_stutter_aux auxtr mtr ->
    (∀ ρ, fair_aux ρ auxtr) ->
    (∀ ρ, fair_model_trace ρ mtr).
  Proof.
    intros Hupto Hfa ρ n Hpmod.
    unfold pred_at in Hpmod.
    destruct (after n mtr) as [mtr'|] eqn:Heq; last done.
    destruct (upto_stutter_after _ _ n Hupto Heq) as (n'&auxtr'&Heq'&Hupto').
    have Hre: role_enabled_model ρ (trfirst mtr') by destruct mtr'.
    specialize (Hfa ρ).
    have Henaux : role_enabled ρ (trfirst auxtr').
    { have HUs: ls_under (trfirst auxtr') = trfirst mtr'.
      - punfold Hupto'. by inversion Hupto'.
      - unfold role_enabled, role_enabled_model in *.
        rewrite HUs //. }
    have Hfa' := (fair_aux_after ρ auxtr n' auxtr' Hfa Heq' 0).
    have Hpredat: pred_at auxtr' 0 (λ δ _, role_enabled ρ δ).
    { rewrite /pred_at /=. destruct auxtr'; done. }
    destruct (upto_stutter_fairness_0 ρ auxtr' mtr' Hupto' (Hfa' Hpredat)) as (m&Hres).
    exists m. rewrite !(pred_at_sum _ n) Heq //.
  Qed.

  Lemma upto_stutter_finiteness auxtr (mtr: @mtrace Mdl):
    upto_stutter_aux auxtr mtr ->
    terminating_trace mtr ->
    terminating_trace auxtr.
  Proof.
    intros Hupto [n Hfin].
    have [n' ?] := upto_stutter_after_None _ _ n Hupto Hfin.
    eexists; done.
  Qed.

End upto_stutter_preserves_fairness_and_terminaison.

(* Classical *)

Require Import Coq.Logic.Classical.
Section infinite_or_finite.
  Context {St L: Type}.

  Lemma infinite_or_finite (tr: trace St L):
    infinite_trace tr ∨ terminating_trace tr.
  Proof.
    destruct (classic (infinite_trace tr)) as [|Hni]; first by eauto.
    rewrite /infinite_trace in Hni.
    apply not_all_ex_not in Hni. destruct Hni as [n Hni%eq_None_not_Some].
    by right; exists n.
  Qed.

End infinite_or_finite.

Global Hint Resolve mtrace_valid_mono : paco.
