From trillium.program_logic Require Export adequacy.
From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.

Require Import
        Coq.Relations.Relation_Definitions
        Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Wf_nat.

Section traces.

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

  Lemma pred_first_trace (S T : Type) (tr: trace S T ) (P: S -> Prop):
    match tr with
    | ⟨ s ⟩ | s -[ _ ]-> _ => P s
    end <-> P (trfirst tr).
  Proof. destruct tr; done. Qed.

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

    Lemma after_0_id (tr : trace St L):
      after 0 tr = Some tr.
    Proof. done. Qed.

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

    Lemma after_S_tr_cons (tr: trace St L) n s ℓ atr
      (AFTER: after n tr = Some (s -[ℓ]-> atr)):
      after (S n) tr = Some atr.
    Proof. 
      by rewrite -Nat.add_1_r after_sum' AFTER.
    Qed.

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

    Lemma pred_at_state_trfirst (tr: trace St L) (P : St → Prop):
      pred_at tr 0 (fun st _ => P st) ↔ P (trfirst tr).
    Proof. 
      rewrite /pred_at. destruct tr; eauto.
    Qed.

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

    Lemma infinite_neg_finite (tr : trace St L):
      terminating_trace tr <-> ¬ infinite_trace tr.
    Proof.
      rewrite /terminating_trace /infinite_trace. split.
      - intros [n A]. intros A'. specialize (A' n). rewrite A in A'. by destruct A'.
      - intros [n A%eq_None_not_Some]%not_forall_exists_not. eexists; eauto.
    Qed. 

  End after.

End traces.

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

  Lemma traces_match_preserves_termination tr1 tr2 :
    traces_match tr1 tr2 ->
    terminating_trace tr2 ->
    terminating_trace tr1.
  Proof.
    intros Hmatch [n HNone].
    revert tr1 tr2 Hmatch HNone. induction n as [|n IHn]; first done.
    intros tr1 tr2 Hmatch HNone.
    replace (S n) with (1 + n) in HNone =>//.
    rewrite (after_sum' _ 1) in HNone.
    destruct tr2 as [s| s ℓ tr2'];
      first by inversion Hmatch; simplify_eq; exists 1.
    simpl in HNone.
    inversion Hmatch; simplify_eq.
    apply terminating_trace_cons.
    eapply IHn =>//.
  Qed.

  

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

Definition oleq (a b : option nat) : Prop :=
  match a, b with
  | Some x, Some y => x ≤ y
  | _, _ => False
  end.

Definition oless (a b : option nat) : Prop :=
  match a, b with
  | Some x, Some y => x < y
  | _, _ => False
  end.

Lemma oleq_oless a b : oless a b -> oleq a b.
Proof. destruct a; destruct b=>//. unfold oless, oleq. lia. Qed.


Section dec_unless.
  Context {St S' L L': Type}.
  Context (Us: St -> S').
  (* Context (Ul: L -> option L'). *)
  Context (Usls: St -> L -> St -> option L').

  Definition dec_unless Ψ (tr: trace St L) :=
    ∀ n, match after n tr with
         | Some ⟨ _ ⟩ | None => True
         | Some (s -[ℓ]-> tr') =>
           (∃ ℓ', Usls s ℓ (trfirst tr') = Some ℓ') ∨
           (Ψ (trfirst tr') < Ψ s ∧ Us s = Us (trfirst tr'))
         end.

  Lemma dec_unless_next Ψ s ℓ tr (Hdec: dec_unless Ψ (s -[ℓ]-> tr)): dec_unless Ψ tr.
  Proof.
    intros n. specialize (Hdec (n+1)). rewrite (after_sum 1) // in Hdec.
  Qed.

End dec_unless.

Section destuttering.
  Context {St S' L L': Type}.
  Context (Us: St -> S').
  (* Context (Ul: L -> option L'). *)
  Context (Usls: St -> L -> St -> option L').

  Inductive upto_stutter_ind (upto_stutter_coind: trace St L -> trace S' L' -> Prop):
    trace St L -> trace S' L' -> Prop :=
  | upto_stutter_singleton s:
      upto_stutter_ind upto_stutter_coind ⟨s⟩ ⟨Us s⟩
  | upto_stutter_stutter btr str s ℓ:
      (* Ul ℓ = None -> *)
      (* (forall ℓ', ¬ inner_step ℓ' s ℓ (trfirst btr)) -> *)
      (Usls s ℓ (trfirst btr) = None) ->
      Us s = Us (trfirst btr) ->
      Us s = trfirst str ->
      upto_stutter_ind upto_stutter_coind btr str ->
      upto_stutter_ind upto_stutter_coind (s -[ℓ]-> btr) str
  | upto_stutter_step btr str s ℓ s' ℓ':
      Us s = s' ->
      (* Ul ℓ = Some ℓ' -> *)
      (* inner_step ℓ' s ℓ (trfirst btr) -> *)
      Usls s ℓ (trfirst btr) = Some ℓ' ->
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

  Lemma upto_stutter_trfirst btr str
    (CORR: upto_stutter btr str):
    trfirst str = Us (trfirst btr). 
  Proof.
    punfold CORR. by inversion CORR.
  Qed. 

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

  Local Ltac gd t := generalize dependent t.

  Lemma upto_stutter_after'
    {btr : trace St L} {str : trace S' L'} (n : nat) {btr' : trace St L}:
    upto_stutter btr str
    → after n btr = Some btr'
      → ∃ (n' : nat) (str' : trace S' L'),
          after n' str = Some str' ∧ upto_stutter btr' str'.
  Proof.
    have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n).
    { intros P [x ?]. by exists (S x). }

    intros. 
    gd btr. gd str. gd btr'. induction n as [|n IH]; intros btr' str btr Hupto Hafter.
    { injection Hafter => <-. clear Hafter. exists 0, str. done. }
    punfold Hupto.
    inversion Hupto; subst. 
    - done.
    - simpl in Hafter. rename btr0 into btr. 
      specialize (IH btr' str btr).
      eapply IH; eauto. 
      by pfold.
    - simpl in Hafter. rename btr0 into btr. rename str0 into str.
      specialize (IH btr' str btr).
      assert (upto_stutter btr str) as UPTO'.
      { (* TODO: proper way of doing it? *)
        inversion H1; eauto. done. }
      specialize (IH UPTO' Hafter) as (?&?&?&?). 
      eauto. 
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

  Lemma upto_stutter_infinite_trace tr1 tr2 :
    upto_stutter tr1 tr2 → infinite_trace tr1 → infinite_trace tr2.
  Proof.
    intros Hstutter Hinf n.
    revert tr1 tr2 Hstutter Hinf.
    induction n as [|n IHn]; intros tr1 tr2 Hstutter Hinf.
    - punfold Hstutter.
    - punfold Hstutter.
      induction Hstutter.
      + specialize (Hinf (1 + n)).
        rewrite after_sum' in Hinf. simpl in *. apply is_Some_None in Hinf. done.
      + apply IHHstutter.
        intros m. specialize (Hinf (1 + m)).
        rewrite after_sum' in Hinf. simpl in *. done.
      + simpl. eapply (IHn btr str); [by destruct H1|].
        intros m. specialize (Hinf (1 + m)).
        rewrite after_sum' in Hinf. simpl in *. done.
  Qed.

  Program Fixpoint destutter_once_step N Ψ (btr: trace St L)
                   (* {DEC: forall ℓ' s1 ℓ s2, Decision (inner_step ℓ' s1 ℓ s2)} *)
    :
    Ψ (trfirst btr) < N →
    dec_unless Us Usls Ψ btr →
    S' + (S' * L' * { btr' : trace St L | dec_unless Us Usls Ψ btr'}) :=
    match N as n return
          Ψ (trfirst btr) < n →
          dec_unless Us Usls Ψ btr →
          S' + (S' * L' * { btr' : trace St L | dec_unless Us Usls Ψ btr'})
    with
    | O => λ Hlt _, False_rect _ (Nat.nlt_0_r _ Hlt)
    | S N' =>
      λ Hlt Hdec,
      match btr as z return btr = z → S' + (S' * L' * { btr' : trace St L | dec_unless Us Usls Ψ btr'}) with
      | tr_singl s => λ _, inl (Us s)
      | tr_cons s l btr' =>
        λ Hbtreq,
        (* match inner_step l as z return Ul l = z → S' + (S' * L' * { btr' : trace St L | dec_unless Us Ul Ψ btr'}) with *)
        (* | Some l' => λ _, inr (Us s, l', exist _ btr' _) *)
        (* | None => λ HUll, destutter_once_step N' Ψ btr' _ _ *)
        (* end *)
        match Usls s l (trfirst btr') as z return Usls s l (trfirst btr') = z → S' + (S' * L' * { btr' : trace St L | dec_unless Us Usls Ψ btr'}) with
        | Some l' => λ _, inr (Us s, l', exist _ btr' _)
        | None => λ HUll, destutter_once_step N' Ψ btr' _ _
        end
          eq_refl
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
    dec_unless Us Usls Ψ btr → trace S' L' :=
    λ Hlt Hdec,
    match destutter_once_step N Ψ btr Hlt Hdec with
    | inl s' => tr_singl s'
    | inr (s', l', z) => tr_cons s' l' (destutter_gen Ψ  (S (Ψ (trfirst $ proj1_sig z)))
                                                 (proj1_sig z) (Nat.lt_succ_diag_r _) (proj2_sig z))
    end.

  Definition destutter Ψ (btr: trace St L) :
    dec_unless Us Usls Ψ btr → trace S' L' :=
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
    destruct (Usls s ℓ (trfirst btr')) as [ℓ'|] eqn:Heq; cbn; first done.
    unfold dec_unless in Hdec.
    destruct (Hdec 0) as [[??]|[? Hsame]]; first congruence.
    rewrite Hsame. apply IHN.
  Qed.

  Lemma destutter_spec_ind N Ψ (btr: trace St L) (Hdec: dec_unless Us Usls Ψ btr)
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
    destruct (Usls s ℓ (trfirst btr')) as [ℓ'|] eqn:Heq; cbn.
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

  Lemma destutter_spec Ψ (btr: trace St L) (Hdec: dec_unless Us Usls Ψ btr):
    upto_stutter btr (destutter Ψ btr Hdec).
  Proof. eapply destutter_spec_ind. Qed.

  Lemma can_destutter Ψ (btr: trace St L) (Hdec: dec_unless Us Usls Ψ btr):
    ∃ str, upto_stutter btr str.
  Proof. exists (destutter Ψ btr Hdec). apply destutter_spec. Qed.

End destuttering.

(* TODO: Does this belong here? *)
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

  #[global] Instance lt_lex_partial_order : PartialOrder lt_lex.
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

#[global] Program Instance add_monoid: Monoid Nat.add :=
  {| monoid_unit := 0 |}.

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
    apply Nat.add_le_mono=>//.
    apply IH=> k' Hin.
    have ?: k ≠ k'.
    { intros ->. apply elem_of_dom in Hin. rewrite HXk in Hin. by destruct Hin. }
    rewrite -(lookup_insert_ne X k k' v) // (lookup_delete_ne Y k) //.
    apply Hx. set_solver.
  Qed.
End addition_monoid.

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
