From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.fairness Require Export inftraces.

Section ltl_lite.
  Context {S L : Type}.

  Definition ltl_pred := trace S L → Prop.
  
  (* Primitive operators *)
  Definition trace_now P : ltl_pred := λ tr, pred_at tr 0 P.
  Definition trace_not P : ltl_pred := λ tr, ¬ P tr.
  Definition trace_or P Q : ltl_pred := λ tr, P tr ∨ Q tr.
  Definition trace_next P : ltl_pred :=
    λ tr, ∃ tr', after 1 tr = Some tr' ∧ P tr'.
  Definition trace_until P Q : ltl_pred :=
    λ tr, ∃ n, (∃ tr', after n tr = Some tr' ∧ Q tr') ∧
               ∀ m, m < n → ∃ tr', after m tr = Some tr' ∧ P tr'.
  
  (* Definition trace_always P : ltl_pred := *)
  (*   λ tr, ∀ n, ∃ tr', after n tr = Some tr' ∧ P tr'. *)
  (* Definition trace_eventually P : ltl_pred := *)
  (*   λ tr, ∃ n tr', after n tr = Some tr' ∧ P tr'. *)
  (* Should maybe be redefined to use ∀ tr' in second conjunct *)

  (* Derived operators *)
  Definition trace_and P Q := (trace_not (trace_or (trace_not P) (trace_not Q))).
  Definition trace_implies P Q := (trace_or (trace_not P) Q).
  Definition trace_biimplies P Q :=
    (trace_and (trace_implies P Q) (trace_implies Q P)).
  Definition trace_true := (trace_now (λ _ _, True)).
  Definition trace_false := (trace_now (λ _ _,False)).
  Definition trace_eventually P := (trace_until trace_true P).
  Definition trace_always P := (trace_not $ trace_eventually (trace_not P)).

  Definition trace_always_eventually_implies
             (P Q : trace S L → Prop) : ltl_pred :=
    trace_always (trace_implies P (trace_eventually Q)).

  Definition trace_always_eventually_implies_now
             (P Q : S → option L → Prop) : ltl_pred :=
    trace_always_eventually_implies (trace_now P) (trace_now Q).

  Parameter role_enabled : S → L → Prop.

  Definition scheduling_fairness ρ : ltl_pred :=
    trace_always_eventually_implies_now
      (λ s _, role_enabled s ρ) (λ s l, ¬ role_enabled s ρ ∨ l = Some ρ).

  Lemma trace_not_not (tr:trace S L) P :
    ¬ P tr ↔ trace_not P tr.
  Proof. done. Qed.

  Lemma after_is_Some_le (tr : trace S L) n m :
    m ≤ n → is_Some $ after n tr → is_Some $ after m tr.
  Proof.
    revert tr m.
    induction n; intros tr m Hle.
    { intros. assert (m = 0) as -> by lia. done. }
    intros.
    destruct m; [done|].
    simpl in *.
    destruct tr; [done|].
    apply IHn. lia. done.
  Qed.

  Lemma trace_eventually_until (tr : trace S L) P :
    trace_eventually (trace_now P) tr →
    trace_until (trace_not (trace_now P)) (trace_now P) tr.
  Proof.
    intros [n [Hn _]].
    induction n as [n IHn] using lt_wf_ind.
    assert ((∀ m, m < n → ∃ tr', after m tr = Some tr' ∧ (trace_not (trace_now P)) tr') ∨
              ¬ (∀ m, m < n → ∃ tr', after m tr = Some tr' ∧ (trace_not (trace_now P)) tr')) as [HP|HP];
      [by apply ExcludedMiddle|by exists n|].
    eapply not_forall_exists_not in HP as [n' HP].
    apply Classical_Prop.imply_to_and in HP as [Hlt HP].
    destruct Hn as [tr' [Hafter' Htr']].
    assert (∃ tr'', after n' tr = Some tr'') as [tr'' Hafter].
    { apply (after_is_Some_le _ n n'); [lia|]. eexists _. done. }
    eapply not_exists_forall_not in HP.
    apply Classical_Prop.not_and_or in HP as [HP|HP]; [done|].
    rewrite -trace_not_not in HP.
    apply NNP_P in HP.
    eapply IHn; [done|]. eexists _. done.
  Qed.

End ltl_lite.
