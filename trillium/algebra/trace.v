From trillium.traces Require Export trace.
From iris.algebra Require Export ofe cmra local_updates.

Inductive trace_alg (A L : Type) : Type :=
| trace_alg_trace (ft : finite_trace A L)
| trace_alg_bot.

Global Arguments trace_alg_trace {_ _} _.
Global Arguments trace_alg_bot {_ _}, _.

Canonical Structure traceO (A L : Type) := leibnizO (finite_trace A L).
Canonical Structure trace_algO (A  L: Type) := leibnizO (trace_alg A L).

Section trace_alg_cmra.
  Context `{!EqDecision A, !EqDecision L}.

  Implicit Types a b : A.
  Implicit Types ℓ : L.
  Implicit Types ft : finite_trace A L.
  Implicit Types fa : trace_alg A L.

  Local Instance trace_alg_pcore_instance : PCore (trace_alg A L) := λ fa, Some fa.

  Local Instance trace_alg_op : Op (trace_alg A L) :=
    λ fa fa',
    match fa with
    | trace_alg_trace ft =>
      match fa' with
      | trace_alg_trace ft' =>
        if (bool_decide (ft `trace_prefix_of` ft')) then
          trace_alg_trace ft'
        else
          if (bool_decide (ft' `trace_prefix_of` ft)) then
            trace_alg_trace ft
          else
            trace_alg_bot
      | trace_alg_bot => trace_alg_bot
      end
    | trace_alg_bot => trace_alg_bot
    end.

  Arguments trace_alg_op _ _ : simpl never.

  Lemma trace_alg_op_traces ft ft' :
    (trace_alg_op (trace_alg_trace ft) (trace_alg_trace ft') = trace_alg_bot ∧
     (¬ ft `trace_prefix_of` ft' ∧
      ¬ ft' `trace_prefix_of` ft)) ∨
    ((trace_alg_op (trace_alg_trace ft) (trace_alg_trace ft') =
      trace_alg_trace ft' ∧ ft `trace_prefix_of` ft') ∨
     (trace_alg_op (trace_alg_trace ft) (trace_alg_trace ft') =
      trace_alg_trace ft ∧ ft' `trace_prefix_of` ft)).
  Proof.
    rewrite /trace_alg_op.
    rewrite -!decide_bool_decide.
    repeat destruct decide; eauto.
  Qed.

  Lemma trace_alg_op_eq_right' ft ft' :
    ft `trace_prefix_of` ft' →
    trace_alg_op (trace_alg_trace ft) (trace_alg_trace ft') = trace_alg_trace ft'.
  Proof.
    intros ?.
    rewrite /trace_alg_op -!decide_bool_decide.
    repeat destruct decide; done.
  Qed.

  Lemma trace_alg_op_eq_left' ft ft' :
    ft' `trace_prefix_of` ft →
    trace_alg_op (trace_alg_trace ft) (trace_alg_trace ft') = trace_alg_trace ft.
  Proof.
    intros ?.
    rewrite /trace_alg_op -!decide_bool_decide.
    repeat destruct decide; [|done|done].
    f_equal; apply trace_prefix_antisym; done.
  Qed.

  Lemma trace_alg_op_eq_neither' ft ft' :
    ¬ ft `trace_prefix_of` ft' →
    ¬ ft' `trace_prefix_of` ft →
    trace_alg_op (trace_alg_trace ft) (trace_alg_trace ft') = trace_alg_bot.
  Proof.
    intros ??.
    rewrite /trace_alg_op -!decide_bool_decide.
    repeat destruct decide; done.
  Qed.

  Lemma trace_alg_op_right_bot' fa :
    trace_alg_op fa trace_alg_bot = trace_alg_bot.
  Proof. destruct fa; done. Qed.

  Lemma trace_alg_op_left_bot' fa :
    trace_alg_op trace_alg_bot fa = trace_alg_bot.
  Proof. destruct fa; done. Qed.

  Lemma trace_alg_op_com fa fa' :
    trace_alg_op fa fa' = trace_alg_op fa' fa.
  Proof.
    destruct fa as [ft|]; destruct fa' as [ft'|]; [|done|done|done].
    destruct (decide (ft `trace_prefix_of` ft')).
    { rewrite (trace_alg_op_eq_right' ft ft'); last done.
      rewrite (trace_alg_op_eq_left' ft' ft); done. }
    destruct (decide (ft' `trace_prefix_of` ft)).
    { rewrite (trace_alg_op_eq_left' ft ft'); last done.
      rewrite (trace_alg_op_eq_right' ft' ft); done. }
    rewrite !trace_alg_op_eq_neither'; done.
  Qed.

  Lemma trace_alg_op_assoc fa fa' fa'' :
    trace_alg_op fa (trace_alg_op fa' fa'') =
    trace_alg_op (trace_alg_op fa fa') fa''.
  Proof.
    destruct fa as [ft|]; last done.
    destruct fa' as [ft'|]; last done.
    destruct fa'' as [ft''|]; last first.
    { by rewrite !trace_alg_op_right_bot'. }
    destruct (trace_alg_op_traces ft ft') as
        [[-> [Hf1 Hf2]]|[[-> Hf]|[-> Hf]]].
    - destruct (trace_alg_op_traces ft' ft'')
        as [[-> [Hg1 Hg2]]|[[-> Hg]|[-> Hg]]]; first done.
      + destruct (decide (ft `trace_prefix_of` ft'')).
        { edestruct (trace_prefixes_related ft ft'); done. }
        destruct (decide (ft' `trace_prefix_of` ft)); first done.
        rewrite (trace_alg_op_eq_neither' ft ft''); [done|done|].
        intros ?; apply Hf2; etrans; done.
      + rewrite (trace_alg_op_eq_neither' ft ft'); [done|done|].
        intros ?; apply Hf2; etrans; done.
    - destruct (trace_alg_op_traces ft' ft'')
        as [[-> [Hg1 Hg2]]|[[-> Hg]|[-> Hg]]]; first done.
      + apply trace_alg_op_eq_right'; etrans; done.
      + apply trace_alg_op_eq_right'; etrans; done.
    - destruct (trace_alg_op_traces ft' ft'')
        as [[-> [Hg1 Hg2]]|[[-> Hg]|[-> Hg]]]; [|done|].
      + rewrite (trace_alg_op_eq_neither' ft ft''); first done.
        * intros ?; apply Hg1; etrans; done.
        * intros ?.
            edestruct (trace_prefixes_related ft'' ft'); done.
      + rewrite !trace_alg_op_eq_left'; [done|etrans; done|done].
  Qed.

  Lemma trace_alg_op_idemp' fa : trace_alg_op fa fa = fa.
  Proof.
    destruct fa; last done.
    rewrite trace_alg_op_eq_left'; done.
  Qed.

  Local Instance trace_alg_valid_instance : Valid (trace_alg A L) :=
    λ fa, match fa with
          | trace_alg_trace _ => True
          | _ => False
          end.

  Lemma trace_alg_RAMixin : RAMixin (trace_alg A L).
  Proof.
    apply ra_total_mixin.
    - eauto.
    - intros fa fa' fa'' ->%leibniz_equiv; done.
    - by intros ?? ->%leibniz_equiv.
    - by intros ?? ->%leibniz_equiv.
    - intros ???; apply trace_alg_op_assoc.
    - intros ??; apply trace_alg_op_com.
    - intros ?; apply trace_alg_op_idemp'.
    - done.
    - done.
    - intros [] []; done.
  Qed.

  Canonical Structure trace_algR := discreteR (trace_alg A L) trace_alg_RAMixin.

  Global Instance trace_alg_cmra_total : CmraTotal trace_algR.
  Proof. econstructor; done. Qed.

  Global Instance trace_alg_cmra_discrete : CmraDiscrete trace_algR.
  Proof. econstructor; [apply _|done]. Qed.

  Global Instance trace_alg_core_id fa : CoreId fa.
  Proof. by constructor. Qed.

  Lemma trace_alg_included ft ft' :
    trace_alg_trace ft ≼ trace_alg_trace ft' ↔ ft `trace_prefix_of` ft'.
  Proof.
    split.
    - intros [fa'' Heq%leibniz_equiv].
      rewrite /op in Heq.
      destruct fa'' as [ft''|]; last by rewrite trace_alg_op_right_bot' in Heq.
      destruct (trace_alg_op_traces ft ft'') as [[Hop Hf]|[[Hop Hf]|[Hop Hf]]].
      + rewrite Hop in Heq; done.
      + rewrite Hop in Heq; simplify_eq; done.
      + rewrite Hop in Heq; simplify_eq; done.
    - intros Hincl; exists (trace_alg_trace ft').
      rewrite /op trace_alg_op_eq_right'; done.
  Qed.

  Lemma trace_alg_includedN ft ft' n :
    trace_alg_trace ft ≼{n} trace_alg_trace ft' ↔ ft `trace_prefix_of` ft'.
  Proof. apply trace_alg_included. Qed.

  Lemma trace_alg_op_idemp'' : IdemP eq (@op (trace_alg A L) _).
  Proof. intros ?; apply trace_alg_op_idemp'. Qed.

  Lemma trace_alg_op_idemp fa : fa ⋅ fa = fa.
  Proof. apply trace_alg_op_idemp'. Qed.

  Lemma trace_alg_op_eq_right ft ft' :
    ft `trace_prefix_of` ft' →
    trace_alg_trace ft ⋅ trace_alg_trace ft' = trace_alg_trace ft'.
  Proof. apply trace_alg_op_eq_right'. Qed.

  Lemma trace_alg_op_eq_left ft ft' :
    ft' `trace_prefix_of` ft →
    trace_alg_trace ft ⋅ trace_alg_trace ft' = trace_alg_trace ft.
  Proof. apply trace_alg_op_eq_left'. Qed.

  Lemma trace_alg_op_eq_neither ft ft' :
    ¬ ft `trace_prefix_of` ft' →
    ¬ ft' `trace_prefix_of` ft →
    trace_alg_trace ft ⋅ trace_alg_trace ft' = trace_alg_bot.
  Proof. apply trace_alg_op_eq_neither'. Qed.

  Lemma trace_alg_op_right_bot fa :
    fa ⋅ trace_alg_bot = trace_alg_bot.
  Proof. apply trace_alg_op_right_bot'. Qed.

  Lemma trace_alg_op_left_bot fa :
    trace_alg_op trace_alg_bot fa = trace_alg_bot.
  Proof. apply trace_alg_op_left_bot'. Qed.

  Lemma trace_alg_validN fa n : ✓{n} fa → ∃ ft, fa = trace_alg_trace ft.
  Proof. destruct fa; by eauto. Qed.

  Lemma trace_alg_valid fa : ✓ fa → ∃ ft, fa = trace_alg_trace ft.
  Proof. destruct fa; by eauto. Qed.

  Lemma trace_alg_pcore fa : pcore fa = Some fa.
  Proof. done. Qed.

  Lemma trace_alg_core fa : core fa = fa.
  Proof. done. Qed.

  Lemma trace_alg_local_update ft fa ft' :
    ft `trace_prefix_of` ft' →
    (trace_alg_trace ft, fa) ~l~> (trace_alg_trace ft', trace_alg_trace ft').
  Proof.
    intros Hpf.
    apply local_update_total_valid.
    intros _ [ft'' ->]%trace_alg_valid Hfts%trace_alg_included.
    setoid_replace (trace_alg_trace ft') with
        (trace_alg_trace ft' ⋅ trace_alg_trace ft) at 1; last first.
    { rewrite trace_alg_op_eq_left; done. }
    setoid_replace (trace_alg_trace ft') with
        (trace_alg_trace ft' ⋅ trace_alg_trace ft'') at 2; last first.
    { rewrite trace_alg_op_eq_left; etrans; done. }
    apply op_local_update.
    intros ??.
    rewrite trace_alg_op_eq_left; done.
  Qed.

End trace_alg_cmra.
