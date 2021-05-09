From aneris.prelude Require Export fixpoint classical.
From aneris.program_logic Require Export weakestpre.

Set Default Proof Using "Type".

Inductive finite_trace (A : Type) : Type :=
| trace_singleton (a : A)
| trace_extend (ft : finite_trace A) (a : A).

Global Arguments trace_singleton {_} _.
Global Arguments trace_extend {_} _ _.

Section finite_trace_lib.
  Context {A : Type}.

  Implicit Types a : A.
  Implicit Types ft : finite_trace A.

  Fixpoint trace_first (ft : finite_trace A) : A :=
    match ft with
    | trace_singleton a => a
    | trace_extend ft' _ => trace_first ft'
    end.

  Definition trace_last (ft : finite_trace A) : A :=
    match ft with
    | trace_singleton a => a
    | trace_extend _ a => a
    end.

End finite_trace_lib.

Definition execution_trace Λ := finite_trace (cfg Λ).

Section execution_trace.
  Context {Λ : language}.

  Implicit Types c : cfg Λ.

  Definition singleton_exec (c : cfg Λ) : execution_trace Λ :=
    trace_singleton c.

  Definition exec_starts_in (ex : execution_trace Λ) (c : cfg Λ) : Prop :=
    trace_first ex = c.

  Definition exec_ends_in (ex : execution_trace Λ) (c : cfg Λ) : Prop :=
    trace_last ex = c.

  Lemma singleton_exec_starts_in c : exec_starts_in (singleton_exec c) c.
  Proof. done. Qed.

  Lemma singleton_exec_starts_in_inv c c' :
    exec_starts_in (singleton_exec c') c → c' = c.
  Proof. by inversion 1. Qed.

  Lemma singleton_exec_ends_in c : exec_ends_in (singleton_exec c) c.
  Proof. done. Qed.

  Lemma singleton_exec_ends_in_inv c c' :
    exec_ends_in (singleton_exec c') c → c' = c.
  Proof. by inversion 1. Qed.

  Lemma exec_ends_in_inj ex c c' :
    exec_ends_in ex c → exec_ends_in ex c' → c = c'.
  Proof. rewrite /exec_ends_in; intros ->; congruence. Qed.

  Definition exec_extend (ex : execution_trace Λ) (c : cfg Λ) :=
    trace_extend ex c.

  Definition exec_contract (ex ex' : execution_trace Λ) : Prop :=
    ∃ c, ex = exec_extend ex' c.

  Lemma exec_contract_of_extend ex c ex' :
    exec_contract (exec_extend ex c) ex' → ex' = ex.
  Proof.
    rewrite /exec_contract /exec_extend.
    intros (? & Heq); simplify_eq.
    repeat match goal with
             Heq : _ |- _ => apply app_singleton_inv in Heq as [? ?]
           end; simplify_eq; done.
  Qed.

  Lemma not_exec_contract_singleton c ex :
    ¬ exec_contract (singleton_exec c) ex.
  Proof. intros (?&?); destruct ex; simplify_eq/=. Qed.

  Inductive valid_exec : execution_trace Λ → Prop :=
  | valid_exec_singleton c : valid_exec (singleton_exec c)
  | valid_exec_step ex c c' :
      exec_ends_in ex c →
      step c c' →
      valid_exec ex →
      valid_exec (exec_extend ex c').

  Lemma valid_singleton_exec c : valid_exec (singleton_exec c).
  Proof. constructor. Qed.

  Lemma exec_extend_starts_in ex c' c :
    exec_starts_in ex c' → exec_starts_in (exec_extend ex c) c'.
  Proof. induction ex; auto. Qed.

  Lemma exec_extend_starts_in_inv ex c' c :
    exec_starts_in (exec_extend ex c) c' →
    exec_starts_in ex c'.
  Proof. induction ex; auto. Qed.

  Lemma exec_extend_ends_in ex c : exec_ends_in (exec_extend ex c) c.
  Proof. done. Qed.

  Lemma valid_exec_ends_in ex : ∃ c, exec_ends_in ex c.
  Proof. destruct ex; rewrite /exec_ends_in; eauto. Qed.

  Lemma extend_valid_exec ex c c':
    valid_exec ex →
    exec_ends_in ex c →
    step c c' →
    valid_exec (exec_extend ex c').
  Proof.
    intros He; revert c c'.
    induction ex; econstructor; eauto.
  Qed.

  Lemma valid_exec_exec_extend_inv ex c':
    valid_exec (exec_extend ex c') →
    valid_exec ex ∧
    ∃ c, exec_ends_in ex c ∧ step c c'.
  Proof. inversion 1; eauto. Qed.

End execution_trace.

Definition auxiliary_trace {Λ} (AS : AuxState Λ) := finite_trace (aux_state AS).

Section auxiliary_trace.
  Context `{AS : AuxState Λ}.

  Definition singleton_auxtr (δ : aux_state AS) : auxiliary_trace AS :=
    trace_singleton δ.

  Definition auxtr_starts_in
             (atr : auxiliary_trace AS) (δ : aux_state AS) : Prop :=
    trace_first atr = δ.

  Definition auxtr_ends_in (atr : auxiliary_trace AS) (δ : aux_state AS)
    : Prop := trace_last atr = δ.

  Lemma singleton_auxtr_starts_in δ : auxtr_starts_in (singleton_auxtr δ) δ.
  Proof. done. Qed.

  Lemma singleton_auxtr_starts_in_inv δ δ' :
    auxtr_starts_in (singleton_auxtr δ') δ → δ' = δ.
  Proof. by inversion 1. Qed.

  Lemma singleton_auxtr_ends_in δ : auxtr_ends_in (singleton_auxtr δ) δ.
  Proof. done. Qed.

  Lemma singleton_auxtr_ends_in_inv δ δ' :
    auxtr_ends_in (singleton_auxtr δ') δ → δ' = δ.
  Proof. by inversion 1. Qed.

  Lemma auxtr_ends_in_inj atr δ δ' :
    auxtr_ends_in atr δ → auxtr_ends_in atr δ' → δ = δ'.
  Proof. rewrite /auxtr_ends_in; intros ->; congruence. Qed.

  Definition auxtr_extend (atr : auxiliary_trace AS) (δ : aux_state AS) :=
    trace_extend atr δ.

  Definition auxtr_contract (atr atr' : auxiliary_trace AS) : Prop :=
    ∃ δ, atr = auxtr_extend atr' δ.

  Lemma auxtr_contract_of_extend atr δ atr' :
    auxtr_contract (auxtr_extend atr δ) atr' → atr' = atr.
  Proof. intros [? ?]; simplify_eq; done. Qed.

  Lemma auxtr_extend_starts_in atr δ' δ :
    auxtr_starts_in atr δ' → auxtr_starts_in (auxtr_extend atr δ) δ'.
  Proof. induction atr; auto. Qed.

  Lemma auxtr_extend_ends_in atr δ : auxtr_ends_in (auxtr_extend atr δ) δ.
  Proof. done. Qed.

End auxiliary_trace.

Section system_trace.
  Context `(AS : AuxState Λ).

  Inductive valid_system_trace : execution_trace Λ → auxiliary_trace AS → Prop :=
  | valid_system_trace_singleton c δ :
      valid_system_trace (singleton_exec c) (singleton_auxtr δ)
  | valid_system_trace_step ex atr c c' δ δ' :
      exec_ends_in ex c →
      step c c' →
      auxtr_ends_in atr δ →
      valid_state_evolution AS c.2 δ c'.2 δ' →
      valid_system_trace ex atr →
      valid_system_trace (exec_extend ex c') (auxtr_extend atr δ').

  Lemma valid_system_trace_valid_exec_trace ex atr :
    valid_system_trace ex atr → valid_exec ex.
  Proof. induction 1; econstructor; eauto. Qed.

  Lemma valid_system_trace_singletons c δ :
    valid_system_trace (singleton_exec c) (singleton_auxtr δ).
  Proof. constructor. Qed.

  Lemma valid_system_trace_extend ex atr c c' δ δ' :
    valid_system_trace ex atr →
    exec_ends_in ex c →
    step c c' →
    auxtr_ends_in atr δ →
    valid_state_evolution AS c.2 δ c'.2 δ' →
    valid_system_trace (exec_extend ex c') (auxtr_extend atr δ').
  Proof.
    intros Heatr; revert c c' δ δ'.
    induction ex; econstructor; eauto.
  Qed.

  Lemma valid_system_trace_extend_inv ex atr c' δ' :
    valid_system_trace (exec_extend ex c') (auxtr_extend atr δ') →
    ∃ c δ,
      valid_system_trace ex atr ∧
      exec_ends_in ex c ∧
      step c c' ∧
      auxtr_ends_in atr δ ∧
      valid_state_evolution AS c.2 δ c'.2 δ'.
  Proof. inversion 1; eauto 10. Qed.

  Lemma valid_system_trace_ends_in ex atr :
    valid_system_trace ex atr → ∃ c δ, exec_ends_in ex c ∧ auxtr_ends_in atr δ.
  Proof.
    inversion 1;
      eauto using exec_extend_ends_in, singleton_exec_ends_in,
      auxtr_extend_ends_in, singleton_auxtr_ends_in.
  Qed.

End system_trace.

Section simulation.
  Context {Λ : language} {AS : AuxState Λ}.

  Implicit Types ex : execution_trace Λ.
  Implicit Types atr : auxiliary_trace AS.

  Definition continued_simulation_pre
             (φ : execution_trace Λ → auxiliary_trace AS → Prop)
             (continued_simulation :
                execution_trace Λ → auxiliary_trace AS → Prop) :
    execution_trace Λ → auxiliary_trace AS → Prop :=
    λ ex atr,
    valid_system_trace AS ex atr ∧
    φ ex atr ∧
    ∀ c c' δ,
      exec_ends_in ex c →
      auxtr_ends_in atr δ →
      step c c' →
      ∃ δ', continued_simulation (exec_extend ex c') (auxtr_extend atr δ').

  Local Definition continued_simulation_pre_curried
        (φ : execution_trace Λ → auxiliary_trace AS → Prop) :
    (execution_trace Λ * auxiliary_trace AS → Prop) →
    (execution_trace Λ * auxiliary_trace AS → Prop) :=
    λ ψ (exatr : execution_trace Λ * auxiliary_trace AS),
    (continued_simulation_pre φ (λ ex atr, ψ (ex, atr)) exatr.1 exatr.2).

  Lemma continued_simulation_pre_curried_mono
        (φ : execution_trace Λ → auxiliary_trace AS → Prop) :
    monotone (continued_simulation_pre_curried φ).
  Proof.
    intros P Q HPQ [ex atr] (?&?&HP); repeat (split; first done).
    intros ? ? ? ? ? ?.
    edestruct HP as (?&?); eauto.
  Qed.

  Definition continued_simulation
             (φ : execution_trace Λ → auxiliary_trace AS → Prop) :=
    λ ex atr, GFX (continued_simulation_pre_curried φ) (ex, atr).

  Lemma continued_simulation_unfold
        (φ : execution_trace Λ → auxiliary_trace AS → Prop) ex atr :
    continued_simulation φ ex atr ↔
    continued_simulation_pre φ (continued_simulation φ) ex atr.
  Proof.
    symmetry; rewrite /continued_simulation /=.
    apply (λ H, GFX_fixpoint (continued_simulation_pre_curried φ) H (_, _)).
    apply continued_simulation_pre_curried_mono.
  Qed.

  Lemma continued_simulation_valid_system_trace Φ ex tr:
    continued_simulation Φ ex tr → valid_system_trace AS ex tr.
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre; intuition.
  Qed.

  Lemma continued_simulation_rel Φ ex tr:
    continued_simulation Φ ex tr → Φ ex tr.
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre; intuition.
  Qed.

  Lemma continued_simulation_next_aux_state_exists
             (φ : execution_trace Λ → auxiliary_trace AS → Prop)
             (ex : execution_trace Λ) (atr : auxiliary_trace AS)
             (c : cfg Λ) :
    continued_simulation φ ex atr →
    valid_exec (exec_extend ex c) →
    ∃ δ : aux_state AS,
      continued_simulation φ (exec_extend ex c) (auxtr_extend atr δ).
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre.
    intros (Hvst & HΦ & Hext) Hvex.
    pose proof (valid_system_trace_ends_in _ _ _ Hvst) as (c1 & δ1 & Hc1 & Hδ1).
    apply valid_exec_exec_extend_inv in Hvex as [Hvex (c1' & Hc1' & Hstep)].
    pose proof (exec_ends_in_inj _ _ _ Hc1 Hc1'); subst.
    eapply Hext; eauto.
  Qed.

  Lemma simulation_does_continue e σ δ φ :
    continued_simulation φ (singleton_exec ([e], σ)) (singleton_auxtr δ) →
    ∀ ex, exec_starts_in ex ([e], σ) → valid_exec ex →
          ∃ atr, continued_simulation φ ex atr.
  Proof.
    intros Hsm ex Hexstr Hex.
    induction Hex as [|? ? ? ? ? ? IHex].
    - apply singleton_exec_starts_in_inv in Hexstr as ->.
      exists (singleton_auxtr δ); eauto using valid_system_trace_singletons.
    - destruct IHex as [atr Hsim].
      { eapply exec_extend_starts_in_inv; eauto. }
      destruct (continued_simulation_next_aux_state_exists φ ex atr c');
        [done| |by eauto].
      econstructor; eauto.
  Qed.

End simulation.
