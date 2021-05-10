From aneris.prelude Require Export fixpoint classical.
From aneris.program_logic Require Export language.

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

  Definition trace_starts_in (ft : finite_trace A) (a : A) : Prop :=
    trace_first ft = a.

  Definition trace_ends_in (ft : finite_trace A) (a : A) : Prop :=
    trace_last ft = a.

  Lemma trace_singleton_starts_in c : trace_starts_in (trace_singleton c) c.
  Proof. done. Qed.

  Lemma trace_singleton_starts_in_inv c c' :
    trace_starts_in (trace_singleton c') c → c' = c.
  Proof. by inversion 1. Qed.

  Lemma trace_singleton_ends_in c : trace_ends_in (trace_singleton c) c.
  Proof. done. Qed.

  Lemma trace_singleton_ends_in_inv c c' :
    trace_ends_in (trace_singleton c') c → c' = c.
  Proof. by inversion 1. Qed.

  Lemma trace_starts_in_inj ex c c' :
   trace_starts_in ex c → trace_starts_in ex c' → c = c'.
  Proof. rewrite /trace_starts_in; intros ->; done. Qed.

  Lemma trace_ends_in_inj ex c c' :
   trace_ends_in ex c → trace_ends_in ex c' → c = c'.
  Proof. rewrite /trace_ends_in; intros ->; done. Qed.

  Definition trace_contract (ft ft' : finite_trace A) : Prop :=
    ∃ a, ft = trace_extend ft' a.

  Lemma trace_contract_of_extend ft a ft' :
    trace_contract (trace_extend ft a) ft' → ft' = ft.
  Proof. intros (? & Heq); simplify_eq; done. Qed.

  Lemma not_trace_contract_singleton a ft :
    ¬ trace_contract (trace_singleton a) ft.
  Proof. intros (?&?); destruct ft; simplify_eq/=. Qed.

  Lemma trace_extend_starts_in ft a' a :
    trace_starts_in ft a' → trace_starts_in (trace_extend ft a) a'.
  Proof. induction ft; auto. Qed.

  Lemma trace_extend_starts_in_inv ft a' a :
    trace_starts_in (trace_extend ft a) a' → trace_starts_in ft a'.
  Proof. induction ft; auto. Qed.

  Lemma trace_extend_ends_in ex c : trace_ends_in (trace_extend ex c) c.
  Proof. done. Qed.

  Lemma trace_does_ends_in ft : ∃ a, trace_ends_in ft a.
  Proof. destruct ft; rewrite /trace_ends_in; eauto. Qed.

End finite_trace_lib.

Definition execution_trace Λ := finite_trace (cfg Λ).

Record AuxState Λ : Type := {
  (** Auxiliary state tracked along the physical state. *)
  aux_state : Type;

  auxiliary_trace := finite_trace aux_state;

  (** The relation between the state before and after every step. *)
  valid_state_evolution :
    finite_trace (cfg Λ) → finite_trace aux_state → cfg Λ → aux_state → Prop;

  (** We can always take a valid step in the auxiliary state *)
  pure_step_evolution_valid extr atr c1 δ1 :
    trace_ends_in extr c1 →
    trace_ends_in atr δ1 →
    valid_state_evolution extr atr c1 δ1;
}.

Arguments aux_state {_}.
Arguments auxiliary_trace {_}.
Arguments valid_state_evolution {_ _}, {_} _.
Arguments pure_step_evolution_valid {_}.

Section execution_trace.
  Context {Λ : language}.

  Implicit Types c : cfg Λ.

  Inductive valid_exec : execution_trace Λ → Prop :=
  | valid_exec_singleton c : valid_exec (trace_singleton c)
  | valid_exec_step ex c c' :
      trace_ends_in ex c →
      step c c' →
      valid_exec ex →
      valid_exec (trace_extend ex c').

  Lemma valid_singleton_exec c : valid_exec (trace_singleton c).
  Proof. constructor. Qed.

  Lemma extend_valid_exec ex c c':
    valid_exec ex →
    trace_ends_in ex c →
    step c c' →
    valid_exec (trace_extend ex c').
  Proof.
    intros He; revert c c'.
    induction ex; econstructor; eauto.
  Qed.

  Lemma valid_exec_exec_extend_inv ex c':
    valid_exec (trace_extend ex c') →
    valid_exec ex ∧
    ∃ c, trace_ends_in ex c ∧ step c c'.
  Proof. inversion 1; eauto. Qed.

End execution_trace.

Section system_trace.
  Context `{AS : AuxState Λ}.

  Inductive valid_system_trace : execution_trace Λ → auxiliary_trace AS → Prop :=
  | valid_system_trace_singleton c δ :
      valid_system_trace (trace_singleton c) (trace_singleton δ)
  | valid_system_trace_step ex atr c c' δ δ' :
      trace_ends_in ex c →
      step c c' →
      trace_ends_in atr δ →
      valid_state_evolution ex atr c' δ' →
      valid_system_trace ex atr →
      valid_system_trace (trace_extend ex c') (trace_extend atr δ').

  Lemma valid_system_trace_valid_exec_trace ex atr :
    valid_system_trace ex atr → valid_exec ex.
  Proof. induction 1; econstructor; eauto. Qed.

  Lemma valid_system_trace_singletons c δ :
    valid_system_trace (trace_singleton c) (trace_singleton δ).
  Proof. constructor. Qed.

  Lemma valid_system_trace_extend ex atr c c' δ δ' :
    valid_system_trace ex atr →
    trace_ends_in ex c →
    step c c' →
    trace_ends_in atr δ →
    valid_state_evolution ex atr c' δ' →
    valid_system_trace (trace_extend ex c') (trace_extend atr δ').
  Proof.
    intros Heatr; revert c c' δ δ'.
    induction ex; econstructor; eauto.
  Qed.

  Lemma valid_system_trace_extend_inv ex atr c' δ' :
    valid_system_trace (trace_extend ex c') (trace_extend atr δ') →
    ∃ c δ,
      valid_system_trace ex atr ∧
      trace_ends_in ex c ∧
      step c c' ∧
      trace_ends_in atr δ ∧
      valid_state_evolution ex atr c' δ'.
  Proof. inversion 1; eauto 10. Qed.

  Lemma valid_system_trace_ends_in ex atr :
    valid_system_trace ex atr → ∃ c δ, trace_ends_in ex c ∧ trace_ends_in atr δ.
  Proof.
    inversion 1;
      eauto using trace_extend_ends_in, trace_singleton_ends_in,
      trace_extend_ends_in, trace_singleton_ends_in.
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
    valid_system_trace ex atr ∧
    φ ex atr ∧
    ∀ c c' δ,
      trace_ends_in ex c →
      trace_ends_in atr δ →
      step c c' →
      ∃ δ', continued_simulation (trace_extend ex c') (trace_extend atr δ').

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
    continued_simulation Φ ex tr → valid_system_trace ex tr.
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
    valid_exec (trace_extend ex c) →
    ∃ δ : aux_state AS,
      continued_simulation φ (trace_extend ex c) (trace_extend atr δ).
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre.
    intros (Hvst & HΦ & Hext) Hvex.
    pose proof (valid_system_trace_ends_in _ _ Hvst) as (c1 & δ1 & Hc1 & Hδ1).
    apply valid_exec_exec_extend_inv in Hvex as [Hvex (c1' & Hc1' & Hstep)].
    pose proof (trace_ends_in_inj _ _ _ Hc1 Hc1'); subst.
    eapply Hext; eauto.
  Qed.

  Lemma simulation_does_continue e σ δ φ :
    continued_simulation φ (trace_singleton ([e], σ)) (trace_singleton δ) →
    ∀ ex, trace_starts_in ex ([e], σ) → valid_exec ex →
          ∃ atr, continued_simulation φ ex atr.
  Proof.
    intros Hsm ex Hexstr Hex.
    induction Hex as [|? ? ? ? ? ? IHex].
    - apply trace_singleton_starts_in_inv in Hexstr as ->.
      exists (trace_singleton δ); eauto using valid_system_trace_singletons.
    - destruct IHex as [atr Hsim].
      { eapply trace_extend_starts_in_inv; eauto. }
      destruct (continued_simulation_next_aux_state_exists φ ex atr c');
        [done| |by eauto].
      econstructor; eauto.
  Qed.

End simulation.
