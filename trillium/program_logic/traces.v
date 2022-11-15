From trillium.traces Require Export trace infinite_trace.
From trillium.program_logic Require Import language.

Import InfListNotations.

Definition ex_label Λ : Type := (locale Λ + config_label Λ).

Definition execution_trace Λ := finite_trace (cfg Λ) (ex_label Λ).

Record Model : Type := MkModel {
  mstate:> Type;
  mlabel: Type;
  mtrans: mstate -> mlabel -> mstate -> Prop;
}.

Arguments mtrans {_} _ _ _.

(* Notation olocale Λ := (option (locale Λ)). *)

Notation auxiliary_trace m := (finite_trace m.(mstate) m.(mlabel)).

Section execution_trace.
  Context {Λ : language}.

  Implicit Types c : cfg Λ.

  Definition valid_exec (ex : execution_trace Λ) : Prop :=
    trace_steps locale_step ex.

  Lemma valid_singleton_exec c : valid_exec (trace_singleton c).
  Proof. constructor. Qed.

  Lemma extend_valid_exec ex c ζ c':
    valid_exec ex →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_exec (ex :tr[ζ]: c').
  Proof. econstructor; done. Qed.

  Lemma valid_exec_exec_extend_inv ex ζ c':
    valid_exec (trace_extend ex ζ c') →
    valid_exec ex ∧
    ∃ c, trace_ends_in ex c ∧ locale_step c ζ c'.
  Proof. apply trace_steps_step_inv. Qed.

End execution_trace.

Section system_trace.
  Context {Λ : language} {M : Model}.

  Implicit Types ex : execution_trace Λ.
  Implicit Types atr : auxiliary_trace M.
  Implicit Types ζ : ex_label Λ.
  Implicit Types ℓ : mlabel M.

  Inductive valid_system_trace : execution_trace Λ → auxiliary_trace M → Prop :=
  | valid_system_trace_singleton c δ :
      valid_system_trace (trace_singleton c) (trace_singleton δ)
  | valid_system_trace_step ex atr c c' δ' ζ ℓ:
      trace_ends_in ex c →
      locale_step c ζ c' →
      valid_system_trace ex atr →
      valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ').

  Lemma valid_system_trace_valid_exec_trace ex atr :
    valid_system_trace ex atr → valid_exec ex.
  Proof. induction 1; econstructor; eauto. Qed.

  Lemma valid_system_trace_singletons c δ :
    valid_system_trace (trace_singleton c) (trace_singleton δ).
  Proof. constructor. Qed.

  Lemma valid_system_trace_extend ex atr c c' δ' ζ ℓ:
    valid_system_trace ex atr →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ').
  Proof.
    intros Heatr; revert c c' δ' ζ ℓ.
    induction ex; econstructor; eauto.
  Qed.

  Lemma valid_system_trace_extend_inv ex atr c' δ' ζ ℓ:
    valid_system_trace (trace_extend ex ζ c') (trace_extend atr ℓ δ') →
    ∃ c,
      valid_system_trace ex atr ∧
      trace_ends_in ex c ∧
      locale_step c ζ c'.
  Proof. inversion 1; eauto. Qed.

  Lemma valid_system_trace_ends_in ex atr :
    valid_system_trace ex atr → ∃ c δ, trace_ends_in ex c ∧ trace_ends_in atr δ.
  Proof.
    inversion 1;
      eauto using trace_extend_ends_in, trace_singleton_ends_in,
      trace_extend_ends_in, trace_singleton_ends_in.
  Qed.

  Lemma trace_steps2_trace_steps (R : M -> mlabel M -> M -> Prop) :
    (∀ ex atr c δ c' δ' ζ ℓ,
        trace_ends_in ex c →
        trace_ends_in atr δ →
        locale_step c ζ c' →
        R δ ℓ δ') →
    ∀ ex atr, valid_system_trace ex atr → valid_exec ex ∧ trace_steps R atr.
  Proof.
    intros HR ex ex' Hexs.
    induction Hexs as [|?????????? []].
    - split; constructor.
    - split; econstructor; [done|done|done|done|eapply HR=>//|done].
  Qed.

End system_trace.

Section simulation.
  Context {Λ : language} {M : Model}.
  Variable (labels_match : ex_label Λ → mlabel M → Prop).

  Implicit Types ex : execution_trace Λ.
  Implicit Types atr : auxiliary_trace M.

  Definition continued_simulation_pre
             (φ : execution_trace Λ → auxiliary_trace M → Prop)
             (continued_simulation :
                execution_trace Λ → auxiliary_trace M → Prop) :
    execution_trace Λ → auxiliary_trace M → Prop :=
    λ ex atr,
      φ ex atr ∧
      ∀ c c' ζ,
        trace_ends_in ex c →
        locale_step c ζ c' →
        ∃ δ' ℓ, continued_simulation (trace_extend ex ζ c') (trace_extend atr ℓ δ').

  Local Definition continued_simulation_pre_curried
        (φ : execution_trace Λ → auxiliary_trace M → Prop) :
    (execution_trace Λ * auxiliary_trace M → Prop) →
    (execution_trace Λ * auxiliary_trace M → Prop) :=
    λ ψ (exatr : execution_trace Λ * auxiliary_trace M),
    (continued_simulation_pre φ (λ ex atr, ψ (ex, atr)) exatr.1 exatr.2).

  Lemma continued_simulation_pre_curried_mono
        (φ : execution_trace Λ → auxiliary_trace M → Prop) :
    monotone (continued_simulation_pre_curried φ).
  Proof.
    intros P Q HPQ [ex atr].
    intros [? HP]. split; [done|].
    intros ?????.
    edestruct HP as (?&?&?); eauto.
  Qed.

  Definition continued_simulation (φ : execution_trace Λ → auxiliary_trace M → Prop) :=
    λ ex atr, GFX (continued_simulation_pre_curried φ) (ex, atr).

  Lemma continued_simulation_unfold
        (φ : execution_trace Λ → auxiliary_trace M → Prop) ex atr :
    continued_simulation φ ex atr ↔
    continued_simulation_pre φ (continued_simulation φ) ex atr.
  Proof.
    symmetry; rewrite /continued_simulation /=.
    apply (λ H, GFX_fixpoint (continued_simulation_pre_curried φ) H (_, _)).
    apply continued_simulation_pre_curried_mono.
  Qed.

  Lemma continued_simulation_rel Φ ex tr:
    continued_simulation Φ ex tr → Φ ex tr.
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre; intuition.
  Qed.

  Lemma continued_simulation_next_aux_state_exists
             (φ : execution_trace Λ → auxiliary_trace M → Prop)
             (ex : execution_trace Λ) (atr : auxiliary_trace M)
             (c : cfg Λ) ζ:
    continued_simulation φ ex atr →
    valid_exec (trace_extend ex ζ c) →
    ∃ δℓ, continued_simulation φ (trace_extend ex ζ c) (trace_extend atr δℓ.2 δℓ.1).
  Proof.
    rewrite continued_simulation_unfold /continued_simulation_pre.
    intros (HΦ & Hext) Hvex.
    apply valid_exec_exec_extend_inv in Hvex as [Hvex (c1 & Hc1 & Hstep)].
    edestruct Hext as (?&?&?); [done..|].
    by eexists (_,_).
  Qed.

  Lemma simulation_does_continue e σ δ φ :
    continued_simulation φ (trace_singleton ([e], σ)) (trace_singleton δ) →
    ∀ ex, trace_starts_in ex ([e], σ) →
          valid_exec ex →
          ∃ atr, trace_starts_in atr δ ∧ continued_simulation φ ex atr.
  Proof.
    intros Hsm ex Hexstr Hex.
    induction Hex as [|? ? ? ? ? ? ? IHex].
    - apply trace_singleton_starts_in_inv in Hexstr as ->.
      exists (trace_singleton δ). done.
    - destruct IHex as [atr [Hstarts Hsim]].
      { eapply trace_extend_starts_in_inv; eauto. }
      edestruct (continued_simulation_next_aux_state_exists φ ex atr) as ([??]&?);
        [done| |].
      { econstructor; eauto. }
      eexists. split; [|done].
      by apply trace_extend_starts_in.
  Qed.

  Lemma continued_simulation_impl (Φ Ψ: execution_trace Λ → auxiliary_trace M → Prop) ex tr:
    (∀ ex tr, Φ ex tr → Ψ ex tr) →
    continued_simulation Φ ex tr → continued_simulation Ψ ex tr.
  Proof.
    intros Himpl Hphi.
    rewrite /continued_simulation /GFX.
    exists (λ '(ex, atr), continued_simulation Φ ex atr).
    split; [done|].
    intros [? ?] ?.
    rewrite /continued_simulation_pre_curried /continued_simulation_pre /=.
    split.
    { by eapply Himpl, continued_simulation_rel. }
    intros c c' ζ ? ?.
    move: H.
    rewrite continued_simulation_unfold /continued_simulation_pre.
    intros [? ?]. eauto.
  Qed.

End simulation.

Definition inf_execution_trace Λ := inflist (ex_label Λ * cfg Λ).

Section inf_execution_trace.
  Context {Λ : language}.

  Definition inf_exec_prepend ζ (c : cfg Λ)
             (iex : inf_execution_trace Λ) : inf_execution_trace Λ :=
    ((ζ, c) :: iex)%inflist.

  CoInductive valid_inf_exec :
    execution_trace Λ → inf_execution_trace Λ → Prop :=
  | valid_inf_exec_singleton ex :
      valid_exec ex → valid_inf_exec ex []%inflist
  | valid_inf_exec_step ex c c' iex ζ:
      valid_exec ex →
      trace_ends_in ex c →
      locale_step c ζ c' →
      valid_inf_exec (trace_extend ex ζ c') iex →
      valid_inf_exec ex (inf_exec_prepend ζ c' iex).

End inf_execution_trace.

Definition inf_auxiliary_trace (M : Model) := inflist ((mlabel $ M) * M).

Definition inf_auxtr_prepend {M : Model} ℓ (δ : M) (atr : inf_auxiliary_trace M) :=
  infcons (ℓ,δ) atr.

CoInductive valid_inf_system_trace {Λ M}
            (Ψ : execution_trace Λ → auxiliary_trace M → Prop) :
  execution_trace Λ → auxiliary_trace M →
  inf_execution_trace Λ → inf_auxiliary_trace M → Prop :=
| valid_inf_system_trace_singleton ex atr :
    Ψ ex atr →
    valid_inf_system_trace Ψ ex atr []%inflist []%inflist
| valid_inf_system_trace_step ex atr c c' δ' iex iatr ζ ℓ:
    Ψ ex atr →
    trace_ends_in ex c →
    locale_step c ζ c' →
    valid_inf_system_trace
      Ψ (trace_extend ex ζ c') (trace_extend atr ℓ δ') iex iatr →
    valid_inf_system_trace
      Ψ ex atr (inf_exec_prepend ζ c' iex) (inf_auxtr_prepend ℓ δ' iatr).

Lemma valid_inf_system_trace_inv {Λ M}
      (Ψ : execution_trace Λ → auxiliary_trace M → Prop) ex atr iex itr :
  valid_inf_system_trace Ψ ex atr iex itr →
  Ψ ex atr.
Proof. by inversion 1. Qed.

Section simulation.
  Context {Λ : language} {M : Model}
          (φ : execution_trace Λ → auxiliary_trace M → Prop).

  Implicit Types ex : execution_trace Λ.
  Implicit Types iex : inf_execution_trace Λ.
  Implicit Types atr : auxiliary_trace M.
  Implicit Types ζ : ex_label Λ.
  Implicit Types ℓ : mlabel M.

  Lemma valid_system_trace_start_or_contract ex atr :
    valid_system_trace ex atr →
    (ex = {tr[trace_first ex]} ∧ atr = {tr[trace_first atr]}) ∨
    (∃ ex' atr' oζ ℓ, trace_contract ex oζ ex' ∧ trace_contract atr ℓ atr').
  Proof. rewrite /trace_contract; inversion 1; simplify_eq; eauto 10. Qed.

  Lemma valid_inf_exec_prepend_valid_exec_extend ex c iex ζ:
    valid_inf_exec ex (inf_exec_prepend ζ c iex) →
    valid_exec (trace_extend ex ζ c).
  Proof.
    inversion 1 as [|???????? Hex]; simplify_eq.
    inversion Hex; done.
  Qed.

  Lemma produce_inf_aux_trace_next_aux_state_exists
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (Hcsm : continued_simulation φ ex atr)
        (c : cfg Λ)
        (ζ: ex_label Λ)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex)) :
    ∃ δℓ, continued_simulation φ (trace_extend ex ζ c) (trace_extend atr δℓ.2 δℓ.1).
  Proof.
    eapply continued_simulation_next_aux_state_exists; first done.
    eapply valid_inf_exec_prepend_valid_exec_extend; eauto.
  Qed.

  Definition produce_inf_aux_trace_next_aux_state
             (ex : execution_trace Λ) (atr : auxiliary_trace M)
             (Hcsm : continued_simulation φ ex atr)
             (c : cfg Λ)
             (ζ: ex_label Λ)
             (iex : inf_execution_trace Λ)
             (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex))
    : (M * mlabel M)%type :=
    epsilon
      (produce_inf_aux_trace_next_aux_state_exists ex atr Hcsm c ζ iex Hvex).

  Definition trace_extend_uncurry (tr: auxiliary_trace M) xy := trace_extend tr xy.2 xy.1.

  Lemma produce_inf_aux_trace_next_aux_state_continued_simulation
        (ex : execution_trace Λ) (atr : auxiliary_trace M)
        (Hcsm : continued_simulation φ ex atr)
        (c : cfg Λ)
        (ζ: ex_label Λ)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend ζ c iex)) :
    continued_simulation
      φ
      (trace_extend ex ζ c)
      (trace_extend_uncurry
         atr (produce_inf_aux_trace_next_aux_state ex atr Hcsm c ζ iex Hvex)).
  Proof.
    rewrite /produce_inf_aux_trace_next_aux_state.
    apply epsilon_correct.
  Qed.

  Local Lemma valid_inf_exec_adjust {ex c iex ζ} :
    valid_inf_exec ex ((ζ, c) :: iex)%inflist →
    valid_inf_exec (trace_extend ex ζ c) iex.
  Proof. inversion 1; done. Qed.

  Lemma valid_inf_exe_valid_exec ex iex :
    valid_inf_exec ex iex → valid_exec ex.
  Proof. by destruct 1. Qed.
  Lemma valid_inf_exe_take_drop ex iex n :
    valid_inf_exec ex iex → valid_inf_exec (ex +trl+ inflist_take n iex) (inflist_drop n iex).
  Proof.
    revert ex iex; induction n as [|n IHn]; intros ex iex Hvl; simpl; first done.
    destruct iex as [|[??]]; simpl; first done.
    apply IHn.
    apply valid_inf_exec_adjust; done.
  Qed.

  CoFixpoint produce_inf_aux_trace
          (ex : execution_trace Λ) (atr : auxiliary_trace M)
          (Hcsm : continued_simulation φ ex atr)
          (iex : inf_execution_trace Λ)
          (Hvex : valid_inf_exec ex iex) :
    inf_auxiliary_trace M :=
    match iex as l return valid_inf_exec ex l → inf_auxiliary_trace M with
    | [] => λ _, []
    | (ζ, c) :: iex' =>
      λ Hvex',
      let δℓ :=
          produce_inf_aux_trace_next_aux_state ex atr Hcsm c ζ iex' Hvex'
      in
      (δℓ.2, δℓ.1) :: (produce_inf_aux_trace
              (trace_extend ex ζ c)
              (trace_extend atr δℓ.2 δℓ.1)
              (produce_inf_aux_trace_next_aux_state_continued_simulation
                 ex atr Hcsm c ζ iex' Hvex')
              iex'
              (valid_inf_exec_adjust Hvex'))
    end%inflist Hvex.

  Theorem produced_inf_aux_trace_valid_inf
          (ex : execution_trace Λ) (atr : auxiliary_trace M)
          (Hst : valid_system_trace ex atr)
          (Hcsm : continued_simulation φ ex atr)
          (iex : inf_execution_trace Λ)
          (Hvex : valid_inf_exec ex iex)
    : valid_inf_system_trace
        (continued_simulation φ)
        ex atr
        iex
        (produce_inf_aux_trace ex atr Hcsm iex Hvex).
  Proof.
    revert ex atr Hcsm Hst iex Hvex; cofix CIH; intros ex atr Hcsm Hst iex Hvex.
    destruct iex as [|[ζ c] iex].
    - rewrite [produce_inf_aux_trace _ _ _ _ _]inflist_unfold_fold /=.
      constructor; trivial.
    - rewrite [produce_inf_aux_trace _ _ _ _ _]inflist_unfold_fold /=.
      pose proof (produce_inf_aux_trace_next_aux_state_continued_simulation
                    ex atr Hcsm c ζ iex Hvex) as Hcsm'.
      assert (valid_system_trace
                (ex :tr[ζ]: c)
                (trace_extend_uncurry
                   atr (produce_inf_aux_trace_next_aux_state ex atr Hcsm c ζ iex Hvex)))
             as Hst'.
      { inversion Hvex; simplify_eq.
        econstructor; try done. }
      apply valid_system_trace_extend_inv in Hst' as (?&?&?&?).
      econstructor; eauto using valid_system_trace_step.
  Qed.

End simulation.
