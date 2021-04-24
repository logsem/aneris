From aneris.program_logic Require Export weakestpre traces.

Set Default Proof Using "Type".

Delimit Scope inflist_scope with inflist.

CoInductive inflist (A : Type) : Type :=
| infnil
| infcons (x : A) (il : inflist A).

Bind Scope inflist_scope with inflist.

Arguments infnil {_}, _.
Arguments infcons {_} _ _%inflist.

Module InfListNotations.
Notation "[ ]" := infnil (format "[ ]") : inflist_scope.
Notation "[ x ]" := (infcons x infnil) : inflist_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (infcons x (infcons y .. (infcons z nil) ..)) : inflist_scope.

Infix "::" := infcons (at level 60, right associativity) : inflist_scope.
End InfListNotations.

Import InfListNotations.

Section inflist.
  Context {A : Type}.

  Implicit Types il : inflist A.

  Lemma inflist_unfold_fold il :
    il = match il with
         | [] => []
         | a :: il' => a :: il'
         end%inflist.
  Proof. destruct il; trivial. Qed.

End inflist.

Definition inf_execution_trace Λ := inflist (list (observation Λ) * cfg Λ).

Section inf_execution_trace.
  Context {Λ : language}.

  Definition inf_exec_prepend (κ : list (observation Λ)) (c : cfg Λ)
             (iex : inf_execution_trace Λ) : inf_execution_trace Λ :=
    ((κ, c) :: iex)%inflist.

  CoInductive valid_inf_exec :
    execution_trace Λ → inf_execution_trace Λ → Prop :=
  | valid_inf_exec_singleton ex :
      valid_exec ex → valid_inf_exec ex []%inflist
  | valid_inf_exec_step ex c κ c' iex :
      valid_exec ex →
      exec_ends_in ex c →
      step c κ c' →
      valid_inf_exec (exec_extend ex κ c') iex →
      valid_inf_exec ex (inf_exec_prepend κ c' iex).

End inf_execution_trace.

Definition inf_auxiliary_trace {Λ} (AS : AuxState Λ) := inflist (aux_state AS).

Definition inf_auxtr_prepend `{AS : AuxState Λ}
           (δ : aux_state AS) (atr : inf_auxiliary_trace AS) := infcons δ atr.

CoInductive valid_inf_system_trace `{AS : AuxState Λ}
            (Ψ : execution_trace Λ → auxiliary_trace AS → Prop) :
  execution_trace Λ → auxiliary_trace AS →
  inf_execution_trace Λ → inf_auxiliary_trace AS → Prop :=
| valid_system_trace_singleton ex atr :
    Ψ ex atr →
    valid_inf_system_trace Ψ ex atr []%inflist []%inflist
| valid_system_trace_step ex atr c κ c' δ δ' iex iatr :
    Ψ ex atr →
    exec_ends_in ex c →
    step c κ c' →
    auxtr_ends_in atr δ →
    valid_state_evolution AS c.2 δ κ c'.2 δ' →
    valid_inf_system_trace
      Ψ (exec_extend ex κ c') (auxtr_extend atr δ') iex iatr →
    valid_inf_system_trace
      Ψ ex atr (inf_exec_prepend κ c' iex) (inf_auxtr_prepend δ' iatr).

Section simulation.
  Context {Λ : language} {AS : AuxState Λ}
          {φ : execution_trace Λ → auxiliary_trace AS → Prop}.

  Implicit Types ex : execution_trace Λ.
  Implicit Types iex : inf_execution_trace Λ.

  Lemma valid_inf_exec_prepend_valid_exec_extend ex κ c iex :
    valid_inf_exec ex (inf_exec_prepend κ c iex) →
    valid_exec (exec_extend ex κ c).
  Proof.
    inversion 1 as [|???????? Hex]; simplify_eq.
    inversion Hex; done.
  Qed.

  Lemma produce_inf_aux_trace_next_aux_state_exists
        (ex : execution_trace Λ) (atr : auxiliary_trace AS)
        (Hcsm : continued_simulation φ ex atr)
        (c : cfg Λ) (κ : list (observation Λ))
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend κ c iex)) :
    ∃ δ, continued_simulation φ (exec_extend ex κ c) (auxtr_extend atr δ).
  Proof.
    apply continued_simulation_next_aux_state_exists; first done.
    eapply valid_inf_exec_prepend_valid_exec_extend; eauto.
  Qed.

  Definition produce_inf_aux_trace_next_aux_state
             (ex : execution_trace Λ) (atr : auxiliary_trace AS)
             (Hcsm : continued_simulation φ ex atr)
             (c : cfg Λ) (κ : list (observation Λ))
             (iex : inf_execution_trace Λ)
             (Hvex : valid_inf_exec ex (inf_exec_prepend κ c iex))
    : aux_state AS :=
    epsilon
      (produce_inf_aux_trace_next_aux_state_exists ex atr Hcsm c κ iex Hvex).

  Lemma produce_inf_aux_trace_next_aux_state_continued_simulation
        (ex : execution_trace Λ) (atr : auxiliary_trace AS)
        (Hcsm : continued_simulation φ ex atr)
        (c : cfg Λ) (κ : list (observation Λ))
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex (inf_exec_prepend κ c iex)) :
    continued_simulation
      φ
      (exec_extend ex κ c)
      (auxtr_extend
         atr (produce_inf_aux_trace_next_aux_state ex atr Hcsm c κ iex Hvex)).
  Proof.
    rewrite /produce_inf_aux_trace_next_aux_state.
    apply epsilon_correct.
  Qed.

  Local Lemma valid_inf_exec_adjust {ex c κ iex} :
    valid_inf_exec ex ((κ, c) :: iex)%inflist →
    valid_inf_exec (exec_extend ex κ c) iex.
  Proof. inversion 1; done. Qed.

  CoFixpoint produce_inf_aux_trace
          (ex : execution_trace Λ) (atr : auxiliary_trace AS)
          (Hcsm : continued_simulation φ ex atr)
          (iex : inf_execution_trace Λ)
          (Hvex : valid_inf_exec ex iex) :
    inf_auxiliary_trace AS :=
    match iex as l return valid_inf_exec ex l → inf_auxiliary_trace AS with
    | [] => λ _, []
    | (κ, c) :: iex' =>
      λ Hvex',
      let δ :=
          produce_inf_aux_trace_next_aux_state ex atr Hcsm c κ iex' Hvex'
      in
      δ :: (produce_inf_aux_trace
              (exec_extend ex κ c)
              (auxtr_extend atr δ)
              (produce_inf_aux_trace_next_aux_state_continued_simulation
                 ex atr Hcsm c κ iex' Hvex')
              iex'
              (valid_inf_exec_adjust Hvex'))
    end%inflist Hvex.

  Theorem produced_inf_aux_trace_valid_inf
        (ex : execution_trace Λ) (atr : auxiliary_trace AS)
        (Hcsm : continued_simulation φ ex atr)
        (iex : inf_execution_trace Λ)
        (Hvex : valid_inf_exec ex iex)
    : valid_inf_system_trace
        (continued_simulation φ)
        ex atr
        iex
        (produce_inf_aux_trace ex atr Hcsm iex Hvex).
  Proof.
    revert ex atr Hcsm iex Hvex; cofix CIH; intros ex atr Hcsm iex Hvex.
    destruct iex as [|[κ c] iex].
    - rewrite [produce_inf_aux_trace _ _ _ _ _]inflist_unfold_fold /=.
      constructor; trivial.
    - rewrite [produce_inf_aux_trace _ _ _ _ _]inflist_unfold_fold /=.
      pose proof (produce_inf_aux_trace_next_aux_state_continued_simulation
                    ex atr Hcsm c κ iex Hvex) as Hcsm'.
      pose proof (continued_simulation_valid_system_trace _ _ _ Hcsm') as Hvst.
      apply valid_system_trace_extend_inv in Hvst as (?&?&?&?&?&?&?).
      econstructor; eauto.
  Qed.

End simulation.
