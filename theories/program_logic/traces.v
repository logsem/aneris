From aneris.program_logic Require Export weakestpre.

Set Default Proof Using "Type".
Import uPred.

Record execution_trace Λ := {
  extr_confs : list (cfg Λ);
  extr_obs : list (list (observation Λ)); }.

Arguments extr_confs {_} _.
Arguments extr_obs {_} _.

Lemma app_singleton_inv {A} (e e' : list A) (x x' : A) :
  e ++ [x] = e' ++ [x'] → e = e' ∧ x = x'.
Proof.
  rewrite -(reverse_involutive (e ++ [x])).
  rewrite -(reverse_involutive (e' ++ [x'])).
  intros Heq.
  eapply (inj (R := (=))) in Heq; last apply _.
  rewrite !reverse_app /= in Heq; simplify_eq; done.
Qed.

Section execution_trace.
  Context {Λ : language}.

  Implicit Types c : cfg Λ.
  Implicit Types κ : list (observation Λ).

  Definition singleton_exec (c : cfg Λ) : execution_trace Λ :=
    {| extr_confs := [c]; extr_obs := []; |}.

  Definition exec_starts_in (ex : execution_trace Λ) (c : cfg Λ) : Prop :=
    hd_error (extr_confs ex) = Some c.

  Definition exec_ends_in (ex : execution_trace Λ) (c : cfg Λ) : Prop :=
    last (extr_confs ex) = Some c.

  Definition exec_last_obs (ex : execution_trace Λ) (κs : list (observation Λ))
    : Prop := last (extr_obs ex) = Some κs.

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

  Lemma exec_last_obs_inj ex κs κs' :
    exec_last_obs ex κs → exec_last_obs ex κs' → κs = κs'.
  Proof. rewrite /exec_last_obs; intros ->; congruence. Qed.

  Definition exec_extend (ex : execution_trace Λ)
             (κ : list (observation Λ)) (c : cfg Λ) :=
    {| extr_confs := extr_confs ex ++ [c];
       extr_obs := extr_obs ex ++ [κ]; |}.

  Definition exec_contract (ex ex' : execution_trace Λ) : Prop :=
    ∃ c κ, ex = exec_extend ex' κ c.

  Lemma exec_contract_of_extend ex κ c ex' :
    exec_contract (exec_extend ex κ c) ex' → ex' = ex.
  Proof.
    rewrite /exec_contract /exec_extend.
    destruct ex as [confs obs].
    destruct ex' as [confs' obs'].
    intros (? & ? & Heq); simplify_eq.
    repeat match goal with
             Heq : _ |- _ => apply app_singleton_inv in Heq as [? ?]
           end; simplify_eq; done.
  Qed.

  Lemma not_exec_contract_singleton c ex :
    ¬ exec_contract (singleton_exec c) ex.
  Proof. intros (?&?&?); destruct ex as [? []]; simplify_eq. Qed.

  Inductive valid_exec : execution_trace Λ → Prop :=
  | valid_exec_singleton c : valid_exec (singleton_exec c)
  | valid_exec_step ex c κ c' :
      exec_ends_in ex c →
      step c κ c' →
      valid_exec ex →
      valid_exec (exec_extend ex κ c').

  Local Lemma valid_exec_non_empty ex :
    valid_exec ex → extr_confs ex ≠ [].
  Proof.
    inversion 1; simplify_eq; simpl in *.
    - intros ?; simplify_eq.
    - intros [? ?]%app_nil; simplify_eq.
  Qed.

  Lemma valid_singleton_exec c : valid_exec (singleton_exec c).
  Proof. constructor. Qed.

  Lemma exec_extend_starts_in ex c' c κ :
    exec_starts_in ex c' → exec_starts_in (exec_extend ex κ c) c'.
  Proof.
    rewrite /exec_starts_in /exec_extend /=; intros Hec'.
    assert (extr_confs ex = c' :: tail (extr_confs ex)) as ->
        by by apply hd_error_tl_repr.
    done.
  Qed.
  Lemma exec_extend_starts_in_inv ex c' c κ :
    valid_exec ex →
    exec_starts_in (exec_extend ex κ c) c' →
    exec_starts_in ex c'.
  Proof.
    intros ?%valid_exec_non_empty.
    destruct ex as [[] obs]; simplify_eq;
      rewrite /exec_starts_in /exec_extend /=; done.
  Qed.

  Lemma exec_extend_ends_in ex c κ : exec_ends_in (exec_extend ex κ c) c.
  Proof. apply last_snoc. Qed.

  Lemma exec_extend_last_obs ex c κ : exec_last_obs (exec_extend ex κ c) κ.
  Proof. apply last_snoc. Qed.

  Lemma valid_exec_ends_in ex : valid_exec ex → ∃ c, exec_ends_in ex c.
  Proof.
    inversion 1; eauto using exec_extend_ends_in, singleton_exec_ends_in.
  Qed.

  Lemma extend_valid_exec ex c κ c':
    valid_exec ex →
    exec_ends_in ex c →
    step c κ c' →
    valid_exec (exec_extend ex κ c').
  Proof.
    intros He; revert c κ c'.
    induction He as [|? ? ? ? ? ? ? IHe]; intros c1 κ' c2.
    - intros; econstructor; [done|done|constructor].
    - intros; econstructor; [done|done|].
      eapply IHe; eauto.
  Qed.

End execution_trace.

Definition auxiliary_trace {Λ} (AS : AuxState Λ) := list (aux_state AS).

Section auxiliary_trace.
  Context `{AS : AuxState Λ}.

  Definition singleton_auxtr (δ : aux_state AS) : auxiliary_trace AS := [δ].

  Definition auxtr_starts_in
             (atr : auxiliary_trace AS) (δ : aux_state AS) : Prop :=
    hd_error atr = Some δ.

  Definition auxtr_ends_in (atr : auxiliary_trace AS) (δ : aux_state AS)
    : Prop := last atr = Some δ.

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
    atr ++ [δ].

  Definition auxtr_contract (atr atr' : auxiliary_trace AS) : Prop :=
    ∃ δ, atr = auxtr_extend atr' δ.

  Lemma auxtr_contract_of_extend atr δ atr' :
    auxtr_contract (auxtr_extend atr δ) atr' → atr' = atr.
  Proof. intros [? [? ?]%app_singleton_inv]; done. Qed.

  Lemma auxtr_extend_starts_in atr δ' δ :
    auxtr_starts_in atr δ' → auxtr_starts_in (auxtr_extend atr δ) δ'.
  Proof.
    rewrite /auxtr_starts_in /auxtr_extend /=; intros Hec'.
    assert (atr = δ' :: tail atr) as -> by by apply hd_error_tl_repr.
    done.
  Qed.

  Lemma auxtr_extend_ends_in atr δ : auxtr_ends_in (auxtr_extend atr δ) δ.
  Proof. apply last_snoc. Qed.

End auxiliary_trace.

Section system_trace.
  Context `(AS : AuxState Λ).

  Inductive valid_system_trace : execution_trace Λ → auxiliary_trace AS → Prop :=
  | valid_system_trace_singleton c δ :
      valid_system_trace (singleton_exec c) (singleton_auxtr δ)
  | valid_system_trace_step ex atr c κ c' δ δ' :
      exec_ends_in ex c →
      step c κ c' →
      auxtr_ends_in atr δ →
      valid_state_evolution AS c.2 δ κ c'.2 δ' →
      valid_system_trace ex atr →
      valid_system_trace (exec_extend ex κ c') (auxtr_extend atr δ').

  Lemma valid_system_trace_valid_exec_trace ex atr :
    valid_system_trace ex atr → valid_exec ex.
  Proof. induction 1; econstructor; eauto. Qed.

  Lemma valid_system_trace_singletons c δ :
    valid_system_trace (singleton_exec c) (singleton_auxtr δ).
  Proof. constructor. Qed.

  Lemma valid_system_trace_extend ex atr c κ c' δ δ' :
    valid_system_trace ex atr →
    exec_ends_in ex c →
    step c κ c' →
    auxtr_ends_in atr δ →
    valid_state_evolution AS c.2 δ κ c'.2 δ' →
    valid_system_trace (exec_extend ex κ c') (auxtr_extend atr δ').
  Proof.
    intros Heatr; revert c κ c' δ δ'.
    induction Heatr as [|? ? ? ? ? ? ? ? ? ? ? ? IHeatr]; intros c1 κ' c2.
    - intros; econstructor; [done|done|done|done|constructor].
    - intros; econstructor; [done|done|done|done|].
      eapply IHeatr; eauto.
  Qed.

  Lemma valid_system_trace_ends_in ex atr :
    valid_system_trace ex atr → ∃ c δ, exec_ends_in ex c ∧ auxtr_ends_in atr δ.
  Proof.
    inversion 1;
      eauto using exec_extend_ends_in, singleton_exec_ends_in,
      auxtr_extend_ends_in, singleton_auxtr_ends_in.
  Qed.

End system_trace.
