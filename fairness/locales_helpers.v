From trillium.program_logic Require Import language adequacy.
From trillium.fairness Require Import utils.

Section XX.
  Context `{Countable (locale Λ)}.

  Notation "'Tid'" := (locale Λ). 

  (* TODO: unify with existing locales_of_list_from_locale_from, 
     remove restriction for Λ *)

  Lemma locales_of_list_from_locale_from' tp0 tp1 ζ:
    ζ ∈ locales_of_list_from tp0 tp1 (Λ := Λ) ->
    is_Some (from_locale_from tp0 tp1 ζ).
  Proof.
    clear -tp0 tp1 ζ.
    revert tp0; induction tp1 as [|e1 tp1 IH]; intros tp0.
    { simpl. intros H. inversion H. }
    simpl.
    rewrite /locales_of_list_from /=. intros.
    destruct (decide (locale_of tp0 e1 = ζ)); simplify_eq; first set_solver.
    apply elem_of_cons in H as [?| ?]; [done| ].
    set_solver.
  Qed.

  Lemma locale_step_from_locale_src `{EqDecision (expr Λ)} c1 c2 ζ:
    locale_step c1 (Some ζ) c2 →
    is_Some(from_locale c1.1 ζ).
  Proof.
    intros Hstep. inversion Hstep; simplify_eq=>//.
    rewrite /from_locale. rewrite from_locale_from_Some; try done.
    apply prefixes_from_spec; eauto.
  Qed. 

  Definition locales_of_cfg (c: cfg Λ): gset (locale Λ) :=
    list_to_set (locales_of_list c.1).

  Definition locales_of_cfg_singleton e σ:
    locales_of_cfg ([e], σ) = {[ locale_of [] e ]}.
  Proof.
    rewrite /locales_of_cfg. simpl. set_solver.
  Qed.

  Lemma locales_of_cfg_Some τ tp σ:
    τ ∈ locales_of_cfg (tp, σ) -> is_Some (from_locale tp τ).
  Proof.
    rewrite /locales_of_cfg. simpl. rewrite elem_of_list_to_set.
    apply locales_of_list_from_locale_from'.
  Qed.

  Definition step_fork (c1 c2: cfg Λ): option (locale Λ) :=
    let diff := locales_of_cfg c2 ∖ locales_of_cfg c1 in
    gset_pick diff. 
   
  Definition extr_last_fork (extr: execution_trace Λ): option (locale Λ) :=
    match extr with
    | {tr[ _ ]} => None
    | extr' :tr[oζ]: c' => step_fork (trace_last extr') c'
    end. 

End XX.
