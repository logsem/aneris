From trillium.program_logic Require Import language adequacy.

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

End XX.
