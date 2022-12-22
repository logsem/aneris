(** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in the Iris sense. *)
From iris.prelude Require Export prelude.
From trillium.program_logic Require Import language.

(** TAKE CARE: When you define an [ectxLanguage] canonical structure for your
language, you need to also define a corresponding [language] canonical
structure. Use the coercion [LanguageOfEctx] as defined in the bottom of this
file for doing that. *)

Section ectx_language_mixin.
  Context {expr val ectx state : Type}.
  Context {locale : Type}.
  Context {config_label : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (empty_ectx : ectx).
  Context (comp_ectx : ectx → ectx → ectx).
  Context (fill : ectx → expr → expr).
  Context (head_step : expr → state → expr → state → list expr → Prop).
  Context (config_step : state → config_label → state → Prop).
  Context (locale_of : list expr → expr → locale).
  Context (config_enabled : config_label → state → Prop).

  Notation locales_equiv t0 t0' :=
    (Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0')).

  Record EctxLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_head_stuck e1 σ1 e2 σ2 efs :
      head_step e1 σ1 e2 σ2 efs → to_val e1 = None;

    mixin_fill_empty e : fill empty_ectx e = e;
    mixin_fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
    mixin_fill_inj K : Inj (=) (=) (fill K);
    mixin_fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e);
    mixin_fill_positive K K' e e' :
      to_val e = None → to_val e' = None →
      fill K e = fill K' e' →
      (∃ K'', K' = comp_ectx K K'') ∨ (∃ K'', K = comp_ectx K' K'');

    (** Given a head redex [e1_redex] somewhere in a term, and another
        decomposition of the same term into [fill K' e1'] such that [e1'] is not
        a value, then the head redex context is [e1']'s context [K'] filled with
        another context [K''].  In particular, this implies [e1 = fill K''
        e1_redex] by [fill_inj], i.e., [e1]' contains the head redex.)

        This implies there can be only one head redex, see
        [head_redex_unique]. *)
    mixin_step_by_val K' K_redex e1' e1_redex σ1 e2 σ2 efs :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 e2 σ2 efs →
      ∃ K'', K_redex = comp_ectx K' K'';

    (** If [fill K e] takes a head step, then either [e] is a value or [K] is
        the empty evaluation context. In other words, if [e] is not a value
        wrapping it in a context does not add new head redex positions. *)
    mixin_head_ctx_step_val K e σ1 e2 σ2 efs :
      head_step (fill K e) σ1 e2 σ2 efs → is_Some (to_val e) ∨ K = empty_ectx;
    mixin_locale_step e1 e2 t1 σ1 σ2 efs: head_step e1 σ1 e2 σ2 efs ->
                                         locale_of t1 e1 = locale_of t1 e2;
    mixin_locale_fill e K t1: locale_of t1 (fill K e) = locale_of t1 e;
    mixin_locale_equiv t t' e: locales_equiv t t' -> locale_of t e = locale_of t' e;
    mixin_locale_injective tp0 e0 tp1 tp e:
      (tp, e) ∈ prefixes_from (tp0 ++ [e0]) tp1 -> locale_of tp0 e0 ≠ locale_of tp e;
    (* mixin_config_enabled σ lbl : *)
    (*   (∃ σ', config_step σ lbl σ') ↔ config_enabled lbl σ; *)
  }.
End ectx_language_mixin.

Structure ectxLanguage := EctxLanguage {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;
  locale : Type;
  config_label : Type;

  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : expr → state → expr → state → list expr → Prop;
  config_step : state → config_label → state → Prop;
  locale_of : list expr → expr → locale;
  config_enabled : config_label → state → Prop;

  ectx_language_mixin :
    EctxLanguageMixin of_val to_val empty_ectx comp_ectx fill head_step (* config_step *) locale_of (* config_enabled *)
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Arguments EctxLanguage {_ _ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments of_val {_} _.
Arguments to_val {_} _.
Arguments empty_ectx {_}.
Arguments comp_ectx {_} _ _.
Arguments fill {_} _ _.
Arguments head_step {_} _ _ _ _ _.
Arguments config_step {_} _ _ _.
Arguments locale_of {_} _ _.
Arguments config_enabled {_} _ _.

Notation locales_equiv t0 t0' :=
  (Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0')).

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {Λ : ectxLanguage}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  (* Only project stuff out of the mixin that is not also in language *)
  Lemma val_head_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_empty e : fill empty_ectx e = e.
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
  Proof. apply ectx_language_mixin. Qed.
  Global Instance fill_inj K : Inj (=) (=) (fill K).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_val K e : is_Some (to_val (fill K e)) → is_Some (to_val e).
  Proof. apply ectx_language_mixin. Qed.
  Lemma fill_positive K K' e e' :
    to_val e = None → to_val e' = None →
    fill K e = fill K' e' →
    (∃ K'', K' = comp_ectx K K'') ∨ (∃ K'', K = comp_ectx K' K'').
  Proof. apply ectx_language_mixin. Qed.
  Lemma step_by_val K' K_redex e1' e1_redex σ1 e2 σ2 efs :
      fill K' e1' = fill K_redex e1_redex →
      to_val e1' = None →
      head_step e1_redex σ1 e2 σ2 efs →
      ∃ K'', K_redex = comp_ectx K' K''.
  Proof. apply ectx_language_mixin. Qed.
  Lemma head_ctx_step_val K e σ1 e2 σ2 efs :
    head_step (fill K e) σ1 e2 σ2 efs → is_Some (to_val e) ∨ K = empty_ectx.
  Proof. apply ectx_language_mixin. Qed.

  Definition head_reducible (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, head_step e σ e' σ' efs.
  Definition head_irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ' efs, ¬head_step e σ e' σ' efs.
  Definition head_stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ head_irreducible e σ.

  Lemma locale_fill e K t1: locale_of t1 (fill K e) = locale_of t1 e.
  Proof. apply ectx_language_mixin. Qed.

  (* All non-value redexes are at the root.  In other words, all sub-redexes are
     values. *)
  Definition sub_redexes_are_values (e : expr Λ) :=
    ∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx.

  Inductive prim_step (e1 : expr Λ) (σ1 : state Λ)
      (e2 : expr Λ) (σ2 : state Λ) (efs : list (expr Λ)) : Prop :=
    Ectx_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step e1' σ1 e2' σ2 efs → prim_step e1 σ1 e2 σ2 efs.

  Lemma Ectx_step' K e1 σ1 e2 σ2 efs :
    head_step e1 σ1 e2 σ2 efs → prim_step (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof. econstructor; eauto. Qed.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Definition ectx_lang_mixin :
    LanguageMixin of_val to_val prim_step (* config_step *) locale_of (* config_enabled *) comp_ectx empty_ectx fill.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros ????? [??? -> -> ?%val_head_stuck].
      apply eq_None_not_Some. by intros ?%fill_val%eq_None_not_Some.
    - intros K; split_and!.
      + eauto using fill_not_val.
      + intros ????? [K' e1' e2' Heq1 Heq2 Hstep].
        exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp; done.
      + intros e1 σ1 e2 σ2 efs Hnval [K'' e1'' e2'' Heq1 -> Hstep].
        destruct (step_by_val K K'' e1 e1'' σ1 e2'' σ2 efs) as [K' ->]; eauto.
        rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
        exists (fill K' e2''); rewrite -fill_comp; split; auto.
        econstructor; eauto.
    - apply fill_empty.
    - intros ? ? ?; rewrite fill_comp; done.
    - apply fill_inj.
    - apply fill_positive.
    - intros e1 e2 t1 σ1 σ2 efs Hpstep. inversion Hpstep; simplify_eq.
      do 2 (erewrite mixin_locale_fill; last apply ectx_language_mixin).
      eapply mixin_locale_step; first apply ectx_language_mixin. done.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    (* - apply ectx_language_mixin. *)
  Qed.

  Canonical Structure ectx_lang : language :=
    Language prim_step config_step (config_enabled := config_enabled)
             empty_ectx fill ectx_lang_mixin.

  Definition head_atomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ e' σ' efs,
      head_step e σ e' σ' efs →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Definition head_stutteringatomic (a : atomicity) (e : expr Λ) : Prop :=
    ∀ σ e' σ' efs,
      head_step e σ e' σ' efs →
      (e' = e ∧ σ' = σ ∧ efs = [])
      ∨
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Lemma not_head_reducible e σ : ¬head_reducible e σ ↔ head_irreducible e σ.
  Proof. unfold head_reducible, head_irreducible. naive_solver. Qed.

  (** The decomposition into head redex and context is unique.

      In all sensible instances, [comp_ectx K' empty_ectx] will be the same as
      [K'], so the conclusion is [K = K' ∧ e = e'], but we do not require a law
      to actually prove that so we cannot use that fact here. *)
  Lemma head_redex_unique K K' e e' σ :
    fill K e = fill K' e' →
    head_reducible e σ →
    head_reducible e' σ →
    K = comp_ectx K' empty_ectx ∧ e = e'.
  Proof.
    intros Heq (e2 & σ2 & efs & Hred) (e2' & σ2' & efs' & Hred').
    edestruct (step_by_val K' K e' e) as [K'' HK];
      [by eauto using val_head_stuck..|].
    subst K. move: Heq. rewrite -fill_comp. intros <-%(inj (fill _)).
    destruct (head_ctx_step_val _ _ _ _ _ _ Hred') as [[]%not_eq_None_Some|HK''].
    { by eapply val_head_stuck. }
    subst K''. rewrite fill_empty. done.
  Qed.

  Lemma head_prim_step e1 σ1 e2 σ2 efs :
    head_step e1 σ1 e2 σ2 efs → prim_step e1 σ1 e2 σ2 efs.
  Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_step_not_stuck e σ e' σ' efs : head_step e σ e' σ' efs → not_stuck e σ.
  Proof. rewrite /not_stuck /reducible /=. eauto 10 using head_prim_step. Qed.

  Lemma fill_prim_step K e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs → prim_step (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof.
    destruct 1 as [K' e1' e2' -> ->].
    rewrite !fill_comp. by econstructor.
  Qed.
  Lemma fill_reducible K e σ : reducible e σ → reducible (fill K e) σ.
  Proof.
    intros (e'&σ'&efs&?). exists (fill K e'), σ', efs.
    by apply fill_prim_step.
  Qed.
  Lemma head_prim_reducible e σ : head_reducible e σ → reducible e σ.
  Proof. intros (e'&σ'&efs&?). eexists e', σ', efs. by apply head_prim_step. Qed.
  Lemma head_prim_fill_reducible e K σ :
    head_reducible e σ → reducible (fill K e) σ.
  Proof. intro. by apply fill_reducible, head_prim_reducible. Qed.
  Lemma head_prim_irreducible e σ : irreducible e σ → head_irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using head_prim_reducible.
  Qed.

  Lemma prim_head_reducible e σ :
    reducible e σ → sub_redexes_are_values e → head_reducible e σ.
  Proof.
    intros (e'&σ'&efs&[K e1' e2' -> -> Hstep]) ?.
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty /head_reducible; eauto.
  Qed.
  Lemma prim_head_irreducible e σ :
    head_irreducible e σ → sub_redexes_are_values e → irreducible e σ.
  Proof.
    rewrite -not_reducible -not_head_reducible. eauto using prim_head_reducible.
  Qed.

  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → stuck e σ.
  Proof.
    intros [] ?. split; first done.
    by apply prim_head_irreducible.
  Qed.

  Lemma ectx_language_atomic a e :
    head_atomic a e → sub_redexes_are_values e → Atomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ e' σ' efs [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    rewrite fill_empty. eapply Hatomic_step. by rewrite fill_empty.
  Qed.

  Lemma ectx_language_stutteringatomic a e :
    head_stutteringatomic a e → sub_redexes_are_values e → StutteringAtomic a e.
  Proof.
    intros Hatomic_step Hatomic_fill σ e' σ' efs [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using val_head_stuck.
    revert Hatomic_step; rewrite !fill_empty; intros Hatomic_step.
    eapply Hatomic_step; done.
  Qed.

  Lemma head_reducible_prim_step_ctx K e1 σ1 e2 σ2 efs :
    head_reducible e1 σ1 →
    prim_step (fill K e1) σ1 e2 σ2 efs →
    ∃ e2', e2 = fill K e2' ∧ head_step e1 σ1 e2' σ2 efs.
  Proof.
    intros (e2''&σ2''&efs''&HhstepK) [K' e1' e2' HKe1 -> Hstep].
    edestruct (step_by_val K) as [K'' ?];
      eauto using val_head_stuck; simplify_eq/=.
    rewrite -fill_comp in HKe1; simplify_eq.
    exists (fill K'' e2'). rewrite fill_comp; split; first done.
    apply head_ctx_step_val in HhstepK as [[v ?]|?]; simplify_eq.
    { apply val_head_stuck in Hstep; simplify_eq. }
    by rewrite !fill_empty.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 e2 σ2 efs :
    head_reducible e1 σ1 →
    prim_step e1 σ1 e2 σ2 efs →
    head_step e1 σ1 e2 σ2 efs.
  Proof.
    intros.
    edestruct (head_reducible_prim_step_ctx empty_ectx) as (?&?&?);
      rewrite ?fill_empty; eauto.
    by simplify_eq; rewrite fill_empty.
  Qed.

  Record pure_head_step (e1 e2 : expr Λ) := {
    pure_head_step_safe σ1 : head_reducible e1 σ1;
    pure_head_step_det σ1 e2' σ2 efs :
      head_step e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []
  }.

  Lemma pure_head_step_pure_step e1 e2 : pure_head_step e1 e2 → pure_step e1 e2.
  Proof.
    intros [Hp1 Hp2]. split.
    - intros σ. destruct (Hp1 σ) as (e2' & σ2 & efs & ?).
      eexists e2', σ2, efs. by apply head_prim_step.
    - intros σ1 e2' σ2 efs ?%head_reducible_prim_step; eauto.
  Qed.

  (** This is not an instance because HeapLang's [wp_pure] tactic already takes
      care of handling the evaluation context.  So the instance is redundant.
      If you are defining your own language and your [wp_pure] works
      differently, you might want to specialize this lemma to your language and
      register that as an instance. *)
  Lemma pure_exec_fill K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (fill K e1) (fill K e2).
  Proof. apply: pure_exec_ctx. Qed.

  Lemma head_locale_step K e1 e2 tp1 tp2 efs σ1 σ2 :
    head_step e1 σ1 e2 σ2 efs →
    locale_step
      (tp1 ++ fill K e1 :: tp2, σ1)
      (inl (locale_of tp1 e1))
      (tp1 ++ fill K e2 :: tp2 ++ efs, σ2).
  Proof.
    intros Hstep. rewrite -(locale_fill _ K). econstructor =>//.
    by apply fill_step, head_prim_step.
  Qed.

End ectx_language.

Arguments ectx_lang : clear implicits.
Coercion ectx_lang : ectxLanguage >-> language.

(* This definition makes sure that the fields of the [language] record do not
refer to the projections of the [ectxLanguage] record but to the actual fields
of the [ectxLanguage] record. This is crucial for canonical structure search to
work.

Note that this trick no longer works when we switch to canonical projections
because then the pattern match [let '...] will be desugared into projections. *)
Definition LanguageOfEctx (Λ : ectxLanguage) : language :=
  let '@EctxLanguage E V C St Loc _ of_val to_val empty comp fill head config loc_of config_enabled mix := Λ in
  @Language E V C St Loc _ of_val to_val _ config loc_of config_enabled comp empty fill
    (@ectx_lang_mixin
       (@EctxLanguage E V C St Loc _ of_val to_val empty comp fill head config loc_of config_enabled mix)).
