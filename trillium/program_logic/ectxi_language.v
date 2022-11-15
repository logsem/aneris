(** An axiomatization of languages based on evaluation context items, including
    a proof that these are instances of general ectx-based languages. *)
From iris.prelude Require Export prelude.
From trillium.program_logic Require Import language ectx_language.

(** TAKE CARE: When you define an [ectxiLanguage] canonical structure for your
language, you need to also define a corresponding [language] and [ectxLanguage]
canonical structure for canonical structure inference to work properly. You
should use the coercion [EctxLanguageOfEctxi] and [LanguageOfEctx] for that, and
not [ectxi_lang] and [ectxi_lang_ectx], otherwise the canonical projections will
not point to the right terms.

A full concrete example of setting up your language can be found in [heap_lang].
Below you can find the relevant parts:

  Module heap_lang.
    (* Your language definition *)

    Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
    Proof. (* ... *) Qed.
  End heap_lang.

  Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
  Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
  Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.
*)

Section ectxi_language_mixin.
  Context {expr val ectx_item state locale : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (fill_item : ectx_item → expr → expr).
  Context (head_step : expr → state → expr → state → list expr → Prop).
  Context (config_step : state → state → Prop).
  Context (locale_of : list expr -> expr -> locale).

  Notation locales_equiv t0 t0' :=
    (Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0')).

  Record EctxiLanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None;

    mixin_fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e);
    (** [fill_item] is always injective on the expression for a fixed
        context. *)
    mixin_fill_item_inj Ki : Inj (=) (=) (fill_item Ki);
    (** [fill_item] with (potentially different) non-value expressions is
        injective on the context. *)
    mixin_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
      to_val e1 = None → to_val e2 = None →
      fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2;

    (** If [fill_item Ki e] takes a head step, then [e] is a value (unlike for
        [ectx_language], an empty context is impossible here).  In other words,
        if [e] is not a value then wrapping it in a context does not add new
        head redex positions. *)
    mixin_head_ctx_step_val Ki e σ1 e2 σ2 efs :
      head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e);

    mixin_locale_step e1 e2 t1 σ1 σ2 efs: head_step e1 σ1 e2 σ2 efs ->
                                         locale_of t1 e1 = locale_of t1 e2;
    mixin_locale_fill e K t1: locale_of t1 (fill_item K e) = locale_of t1 e;
    mixin_locale_equiv t t' e: locales_equiv t t' -> locale_of t e = locale_of t' e;
    mixin_locale_injective tp0 e0 tp1 tp e:
      (tp, e) ∈ prefixes_from (tp0 ++ [e0]) tp1 -> locale_of tp0 e0 ≠ locale_of tp e;
  }.
End ectxi_language_mixin.

Structure ectxiLanguage := EctxiLanguage {
  expr : Type;
  val : Type;
  ectx_item : Type;
  state : Type;
  locale : Type;
  config_label : Type;

  of_val : val → expr;
  to_val : expr → option val;
  fill_item : ectx_item → expr → expr;
  head_step : expr → state → expr → state → list expr → Prop;
  config_step : state → config_label → state → Prop;
  locale_of : list expr -> expr -> locale;

  ectxi_language_mixin :
    EctxiLanguageMixin of_val to_val fill_item head_step locale_of
}.

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Arguments EctxiLanguage {_ _ _ _ _ _ _ _ _} _ _.
Arguments of_val {_} _.
Arguments to_val {_} _.
Arguments fill_item {_} _ _.
Arguments head_step {_} _ _ _ _ _.
Arguments config_step {_} _ _ _.
Arguments locale_of {_} _ _.

Section ectxi_language.
  Context {Λ : ectxiLanguage}.
  Implicit Types (e : expr Λ) (Ki : ectx_item Λ).
  Notation ectx := (list (ectx_item Λ)).

  (* Only project stuff out of the mixin that is not also in ectxLanguage *)
  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_val Ki e : is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof. apply ectxi_language_mixin. Qed.
  Lemma head_ctx_step_val Ki e σ1 e2 σ2 efs :
    head_step (fill_item Ki e) σ1 e2 σ2 efs → is_Some (to_val e).
  Proof. apply ectxi_language_mixin. Qed.

  Definition fill (K : ectx) (e : expr Λ) : expr Λ := foldl (flip fill_item) e K.

  Lemma fill_app (K1 K2 : ectx) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
  Proof. apply foldl_app. Qed.

  Definition ectxi_lang_ectx_mixin :
    EctxLanguageMixin of_val to_val [] (flip (++)) fill head_step locale_of.
  Proof.
    assert (fill_val : ∀ K e, is_Some (to_val (fill K e)) → is_Some (to_val e)).
    { intros K. induction K as [|Ki K IH]=> e //=. by intros ?%IH%fill_item_val. }
    assert (fill_not_val : ∀ K e, to_val e = None → to_val (fill K e) = None).
    { intros K e. rewrite !eq_None_not_Some. eauto. }
    split.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - done.
    - intros K1 K2 e. by rewrite /fill /= foldl_app.
    - intros K; induction K as [|Ki K IH]; rewrite /Inj; naive_solver.
    - done.
    - intros K; induction K as [|Ki K IHK] using rev_ind; simpl in *;
        first by setoid_rewrite app_nil_r; eauto.
      intros K'.
      destruct K' as [|Ki' K' _] using rev_ind; simpl in *;
        first by setoid_rewrite app_nil_r; eauto.
      intros e e' He He' Hes.
      rewrite !fill_app /= in Hes.
      pose proof Hes as Hes'.
      apply fill_item_no_val_inj in Hes'; [|naive_solver|naive_solver];
        simplify_eq.
      apply IHK in Hes as [[Kx ->]|[Kx ->]]; [| |done|done].
      + left; eexists; rewrite -assoc; done.
      + right; eexists; rewrite -assoc; done.
    - intros K K' e1 e1' σ1 e2 σ2 efs Hfill Hred Hstep; revert K' Hfill.
      induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
      destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
      { rewrite fill_app in Hstep. apply head_ctx_step_val in Hstep.
        apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
      rewrite !fill_app /= in Hfill.
      assert (Ki = Ki') as ->.
      { eapply fill_item_no_val_inj, Hfill; eauto using val_head_stuck.
        apply fill_not_val. revert Hstep. apply ectxi_language_mixin. }
      simplify_eq. destruct (IH K') as [K'' ->]; auto.
      exists K''. by rewrite assoc.
    - intros K e1 σ1 e2 σ2 efs.
      destruct K as [|Ki K _] using rev_ind; simpl; first by auto.
      rewrite fill_app /=.
      intros ?%head_ctx_step_val; eauto using fill_val.
    - apply ectxi_language_mixin.
    - intros e K; revert e. induction K as [|Ki K IH]; first naive_solver.
      intros e t1. rewrite IH. apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
    - apply ectxi_language_mixin.
  Qed.

  Canonical Structure ectxi_lang_ectx := EctxLanguage head_step config_step locale_of ectxi_lang_ectx_mixin.
  Canonical Structure ectxi_lang := LanguageOfEctx ectxi_lang_ectx.

  Lemma fill_not_val K e : to_val e = None → to_val (fill K e) = None.
  Proof. rewrite !eq_None_not_Some. eauto using fill_val. Qed.

  Lemma ectxi_language_sub_redexes_are_values e :
    (∀ Ki e', e = fill_item Ki e' → is_Some (to_val e')) →
    sub_redexes_are_values e.
  Proof.
    intros Hsub K e' ->. destruct K as [|Ki K _] using @rev_ind=> //=.
    intros []%eq_None_not_Some. eapply fill_val, Hsub. by rewrite /= fill_app.
  Qed.

End ectxi_language.

Arguments ectxi_lang_ectx : clear implicits.
Arguments ectxi_lang : clear implicits.
Coercion ectxi_lang_ectx : ectxiLanguage >-> ectxLanguage.
Coercion ectxi_lang : ectxiLanguage >-> language.

Definition EctxLanguageOfEctxi (Λ : ectxiLanguage) : ectxLanguage :=
  let '@EctxiLanguage E V C St L _ of_val to_val fill head config locale_of mix := Λ in
  @EctxLanguage E V (list C) St L _ of_val to_val _ _ _ _ config locale_of
    (@ectxi_lang_ectx_mixin
       (@EctxiLanguage E V C St L _ of_val to_val fill head config locale_of mix)).
