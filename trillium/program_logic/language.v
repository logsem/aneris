From iris.algebra Require Export ofe.

Section prefixes.
  Context {A : Type}.

  Fixpoint prefixes_from pref l : list (list A * A) :=
    match l with
    | [] => []
    | x::xs => (pref, x) :: prefixes_from (pref ++ [x]) xs
    end.

  Notation prefixes l := (prefixes_from [] l).

  Lemma prefixes_from_app l0 l1 l2:
    prefixes_from l0 (l1 ++ l2) = prefixes_from l0 l1 ++ prefixes_from (l0++l1) l2.
  Proof.
    revert l0 l2. induction l1 ; intros l0 l2; first by list_simplifier.
    list_simplifier.
    replace (a :: l1 ++ l2) with (a :: (l1 ++ l2)); last by list_simplifier.
    rewrite IHl1. by list_simplifier.
  Qed.

  Lemma prefixes_from_spec `{EqDecision A} tp0 tp1 e tp:
    (tp, e) ∈ prefixes_from tp0 tp1 <->
      (∃ t t', tp = tp0 ++ t ∧ tp1 = t ++ e :: t').
  Proof.
    revert tp e tp0. induction tp1 as [|e' t' IH]; intros tp e0 tp'.
    { list_simplifier. split; first set_solver. intros (?&?&?&Hf).
      by apply app_cons_not_nil in Hf. }
    split.
    - simpl. intros [Hin|Hin]%elem_of_cons.
      + simplify_eq. eexists [], t'. by list_simplifier.
      + destruct (iffLR (IH _ _ _) Hin) as (?&?&?&?). list_simplifier. eauto.
    - intros (t1&t2&Heq1&Heq2). simpl. apply elem_of_cons.
      destruct (decide (tp = tp' ∧ e0 = e')) as [[??]|Hneq].
      + simplify_eq. left; congruence.
      + right. apply IH. simplify_eq.
        assert (∃ t1', t1 = e' :: t1') as [t1' ->].
        { assert ((t1 ++ e0 :: t2) !! 0 = Some e') as H; first by rewrite -Heq2; set_solver.
          destruct t1 as [| e1 t1]; first by apply not_and_l in Hneq as [Hneq|Hneq]; list_simplifier.
          exists t1. f_equal. simpl in H. congruence. }
        list_simplifier. eexists _, _. by list_simplifier.
  Qed.

  Lemma prefixes_from_lookup tp0 tp1 n e :
    tp1 !! n = Some e ->
    prefixes_from tp0 tp1 !! n = Some (tp0 ++ take n tp1, e).
  Proof.
    revert tp0 n; induction tp1 as [| e1 tp1 IH]; intros tp0 n Hlk; first done.
    destruct n as [|n]; simpl in *; first by list_simplifier.
    replace (tp0 ++ e1 :: take n tp1) with ((tp0 ++ [e1]) ++ take n tp1); last by list_simplifier.
    by apply IH.
  Qed.
End prefixes.
Notation prefixes l := (prefixes_from [] l).

Section language_mixin.
  Context {expr val ectx state : Type}.
  Context {locale : Type}.
  Context {config_label : Type}.

  Context (of_val : val → expr).
  Context (to_val : expr → option val).

  Context (prim_step : expr → state → expr → state → list expr → Prop).
  Context (config_step : state → config_label → state → Prop).

  Context (locale_of : list expr -> expr -> locale).
  Context (config_enabled : config_label → state → Prop).

  (** Evaluation contexts: we need to include them in the definition of the
      language because they are used in the program logic for forming
      program traces. *)
  Context (ectx_comp : ectx → ectx → ectx).
  Context (ectx_emp : ectx).
  Context (ectx_fill : ectx → expr → expr).

  Notation locales_equiv t0 t0' :=
    (Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0')).

  Record LanguageMixin := {
    mixin_to_of_val v : to_val (of_val v) = Some v;
    mixin_of_to_val e v : to_val e = Some v → of_val v = e;
    mixin_val_stuck e σ e' σ' efs : prim_step e σ e' σ' efs → to_val e = None;
    mixin_is_eval_ctx K :
      (∀ e, to_val e = None → to_val (ectx_fill K e) = None) ∧
      (∀ e1 σ1 e2 σ2 efs,
        prim_step e1 σ1 e2 σ2 efs →
        prim_step (ectx_fill K e1) σ1 (ectx_fill K e2) σ2 efs) ∧
      (∀ e1' σ1 e2 σ2 efs,
        to_val e1' = None → prim_step (ectx_fill K e1') σ1 e2 σ2 efs →
        ∃ e2', e2 = ectx_fill K e2' ∧ prim_step e1' σ1 e2' σ2 efs);
    mixin_ectx_fill_emp e : ectx_fill ectx_emp e = e;
    mixin_ectx_comp_comp K K' e :
      ectx_fill (ectx_comp K K') e = ectx_fill K (ectx_fill K' e);
    mixin_ectx_fill_inj K e e' : ectx_fill K e = ectx_fill K e' → e = e';
    mixin_ectx_fill_positive K K' e e' :
      to_val e = None → to_val e' = None →
      ectx_fill K e = ectx_fill K' e' →
      (∃ K'', K' = ectx_comp K K'') ∨ (∃ K'', K = ectx_comp K' K'');
    mixin_locale_step e1 e2 t1 σ1 σ2 efs: prim_step e1 σ1 e2 σ2 efs ->
                                          locale_of t1 e1 = locale_of t1 e2;
    mixin_locale_fill e K t1: locale_of t1 (ectx_fill K e) = locale_of t1 e;
    mixin_locale_equiv t t' e: locales_equiv t t' -> locale_of t e = locale_of t' e;
    mixin_locale_injective tp0 e0 tp1 tp e:
      (tp, e) ∈ prefixes_from (tp0 ++ [e0]) tp1 -> locale_of tp0 e0 ≠ locale_of tp e;    
  (* Might need something like this to prove fair derivation for generic
     programs and models *)
  (*   mixin_config_enabled σ lbl : *)
  (*     (∃ σ', config_step σ lbl σ') ↔ config_enabled lbl σ; *)
  }.
End language_mixin.

Structure language := Language {
  expr : Type;
  val : Type;
  ectx : Type;
  state : Type;
  locale : Type;
  config_label : Type;
  of_val : val → expr;
  to_val : expr → option val;
  prim_step : expr → state → expr → state → list expr → Prop;
  config_step : state → config_label → state → Prop;
  locale_of : list expr → expr → locale;
  config_enabled : config_label → state → Prop;
  ectx_comp : ectx → ectx → ectx;
  ectx_emp : ectx;
  ectx_fill : ectx → expr → expr;
  language_mixin :
    LanguageMixin of_val to_val prim_step (* config_step*) locale_of (* config_enabled *) ectx_comp ectx_emp ectx_fill
}.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

Arguments Language {_ _ _ _ _ _ _ _} prim_step config_step {_ _ _} _ _ _.
Arguments of_val {_} _.
Arguments to_val {_} _.
Arguments prim_step {_} _ _ _ _ _.
Arguments config_step {_} _ _ _.
Arguments ectx_comp {_} _ _.
Arguments ectx_emp {_}.
Arguments ectx_fill {_} _ _.
Arguments locale_of {_} _ _.
Arguments config_enabled {_} _ _.

Notation locales_equiv t0 t0' :=
  (Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0')).

Canonical Structure stateO Λ := leibnizO (state Λ).
Canonical Structure valO Λ := leibnizO (val Λ).
Canonical Structure exprO Λ := leibnizO (expr Λ).

Definition cfg (Λ : language) := (list (expr Λ) * state Λ)%type.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Record is_an_eval_ctx {Λ : language} (K : expr Λ → expr Λ) := {
  is_an_eval_ctx_fill_not_val e :
    to_val e = None → to_val (K e) = None;
  is_an_eval_ctx_fill_step e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs →
    prim_step (K e1) σ1 (K e2) σ2 efs;
  is_an_eval_ctx_fill_step_inv e1' σ1 e2 σ2 efs :
    to_val e1' = None → prim_step (K e1') σ1 e2 σ2 efs →
    ∃ e2', e2 = K e2' ∧ prim_step e1' σ1 e2' σ2 efs
}.

Global Arguments is_an_eval_ctx_fill_not_val {_ _} _.
Global Arguments is_an_eval_ctx_fill_step {_ _} _.
Global Arguments is_an_eval_ctx_fill_step_inv {_ _} _.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types K : ectx Λ.

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. apply language_mixin. Qed.
  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof. apply language_mixin. Qed.
  Lemma val_stuck e σ e' σ' efs : prim_step e σ e' σ' efs → to_val e = None.
  Proof. apply language_mixin. Qed.
  Lemma is_eval_ctx K : is_an_eval_ctx (ectx_fill K).
  Proof. split; apply language_mixin. Qed.
  Lemma ectx_fill_emp e : ectx_fill ectx_emp e = e.
  Proof. apply language_mixin. Qed.
  Lemma ectx_comp_comp K K' e :
    ectx_fill (ectx_comp K K') e = ectx_fill K (ectx_fill K' e).
  Proof. apply language_mixin. Qed.
  Lemma ectx_fill_inj K e e' : ectx_fill K e = ectx_fill K e' → e = e'.
  Proof. apply language_mixin. Qed.
  Lemma ectx_fill_positive K K' e e' :
    to_val e = None → to_val e' = None →
    ectx_fill K e = ectx_fill K' e' →
    (∃ K'', K' = ectx_comp K K'') ∨ (∃ K'', K = ectx_comp K' K'').
  Proof. apply language_mixin. Qed.

  Lemma fill_not_val K e :
    to_val e = None → to_val (ectx_fill K e) = None.
  Proof. apply is_an_eval_ctx_fill_not_val, is_eval_ctx. Qed.
  Lemma fill_step K e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs →
    prim_step (ectx_fill K e1) σ1 (ectx_fill K e2) σ2 efs.
  Proof. apply is_an_eval_ctx_fill_step, is_eval_ctx. Qed.
  Lemma fill_step_inv K e1' σ1 e2 σ2 efs :
    to_val e1' = None → prim_step (ectx_fill K e1') σ1 e2 σ2 efs →
    ∃ e2', e2 = ectx_fill K e2' ∧ prim_step e1' σ1 e2' σ2 efs.
  Proof. apply is_an_eval_ctx_fill_step_inv, is_eval_ctx. Qed.


  Lemma locale_fill e t1 K:
    locale_of t1 (ectx_fill K e) = locale_of t1 (e).
  Proof.
    erewrite !mixin_locale_fill; [done | apply language_mixin].
  Qed.
  Lemma locale_step_preserve e1 e2 σ1 σ2 t1 efs:
    prim_step e1 σ1 e2 σ2 efs ->
    locale_of t1 e1 = locale_of t1 e2.
  Proof.
    intros ?. eapply mixin_locale_step; [apply language_mixin|done].
  Qed.
  Lemma locale_fill_step e1 e2 σ1 σ2 t1 efs K:
    prim_step e1 σ1 e2 σ2 efs ->
    locale_of t1 (ectx_fill K e1) = locale_of t1 (ectx_fill K e2).
  Proof.
    erewrite !locale_fill. intros ?. by eapply locale_step_preserve.
  Qed.
  Lemma locale_equiv t t' e: locales_equiv t t' -> locale_of t e = locale_of t' e.
  Proof. apply language_mixin. Qed.
  Lemma locale_injective  tp0 e0 tp1 tp e :
      (tp, e) ∈ prefixes_from (tp0 ++ [e0]) tp1 -> locale_of tp0 e0 ≠ locale_of tp e.
  Proof. eapply language_mixin. Qed.  

  Definition reducible (e : expr Λ) (σ : state Λ) :=
    ∃ e' σ' efs, prim_step e σ e' σ' efs.
  Definition irreducible (e : expr Λ) (σ : state Λ) :=
    ∀ e' σ' efs, ¬prim_step e σ e' σ' efs.
  Definition stuck (e : expr Λ) (σ : state Λ) :=
    to_val e = None ∧ irreducible e σ.
  Definition not_stuck (e : expr Λ) (σ : state Λ) :=
    is_Some (to_val e) ∨ reducible e σ.

  (* [Atomic WeaklyAtomic]: This (weak) form of atomicity is enough to open
     invariants when WP ensures safety, i.e., programs never can get stuck.  We
     have an example in lambdaRust of an expression that is atomic in this
     sense, but not in the stronger sense defined below, and we have to be able
     to open invariants around that expression.  See `CasStuckS` in
     [lambdaRust](https://gitlab.mpi-sws.org/FP/LambdaRust-coq/blob/master/theories/lang/lang.v).

     [Atomic StronglyAtomic]: To open invariants with a WP that does not ensure
     safety, we need a stronger form of atomicity.  With the above definition,
     in case `e` reduces to a stuck non-value, there is no proof that the
     invariants have been established again. *)
  Class Atomic (a : atomicity) (e : expr Λ) : Prop :=
    atomic σ e' σ' efs :
      prim_step e σ e' σ' efs →
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Class StutteringAtomic (a : atomicity) (e : expr Λ) : Prop :=
    stutteringatomic σ e' σ' efs :
      prim_step e σ e' σ' efs →
      (e' = e ∧ σ' = σ ∧ efs = [])
      ∨
      if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

  Global Instance atomic_stutteringatomic a e :
    Atomic a e → StutteringAtomic a e.
  Proof.
    rewrite /Atomic /StutteringAtomic.
    intros Hat ?????; right; eapply Hat; eauto.
  Qed.

  Inductive step (ρ1 : cfg Λ) (ρ2 : cfg Λ) : Prop :=
    | step_atomic e1 σ1 e2 σ2 efs t1 t2 :
       ρ1 = (t1 ++ e1 :: t2, σ1) →
       ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
       prim_step e1 σ1 e2 σ2 efs →
       step ρ1 ρ2
    | step_state σ1 lbl σ2 t :
       ρ1 = (t, σ1) →
       ρ2 = (t, σ2) →
       config_step σ1 lbl σ2 →
       step ρ1 ρ2.
  Hint Constructors step : core.

  Inductive locale_step: cfg Λ -> (locale Λ + config_label Λ) -> cfg Λ -> Prop :=
  | locale_step_atomic ρ1 ρ2 e1 σ1 e2 σ2 efs t1 t2 :
      ρ1 = (t1 ++ e1 :: t2, σ1) →
      ρ2 = (t1 ++ e2 :: t2 ++ efs, σ2) →
      prim_step e1 σ1 e2 σ2 efs →
      locale_step ρ1 (inl $ locale_of t1 e1) ρ2
  | locale_step_state ρ1 ρ2 σ1 lbl σ2 t :
      ρ1 = (t, σ1) →
      ρ2 = (t, σ2) →
      config_step σ1 lbl σ2 →
      locale_step ρ1 (inr $ lbl) ρ2.
  Hint Constructors locale_step : core.

  Inductive nsteps : nat → cfg Λ → cfg Λ → Prop :=
    | nsteps_refl ρ : nsteps 0 ρ ρ
    | nsteps_l n ρ1 ρ2 ρ3 : step ρ1 ρ2 → nsteps n ρ2 ρ3 → nsteps (S n) ρ1 ρ3.
  Hint Constructors nsteps : core.

  (** [rtc step] and [nsteps] encode the same thing, just packaged
      in a different way. *)
  Lemma steps_nsteps ρ1 ρ2 :
    rtc step ρ1 ρ2 ↔ ∃ n, nsteps n ρ1 ρ2.
  Proof.
    split.
    - induction 1; firstorder eauto. (* FIXME: [naive_solver eauto] should be able to handle this *)
    - intros (n & Hsteps).
      induction Hsteps; eauto using rtc_refl, rtc_l.
  Qed.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.

  Lemma not_reducible e σ : ¬reducible e σ ↔ irreducible e σ.
  Proof. unfold reducible, irreducible. naive_solver. Qed.
  Lemma reducible_not_val e σ : reducible e σ → to_val e = None.
  Proof. intros (?&?&?&?); eauto using val_stuck. Qed.
  Lemma val_irreducible e σ : is_Some (to_val e) → irreducible e σ.
  Proof. intros [??] ??? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
  Lemma not_not_stuck e σ : ¬not_stuck e σ ↔ stuck e σ.
  Proof.
    rewrite /stuck /not_stuck -not_eq_None_Some -not_reducible.
    destruct (decide (to_val e = None)); naive_solver.
  Qed.

  Lemma strongly_atomic_atomic e a :
    Atomic StronglyAtomic e → Atomic a e.
  Proof. unfold Atomic. destruct a; eauto using val_irreducible. Qed.

  Lemma strongly_stutteringatomic_stutteringatomic e a :
    StutteringAtomic StronglyAtomic e → StutteringAtomic a e.
  Proof.
    unfold StutteringAtomic.
    destruct a; intros Hat; first tauto.
    intros ? ? ? ? [|]%Hat; auto using val_irreducible.
  Qed.
  Lemma reducible_fill K e σ :
    reducible e σ → reducible (ectx_fill K e) σ.
  Proof.
    unfold reducible in *.
    naive_solver eauto using fill_step.
  Qed.
  Lemma reducible_fill_inv K e σ :
    to_val e = None → reducible (ectx_fill K e) σ → reducible e σ.
  Proof.
    intros ? (e'&σ'&efs&Hstep); unfold reducible.
    apply fill_step_inv in Hstep as (e2' & _ & Hstep); eauto.
  Qed.
  Lemma irreducible_fill K e σ :
    to_val e = None → irreducible e σ → irreducible (ectx_fill K e) σ.
  Proof.
    rewrite -!not_reducible. naive_solver eauto using reducible_fill_inv.
  Qed.
  Lemma irreducible_fill_inv K e σ :
    irreducible (ectx_fill K e) σ → irreducible e σ.
  Proof. rewrite -!not_reducible. naive_solver eauto using reducible_fill. Qed.

  Lemma not_stuck_fill_inv K e σ :
    not_stuck (ectx_fill K e) σ → not_stuck e σ.
  Proof.
    rewrite /not_stuck -!not_eq_None_Some. intros [?|?].
    - auto using fill_not_val.
    - destruct (decide (to_val e = None)); eauto using reducible_fill_inv.
  Qed.

  Lemma stuck_fill K e σ :
    stuck e σ → stuck (ectx_fill K e) σ.
  Proof. rewrite -!not_not_stuck. eauto using not_stuck_fill_inv. Qed.

  Lemma step_Permutation (t1 t1' t2 : list (expr Λ)) σ1 σ2 :
    t1 ≡ₚ t1' → step (t1,σ1) (t2,σ2) → ∃ t2', t2 ≡ₚ t2' ∧ step (t1',σ1) (t2',σ2).
  Proof.
    intros Ht Hs.
    inversion Hs as [e1 σ1' e2 σ2' efs tl tr ?? Hstep|]; simplify_eq /=.
    - move: Ht. rewrite -Permutation_middle (symmetry_iff (≡ₚ)).
      intros (tl'&tr'&->&Ht)%Permutation_cons_inv_r.
      exists (tl' ++ e2 :: tr' ++ efs); split; [|by econstructor].
        by rewrite -!Permutation_middle !assoc_L Ht.
    - exists t1'; split; first done.
      econstructor 2; eauto.
  Qed.

  Lemma step_insert i t2 σ2 e e' σ3 efs :
    t2 !! i = Some e →
    prim_step e σ2 e' σ3 efs →
    step (t2, σ2) (<[i:=e']>t2 ++ efs, σ3).
  Proof.
    intros.
    edestruct (elem_of_list_split_length t2) as (t21&t22&?&?);
      first (by eauto using elem_of_list_lookup_2); simplify_eq.
    econstructor; eauto.
    by rewrite insert_app_r_alt // Nat.sub_diag /= -assoc_L.
  Qed.

  Record pure_step (e1 e2 : expr Λ) := {
    pure_step_safe σ1 : reducible e1 σ1;
    pure_step_det σ1 e2' σ2 efs :
      prim_step e1 σ1 e2' σ2 efs → σ2 = σ1 ∧ e2' = e2 ∧ efs = []
  }.

  Notation pure_steps_tp := (Forall2 (rtc pure_step)).

  (* TODO: Exclude the case of [n=0], either here, or in [wp_pure] to avoid it
  succeeding when it did not actually do anything. *)
  Class PureExec (φ : Prop) (n : nat) (e1 e2 : expr Λ) :=
    pure_exec : φ → relations.nsteps pure_step n e1 e2.

  Lemma pure_step_ctx K e1 e2 :
    pure_step e1 e2 →
    pure_step (ectx_fill K e1) (ectx_fill K e2).
  Proof.
    intros [Hred Hstep]. split.
    - unfold reducible in *.
      naive_solver eauto using fill_step.
    - intros σ1 e2' σ2 efs Hpstep.
      destruct (fill_step_inv K e1 σ1 e2' σ2 efs)
        as (e2'' & -> & ?); [|exact Hpstep|].
      + destruct (Hred σ1) as (? & ? & ? & ?); eauto using val_stuck.
      + edestruct (Hstep σ1 e2'' σ2 efs) as (-> & -> & ->); auto.
  Qed.

  Lemma pure_step_nsteps_ctx K n e1 e2 :
    relations.nsteps pure_step n e1 e2 →
    relations.nsteps pure_step n (ectx_fill K e1) (ectx_fill K e2).
  Proof. eauto using nsteps_congruence, pure_step_ctx. Qed.

  Lemma rtc_pure_step_ctx K e1 e2 :
    rtc pure_step e1 e2 → rtc pure_step (ectx_fill K e1) (ectx_fill K e2).
  Proof. eauto using rtc_congruence, pure_step_ctx. Qed.

  (* We do not make this an instance because it is awfully general. *)
  Lemma pure_exec_ctx K φ n e1 e2 :
    PureExec φ n e1 e2 →
    PureExec φ n (ectx_fill K e1) (ectx_fill K e2).
  Proof. rewrite /PureExec; eauto using pure_step_nsteps_ctx. Qed.

  (* This is a family of frequent assumptions for PureExec *)
  Class IntoVal (e : expr Λ) (v : val Λ) :=
    into_val : of_val v = e.

  Class AsVal (e : expr Λ) := as_val : ∃ v, of_val v = e.
  (* There is no instance [IntoVal → AsVal] as often one can solve [AsVal] more
  efficiently since no witness has to be computed. *)
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /=; eauto.
  Qed.

  Lemma as_val_is_Some e :
    (∃ v, of_val v = e) → is_Some (to_val e).
  Proof. intros [v <-]. rewrite to_of_val. eauto. Qed.

  Lemma prim_step_not_stuck e σ e' σ' efs :
    prim_step e σ e' σ' efs → not_stuck e σ.
  Proof. rewrite /not_stuck /reducible. eauto 10. Qed.

  Lemma rtc_pure_step_val `{!Inhabited (state Λ)} v e :
    rtc pure_step (of_val v) e → to_val e = Some v.
  Proof.
    intros ?; rewrite <- to_of_val.
    f_equal; symmetry; eapply rtc_nf; first done.
    intros [e' [Hstep _]].
    destruct (Hstep inhabitant) as (?&?&?&Hval%val_stuck).
    by rewrite to_of_val in Hval.
  Qed.
  (* FIXME: add a new case *)
  (** Let thread pools [t1] and [t3] be such that each thread in [t1] makes
   (zero or more) pure steps to the corresponding thread in [t3]. Furthermore,
   let [t2] be a thread pool such that [t1] under state [σ1] makes a (single)
   step to thread pool [t2] and state [σ2]. In this situation, either the step
   from [t1] to [t2] corresponds to one of the pure steps between [t1] and [t3],
   or, there is an [i] such that [i]th thread does not participate in the
   pure steps between [t1] and [t3] and [t2] corresponds to taking a step in
   the [i]th thread starting from [t1]. *)
  Lemma step_pure_step_tp t1 σ1 t2 σ2 t3 :
    step (t1, σ1) (t2, σ2) →
    pure_steps_tp t1 t3 →
    (σ1 = σ2 ∧ pure_steps_tp t2 t3) ∨
    (∃ i e efs e',
      t1 !! i = Some e ∧ t3 !! i = Some e ∧
      t2 = <[i:=e']>t1 ++ efs ∧
      prim_step e σ1 e' σ2 efs) ∨ (∃ lbl, config_step σ1 lbl σ2).
  Proof.
    intros Ht Hps.
    inversion Ht as [e σ e' σ' efs t11 t12 ?? Hstep|]; simplify_eq/=.
    -  apply Forall2_app_inv_l in Hps
        as (t31&?&Hpsteps&(e''&t32&Hps&?&->)%Forall2_cons_inv_l&->).
       destruct Hps as [e|e1 e2 e3 [_ Hprs]].
       + right; left.
         exists (length t11), e, efs, e'; split_and!; last done.
         * by rewrite lookup_app_r // Nat.sub_diag.
         * apply Forall2_length in Hpsteps.
             by rewrite lookup_app_r Hpsteps // Nat.sub_diag.
         * by rewrite insert_app_r_alt // Nat.sub_diag /= -assoc_L.
       + edestruct Hprs as (?&?&?); first done; simplify_eq.
         left; split; first done.
         rewrite right_id_L.
         eauto using Forall2_app.
    - right; right; eauto.
  Qed.

End language.

Notation pure_steps_tp := (Forall2 (rtc pure_step)).
