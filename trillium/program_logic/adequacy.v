From stdpp Require Import finite.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.bi.lib Require Import fixpoint.
From iris.base_logic.lib Require Import wsat later_credits.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Import quantifiers iris_extraction finitary classical_instances.
From trillium.program_logic Require Export weakestpre traces.

Set Default Proof Using "Type".
Import uPred.

(* TODO: move *)
Lemma step_tp_length {Λ} c c' oζ:
  locale_step (Λ := Λ) c oζ c' → length c.1 ≤ length c'.1.
Proof.
  inversion 1; simplify_eq; last done.
  rewrite !app_length /= !app_length; lia.
Qed.

Lemma valid_exec_length {Λ} ex (tp1 tp2 : list $ expr Λ) σ1 σ2:
  valid_exec ex ->
  trace_starts_in ex (tp1, σ1) ->
  trace_ends_in ex (tp2, σ2) ->
  length tp1 ≤ length tp2.
Proof.
    revert σ1 σ2 tp1 tp2. induction ex as [| ex IH oζ c']; intros σ1 σ2 tp1 tp2.
    - intros ? -> Heq. inversion Heq; simplify_eq; done.
    - intros Hval Hstarts Hends.
      inversion Hval as [A B|A [tp' σ'] C D E Hstep]. simplify_eq.
      etransitivity; first eapply IH =>//.
      pose proof (step_tp_length _ _ _ Hstep) as Hlen. simpl in *.
      rewrite ->Hends in Hlen. simpl in Hlen. lia.
Qed.

Notation wptp_from t0 s t Φs := ([∗ list] tp1_e;Φ ∈ (prefixes_from t0 t);Φs, WP tp1_e.2 @ s; locale_of tp1_e.1 tp1_e.2; ⊤ {{ Φ }})%I.
Notation wptp s t Φs := (wptp_from [] s t Φs).

Notation posts_of t Φs :=
  ([∗ list] vΦ ∈
    (omap (λ x, (λ v, (v, x.2)) <$> to_val x.1)
          (zip_with (λ x y, (x, y)) t Φs)), vΦ.2 vΦ.1)%I.

Definition config_wp `{!irisG Λ M Σ} : iProp Σ :=
  □ ∀ ex atr c1 lbl σ2 ,
      ⌜valid_exec ex⌝ →
      ⌜trace_ends_in ex c1⌝ →
      ⌜config_step c1.2 lbl σ2⌝ →
      state_interp ex atr ={⊤,∅}=∗ |={∅}▷=>^(S $ trace_length ex) |={∅,⊤}=>
         ∃ δ2 ℓ, state_interp (trace_extend ex (inr lbl) (c1.1, σ2))
                              (trace_extend atr ℓ δ2).

#[global] Instance config_wp_persistent `{!irisG Λ M Σ} : Persistent config_wp.
Proof. apply _. Qed.

#[global] Typeclasses Opaque config_wp.

(* the guarded definition of simulation. *)
Definition Gsim_pre Σ {Λ} (M : Model) (s : stuckness)
           (ξ : execution_trace Λ → auxiliary_trace M → Prop)
           (gsim : execution_trace Λ -d> auxiliary_trace M -d> iPropO Σ) :
  execution_trace Λ -d> auxiliary_trace M -d> iPropO Σ :=
  (λ ex atr,
   ▷ (⌜ξ ex atr⌝ ∧
      ∀ c oζ c',
        ⌜trace_ends_in ex c⌝ →
        ⌜locale_step c oζ c'⌝ →
        ▷ ▷^(S $ trace_length ex) (∃ δ' ℓ, gsim (trace_extend ex oζ c') (trace_extend atr ℓ δ'))))%I.

#[local] Instance Gsim_pre_contractive Σ M Λ s ξ :
  Contractive (@Gsim_pre Σ M Λ s ξ).
Proof.
  rewrite /Gsim_pre=> n wp wp' HGsm ex sm.
  repeat (f_contractive || f_equiv); repeat (apply dist_S; try apply HGsm).
Qed.

Definition Gsim Σ {Λ} (M : Model) (s : stuckness)
           (ξ : execution_trace Λ → auxiliary_trace M → Prop) :
  execution_trace Λ → auxiliary_trace M → iProp Σ :=
  fixpoint (Gsim_pre Σ M s ξ).

#[global] Instance is_except_0_wptp {Σ} Λ M s ξ ex sm:
  IsExcept0 (@Gsim Σ Λ M s ξ ex sm).
Proof.
  rewrite /IsExcept0; iIntros "H".
  rewrite /Gsim (fixpoint_unfold (Gsim_pre _ _ _ _) _ _).
  iMod "H".
  iApply "H"; done.
Qed.

#[global] Instance Gsim_plain Σ M {Λ} s ξ ex sm : Plain (@Gsim Σ M Λ s ξ ex sm).
Proof.
  rewrite /Plain.
  iIntros "H".
  iLöb as "IH" forall (ex sm).
  rewrite /Gsim (fixpoint_unfold (Gsim_pre _ _ _ _) _ _).
  rewrite {3 5}/Gsim_pre.
  iApply later_plainly_1; iNext.
  iDestruct "H" as "(#H1 & H)".
  iSplit; first (iClear "IH H"; iModIntro; done).
  iIntros (c ? ? ? ?).
  iDestruct ("H" with "[] []") as "H"; [done|done|].
  do 2 (iApply later_plainly_1; iNext).
  iApply laterN_plainly.
  iModIntro.
  iDestruct "H" as (δ' ℓ) "H".
  iExists _, _. iApply "IH"; done.
Qed.

Notation locales_equiv_from t0 t0' t1 t1' :=
  (Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e')
           (prefixes_from t0 t1) (prefixes_from t0' t1')).

Section locales_helpers.
  Context {Λ: language}.

  Lemma locales_equiv_from_app (t0 t0' t1 t1' t2 t2': list (expr Λ)):
    locales_equiv_from t0 t0' t1 t1' ->
    locales_equiv_from (t0 ++ t1) (t0' ++ t1') t2 t2' ->
    locales_equiv_from t0 t0' (t1 ++ t2) (t1' ++ t2').
  Proof.
    revert t0 t0' t1 t2 t2'. induction t1' ; intros t0 t0' t1 t2 t2' Hequiv1 Hequiv2.
    - destruct t1; last by apply Forall2_cons_nil_inv in Hequiv1. simpl.
      clear Hequiv1. revert t0 t0' t2 Hequiv2; induction t2'; intros t0 t0' t2 Hequiv2.
      + destruct t2; last by apply Forall2_cons_nil_inv in Hequiv2. constructor.
      + destruct t2; first by inversion Hequiv2.
        rewrite !(right_id_L [] (++)) // in Hequiv2.
    - destruct t1; first by inversion Hequiv1.
      replace ((e :: t1) ++ t2) with (e :: (t1 ++ t2)); last by list_simplifier.
      replace ((a :: t1') ++ t2') with (a :: (t1' ++ t2')); last by list_simplifier.
      simpl. constructor.
      + inversion Hequiv1 =>//.
      + apply IHt1'.
        * inversion Hequiv1 =>//.
        * by list_simplifier.
  Qed.

  Lemma prefixes_from_length {A} (t0 t1: list A):
    length (prefixes_from t0 t1) = length t1.
  Proof. revert t0; induction t1; intros ?; [done|]; rewrite /= IHt1 //. Qed.

  Lemma locales_equiv_from_impl (t0 t0' t1 t1' t2 t2': list (expr Λ)):
    length t2 = length t2' ->
    locales_equiv_from t0 t0' (t1 ++ t2) (t1' ++ t2') ->
    locales_equiv_from (t0 ++ t1) (t0' ++ t1') t2 t2'.
  Proof.
    revert t0 t0' t1 t1' t2. induction t2'; intros t0 t0' t1 t1' t2 Hlen Hequiv.
    - destruct t2 ; simpl in *; done.
    - destruct t2; first done.
      revert e a t0 t0' t1 t2' t2 IHt2' Hlen Hequiv. induction t1'; intros x y t0 t0' t1 t2' t2 IHt2' Hlen Hequiv.
      + destruct t1; first by simpl; constructor; list_simplifier.
        apply Forall2_length in Hequiv. rewrite !prefixes_from_length app_length /= in Hequiv.
        simpl in Hlen. lia.
      + destruct t1.
        { apply Forall2_length in Hequiv. rewrite !prefixes_from_length !app_length /= in Hequiv.
          simpl in Hlen. lia. }
        assert (H: locales_equiv_from (t0 ++ e :: t1) (t0' ++ a :: t1')
                    (x :: t2) (y :: t2')).
        { replace (t0 ++ e :: t1) with ((t0 ++ [e]) ++ t1); last by list_simplifier.
          replace (t0' ++ a :: t1') with ((t0' ++ [a]) ++ t1'); last by list_simplifier.
          apply IHt1' =>//.
          by list_simplifier. }
        simpl; constructor; [inversion H =>// |].
        apply IHt2'; first by simpl in Hlen; lia. done.
  Qed.

  Lemma locales_from_equiv_refl (t0 t0' t: list (expr Λ)):
    locales_equiv t0 t0' ->
    locales_equiv_from t0 t0' t t.
  Proof.
    revert t0 t0'; induction t; intros t0 t0' H; simpl; constructor =>//.
    { apply locale_equiv =>//. }
    apply IHt. apply locales_equiv_from_app =>//. simpl.
    constructor; [ by apply locale_equiv | done].
  Qed.

  Lemma locales_equiv_refl (t: list (expr Λ)):
    locales_equiv t t.
  Proof. apply locales_from_equiv_refl. constructor. Qed.

  Lemma locales_equiv_snoc t0 t0' (e e' : expr Λ) t1 t1':
    locales_equiv t0 t0' ->
    locales_equiv_from t0 t0' t1 t1' ->
    locale_of (t0 ++ t1) e = locale_of (t0' ++ t1') e' ->
    locales_equiv_from t0 t0' (t1 ++ [e]) (t1' ++ [e']).
  Proof.
    intros ???.
    apply locales_equiv_from_app =>//.
    simpl. by constructor.
  Qed.

  Lemma locales_equiv_snoc_same t0 (e e' : expr Λ) t1:
    locale_of (t0 ++ t1) e = locale_of (t0 ++ t1) e' ->
    locales_equiv_from t0 t0 (t1 ++ [e]) (t1 ++ [e']).
  Proof.
    intros ?. apply locales_equiv_snoc =>//; apply locales_from_equiv_refl; apply locales_equiv_refl.
  Qed.

  Lemma locales_equiv_from_middle t0 (e e' : expr Λ) t1 t2:
    locale_of (t0 ++ t1) e = locale_of (t0 ++ t1) e' ->
    locales_equiv_from t0 t0 (t1 ++ e :: t2) (t1 ++ e' :: t2).
  Proof.
    intros ?.
    apply locales_equiv_from_app.
    - apply locales_from_equiv_refl. apply locales_equiv_refl.
    - simpl. constructor; first done.
      apply locales_equiv_from_impl =>//=.
      constructor =>//. apply locales_from_equiv_refl.
      apply locales_equiv_snoc_same. by list_simplifier.
  Qed.

  Lemma locales_equiv_middle (e e' : expr Λ) t1 t2:
    locale_of t1 e = locale_of t1 e' ->
    locales_equiv (t1 ++ e :: t2) (t1 ++ e' :: t2).
  Proof.
    intros ?. apply locales_equiv_from_middle.
    by list_simplifier.
  Qed.

  Lemma locale_step_equiv (c c' : cfg Λ) oζ:
    locale_step c oζ c' ->
    locales_equiv c.1 (take (length c.1) c'.1).
  Proof.
    intros H. inversion H as [? ? e1 ? e2 ? efs t1 t2|]; simplify_eq; simpl.
    - replace (t1 ++ e2 :: t2 ++ efs) with ((t1 ++ e2 :: t2) ++ efs); last by list_simplifier.
      replace (length (t1 ++ e1 :: t2)) with (length (t1 ++ e2 :: t2)); last first.
      { rewrite !app_length //=. }
      rewrite take_app. apply locales_equiv_middle.
      eapply locale_step_preserve =>//.
    - rewrite take_ge =>//. apply locales_equiv_refl.
  Qed.

  Lemma locale_equiv_from_take (t0 t0' t1 t1' : list $ expr Λ) n:
    locales_equiv_from t0 t0' t1 t1' ->
    locales_equiv_from t0 t0' (take n t1) (take n t1').
  Proof.
    revert t0 t0' t1 t1'. induction n as [|n IHn]; intros t0 t0' t1 t1' Hequiv; first constructor.
    destruct t1 as [|e1 t1]; destruct t1' as [|e1' t1']; try by inversion Hequiv.
    simpl. constructor; first by inversion Hequiv.
    apply IHn. by inversion Hequiv.
  Qed.

  Lemma locale_equiv_take (t1 t2 : list $ expr Λ) n:
    locales_equiv t1 t2 ->
    locales_equiv (take n t1) (take n t2).
  Proof. apply locale_equiv_from_take. Qed.

  Lemma locale_equiv_from_transitive (s1 s2 s3 t1 t2 t3 : list $ expr Λ):
    locales_equiv s1 s2 ->
    locales_equiv s2 s3 ->
    locales_equiv_from s1 s2 t1 t2 ->
    locales_equiv_from s2 s3 t2 t3 ->
    locales_equiv_from s1 s3 t1 t3.
  Proof.
    revert s1 s2 s3 t1 t2. induction t3 as [|e3 t3] ; intros s1 s2 s3 t1 t2 Hpref1 Hpref2 Hequiv1 Hequiv2;
      destruct t2 as [|e2 t2]; try by inversion Hequiv2; simplify_eq.
    destruct t1 as [|e1 t1]; try by inversion Hequiv1; simplify_eq.
    simpl; constructor; first by etransitivity; [inversion Hequiv1 | inversion Hequiv2].
    eapply (IHt3 _ (s2 ++ [e2]) _ _ t2).
    - inversion Hequiv1; simplify_eq =>//. apply locales_equiv_snoc =>//. constructor.
    - inversion Hequiv2; simplify_eq =>//. apply locales_equiv_snoc =>//. constructor.
    - inversion Hequiv1 =>//.
    - inversion Hequiv2 => //.
  Qed.

  Lemma locale_equiv_transitive (t1 t2 t3 : list $ expr Λ):
    locales_equiv t1 t2 ->
    locales_equiv t2 t3 ->
    locales_equiv t1 t3.
  Proof. apply locale_equiv_from_transitive; constructor. Qed.

  Lemma locale_valid_exec ex (tp1 tp2 : list $ expr Λ) σ1 σ2:
    valid_exec ex ->
    trace_starts_in ex (tp1, σ1) ->
    trace_ends_in ex (tp2, σ2) ->
    locales_equiv tp1 (take (length tp1) tp2).
  Proof.
    revert σ1 σ2 tp1 tp2. induction ex as [| ex IH oζ c']; intros σ1 σ2 tp1 tp2.
    - intros ? -> Heq. inversion Heq; simplify_eq.
      rewrite take_ge //. apply locales_equiv_refl.
    - intros Hval Hstarts Hends.
      inversion Hval as [A B|A [tp' σ'] C D E Hstep]. simplify_eq.
      eapply locale_equiv_transitive.
      eapply IH =>//.
      pose proof (locale_step_equiv _ _ _ Hstep) as Hequiv.
      rewrite /trace_ends_in /trace_last in Hends.
      rewrite Hends in Hequiv.
      apply (locale_equiv_take _ _ (length tp1)) in Hequiv.
      rewrite take_take in Hequiv.
      assert (length tp1 ≤ length tp').
      { eapply (valid_exec_length ex ) =>//. }
      simpl in Hequiv.
      replace (length tp1 `min` length tp') with (length tp1) in Hequiv;
        [done|lia].
  Qed.

End locales_helpers.

Section from_locale.
  Context {Λ: language}.
  Context `{ EqDecision (locale Λ)}.

  Fixpoint from_locale_from tp0 tp ζ :=
    match tp with
    | [] => None
    | e::tp' => if decide (locale_of tp0 e = ζ) then Some e else from_locale_from (tp0 ++ [e]) tp' ζ
    end.

  Definition from_locale tp ζ := from_locale_from [] tp ζ.

  (* Other possibility is:
  Definition from_locale tp ζ := list_find (λ '(tp, e), locale_of tp e = ζ) (prefixes tp).*)

  Lemma from_locale_from_Some_app tp0 tp tp' ζ e :
    from_locale_from tp0 tp ζ = Some e ->
    from_locale_from tp0 (tp ++ tp') ζ = Some e.
  Proof.
    revert tp0 tp'. induction tp as [|e' tp IH]; first by list_simplifier.
    simpl. intros tp0 tp' Hfl.
    destruct (decide (locale_of tp0 e' = ζ)) =>//.
    apply IH =>//.
  Qed.

  Lemma from_locale_from_is_Some_app tp0 tp tp' ζ :
    is_Some (from_locale_from tp0 tp ζ) ->
    is_Some (from_locale_from tp0 (tp ++ tp') ζ).
  Proof.
    intros [? HS]. eapply from_locale_from_Some_app in HS. eauto.
  Qed.

  Lemma from_locale_from_equiv tp0 tp0' tp tp' ζ :
    locales_equiv tp0 tp0' ->
    locales_equiv_from tp0 tp0' tp tp' ->
    is_Some (from_locale_from tp0 tp ζ) ->
    is_Some (from_locale_from tp0' tp' ζ).
  Proof.
    revert tp0 tp0' tp'. induction tp as [|e tp IH]; intros tp0 tp0' tp' Heq0 Heq [eζ Heζ];
      destruct tp' as [|e' tp']; try by apply Forall2_length in Heq.
    simpl in *.
    destruct (decide (locale_of tp0 e' = ζ)).
    - rewrite decide_True //; eauto. erewrite <-locale_equiv =>//.
    - rewrite decide_False; last by erewrite <-locale_equiv.
      apply Forall2_cons_1 in Heq as [Hlocs ?].
      rewrite decide_False // in Heζ; last by erewrite Hlocs, <-locale_equiv =>//.
      apply (IH (tp0 ++ [e])); eauto.
      apply locales_equiv_snoc =>//. constructor.
  Qed.

  Lemma from_locale_step tp1 tp2 ζ oζ σ1 σ2 :
    locale_step (tp1, σ1) oζ (tp2, σ2) →
    is_Some(from_locale tp1 ζ) →
    is_Some(from_locale tp2 ζ).
  Proof.
    intros Hstep. inversion Hstep; simplify_eq=>//.
    intros HiS. replace (t1 ++ e2 :: t2 ++ efs) with ((t1 ++ e2 :: t2) ++ efs);
                  last by list_simplifier.
    apply from_locale_from_is_Some_app.
    eapply from_locale_from_equiv; eauto; [constructor|].
    apply locales_equiv_from_middle. list_simplifier. by eapply locale_step_preserve.
  Qed.

  Lemma from_locale_from_Some tp0 tp1 tp e :
    (tp, e) ∈ prefixes_from tp0 tp1 →
    from_locale_from tp0 tp1 (locale_of tp e) = Some e.
  Proof.
    revert tp0 tp e; induction tp1 as [| e1 tp1 IH]; intros tp0 tp e Hin; first set_solver.
    apply elem_of_cons in Hin as [Heq|Hin].
    { simplify_eq. rewrite /= decide_True //. }
    rewrite /= decide_False; first by apply IH.
    fold (prefixes_from (A := expr Λ)) in Hin.
    by eapply locale_injective.
  Qed.

End from_locale.

Section locales_utils.
  Context {Λ: language}.

  Definition locales_of_list_from tp0 (tp: list $ expr Λ): list $ locale Λ :=
    (λ '(t, e), locale_of t e) <$> (prefixes_from tp0 tp).
  Notation locales_of_list tp := (locales_of_list_from [] tp).

  Lemma locales_of_list_equiv tp0 tp0' tp1 tp2:
    locales_equiv_from tp0 tp0' tp1 tp2 →
    locales_of_list_from tp0 tp1 = locales_of_list_from tp0' tp2.
  Proof.
    revert tp0 tp0' tp1. induction tp2; intros tp0 tp0' tp1 H;
    destruct tp1 as [|e1 tp1]; try by apply Forall2_length in H.
    unfold locales_of_list_from. simpl.
    simpl in H. apply Forall2_cons_1 in H as [??]. f_equal =>//.
    apply IHtp2 =>//.
  Qed.

  Lemma locales_of_list_step_incl σ1 σ2 oζ tp1 tp2 :
      locale_step (tp1, σ1) oζ (tp2, σ2) ->
      locales_of_list tp1 ⊆ locales_of_list tp2.
  Proof.
    intros H. inversion H; simplify_eq=>//.
    replace (t1 ++ e2 :: t2 ++ efs) with ((t1 ++ e2 :: t2) ++ efs); last by list_simplifier.
    rewrite /locales_of_list_from. rewrite [in X in _ ⊆ X]prefixes_from_app /= fmap_app.
    assert ((λ '(t, e), locale_of t e) <$> prefixes (t1 ++ e1 :: t2) = (λ '(t, e), locale_of t e) <$> prefixes (t1 ++ e2 :: t2))
      as ->; last set_solver.
    apply locales_of_list_equiv, locales_equiv_middle. by eapply locale_step_preserve.
  Qed.

  Lemma locales_of_list_from_locale_from `{EqDecision (locale Λ)} tp0 tp1 ζ:
    is_Some (from_locale_from tp0 tp1 ζ) ->
    ζ ∈ locales_of_list_from tp0 tp1.
  Proof.
    revert tp0; induction tp1 as [|e1 tp1 IH]; intros tp0.
    { simpl. intros H. inversion H. congruence. }
    simpl. intros [e Hsome]. rewrite /locales_of_list_from /=.
    destruct (decide (locale_of tp0 e1 = ζ)); simplify_eq; first set_solver.
    apply elem_of_cons; right. apply IH. eauto.
  Qed.

End locales_utils.
Notation locales_of_list tp := (locales_of_list_from [] tp).


Section adequacy_helper_lemmas.
  Context `{!irisG Λ M Σ}.

  Lemma wp_take_step s Φ ex atr tp1 e1 tp2 σ1 e2 σ2 efs ζ:
    valid_exec ex →
    prim_step e1 σ1 e2 σ2 efs →
    trace_ends_in ex (tp1 ++ e1 :: tp2, σ1) →
    locale_of tp1 e1 = ζ ->
    state_interp ex atr -∗
    WP e1 @ s; ζ; ⊤ {{ v, Φ v } } ={⊤,∅}=∗ |={∅}▷=>^(S $ trace_length ex)
                                             |={∅,⊤}=>
    ∃ δ' ℓ,
      state_interp (trace_extend ex (inl ζ) (tp1 ++ e2 :: tp2 ++ efs, σ2))
                   (trace_extend atr ℓ δ') ∗
      WP e2 @ s; ζ; ⊤ {{ v, Φ v } } ∗
      ([∗ list] i↦ef ∈ efs,
        WP ef @ s; locale_of (tp1 ++ e1 :: tp2 ++ take i efs) ef; ⊤
        {{ v, fork_post (locale_of (tp1 ++ e1 :: tp2 ++ take i efs) ef) v }}).
  Proof.
    iIntros (Hex Hstp Hei Hlocale) "HSI Hwp".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e1) eqn:He1.
    { erewrite val_stuck in He1; done. }
    iMod ("Hwp" $! _ _ ectx_emp with "[//] [] [] HSI") as "[Hs Hwp]";
      [by rewrite locale_fill|by rewrite ectx_fill_emp|].
    iDestruct ("Hwp" with "[]") as "Hwp"; first done.
    iModIntro.
    iApply (step_fupdN_wand with "[Hwp]"); first by iApply "Hwp".
    iIntros "Hwp".
    rewrite !ectx_fill_emp.
    iMod "Hwp" as (δ' ℓ) "(? & ? & ?)".
    iModIntro; iExists _, _; iFrame; done.
  Qed.

  Lemma wp_not_stuck ex atr K tp1 tp2 σ e s Φ ζ :
    valid_exec ex →
    trace_ends_in ex (tp1 ++ ectx_fill K e :: tp2, σ) →
    locale_of tp1 e = ζ ->
    state_interp ex atr -∗
    WP e @ s; ζ; ⊤ {{ v, Φ v }} ={⊤}=∗
    state_interp ex atr ∗
    WP e @ s; ζ; ⊤ {{ v, Φ v }} ∗
    ⌜s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (???) "HSI Hwp".
    rewrite /not_stuck assoc.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "[HSI Hwp]".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e) eqn:He.
    - iModIntro; iPureIntro; eauto.
    - iApply fupd_plain_mask.
      iMod ("Hwp" with "[] [] [] HSI") as "[Hs Hwp]"; [done| by erewrite locale_fill|done|].
      erewrite last_eq_trace_ends_in; last done; simpl.
      iModIntro; destruct s; [iDestruct "Hs" as %?|]; iPureIntro; by eauto.
  Qed.

  Lemma wptp_from_same_locales t0' t0 s tp Φs:
    locales_equiv t0 t0' ->
    wptp_from t0' s tp Φs -∗ wptp_from t0 s tp Φs.
  Proof.
    revert Φs t0 t0'. induction tp; intros Φs t0 t0'; iIntros (Hequiv) "H" =>//.
    simpl.
    iDestruct (big_sepL2_cons_inv_l with "H") as (Φ Φs' ->) "[??]".
    rewrite big_sepL2_cons. simpl. erewrite <-locale_equiv =>//. iFrame.
    iApply IHtp =>//. apply locales_equiv_snoc =>//; [constructor|].
    apply locale_equiv =>//.
  Qed.

  Lemma wptp_not_stuck ex atr σ tp t0 t0' trest s Φs :
    Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0') ->
    valid_exec ex →
    trace_ends_in ex (t0 ++ tp ++ trest, σ) →
    state_interp ex atr -∗ wptp_from t0' s tp Φs ={⊤}=∗
    state_interp ex atr ∗ wptp_from t0 s tp Φs ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (Hsame Hexvalid Hex) "HSI Ht".
    rewrite assoc.
    rewrite (wptp_from_same_locales t0') =>//.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "[HSI Ht]".
    iIntros (e He).
    apply elem_of_list_split in He as (t1 & t2 & ->).
    rewrite prefixes_from_app.
    iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2') "[-> [Ht1 Het2]]".
    iDestruct (big_sepL2_cons_inv_l with "Het2") as (Φ Φs2) "[-> [He Ht2]]".
    iMod (wp_not_stuck _ _ ectx_emp with "HSI He") as "(_ & _ & ?)";
      [done| rewrite ectx_fill_emp // | |done].
    - replace (t0 ++ (t1 ++ e :: t2) ++ trest) with ((t0 ++ t1) ++ e :: (t2 ++ trest)) in Hex.
      + simpl. done.
      + list_simplifier. done.
    - done.
  Qed.

  Lemma wptp_not_stuck_same ex atr σ tp t0 trest s Φs :
    valid_exec ex →
    trace_ends_in ex (t0 ++ tp ++ trest, σ) →
    state_interp ex atr -∗ wptp_from t0 s tp Φs ={⊤}=∗
    state_interp ex atr ∗ wptp_from t0 s tp Φs ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (??) "??". iApply (wptp_not_stuck with "[$] [$]") =>//.
    eapply Forall2_lookup. intros i. destruct (prefixes t0 !! i) as [[??]|]; by constructor.
  Qed.

  Lemma wp_of_val_post e s Φ ζ:
    WP e @ s; ζ; ⊤ {{ v, Φ v }} ={⊤}=∗
    from_option Φ True (to_val e) ∗
    (from_option Φ True (to_val e) -∗ WP e @ s; ζ; ⊤ {{ v, Φ v }}).
  Proof.
    iIntros "Hwp".
    rewrite wp_unfold /wp_pre.
    destruct (to_val e) eqn:He; simpl.
    - iMod "Hwp"; simpl; iFrame; auto.
    - iModIntro.
      iSplit; first by iClear "Hwp".
      iIntros "_"; done.
  Qed.

  Lemma wptp_app s t0 t1 t0t1 Φs1 t2 Φs2 :
    t0t1 = t0 ++ t1 ->
    wptp_from t0 s t1 Φs1 -∗ wptp_from t0t1 s t2 Φs2 -∗ wptp_from t0 s (t1 ++ t2) (Φs1 ++ Φs2).
  Proof.
    iIntros (->) "H1 H2". rewrite prefixes_from_app.
    iApply (big_sepL2_app with "[H1] [H2]"); eauto.
  Qed.

  Lemma wptp_cons_r s e Φ Φs t0 t1:
    WP e @ s; locale_of (t0 ++ t1) e; ⊤ {{v, Φ v}} -∗ wptp_from t0 s t1 Φs
                              -∗ wptp_from t0 s (t1 ++ [e]) (Φs ++ [Φ]).
  Proof.
    iIntros "H1 H2". rewrite !prefixes_from_app.
    iApply (big_sepL2_app with "[H2] [H1]"); eauto.
    rewrite big_sepL2_singleton. done.
  Qed.

  Lemma wptp_cons_l s e Φ t Φs t0:
    WP e @ s; locale_of t0 e; ⊤ {{v, Φ v}} -∗
    wptp_from (t0 ++[e]) s t Φs -∗
    wptp_from t0 s (e :: t) (Φ :: Φs).
  Proof. iIntros "? ?"; rewrite big_sepL2_cons; iFrame. Qed.

  Lemma wptp_of_val_post t s Φs t0:
    wptp_from t0 s t Φs ={⊤}=∗ posts_of t Φs ∗ (posts_of t Φs -∗ wptp_from t0 s t Φs).
  Proof.
    iIntros "Ht"; simpl.
    iInduction t as [|e t IHt] "IH" forall (Φs t0); simpl.
    { iDestruct (big_sepL2_nil_inv_l with "Ht") as %->; eauto. }
    iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs') "[-> [He Ht]] /=".
    iMod (wp_of_val_post with "He") as "[Hpost Hback]".
    iMod ("IH" with "Ht") as "[Ht Htback]".
    iModIntro.
    destruct (to_val e); simpl.
    - iFrame.
      iIntros "[Hpost Htpost]".
      iSplitL "Hpost Hback"; [iApply "Hback"|iApply "Htback"]; iFrame.
    - iFrame.
      iIntros "Hefspost".
      iSplitL "Hback"; [iApply "Hback"|iApply "Htback"]; iFrame; done.
  Qed.

  Notation newelems t t' := (drop (length t) t').
  Notation newposts t t' :=
    (map (λ '(tnew, e), fork_post (locale_of tnew e))
        (prefixes_from t (newelems t t'))).

  Lemma newposts_locales_equiv_helper (t0 t0' t1 t1' t : list (expr Λ)):
    length t1 = length t1' ->
    locales_equiv t0 t0' ->
    map (λ '(tnew, e0), fork_post (locale_of tnew e0))
        (prefixes_from t0 (newelems t1 t)) =
    map (λ '(tnew, e0), fork_post (locale_of tnew e0))
        (prefixes_from t0' (newelems t1' t)).
  Proof.
    intros Hlen1 H.
    assert (Hlen2: length t0 = length t0').
    { apply Forall2_length in H. rewrite !prefixes_from_length // in H. }
    revert t0 t0' t1 t1' Hlen1 Hlen2 H. induction t; intros t0 t0' t1 t1' Hlen1 Hlen2 H.
    - rewrite !drop_nil //.
    - destruct t1; destruct t1' =>//.
      + simpl; f_equal; first erewrite locale_equiv=> //.
        specialize (IHt (t0 ++ [a]) (t0' ++ [a]) _ _ Hlen1).
        simpl in IHt. rewrite !drop_0 in IHt. apply IHt.
        * rewrite !app_length. lia.
        * apply locales_equiv_snoc =>//; first constructor.
          list_simplifier. apply locale_equiv =>//.
      + simpl. apply IHt =>//. simpl in Hlen1. lia.
  Qed.

  Lemma forkposts_locales_equiv (t0 t0' t1 t1' : list (expr Λ)):
    locales_equiv_from t0 t0' t1 t1' ->
    map (λ '(tnew, e0), fork_post (locale_of tnew e0))
        (prefixes_from t0 t1) =
    map (λ '(tnew, e0), fork_post (locale_of tnew e0))
        (prefixes_from t0' t1').
  Proof.
    intros H.
    revert t0 t0' t1' H. induction t1; intros t0 t0' t1' H.
    - destruct t1' =>//. inversion H.
    - destruct t1' =>//; first inversion H.
      inversion H; simplify_eq.
      simpl; f_equal; first by f_equal.
      by apply IHt1.
  Qed.

  Lemma newposts_locales_equiv t0 t0' t:
    locales_equiv t0 t0' ->
    newposts t0 t = newposts t0' t.
  Proof.
    intros H; apply newposts_locales_equiv_helper =>//.
    eapply Forall2_length in H. rewrite !prefixes_from_length // in H.
  Qed.

  Lemma newposts_same_empty t:
    newposts t t = [].
  Proof. rewrite drop_ge //. Qed.

  Lemma new_threads_wptp_from s t efs:
    (([∗ list] i ↦ ef ∈ efs,
      WP ef @ s; locale_of (t ++ take i efs) ef ; ⊤
      {{ v, fork_post (locale_of (t ++ take i efs) ef) v }})
    ⊣⊢ wptp_from t s efs (newposts t (t ++ efs))).
  Proof.
    (* TODO: factorize the two halves *)
    rewrite big_sepL2_alt; iSplit.
    - iIntros "H". iSplit.
      { rewrite drop_app_alt // map_length !prefixes_from_length //. }
      iInduction efs as [|ef efs] "IH" forall (t); first done.
      rewrite /= !drop_app_alt //=.
      iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
      replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                   (prefixes_from (t ++ [ef]) efs))
        with
          (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
      + iApply "IH". iApply (big_sepL_impl with "H").
        iIntros "!>" (k e Hin) "H". by list_simplifier.
      + list_simplifier.
        replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
        rewrite drop_app_alt //.
    - iIntros "[_ H]".
      iInduction efs as [|ef efs] "IH" forall (t); first done.
      rewrite /= !drop_app_alt //=.
      iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
      replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                   (prefixes_from (t ++ [ef]) efs))
        with
          (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
      + iSpecialize ("IH" with "H"). iApply (big_sepL_impl with "IH").
        iIntros "!>" (k e Hin) "H". by list_simplifier.
      + list_simplifier.
        replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
        rewrite drop_app_alt //.
  Qed.

  Lemma take_step s Φs ex atr c c' oζ:
    valid_exec ex →
    trace_ends_in ex c →
    locale_step c oζ c' →
    config_wp -∗
    state_interp ex atr -∗
    wptp s c.1 Φs ={⊤,∅}=∗ |={∅}▷=>^(S (trace_length ex))
                                             |={∅,⊤}=>
    ⌜∀ e2, s = NotStuck → e2 ∈ c'.1 → not_stuck e2 c'.2⌝ ∗
    ∃ δ' ℓ,
      state_interp (trace_extend ex oζ c') (trace_extend atr ℓ δ') ∗
      posts_of  c'.1 (Φs ++ newposts c.1 c'.1) ∗
      (posts_of c'.1 (Φs ++ newposts c.1 c'.1) -∗
        wptp s  c'.1 (Φs ++ newposts c.1 c'.1)).
  Proof.
    iIntros (Hexvalid Hexe Hstep) "config_wp HSI Hc1".
    inversion Hstep as
        [ρ1 ρ2 e1 σ1 e2 σ2 efs t1 t2 -> -> Hpstep | ρ1 ρ2 σ1 lbl σ2 t -> -> Hcfgstep].
    - rewrite /= !prefixes_from_app.
      iDestruct (big_sepL2_app_inv_l with "Hc1") as
          (Φs1 Φs2') "[-> [Ht1 Het2]]".
      iDestruct (big_sepL2_cons_inv_l with "Het2") as (Φ Φs2) "[-> [He Ht2]]".
      iDestruct (wp_take_step with "HSI He") as "He"; [done|done|done|done|].
      iMod "He" as "He". iModIntro. iMod "He" as "He". iModIntro. iNext.
      iMod "He" as "He". iModIntro.
      iApply (step_fupdN_wand with "[He]"); first by iApply "He".
      iIntros "He".
      iMod "He" as (δ' ℓ) "(HSI & He2 & Hefs) /=".
      have Heq: forall a b c d, a ++ e1 :: c ++ d = (a ++ e1 :: c) ++ d.
      { intros **. by list_simplifier. }
      iAssert (wptp_from (t1 ++ e2 :: t2) s efs (newposts (t1 ++ e2 :: t2) ((t1 ++ e2 :: t2) ++ efs)))
        with "[Hefs]" as "Hefs".
      { rewrite -new_threads_wptp_from. iApply (big_sepL_impl with "Hefs").
        iIntros "!#" (i e Hin) "Hwp". list_simplifier.
        erewrite locale_equiv; first by iFrame.
        apply locales_equiv_middle. erewrite locale_step_preserve =>//. }
      assert (valid_exec (ex :tr[inl (locale_of t1 e1)]: (t1 ++ e2 :: t2 ++ efs, σ2))).
      { econstructor; eauto. }
      iMod (wptp_not_stuck_same _ _ σ2 _ _ [] with "HSI Hefs") as "[HSI [Hefs %]]"; [done| | ].
      { list_simplifier. done. }
      iMod (wptp_not_stuck_same _ _ σ2 _ _ (e2 :: (t2 ++ efs)) with "HSI Ht1") as "[HSI [Ht1 %]]"; [done|  |].
      {  list_simplifier. done. }
      iMod (wptp_not_stuck _ _ σ2 _ (t1 ++ [e2]) _ efs with "HSI Ht2") as "[HSI [Ht2 %]]"; [| done | |].
      { rewrite !prefixes_from_app. apply Forall2_app.
        - apply locales_equiv_refl.
        - constructor; last constructor. list_simplifier. erewrite <-locale_step_preserve =>//. }
      { list_simplifier. done. }
      iMod (wp_not_stuck _ _ ectx_emp with "HSI He2") as "[HSI [He2 %]]";
        [done|by rewrite ectx_fill_emp|by erewrite <-locale_step_preserve|].

      iDestruct (wptp_app with "Ht2 Hefs") as "Ht2efs".
      { by list_simplifier. }
      erewrite (locale_step_preserve e1 e2) =>//.
      iDestruct (wptp_cons_l with "He2 Ht2efs") as "He2t2efs".
      iDestruct (wptp_app with "Ht1 He2t2efs") as "Hc2"; [by list_simplifier|].
      iMod (wptp_of_val_post with "Hc2") as "[Hc2posts Hc2back]".
      iModIntro; simpl in *.
      iSplit.
      { iPureIntro; set_solver. }
      iExists δ', ℓ.
      rewrite -!app_assoc.
      iFrame.
      list_simplifier.
      erewrite newposts_locales_equiv;
        [iFrame | apply locales_equiv_middle; erewrite <-locale_step_preserve =>//].
      iIntros "H". iSpecialize ("Hc2back" with "H").
      rewrite prefixes_from_app //.
    - rewrite /= /config_wp.
      iDestruct ("config_wp" with "[] [] [] HSI") as "Hcfg"; [done|done|done|].
      iMod "Hcfg". iModIntro. iMod "Hcfg". iModIntro.
      iNext. iMod "Hcfg". iModIntro.
      iApply (step_fupdN_wand with "[Hcfg]"); first by iApply "Hcfg".
      iIntros "Hcfg".
      iMod "Hcfg" as (δ2 ℓ) "HSI".
      assert (valid_exec (ex :tr[inr lbl]: ((t, σ1).1, σ2))).
      { econstructor; eauto. }
      iMod (wptp_not_stuck _ _ σ2 _ _ _ [] with "HSI Hc1") as "[HSI [Hc1 %]]";
        [apply locales_equiv_refl|done|by list_simplifier|].
      iMod (wptp_of_val_post with "Hc1") as "[Hc1posts Hc1back]".
      iModIntro.
      iSplit; first by auto.
      iExists δ2, ℓ.
      rewrite newposts_same_empty. list_simplifier.
      iFrame.
  Qed.

End adequacy_helper_lemmas.

(** Fixpoint definition of the soundness goal of Trillium *)
Definition fupd_to_bupd_aux `{invGS_gen hlc Σ}
           (rec : coPset → iProp Σ) (E1 : coPset) : iProp Σ :=
  ∀ (P : iProp Σ) E2, ((|={E1,E2}=> rec E2 -∗ P) ==∗ ◇ P).

Definition fupd_to_bupd `{invGS_gen hlc Σ} :=
  bi_greatest_fixpoint fupd_to_bupd_aux.

Instance fupd_to_bupd_aux_bi_mono `{invGS_gen hlc Σ} :
  BiMonoPred (fupd_to_bupd_aux).
Proof.
  split.
  - iIntros (Φ Ψ HΦne HΨne) "#H". iIntros (E1) "HE". iIntros (P E2) "HP".
    iApply "HE"; iMod "HP"; iModIntro. by iIntros; iApply "HP"; iApply "H".
  - iIntros (Φ HΦne). by intros ??? ->%leibniz_equiv.
Qed.

Lemma fupd_to_bupd_unfold `{invGS_gen hlc Σ} E :
  fupd_to_bupd E ≡ fupd_to_bupd_aux fupd_to_bupd E.
Proof. by rewrite /fupd_to_bupd greatest_fixpoint_unfold. Qed.

Lemma fupd_to_bupd_soundness_no_lc `{!invGpreS Σ} (Q : iProp Σ) :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, fupd_to_bupd ⊤ -∗ Q) → ⊢ |==> Q.
Proof.
  iIntros (Hfupd).
  iMod (@wsat_alloc _ (invGpreS0.(invGpreS_wsat))) as (Hw) "[Hw HE]".
  iMod (@later_credits.le_upd.lc_alloc _ (invGpreS0.(invGpreS_lc)) 0) as (Hc) "_".
  set (Hi := InvG HasNoLc _ Hw Hc).
  iApply (@Hfupd Hi).
  assert (NonExpansive (λ E, wsat ∗ ownE E)%I).
  { by intros ??? ->%leibniz_equiv. }
  iApply (greatest_fixpoint_coiter _ (λ E, wsat ∗ ownE E)%I with "[] [$Hw $HE]").
  iIntros "!>" (E1) "?".
  iIntros (P E2) "HP".
  rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def /=.
  iMod ("HP" with "[$]") as ">(Hw & HE & HP)".
  do 2 iModIntro; iApply "HP"; iFrame.
Qed.

Lemma fupd_to_bupd_soundness_no_lc' `{!invGpreS Σ} (Q : iProp Σ) `{!Plain Q} :
  (∀ `{Hinv: !invGS_gen HasNoLc Σ}, fupd_to_bupd ⊤ -∗ Q) → ⊢ Q.
Proof. by iIntros; iApply bupd_plain; iApply fupd_to_bupd_soundness_no_lc. Qed.

Theorem wp_strong_adequacy_helper Σ Λ M `{!invGpreS Σ}
        (s: stuckness) (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        e1 σ1 δ:
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (trace_inv : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI (trace_singleton ([e1], σ1)) (trace_singleton δ) ∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) c,
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex ([e1], σ1)⌝ -∗
         ⌜trace_starts_in atr δ⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         stateI ex atr -∗
         posts_of c.1 (Φ  :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) c.1)))) -∗
         □ (stateI ex atr ∗
             (∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
            ={⊤}=∗ stateI ex atr ∗ trace_inv ex atr) ∗
         ((∀ ex' atr' oζ ℓ,
              ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
          ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  ⊢ Gsim Σ M s ξ (trace_singleton ([e1], σ1)) (trace_singleton δ).
Proof.
  intros Hwp.
  apply extract_except_0.
  iApply fupd_to_bupd_soundness_no_lc'.
  iIntros (Hinv) "HFtB".
  rewrite fupd_to_bupd_unfold /fupd_to_bupd_aux.
  iApply bupd_plain.
  iApply "HFtB".
  iPoseProof (Hwp Hinv) as "Hwp".
  iMod "Hwp" as (stateI trace_inv Φ fork_post) "(#config_wp & HSI & Hwp & Hstep)".
  clear Hwp.
  set (IrisG Λ M Σ Hinv stateI fork_post).
  iAssert (∃ ex atr c1 δ1,
              ⌜trace_singleton ([e1], σ1) = ex⌝ ∗
              ⌜trace_singleton δ = atr⌝ ∗
              ⌜([e1], σ1) = c1⌝ ∗
              ⌜δ = δ1⌝ ∗
              ⌜length c1.1 ≥ 1⌝ ∗
              stateI ex atr ∗
              (∀ ex' atr' oζ ℓ,
                  ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr') ∗
              wptp s c1.1 (Φ :: map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop 1 c1.1))))%I
    with "[HSI Hwp]" as "Hex".
  { iExists (trace_singleton ([e1], σ1)), (trace_singleton δ), ([e1], σ1), δ; simpl.
    iFrame.
    repeat (iSplit; first by auto).
    iIntros (???? ?%not_trace_contract_singleton); done. }
  iDestruct "Hex" as (ex atr c1 δ1 Hexsing Hatrsing Hc1 Hδ1 Hlen) "(HSI & HTI & Htp)".
  assert
    (valid_system_trace ex atr ∧
     trace_starts_in ex ([e1], σ1) ∧
     trace_ends_in ex c1 ∧
     trace_starts_in atr δ ∧
     (∀ ex' atr' oζ ℓ,
         trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'))
    as Hextras.
  { rewrite -Hexsing -Hatrsing -Hc1.
    split; first apply valid_system_trace_singletons.
    repeat (split; first done).
    intros ? ? ? ? ? ?%not_trace_contract_singleton; done. }
  clear Hc1 Hδ1.
  rewrite Hexsing Hatrsing; clear Hexsing Hatrsing.
  iLöb as "IH" forall (ex atr c1 Hextras Hlen) "HSI HTI Htp".
  destruct Hextras as (Hv & Hex & Hc1 & Hatr & Hξ).
  rewrite {2}/Gsim (fixpoint_unfold (Gsim_pre _ _ _ _) _ _).
  destruct c1 as [tp σ1'].
  assert (valid_exec ex) as Hexv.
  { by eapply valid_system_trace_valid_exec_trace. }
  iPoseProof (wptp_not_stuck _ _ _ _ _ _ [] with "[$HSI] Htp") as "Htp";
    [apply locales_equiv_refl|done|by list_simplifier|].
  iMod ("Htp") as "(HSI & Htp & %Hnstk)".
  rewrite (last_eq_trace_ends_in _ (tp, σ1')) in Hnstk; last done.
  iPoseProof (wptp_of_val_post with "Htp") as "Htp".
  iMod ("Htp") as "(Hpost & Hback)".
  iAssert (|={⊤}=> ▷ ⌜ξ ex atr⌝ ∗ (_ ∗ _ ∗ _ ∗ _))%I with "[Hstep HTI HSI Hpost]"
    as ">[Hξ (HSI & Hpost & HTI & Hstep)]".
  { iCombine "HTI" "Hstep" as "HS".
    iCombine "Hpost" "HS" as "HS".
    iCombine "HSI" "HS" as "HS".
    iApply fupd_plain_keep_l; iSplitR; [|iExact "HS"].
    iIntros "(HSI & Hpost & HTI & Hstep)".
    iDestruct ("Hstep" with "[] [] [] [] [] [] HSI Hpost") as "[_ Hξ]"; auto.
    iApply fupd_plain_mask.
    iMod ("Hξ" with "HTI") as "%"; auto. }
  iAssert (□ (stateI ex atr -∗
             (∀ ex' atr' oζ ℓ,
                 ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
                 ={⊤}=∗ stateI ex atr ∗ trace_inv ex atr))%I as "#HTIextend".
  { iDestruct ("Hstep" with "[] [] [] [] [] [] HSI Hpost") as "[#Hext _]"; auto.
    iModIntro.
    iIntros "HSI HTI".
    iApply ("Hext" with "[$HSI $HTI]"). }
  iMod ("HTIextend" with "HSI HTI") as "[HSI HTI]".
  iDestruct ("Hback" with "Hpost") as "Htp".
  iModIntro.
  iIntros "HFtB".
  iNext; iSplit; first done.
  iDestruct "Hξ" as %Hξ'.
  iIntros (c oζ c' Hc Hstep).
  pose proof (trace_ends_in_inj ex c (tp, σ1') Hc Hc1); simplify_eq.
  iPoseProof (take_step with "config_wp HSI Htp") as "Hstp"; [done|done|done|].
  assert (∃ n, n = trace_length ex) as [n Hn] by eauto.
  rewrite -Hn.
  clear Hn.
  rewrite -> fupd_to_bupd_unfold; rewrite /fupd_to_bupd_aux.
  iApply except_0_later.
  iApply bupd_plain.
  iApply "HFtB".
  iMod "Hstp"; simpl.
  iMod "Hstp".
  iModIntro.
  iIntros "HFtB".
  rewrite (fupd_to_bupd_unfold (∅ : coPset)); rewrite /fupd_to_bupd_aux.
  iNext.
  iApply except_0_later.
  iApply bupd_plain.
  iApply "HFtB".
  iMod "Hstp".
  iModIntro.
  iIntros "HFtB".
  iInduction n as [|n] "IHlen"; simpl; last first.
  { rewrite (fupd_to_bupd_unfold (∅ : coPset)); rewrite /fupd_to_bupd_aux.
    iApply except_0_later.
    iApply bupd_plain.
    iApply "HFtB".
    iMod "Hstp".
    iModIntro.
    iIntros "HFtB".
    rewrite (fupd_to_bupd_unfold (∅ : coPset)); rewrite /fupd_to_bupd_aux.
    iNext.
    iApply except_0_later.
    iApply bupd_plain.
    iApply "HFtB".
    iMod "Hstp".
    iModIntro.
    iIntros "HFtB".
    rewrite (fupd_to_bupd_unfold (∅ : coPset)); rewrite /fupd_to_bupd_aux.
    iApply ("IHlen" with "Hstep HTI Hstp"); done. }
  rewrite (fupd_to_bupd_unfold (∅ : coPset)); rewrite /fupd_to_bupd_aux.
  iApply except_0_later.
  iApply bupd_plain.
  iApply "HFtB".
  iMod "Hstp" as "(% & H)".
  iModIntro.
  iIntros "HFtB".
  iDestruct "H" as (δ'' ℓ) "(HSI & Hpost & Hback)"; simpl in *.
  iSpecialize ("Hback" with "Hpost").
  assert (Hlocales: map (λ '(tnew, e), weakestpre.fork_post (locale_of tnew e))
                    (prefixes_from [e1] (drop 1 tp)) ++
                  map (λ '(tnew, e), weakestpre.fork_post (locale_of tnew e))
                  (prefixes_from tp (drop (length tp) c'.1))
         = map (λ '(tnew, e), weakestpre.fork_post (locale_of tnew e))
                    (prefixes_from [e1] (drop 1 c'.1)) ).
  { pose proof (locale_valid_exec _ _ _ _ _ Hexv Hex Hc) as Hequivex.
    destruct c'.1 as [|e3 tp3_rest] eqn:Heq.
    { exfalso. pose proof (step_tp_length _ _ _ Hstep). rewrite ->Heq in *. simpl in *. lia. }
    destruct tp as [|e2 tp2_rest] eqn:Heq'.
    { simpl in Hlen; lia. }
    change fork_post with weakestpre.fork_post.
    assert (locale_of [] e1 = locale_of [] e2); first by inversion Hequivex.
    change 1 with (length [e1]).
    rewrite !(newposts_locales_equiv [e1] [e2]); [| by constructor =>// | by constructor =>//].
    rewrite ![drop _ _]/=.
    rewrite drop_0.
    assert (Hequiv: locales_equiv (e2 :: tp2_rest) (take (length (e2 :: tp2_rest)) (e3 :: tp3_rest))).
    { pose proof (locale_step_equiv _ _ _ Hstep) as Hequiv.
      rewrite Heq // in Hequiv. }
    assert (Hequiv_from: locales_equiv_from [e2] [e3] tp2_rest (take (length tp2_rest) tp3_rest)).
    { change [e2] with ([] ++ [e2]).
      change [e3] with ([] ++ [e3]).
      change (e2 :: tp2_rest) with ([e2] ++ tp2_rest) in Hequiv.
      rewrite [take _ _]/= in Hequiv.
      change (e3 :: take (length tp2_rest) tp3_rest) with ([e3] ++ take (length tp2_rest) tp3_rest) in Hequiv.
      assert (length tp2_rest = length (take (length tp2_rest) tp3_rest)) as Hlen'.
      { rewrite take_length. pose proof (step_tp_length _ _ _ Hstep) as Hdec.
        rewrite Heq /= in Hdec. lia. }
      apply (locales_equiv_from_impl _ _ _ _ _ _ Hlen' Hequiv) =>//. }
    erewrite forkposts_locales_equiv; last done.
    assert (Hequiv_from': forall t, locales_equiv_from (e2 :: tp2_rest) (e3 :: take (length tp2_rest) tp3_rest) t t).
    { intros t. by apply locales_from_equiv_refl. }
    erewrite (forkposts_locales_equiv (e2 :: tp2_rest)); last first.
    { eauto using Hequiv_from'. }
    assert (Hequiv_from'': forall t, locales_equiv_from [e2] [e3] t t).
    { intros t. apply locales_from_equiv_refl. constructor =>//. by inversion Hequiv. }
    erewrite (forkposts_locales_equiv [e2]); last by eauto.
    rewrite -map_app -prefixes_from_app take_drop.
    rewrite [drop _ _]/= drop_0 //. }
  iAssert (▷ ⌜ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ'')⌝)%I as "#Hextend'".
  { iDestruct ("Hstep" with "[] [] [] [] [] [] HSI") as "H"; [iPureIntro..|].
    - eapply valid_system_trace_extend; eauto.
    - eapply trace_extend_starts_in; eauto.
    - eapply trace_extend_starts_in; eauto.
    - eapply trace_extend_ends_in; eauto.
    - by intros ? ? ? ? [-> ->]%trace_contract_of_extend [-> ->]%trace_contract_of_extend.
    - done.
    - rewrite Hlocales.
      iPoseProof (wptp_of_val_post with "Hback") as "Hback".
      rewrite -> (fupd_to_bupd_unfold (⊤ : coPset)); rewrite /fupd_to_bupd_aux.
      iApply except_0_later.
      iApply bupd_plain.
      iApply "HFtB".
      iMod "Hback" as "(Hpost & Hwptp)".
      iDestruct ("H" with "Hpost") as "[? Hξ]".
      iMod ("Hξ" with "[HTI]") as "%".
      + iIntros (? ? ? ? [-> ->]%trace_contract_of_extend
                 [-> ->]%trace_contract_of_extend); done.
      + iModIntro.
        iIntros "HFtB"; done. }
  iExists _, _.
  rewrite -> (fupd_to_bupd_unfold (⊤ : coPset)); rewrite /fupd_to_bupd_aux.
  iApply except_0_later.
  iApply bupd_plain.
  iApply "HFtB".
  iMod ("IH" with "[] [] Hstep HSI [HTI] [Hback]") as "IH'".
  - iPureIntro; split_and!.
    + eapply valid_system_trace_extend; eauto.
    + eapply trace_extend_starts_in; eauto.
    + eapply trace_extend_ends_in; eauto.
    + eapply trace_extend_starts_in; eauto.
    + by intros ???? [-> ->]%trace_contract_of_extend
                [-> ->]%trace_contract_of_extend.
  - iPureIntro. pose proof (step_tp_length _ _ _ Hstep). simpl in *. lia.
  - iIntros (???? [-> ->]%trace_contract_of_extend
                  [-> ->]%trace_contract_of_extend); done.
  - rewrite Hlocales //.
  - iModIntro. iIntros "HFtB". iNext. iApply "IH'"; done.
Qed.

Definition rel_finitary {A B C D}
           (ξ : finite_trace A B → finite_trace C D → Prop) :=
  ∀ (ex : finite_trace A B) (atr : finite_trace C D) c' oζ,
    smaller_card (sig (λ '(δ', ℓ), ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ'))) nat.

Section finitary_lemma.
  Lemma rel_finitary_impl {A B C D} `{EqDecision C, EqDecision D}
        (ξ ξ' : finite_trace A B -> finite_trace C D -> Prop):
    (∀ ex aux, ξ ex aux -> ξ' ex aux) ->
    rel_finitary ξ' ->
    rel_finitary ξ.
  Proof.
    intros Himpl Hξ' ex aux c' oζ.
    assert (
        ∀ ξ x, ProofIrrel
                 (match x return Prop with (δ', ℓ) =>
                    ξ (ex :tr[ oζ ]: c') (aux :tr[ ℓ ]: δ')
                  end)).
    { intros ?[??]. apply make_proof_irrel. }
    apply finite_smaller_card_nat.
    specialize (Hξ' ex aux c' oζ). apply smaller_card_nat_finite in Hξ'.
    eapply (in_list_finite (map proj1_sig (@enum _ _ Hξ'))).
    intros [δ' ℓ] ?. apply elem_of_list_fmap.
    assert ((λ '(δ', ℓ), ξ' (ex :tr[ oζ ]: c') (aux :tr[ ℓ ]: δ')) (δ', ℓ)) by eauto.
    exists ((δ', ℓ) ↾ ltac:(eauto)). split =>//.
    apply elem_of_enum.
  Qed.
End finitary_lemma.

(** We can extract the simulation correspondence in the meta-logic
    from a proof of the simulation correspondence in the object-logic. *)
Theorem simulation_correspondence Λ M Σ `{!invGpreS Σ}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        e1 σ1 δ1 :
  rel_finitary ξ →
  (⊢ Gsim Σ M s ξ {tr[ ([e1], σ1) ]} {tr[ δ1 ]}) →
  continued_simulation ξ {tr[ ([e1], σ1) ]} {tr[δ1]}.
Proof.
  intros Hsc Hwptp.
  exists (λ exatr, ⊢ Gsim Σ M s ξ exatr.1 exatr.2); split; first done.
  clear Hwptp.
  intros [ex atr].
  rewrite {1}/Gsim (fixpoint_unfold (Gsim_pre _ _ _ _) _ _); simpl; intros Hgsim.
  revert Hgsim; rewrite extract_later; intros Hgsim.
  apply extract_and in Hgsim as [Hvlt Hgsim].
  revert Hvlt; rewrite extract_pure; intros Hvlt.
  split; first done.
  intros c c' oζ Hsmends Hstep.
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim c).
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim oζ).
  revert Hgsim; rewrite extract_forall; intros Hgsim.
  specialize (Hgsim c').
  apply (extract_impl ⌜_⌝) in Hgsim; last by apply extract_pure.
  apply (extract_impl ⌜_⌝) in Hgsim; last by apply extract_pure.
  induction (trace_length ex) as [|n IHlen]; last first.
  { simpl in *.
    revert Hgsim; do 3 rewrite extract_later; intros Hgsim.
    apply IHlen. do 2 rewrite extract_later. apply Hgsim. }
  revert Hgsim; rewrite !extract_later; intros Hgsim.
  simpl in *.
  assert (⊢ ▷ ∃ (δ': M) ℓ,
               (⌜ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ')⌝) ∧
               fixpoint (Gsim_pre Σ M s ξ) (ex :tr[oζ]: c') (atr :tr[ℓ]: δ')).
  { iStartProof. iDestruct Hgsim as (δ'' ℓ) "Hfix". iExists δ'', ℓ.
    iSplit; last done.
    rewrite (fixpoint_unfold (Gsim_pre _ _ _ _) _ _) /Gsim_pre.
    iNext. by iDestruct "Hfix" as "[? _]". }
  rewrite -> extract_later in H.
  apply extract_exists_alt2 in H as (δ'' & ℓ & H); last done.
  exists δ'', ℓ.
  revert H.
  rewrite !extract_and.
  intros [_ ?]; done.
Qed.

Theorem wp_strong_adequacy_with_trace_inv Λ M Σ `{!invGpreS Σ}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        e1 σ1 δ1 :
  rel_finitary ξ →
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (trace_inv : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI (trace_singleton ([e1], σ1)) (trace_singleton δ1) ∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) (c : cfg Λ),
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex ([e1], σ1)⌝ -∗
         ⌜trace_starts_in atr δ1⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         stateI ex atr -∗
         posts_of c.1 (Φ  :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) c.1)))) -∗
         □ (stateI ex atr ∗
             (∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
            ={⊤}=∗ stateI ex atr ∗ trace_inv ex atr) ∗
         ((∀ ex' atr' oζ ℓ,
              ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
          ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  continued_simulation ξ (trace_singleton ([e1], σ1)) (trace_singleton δ1).
Proof.
  intros Hsc Hwptp%wp_strong_adequacy_helper; last done.
  by eapply simulation_correspondence.
Qed.

Theorem wp_strong_adequacy Λ M Σ `{!invGpreS Σ}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        e1 σ1 δ1 :
  rel_finitary ξ →
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       stateI (trace_singleton ([e1], σ1)) (trace_singleton δ1) ∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) c,
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex ([e1], σ1)⌝ -∗
         ⌜trace_starts_in atr δ1⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         stateI ex atr -∗
         posts_of c.1 (Φ  :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) c.1)))) -∗
         |={⊤, ∅}=> ⌜ξ ex atr⌝)) ->
  continued_simulation ξ (trace_singleton ([e1], σ1)) (trace_singleton δ1).
Proof.
  intros Hsc Hwptp.
  eapply wp_strong_adequacy_with_trace_inv; [done|done|].
  iIntros (Hinv) "".
  iMod (Hwptp Hinv) as (stateI Φ fork_post) "(Hwpcfg & HSI & Hwp & Hstep)".
  iModIntro.
  iExists stateI, (λ _ _, True)%I, Φ, fork_post; iFrame "Hwpcfg HSI Hwp".
  iIntros (ex atr c ? ? ? ? ? ?) "HSI Hposts".
  iSplit; last first.
  { iIntros "?". iApply ("Hstep" with "[] [] [] [] [] [] HSI"); eauto. }
  iModIntro; iIntros "[$ ?]"; done.
Qed.

(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate {Λ} (s : stuckness) (e1 : expr Λ) (σ1 : state Λ)
    (φ : val Λ → state Λ → Prop) : Prop := {
  adequate_result ex t2 σ2 v2 :
    valid_exec ex →
   trace_starts_in ex ([e1], σ1) →
   trace_ends_in ex (of_val v2 :: t2, σ2) →
   φ v2 σ2;
  adequate_not_stuck ex t2 σ2 e2 :
   s = NotStuck →
   valid_exec ex →
   trace_starts_in ex ([e1], σ1) →
   trace_ends_in ex (t2, σ2) →
   e2 ∈ t2 → not_stuck e2 σ2
}.

Lemma adequate_alt {Λ} s e1 σ1 (φ : val Λ → state Λ → Prop) :
  adequate s e1 σ1 φ ↔ ∀ ex t2 σ2,
      valid_exec ex →
      trace_starts_in ex ([e1], σ1) →
      trace_ends_in ex (t2, σ2) →
      (∀ v2 t2', t2 = of_val v2 :: t2' → φ v2 σ2) ∧
      (∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) ex t2 σ1 σ2 φ :
  adequate NotStuck e1 σ1 φ →
  valid_exec ex →
  trace_starts_in ex ([e1], σ1) →
  trace_ends_in ex (t2, σ2) →
  Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3).
Proof.
  intros Had ? ? ?.
  destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2).
  destruct (adequate_not_stuck NotStuck e1 σ1 φ Had ex t2 σ2 e2)
    as [?|(e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto.
  right; exists (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto.
Qed.

Local Definition wp_adequacy_relation Λ M s (φ : val Λ → Prop)
           (ex : execution_trace Λ) (atr : auxiliary_trace M) : Prop :=
  ∀ c, trace_ends_in ex c →
       (∀ v2 t2', c.1 = of_val v2 :: t2' → φ v2) ∧
       (∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2).

Local Lemma wp_adequacy_relation_adequacy {Λ M} s e σ δ φ (ξ : _ -> _ -> Prop):
  (forall ex aux, ξ ex aux -> wp_adequacy_relation Λ M s φ ex aux) ->
  continued_simulation
    ξ
    (trace_singleton ([e], σ))
    (trace_singleton δ) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Himpl Hsm; apply adequate_alt.
  intros ex t2 σ2 Hex Hexstr Hexend.
  eapply simulation_does_continue in Hex as [atr [? Hatr]]; eauto.
  rewrite -> continued_simulation_unfold in Hatr.
  destruct Hatr as (Hψ & Hatr).
  apply Himpl in Hψ.
  apply (Hψ (t2, σ2)); done.
Qed.

Corollary adequacy_xi Λ M Σ `{!invGpreS Σ} `{EqDecision (mlabel M), EqDecision M}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        (φ : val Λ → Prop)
        e1 σ1 δ1 :
  rel_finitary ξ →
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (trace_inv : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       (∀ v, Φ v -∗ ⌜φ v⌝) ∗
       stateI (trace_singleton ([e1], σ1)) (trace_singleton δ1) ∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) c,
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex ([e1], σ1)⌝ -∗
         ⌜trace_starts_in atr δ1⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         stateI ex atr -∗
         posts_of c.1 (Φ  :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) c.1)))) -∗
         □ (stateI ex atr ∗
             (∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
            ={⊤}=∗ stateI ex atr ∗ trace_inv ex atr) ∗
         ((∀ ex' atr' oζ ℓ,
              ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
          ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  adequate s e1 σ1 (λ v _, φ v).
Proof.
  pose (ξ' := λ ex aux, ξ ex aux ∧ wp_adequacy_relation Λ M s φ ex aux).
  intros ? Hwp; apply (wp_adequacy_relation_adequacy (M := M) _ _ _ δ1 _ ξ').
  { by intros ??[??]. }
  apply (wp_strong_adequacy_with_trace_inv Λ M Σ s).
  { apply (rel_finitary_impl ξ' ξ) =>//. by intros ??[??]. }
  iIntros (?) "".
  iMod Hwp as (stateI post Φ fork_post) "(config_wp & HΦ & HSI & Hwp & H)".
  iModIntro; iExists _, _, _, _. iFrame "config_wp HSI Hwp".
  iIntros (ex atr c Hvlt Hexs Hexe Hatre Hψ Hnst) "HSI Hposts".
  iSpecialize ("H" with "[//] [//] [//] [//] [] [//]").
  - iPureIntro. intros ??????. by eapply Hψ.
  - simpl.
    iAssert (⌜∀ v t, c.1 = of_val v :: t → φ v⌝)%I as "%Hφ".
    { iIntros (?? ->). rewrite /= to_of_val /=.
      iApply "HΦ". iDestruct "Hposts" as "[$ ?]". }
    iDestruct ("H" with "HSI Hposts") as "[? H]". iSplit =>//.
    iIntros "H1". iMod ("H" with "H1"). iModIntro. iSplit=>//.
    iIntros (c' Hc').
    assert (c' = c) as -> by by eapply trace_ends_in_inj. eauto.
Qed.

Corollary sim_and_adequacy_xi Λ M Σ `{!invGpreS Σ} `{EqDecision (mlabel M), EqDecision M}
        (s: stuckness)
        (ξ : execution_trace Λ → auxiliary_trace M → Prop)
        (φ : val Λ → Prop)
        e1 σ1 δ1 :
  rel_finitary ξ →
  (∀ `{Hinv : !invGS_gen HasNoLc Σ},
    ⊢ |={⊤}=> ∃
         (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (trace_inv : execution_trace Λ → auxiliary_trace M → iProp Σ)
         (Φ : val Λ → iProp Σ)
         (fork_post : locale Λ → val Λ → iProp Σ),
       let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in
       config_wp ∗
       (∀ v, Φ v -∗ ⌜φ v⌝) ∗
       stateI (trace_singleton ([e1], σ1)) (trace_singleton δ1) ∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace Λ) (atr : auxiliary_trace M) c,
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex ([e1], σ1)⌝ -∗
         ⌜trace_starts_in atr δ1⌝ -∗
         ⌜trace_ends_in ex c⌝ -∗
         ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
         stateI ex atr -∗
         posts_of c.1 (Φ  :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) c.1)))) -∗
         □ (stateI ex atr ∗
             (∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
            ={⊤}=∗ stateI ex atr ∗ trace_inv ex atr) ∗
         ((∀ ex' atr' oζ ℓ,
              ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
          ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  (continued_simulation ξ (trace_singleton ([e1], σ1)) (trace_singleton δ1) ∧
     adequate s e1 σ1 (λ v _, φ v)).
Proof.
  intros ? Hwp. split; eauto using adequacy_xi.
  eapply wp_strong_adequacy_with_trace_inv; [done|done|].
  iIntros (?). iMod Hwp as (? ? ? ?) "(?&?&?&?&?)".
  iModIntro. iExists _, _, _, _. iFrame.
Qed.

(* Corollary wp_adequacy Λ M Σ `{!invGpreS Σ} s e σ δ φ : *)
(*   (∀ `{Hinv : !invGS_gen HasNoLc Σ}, *)
(*      ⊢ |={⊤}=> ∃ *)
(*          (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ) *)
(*          (fork_post : locale Λ -> val Λ → iProp Σ), *)
(*        let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in *)
(*        config_wp ∗ stateI (trace_singleton ([e], σ)) (trace_singleton δ) ∗ *)
(*        WP e @ s; locale_of [] e; ⊤ {{ v, ⌜φ v⌝ }}) → *)
(*   adequate s e σ (λ v _, φ v). *)
(* Proof. *)
(*   intros Hwp. *)
(*   pose (ξ := λ ex aux, wp_adequacy_relation Λ M s φ ex aux). *)
(*   eapply (wp_adequacy_relation_adequacy (M := M) _ _ _ δ φ ξ)=>//. *)
(*   apply (wp_strong_adequacy Λ M Σ s). *)
(*   { admit. } *)
(*   iIntros (?) "". *)
(*   iMod Hwp as (stateI fork_post) "(config_wp & HSI & Hwp)". *)
(*   iModIntro; iExists _, _, _; iFrame. *)
(*   iIntros (ex atr c Hvlt Hexs Hatrs Hexe Hψ Hnst) "HSI Hposts". *)
(*   iApply fupd_mask_intro_discard; first done. *)
(*   (* iPureIntro. *) *)
(*   (* iSplit. *) *)
(*   (* {  *) *)
(*   (* admit.  *) *)
(*   (* iSplit. *) *)
(*   (* { *) *)
(*   iIntros (c' Hc'). *)
(*   assert (c' = c) as -> by by eapply trace_ends_in_inj. *)
(*   iSplit; last done. *)
(*   iIntros (v2 t2 ->). rewrite /= to_of_val /=. *)
(*   iDestruct "Hposts" as "[% ?]"; done. *)
(* Qed. *)

(* Local Definition wp_invariance_relation Λ M e1 σ1 t2 σ2 (φ : Prop) *)
(*       (ex : execution_trace Λ) (atr : auxiliary_trace M) : Prop := *)
(*   trace_starts_in ex ([e1], σ1) → trace_ends_in ex (t2, σ2) → φ. *)

(* Local Lemma wp_invariance_relation_invariance {Λ M} e1 σ1 δ1 t2 σ2 φ : *)
(*   continued_simulation *)
(*     (wp_invariance_relation Λ M e1 σ1 t2 σ2 φ) *)
(*     (trace_singleton ([e1], σ1)) *)
(*     (trace_singleton δ1) → *)
(*   ∀ ex, *)
(*     valid_exec ex → *)
(*     trace_starts_in ex ([e1], σ1) → *)
(*     trace_ends_in ex (t2, σ2) → *)
(*     φ. *)
(* Proof. *)
(*   intros Hsm ex Hex Hexstr Hexend. *)
(*   eapply simulation_does_continue in Hsm as [atr [? Hatr]]; eauto. *)
(*   rewrite -> continued_simulation_unfold in Hatr. *)
(*   destruct Hatr as (Hψ & Hatr); auto. *)
(* Qed. *)

(* Corollary wp_invariance Λ M Σ `{!invGpreS Σ} s e1 σ1 δ1 t2 σ2 φ : *)
(*   rel_finitary (wp_invariance_relation Λ M e1 σ1 t2 σ2 φ) → *)
(*   (∀ `{Hinv : !invGS_gen HasNoLc Σ}, *)
(*      ⊢ |={⊤}=> ∃ *)
(*          (stateI : execution_trace Λ → auxiliary_trace M → iProp Σ) *)
(*          (fork_post : locale Λ -> val Λ → iProp Σ), *)
(*        let _ : irisG Λ M Σ := IrisG _ _ _ Hinv stateI fork_post in *)
(*        config_wp ∗ stateI (trace_singleton ([e1], σ1)) (trace_singleton δ1) ∗ *)
(*        WP e1 @ s; locale_of [] e1; ⊤ {{ _, True }} ∗ *)
(*        (∀ ex atr, *)
(*            ⌜valid_system_trace ex atr⌝ → *)
(*            ⌜trace_starts_in ex ([e1], σ1)⌝ → *)
(*            ⌜trace_starts_in atr δ1⌝ → *)
(*            ⌜trace_ends_in ex (t2, σ2)⌝ → *)
(*            stateI ex atr -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) → *)
(*   ∀ ex, *)
(*     valid_exec ex → *)
(*     trace_starts_in ex ([e1], σ1) → *)
(*     trace_ends_in ex (t2, σ2) → *)
(*     φ. *)
(* Proof. *)
(*   intros ? Hwp. *)
(*   apply (wp_invariance_relation_invariance _ _ δ1). *)
(*   apply (wp_strong_adequacy Λ M Σ s); first done. *)
(*   iIntros (?) "". *)
(*   iMod Hwp as (stateI fork_post) "(config_wp & HSI & Hwp & Hφ)". *)
(*   iModIntro; iExists _, _, _; iFrame. *)
(*   iIntros (ex atr c Hvlt Hexs Hatrs Hexe Hψ Hnst) "HSI Hposts". *)
(*   rewrite /wp_invariance_relation. *)
(*   iAssert ((∀ _ : trace_starts_in ex ([e1], σ1) ∧ trace_ends_in ex (t2, σ2), *)
(*                  |={⊤}=> ⌜φ⌝)%I) with "[HSI Hφ]" as "H". *)
(*   { iIntros ([? ?]). *)
(*     assert (c = (t2, σ2)) as -> by by eapply trace_ends_in_inj. *)
(*     iDestruct ("Hφ" with "[] [] [] [] HSI") as (E) "Hφ"; [done|done|done|done|]. *)
(*     iDestruct (fupd_plain_mask with "Hφ") as ">Hφ"; done. } *)
(*   rewrite -fupd_plain_forall'. *)
(*   iMod "H". *)
(*   iApply fupd_mask_intro_discard; first done. *)
(*   iIntros (Hexs' Hexe'); iApply "H"; done. *)
(* Qed. *)
