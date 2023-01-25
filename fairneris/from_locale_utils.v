(* TODO: Clean up imports *)
From Paco Require Import pacotac.
From stdpp Require Import finite.
From iris.proofmode Require Import proofmode.
From fairneris.aneris_lang.state_interp Require Import state_interp_def.
From fairneris.aneris_lang.state_interp Require Import state_interp_config_wp.
From fairneris.aneris_lang.state_interp Require Import state_interp.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.

Lemma from_locale_from_elem_of es tp ζ e :
  from_locale_from es tp ζ = Some e → ∃ i, tp !! i = Some e.
Proof.
  revert es.
  induction tp as [|e' tp IHtp]; [done|].
  intros es Hlocale.
  rewrite /from_locale in Hlocale.
  simpl in *.
  case_decide.
  - simplify_eq. exists 0%nat. rewrite lookup_cons. done.
  - specialize (IHtp (es ++ [e']) Hlocale) as [i Hi].
    exists (S i). done.
Qed.

Lemma from_locale_elem_of tp ζ e :
  from_locale tp ζ = Some e → ∃ i, tp !! i = Some e.
Proof. apply from_locale_from_elem_of. Qed.

Lemma from_locale_from_elem_of' es tp ζ e :
  from_locale_from es tp ζ = Some e →
  ∃ i, tp !! i = Some e ∧ locale_of (es ++ take i tp) e = ζ.
Proof.
  revert es.
  induction tp as [|e' tp IHtp]; [done|].
  intros es Hlocale.
  rewrite /from_locale in Hlocale.
  simpl in *.
  case_decide.
  - simplify_eq. exists 0%nat. rewrite lookup_cons.
    rewrite right_id. done.
  - specialize (IHtp (es ++ [e']) Hlocale) as [i [Hlookup Hi]].
    exists (S i). simpl. split; [done|].
    rewrite cons_middle assoc. done.
Qed.

Lemma from_locale_elem_of' tp ζ e :
  from_locale tp ζ = Some e → ∃ i, tp !! i = Some e ∧ locale_of (take i tp) e = ζ.
Proof. apply from_locale_from_elem_of'. Qed.

Lemma posts_of_idx
      `{!anerisG (fair_model_to_model simple_fair_model) Σ}
      (e : aneris_expr) v (tp : list aneris_expr) ζ :
  from_locale tp ζ = Some e → aneris_to_val e = Some v →
  posts_of tp
           (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes tp)) -∗
  (∃ ℓ, ⌜labels_match (inl ζ) ℓ⌝ ∗ dead_role_frag_own ℓ)%I.
Proof.
  iIntros (Hlocale Hval) "Hposts".
  apply from_locale_elem_of' in Hlocale as [i [Hlookup Hlocale]].
  iDestruct (big_sepL_elem_of _ _ _ with "Hposts") as "H".
  { rewrite elem_of_list_omap.
    eexists (e, (λ _, ∃ ℓ : simple_role, ⌜labels_match (inl ζ) ℓ⌝ ∗ dead_role_frag_own ℓ)%I).
    split; last first.
    - simpl. apply fmap_Some. exists v. split; done.
    - destruct tp as [|e1' tp]; [set_solver|]. simpl.
      apply elem_of_cons.
      destruct i as [|i]; [left|right].
      * simpl in *. simplify_eq. done.
      * apply elem_of_lookup_zip_with.
        eexists i, e, _.
        do 2 split=> //.
        rewrite /locale_of /=.
        rewrite list_lookup_fmap fmap_Some. simpl in Hlookup.
        exists (e1' :: take i tp, e). simpl in *.
        split.
        -- erewrite prefixes_from_lookup =>//.
        -- rewrite /locale_of in Hlocale.
           rewrite Hlocale.
           done. }
  done.
Qed.

(* TODO: Should likely move this to [lang.v] *)
Definition locale_of' (ips : list ip_address) ip :=
  (ip, length $ (filter (λ ip', ip' = ip)) ips).

Lemma locale_of_locale_of' es e :
  locale_of es e = locale_of' (map expr_n es) (expr_n e).
Proof.
  induction es; [done|].
  rewrite /locale_of /locale_of'. simpl.
  rewrite !filter_cons. case_decide; [|done]=> /=.
  f_equiv. rewrite /locale_of /locale_of' in IHes. simplify_eq. by rewrite IHes.
Qed.

Lemma prefixes_map_from_locale_of_locale_of' tp0 tp1 :
  map (λ '(t,e), locale_of t e) (prefixes_from tp0 tp1) =
  map (λ '(t,e), locale_of' t e) (prefixes_from (map expr_n tp0) (map expr_n tp1)).
Proof.
  revert tp0.
  induction tp1; [done|]; intros tp0=> /=.
  rewrite locale_of_locale_of'. f_equiv.
  replace ([expr_n a]) with (map expr_n [a]) by done.
  rewrite -(map_app _ tp0 [a]).
  apply IHtp1.
Qed.

(* This is almost identical to above lemma, but differs in [map] vs [list_fmap] *)
Lemma prefixes_list_fmap_from_locale_of_locale_of' tp0 tp1 :
  (λ '(t,e), locale_of t e) <$> prefixes_from tp0 tp1 =
  (λ '(t,e), locale_of' t e) <$> prefixes_from (map (expr_n) tp0) (map expr_n tp1).
Proof.
  revert tp0.
  induction tp1; [done|]; intros tp0=> /=.
  rewrite locale_of_locale_of'. f_equiv.
  replace ([expr_n a]) with (map expr_n [a]) by done.
  rewrite -(map_app _ tp0 [a]).
  apply IHtp1.
Qed.

Lemma prefixes_from_take {A} n (xs ys : list A) :
  prefixes_from xs (take n ys) = take n (prefixes_from xs ys).
Proof.
  revert n xs.
  induction ys as [|y ys IHys]; intros n xs.
  { by rewrite !take_nil. }
  destruct n; [done|]=> /=. by f_equiv.
Qed.

Lemma locales_of_list_from_drop Σ
    `{!anerisG (fair_model_to_model simple_fair_model) Σ} es es' tp :
  locales_equiv_prefix_from es' es tp →
  (λ '(t,e) v, fork_post (locale_of t e) v) <$>
      (prefixes_from es' tp) =
  (λ '(t,e) v, fork_post (locale_of t e) v) <$>
      (prefixes_from es' (es ++ drop (length es) tp)).
Proof.
  intros Hζ. apply locales_of_list_from_fork_post.
  by apply locales_of_list_equiv, locales_equiv_prefix_from_drop.
Qed.

Lemma posts_of_length_drop Σ
    `{!anerisG (fair_model_to_model simple_fair_model) Σ} es es' tp :
  locales_equiv_prefix_from es' es tp →
  posts_of tp ((λ '(t,e) v, fork_post (locale_of t e) v) <$>
                   (prefixes_from es' (es ++ drop (length es) tp))) -∗
  posts_of tp ((λ '(t,e) v, fork_post (locale_of t e) v) <$>
                   (prefixes_from es' tp)).
Proof. iIntros (Hζ) "H". by erewrite <-locales_of_list_from_drop. Qed.
