From fairness Require Import locales_helpers utils_sets.
From heap_lang Require Export lang tactics notation.

Close Scope Z. 
  
Lemma from_locale_from_lookup tp0 tp tid e :
  from_locale_from tp0 tp tid = Some e <-> (tp !! (tid - length tp0)%nat = Some e ∧ (length tp0 <= tid)%nat).
Proof.
  split.
  - revert tp0 tid. induction tp as [| e1 tp1 IH]; intros tp0 tid.
    { unfold from_locale. simpl. done. }
    unfold from_locale. simpl.
    destruct (decide (locale_of tp0 e1 = tid)).
    + intros ?; simplify_eq. rewrite /locale_of /= Nat.sub_diag.
      split; [done|lia].
    + intros [H Hlen]%IH. rewrite app_length /= in H.
      rewrite app_length /= in Hlen.
      destruct tid as [|tid]; first lia.
      assert (Heq1 : (length tp0 + 1 = S (length tp0))%nat) by lia.
      rewrite Heq1 in Hlen.
      assert (length tp0 ≤ tid)%nat by lia.
      assert (Heq : (S tid - length tp0)%nat = (S ((tid - (length tp0))))%nat) by lia.
      rewrite Heq /=. split.
      * rewrite -H. f_equal. lia.
      * transitivity tid; try lia. assumption.
  - revert tp0 tid. induction tp as [|e1 tp1 IH]; intros tp0 tid.
    { set_solver. }
    destruct (decide (tid = length tp0)) as [-> | Hneq].
    + rewrite Nat.sub_diag /=. intros  [? _]. simplify_eq.
      rewrite decide_True //.
    + intros [Hlk Hlen]. assert (length tp0 < tid)%nat as Hle by lia.
      simpl. rewrite decide_False //. apply IH. split.
      * assert (tid - length tp0 = S ((tid - 1) - length tp0))%nat as Heq by lia.
        rewrite Heq /= in Hlk. rewrite -Hlk app_length /=. f_equal; lia.
      * rewrite app_length /=. apply Nat.le_succ_l in Hle. rewrite Nat.add_comm //.
Qed.

  
Lemma from_locale_lookup tp tid e :
  from_locale tp tid = Some e <-> tp !! tid = Some e.
Proof.
  assert (from_locale tp tid = Some e <-> (tp !! tid = Some e ∧ 0 ≤ tid)%nat) as H; last first.
  { split; intros ?; apply H; eauto. split; [done|lia]. }
  unfold from_locale. replace (tid) with (tid - length (A := expr) [])%nat at 2;
    first apply from_locale_from_lookup. simpl; lia.
Qed.

Definition indexes {A} (xs : list A) := imap (λ i _, i) xs.

Lemma locales_of_list_from_indexes (es' es : list expr) :
  locales_of_list_from es' es = imap (λ i _, length es' + i)%nat es.
Proof.
  revert es'. induction es; [done|]; intros es'.
  rewrite locales_of_list_from_cons=> /=. rewrite /locale_of.
  f_equiv; [lia|]. rewrite IHes. apply imap_ext.
  intros x ? Hin. rewrite app_length=> /=. lia.
Qed.

Lemma locales_of_list_indexes (es : list expr) :
  locales_of_list es = indexes es.
Proof. apply locales_of_list_from_indexes. Qed.

Lemma locales_of_cfg_simpl l σ:
  locales_of_cfg (l, σ) = set_seq 0 (length l).
Proof. 
  rewrite /locales_of_cfg. f_equal. simpl.
  rewrite !locales_of_list_from_indexes. simpl.
  rewrite !imap_seq_0. rewrite !list_fmap_id.
  apply list_to_set_seq.
Qed. 

Lemma length_upd_middle {A: Type} (x y: A) l1 l2:
  length (l1 ++ x :: l2) = length (l1 ++ y :: l2).
Proof.  intros. rewrite !app_length. simpl. lia. Qed.

Lemma locale_step_sub c1 c2 τ
  (STEP: locale_step c1 (Some τ) c2):
  locales_of_cfg c1 ⊆ locales_of_cfg c2. 
Proof.
  inversion STEP. subst.
  
  rewrite !locales_of_cfg_simpl. 
  rewrite app_comm_cons. rewrite app_assoc. rewrite (app_length _ efs). 
  rewrite -!list_to_set_seq. rewrite seq_app.
  rewrite list_to_set_app.
  rewrite (length_upd_middle e1 e2). set_solver.
Qed. 

  (* TODO: move the lemmas below to appropriate places *)
  (* TODO: this is pretty much the definition of locales_of_list *)
  Lemma locales_of_list_from_locales t0 (es : list expr):
    locales_of_list_from t0 es = map (fun '(l, e) => locale_of l e) (prefixes_from t0 es).
  Proof using. set_solver. Qed. 

  (* TODO: this is pretty much the definition of locales_of_list *)
  Lemma locales_of_list_locales (es : list expr) :    
    locales_of_list es = map (fun '(l, e) => locale_of l e) (prefixes es).
  Proof using. set_solver. Qed. 

  (* TODO: move *)
  Lemma prefixes_from_ith_length (t0 t: list expr) pf i
    (ITH: prefixes_from t0 t !! i = Some pf):
    length pf.1 = length t0 + i.
  Proof using.
    clear -ITH. 
    generalize dependent t0. generalize dependent i. generalize dependent pf.
    induction t.
    { intros. simpl. destruct t0; done. }
    intros. destruct i.
    { simpl in ITH. inversion ITH. subst. simpl. lia. }
    simpl in ITH. apply IHt in ITH.
    rewrite length_app /= in ITH. lia.
  Qed.

  Lemma prefixes_ith_length (t: list expr) pf i
    (ITH: prefixes t !! i = Some pf):
    length pf.1 = i. 
  Proof using.
    apply prefixes_from_ith_length in ITH. by rewrite ITH.
  Qed.

  Lemma from_locale_from_locale_of t0 t1 t2 e:
    from_locale_from t0 (t1 ++ e :: t2) (locale_of (t0 ++ t1) e) = Some e.
  Proof using.
    apply from_locale_from_lookup.
    rewrite /locale_of. rewrite length_app. simpl.
    split; [| lia].
    rewrite Nat.add_sub'. by apply list_lookup_middle.
  Qed.

  (* TODO: find existing *)
  Lemma locales_equiv_from_of_list_from (tp1 tp2: list expr) tp01 tp02:
    locales_equiv_from tp01 tp02 tp1 tp2 <-> locales_of_list_from tp01 tp1 = locales_of_list_from tp02 tp2.
  Proof using.
    rewrite !locales_of_list_from_locales.    
    generalize dependent tp2. generalize dependent tp01. generalize dependent tp02. 
    induction tp1.
    { intros. simpl.
      split; intros EQUIV.
      - destruct tp2; inversion EQUIV. done.
      - destruct tp2; [| done]. done. }
    intros. simpl. split.
    - intros EQUIV. inversion EQUIV; subst.
      simpl. destruct y.
      destruct tp2; [done| ].
      simpl in H1. inversion H1. subst.
      f_equal; [done| ].
      by apply IHtp1.
    - intros EQ. destruct tp2; [done| ].
      simpl in EQ. inversion EQ.
      simpl. econstructor; try done.
      eapply IHtp1; eauto.
  Qed.

  (* TODO: find existing *)
  Lemma locales_equiv_of_list (tp1 tp2: list expr):
    locales_equiv tp1 tp2 <-> locales_of_list tp1 = locales_of_list tp2.
  Proof using. apply locales_equiv_from_of_list_from. Qed.

  Lemma locales_of_cfg_equiv tp1 tp2 σ1 σ2
    (EQUIV: locales_equiv tp1 tp2):
    locales_of_cfg (tp1, σ1) = locales_of_cfg (tp2, σ2).
  Proof using.
    rewrite /locales_of_cfg. simpl.
    apply locales_equiv_of_list in EQUIV. by rewrite EQUIV.
  Qed.

  Lemma locales_of_cfg_ext tp1 ef σ:
    locales_of_cfg (tp1 ++ [ef], σ) = locales_of_cfg (tp1, σ) ∪ {[ locale_of tp1 ef ]}.
  Proof using.
    rewrite /locales_of_cfg. simpl.
    rewrite locales_of_list_locales.
    rewrite prefixes_from_app map_app. simpl.
    rewrite list_to_set_app_L. set_solver.
  Qed. 

  Lemma step_fork_locales_equiv c1 c2
    (LOCALES_EQUIV: locales_equiv c1.1 c2.1):
  step_fork c1 c2 = None.
  Proof using.
    rewrite /step_fork.
    destruct c1, c2.
    erewrite (locales_of_cfg_equiv l); eauto.
    simpl. apply gset_pick_None.
    apply difference_diag_L.
  Qed.

  Lemma step_fork_fork tp1 tp2 ef σ1 σ2
    (EQUIV: locales_equiv tp1 tp2):
    step_fork (tp1, σ1) (tp2 ++ [ef], σ2) = Some (locale_of tp1 ef).
  Proof using.
    rewrite /step_fork.
    rewrite locales_of_cfg_ext. rewrite difference_union_distr_l_L.
    erewrite (locales_of_cfg_equiv tp1); [| done].
    erewrite difference_diag_L.
    rewrite difference_disjoint_L.
    2: { apply disjoint_singleton_l.
         rewrite locales_of_cfg_simpl. rewrite /locale_of.
         intros ?%elem_of_set_seq. simpl in H. lia. }
    rewrite union_empty_l_L. simpl. rewrite gset_pick_singleton.
    f_equal. rewrite /locale_of. apply Forall2_length in EQUIV.
    rewrite !prefixes_from_length in EQUIV. done.
  Qed.

  Lemma step_fork_hl t1 t2 e e' efs σ σ'
    (c := (t1 ++ e :: t2, σ))
    (c' := (t1 ++ e' :: t2 ++ efs, σ'))
    (STEP: locale_step c (Some (locale_of t1 e)) c'):
    step_fork c c' = None /\ efs = [] \/ exists ef, efs = [ef] /\ step_fork c c' = Some (locale_of c.1 ef).
  Proof using.
    inversion STEP; subst. subst c c'.
    rewrite /locale_of in H.
    inversion H0. subst. 
    assert (t0 = t1 /\ e1 = e /\ t3 = t2 /\ e2 = e' /\ efs0 = efs) as (-> & -> & -> & -> & ->). 
    { by list_simplifier. }
    simpl in H3. clear H H0 H4 H1.
    inversion H3. subst. simpl in *.
    inversion H1; subst.
    all: try by (left; split; [| reflexivity];
                 apply step_fork_locales_equiv; rewrite app_nil_r;
                 apply locales_equiv_middle). 
    right. eexists. split; eauto.
    rewrite app_comm_cons. rewrite app_assoc. 
    rewrite step_fork_fork; [done| ].
    apply locales_equiv_middle. done.
  Qed.

Lemma locale_step_step_fork_exact c1 c2 τ
  (STEP: locale_step c1 (Some τ) c2):
  locales_of_cfg c2 = locales_of_cfg c1 ∪ from_option singleton ∅ (step_fork c1 c2).
Proof using.
  inversion STEP. subst.
  eapply step_fork_hl in STEP.
  destruct STEP as [[-> ->] | (? & -> & ->)].
  - rewrite app_nil_r. simpl.
    rewrite union_empty_r_L. apply locales_of_cfg_equiv.
    by apply locales_equiv_middle.
  - simpl. rewrite -locales_of_cfg_ext.
    apply locales_of_cfg_equiv.
    rewrite -app_assoc. rewrite -app_comm_cons.   
    by apply locales_equiv_middle.
Qed.

Lemma step_fork_difference c1 c2 τ
  (SF: step_fork c1 c2 = Some τ):
  τ ∈ locales_of_cfg c2 ∖ locales_of_cfg c1.
Proof using.
  rewrite /step_fork in SF. apply gset_pick_Some in SF. set_solver.
Qed.

Lemma locale_step_fresh_exact c1 c2 τ τ'
  (STEP: locale_step c1 (Some τ) c2)
  (FRESH: τ' ∈ locales_of_cfg c2 ∖ locales_of_cfg c1):
  locales_of_cfg c2 = locales_of_cfg c1 ∪ {[ τ' ]} /\ τ' ∉ locales_of_cfg c1.
Proof using.
  erewrite locale_step_step_fork_exact; eauto.
  inversion STEP. subst. apply step_fork_hl in STEP.
  destruct STEP as [[-> ->] | (? & -> & ->)].
  - rewrite app_nil_r in FRESH.
    erewrite locales_of_cfg_equiv in FRESH.
    { erewrite difference_diag_L in FRESH. set_solver. }
    by apply locales_equiv_middle.
  - simpl. revert FRESH. 
    rewrite app_comm_cons app_assoc. 
    rewrite locales_of_cfg_ext. 
    rewrite difference_union_distr_l_L. 
    erewrite locales_of_cfg_equiv.
    1: erewrite difference_diag_L.
    2: { by apply locales_equiv_middle. }
    rewrite union_empty_l_L. intros [->%elem_of_singleton ?]%elem_of_difference.
    split; auto.
    do 2 f_equal.
    rewrite /locale_of. rewrite !length_app. simpl. lia.
Qed.

Lemma locale_step_fork_Some c1 τ c2 τ'
  (STEP: locale_step c1 (Some τ) c2)
  (FORK: step_fork c1 c2 = Some τ'):
  locales_of_cfg c2 = locales_of_cfg c1 ∪ {[τ']} ∧ τ' ∉ locales_of_cfg c1.
Proof using.
  apply gset_pick_Some in FORK.
  eapply locale_step_fresh_exact in FORK; eauto.
Qed.
