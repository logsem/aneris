From trillium.fairness Require Import locales_helpers utils_sets.
From trillium.fairness.heap_lang Require Export lang tactics notation.

  
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

Lemma locale_step_fresh_exact c1 c2 τ τ'
  (STEP: locale_step c1 (Some τ) c2)
  (FRESH: τ' ∈ locales_of_cfg c2 ∖ locales_of_cfg c1):
  locales_of_cfg c2 = locales_of_cfg c1 ∪ {[ τ' ]} /\ τ' ∉ locales_of_cfg c1.
Proof.
  inversion STEP. subst.
  revert FRESH.
  
  rewrite !locales_of_cfg_simpl. 
  rewrite app_comm_cons. rewrite app_assoc. rewrite app_length.
  rewrite -!list_to_set_seq. rewrite seq_app. simpl. 
  rewrite list_to_set_app_L. rewrite !list_to_set_seq.
  
  rewrite (length_upd_middle e2 e1). remember (length (t1 ++ e1 :: t2)) as N.
  rewrite -HeqN. remember (set_seq 0 N) as D. 
  
  rewrite difference_union_distr_l_L. rewrite subseteq_empty_difference; [| done].
  rewrite union_empty_l. intros [DOM2 NDOM1]%elem_of_difference.
  split; [| done].
  f_equal.
  
  assert (¬ (efs = [])) as FORK.
  { intros NOFORK. inversion H3. subst. inversion H1; subst; done. }
  inversion H3. subst. inversion H1; subst; try done.
  simpl in DOM2. rewrite union_empty_r in DOM2. apply elem_of_singleton in DOM2.
  simpl. set_solver.
Qed.            

Lemma locale_step_fork_Some c1 τ c2 τ'
  (STEP: locale_step c1 (Some τ) c2)
  (FORK: step_fork c1 c2 = Some τ'):
  locales_of_cfg c2 = locales_of_cfg c1 ∪ {[τ']} ∧ τ' ∉ locales_of_cfg c1.
Proof using.
  apply gset_pick_Some in FORK.
  eapply locale_step_fresh_exact in FORK; eauto.
Qed.
