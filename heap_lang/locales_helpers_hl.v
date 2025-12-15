From fairness Require Import locales_helpers utils.
From heap_lang Require Export lang tactics notation.
From trillium.traces Require Import exec_traces trace_lookup.
From fairness Require Import utils_traces.

Close Scope Z_scope. 
  
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
    + intros [H Hlen]%IH. rewrite length_app /= in H.
      rewrite length_app /= in Hlen.
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
        rewrite Heq /= in Hlk. rewrite -Hlk length_app /=. f_equal; lia.
      * rewrite length_app /=. apply Nat.le_succ_l in Hle. rewrite Nat.add_comm //.
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
  intros x ? Hin. rewrite length_app=> /=. lia.
Qed.

Lemma locales_of_list_indexes (es : list expr) :
  locales_of_list es = indexes es.
Proof. apply locales_of_list_from_indexes. Qed.

Lemma locales_of_list_from_app (tp0 tp1 tp2: list expr):
  locales_of_list_from tp0 (tp1 ++ tp2) =
  locales_of_list_from tp0 tp1 ++
  locales_of_list_from (tp0 ++ tp1) tp2.
Proof using.
  rewrite /locales_of_list_from.
  rewrite !prefixes_from_app.
  by rewrite !fmap_app.
Qed.

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
Proof.  intros. rewrite !length_app. simpl. lia. Qed.

Lemma locale_step_sub c1 c2 τ
  (STEP: locale_step c1 (Some τ) c2):
  locales_of_cfg c1 ⊆ locales_of_cfg c2. 
Proof.
  inversion STEP. subst.
  
  rewrite !locales_of_cfg_simpl. 
  rewrite app_comm_cons. rewrite app_assoc. rewrite (length_app _ efs). 
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


Lemma thread_pool_split (tp: list expr) (τ: locale heap_lang):
  exists tp1 tp2 tp', tp = tp1 ++ tp' ++ tp2 /\ (tp' = [] \/ exists e, tp' = [e] /\ τ = locale_of tp1 e) /\
    τ ∉ locales_of_list_from [] tp1 /\ τ ∉ locales_of_list_from (tp1 ++ tp') tp2.
Proof using.
  destruct (decide (τ ∈ (locales_of_list tp))).
  2: { exists tp, [], []. split; [by list_simplifier| ].
       split.
       { tauto. }
       split; auto. rewrite app_nil_r. simpl. set_solver. }
  apply elem_of_list_In, In_nth_error in e. destruct e as (i & ITH).
  rewrite locales_of_list_locales in ITH.
  rewrite nth_error_map in ITH.
  destruct nth_error as [[??]|] eqn:ITH'; [| done]. simpl in ITH.
  inversion ITH. clear ITH. 
  rewrite nth_error_lookup in ITH'.
  pose proof ITH' as ITH%prefixes_lookup_orig.
  pose proof ITH as (tp1 & tp2 & EQ & LEN1)%elem_of_list_split_length.
  apply prefixes_ith_length in ITH'. simpl in ITH'.
  exists tp1, tp2, [e]. split; [done| ]. split.
  { right. eexists. split; eauto.
    revert H0. rewrite /locale_of.
    congruence. }
  split.
  - intros IN. rewrite /locale_of locales_of_list_from_indexes /= in IN.
    apply elem_of_lookup_imap in IN as (?&?&?&?).
    subst. apply lookup_lt_Some in H1. lia.
  - intros IN. rewrite /locale_of locales_of_list_from_indexes /= in IN.
    apply elem_of_lookup_imap in IN as (?&?&?&?).
    subst. rewrite length_app /= in H. 
    apply lookup_lt_Some in H1. lia.
Qed.


(* TODO: use in other places *)
Lemma elem_of_locales_of_list_from_from_locale_from tp0 τ tp:
  τ ∈ locales_of_list_from tp0 tp <-> exists e, from_locale_from tp0 tp τ = Some e.
Proof using.
  rewrite locales_of_list_from_locales.
  rewrite elem_of_list_In in_map_iff.
  rewrite ex_prod. rewrite ex2_comm.
  apply exist_proper. intros e.
  rewrite from_locale_from_lookup.
  rewrite /locale_of.
  setoid_rewrite <- elem_of_list_In.
  setoid_rewrite elem_of_list_lookup.  
  split.
  - intros (pf & <- & (i & IN)).
    pose proof IN as ?%prefixes_lookup_orig.
    pose proof IN as ?%prefixes_from_ith_length. simpl in *.
    split; [| lia]. rewrite -H. f_equal. lia.
  - intros (IN & LEN).
    eexists. split.
    2: { eexists. eapply prefixes_from_lookup; eauto. }
    rewrite length_app.
    apply lookup_lt_Some in IN. simpl in *. 
    rewrite firstn_length_le; lia.
Qed.


Lemma from_locale_from_elem_of tp0 tp τ e
  (IN: from_locale_from tp0 tp τ = Some e):
  e ∈ tp.
Proof using.
  apply from_locale_from_lookup in IN.
  destruct IN as [IN _].
  eapply elem_of_list_lookup; eauto.
Qed.


Lemma from_locale_from_app_Some tp0 tp1 tp2 τ e:
  from_locale_from tp0 (tp1 ++ tp2) τ = Some e <->
  from_locale_from tp0 tp1 τ = Some e \/ from_locale_from (tp0 ++ tp1) tp2 τ = Some e.
Proof using.
  clear. 
  rewrite !from_locale_from_lookup.
  rewrite lookup_app. rewrite !length_app.
  destruct (tp1 !! (τ - length tp0)) eqn:L1.
  - split; try tauto. intros [? | [EQ2 LEN2]]; [done| ].
    apply lookup_lt_Some in L1, EQ2. lia.
  - etrans.
    2: { rewrite Morphisms_Prop.or_iff_morphism; [..| reflexivity].
         2: apply iff_False_helper; set_solver. 
         reflexivity. }
    rewrite False_or. rewrite Nat.sub_add_distr.
    apply iff_and_pre. intros ?%lookup_lt_Some.
    apply lookup_ge_None in L1. lia.
Qed.

Lemma from_locale_from_Some_app' tp0 tp tp' ζ e :
  from_locale_from (tp0 ++ tp) tp' ζ = Some e ->
  from_locale_from tp0 (tp ++ tp') ζ = Some e.
Proof.
  intros EQ. rewrite from_locale_from_app_Some. eauto. 
Qed.


(* TODO: move, find existing, generalize? *)
Lemma locale_step_other_same c1 oτ c2 τ' e'
  (EXPR: from_locale c1.1 τ' = Some e')
  (STEP: locale_step c1 oτ c2)
  (OTHER: oτ ≠ Some τ'):
  from_locale c2.1 τ' = Some e'.
Proof using.
  rewrite -EXPR. simpl.
  inversion STEP; subst; simpl in *.
  2: { done. }
  apply from_locale_from_app_Some in EXPR as [IN1 | IN2].
  { rewrite /from_locale. repeat erewrite from_locale_from_Some_app; eauto. }
  simpl in IN2. rewrite decide_False in IN2; [| set_solver].
  rewrite /from_locale.
  symmetry. rewrite (app_assoc _ ([_])).
  erewrite from_locale_from_Some_app'; eauto.
  symmetry. apply from_locale_from_Some_app'. simpl.
  rewrite decide_False; [| set_solver].
  apply from_locale_from_Some_app.
  apply from_locale_from_lookup in IN2 as (?&?). 
  eapply from_locale_from_lookup. split.
  - rewrite -H. rewrite !length_app /=. done.
  - etrans; [| apply H0]. rewrite !length_app /=. done.
Qed.    


Lemma prefixes_simpl {A B: Type} (es tp: list expr) (P: nat -> B -> A) (s: B): 
  (λ '(tnew, e) (_ : val), P (locale_of tnew e) s) <$> prefixes_from es (drop (length es) tp) = map (fun i _ => P i s) (seq (length es) (length tp - length es)). 
Proof using.
  destruct (decide (length es < length tp)).
  2: { rewrite skipn_all2; [| lia].
       replace (length tp - length es) with 0.
       { done. }
       simpl in n. lia. }
  
  remember (drop (length es) tp) as tp'.
  replace (length tp - length es) with (length tp').
  2: { subst. rewrite length_drop. lia. }
  clear Heqtp'. simpl.
  
  clear l. revert es. 
  
  induction tp'.
  { simpl. done. }
  
  intros. simpl.
  f_equal.
  pose proof (IHtp' (es ++ [a])).
  replace (S (length es)) with (length (es ++ [a])).
  2: { simpl. rewrite length_app. simpl. lia. } 
  rewrite -H. simpl. done.
Qed.

Lemma indexes_seq {A: Type} (l: list A):
  indexes l = seq 0 (length l).
Proof using.
  rewrite /indexes. rewrite imap_seq_0. by rewrite list_fmap_id.
Qed.


(* TODO: ? generalize *)
Lemma enabled_disabled_step_between (etr: extrace heap_lang) i j ci cj τ
  (ITH: etr S!! i = Some ci)
  (JTH: etr S!! j = Some cj)
  (LE: i <= j)
  (ENi: locale_enabled τ ci)
  (DISj: ¬ locale_enabled τ cj)
  (VALID: extrace_valid etr):
  exists k, i <= k < j /\ etr L!! k = Some $ Some τ.
Proof using.
  pose proof @steps_not_kept_step_between as KEPT.
  apply extrace_valid_alt in VALID. 
  ospecialize * (KEPT _ _ _ _ VALID _ (locale_enabled τ) (fun τ' => τ' ≠ Some τ)).
  4: by apply LE.
  all: eauto.
  { red. intros.
    destruct Pst as (?&E&?).
    pose proof E as E'. 
    erewrite <- locale_step_other_same in E; eauto.
    red. eexists. split; eauto. congruence. }
  destruct KEPT as (?&?&?&?&?).
  eexists. split; eauto. rewrite H0.
  apply dec_stable in H1. congruence.
Qed.

Lemma locale_step_val_preserved c1 oτ c2 τv v
  (VAL: from_locale c1.1 τv = Some (of_val v))
  (STEP: locale_step c1 oτ c2):
  from_locale c2.1 τv = Some (of_val v).
Proof using.
  destruct (decide (oτ = Some τv)) as [-> | ].
  2: { erewrite locale_step_other_same; eauto. }
  inversion STEP. subst. simpl in *.
  rewrite /from_locale from_locale_from_locale_of in VAL.
  inversion VAL. subst e1.
  inversion H3. subst.
  apply ectx_language.val_head_stuck in H1.
  eapply ectx_language.fill_not_val in H1.
  by erewrite <- H in H1.
Qed.

Lemma val_preserved_trace etr v i ci τv j 
  (VALID: extrace_valid etr)
  (ITH: etr S!! i = Some ci)
  (VAL: from_locale ci.1 τv = Some (of_val v))
  (LE: i <= j):
  from_option (fun cj => from_locale cj.1 τv = Some (of_val v)) True (etr S!! j).
Proof using.
  apply Nat.le_sum in LE as [d ->]. induction d.
  { rewrite Nat.add_0_r. by rewrite ITH. }
  destruct (etr S!! (i + S d)) eqn:JTH; [| done]. simpl.
  rewrite Nat.add_succ_r in JTH.
  pose proof JTH as [[? JTH'] [? JTHl]]%mk_is_Some%next_state_lookup.
  rewrite JTH' /= in IHd.
  eapply locale_step_val_preserved; eauto.
  eapply trace_valid_steps''; eauto. 
  { by apply extrace_valid_alt. }
  rewrite -JTH. f_equal. lia.
Qed.

Lemma from_locale_trace etr i ci τ j
  (VALID: extrace_valid etr)
  (ITH: etr S!! i = Some ci)
  (VAL: is_Some (from_locale ci.1 τ))
  (LE: i <= j):
  from_option (fun cj => is_Some (from_locale cj.1 τ)) True (etr S!! j).
Proof using.
  apply Nat.le_sum in LE as [d ->]. induction d.
  { rewrite Nat.add_0_r. by rewrite ITH. }
  destruct (etr S!! (i + S d)) eqn:JTH; [| done]. simpl.
  rewrite Nat.add_succ_r in JTH.
  pose proof JTH as [[[??] JTH'] [? JTHl]]%mk_is_Some%next_state_lookup.
  rewrite JTH' /= in IHd.
  eapply from_locale_step; eauto. 
  eapply trace_valid_steps''; eauto. 
  { by apply extrace_valid_alt. }
  erewrite <- surjective_pairing, <-JTH. f_equal. lia.
Qed.

