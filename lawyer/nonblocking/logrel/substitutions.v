From fairness Require Import utils. 
From heap_lang Require Import lang heap_lang_defs tactics. 

Definition subst_env (vs: gmap string val) (e: expr) := 
  map_fold subst e vs.

Lemma subst_env_var x vs:
  subst_env vs (Var x) = from_option Val (Var x) (vs !! x).
Proof using.
  rewrite /subst_env.
  
  set (P := fun (e: expr) (mp: gmap string val) =>
              e = from_option Val (Var x) (mp !! x)).
  enough (P (map_fold subst (Var x) vs) vs).
  { done. }
  
  apply map_fold_weak_ind; clear vs. 
  { done. }
  subst P. simpl. intros s v vs e NIN ->.
  rewrite insert_union_singleton_l. rewrite lookup_union.
  rewrite lookup_map_singleton.
  
  destruct decide as [-> | NEQ]. 
  { simpl. rewrite NIN. simpl. by rewrite decide_True. }
  rewrite option_union_left_id.
  destruct (vs !! x) eqn:XTH.
  - simpl. done.
  - simpl. by rewrite decide_False.
Qed.

Lemma subst_env_arg3
  (F: expr -> expr -> expr -> expr)
  (DISTR: forall e1 e2 e3 s v, subst s v (F e1 e2 e3) = F (subst s v e1) (subst s v e2) (subst s v e3)):
  forall e1 e2 e3 vs, subst_env vs (F e1 e2 e3) = F (subst_env vs e1) (subst_env vs e2) (subst_env vs e3).
Proof using.
  intros. rewrite /subst_env.
  pattern vs. apply map_first_key_ind. 
  { intros. by rewrite !map_fold_empty. }
  intros s v m NIN FKEY IH.
  rewrite !map_fold_insert_first_key; auto.
  by rewrite IH.
Qed.

Lemma subst_env_arg2 (F: expr -> expr -> expr)
  (DISTR: forall e1 e2 s v, subst s v (F e1 e2) = F (subst s v e1) (subst s v e2)):
  forall e1 e2 vs, subst_env vs (F e1 e2) = F (subst_env vs e1) (subst_env vs e2).
Proof using.
  intros. rewrite /subst_env.
  pattern vs. apply map_first_key_ind. 
  { intros. by rewrite !map_fold_empty. }
  intros s v m NIN FKEY IH.
  rewrite !map_fold_insert_first_key; auto.
  by rewrite IH.
Qed.

Lemma subst_env_arg1 (F: expr -> expr)
  (DISTR: forall e1 s v, subst s v (F e1) = F (subst s v e1)):
  forall e1 vs, subst_env vs (F e1) = F (subst_env vs e1).
Proof using.
  intros. rewrite /subst_env.
  pattern vs. apply map_first_key_ind. 
  { intros. by rewrite !map_fold_empty. }
  intros s v m NIN FKEY IH.
  rewrite !map_fold_insert_first_key; auto.
  by rewrite IH.
Qed.

Definition rm_binder (b: binder) (vs: gmap string val) :=
  match b with 
  | BNamed s => delete s vs
  | BAnon => vs
  end.

Lemma subst_env_empty e: subst_env ∅ e = e.
Proof using. done. Qed.

Lemma subst_env_singleton s v e: subst_env {[ s := v ]} e = subst s v e.
Proof using.
  rewrite /subst_env. by rewrite map_fold_singleton.
Qed.

Lemma rm_binder_empty b: rm_binder b ∅ = ∅.
Proof using. destruct b; set_solver. Qed.

Ltac gd x := generalize dependent x. 

Lemma subst_comm s1 v1 s2 v2 e
  (NEQ: s1 ≠ s2):
  subst s1 v1 (subst s2 v2 e) = subst s2 v2 (subst s1 v1 e).
Proof using.
  gd s1. gd v1. gd s2. gd v2. 
  induction e; intros; simpl; try done.
  all: try by (f_equal; eauto).
  - destruct decide, decide; subst; simpl; try done.
    + by rewrite decide_True.
    + by rewrite decide_True.
    + by rewrite !decide_False.
  - destruct decide, decide; subst; simpl; try done.
    f_equal. eauto.
Qed.

Lemma subst_env_insert s v vs e
  (FRESH: s ∉ dom vs):
  subst_env (<[ s := v ]> vs) e = subst s v (subst_env vs e).
Proof using.
  rewrite /subst_env.
  eapply map_fold_insert_L.
  2: by apply not_elem_of_dom.
  intros. by apply subst_comm.
Qed.

Lemma subst_env_insert' s v vs e
  (FRESH: s ∉ dom vs):
  subst_env (<[ s := v ]> vs) e = subst_env vs (subst s v e). 
Proof using.
  rewrite subst_env_insert; [| done].
  (* TODO: extract lemma *)
  gd e. revert FRESH. pattern vs. apply map_first_key_ind; clear vs. 
  { intros. by rewrite !subst_env_empty. }
  intros. rewrite subst_env_insert; [| by apply not_elem_of_dom].
  rewrite dom_insert_L in FRESH. 
  apply not_elem_of_union in FRESH as [?%not_elem_of_singleton ?].
  rewrite subst_comm; [| done].
  rewrite H1; [| done].  
  rewrite -subst_env_insert; [| by apply not_elem_of_dom]. 
  done.
Qed.

Lemma rm_binder_insert_comm b s v vs
  (NEQ: b ≠ BNamed s):
  rm_binder b (<[ s := v ]> vs) = <[ s := v ]> (rm_binder b vs).
Proof using.
  destruct b as [| sb]; simpl. 
  { done. }
  apply map_eq. intros s'.
  Set Printing Coercions.
  assert (sb ≠ s).
  { congruence. }
  destruct (decide (s' = s)) as [-> | NEQ'].
  { rewrite lookup_delete_ne; [| done].
    by rewrite !lookup_insert. }
  rewrite lookup_insert_ne; [| done].
  destruct (decide (sb = s')) as [-> | NEQ''].
  { by rewrite !lookup_delete. }
  do 2 (rewrite lookup_delete_ne; [| done]).
  rewrite lookup_insert_ne; done.
Qed.

Lemma dom_rm_binder b vs:
  dom (rm_binder b vs) = dom vs ∖ match b with | BNamed s => {[ s ]} | _ => ∅ end.
Proof using.
  rewrite /rm_binder. destruct b; set_solver.
Qed.

Lemma rm_binder_subseteq s vs:
  rm_binder s vs ⊆ vs.
Proof using.
  destruct s; simpl; try set_solver.
  apply delete_subseteq.
Qed. 
    
Lemma subst_env_rec (b x: binder) (f: expr) vs:
  let vs' := rm_binder b $ rm_binder x vs in
  subst_env vs (Rec b x f) = Rec b x (subst_env vs' f).
Proof using.
  simpl. generalize dependent f. 
  pattern vs. apply map_first_key_ind; clear vs. 
  { intros. by rewrite !rm_binder_empty !subst_env_empty. }
  intros s v vs NIN FKEY IH f.
  rewrite subst_env_insert; [| by apply not_elem_of_dom].
  rewrite IH. simpl. f_equal.
  destruct decide.
  - destruct a. 
    rewrite -subst_env_insert.
    2: { rewrite !dom_rm_binder.
         apply not_elem_of_dom in NIN.
         destruct x, b; set_solver. }
    rewrite rm_binder_insert_comm; [| done].
    f_equal. rewrite rm_binder_insert_comm; [| done].
    done. 
  - apply Classical_Prop.not_and_or in n.
    destruct (decide (BNamed s = x)) as [<- | ?]; simpl. 
    + by rewrite delete_insert_delete.
    + rewrite rm_binder_insert_comm; [| done].
      destruct n as [<-%NNP_P | <-%NNP_P]; simpl; try done.
      by rewrite delete_insert_delete.
Qed.

Lemma subst_subst_ignored s v v' e:
  subst s v' (subst s v e) = subst s v e.
Proof using.
  gd v. gd v'. induction e; simpl; try done.
  all: try by (intros; f_equal; eauto).
  - intros. destruct decide; try done. simpl.
    by rewrite decide_False.
  - destruct decide; try done.
    intros. f_equal. eauto.
Qed.

