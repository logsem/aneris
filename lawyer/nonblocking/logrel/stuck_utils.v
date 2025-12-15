From iris.proofmode Require Import proofmode coq_tactics.
From fairness Require Import utils.
From lawyer.nonblocking.logrel Require Export substitutions.
From lawyer.nonblocking Require Export pwp. 
From heap_lang Require Import lang. 

Lemma srav_helper (e: expr)
  (NO_FILL_ITEM: ¬ exists i e', e = fill_item i e' /\ to_val e' = None):
  sub_redexes_are_values e.
Proof using.
  red. simpl. intros. 
  rewrite /fill in H.
  rewrite foldl_foldr_rev in H. simpl in H.
  destruct (rev K) eqn:RR.
  { eapply (@f_equal _ _ length) in RR.
    rewrite length_rev /= in RR.
    destruct K; simpl in *; done. }
  
  clear RR. simpl in H.
  rewrite -(rev_involutive l) in H. rewrite -foldl_foldr_rev in H.
  replace (foldl (flip fill_item) e' (rev l)) with (fill (rev l) e') in H by done.
  
  destruct NO_FILL_ITEM. do 2 eexists. split; eauto.
  destruct (to_val (fill _ _)) eqn:VV; [| done].
  apply to_val_fill_some in VV as (?&->). done. 
Qed.

Ltac solve_no_fill_item := 
  intros (i&?&FILL&NVAL);
  destruct i; simpl in FILL; try congruence;
  inversion FILL; subst; done.

Ltac solve_head_stuck := 
  intros; red; simpl; split; [done| ];
  red; simpl; intros ??? STEP;
  inversion STEP; subst; (congruence || by eauto || set_solver).

Ltac solve_stuck_case :=
  iApply ectx_lifting.wp_lift_pure_head_stuck;
  [done | apply srav_helper; solve_no_fill_item | solve_head_stuck ..].

Ltac try_solve_val_dec v rtac :=
  destruct v; (try by (right; rtac)). 

Ltac solve_val_dec v rtac :=
  destruct v; (try by (right; rtac)); [];
  left; eauto. 
  
Global Instance is_RecV_dec f: Decision (exists b s e, f = RecV b s e).
Proof using. solve_val_dec f ltac:(by intros (?&?&?&?)). Qed.  
  
Global Instance is_InjLV_dec v: Decision (∃ v', v = InjLV v').
Proof using. solve_val_dec v ltac:(by intros (?&?)). Qed.  

Global Instance is_InjRV_dec v: Decision (∃ v', v = InjRV v').
Proof using. solve_val_dec v ltac:(by intros (?&?)). Qed.

Global Instance is_loc_dec v: Decision (exists l, v = LitV $ LitLoc l).
Proof using.
  try_solve_val_dec v ltac:(by intros (?&?)).
  solve_val_dec l ltac:(by intros (?&?)).
Qed.

Global Instance is_int_dec v: Decision (exists (n: Z), v = LitV $ LitInt n).
Proof using. 
  try_solve_val_dec v ltac:(by intros (?&?)).
  solve_val_dec l ltac:(by intros (?&?)).
Qed.

Global Instance is_bool_dec v: Decision (exists b, v = LitV $ LitBool b).
Proof using. 
  try_solve_val_dec v ltac:(by intros (?&?)).
  solve_val_dec l ltac:(by intros (?&?)).
Qed. 

Global Instance is_PairV_dec v: Decision (exists v1 v2, v = PairV v1 v2).
Proof using.
  solve_val_dec v ltac:(by intros (?&?&?)).
Qed.
