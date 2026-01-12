From iris.proofmode Require Import proofmode coq_tactics.
From heap_lang Require Import heap_lang_defs tactics. 


  Lemma bin_op_eval_inv op a b r
    (EVAL: bin_op_eval op a b = Some r):
    (op = EqOp /\ vals_compare_safe a b /\ r = LitV $ LitBool $ bool_decide (a = b)) \/
    (exists na nb vr, a = LitV $ LitInt na /\ b = LitV $ LitInt nb /\ r = LitV vr /\
                 ((exists i, vr = LitInt i) \/ (exists b, vr = LitBool b)) /\
                 bin_op_eval_int op na nb = Some vr) \/
    (exists ba bb br, a = LitV $ LitBool ba /\ b = LitV $ LitBool bb /\ r = LitV $ LitBool br /\
                 bin_op_eval_bool op ba bb = Some $ LitBool br) \/
    (exists la ob, a = LitV $ LitLoc la /\ b = LitV (LitInt ob) /\
              op = OffsetOp /\
              r = LitV (LitLoc (la +ₗ ob))).
  Proof using.
    rewrite /bin_op_eval in EVAL.
    destruct decide.
    { subst. destruct decide; [| done].
      left. inversion EVAL. subst. eauto. }
    destruct a; try done.
    destruct l; try done.
    all: destruct b; (try done); destruct l; try done.
    - apply fmap_Some in EVAL as (?&?&->).
      right. left. do 3 eexists. repeat split; eauto.
      destruct op; simpl in H; set_solver.      
    - apply fmap_Some in EVAL as (?&?&->).
      destruct op; simpl in H; set_solver.
    - destruct l0; try done. destruct op; try done. 
      inversion EVAL. subst. 
      repeat right. do 2 eexists. eauto.
  Qed.

  Ltac inv_binop_eval H :=
    apply bin_op_eval_inv in H as
        [(-> & ? & ->) | [(?&?&?&->&->&->&[(?&->) | (?&->)]&?) | [(?&?&?&->&->&->&?) | (?&?&->&->&->&->)]]].

  Lemma un_op_eval_inv op v r
    (EVAL: un_op_eval op v = Some r):
    (op = NegOp /\ exists b, v = LitV $ LitBool b /\ r = LitV $ LitBool $ negb b) \/
    (op = NegOp /\ exists n, v = LitV $ LitInt n /\ r = LitV $ LitInt $ (Z.lnot n)) \/ 
    (op = MinusUnOp /\ exists n, v = LitV $ LitInt n /\ r = LitV $ LitInt (- n)). 
  Proof using.
    rewrite /un_op_eval in EVAL.
    destruct op, v; try congruence.
    all: destruct l; try congruence; inversion EVAL; subst.
    all: set_solver.
  Qed.

  Ltac inv_unop_eval H :=
    apply un_op_eval_inv in H as
        [(-> & ? & -> & ->) | [(-> & ? & -> & ->)| (-> & ? & -> & ->)]]. 
