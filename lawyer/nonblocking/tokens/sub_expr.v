From iris.proofmode Require Import proofmode coq_tactics.
From iris.prelude Require Import options.
From heap_lang Require Import heap_lang_defs sswp_logic tactics locales_helpers_hl. 
From fairness Require Import locales_helpers.
From lawyer.nonblocking.logrel Require Import valid_client.
From lawyer.nonblocking Require Import trace_context.


Inductive is_sub_expr_expr_1 : expr -> expr -> Prop :=
  | ise1_rec f y e : is_sub_expr_expr_1 e (Rec f y e)
  (* | ise1_recV f y e : is_sub_expr_expr_1 e (Val $ RecV f y e) *)
  | ise1_app_l e1 e2 : is_sub_expr_expr_1 e1 (App e1 e2)
  | ise1_app_r e1 e2 : is_sub_expr_expr_1 e2 (App e1 e2)
  | ise1_unop op e : is_sub_expr_expr_1 e (UnOp op e)
  | ise1_binop_l op e1 e2 : is_sub_expr_expr_1 e1 (BinOp op e1 e2)
  | ise1_binop_r op e1 e2 : is_sub_expr_expr_1 e2 (BinOp op e1 e2)
  | ise1_if_l e0 e1 e2 : is_sub_expr_expr_1 e0 (If e0 e1 e2)
  | ise1_if_c e0 e1 e2 : is_sub_expr_expr_1 e1 (If e0 e1 e2)
  | ise1_if_r e0 e1 e2 : is_sub_expr_expr_1 e2 (If e0 e1 e2)
  | ise1_pair_l e1 e2 : is_sub_expr_expr_1 e1 (Pair e1 e2)
  | ise1_pair_r e1 e2 : is_sub_expr_expr_1 e2 (Pair e1 e2)
  | ise1_fst e : is_sub_expr_expr_1 e (Fst e)
  | ise1_snd e : is_sub_expr_expr_1 e (Snd e)
  | ise1_InjL e : is_sub_expr_expr_1 e (InjL e)
  | ise1_InjR e : is_sub_expr_expr_1 e (InjR e)
  | ise1_case_l e0 e1 e2 : is_sub_expr_expr_1 e0 (Case e0 e1 e2)
  | ise1_case_c e0 e1 e2 : is_sub_expr_expr_1 e1 (Case e0 e1 e2)
  | ise1_case_r e0 e1 e2 : is_sub_expr_expr_1 e2 (Case e0 e1 e2)
  | ise1_Fork e : is_sub_expr_expr_1 e (Fork e)
  | ise1_AllocN_l e1 e2 : is_sub_expr_expr_1 e1 (AllocN e1 e2)
  | ise1_AllocN_r e1 e2 : is_sub_expr_expr_1 e2 (AllocN e1 e2)
  | ise1_Free e : is_sub_expr_expr_1 e (Free e)
  | ise1_Load e : is_sub_expr_expr_1 e (Load e)
  | ise1_Store_l e1 e2 : is_sub_expr_expr_1 e1 (Store e1 e2)
  | ise1_Store_r e1 e2 : is_sub_expr_expr_1 e2 (Store e1 e2)
  | ise1_CmpXchg_l e0 e1 e2 : is_sub_expr_expr_1 e0 (CmpXchg e0 e1 e2)
  | ise1_CmpXchg_c e0 e1 e2 : is_sub_expr_expr_1 e1 (CmpXchg e0 e1 e2)
  | ise1_CmpXchg_r e0 e1 e2 : is_sub_expr_expr_1 e2 (CmpXchg e0 e1 e2)
  | ise1_FAA_l e1 e2 : is_sub_expr_expr_1 e1 (FAA e1 e2)
  | ise1_FAA_r e1 e2 : is_sub_expr_expr_1 e2 (FAA e1 e2)
  .

  Inductive is_sub_val_val_1 : val -> val -> Prop :=
    | isv1_pair_l v1 v2 : is_sub_val_val_1 v1 (PairV v1 v2)
    | isv1_pair_r v1 v2 : is_sub_val_val_1 v2 (PairV v1 v2)
    | isv1_inj_l v : is_sub_val_val_1 v (InjLV v)
    | isv1_inj_r v : is_sub_val_val_1 v (InjRV v)
  .

  (* Inductive is_sub_expr : expr -> expr -> Prop := *)
  (* | ise_refl e : is_sub_expr e e *)
  (* | ise_step e1 e2 e3 (ISE12: is_sub_expr_expr_1 e1 e2) (ISE23: is_sub_expr e2 e3) *)
  (*   : is_sub_expr e1 e3 *)
  (* | ise_expr_val e s f : is_sub_expr e (Val $ RecV s f e) *)
  (* | ise_val_val v1 v2 (VAL: is_sub_val v1 v2) : is_sub_expr (Val v1) (Val v2) *)
  (* with is_sub_val : val -> val -> Prop := *)
  (* | isv_refl v : is_sub_val v v *)
  (* | isv_step v1 v2 v3 (ISV12: is_sub_val_val_1 v1 v2) (ISV23: is_sub_val v2 v3) *)
  (*   : is_sub_val v1 v3 *)
  (* | isv_recv s f e1 e2 (EXPR: is_sub_expr e1 e2) : *)
  (*   is_sub_val (RecV s f e1) (RecV s f e2)  *)
  (* . *)

  (* Local Instance ise_refl_: Reflexive is_sub_expr. *)
  (* Proof using. red. constructor. Qed.  *)
  (* Local Instance isv_refl_: Reflexive is_sub_val. *)
  (* Proof using. red. constructor. Qed. *)

  (* TODO: move *)
  Lemma valid_client_fill_item e Ki
    (VALID: valid_client (fill_item Ki e)):
    valid_client e.
  Proof using. destruct Ki, e; simpl in *; tauto. Qed.

  (* TODO: move *)
  Lemma valid_client_fill e K
    (VALID: valid_client (fill K e)):
    valid_client e.
  Proof using.
    revert e VALID. pattern K. apply rev_ind; clear K. 
    { done. }
    intros.
    rewrite fill_app /= in VALID.
    apply valid_client_fill_item in VALID. set_solver.
  Qed.

  (* (* holds, but we only need this for token pwp and for arbitrary sub-exprs*) *)
  (* Theorem fundamental_ctx_val K (v: val) *)
  (*   (VALID: valid_client (fill K (Val v))): *)
  (*   ⊢ |~~| interp v. *)
  (* Proof using. *)
  (*   apply valid_client_fill in VALID. *)
  (*   apply fundamental in VALID. *)
  (*   rewrite /logrel in VALID. *)
  (*   iStartProof. *)
  (*   iPoseProof (VALID $! ∅ 0%nat with "[]") as "V". *)
  (*   { by iApply interp_env_nil. } *)
  (*   erewrite subst_env_empty. *)
  (*   rewrite /interp_expr. *)
  (*   by iApply wp_value_inv. *)
  (* Qed. *)

  (* this is what we need *)
  (* Theorem fundamental_ctx_val' (v: val) e *)
  (*   (VALIDe: valid_client e) *)
  (*   (SUB: is_sub_expr (Val v) e): *)
  (*   ⊢ |~~| interp v. *)
  (* Proof using. *)

  Definition is_sub_expr: expr -> expr -> Prop. Admitted.
  Definition is_sub_val: val -> val -> Prop. Admitted.

  Global Instance ise_PO: PartialOrder is_sub_expr. Admitted.
  Global Instance isv_PO: PartialOrder is_sub_val. Admitted.

  Global Instance ise_dec v e: Decision (is_sub_expr v e).
  Proof. Admitted. 

  From lawyer.nonblocking Require Import calls.

  Lemma is_sub_expr_fill e K:
    is_sub_expr e (fill K e).
  Proof. Admitted.

  (** if value doesn't belong to the sub-expression under the context,
      then it belongs to the context itself, which doesn't change *)
  (* can also assume head_step(e, e') *)
  Lemma is_sub_expr_in_ectx v K e e'
    (SUB: is_sub_expr v (fill K e))
    (NOT_IN: ¬ is_sub_expr v e):
    is_sub_expr v (fill K e').
  Proof. Admitted.

  Lemma head_step_sub_values e1 σ1 e2 σ2 efs
    (STEP: head_step e1 σ1 e2 σ2 efs):
    forall v, is_sub_expr (Val v) e2 -> 
         is_sub_expr (Val v) e1 \/ exists v2, e2 = Val v2 /\ is_sub_val v v2. 
  Proof using. Admitted.
      
  (* Lemma locale_step_sub_values K e1 tp σ1 e2 tp' σ2 efs *)
  (*   (c1 := (tp ++ (fill K e1) :: tp', σ1)) *)
  (*   (c2 := (tp ++ (fill K e2) :: tp' ++ efs, σ2)) *)
  (*   (STEP: head_step e1 σ1 e2 σ2 efs) *)
  (*   (** should be generalizable to forks, but we don't use it *) *)
  (*   (NOFORK: step_fork c1 c2 = None):  *)
  (*   forall v τ e2,  *)
  (*     from_locale c2.1 τ = Some e2 -> is_sub_expr (Val v) e2 -> *)
  (*     (exists e1, from_locale c1.1 τ = Some e1 /\ is_sub_expr (Val v) e1) \/ *)
  (*     exists v2, e2 = fill K (Val v2) /\ is_sub_val v v2.  *)
  (* Proof using. *)
  (*   intros * TTH SUB2. *)
  (*   (* pose proof STEP as HSTEP. *) *)
  (*   assert (locale_step c1 (Some $ locale_of tp (fill K e1)) c2) as LSTEP. *)
  (*   { subst c1 c2. econstructor; eauto. *)
  (*     econstructor; eauto. } *)
    
  (*   pose proof LSTEP as EQ%locale_step_step_fork_exact. *)
  (*   rewrite NOFORK /= union_empty_r_L in EQ. *)

  (*   subst c1 c2. simpl in *. subst. *)
  (*   rewrite set_eq in EQ. *)
  (*   ospecialize (EQ _). apply proj1 in EQ. ospecialize * EQ. *)
  (*   { eapply locales_of_cfg_Some. eauto. } *)
  (*   apply locales_of_cfg_Some in EQ as [??]. *)

  (*   destruct (decide (τ = locale_of tp (fill K e1))). *)
  (*   2: { eapply locale_step_other_same in LSTEP; eauto. *)
  (*        2: { intros [=]. congruence. } *)
  (*        rewrite TTH in LSTEP. inversion LSTEP. subst. *)
  (*        eauto. } *)

  (*   subst. *)
  (*   apply from_locale_lookup in TTH. rewrite /locale_of in TTH. *)
  (*   rewrite lookup_app_r in TTH; [| simpl; lia]. *)
  (*   rewrite Nat.sub_diag in TTH. simpl in TTH. inversion TTH. subst. *)

  (*   pose proof H as TTH1.   *)
  (*   apply from_locale_lookup in H. rewrite /locale_of in H. *)
  (*   rewrite lookup_app_r in H; [| simpl; lia]. *)
  (*   rewrite Nat.sub_diag in H. simpl in H. inversion H. subst. *)

  (*   destruct (decide (is_sub_expr v e2)). *)
  (*   { eapply head_step_sub_values in STEP; eauto. *)
  (*     destruct STEP. *)
  (*     { left. eexists. split; eauto. *)
  (*       etrans; [apply H0| ]. apply is_sub_expr_fill. } *)
  (*     destruct H0 as (?&->&?).  *)
  (*     right. do 2 eexists; eauto. } *)
    
  (*   left. eexists. split; eauto. *)
  (*   eapply is_sub_expr_in_ectx; eauto. *)
  (* Qed. *)
  
  Lemma locale_step_sub_values K e1 tp σ1 e2 tp' σ2 efs
    (c1 := (tp ++ (fill K e1) :: tp', σ1))
    (c2 := (tp ++ (fill K e2) :: tp' ++ efs, σ2))
    (τ := locale_of tp (fill K e1))
    (STEP: head_step e1 σ1 e2 σ2 efs)
    (** should be generalizable to forks, but we don't use it *)
    (NOFORK: step_fork c1 c2 = None):
    forall v e2,
      from_locale c2.1 τ = Some e2 -> is_sub_expr (Val v) e2 ->
      (is_sub_expr (Val v) (fill K e1)) \/
      exists v2, e2 = fill K (Val v2) /\ is_sub_val v v2.
  Proof using.
    intros * TTH SUB2.
    (* pose proof STEP as HSTEP. *)
    assert (locale_step c1 (Some $ locale_of tp (fill K e1)) c2) as LSTEP.
    { subst c1 c2. econstructor; eauto.
      econstructor; eauto. }
    
    pose proof LSTEP as EQ%locale_step_step_fork_exact.
    rewrite NOFORK /= union_empty_r_L in EQ.

    subst c1 c2. simpl in *. subst.
    rewrite set_eq in EQ.
    ospecialize (EQ _). apply proj1 in EQ. ospecialize * EQ.
    { eapply locales_of_cfg_Some. eauto. }
    apply locales_of_cfg_Some in EQ as [??].

    (* destruct (decide (τ = locale_of tp (fill K e1))). *)
    (* 2: { eapply locale_step_other_same in LSTEP; eauto. *)
    (*      2: { intros [=]. congruence. } *)
    (*      rewrite TTH in LSTEP. inversion LSTEP. subst. *)
    (*      eauto. } *)

    subst. unfold locale_of in τ. subst τ.  
    apply from_locale_lookup in TTH. rewrite /locale_of in TTH.
    rewrite lookup_app_r in TTH; [| simpl; lia].
    rewrite Nat.sub_diag in TTH. simpl in TTH. inversion TTH. subst.

    pose proof H as TTH1.
    apply from_locale_lookup in H. rewrite /locale_of in H.
    rewrite lookup_app_r in H; [| simpl; lia].
    rewrite Nat.sub_diag in H. simpl in H. inversion H. subst.

    destruct (decide (is_sub_expr v e2)).
    { eapply head_step_sub_values in STEP; eauto.
      destruct STEP.
      { left. etrans; [apply H0| ]. apply is_sub_expr_fill. }
      destruct H0 as (?&->&?).
      right. do 2 eexists; eauto. }
    
    left. 
    eapply is_sub_expr_in_ectx; eauto.
  Qed.

  (* TODO: maybe we won't need such lemma directly? *)
  (* TODO: unify 'no fork' restrictions *)
  Lemma exec_sub_values (etr: execution_trace heap_lang) K τ i ei ci j ej cj
    (* (c1 := (tp ++ (fill K e1) :: tp', σ1)) *)
    (* (c2 := (tp ++ (fill K e2) :: tp' (* ++ efs *), σ2)) *)
    (ITH: etr !! i = Some ci) (EI: expr_at (TpoolCtx K τ) ci ei)
    (JTH: etr !! j = Some cj) (EJ: expr_at (TpoolCtx K τ) cj ej)
    (LE: i <= j)
    (VALID: valid_exec etr)
    (KK: forall k, i <= k <= j -> from_option (nval_at $ TpoolCtx K τ) False (etr !! k))
    (NOFORKS: length cj.1 = length ci.1)
    :
    forall v ej, 
      from_locale cj.1 τ = Some ej -> is_sub_expr (Val v) ej ->
      (is_sub_expr (Val v) (fill K ei)) \/
      exists v2, ej = fill K (Val v2) /\ is_sub_val v v2. 
  Proof using.
    apply Nat.le_sum in LE as [d ->].
    generalize dependent cj. generalize dependent ej.
    induction d.
    { rewrite Nat.add_0_r. set_solver. }

    intros. edestruct (trace_lookup_lt_Some_2 etr (i + d)) as [ep PREV].
    { apply mk_is_Some, trace_lookup_lt_Some in JTH. lia. }
  Abort. 
   
