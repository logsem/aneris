From iris.proofmode Require Import tactics.
From fairness Require Import locales_helpers utils fairness.
From lawyer.nonblocking Require Import trace_context.
From heap_lang Require Import lang notation.
From trillium.traces Require Import exec_traces trace_lookup inftraces.
From heap_lang Require Import locales_helpers_hl.


Close Scope Z. 


Section UnderCtx.

  Local Definition check P `{Decision P} (e: expr) :=
    if (decide P) then Some e else None. 

  Definition under_ctx_item (Ki: ectx_item) (e: expr): option expr :=
    match Ki, e with 
  | AppLCtx vc2, App e e2 => check (e2 = of_val vc2) e
  | AppRCtx ec1, App e1 e => check (e1 = ec1) e
  | UnOpCtx opc, UnOp op e => check (op = opc) e
  | BinOpLCtx opc vc, BinOp op e1 v2 => check (op = opc /\ v2 = vc) e1
  | BinOpRCtx opc ec, BinOp op e1 e2 => check (op = opc /\ e1 = ec) e2
  | IfCtx ec1 ec2, If e e1 e2 => check (e1 = ec1 /\ e2 = ec2) e
  | PairLCtx vc2, Pair e (Val v2) => check (v2 = vc2) e
  | PairRCtx ec1, Pair e1 e => check (e1 = ec1) e
  | FstCtx, Fst e => Some e
  | SndCtx, Snd e => Some e
  | InjLCtx, InjL e => Some e
  | InjRCtx, InjR e => Some e
  | CaseCtx ec1 ec2, Case e e1 e2 => check (e1 = ec1 /\ e2 = ec2) e
  | AllocNLCtx vc2, AllocN e (Val v2) => check (v2 = vc2) e
  | AllocNRCtx ec1, AllocN e1 e => check (e1 = ec1) e
  | FreeCtx, Free e => Some e
  | LoadCtx, Load e => Some e
  | StoreLCtx vc2, Store e (Val v2) => check (v2 = vc2) e
  | StoreRCtx ec1, Store e1 e => check (e1 = ec1) e
  | CmpXchgLCtx vc1 vc2, CmpXchg e (Val v1) (Val v2) => check (v1 = vc1 /\ v2 = vc2) e
  | CmpXchgMCtx ec0 vc2, CmpXchg e0 e (Val v2) => check (e0 = ec0 /\ v2 = vc2) e
  | CmpXchgRCtx ec0 ec1, CmpXchg e0 e1 e => check (e0 = ec0 /\ e1 = ec1) e
  | FaaLCtx vc2, FAA e (Val v2) => check (v2 = vc2) e
  | FaaRCtx ec1, FAA e1 e => check (e1 = ec1) e
  | _, _ => None
    end.

  Local Lemma not_eq_helper (x e1 e2: expr)
    (NEQ: e1 ≠ e2):
    None = Some x <-> e1 = e2.
  Proof using. trans False; done. Qed.
    
  Lemma under_ctx_item_spec Ki e e':
    under_ctx_item Ki e = Some e' <-> fill_item Ki e' = e.
  Proof using.
    destruct Ki, e; simpl.
    all: try by apply not_eq_helper. 
    Local Ltac solve_iff := rewrite /check; destruct decide; try apply not_eq_helper; subst; set_solver.
    all: try by solve_iff.
    all: try by set_solver.
    all: try by (destruct e2; by apply not_eq_helper || solve_iff). 
    - destruct e2, e3; by apply not_eq_helper || solve_iff.
    - destruct e3; by apply not_eq_helper || solve_iff.
  Qed.

  (* TODO: move *)
  Lemma fill_item_nval_strong e1 e2 i1 i2
    (NVAL1: to_val e1 = None) (NVAL2: to_val e2 = None)
    (EQ: fill_item i1 e1 = fill_item i2 e2):
    i1 = i2 /\ e1 = e2. 
  Proof using.
    Set Printing Coercions.
    destruct i1, i2; simpl in EQ.
    all: try congruence.
    all: try by (inversion EQ; subst; done).
  Qed.

  Fixpoint expr_depth (e: expr) :=
    match e with
    | Val _ (** for the purposes expr_depth is used, depth of this value is irrelevant *)
    | Var _ | ChooseNat => 0
    | Rec _ _ e | UnOp _ e | Fst e | Snd e | InjL e
    | InjR e | Fork e | Free e | Load e
                                 => S $ expr_depth e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2
    | AllocN e1 e2 | Store e1 e2 | FAA e1 e2
                                   => S $ max (expr_depth e1) (expr_depth e2)
    | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2
                                    => S $ max_list [expr_depth e0; expr_depth e1; expr_depth e2]
      end.

  Lemma fill_item_depth i e:
    expr_depth e < expr_depth (fill_item i e). 
  Proof using.
    destruct i; simpl; lia.
  Qed.

  From lawyer.nonblocking.logrel Require Import substitutions.

  (* TODO: upstream most of fill/fill_item lemmas below *)
  (* TODO: move, find existing? *)
  Lemma fill_app K1 K2 (e: expr):
    fill K1 (fill K2 e) = fill (K2 ++ K1) e. 
  Proof using.
    rewrite /fill. by rewrite foldl_app.
  Qed.

  (* TODO: move, find existing? *)
  Lemma fill_item_fill_1 i (e: expr):
    fill_item i e = fill [i] e. 
  Proof using. done. Qed.

  Lemma fill_item_fill K i e:
    let K' := take (length K) (i :: K) in
    fill K (fill_item i e) = fill_item (default i (last K)) (fill K' e).
  Proof using.
    simpl. 
    rewrite !fill_item_fill_1.
    rewrite !fill_app.
    f_equal.
    simpl. 

    generalize dependent i. clear e. pattern K. apply rev_ind; clear K. 
    { done. }
    intros. simpl. 
    (* we really only need the tail element, IH doesn't matter *)
    clear H. 
    rewrite length_app. simpl.
    rewrite app_comm_cons.
    rewrite take_app_length'.
    2: simpl; lia.
    rewrite last_snoc. done.
  Qed.

  Lemma fill_depth' K e
    (NEMP: K ≠ ectx_emp):
    expr_depth e < expr_depth (fill K e).
  Proof using.
    generalize dependent e.
    revert NEMP. pattern K. apply rev_ind; clear K. 
    { done. }
    simpl. intros.
    destruct l.
    { simpl. apply fill_item_depth. }
    etrans; [apply H; done| ]. 
    rewrite -fill_app. rewrite -fill_item_fill_1. 
    apply fill_item_depth.
  Qed.   

  Lemma fill_depth K e:
    expr_depth e <= expr_depth (fill K e).
  Proof using.
    destruct K.
    { done. }
    apply Nat.lt_le_incl.
    by apply fill_depth'. 
  Qed.

  Lemma fill_eq_inv (e: expr) K
    (EQ: fill K e = e):
    K = [].
  Proof using. 
    destruct K; [done| ].
    symmetry in EQ. 
    apply (@f_equal _ _ expr_depth) in EQ.
    apply Nat.lt_neq in EQ; [done| ].
    by apply fill_depth'.
  Qed.

  (* TODO: move *)
  Lemma ectx_fill_ctx_nval e
    (NVAL: to_val e = None):
    Inj eq eq (flip fill e).
  Proof using.
    red. simpl. intros x. generalize dependent e.
    pattern x. apply rev_ind; clear x; simpl. 
    { intros. symmetry. by eapply fill_eq_inv. } 
    intros a x IH e NVAL y EQ.

    revert EQ. pattern y. apply rev_ind; clear y. 
    { intros EQ. simpl in EQ. by eapply fill_eq_inv. } 

    intros y' b _ EQ.
    rewrite -!fill_app -!fill_item_fill_1 in EQ.
    apply fill_item_nval_strong in EQ as [??].
    2, 3: by apply fill_not_val. 
    subst. f_equal. eauto.
  Qed.

  Fixpoint under_ctx (K: ectx heap_lang) (e: expr): option expr :=
    match K with
    | [] => Some e
    | Ki :: K' => from_option (under_ctx_item Ki) None (under_ctx K' e)
    end. 

  Lemma under_ctx_spec K e e':
    under_ctx K e = Some e' <-> fill K e' = e.
  Proof using.
    generalize dependent e. generalize dependent e'.
    induction K.
    { simpl. set_solver. }
    intros. simpl. destruct under_ctx eqn:ITEM.
    2: { apply not_eq_helper.
         intros EQ. rewrite -IHK in EQ. congruence. }
    rewrite under_ctx_item_spec.
    apply IHK in ITEM. simpl in *.
    rewrite -ITEM. split.
    + by intros <-.
    + by intros ?%ectx_fill_inj.
  Qed.

  Lemma under_ctx_spec_neg K e:
    under_ctx K e = None <-> forall e', fill K e' ≠ e.
  Proof using.
    simpl. split; intros. 
    - intros EQ%under_ctx_spec. congruence.
    - destruct under_ctx eqn:UC; [| done].
      apply under_ctx_spec in UC.
      edestruct H; eauto.
  Qed.

  Lemma under_ctx_fill K e:
    under_ctx K (fill K e) = Some e.
  Proof using. by apply under_ctx_spec. Qed.

  Lemma under_ctx_val_Some_inv (e ec: expr) K
    (CTX: under_ctx K e = Some ec)
    (VAL: is_Some (language.to_val e)):
    K = ectx_emp /\ ec = e.
  Proof using.
    apply under_ctx_spec in CTX. simpl in *.
    destruct K; simpl in CTX; subst; try done.
    simpl in VAL.
    rewrite fill_not_val in VAL.
    { by destruct VAL. }
    by destruct e0. 
  Qed.

  (** specific to heap_lang, as it requires under_ctx *)
  Global Instance nval_at_dec:
    forall tc c, Decision (nval_at tc c).
  Proof using.
    intros [K τ] ?. rewrite /nval_at /expr_at.
    apply ex_fin_dec with
             (l := from_option
                     (fun e => from_option (flip cons nil) [] (under_ctx K e))
                     [] (from_locale c.1 τ)); [apply _| ].
    intros ec (IN & NVAL).
    rewrite IN. simpl. rewrite under_ctx_fill. simpl. tauto.  
  Qed.

End UnderCtx.

Section NestedCalls.
  Context (f x: binder) (b: expr). 
  Let m := RecV f x b. 
  (* TODO: the restriction to RecV is reasonable,
     but is only needed for premise of head_redex_unique.
     What changes if (m a) is not reducible (i.e. m ≠ RecV)? *)

  Definition empty_state := Build_state ∅ ∅. 

  Lemma call_unique 
    (K1 K2: ectx heap_lang) (a1 a2: val)
    (EQ: ectx_language.fill K1 (m a1) = ectx_language.fill K2 (m a2)):
    K1 = K2 /\ a1 = a2.
  Proof using.
    subst m. 
    eapply head_redex_unique with (σ := empty_state) in EQ as [K_EQ APP_EQ].
    2, 3: by (red; do 3 eexists; eapply BetaS; eauto).
    by inversion APP_EQ.
  Qed.

  Lemma comp_ectx_heap_lang:
    forall (K1 K2: ectx heap_lang), comp_ectx K1 K2 = K2 ++ K1.
  Proof using. done. Qed.

      (* fill K' e1' = fill K_redex e1_redex → (* K' = K1, K_redex = K2 *) *)
      (* to_val e1' = None → (* e1' = e1 ∉ Val *) *)
      (* head_step e1_redex σ1 e2 σ2 efs → (* e1_redex = m a2 *) *)
      (* ∃ K'', K_redex = comp_ectx K' K''; (* ==> K2 is deeper than K1 *) *)

  (* TODO: rename? *)
  Lemma call_ctx_is_deeper K1 e1 K2 (a2: val)
    (EQ: fill K1 e1 = fill K2 (m a2))
    (NVAL1: to_val e1 = None):
    exists K', K2 = ectx_comp K1 K'.
  Proof using.
    eapply mixin_step_by_val; eauto.
    { apply ectx_language_mixin. }
    simpl. apply @BetaS. reflexivity.
    Unshelve. exact empty_state.
  Qed.

  (* TODO: move  *)
  Lemma locale_of_hl_expr_irrel tp e e':
    locale_of tp e = locale_of tp e'.
  Proof using. done. Qed. 

  Lemma call_continues_or_returns tpc_ c1 c2 oτ
    (NVAL: nval_at tpc_ c1)
    (STEP: locale_step c1 oτ c2):
    nval_at tpc_ c2 \/ exists r, return_at tpc_ c2 r.
  Proof using.
    red in NVAL. destruct NVAL as (e & EXPR & NVAL).
    pose proof EXPR as [eτi TI]%expr_at_in_locales%locales_of_cfg_Some.
    2: by apply c1. 
    red in EXPR. destruct tpc_ as [K' τ'].  
    simpl in STEP. 
    inversion STEP; subst; inversion H1.

    subst. simpl in *.
    destruct (decide (τ' = locale_of t1 (fill K e1'))).
    2: { left. exists e. split; auto.
         red. eapply locale_step_other_same; set_solver. } 

    subst τ'.
    rewrite /from_locale from_locale_from_locale_of in EXPR. inversion EXPR as [FILL'].
    rewrite FILL' in H1.
    apply fill_step_inv in H1; eauto. simpl in *.
    destruct H1 as (e' & EQ2 & STEP'). rewrite FILL' EQ2.

    rewrite /nval_at. simpl.
    erewrite locale_of_hl_expr_irrel.
    rewrite /from_locale. erewrite (from_locale_from_locale_of nil t1).

    destruct (to_val e') eqn:VAL; [| by eauto]. 
    right. exists v. Set Printing Coercions.
    erewrite of_to_val; eauto.
  Qed.

  Lemma call_returns_if_not_continues tpc_ i j ci cj etr
    (VALID: extrace_valid etr)
    (ITH: etr S!! i = Some ci)
    (CALL : nval_at tpc_ ci)
    (LE: i <= j)
    (JTH: etr S!! j = Some cj)
    (NOCONT: ¬ nval_at tpc_ cj)
    :
    exists k r ck, i < k <= j /\ etr S!! k = Some ck /\ return_at tpc_ ck r. 
  Proof using.
    apply Nat.le_sum in LE as [d ->].    
    generalize dependent i. generalize dependent ci.
    induction d.
    { simpl. setoid_rewrite Nat.add_0_r. intros.
      rewrite ITH in JTH. inversion JTH. by subst. }
    intros.
    pose proof JTH as X.
    apply mk_is_Some, state_lookup_prev with (j := S i) in X as [ci' ITH']; [| lia].
    pose proof ITH' as [oτ ITHl]%mk_is_Some%label_lookup_states'.
    rewrite -Nat.add_1_r in ITH'.
    opose proof * (trace_valid_steps'' _ _ _ i) as STEP; eauto.
    { apply extrace_valid_alt in VALID; eauto. }
    eapply call_continues_or_returns in STEP; eauto.
    destruct STEP as [NVAL | [r RET]].
    2: { do 3 eexists. split; eauto. lia. }
    ospecialize (IHd _ NVAL _ ITH' _).
    { rewrite -JTH. f_equal. lia. }
    destruct IHd as (?&?&?&?&?&?).
    do 3 eexists. split; eauto. lia.
  Qed.

  Lemma nested_call_returns_earlier (etr: extrace heap_lang) τ
    K1 a1 c1 i1
    K2 a2 c2 i2
    r1 c1'
    (VALID: extrace_valid etr)
    (ST1: etr S!! i1 = Some c1)
    (CALL1: call_at (TpoolCtx K1 τ) c1 m a1 (APP := App))
    (ST2: etr S!! i2 = Some c2)
    (CALL2: call_at (TpoolCtx K2 τ) c2 m a2 (APP := App))
    (* (NESTED: nval_at *)
    (NESTED: exists K', K2 = ectx_comp K1 K')
    (AFTER: i1 <= i2)
    (ST1': etr S!! r1 = Some c1')
    (ORDER: i2 <= r1)
    (RET1: exists v, return_at (TpoolCtx K1 τ) c1' v):
    exists r2 c2' v2, i2 <= r2 /\ r2 <= r1 /\ etr S!! r2 = Some c2' /\
                  return_at (TpoolCtx K2 τ) c2' v2.
  Proof using.
    destruct NESTED as [K' ->].
    opose proof * (call_returns_if_not_continues (TpoolCtx (ectx_comp K1 K') τ) i2 r1) as RET2; eauto.
    { eapply call_nval_at; eauto. done. }
    { red. rewrite /nval_at /expr_at. intros (?&EQ&NVAL).
      rewrite /return_at /expr_at in RET1. destruct RET1 as (?&EQ').
      rewrite EQ' in EQ. rewrite ectx_comp_comp in EQ.
      inversion EQ. apply ectx_fill_inj in H0.
      eapply fill_not_val in NVAL.
      apply (@f_equal _ _ to_val) in H0.
      rewrite NVAL in H0. done. }
    destruct RET2 as (?&?&?&?&?&RET2).
    do 3 eexists. repeat split.
    4: by apply RET2.
    3: by apply H0.
    all: try lia.
    (* TODO: get rid of it *)
    Unshelve. eauto.
  Qed.                                    

End NestedCalls.
