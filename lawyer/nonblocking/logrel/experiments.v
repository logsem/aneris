From iris.proofmode Require Import proofmode coq_tactics.
From lawyer.nonblocking.logrel Require Export persistent_pred logrel substitutions valid_client.
From lawyer.nonblocking Require Export pwp trace_context. 
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
From heap_lang Require Import heap_lang_defs sswp_logic tactics lang notation. 
From trillium.traces Require Import exec_traces  inftraces trace_lookup.
From fairness Require Import fairness locales_helpers utils.

(* Section EctxLe. *)
(*   Context {Λ: language}.  *)

(*   Definition ectx_le (K1 K2: ectx Λ) := exists K', K2 = ectx_comp K1 K'. *)

(*   Global Instance ectx_le_preorder: PreOrder ectx_le. *)
(*   Proof using. *)
(*     split. *)
(*     - red. intros ?. eexists. apply _.  *)

(* End EctxLe.  *)
  
Close Scope Z. 


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

  Lemma call_continues_or_returns tpc_ c1 c2 oτ
    (NVAL: nval_at tpc_ c1)
    (STEP: locale_step c1 oτ c2):
    nval_at tpc_ c2 \/ exists r, return_at tpc_ c2 r.
  Proof using.
    red in NVAL. destruct NVAL as (e & EXPR & NVAL).
    pose proof EXPR as [eτi TI]%expr_at_in_locales%locales_of_cfg_Some.
    2: by apply c1. 
    red in EXPR. destruct tpc_ as [K' τ'].  
    (* pose proof EXPR as [eτi TI]%expr_at_in_locales%locales_of_cfg_Some. *)
    (* 2: { by apply c1. } *)
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
    clear dependent ic. clear dependent m. 
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
    (ST1: etr S!! i1 = Some c1)
    (CALL1: call_at (TpoolCtx K1 τ) c1 m a1 (APP := App))
    (ST2: etr S!! i2 = Some c2)
    (CALL2: call_at (TpoolCtx K2 τ) c2 m a2 (APP := App))
    (* (NESTED: nval_at *)
    (NESTED: exists K', K2 = ectx_comp K1 K')
    (AFTER: i1 < i2)
    (ST1': etr S!! r1 = Some c1')
    (ORDER1: i1 < r1)
    (RET1: exists v, return_at (TpoolCtx K1 τ) c1' v):
    exists r2 c2' v2, i2 < r2 /\ r2 < r1 /\ etr S!! r2 = Some c2' /\
                  return_at (TpoolCtx K2 τ) c2' v2.
  Proof using.
    destruct NESTED as [K' ->].
    call_returns_if_not_continues
                                    

End NestedCalls.
