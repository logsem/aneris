From trillium.fairness Require Import fairness.

Section ActionModel.

  (* Class PreModel := { *)
  (*     pmState: Type; *)
  (*     pmPubA: Type; *)
  (*     pmPrivA: Type; *)
  (*     pmA: Type := pmPubA + pmPrivA; *)
  (*     pmTrans: pmState -> option pmA -> pmState -> Prop; *)
  (* }. *)
    
  (* Class PreModel (pmPubA: Type) := { *)
  (*     pmState: Type; *)
  (*     pmPrivA: Type; *)
  (*     pmRole: Type; *)
  (*     pmA: Type := option pmPubA + pmPrivA; *)
  (*     pmTrans: pmState -> pmA * pmRole -> pmState -> Prop; *)
  (* }. *)

  Record ActionModel := {
      amSt: Type;
      (* amPubA: Type; *)
      (* amPrivA: Type; *)
      (* amA: Type := amPubA + amPrivA; *)
      amA: Type;
      amRole: Type;
      amTrans: amSt -> amA * option amRole -> amSt -> Prop;
  }.

  Arguments amTrans {_}. 

  Definition AM_strong_lr (AM: ActionModel) `{Countable (amRole AM)} :=
    {lr: amSt AM -> gset (option (amRole AM)) |
      forall st oρ, oρ ∈ lr st <-> exists a st', amTrans st (a, oρ) st'}.

  Definition AM_fin_branch' (AM: ActionModel) := 
    {next_steps': amSt AM -> list (amSt AM * amA AM * option (amRole AM)) 
     | forall s1 s2 a oρ, amTrans s1 (a, oρ) s2 -> (s2, a, oρ) ∈ next_steps' s1}.

  Definition AM_step_dec (AM: ActionModel) :=
    forall s1 a oρ s2, Decision (@amTrans AM s1 (a, oρ) s2).

  Definition AM_fin_branch (AM: ActionModel) := 
    {next_steps: amSt AM -> list (amSt AM * amA AM * option (amRole AM)) 
     | forall s1 s2 a oρ, amTrans s1 (a, oρ) s2 <-> (s2, a, oρ) ∈ next_steps s1}.

  Lemma AM_fin_branch_dec (AM: ActionModel)
    (FIN: AM_fin_branch' AM) (DEC: AM_step_dec AM):
    AM_fin_branch AM.
  Proof. 
    destruct FIN as [ns' FIN]. 
    exists (fun s => filter (fun '(s2, a, oρ) => @bool_decide _ (DEC s a oρ s2)) (ns' s)).
    intros. rewrite elem_of_list_filter. rewrite bool_decide_spec.
    symmetry. apply iff_and_impl_helper. intuition.
  Qed.

  (* TODO: move *)
  Lemma ex_prod {A B: Type} (P: A * B -> Prop):
    (exists ab, P ab) <-> (exists a b, P (a, b)).
  Proof.
    split.
    - intros [[??] ?]. eauto.
    - intros (?&?&?). eauto.
  Qed. 

  Lemma fin_branch_strong (AM: ActionModel) `{Countable (amRole AM)}
    (FIN: AM_fin_branch' AM) (DEC: AM_step_dec AM):
    AM_strong_lr AM.
  Proof.
    eapply AM_fin_branch_dec in FIN as [ns FIN]; auto.
    exists (fun s => list_to_set ((fun '(_, _, oρ) => oρ) <$> ns s)). 
    intros. rewrite elem_of_list_to_set. rewrite elem_of_list_fmap.
    do 2 rewrite ex_prod.
    setoid_rewrite ex_det_iff with (a := oρ); [| by intuition].
    rewrite ex2_comm. do 2 (apply exist_proper; intros).
    rewrite FIN. tauto.
  Qed. 


  Section AMProduct.
    Context {AM1 AM2: ActionModel}.
    Context {PA: Type}. 

    (* TODO: should these types be isomorphic? *)
    Context {fact_act: PA -> option (@amA AM1) * option (@amA AM2)}.

    Let PS: Type := @amSt AM1 * @amSt AM2.
    Let PR: Type := @amRole AM1 + @amRole AM2.

    Inductive ProdTrans: PS -> PA * option PR -> PS -> Prop :=
    | pt_inner1 s1 s1' s2 a1 r1 pa
        (LBL: fact_act pa = (Some a1, None))
        (STEP1: amTrans s1 (a1, Some r1) s1'):
      ProdTrans (s1, s2) (pa, Some (inl r1)) (s1', s2)
    | pt_inner2 s2 s2' s1 a2 r2 pa
        (LBL: fact_act pa = (None, Some a2))
        (STEP2: amTrans s2 (a2, Some r2) s2'):
      ProdTrans (s1, s2) (pa, Some (inr r2)) (s1, s2')
    | pt_sync1 s1 s1' s2 s2' a1 a2 r1 pa
        (LBL: fact_act pa = (Some a1, Some a2))
        (STEP1: amTrans s1 (a1, Some r1) s1')
        (STEP2: amTrans s2 (a2, None) s2'):
      ProdTrans (s1, s2) (pa, Some (inl r1)) (s1', s2')
    | pt_sync2 s1 s1' s2 s2' a1 a2 r2 pa
        (LBL: fact_act pa = (Some a1, Some a2))
        (STEP1: amTrans s1 (a1, None) s1')
        (STEP2: amTrans s2 (a2, Some r2) s2'):
      ProdTrans (s1, s2) (pa, Some (inr r2)) (s1', s2')
    .
    
    Definition ProdAM: ActionModel := {| amTrans := ProdTrans; |}.

    (* Lemma ProdAM_strong_lr `{Countable (amRole AM1), Countable (amRole AM2)} *)
    (*   {S1: AM_strong_lr AM1} {S2: AM_strong_lr AM1}:  *)
    (*   AM_strong_lr ProdAM. *)
    (* Proof.  *)
    (*   destruct S1 as [lr1 S1], S2 as [lr2 S2].  *)

    Lemma prod_AM_step_dec {EQ1: EqDecision (amSt AM1)} {EQ2: EqDecision (amSt AM2)}
      (D1: AM_step_dec AM1) (D2: AM_step_dec AM2):      
      AM_step_dec ProdAM.
    Proof.
      red. intros [s1 s2] a oρ [s1' s2'].
      Ltac inv_step := right; intros S; inversion S; subst; congruence.
      destruct oρ as [ρ| ]; [| inv_step]. 
      destruct (fact_act a) as [oa1 oa2] eqn:F.
      destruct oa1 as [a1| ], oa2 as [a2| ]; revgoals. 
      { inv_step. }
      - destruct ρ as [ρ1 | ρ2]. 
        { inv_step. }
        destruct (decide (s1' = s1)) as [-> | ?]; [| inv_step]. 
        destruct (D2 s2 a2 (Some ρ2) s2'); [| inv_step]. 
        left. econstructor; eauto.
      - destruct ρ as [ρ1 | ρ2]. 
        2: { inv_step. }
        destruct (decide (s2' = s2)) as [-> | ?]; [| inv_step]. 
        destruct (D1 s1 a1 (Some ρ1) s1'); [| inv_step]. 
        left. econstructor; eauto.
      - destruct ρ as [ρ1 | ρ2].
        + destruct (D1 s1 a1 (Some ρ1) s1'), (D2 s2 a2 None s2').
          2-4: inv_step.
          left. econstructor; eauto.
        + destruct (D1 s1 a1 None s1'), (D2 s2 a2 (Some ρ2) s2').
          2-4: inv_step.
          left. econstructor; eauto.
    Qed.

    (* TODO: move *)
    Lemma ex_proper3 {A B C: Prop} (P Q: A -> B -> C -> Prop)
      (EQUIV: forall a b c, P a b c <-> Q a b c):
      (exists a b c, P a b c) <-> (exists a b c, Q a b c).
    Proof.
      set_solver.
    Qed. 
      
    (* TODO: move *)
    Lemma ex_prod' {A B: Type} (P: A -> B -> Prop):
      (exists a b, P a b) <-> (exists ab, P ab.1 ab.2).
    Proof.
      split.
      - intros (?&?&?). eexists (_, _). eauto.
      - intros [[??] ?]. eauto.
    Qed.

    Lemma prod_AM_fin_branch' (FIN1: AM_fin_branch' AM1) (FIN2: AM_fin_branch' AM2)
      inv_fact (INV: Cancel eq inv_fact fact_act)
      :
      AM_fin_branch' ProdAM.
    Proof. 
      destruct FIN1 as [ns1 FIN1], FIN2 as [ns2 FIN2].      
      exists (fun '(s1, s2) =>
           let l1 := (fun '(x, y, z) => (x, Some y, z)) <$> ns1 s1 in
           let l2 := (fun '(x, y, z) => (x, Some y, z)) <$> ns2 s2 in 
           '(s1', a1, oρ1) ← (s1, None, None) :: l1;
           '(s2', a2, oρ2) ← (s2, None, None) :: l2;
           let a' := inv_fact (a1, a2) in
           ρ' ← [from_option (Some ∘ inl) None oρ1; from_option (Some ∘ inr) None oρ2];
           mret ((s1', s2'), a', ρ')).
      
      intros [s1 s2] [s1' s2'] a oρ STEP.
      pose proof (cancel_surj a) as [[oa1 oa2] EQ].
      rewrite elem_of_list_bind.
      rewrite !ex_prod.

      (* TODO: shorten the following proof, rewrite under binders? *)
      (* setoid_rewrite elem_of_list_bind. *)      
      inversion STEP; subst.
      { exists s1', (Some a1), (Some r1).
        split.
        2: { apply elem_of_cons. right. rewrite elem_of_list_fmap.
             eexists. split; eauto. simpl. reflexivity. }
        rewrite elem_of_list_bind.
        exists (s2', None, None). 
        rewrite elem_of_list_bind. split.
        2: { apply elem_of_cons. tauto. }
        exists (Some (inl r1)). simpl.
        rewrite elem_of_list_ret. split; [| set_solver].
        do 2 f_equal.
        apply (@f_equal _ _ inv_fact) in LBL. by rewrite INV in LBL. }
      { exists s1', None, None.
        split.
        2: { apply elem_of_cons. tauto. }
        rewrite elem_of_list_bind.        
        exists (s2', (Some a2), (Some r2)).
        rewrite elem_of_list_bind. split.
        2: { apply elem_of_cons. right. rewrite elem_of_list_fmap.
             eexists. split; eauto. simpl. reflexivity. }
        exists (Some (inr r2)). simpl.
        rewrite elem_of_list_ret. split; [| set_solver].
        do 2 f_equal.
        apply (@f_equal _ _ inv_fact) in LBL. by rewrite INV in LBL. }  
      { exists s1', (Some a1), (Some r1).
        split.
        2: { apply elem_of_cons. right. rewrite elem_of_list_fmap.
             eexists. split; eauto. simpl. reflexivity. }
        rewrite elem_of_list_bind.
        exists (s2', Some a2, None). 
        rewrite elem_of_list_bind. split.
        2: { apply elem_of_cons. right. rewrite elem_of_list_fmap.
             eexists. split; eauto. simpl. reflexivity. }
        exists (Some (inl r1)). simpl.
        rewrite elem_of_list_ret. split; [| set_solver].
        do 2 f_equal.
        apply (@f_equal _ _ inv_fact) in LBL. by rewrite INV in LBL. }
      { exists s1', (Some a1), None.
        split.
        2: { apply elem_of_cons. right. rewrite elem_of_list_fmap.
             eexists. split; eauto. simpl. reflexivity. }
        rewrite elem_of_list_bind.
        exists (s2', Some a2, Some r2). 
        rewrite elem_of_list_bind. split.
        2: { apply elem_of_cons. right. rewrite elem_of_list_fmap.
             eexists. split; eauto. simpl. reflexivity. }
        exists (Some (inr r2)). simpl.
        rewrite elem_of_list_ret. split; [| set_solver].
        do 2 f_equal.
        apply (@f_equal _ _ inv_fact) in LBL. by rewrite INV in LBL. }
    Qed. 

  End AMProduct.

  Section AM2FM.
    Context (AM: ActionModel).
    Context `{CNT_R: Countable (amRole AM)}. 
    Context {EQ_ST: EqDecision (amSt AM)}. 
    Context {INH_ST: Inhabited (amSt AM)} {INH_R: Inhabited (amRole AM)}. 

    Context (am_lr: amSt AM -> gset (amRole AM)). 
    Hypothesis (AM_LIVE_ROLES: forall s1 a ρ s2, amTrans s1 (a, Some ρ) s2 → ρ ∈ am_lr s1).

    Inductive am_fmtrans: amSt AM → option (amRole AM) → amSt AM → Prop :=
    | amfm_role_step s1 s2 a r (STEP: amTrans s1 (a, Some r) s2):
      am_fmtrans s1 (Some r) s2
    | amfm_env_step s1 s2 a (STEP: amTrans s1 (a, None) s2):
      am_fmtrans s1 None s2
    .

    Lemma am_lr_spec: ∀ (s : amSt AM) (ρ : amRole AM) (s' : amSt AM),
        am_fmtrans s (Some ρ) s' → ρ ∈ am_lr s.
    Proof.
      intros ? ? ? STEP.
      inversion STEP. subst.  
      eapply AM_LIVE_ROLES; eauto.
    Qed.

    Definition AM2FM : FairModel.
      refine {| fm_live_spec := am_lr_spec |}.
    Defined.      

  End AM2FM.  

End ActionModel.
