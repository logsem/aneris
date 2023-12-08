From trillium.fairness Require Import fairness fuel fuel_ext utils.

Close Scope Z_scope.


Section LocaleTrans.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI}. 
  Context `{∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2)}.
  Context `{EqDecision (fmstate M)}. 

  (* TODO: rename *)
  Definition locale_trans  (st1: lm_ls LM) (τ: G) st2 :=
    exists ℓ, ls_trans (lm_fl LM) st1 ℓ st2 /\ fair_lbl_matches_group ℓ τ. 
    
  Definition potential_step_FLs `{LM: LiveModel G M LSI}
    (st1: lm_ls LM) (τ: G): 
    gset (@FairLabel G (fmrole M)) :=
    {[ Silent_step τ ]} ∪ (set_map (fun ρ => Take_step ρ τ) (dom (ls_fuel st1))).

  (* TODO: move *)
  Global Instance lm_ls_trans_dec st1 l st2:
    Decision (lm_ls_trans LM st1 l st2).
  Proof.
    destruct l; simpl. 
    3: { right. intros []. tauto. }
    - solve_decision. 
    - repeat apply and_dec; try solve_decision.
      destruct (ls_tmap st1 !! g) eqn:TMAP.
      2: { right. intros [? MAP].
           apply ls_mapping_tmap_corr in MAP as (?&?&?).
           set_solver. }
      destruct (decide (g0 = ∅)) as [-> |NEMPTY].
      { right. intros [? MAP].
        apply (ls_mapping_tmap_corr) in MAP as (?&?&?).
        set_solver. }
      left. apply set_choose_L in NEMPTY as [ρ ?].
      exists ρ. apply (ls_mapping_tmap_corr). eauto. 
  Defined. 
    
  Definition allowed_step_FLs δ1 τ δ2: gset (@FairLabel G (fmrole M)) :=
    filter (fun l => bool_decide (lm_ls_trans LM δ1 l δ2) = true)
      (potential_step_FLs δ1 τ (LM := LM)).

  Lemma aFLs_unique_TS_helper δ1 τ δ2 ρ:
    Take_step ρ τ ∈ allowed_step_FLs δ1 τ δ2 ->
    lm_ls_trans LM δ1 (Take_step ρ τ) δ2 /\ ls_mapping δ1 !! ρ = Some τ.
  Proof.
    rewrite /allowed_step_FLs /potential_step_FLs. 
    rewrite !elem_of_filter. rewrite !elem_of_union.
    rewrite elem_of_singleton elem_of_map.
    intros [STEP%bool_decide_eq_true [[=] | IN]].
    destruct IN as (?&[=]&?). subst.
    split; auto.
    apply STEP.
  Qed.


  Lemma locale_trans_alt δ1 τ δ2:
    locale_trans δ1 τ δ2 <-> allowed_step_FLs δ1 τ δ2 ≠ ∅.
  Proof using. 
    rewrite /allowed_step_FLs /locale_trans. 
    rewrite gset_not_elem_of_equiv_not_empty_L.
    setoid_rewrite elem_of_filter.
    rewrite /potential_step_FLs.
    setoid_rewrite elem_of_union. setoid_rewrite elem_of_singleton.
    setoid_rewrite elem_of_map. 
    rewrite -ls_same_doms. setoid_rewrite elem_of_dom.  
    setoid_rewrite bool_decide_eq_true. 
    split.
    - intros (ℓ & T & MATCH).
      eexists. split; eauto.
      destruct ℓ; simpl in MATCH; subst; try tauto.
      right. eexists. split; eauto. inversion T. set_solver. 
    - intros (?&STEP&POT).
      destruct POT as [-> | (?&->&MAP)].
      all: eexists; split; [eapply STEP| done]. 
  Qed.

  Global Instance locale_trans_dec st1 τ st2:
    Decision (locale_trans st1 τ st2).
  Proof.
    eapply Decision_iff_impl; [symmetry; by apply locale_trans_alt| ].
    solve_decision.
  Qed.

  (* TODO: move *)
  Lemma iff_and_pre {A B C: Prop}
    (BC: A -> (B <-> C)):
    A /\ B <-> A /\ C.
  Proof using. tauto. Qed.
                    
  Lemma aFLs_equiv ℓ δ1 τ δ2 :
    ℓ ∈ allowed_step_FLs δ1 τ δ2 <-> lm_ls_trans LM δ1 ℓ δ2 /\ fair_lbl_matches_group ℓ τ.
  Proof using.
    rewrite /allowed_step_FLs elem_of_filter.
    rewrite bool_decide_eq_true.
    apply iff_and_pre. intros STEP. 
    rewrite /potential_step_FLs /fair_lbl_matches_group.
    rewrite elem_of_union elem_of_singleton elem_of_map.
    split.
    { by intros [-> | (?&->&?)]. } 
    destruct ℓ; [..| done]; intros ->; eauto. 
    right. eexists. split; eauto.
    simpl in STEP. rewrite -ls_same_doms. apply elem_of_dom.
    eexists. apply STEP. 
  Qed. 

End LocaleTrans. 

(* excluding parts that are provided by other classes in context *)
(* TODO: find a better solution *)
Class LMFairPre' {G M LSI} `{Countable G} (LM: LiveModel G M LSI) := {
  (* edG :> EqDecision G; *)
  (* cntG :> Countable G; *)
  edM' :> EqDecision (fmstate M);
  dTr' :> ∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2);
  inhLM' :> Inhabited (lm_ls LM);
  inhG' :> Inhabited G;
  locale_trans_ex_dec' τ δ1 :> Decision (exists δ2, locale_trans δ1 τ δ2 (LM := LM));
}.

(* Class LMFairPre {G M LSI} (LM: LiveModel G M LSI) := { *)
(*   edG :> EqDecision G; *)
(*   cntG :> Countable G; *)
(*   edM :> EqDecision (fmstate M); *)
(*   dTr :> ∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2); *)
(*   inhLM :> Inhabited (lm_ls LM); *)
(*   inhG :> Inhabited G; *)
(*   locale_trans_ex_dec τ δ1 :> Decision (exists δ2, locale_trans δ1 τ δ2 (LM := LM)); *)
(* }. *)

(* TODO: get rid of this duplication *)
(* Definition LMFairPre {G M LSI} `{Countable G} (LM: LiveModel G M LSI) := *)
(*   LMFairPre' LM.  *)
Class LMFairPre {G M LSI} `{Countable G} (LM: LiveModel G M LSI) := {
  (* edG :> EqDecision G; *)
  (* cntG :> Countable G; *)
  edM :> EqDecision (fmstate M);
  dTr :> ∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2);
  inhLM :> Inhabited (lm_ls LM);
  inhG :> Inhabited G;
  locale_trans_ex_dec τ δ1 :> Decision (exists δ2, locale_trans δ1 τ δ2 (LM := LM));
}.


Section LMFair.
  Context `{CNTG: Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {LF: LMFairPre LM}.
  
  Global Instance LS_eqdec: EqDecision (LiveState G M LSI).
  Proof.
    red. intros [] [].
    destruct (decide (ls_under = ls_under0)), (decide (ls_fuel = ls_fuel0)), (decide (ls_tmap = ls_tmap0)).
    2-8: right; intros [=]; congruence.
    subst.
    left. f_equal.
    all: apply ProofIrrelevance. 
  Qed. 

  (* TODO: move, use in other places *)
  Lemma dec_forall_fin_impl {A: Type} (P Q: A -> Prop) (domP: list A)
    (DOMP: forall a, P a -> a ∈ domP)
    (DECP: forall a, Decision (P a))
    (DECQ: forall a, P a -> Decision (Q a)):
    Decision (forall a, P a -> Q a).
  Proof. 
    set (domPP := filter P domP). 
    destruct (@decide (Forall Q domPP)).
    { assert (forall a, a ∈ domPP -> P a).
      { subst domPP. intros ??%elem_of_list_filter. tauto. }
      remember domPP as dom. clear Heqdom. induction dom.
      { left. by apply Forall_nil. }
      assert (P a) as Pa.
      { apply H; eauto. set_solver. }
      specialize (DECQ _ Pa). 
      destruct DECQ.
      2: { right. by intros ALL%Forall_inv. }
      destruct IHdom.
      { intros. apply H. set_solver. }
      - left. by constructor.
      - right. by intros ALL%Forall_inv_tail. } 
    - left. intros.
      eapply Forall_forall; eauto.
      subst domPP. apply elem_of_list_filter. split; auto. 
    - right. intros IMPL.
      apply n. apply List.Forall_forall.
      intros. apply IMPL.
      subst domPP. apply elem_of_list_In, elem_of_list_filter in H.
      tauto.
  Qed.
    
  Lemma dec_forall_fin_impl' {A: Type} `{Countable A} 
    (P Q: A -> Prop) (domP: gset A)
    (DOMP: forall a, P a -> a ∈ domP)
    (DECP: forall a, Decision (P a))
    (DECQ: forall a, P a -> Decision (Q a)):
    Decision (forall a, P a -> Q a).
  Proof.
    apply dec_forall_fin_impl with (domP := elements domP); auto.
    set_solver. 
  Qed. 

  (* not true in general - it's possible to burn fuels even for the stepping role *)
  (* Lemma allowed_FLs_unique_TS δ1 τ δ2: *)
  (*   forall ρ1 ρ2, *)
  (*     Take_step ρ1 τ ∈ allowed_step_FLs δ1 τ δ2 -> *)
  (*     Take_step ρ2 τ ∈ allowed_step_FLs δ1 τ δ2 -> *)
  (*     ρ1 = ρ2. *)

  (* Lemma lm_trans_simpl_dom δ1 ℓ δ2 *)
  (*   (TRANS: lm_ls_trans LM δ1 ℓ δ2): *)
  (*   exists (δ2': LiveState _ _ LSI), lm_ls_trans LM δ1 ℓ δ2 /\ *)
  (*            ls_under δ2' = ls_under δ2 /\ ls_fuel δ2' = ls_fuel δ2 /\ *)
  (*            ls_mapping δ2' = ls_mapping δ1. *)
  (* Proof.  *)
  (*   unshelve eset (δ2' := {| ls_under := ls_under δ2;  *)
  (*                   ls_fuel := ls_fuel δ2; *)
  (*                   ls_mapping := ls_mapping δ1 |}). *)
  (*   { exact LSI. } *)

  Definition olocale_trans st1 oρ st2 :=
    match oρ with
    | Some τ => locale_trans st1 τ st2 (LM := LM)
    | _ => False
    end.

  (* TODO: rename "locale" into "group" everywhere *)
  Global Definition LM_Fair: FairModel.
    refine {|
        fmstate := lm_ls LM;
        fmrole := G;
        fmtrans := olocale_trans;
        live_roles δ := filter (fun τ => exists δ', locale_trans δ τ δ') (dom (ls_tmap δ));
      |}.
    (* - apply lm_ls_eqdec.  *)
    - intros ??? STEP.
      apply elem_of_filter. split; eauto.
      destruct STEP as (ℓ & STEP & MATCH). destruct ℓ; simpl in *; try done; subst.
      + destruct STEP as (_&MAP&_).
        eapply ls_mapping_tmap_corr in MAP as (?&?&?). eapply elem_of_dom; eauto.
      + destruct STEP as ([? MAP]&_). 
        eapply ls_mapping_tmap_corr in MAP as (?&?&?). eapply elem_of_dom; eauto.
  Defined.

  Lemma LM_live_roles_strong δ τ:
    τ ∈ live_roles LM_Fair δ <-> (exists δ', locale_trans δ τ δ' (LM := LM)).
  Proof.
    split.
    2: { intros [??]. eapply LM_Fair. simpl. eauto. }
    simpl. intros [??]%elem_of_filter. eauto.
  Qed.

  (* Useful in cases where the whole LM_Fair machinery cannot be used *)
  Definition group_enabled τ δ := exists δ', locale_trans δ τ δ' (LM := LM).

  Lemma LM_live_role_map_notempty δ τ
    (LIVE: τ ∈ live_roles LM_Fair δ):
    exists R, ls_tmap δ !! τ = Some R /\ R ≠ ∅.
  Proof using.
    apply LM_live_roles_strong in LIVE as [? STEP].
    destruct STEP as (ℓ & T & MATCH).
    destruct ℓ; simpl in *; try done; subst. 
    - destruct T as (_&MAP&_).
      eapply ls_mapping_tmap_corr in MAP as (?&?&?).
      eexists. split; eauto. set_solver. 
    - destruct T as ([? MAP]&_). 
      eapply ls_mapping_tmap_corr in MAP as (?&?&?). 
      eexists. split; eauto. set_solver. 
  Qed. 

  Lemma LM_map_empty_notlive δ τ
    (MAP0: ls_tmap δ !! τ = Some ∅ \/ ls_tmap δ !! τ = None):
    τ ∉ live_roles LM_Fair δ. 
  Proof using. 
    destruct (decide (τ ∈ live_roles LM_Fair δ)) as [LR| ]; [| done].
    apply LM_live_role_map_notempty in LR as (? & TMAP & NE).
    destruct MAP0; set_solver. 
  Qed. 
      
End LMFair.
