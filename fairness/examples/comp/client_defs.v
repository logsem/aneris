From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import resources.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness Require Import lm_fair. 
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.comp Require Import lib lib_ext tracker.
From trillium.fairness.heap_lang Require Export lang.

Close Scope Z_scope.

Section ClientDefs.

  Definition lib_gs: gset lib_grole := {[ ρlg ]}.

  Lemma lib_gs_ne: lib_gs ≠ ∅.
  Proof. done. Qed.
  Lemma ρlg_in_lib_gs: ρlg ∈ lib_gs.
  Proof. done. Qed. 

  Definition lf := lib_fair _ lib_gs_ne.

  Let lib_st := fmstate lf.
  (* Let lib_role := fmrole lib_fair. *)
  Let lib_erole := @ext_role _ (@ExtLibLM _ lib_gs_ne). 

  Definition client_state: Type := lib_st * nat.

  Inductive y_role := ρy.
  Definition client_role: Type := lib_erole + y_role.

  Definition ρ_cl: client_role := inr ρy.
  Definition ρ_lib: client_role := inl $ inl ρlg.
  Definition ρ_ext: client_role := inl $ inr $ env (eiG ρlg) (EM := (@ExtLibLM _ lib_gs_ne)). 
  
  Inductive client_trans: client_state -> option client_role -> client_state -> Prop :=
  | ct_y_step_3 lb:
    client_trans (lb, 3) (Some ρ_cl) (lb, 2)
  (* TODO: allow arbitrary library's LM roles *)
  | ct_lib_ext lb (STOP: lm_is_stopped ρlg lb):
    client_trans (lb, 2) (Some ρ_ext) (reset_lm_st ρlg lb ρlg_in_lib_gs, 1)
  | ct_lib_step lb1 lb2 (LIB_STEP: fmtrans lf lb1 (Some ρlg) lb2):
    client_trans (lb1, 1) (Some ρ_lib) (lb2, 1)
  | ct_y_step_1 (lb: fmstate lf)
                (* (LIB_NOSTEP: 0 ∉ live_roles _ lb) *)
                (LIB_NOROLES: ls_tmap lb !! ρlg = Some ∅)
    :
    client_trans (lb, 1) (Some ρ_cl) (lb, 0)
  .

  Global Instance lib_role_EqDec: EqDecision lib_erole.
  Proof. solve_decision. Defined.
  Global Instance lib_role_Cnt: Countable lib_erole.
  Proof using.
    rewrite /lib_erole. simpl. apply _.
  Defined.
  
  Instance y_EqDec: EqDecision y_role.
  Proof. by (solve_decision). Qed.

  Global Instance client_role_Cnt: Countable client_role.
  Proof using.
    rewrite /client_role.
    unshelve eapply sum_countable.
    eauto. eapply (inj_countable' (fun _ => ()) (fun _ => ρy)).
    by destruct x.
  Qed.

  (* Instance lib_step_dec (st: client_state) (ρ: client_role) st': *)
  (*   Decision (client_trans st (Some ρ) st'). *)
  (* Proof. *)
  (*   Local Ltac nostep := right; intros T; inversion T. *)
  (*   destruct st as [δ_lib n], st' as [δ'_lib n']. *)
  (*   destruct (decide (n = S n' /\ ρ = inr ρy /\ δ_lib = δ'_lib)), *)
  (*            (decide (n = 1 /\ n' = 1 /\ ρ = inl ρlg)). *)
  (*   { lia. } *)
  (*   3: { nostep; subst; tauto. } *)
  (*   - destruct a as (->&->&<-). *)
  (*     destruct n'; [| destruct n'].  *)
  (*     + destruct (ls_tmap δ_lib (LM := lib_model) !! ρlg) eqn:LIB_OBLS. *)
  (*       2: { nostep. by rewrite LIB_OBLS in LIB_NOROLES. } *)
  (*       destruct (decide (g = ∅)). *)
  (*       * subst. left. by constructor.  *)
  (*       * nostep. rewrite LIB_OBLS in LIB_NOROLES. set_solver. *)
  (*     + left. econstructor. *)
  (*     + nostep. *)
  (*   - destruct a as (->&->&->). *)
  (*     destruct (decide (locale_trans δ_lib ρlg δ'_lib (LM := lib_model))).  *)
  
  Instance client_step_ex_dec (st: client_state) (ρ: client_role):
    Decision (exists st', client_trans st (Some ρ) st').
  Proof.
    Local Ltac nostep := right; intros [? T]; inversion T.
    destruct st as [δ_lib n]. destruct n; [| destruct n]; [..| destruct n]; [..| destruct n]. 
    - by nostep. 
    - destruct ρ.
      + destruct l.
        2: by nostep. 
        destruct f.
        pose proof (@lib_LF _ lib_gs_ne). (* why it's not inferred anymore? *)
        destruct (decide (exists δ'_lib, locale_trans δ_lib () δ'_lib (LM := lib_model lib_gs))).
        ** left. destruct e. eexists. econstructor. simpl. eauto.
        ** nostep. simpl in LIB_STEP. eauto. 
      + destruct y. 
        destruct (ls_tmap δ_lib !! ρlg) eqn:LIB_OBLS.
        2: { nostep. by rewrite LIB_OBLS in LIB_NOROLES. }
        destruct (decide (g = ∅)).
        * subst. left. eexists. by constructor. 
        * nostep. rewrite LIB_OBLS in LIB_NOROLES. set_solver.
    - destruct ρ; [destruct l| ]. 
      1, 3: by nostep. 
      destruct e. destruct (decide (i ∈ active_exts δ_lib)).
      + left. destruct i. 
        apply active_exts_spec in e as [??]. simpl in *. 
        eexists. destruct ρlg. 
        eapply ct_lib_ext; eauto.
        apply H.
      + nostep. subst. apply n. apply active_exts_spec.
        inversion T. subst. simpl.
        eexists. red. eauto.
        Unshelve. apply ρlg_in_lib_gs. 
    - destruct ρ.
      + nostep.
      + destruct y. left. eexists. constructor.
    - nostep. 
  Qed.

  Definition client_lr (st: client_state): gset (client_role) :=
    filter (fun r => (@bool_decide _ (client_step_ex_dec st r) = true))  
      {[ ρ_lib; ρ_ext; ρ_cl ]}. 

  Lemma client_lr_spec: ∀ (s : client_state) (ρ : client_role),
      (exists s', client_trans s (Some ρ) s') <-> ρ ∈ client_lr s.
  Proof.
    intros ??. rewrite /client_lr.
    rewrite elem_of_filter. rewrite @bool_decide_eq_true.
    rewrite !elem_of_union. rewrite !elem_of_singleton. 
    split.
    2: tauto. 
    intros [? TRANS]. split; eauto. inversion TRANS; subst; eauto.
  Qed.

  Definition client_model_impl: FairModel.
  Proof.
    refine ({|
        fmstate := client_state; 
        fmrole := client_role;
        fmtrans := client_trans;
        live_roles := client_lr;
    |}).
    - pose proof (@LS_eqdec _ _ _ _ _ _ (@lib_LF _ lib_gs_ne)). (* not inferred? *)
      solve_decision.       
    - intros. eapply client_lr_spec; eauto. 
  Defined.

  Lemma live_roles_1 lb:
    live_roles client_model_impl (lb, 1) =
    if (decide (ρlg ∈ live_roles _ lb))
    then {[ ρ_lib ]}
    else if decide (ls_tmap lb !! ρlg = Some ∅)
         then {[ ρ_cl ]}
         else ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.

    erewrite filter_singleton_not with (x := ρ_ext). 
    2: { rewrite bool_decide_eq_false_2; [done| ].
         intros [? STEP]. inversion STEP. }
    rewrite union_empty_r. 

    destruct (decide (ρlg ∈ live_roles lf lb)) as [LR | LR].
    - pose proof (LM_live_role_map_notempty _ _ LR) as (?&MAP&?).
      erewrite filter_singleton, filter_singleton_not, decide_True.
      + set_solver.
      + eauto.
      + rewrite bool_decide_eq_false_2; [done| ].
        intros [? STEP]. inversion STEP. subst. set_solver.
      + rewrite bool_decide_eq_true_2; [done| ].
        eapply LM_live_roles_strong in LR as [? ?]. eauto.
        eexists. eapply ct_lib_step. simpl. eauto.
    - rewrite filter_singleton_not; [rewrite decide_False| ].
      2: { intros [DOM LIVE]%elem_of_filter.
           eapply LM_live_roles_strong in DOM. done. }
      2: { rewrite bool_decide_eq_false_2; [done| ].
           intros [? STEP]. inversion STEP. subst. simpl in LIB_STEP.
           destruct LR. apply LM_live_roles_strong. eauto. }
      destruct (ls_tmap lb !! ρlg) eqn:MAP0.
      (* ; rewrite MAP0. *)
      + destruct (decide (g = ∅)) as [-> | ?].
        * erewrite decide_True; [| done].
          rewrite filter_singleton; [set_solver| ].
          rewrite bool_decide_eq_true_2; [done| ]. eexists. by econstructor.
        * erewrite decide_False.
          2: { intros [=]. done. }
          rewrite filter_singleton_not; [set_solver| ].
          rewrite bool_decide_eq_false_2; [done| ].
          intros [? STEP]. inversion STEP. subst.
          rewrite MAP0 in LIB_NOROLES. congruence.
      + erewrite decide_False; [| done].
        rewrite filter_singleton_not; [set_solver| ].
        rewrite bool_decide_eq_false_2; [done| ].
        intros [? STEP]. inversion STEP. subst.
        rewrite MAP0 in LIB_NOROLES. congruence.
  Qed.

  Lemma live_roles_3 lb0:
    live_roles client_model_impl (lb0, 3) ≡ {[ ρ_cl ]}.
  Proof.
    simpl. rewrite /client_lr.
    rewrite !filter_union.
    erewrite filter_singleton_not, filter_singleton_not, filter_singleton; [set_solver| ..].
    - rewrite bool_decide_eq_true_2; [done| ]. eexists. econstructor.
    - apply not_true_iff_false.
      rewrite bool_decide_eq_false_2; [tauto| ].
      intros [? STEP]. inversion STEP.
    - apply not_true_iff_false.
      rewrite bool_decide_eq_false_2; [tauto| ].
      intros [? STEP]. inversion STEP.
  Qed.

  Lemma live_roles_0 lb:
    live_roles client_model_impl (lb, 0) = ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.
    erewrite !filter_singleton_not; [set_solver| ..].
    all: rewrite bool_decide_eq_false_2; [done| ].
    all: intros [? STEP]; inversion STEP.
  Qed.

  Lemma live_roles_2 lb:
    live_roles client_model_impl (lb, 2) =
    if (decide (lm_is_stopped ρlg lb (NE := lib_gs_ne)))
    then {[ ρ_ext ]}
    else ∅.
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.
    rewrite union_comm.
    rewrite filter_singleton_not; [rewrite filter_singleton_not| ].
    2, 3: rewrite bool_decide_eq_false_2; [done| ]; 
    intros [? STEP]; by inversion STEP.
    rewrite !union_empty_l.

    unshelve erewrite set_filter_equiv with (P2 := fun r => r = ρ_ext /\ lm_is_stopped ρlg lb).
    5: reflexivity.
    { apply lib_gs_ne. }
    2: { intros. rewrite bool_decide_eq_true.
         split.
         - intros [? STEP]. inversion STEP. subst. split; eauto.
         - intros [-> STOP]. exists ((reset_lm_st ρlg lb ρlg_in_lib_gs), 1).
           by econstructor. }

    rewrite -set_filter_and set_filter_comm.
    erewrite set_filter_equiv.
    3: { rewrite filter_singleton; reflexivity. }
    2: { intros. apply iff_refl. }
    rewrite filter_singleton_if. 
    repeat destruct decide; reflexivity || tauto.
    Unshelve. intros. solve_decision. 
  Qed. 

  Definition client_LSI (s: client_state)
    (tm: groups_map (M := client_model_impl) (G := locale heap_lang))
    (_: gmap (fmrole client_model_impl) nat) :=
    forall gi, (exists ρi, ls_mapping s.1 !! ρi = Some gi) -> inl $ inl gi ∈ mapped_roles tm.
    
  Definition client_fl := 15. 
  Definition client_model: LiveModel (locale heap_lang) client_model_impl client_LSI :=
    {| lm_fl _ := client_fl; |}.  

  Class clientPreGS (Σ: gFunctors) := ClientPreGS {
     cl_pre_y_st :> inG Σ (authUR (optionR (exclR natO)));
     cl_lib_preΣ :> fairnessGpreS (lib_model lib_gs) Σ;
     (* cl_trackerΣ :> inG Σ trackerRA; *)
  }.

  Class clientGS Σ := ClientGS {
    cl_pre_inG :> clientPreGS Σ;
    cl_y_st_name : gname;
    (* cl_tracker_name : gname; *)
    cl_lib_Σ :> fairnessGS (lib_model lib_gs) Σ;
  }.

End ClientDefs. 

Section ClientRA.
  Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} {cG: clientGS Σ}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ client_model_impl}.
  
  Notation "'lib_inn_role'" := (fmrole lib_model_impl).
  Notation "'lib_inn_state'" := (fmstate lib_model_impl).
  Notation "'lib_state'" := (fmstate lib_fair).

  Definition y_auth_model_is (y: nat): iProp Σ :=
    own cl_y_st_name (● Excl' y).

  Definition y_frag_model_is (y: nat): iProp Σ :=
    own cl_y_st_name (◯ Excl' y).
  

  Definition client_inv_impl (st: client_state) : iProp Σ :=
    let (lb, y) := st in
    partial_model_is st ∗
    y_auth_model_is y ∗
    model_state_interp lb (fG := cl_lib_Σ).    
    (* tracked (⌜ ls_tmap lb !! ρlg = Some ∅ ⌝ ∗ partial_free_roles_are {[ ρ_lib ]} ∨ ⌜ ls_tmap lb !! ρlg ≠ Some ∅ ⌝ ∗ partial_free_roles_are {[ ρ_lib ]} *)

  Definition Ns := nroot .@ "client".

  Definition client_inv: iProp Σ :=
    inv Ns (∃ (st: client_state), client_inv_impl st).

End ClientRA.
