From iris.proofmode Require Import tactics.
From trillium.fairness Require Import resources.
From trillium.fairness.heap_lang Require Import notation heap_lang_defs.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness Require Import lm_fair fairness fuel. 
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.comp Require Import tracker lib_interface.
From trillium.fairness.heap_lang Require Export lang.

Close Scope Z_scope.

Section ClientDefs.

  (* Definition lib_gs: gset lib_grole := {[ ρlg ]}. *)

  (* Lemma lib_gs_ne: lib_gs ≠ ∅. *)
  (* Proof. done. Qed. *)
  (* Lemma ρlg_in_lib_gs: ρlg ∈ lib_gs. *)
  (* Proof. done. Qed.  *)

  (* Definition lf := lib_fair _ lib_gs_ne. *)
  (* Context (lf: FairModel).  *)
  Context {lib: LibInterface}. 

  Let lib_st := fmstate libM.
  Let lib_role := fmrole libM.

  (* Let lib_erole := @ext_role _ (@ExtLibLM _ lib_gs_ne).  *)
  Let lib_erole := @ext_role libM (fmrole libM).

  Definition client_state: Type := lib_st * nat.

  Inductive y_role := ρy.
  Definition client_role: Type := lib_erole + y_role.

  Context {ρlg: fmrole libM}. 

  Definition ρ_cl: client_role := inr ρy.
  Definition ρ_lib: client_role := inl $ inl ρlg.
  Definition ρ_ext: client_role := inl $ inr $ env ρlg.

  Inductive client_trans: client_state -> option client_role -> client_state -> Prop :=
  | ct_y_step_3 lb:
    client_trans (lb, 3) (Some ρ_cl) (lb, 2)
  (* TODO: allow arbitrary library's LM roles *)
  | ct_lib_ext lb lb'
      (* (STOP: ¬ role_enabled_model ρlg lb) *)
      (RESET: reset_lib ρlg lb lb')
    :
    client_trans (lb, 2) (Some ρ_ext) (lb', 1)
  | ct_lib_step lb1 lb2 (LIB_STEP: fmtrans _ lb1 (Some ρlg) lb2):
    client_trans (lb1, 1) (Some ρ_lib) (lb2, 1)
  | ct_y_step_1 (lb: fmstate libM)
                (* (LIB_NOSTEP: 0 ∉ live_roles _ lb) *)
                (* (LIB_NOROLES: ls_tmap lb !! ρlg = Some ∅) *)
                (LIB_STOP: ¬ role_enabled_model (ρlg: fmrole libM) lb)
    :
    client_trans (lb, 1) (Some ρ_cl) (lb, 0)
  .


  (* Instance sum_EqDec `{EqDecision A} `{EqDecision B}: *)
  (*   EqDecision (A + B). *)
  (* Proof. *)
  (*   solve_decision. *)
  (* Defined. *)

  (* Global Instance lib_role_EqDec: EqDecision lib_erole. *)
  (* Proof using. *)
  (*   unshelve eapply sum_eq_dec.  *)
  (*   clear ρlg. *)
  (*   destruct lib. destruct libM0. solve_decision. *)
  (* Defined. *)

  (* Global Instance lib_role_Cnt: Countable lib_erole. *)
  (* Proof using. *)
  (*   rewrite /lib_erole. *)
  (*   rewrite /ext_role. *)
  (*   unshelve eapply sum_countable; eauto. *)
  (*   apply env_role_cnt.  *)
  (*   simpl. *)
  (*   pose proof (@libM lib). destruct X.     *)
  (*   apply _.  *)
  (*   destruct lib. apply _. *)
  (* Defined. *)
  
  Instance y_EqDec: EqDecision y_role.
  Proof. by (solve_decision). Qed.

  Instance client_role_EqDec: EqDecision client_role.
  Proof.
  (*   solve_decision. *)
  (* Defined. *)
  Admitted. 

  Global Instance client_role_Cnt: Countable client_role.
  Proof using.
  (*   rewrite /client_role. *)
  (*   unshelve eapply sum_countable; eauto.  *)
  (*   eauto. eapply (inj_countable' (fun _ => ()) (fun _ => ρy)). *)
  (*   by destruct x. *)
  (* Qed. *)
  Admitted. 

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
      + destruct l as [l| ].
        2: by nostep. 
        (* destruct f. *)
        (* pose proof (@lib_LF _ lib_gs_ne). (* why it's not inferred anymore? *) *)
        destruct (decide (l = ρlg)) as [-> | ?].
        2: { nostep. eauto. }
        destruct (lib_step_ex_dec δ_lib ρlg) as [STEP | NOSTEP].
        * left. destruct STEP. eexists. econstructor. eauto. 
        * nostep. simpl in LIB_STEP. eauto. 
      + destruct y.
        destruct (decide (role_enabled_model (ρlg: fmrole libM) δ_lib)).
        2: { left. eexists. by constructor. }
        by nostep. 
    - destruct ρ; [destruct l| ]. 
      1, 3: by nostep. 
      destruct e.
      destruct (decide (i = ρlg)) as [-> | ?]. 
      2: { nostep. eauto. }
      destruct (decide (ρlg ∈ active_exts δ_lib (ExtModel := libEM))).
      + left. 
        apply active_exts_spec in e as [??]. simpl in *. 
        eexists. 
        eapply ct_lib_ext; eauto.
      + nostep. subst. apply n. apply active_exts_spec.
        inversion T. subst. simpl.
        eexists. red. eauto.
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
  Proof using ρlg lib_st lib_role lib_erole lib.
    refine ({|
        fmstate := client_state; 
        fmrole := client_role;
        fmtrans := client_trans;
        live_roles := client_lr;
    |}).
    - pose proof (fmstate_eqdec libM). solve_decision. 
    - intros. eapply client_lr_spec; eauto. 
  Defined.

  Lemma live_roles_1 lb:
    live_roles client_model_impl (lb, 1) =
    if (decide (ρlg ∈ live_roles _ lb))
    then {[ ρ_lib ]}
    (* else if decide (ls_tmap lb !! ρlg = Some ∅) *)
    (*      then {[ ρ_cl ]} *)
    (*      else ∅. *)
    else {[ ρ_cl ]}. 
  Proof.
    simpl. rewrite /client_lr.
    apply leibniz_equiv. rewrite !filter_union.

    erewrite filter_singleton_not with (x := ρ_ext). 
    2: { rewrite bool_decide_eq_false_2; [done| ].
         intros [? STEP]. inversion STEP. }
    rewrite union_empty_r. 

    destruct (decide (ρlg ∈ live_roles libM lb)) as [LR | LR].
    - (* pose proof (LM_live_role_map_notempty _ _ LR) as (?&MAP&?). *)
      erewrite filter_singleton, filter_singleton_not. 
      + set_solver.
      + rewrite bool_decide_eq_false_2; [done| ].
        intros [? STEP]. inversion STEP. subst. set_solver.
      + rewrite bool_decide_eq_true_2; [done| ].
        apply lib_strong_lr in LR as [? ?]. 
        eexists. eapply ct_lib_step. eauto.
    - rewrite filter_singleton_not.
      (* 2: { intros [DOM LIVE]%elem_of_filter. *)
      (*      eapply LM_live_roles_strong in DOM. done. } *)
      2: { rewrite bool_decide_eq_false_2; [done| ].
           intros [? STEP]. inversion STEP. subst. simpl in LIB_STEP.
           destruct LR. apply lib_strong_lr. eauto. }
      rewrite filter_singleton; [set_solver| ].
      apply bool_decide_eq_true_2. eauto.
      eexists. by econstructor.
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
    if (decide (¬ role_enabled_model ρlg lb))
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

    unshelve erewrite set_filter_equiv with (P2 := fun r => r = ρ_ext /\ ¬ role_enabled_model ρlg lb).
    4: reflexivity.
    2: { intros. rewrite bool_decide_eq_true.
         split.
         - intros [? STEP]. inversion STEP. subst. split; eauto.
           intros EN%lib_reset_dom; auto. red. eauto.
         - intros [-> STOP].
           apply lib_reset_dom in STOP as [lb' STEP].
           eexists. econstructor; eauto. }

    rewrite -set_filter_and set_filter_comm.
    erewrite set_filter_equiv.
    3: { rewrite filter_singleton; reflexivity. }
    2: { intros. apply iff_refl. }
    rewrite filter_singleton_if. 
    repeat destruct decide; reflexivity || tauto.
    Unshelve. intros. solve_decision. 
  Qed. 

  Definition client_LSI 
    (s: fmstate client_model_impl)
    (tm: groups_map (M := client_model_impl) (G := locale heap_lang))
    (fm: gmap (fmrole client_model_impl) nat) :=
    (* forall gi, (exists ρi, ls_mapping s.1 !! ρi = Some gi) -> inl $ inl gi ∈ mapped_roles tm. *)
    LSI_True s tm fm. 
    
  Definition client_fl := 15. 
  Definition client_model: LiveModel (locale heap_lang) client_model_impl client_LSI :=
    {| lm_fl _ := client_fl; |}.

  Definition set_pair_RA: ucmra :=
    let setRA := gsetUR (fmrole client_model_impl) in 
    excl_authR (prodUR setRA setRA).

  Class clientPreGS (Σ: gFunctors) := ClientPreGS {
     cl_pre_y_st :> inG Σ (authUR (optionR (exclR natO)));
     (* cl_LM_preΣ :> fairnessGpreS client_model Σ;  *)
     cl_LMΣ :> fairnessGS client_model Σ; 
     libGSPreΣ :> libGSPre Σ;
     cl_trackerΣ :> inG Σ trackerRA;
     cl_set_pairΣ :> inG Σ set_pair_RA;
  }.

  Class clientGS Σ := ClientGS {
    cl_pre_inG :> clientPreGS Σ;    
    cl_y_st_name : gname;
    cl_tracker_name : gname;
    cl_set_pair_name: gname;                          
    libGSΣ :> libGS Σ;
  }.

End ClientDefs. 
