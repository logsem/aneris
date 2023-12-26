From iris.proofmode Require Import tactics.
From trillium.prelude Require Import finitary classical_instances.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness Require Import trace_helpers.
From stdpp Require Import finite.
From trillium.fairness.ext_models Require Import ext_models destutter_ext.
From trillium.fairness.examples.ticketlock Require Import fair_lock group_roles.
From trillium.fairness.heap_lang Require Export lang.
From trillium.fairness Require Import lemmas trace_len fuel lm_fair lm_fair_traces subtrace comp_utils my_omega lm_fairness_preservation lm_fairness_preservation_wip trace_lookup fairness_finiteness.
From trillium.fairness.heap_lang Require Import simulation_adequacy_lm_ext.
Require Import Coq.Logic.Classical.

Close Scope Z_scope.


(* TODO: replace 'Tl' prefixes with 'Fl' *)
Section ClientDefs.
  
  Context {Gtl: Type} `{Countable Gtl}.
  Context (get_Gtls: forall n, { gls: gset Gtl | size gls = n}).
  
  Inductive cl_id := | cl_L | cl_R.
  Definition cl_id_nat c := match c with | cl_L => 0 | cl_R => 1 end. 

  Definition lib_gs: gset Gtl := gls get_Gtls 2.
  Definition ρlg_tl c := ρlg_i get_Gtls 2 (cl_id_nat c).
  Definition ρlg_l := ρlg_tl cl_L.
  Definition ρlg_r := ρlg_tl cl_R.   

  Lemma lib_gs_ρlg:
    lib_gs = {[ ρlg_l; ρlg_r ]}.
  Proof.
    rewrite /lib_gs /ρlg_l /ρlg_r.
    rewrite gls_ρlg. simpl. set_solver.
  Qed. 

  Lemma lib_gs_ne: lib_gs ≠ ∅.
  Proof. rewrite lib_gs_ρlg. set_solver. Qed.

  Lemma ρlg_lr_neq: ρlg_l ≠ ρlg_r.
  Proof.
    intros EQ%ρlg_i_dom_inj; [done|..]. 
    all: simpl; lia.
  Qed. 

  Lemma ρlg_in_lib_gs: forall c, ρlg_tl c ∈ lib_gs.
  Proof. 
    rewrite lib_gs_ρlg. intros c.
    destruct c; set_solver. 
  Qed.

  Lemma ρlg_tl_inj: Inj eq eq ρlg_tl.
  Proof.
    intros ?? EQ%ρlg_i_dom_inj.
    - destruct x, y; done.
    - destruct x; simpl; lia. 
    - destruct y; simpl; lia.
  Qed. 

  Context {Mtl: FairModel}.
  Context {Tl_nexts: forall tl_st, next_states tl_st (M := Mtl)}.
  Context (Mtl_TERM: ∀ mtr: mtrace Mtl, mtrace_fairly_terminating mtr). 

  Context {TlLM': forall gs, LiveModel Gtl Mtl (LSI_groups_fixed gs)}.  
  Context (TlLM_LFP': ∀ gs: gset Gtl, gs ≠ ∅ → LMFairPre (TlLM' gs)).
  (* Context (TlEM': forall gs (NE: gs ≠ ∅), ExtModel (LM_Fair (LF := TlLM_LFP' _ NE))). *)

  Definition TlLM := TlLM' lib_gs. 
  Definition TlLM_LFP := TlLM_LFP' _ lib_gs_ne.
  Definition TlLM_FM := LM_Fair (LF := TlLM_LFP).

  Context `(TlEM_FL: @FairLock TlLM_FM tl_FLP tl_FLE).
  Definition TlEM := FL_EM tl_FLE.
  Context (TlEM_EXT_KEEPS: ext_keeps_asg (ELM := TlEM)).

  (* TODO: reorganize the premises so those below don't depend
     on the client's choice of lib_gs *)
  Let tl_state := fmstate TlLM_FM. 
  Let tl_role := fmrole TlLM_FM.
  Let tl_erole := @ext_role _ TlEM.

  Inductive flag_state := | fs_U | fs_S | fs_S' | fs_O. 
  Definition client_state: Type := tl_state * flag_state.

  (* TODO: cl_id is not used, get rid of it? *)
  Definition client_role: Type := tl_erole + cl_id. 

  Definition ρ_cl c: client_role := inr c. 
  Definition ρ_lib ρlg: client_role := inl $ inl ρlg.
  Definition ρ_ext er: client_role := inl $ inr $ env er (EM := TlEM). 

  
  Inductive client_trans: client_state -> option client_role -> client_state -> Prop :=
  | ct_lib_step tl1 tl2 c flag
        (LIB_STEP: fmtrans TlLM_FM tl1 (Some (ρlg_tl c)) tl2):
      client_trans (tl1, flag) (Some $ ρ_lib (ρlg_tl c)) (tl2, flag)
  (* | ct_flag_US tl  *)
  (*     (LOCK: has_lock_st (ρlg_tl cl_L) tl) *)
  (*     (DIS: ¬ active_st (ρlg_tl cl_L) tl): *)
  (*   client_trans (tl, fs_U) (Some $ ρ_cl cl_L) (tl, fs_S) *)
  | ct_au_L tl (ρlg := ρlg_l)
      (LOCK: has_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl):
    client_trans (tl, fs_U) (Some $ ρ_ext $ flU (ρlg: fmrole TlLM_FM)) (allow_unlock_impl ρlg tl, fs_S)
  | ct_au_R tl fs fs'
      (ρlg := ρlg_r)
      (FS: fs = fs_U /\ fs' = fs_U \/ (fs = fs_S \/ fs = fs_S') /\ fs' = fs_O)
      (LOCK: has_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl):
    client_trans (tl, fs) (Some $ ρ_ext $ flU (ρlg: fmrole TlLM_FM)) (allow_unlock_impl ρlg tl, fs')
  | ct_al_R tl fs fs'
      (ρlg := ρlg_r)
      (CANL: can_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl)
      (* (NO: fs ≠ fs_O) *)
      (FS: fs = fs_U /\ fs' = fs_U \/ fs = fs_S /\ fs' = fs_S')
    :
    client_trans (tl, fs) (Some $ ρ_ext $ flL (ρlg: fmrole TlLM_FM)) (allow_lock_impl ρlg tl, fs')
  .

  Instance flag_state_dec: EqDecision flag_state.
  Proof. solve_decision. Qed.   
  Instance cl_id_dec: EqDecision cl_id.
  Proof. solve_decision. Qed.

  Ltac fin_type_countable all_values :=
    unshelve eapply finite.finite_countable;
    refine {| finite.enum := all_values |};
    [ repeat (apply NoDup_cons; split; [set_solver| ]); apply NoDup_nil_2 |
     by intros x; destruct x; set_solver]. 
       
  Let all_flag_states := [fs_U; fs_S; fs_S'; fs_O]. 
  Instance flag_state_cnt: Countable flag_state.
  Proof. fin_type_countable all_flag_states. Qed. 

  Let all_cl_id := [cl_L; cl_R]. 
  Instance cl_id_cnt: Countable cl_id.
  Proof. fin_type_countable all_cl_id. Qed. 
  
  Lemma all_flag_states_spec: forall f, f ∈ all_flag_states.
  Proof. destruct f; set_solver. Qed.  

  Lemma ρlg_dom_dec (ρlg: Gtl):
    {c | ρlg = ρlg_tl c} + (forall c, ρlg ≠ ρlg_tl c).
  Proof. 
    destruct (decide (ρlg = ρlg_tl cl_L)) as [-> | ?].
    { left. eauto. } 
    destruct (decide (ρlg = ρlg_tl cl_R)) as [-> | ?].
    { left. eauto. }
    right. intros c. by destruct c.
  Qed. 

  Local Instance client_eq: EqDecision client_state.
  Proof.
    pose proof (@LS_eqdec _ _ _ _ _ _ TlLM_LFP).
    solve_decision. 
  Defined.  

  Instance client_step_dec st1 ρ st2:
    Decision (client_trans st1 (Some ρ) st2).
  Proof.
    pose proof (@LS_eqdec _ _ _ _ _ _ TlLM_LFP).
    destruct st1 as [tl_st1 flag1], st2 as [tl_st2 flag2].
    destruct ρ as [er | c].
    2: { right. intros STEP. inversion STEP. }

    destruct er as [ρlg | [ι]]. 
    { destruct (ρlg_dom_dec ρlg).
      2: { right. intros STEP. inversion STEP. subst.
           eapply n; eauto. }
      destruct s as [c ->]. 
      pose proof TlLM_LFP. (* why it's not inferred? *)
      destruct (decide (locale_trans tl_st1 (ρlg_tl c) tl_st2 (LM := TlLM) /\ flag1 = flag2)) as [[STEP ->] | NOSTEP]. 
      + left. 
        eapply ct_lib_step. apply STEP.
      + right. intros STEP. inversion STEP. subst.
        apply ρlg_tl_inj in H3. subst. 
        by eapply NOSTEP. }

    destruct ι.
    - destruct (decide (ρ = ρlg_tl cl_L)) as [-> | ?].
      { destruct (decide (has_lock_st (ρlg_tl cl_L) tl_st1 (M := TlLM_FM) /\ ¬ active_st (ρlg_tl cl_L) tl_st1 (M := TlLM_FM) /\ tl_st2 = allow_unlock_impl ((ρlg_tl cl_L): fmrole TlLM_FM) tl_st1 /\ flag1 = fs_U /\ flag2 = fs_S)) as [(?&?&->&->&->)| ]. 
        * left. eapply ct_au_L; eauto.
        * right. intros STEP. inversion STEP; subst; try tauto.
          by eapply ρlg_lr_neq. }
      destruct (decide (ρ = ρlg_tl cl_R)) as [-> | ?].
      { destruct (decide (has_lock_st (ρlg_tl cl_R) tl_st1 (M := TlLM_FM) /\ ¬ active_st (ρlg_tl cl_R) tl_st1 (M := TlLM_FM) /\ tl_st2 = allow_unlock_impl ((ρlg_tl cl_R): fmrole TlLM_FM) tl_st1 /\ (flag1 = fs_U /\ flag2 = fs_U \/ (flag1 = fs_S \/ flag1 = fs_S') /\ flag2 = fs_O))) as [(?&?&->&?)| ].
        * left. eapply ct_au_R; eauto.
        * right. intros STEP. inversion STEP; subst; try tauto.
          apply n0; set_solver. }
      right. intros STEP. inversion STEP; subst; tauto.
    - destruct (decide (ρ = ρlg_tl cl_R)) as [-> | ?].
      2: { right. intros STEP. inversion STEP; subst; tauto. }
      destruct (decide (can_lock_st (ρlg_tl cl_R) tl_st1 (M := TlLM_FM) /\ ¬ active_st (ρlg_tl cl_R) tl_st1 (M := TlLM_FM) /\ tl_st2 = allow_lock_impl ((ρlg_tl cl_R): fmrole TlLM_FM) tl_st1 /\ (flag1 = fs_U /\ flag2 = fs_U \/ flag1 = fs_S /\ flag2 = fs_S'))) as [(?&?&->&?) | NOSTEP].
      + left. econstructor; eauto.
      + right. intros STEP. inversion STEP; subst. tauto.
  Qed.

  Lemma client_model_step_fin (s1 : client_state):
    {nexts: list (client_state) | forall s2 oρ, client_trans s1 oρ s2 -> s2 ∈ nexts}.
  Proof.
    destruct s1 as (δ_lib, f).
    pose proof (Tl_nexts (ls_under δ_lib)) as [ie_lib IE_LIB].
    pose proof (role_LM_step_dom_all δ_lib ((ls_under δ_lib) :: ie_lib) (elements lib_gs) (LM := TlLM)) as STEPS_LIB.

    set nexts_lib := (map fst (enumerate_next δ_lib ((ls_under δ_lib) :: ie_lib) (elements lib_gs) (LM := TlLM))).
    fold nexts_lib in STEPS_LIB.
    
    set (nexts_tl :=
           δ_lib :: nexts_lib ++
           map (flip allow_unlock_impl δ_lib) (elements lib_gs) ++
           map (flip allow_lock_impl δ_lib) (elements lib_gs)). 
    set nexts := f ← all_flag_states; δ ← nexts_tl; mret (δ, f). 
    
    exists nexts. 
    intros [δ' f'] oρ TRANS. simpl in TRANS.
    subst nexts. repeat setoid_rewrite elem_of_list_bind.
    setoid_rewrite elem_of_list_ret.
    eexists. split; [| by apply all_flag_states_spec].
    eexists. split; eauto.
    subst nexts_tl. 
    inversion TRANS; subst.
    - apply elem_of_list_further, elem_of_app. left.
      simpl in LIB_STEP. destruct LIB_STEP as (ℓ & LIB_STEP & MATCH). 
      apply elem_of_list_In. eapply STEPS_LIB; eauto.
      2: { rewrite list_to_set_elements_L. by apply δ'. }
      apply elem_of_cons. 
      edestruct @locale_trans_fmtrans_or_eq as [[? FM] | EQ]. 
      { eexists. eauto. }
      + right. eauto.
      + by left.
    (* - apply elem_of_cons. tauto. *)
    - apply elem_of_list_further, elem_of_app. right.
      apply elem_of_app. left. rewrite lib_gs_ρlg. 
      apply elem_of_list_fmap. eexists. split; eauto.
      apply elem_of_elements. set_solver.
    - apply elem_of_list_further, elem_of_app. right.
      apply elem_of_app. left. rewrite lib_gs_ρlg.
      apply elem_of_list_fmap. eexists. split; eauto.
      apply elem_of_elements. set_solver.
    - apply elem_of_list_further, elem_of_app. right.
      apply elem_of_app. right. rewrite lib_gs_ρlg.
      apply elem_of_list_fmap. eexists. split; eauto.
      apply elem_of_elements. set_solver.
  Qed. 

  (* TODO: generalize this derivation *)
  Instance client_step_ex_dec (st: client_state) (ρ: client_role):
    Decision (exists st', client_trans st (Some ρ) st').
  Proof.
    eapply Decision_iff_impl with (P := Exists (fun st' => client_trans st (Some ρ) st') (proj1_sig $ client_model_step_fin st)).
    2: { solve_decision. }
    rewrite List.Exists_exists. apply exist_proper. intros st'.
    rewrite and_comm. apply iff_and_impl_helper.
    destruct client_model_step_fin; simpl in *.
    rewrite -elem_of_list_In. eauto.
  Qed. 

  Let all_roles: gset client_role :=
      list_to_set $
      f ← [ρ_lib ∘ ρlg_tl; ρ_ext ∘ flU ∘ ρlg_tl; ρ_ext ∘ flL ∘ ρlg_tl; ρ_cl];
      c ← [cl_L; cl_R];
      mret (f c).

  Definition client_lr (st: client_state): gset (client_role) :=
    filter (fun r => (@bool_decide _ (client_step_ex_dec st r) = true)) all_roles. 

  Lemma client_lr_spec: ∀ (s : client_state) (ρ : client_role),
      (exists s', client_trans s (Some ρ) s') <-> ρ ∈ client_lr s.
  Proof.
    intros ??. rewrite /client_lr.
    rewrite elem_of_filter. rewrite @bool_decide_eq_true.
    rewrite iff_and_impl_helper; [done| ]. 
    intros [? STEP]. apply elem_of_list_to_set.
    simpl. inversion STEP; subst. 
    { destruct c; set_solver. }
    all: set_solver.
  Qed.
    
  Definition client_model_impl: FairModel.
  Proof.
    refine ({|
        fmstate := client_state; 
        fmrole := client_role;
        fmtrans := client_trans;
        live_roles := client_lr;
    |}).
    - pose proof (@inhLM _ _ _ _ _ _ TlLM_LFP) as [δ]. 
      apply (populate (δ, fs_U)).
    - intros. apply client_lr_spec. eauto.
  Defined.

  Definition project_tl_trace (tr: mtrace client_model_impl): 
    elmftrace (ELM := TlEM) :=
    project_nested_trace fst 
      (fun ℓ => match ℓ with | Some (inl l) => Some $ Some l | _ => None end)                         
      tr. 
    
  Local Ltac unfold_slm H :=
    match type of H with 
    | step_label_matches ?step ?P => destruct H as (?&?&?&->&?Pstep)
    end.

  Definition is_tl_step (step: model_trace_step client_model_impl) :=
    step_label_matches step (fun ρ => exists ρlg, Some $ inl ρlg = ρ). 

  (* TODO: show that all TL states used in client trace are WF;
     add a "step belongs to trace" premise to nested_trace_construction *)
  Lemma ALWAYS_tl_state_wf (tl: tl_state): state_wf tl.
  Proof. Admitted. 
  
  Lemma tl_trace_construction (tr: mtrace client_model_impl)
    (VALID: mtrace_valid tr)
    (TL_STEPS: ∀ i res, tr !! i = Some res → is_tl_step res \/ is_end_state res):
    lm_model_traces_match
      (transA := @ext_trans _ TlEM)
      ((option_fmap _ _ inl): option (@ext_role _ TlEM) -> option $ fmrole client_model_impl)
      (fun c δ_lib => fst c = δ_lib)
      tr (project_tl_trace tr).
  Proof.
    do 2 red.
    rewrite /out_A_labels_match. simpl.
    eapply traces_match_impl; cycle 1.
    { intros *. intros X. apply X. }
    { eapply nested_trace_construction.
      { done. }
      { intros * ITH. apply TL_STEPS in ITH as [LIB | ?]; [| tauto].
        red in LIB. unfold_slm LIB. destruct Pstep as [? <-].
        left. do 3 eexists. eauto. }
      intros. destruct ℓ; [| done]. destruct c; [| done].
      inversion H1. subst.
      inversion H0; subst; simpl in *.
      - econstructor. auto.
      - econstructor. simpl.
        eapply allows_unlock_impl_spec; auto.
        apply ALWAYS_tl_state_wf.
      - econstructor. simpl. 
        eapply allows_unlock_impl_spec; auto.
        apply ALWAYS_tl_state_wf.
      - econstructor. simpl. 
        eapply allows_lock_impl_spec; auto. }
    simpl. intros. destruct ℓ1; [| done]. destruct c; [| done].
    by inversion H0.
  Qed.

  Definition is_UU_step (step: model_trace_step client_model_impl) :=
    exists tl1 oℓ tl2, step = ((tl1, fs_U), Some (oℓ, (tl2, fs_U))). 

  Definition is_init_cl_state (st: client_state) :=
    (forall c, let ρlg := ρlg_tl c in can_lock_st ρlg st.1 /\ active_st ρlg st.1) /\
    st.2 = fs_U.

 
  Definition client_LSI (s: client_state)
    (tm: groups_map (M := client_model_impl) (G := locale heap_lang))
    (_: gmap (fmrole client_model_impl) nat) :=
    forall gi, (exists ρi, ls_mapping s.1 !! ρi = Some gi) -> inl $ inl gi ∈ mapped_roles tm.
    
  Definition client_fl := 15. 
  Definition client_model: LiveModel (locale heap_lang) client_model_impl client_LSI :=
    {| lm_fl _ := client_fl; |}.  

  Local Instance inh_client: Inhabited (lm_ls client_model).
  Proof.
    (* pose proof (LSI_gf_ls_inh (lib_model lib_gs) lib_gs_ne) as [δ].   *)
    pose proof (@inhLM _ _ _ _ _ _ TlLM_LFP) as [tl_st].  
    assert (Inhabited (locale heap_lang)) as [τ] by apply _.
    apply populate.
    refine {| ls_under := (tl_st, fs_U): fmstate client_model_impl;
              ls_fuel := (gset_to_gmap 0 all_roles);
              ls_tmap := {[ τ := all_roles ]}; |}.
    - rewrite dom_gset_to_gmap. simpl. set_solver.   
    - intros ρ. 
      rewrite dom_gset_to_gmap. 
      setoid_rewrite lookup_singleton_Some.
      etrans.
      2: { symmetry. apply ex_det_iff with (a := τ). by intros ? (?&[??]&?). } 
      etrans.
      2: { symmetry. eapply ex_det_iff. intros ? ([??]&?). symmetry. apply H1. }
      tauto.
  - red. intros * NEQ TM1%lookup_singleton_Some TM2%lookup_singleton_Some.
    destruct TM1, TM2. congruence.
  - red. intros g [ρ MAP]. simpl in MAP. 
    rewrite /mapped_roles. rewrite map_img_singleton_L flatten_gset_singleton.
    apply ls_mapping_tmap_corr in MAP as (?&TM&?).
    forward eapply (ls_inv tl_st g) as IN.
    { eapply @elem_of_dom; [apply _| ]. eauto. }
    rewrite lib_gs_ρlg in IN.
    rewrite /all_roles. set_solver.
  Qed.

  Instance client_LSI_dec: 
    forall st tm fm, Decision (client_LSI st tm fm).
  Proof. 
    intros [tl_st ?] tm fm. rewrite /client_LSI. simpl. 
    eapply Decision_iff_impl with
      (P := Forall 
              (fun g => Exists 
                       (fun ρ => ls_mapping tl_st !! ρ = Some g) 
                       (elements $ dom $ ls_mapping tl_st) -> inl (inl g) ∈ mapped_roles tm)
              (elements lib_gs)).
    2: { solve_decision. }
    
    rewrite -set_Forall_elements.
    apply forall_proper. intros g.
    rewrite curry_uncurry_prop. apply ZifyClasses.impl_morph; [| done].
    rewrite and_comm. rewrite iff_and_impl_helper.
    2: { intros (?&?&IN)%List.Exists_exists.
         apply (ls_inv tl_st). 
         apply ls_mapping_tmap_corr in IN as (?&IN&?).
         eapply @elem_of_dom; eauto. apply _. }
    rewrite List.Exists_exists.
    apply exist_proper. intros ρ. 
    rewrite and_comm. apply iff_and_impl_helper.
    intros. apply elem_of_list_In, elem_of_elements. by apply elem_of_dom.
  Qed. 

  Instance client_lm_dec_ex_step:
    ∀ τ δ1, Decision (∃ δ2, locale_trans δ1 τ δ2 (LM := client_model)).
  Proof. 
    intros.
    pose proof (client_model_step_fin (ls_under δ1)) as [nexts NEXTS]. 
    apply locale_trans_ex_dec_fin with (steps := nexts).
    { intros. apply elem_of_list_In. eauto. }
    intros. eexists. eapply rearrange_roles_spec.
    Unshelve.
    + exact client_model. 
    + red. intros ? [??].
      erewrite <- mapped_roles_dom_fuels_gen.
      2: { apply rrm_tmap_fuel_same_doms. }
      pose proof (ls_inv δ2) as LSI2. red in LSI2. 
      specialize (LSI2 _ ltac:(eauto)).
      by rewrite -mapped_roles_dom_fuels in LSI2. 
  Qed. 
    
  Local Instance client_LF: LMFairPre client_model.
  esplit; apply _.
  Defined.

  Definition client_LM_trace_exposing :=
    outer_LM_trace_exposing TlEM_EXT_KEEPS
      ((inl ∘ inl): Gtl -> fmrole client_model_impl) (option_fmap _ _ inl) (λ st tl_st, st.1 = tl_st)
      (LMo := client_model)
  .
 

  (* TODO: move*)
  Lemma model_step_keeps_others_preds st1 ρ st2 ρ'
    (LIB_STEP: fmtrans TlLM_FM st1 (Some ρ) st2)
    (NEQ: ρ' ≠ ρ):
    forall P, P ∈ [has_lock_st ρ'; can_lock_st ρ'; active_st ρ'] ->
         P st2 <-> P st1.
  Proof using. Admitted.

  
  (* TODO: move*)
  Lemma ext_step_keeps_others_preds st1 ρ st2 ρ'
    mkEI
    (MK: mkEI ∈ [flU; flL])
    (LIB_STEP: @ETs _ (FL_EM tl_FLE) (mkEI ρ) st1 st2)
    (NEQ: ρ' ≠ ρ):
    forall P, P ∈ [has_lock_st ρ'; can_lock_st ρ'; active_st ρ'] ->
         P st2 <-> P st1.
  Proof using. Admitted.

  (* TODO: is it possible to get rid of this active_st - live_roles duplication? *)
  (* TODO: move *)
  Lemma not_active_st_not_live tl_st ρlg:
    ¬ active_st ρlg tl_st -> ρlg ∉ live_roles _ tl_st.
  Proof. Admitted. 

  (* TODO: move *)
  Lemma has_lock_st_excl tl_st ρlg1 ρlg2:
    has_lock_st ρlg1 tl_st -> has_lock_st ρlg2 tl_st -> ρlg1 = ρlg2.
  Proof. Admitted. 

  (* TODO: move *)
  Lemma can_has_lock_incompat tl_st ρlg:
    has_lock_st ρlg tl_st -> can_lock_st ρlg tl_st -> False. 
  Proof. Admitted. 

  (* TODO: move, introduce more uniform treatment of ETs pre- and postconditions *)
  Lemma allows_unlock_spec tl_st1 ρlg tl_st2:
    allows_unlock ρlg tl_st1 tl_st2 ->
    has_lock_st ρlg tl_st1 /\ ¬ active_st ρlg tl_st1 /\
    has_lock_st ρlg tl_st2 /\ active_st ρlg tl_st2. 
  Proof. Admitted. 

  (* TODO: move, rename *)
  Lemma kept2:
  @label_kept_state client_model_impl
    (@role_enabled_model client_model_impl (ρ_ext (@flU TlLM_FM ρlg_r)))
    (ρ_ext (@flU TlLM_FM ρlg_r)). 
  Proof.
    red. intros [tl_st f] ? [tl_st' f'] **. simpl in STEP.
    destruct oℓ' as [ρ | ].
    2: { by inversion STEP. }
    assert (ρ ≠ ρ_ext (flU (ρlg_r: fmrole TlLM_FM))) as NEQ' by congruence.
    
    assert ((f ≠ fs_O) /\
              has_lock_st ρlg_r tl_st /\ ¬ active_st ρlg_r tl_st) as PREρlg.
    { red in Ps. simpl in Ps. apply client_lr_spec in Ps as [? STEP'].
      inversion STEP'; subst; repeat split; try tauto.
      { congruence. }
      clear -FS. set_solver. }
    
    pose proof (ct_au_R tl_st' f' (match f' with | fs_U => fs_U | _ => fs_O end)) as STEPr.
    simpl in STEPr. rewrite !curry_uncurry_prop in STEPr.
    red. simpl. apply client_lr_spec.
    eexists. apply STEPr. apply and_assoc. split.
    { apply proj1 in PREρlg.
      inversion STEP; subst; try tauto. 
      all: destruct f'; tauto. }
    inversion STEP; subst.
    - split.
      + eapply model_step_keeps_others_preds with (ρ' := ρlg_r); eauto.
        { rewrite /ρlg_r. intros EQ%ρlg_i_dom_inj.
          2: { simpl; lia. }
          2: { destruct c; simpl; lia. }
          assert (c = cl_R) as -> by (by destruct c). 
          eapply not_active_st_not_live; eauto. apply PREρlg.
          by eapply fm_live_spec. }
        { set_solver. }
        apply PREρlg.
      + 
        (* TODO: unify with proof above *)
        forward eapply model_step_keeps_others_preds with (ρ' := ρlg_r) (P := active_st (ρlg_r: fmrole TlLM_FM)); eauto.
        { rewrite /ρlg_r. intros EQ%ρlg_i_dom_inj.
          2: { simpl; lia. }
          2: { destruct c; simpl; lia. }
          assert (c = cl_R) as -> by (by destruct c). 
          eapply not_active_st_not_live; eauto. apply PREρlg.
          by eapply fm_live_spec. }
        { set_solver. }
        intros EQUIV%not_iff_compat. apply EQUIV.
        apply PREρlg.
    - edestruct ρlg_lr_neq. eapply has_lock_st_excl; eauto. apply PREρlg.
    - done.
    - edestruct can_has_lock_incompat; eauto. apply PREρlg.
  Qed.
        
  (* (* TODO: move, rename *) *)
  (* Lemma kept1: *)
  (* @label_kept_state client_model_impl *)
  (*   (@role_enabled_model client_model_impl (ρ_cl cl_L))  *)
  (*   (ρ_cl cl_L).  *)
  (* Proof. *)
  (*   red. intros [tl_st f] ? [tl_st' f'] **. simpl in STEP. *)
  (*   destruct oℓ' as [ρ | ]. *)
  (*   2: { by inversion STEP. } *)
    
  (*   assert (f = fs_U /\ has_lock_st ρlg_l tl_st /\ ¬ active_st ρlg_l tl_st) as [-> PREρlg]. *)
  (*   { red in Ps. simpl in Ps. apply client_lr_spec in Ps as [? STEP']. *)
  (*     inversion STEP'; subst; tauto. } *)
    
  (*   pose proof (ct_flag_US tl_st') as STEPr. *)
  (*   pattern fs_U in STEPr. erewrite (forall_eq_gen _ fs_U) in STEPr.  *)
  (*   simpl in STEPr. repeat setoid_rewrite curry_uncurry_prop in STEPr. *)
  (*   red. simpl. apply client_lr_spec. *)
  (*   eexists. apply STEPr. *)
  (*   apply and_assoc. *)
  (*   inversion STEP; subst. *)
  (*   - split; [done| ]. split. *)
  (*     + eapply model_step_keeps_others_preds with (ρ' := ρlg_l); eauto. *)
  (*       { rewrite /ρlg_l. intros EQ%ρlg_i_dom_inj. *)
  (*         2: { simpl; lia. } *)
  (*         2: { destruct c; simpl; lia. } *)
  (*         assert (c = cl_L) as -> by (by destruct c). *)
  (*         eapply not_active_st_not_live; eauto. apply PREρlg. *)
  (*         by eapply fm_live_spec. } *)
  (*       { set_solver. } *)
  (*       apply PREρlg. *)
  (*     + *)
  (*       (* TODO: unify with proof above *) *)
  (*       forward eapply model_step_keeps_others_preds with (ρ' := ρlg_l) (P := active_st (ρlg_l: fmrole TlLM_FM)); eauto. *)
  (*       { rewrite /ρlg_l. intros EQ%ρlg_i_dom_inj. *)
  (*         2: { simpl; lia. } *)
  (*         2: { destruct c; simpl; lia. } *)
  (*         assert (c = cl_L) as -> by (by destruct c). *)
  (*         eapply not_active_st_not_live; eauto. apply PREρlg. *)
  (*         by eapply fm_live_spec. } *)
  (*       { set_solver. } *)
  (*       tauto.  *)
  (*   - congruence.  *)
  (*   - edestruct ρlg_lr_neq. eapply has_lock_st_excl; eauto. apply PREρlg. *)
  (*   - split; [done| ]. *)
  (*     split. *)
  (*     + eapply ext_step_keeps_others_preds with (mkEI := flL) (ρ' := ρlg_l); eauto. *)
  (*       { set_solver. } *)
  (*       1: { eapply allows_lock_impl_spec; eauto. } *)
  (*       3: by apply PREρlg. *)
  (*       { by intros ?%ρlg_lr_neq. } *)
  (*       set_solver. *)
  (*     + forward eapply ext_step_keeps_others_preds with (ρ' := ρlg_l) (mkEI := flL) (P := active_st (ρlg_l: fmrole TlLM_FM)); eauto. *)
  (*       { set_solver. } *)
  (*       1: { eapply allows_lock_impl_spec; eauto. } *)
  (*       { by intros ?%ρlg_lr_neq. } *)
  (*       { set_solver. } *)
  (*       tauto.  *)
  (* Qed. *)

  Lemma kept1:
  @label_kept_state client_model_impl
    (@role_enabled_model client_model_impl (ρ_ext (@flU TlLM_FM ρlg_l)))
    (ρ_ext (@flU TlLM_FM ρlg_l)).
  Proof.
    red. intros [tl_st f] ? [tl_st' f'] **. simpl in STEP.
    destruct oℓ' as [ρ | ].
    2: { by inversion STEP. }
    assert (ρ ≠ ρ_ext (flU (ρlg_l: fmrole TlLM_FM))) as NEQ' by congruence.
    
    assert (f = fs_U /\ has_lock_st ρlg_l tl_st /\ ¬ active_st ρlg_l tl_st) as [-> PREρlg].
    { red in Ps. simpl in Ps. apply client_lr_spec in Ps as [? STEP'].
      inversion STEP'; subst; eauto.
      edestruct ρlg_lr_neq; eauto. }
    
    pose proof (ct_au_L tl_st') as STEPr.
    pattern fs_U in STEPr. erewrite (forall_eq_gen _ fs_U) in STEPr.
    simpl in STEPr. repeat setoid_rewrite curry_uncurry_prop in STEPr.
    red. simpl. apply client_lr_spec.
    eexists. apply STEPr. apply and_assoc.
    inversion STEP; subst.
    - split; [done| ]. 
      split.
      + eapply model_step_keeps_others_preds with (ρ' := ρlg_l); eauto.
        { rewrite /ρlg_l. intros EQ%ρlg_i_dom_inj.
          2: { simpl; lia. }
          2: { destruct c; simpl; lia. }
          assert (c = cl_L) as -> by (by destruct c). 
          eapply not_active_st_not_live; eauto. apply PREρlg.
          by eapply fm_live_spec. }
        { set_solver. }
        apply PREρlg.
      + 
        (* TODO: unify with proof above *)
        forward eapply model_step_keeps_others_preds with (ρ' := ρlg_l) (P := active_st (ρlg_l: fmrole TlLM_FM)); eauto.
        { rewrite /ρlg_l. intros EQ%ρlg_i_dom_inj.
          2: { simpl; lia. }
          2: { destruct c; simpl; lia. }
          assert (c = cl_L) as -> by (by destruct c). 
          eapply not_active_st_not_live; eauto. apply PREρlg.
          by eapply fm_live_spec. }
        { set_solver. }
        intros EQUIV%not_iff_compat. apply EQUIV.
        apply PREρlg.
    - done. 
    - edestruct ρlg_lr_neq. eapply has_lock_st_excl; eauto. apply PREρlg.
    - destruct FS as [[? ->] | [[=] ?]]. 
      split; [done| ].
      split.
      + eapply ext_step_keeps_others_preds with (mkEI := flL) (ρ' := ρlg_l); eauto.
        { set_solver. }
        1: { eapply allows_lock_impl_spec; eauto. }
        3: by apply PREρlg.
        { by intros ?%ρlg_lr_neq. }
        set_solver.
      + forward eapply ext_step_keeps_others_preds with (ρ' := ρlg_l) (mkEI := flL) (P := active_st (ρlg_l: fmrole TlLM_FM)); eauto.
        { set_solver. }
        1: { eapply allows_lock_impl_spec; eauto. }
        { by intros ?%ρlg_lr_neq. }
        { set_solver. }
        tauto.
  Qed.


  (* TODO: simplify MATCH *)
  Lemma tl_subtrace_fair lmtr (tr str: mtrace client_model_impl) k
    (OUTER_CORR : client_LM_trace_exposing lmtr tr)
    (LEN1': trace_len_is str NOinfinity)
    (SUB1 : subtrace tr k NOinfinity = Some str)
    (MATCH : @lm_model_traces_match Gtl EqDecision0 H Mtl
            (@LSI_groups_fixed Gtl EqDecision0 H Mtl lib_gs) 
            (TlLM' lib_gs) (option (@ext_role TlLM_FM TlEM))
            (@ext_trans TlLM_FM TlEM) client_model_impl
            (option_fmap (@ext_role TlLM_FM TlEM)
               (sum (@ext_role TlLM_FM TlEM) cl_id)
               (@inl (@ext_role TlLM_FM TlEM) cl_id))
            (fun (c : fmstate client_model_impl)
               (δ_lib : @lm_ls Gtl Mtl EqDecision0 H
                          (@LSI_groups_fixed Gtl EqDecision0 H Mtl lib_gs)
                          (TlLM' lib_gs)) =>
             @eq tl_state (@fst tl_state flag_state c) δ_lib) str
            (project_tl_trace str)):
  inner_fair_ext_model_trace (project_tl_trace str).
  Proof.
    forward eapply outer_exposing_subtrace; eauto.
    intros [? EXP'].       
    assert (∀ ρ, fair_by_group (ELM_ALM TlEM_EXT_KEEPS) ρ (project_tl_trace str)) as TL_FAIR'.
    { eapply inner_LM_trace_fair_aux_group.
      - apply _.
      - done.
      - by apply EXP'. 
      - simpl. intros ?? [=<-].
        by apply EXP'.
      - by apply EXP'.
      - subst. eapply infinite_trace_equiv; eauto. 
      - by apply MATCH. }
    red. red. intros ? [g ->]. simpl in g.
    red. red. intros n ENg. simpl in ENg.
    
    apply pred_at_trace_lookup in ENg as (?&NTH&ENg).
    red in ENg. simpl in ENg. rewrite /ext_live_roles in ENg.
    apply elem_of_union in ENg as [ENg | ?].
    2: { set_solver. }
    apply elem_of_map in ENg as (?&[=<-]&ENg).
    
    specialize (TL_FAIR' g). do 2 red in TL_FAIR'.
    specialize (TL_FAIR' n). specialize_full TL_FAIR'.
    { apply pred_at_trace_lookup. eexists. split; eauto.
      apply LM_live_roles_strong in ENg as [? STEP].
      eapply locale_trans_ex_role; eauto. }
    destruct TL_FAIR' as [m FAIR']. exists m.
    eapply pred_at_impl; [| apply FAIR'].
    intros.
    red in H0. red. destruct H0.
    2: { right. simpl. destruct H0 as (er & -> & <-).
         eexists. split; eauto. done. }
    left. intros EN. apply H0.
    red in EN. simpl in EN. rewrite /ext_live_roles in EN.
    apply elem_of_union in EN as [EN | ?].
    2: { set_solver. }
    apply elem_of_map in EN as (?&[=<-]&EN).
    apply LM_live_roles_strong in EN as [? STEP].
    eapply locale_trans_ex_role; eauto.  
  Qed. 
    

  Lemma first_tl_subtrace_finite
  (tr : mtrace client_model_impl)
  (lmtr : lm_fair_traces.lmftrace)
  (OUTER_CORR : client_LM_trace_exposing lmtr tr)
  (VALID : mtrace_valid tr)
  (FAIR : ∀ ρ, fair_model_trace ρ tr)
  (len : nat_omega)
  (LEN : trace_len_is tr len)
  (i'_s : nat_omega)
  (STEPs : ∀ i res, NOmega.lt (NOnum i) i'_s → tr !! i = Some res → is_UU_step res)
  (LEN1 : NOmega.le i'_s len):
    exists i_s, i'_s = NOnum i_s.
  Proof.    
    destruct (decide (i'_s = NOnum 0)) as [| NZ1]. 
    { eauto. }
      
    forward eapply (subtrace_len tr _ 0 i'_s) as SUB1; eauto.
    { lia_NO' i'_s. destruct n; try lia. done. } 
    destruct SUB1 as (str & SUB1 & LEN1').
    rewrite NOmega.sub_0_r in LEN1'. 
    
    forward eapply (tl_trace_construction str) as MATCH. 
    { subst. eapply (subtrace_valid tr); eauto. }
    { subst. intros i res RES.
      
      (* TODO: make this 'P \/ is_end_state' a lemma? *)
      pose proof (trace_lookup_trichotomy _ _ LEN1' i) as [TL | [END | NO]]; cycle 1. 
      { right.
        destruct END as (?&END&->).
        rewrite RES in END. inversion END. subst.
        eexists. eauto. } 
      { rewrite RES in NO. by apply proj1 in NO. }
      left. 
      destruct TL as (?&?&?&TL&dom). rewrite RES in TL. inversion TL. subst.
      apply subtrace_lookup with (k := i) in SUB1.
      2: { lia_NO i'_s. }
      pose proof RES as RES'.
      rewrite SUB1 in RES. simpl in RES.
      pose proof RES as UUres.
      apply STEPs in UUres.
      2: { eapply trace_lookup_dom; eauto. }
      destruct UUres as (?&?&?&[=]). subst.
      eapply trace_valid_steps' in RES; eauto.
      inversion RES; subst. 
      all: by do 3 eexists; eauto. }
    
    destruct (decide (i'_s = NOinfinity)) as [INF| ]. 
    2: { destruct i'_s; set_solver. }
    
    forward eapply (lock_progress (project_tl_trace str) (ρlg_tl cl_L) 0 (trfirst str).1).
    { by eapply traces_match_valid2. }
    { intros.
      apply ALWAYS_tl_state_wf. }
    { subst i'_s. eapply tl_subtrace_fair; eauto. }
    { rewrite state_lookup_0. by rewrite project_nested_trfirst. }
    { admit. (* assume this for the initial state *) }
    { admit. (* assume this for the initial state *) }
    { red. intros ρlg j tl_st **. specialize (AFTER ltac:(lia)).
      destruct AFTER as [NEQ NO_L_LOCKS].
      assert (ρlg = ρlg_r) as ->.
      { admit. (* need to ensure that we only operate with lib_gs roles *) }
      destruct (decide (active_st (ρlg_r: fmrole TlLM_FM) tl_st)) as [| DIS]. 
      { eauto. }
      eapply traces_match_state_lookup_2 in JTH as (st&JTH&EQ).
      2: by apply MATCH.
      destruct st as [? f]. simpl in EQ. subst.
      assert (f = fs_U) as ->.
      { apply trace_state_lookup_simpl' in JTH as (step&JTH&ST).
        erewrite subtrace_lookup in JTH; eauto.
        2: done.
        simpl in JTH. apply STEPs in JTH; [| done].
        destruct JTH as (?&?&?&[=]). subst. by inversion ST. }
      
      pose proof SUB1 as FAIR1. eapply fair_by_subtrace in FAIR1; eauto.
      Unshelve. 2: exact (ρ_ext $ flU (ρlg_r: fmrole TlLM_FM)).
      forward eapply kept_state_fair_step.
      5: by apply JTH.
      3: { intros ? P. apply P. }
      4: { simpl. red. eapply fm_live_spec.
           eapply ct_au_R; eauto. }
      { eapply (subtrace_valid tr); eauto. }
      { apply kept2. }
      { eapply fair_by_subtrace; eauto. }
      
      clear dependent tl_st. 
      simpl. intros (k & st & PROPk & KTH & ENk).
      red in PROPk. destruct PROPk as [[LE STEP] MINk].
      apply trace_label_lookup_simpl' in STEP as (? & st' & KTH').
      exists (k + 1), st'.1. repeat split.
      2: lia.
      { apply state_label_lookup in KTH' as (?&KTH'&?).
        eapply traces_match_state_lookup_1 in KTH' as (? & KTH' & EQ).
        2: { eauto. }
        rewrite KTH'. congruence. }
      
      eapply trace_state_lookup_simpl in KTH; eauto. subst.
      eapply trace_valid_steps' in KTH'.
      2: { eapply subtrace_valid in SUB1; eauto. }
      inversion KTH'; subst.
      { by apply ρlg_lr_neq in H2. }
      simpl. eapply allows_unlock_spec; eauto.
      apply allows_unlock_impl_spec; eauto.
      apply ALWAYS_tl_state_wf. }
    
    intros (k & tl_st & ? & KTH & LOCKl & DISl). 
    eapply traces_match_state_lookup_2 in KTH as (s & KTH & EQ); [| by eauto].
    destruct s as [? f]. simpl in EQ. subst.
    assert (f = fs_U) as ->.
    { apply trace_state_lookup_simpl' in KTH as (step&KTH&ST).
      erewrite subtrace_lookup in KTH; eauto.
      2: done.
      simpl in KTH. apply STEPs in KTH; [| done].
      destruct KTH as (?&?&?&[=]). subst. by inversion ST. }
    
    forward eapply kept_state_fair_step.
    5: by apply KTH.
    3: { intros ? P. apply P. }
    4: { simpl. red. eapply fm_live_spec.
         eapply ct_au_L; eauto. }
    { eapply (subtrace_valid tr); eauto. }
    { apply kept1. }
    { eapply fair_by_subtrace; eauto. }
    
    intros (j & st & PROPj & JTH & ENj).
    clear dependent tl_st. 
    red in PROPj. destruct PROPj as [[LE STEP] MINj].
    apply trace_label_lookup_simpl' in STEP as (? & st' & JTH').
    erewrite subtrace_lookup in JTH'; eauto.
    2: { done. }
    simpl in JTH'.
    pose proof JTH' as STEP. eapply trace_valid_steps' in STEP; eauto.
    simpl in STEP. inversion STEP; subst.
    2: { edestruct ρlg_lr_neq; eauto. }
    apply STEPs in JTH'; [| done].
    destruct JTH' as (?&?&?&[=]). 
  Admitted.


  Definition fs_le f1 f2: Prop :=
    let fn := 
      fun fs => 
        match fs with | fs_U => 3 | fs_S => 2 | fs_S' => 1 | fs_O => 0 end in
    fn f1 <= fn f2.
  Local Hint Unfold fs_le. 

  Instance fs_le_TO: TotalOrder fs_le.
  Proof. 
    split. 
    - split.
      + split.
        * intros [| | |]; red; lia.
        * unfold fs_le. intros [| | |][| | |][| | |]; lia.
      + unfold fs_le. intros [| | |][| | |]; try lia.
        all: congruence.
    - red. unfold fs_le, strict. intros [| | |][| | |]; simpl; try lia.
      all: tauto.
  Qed. 

  Lemma client_trans_fs_mono st1 ρ st2
    (STEP: client_trans st1 ρ st2):
    fs_le st2.2 st1.2.
  Proof. 
    inversion STEP; subst; simpl.
    all: try reflexivity; auto.
    - destruct FS as [[-> ->] | [[ ->| ->] ->]]; auto.
    - destruct FS as [[-> ->] | [-> ->]]; auto.
  Qed.
  
  Lemma client_trace_fs_mono (tr: mtrace client_model_impl) i j si sj
    (VALID : mtrace_valid tr)
    (LE: i <= j)
    (ITH: tr S!! i = Some si) (JTH: tr S!! j = Some sj):
    fs_le sj.2 si.2.
  Proof. 
    apply Nat.le_sum in LE as [d ->].
    generalize dependent sj. induction d.
    { intros. rewrite Nat.add_0_r in JTH. rewrite ITH in JTH. by inversion JTH. }
    rewrite Nat.add_succ_r -Nat.add_1_r. intros sj' JTH'. 
    pose proof (trace_has_len tr) as [len LEN].  
    destruct (proj2 (trace_lookup_dom_strong _ _ LEN (i + d))) as (sj & ρ & sj'_ & JTH). 
    { eapply state_lookup_dom; eauto. }
    apply state_label_lookup in JTH as (JTH & JTH'_ & JTHρ).
    rewrite JTH' in JTH'_. inversion JTH'_. subst sj'_. clear JTH'_.   
    specialize (IHd _ JTH). etrans; [| apply IHd].
    eapply client_trans_fs_mono.
    eapply trace_valid_steps''; eauto.
  Qed.

  (* TODO: move *)
  Lemma forall_impl_helper {A: Type} (P Q: A -> Prop):
    (forall a, P a -> Q a) -> all P -> all Q.
  Proof. rewrite /all. intros. eauto. Qed. 

  Lemma client_trace_tl_ext_bounded (tr: mtrace client_model_impl)
    (VALID: mtrace_valid tr)
    (S0: fs_le (trfirst tr).2 fs_S):
    trans_bounded tr (fun oℓ => exists ι, oℓ = Some (ρ_ext ι)).
  Proof.
    assert (forall tl_st1 f1 ι tl_st2 f2,
               client_trans (tl_st1, f1) (Some (ρ_ext ι)) (tl_st2, f2) -> f1 ≠ fs_U ->
               strict fs_le f2 f1) as LT.
    { intros * STEP NU. inversion STEP; subst.
      - done.
      - destruct FS as [[-> ->] | [[-> | ->] ->]]; try done.
        + red. split; auto. auto. rewrite /fs_le. lia.
        + split; auto. rewrite /fs_le. lia.
      - destruct FS as [[-> ->] | [-> ->]]; try done.
        split; auto. rewrite /fs_le. lia. }

    destruct (classic (trans_bounded tr (fun oℓ => exists ι, oℓ = Some (ρ_ext ι)))) as [| INF]; [done| ].
    pose proof (trace_has_len tr) as [len LEN].
    destruct len.
    2: { apply fin_trans_bounded. eapply terminating_trace_equiv; eauto. }

    rewrite /trans_bounded in INF.
    pose proof (@not_exists_forall_not _ _ INF) as INF'. simpl in INF'. clear INF.
    eapply forall_impl_helper in INF'.
    2: { intros ?. apply not_forall_exists_not. }
    (* TODO: shorten *)
    eapply Morphisms_Prop.all_impl_morphism in INF'.
    2: { red. intros ?. apply Morphisms_Prop.ex_impl_morphism. intros ?.
         red. apply not_forall_exists_not. }
    eapply Morphisms_Prop.all_impl_morphism in INF'.
    2: { red. intros ?. red. do 2 (apply Morphisms_Prop.ex_impl_morphism; intros ?).
         red. apply imply_to_and. } 
    eapply Morphisms_Prop.all_impl_morphism in INF'.
    2: { red. intros ?. red. do 2 (apply Morphisms_Prop.ex_impl_morphism; intros ?).
         red. eapply Morphisms_Prop.and_impl_morphism; [reflexivity| ].
         red. apply imply_to_and. }
    eapply Morphisms_Prop.all_impl_morphism in INF'.
    2: { red. intros ?. red. do 2 (apply Morphisms_Prop.ex_impl_morphism; intros ?).
         red. eapply Morphisms_Prop.and_impl_morphism; [reflexivity| ].
         red. eapply Morphisms_Prop.and_impl_morphism; [reflexivity| ].
         red. apply NNPP. }
    red in INF'. 
    

    pose proof (INF' 0). destruct H0.  
    apply Morphisms_Prop.all_impl_morphism in INF'.
    2: { intros. 
    
    contra. 
    
    destruct (classic (exists n ι, tr L!! n = Some (Some (ρ_ext ι)))) as [(n&ι&Ln)|NO].
    2: { exists 0. intros. intros [? ->]. apply NO. eauto. }
    apply trace_label_lookup_simpl' in Ln as ([? f]&[? f']&NTH).
    assert (fs_le f' fs_S) as ->.
    { assert (fs_le f fs_S) as LE.
      { forward eapply (client_trace_fs_mono tr 0 n); eauto.
        { lia. }
        { rewrite state_lookup_0. reflexivity. }
        { eapply trace_state_lookup; eauto. }
        simpl. intros. etrans; eauto. }
      eapply trace_valid_steps' in NTH; eauto.
      simpl in NTH. red in LE. inversion NTH; subst; try auto || lia.
      - destruct FS as [[-> ->]|[-> ->]]; [| done]. lia.
      - destruct f'; try auto || lia.
  Abort.
   
    
  Lemma client_model_fair_term (tr: mtrace client_model_impl)
    lmtr
    (OUTER_CORR: client_LM_trace_exposing lmtr tr)
    (INIT: is_init_cl_state (trfirst tr))
    :
    mtrace_fairly_terminating tr.
  Proof.
    intros. red. intros VALID FAIR.
    pose proof (trace_has_len tr) as [len LEN].
    
    forward eapply trace_prop_split with (P := is_UU_step) as (i'_s & STEPs & NOs & LEN1).
    2: by apply LEN. 
    { intros [[? f] ostep]. destruct ostep as [[? [? f']] | ]. 
      2: { right. intros (?&?&?&[=]). }
      destruct (decide (f = fs_U /\ f' = fs_U)) as [[-> ->]|].
      - left. red. eauto.
      - right. intros (?&?&?&[=]). subst. tauto. }

    forward eapply first_tl_subtrace_finite; eauto. intros [m ->].
    apply NOmega.nomega_le_lt_eq in LEN1 as [LEN1 | <-].
    2: { eapply terminating_trace_equiv; eauto. }
    destruct (proj2 (trace_lookup_dom _ _ LEN m)) as [[[tl_st f] step] MTH]; [done| ].
    destruct step as [[ρ [tl_st' f']]| ]. 
    2: { forward eapply (proj1 (trace_lookup_dom_eq _ _ LEN m)); eauto.
         intros ->. eapply terminating_trace_equiv; eauto. }
    assert (f = fs_U) as ->.
    { destruct m.
      { destruct (trace_lookup_0 tr) as [? TR0].
        rewrite MTH in TR0. inversion TR0. subst.
        red in INIT. rewrite -H1 in INIT. tauto. }
      apply trace_lookup_prev in MTH as (?&?&MTH).
      apply STEPs in MTH; [| simpl; lia]. 
      by destruct MTH as (?&?&?&[=]). }
    pose proof MTH as STEP. eapply trace_valid_steps' in STEP; eauto.
    Local Ltac exploit_UU NOs MTH := apply NOs in MTH; [| done]; destruct MTH; by repeat eexists.
    (* assert (fs_le f' fs_S) as LE.  *)
    assert (f' = fs_S) as ->.
    { simpl in STEP. inversion STEP; subst; cycle -2. 
      { destruct FS as [[? ->] | [[[=] | [=]] ?]]. exploit_UU NOs MTH. }
      - destruct FS as [[? ->] | [[=] ?]].
        by exploit_UU NOs MTH.
      - by exploit_UU NOs MTH.
      - done. }    

    forward eapply (subtrace_len tr _ (S m) len); eauto.
    { rewrite -Nat.add_1_r. eapply trace_lookup_dom_strong; eauto. }
    { reflexivity. }
    intros (str & SUB & LEN2).
    destruct len as [ | ?].
    2: { eapply terminating_trace_equiv; eauto. }
    enough (terminating_trace str) as TERM.
    { eapply terminating_trace_equiv in TERM as [? LEN']; eauto.
      simpl in LEN'. done. }

    simpl in LEN2.
    forward eapply (tl_trace_construction str) as MATCH. 
    { subst. eapply (subtrace_valid tr); eauto. done. }
    {
      rename tl_st' into tl_st''. rename tl_st into tl_st'.
      rename ρ into ρ'. 
      intros i [[tl_st f] [[ρ st']| ]] RES.
      2: { right. eexists. eauto. }
      left.
      assert (fs_le f fs_S) as LEi.
      { eapply state_label_lookup in MTH as (_&MTH'&_).
        apply trace_state_lookup in RES. 
        erewrite subtrace_state_lookup in RES; eauto.
        unshelve forward eapply (client_trace_fs_mono _ _ _ _ _ _ _ MTH' RES); eauto.
        lia. }
      pose proof RES as STEP'. eapply trace_valid_steps' in STEP'.
      2: { eapply (subtrace_valid tr); eauto. done. }
      inversion STEP'; subst; try done.
      all: try by repeat eexists. }

    eapply simulation_adequacy_terminate_general'_ext.
    5: by apply MATCH.
    { Unshelve.
      all: admit. }
    { intros.
      eapply fin_ext_fair_termination; eauto. }
    { admit. }
    { (* TODO: unify this proof, one in tl_subtrace_fair
         and one in comp_adequacy *)
      subst. simpl in *.
      forward eapply outer_exposing_subtrace; eauto.
      intros [? EXP'].

      unshelve eapply ELM_ALM_afair_by_next.
      { red. apply TlEM_EXT_KEEPS. }  

      eapply inner_LM_trace_fair_aux.
      - apply _.
      - done. 
      - by apply EXP'. 
      - simpl. intros ?? [=<-].
        by apply EXP'.
      - by apply EXP'.
      - subst. eapply infinite_trace_equiv; eauto. 
      - by apply MATCH. }
    { eapply traces_match_valid1; eauto. }
    subst. eapply fair_by_subtrace; eauto.

  Qed. 

End ClientDefs. 