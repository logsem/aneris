From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness Require Import trace_helpers.
(* TODO: rearrange the code *)
From trillium.fairness Require Import lemmas trace_len trace_lookup fuel lm_fair subtrace comp_utils my_omega lm_fairness_preservation.
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.ticketlock Require Import fair_lock.

Close Scope Z_scope.

(* TODO: move *)
(* TODO: rename definitions inside? *)
Section GroupRolesInstantiation.  
  Context {Gl: Type} `{Countable Gl}.
  Context (get_Gls: forall n, { gls: gset Gl | size gls = n}).
  Let get_Gls' n := elements (proj1_sig (get_Gls n)). 

  Instance Gl_inhabited: Inhabited Gl.
  Proof. 
    pose proof (get_Gls 1) as [gls SPEC].
    destruct (decide (gls = ∅)).
    { subst. set_solver. }
    apply finitary.set_choose_L' in n as [g IN].
    econstructor. apply g. 
  Qed.

  Let g0 := @inhabitant _ Gl_inhabited.

  Definition gls' n: list Gl := 
    let gls_Sn := get_Gls' (S n) in
    if (decide (g0 ∈ gls_Sn)) 
    then remove EqDecision0 g0 gls_Sn
    else drop 1 gls_Sn. 
      
  Definition ρlg_i (n i: nat) := nth i (gls' n) g0.

  (* TODO: move *)
  Lemma nth_error_seq n i (DOM: i < n):
    nth_error (seq 0 n) i = Some i.
  Proof.
    erewrite nth_error_nth' with (d := 0).
    - f_equal. by apply seq_nth.
    - by rewrite seq_length. 
  Qed. 

  (* TODO: move *)
  Lemma length_remove_NoDup `{ED: EqDecision A} (l: list A) (a: A)
                            (ND: NoDup l)
    :
    length (remove ED a l) = length l - (if (decide (a ∈ l)) then 1 else 0).
  Proof.
    destruct (decide (a ∈ l)) as [IN| ].
    2: { rewrite notin_remove; [lia| ].
         by intros ?%elem_of_list_In. }
    apply elem_of_list_In, In_nth_error in IN as [i ITH].
    pose proof ITH as (l1 & l2 & -> & LEN)%nth_error_split.
    rewrite remove_app. rewrite notin_remove.
    2: { apply NoDup_app in ND as (?&NIN&?).
         intros IN1. apply (NIN a); [| set_solver]. by apply elem_of_list_In. }
    simpl. rewrite decide_True; [| done].
    rewrite notin_remove.
    2: { rewrite cons_middle app_assoc in ND. 
         apply NoDup_app in ND as (?&NIN&?).
         intros ?%elem_of_list_In. apply (NIN a); set_solver. }
    rewrite !app_length. simpl. lia.
  Qed. 


  Lemma get_Gls'_len n: length (get_Gls' n) = n. 
  Proof.
    rewrite /get_Gls'. 
    destruct (get_Gls n) as [gls SPEC]; simpl in *.
    rewrite -(list_to_set_elements_L gls) in SPEC.
    rewrite size_list_to_set in SPEC; [lia| ].
    apply NoDup_elements.
  Qed. 

  Lemma gls'_len n: length (gls' n) = n.
  Proof. 
    rewrite /gls'. destruct decide.
    - rewrite length_remove_NoDup.
      2: { rewrite /get_Gls'. apply NoDup_elements. }
      rewrite decide_True; [| done].
      rewrite get_Gls'_len. lia. 
    - rewrite skipn_length.
      rewrite get_Gls'_len. lia. 
  Qed. 

  Lemma gls'_ρlg n:
    gls' n = map (ρlg_i n) (seq 0 n). 
  Proof.
    pose proof (gls'_len n) as LEN'. 
    apply nth_ext with (d := g0) (d' := g0).
    { by rewrite fmap_length seq_length. }

    intros i DOM.    
    eapply Some_inj.
    rewrite -nth_error_nth'; [| done].
    rewrite -nth_error_nth'. 
    2: { rewrite fmap_length seq_length. congruence. }
    rewrite nth_error_map.
    rewrite nth_error_seq; [| congruence].
    simpl. rewrite /ρlg_i.
    by apply nth_error_nth'.
  Qed.

  Definition gls n: gset Gl := list_to_set (gls' n). 

  Lemma gls_ρlg n:
    gls n = list_to_set (map (ρlg_i n) (seq 0 n)).
  Proof. 
    rewrite /gls. f_equal. apply gls'_ρlg.
  Qed. 

  Lemma get_Gls'_NoDup n: NoDup (get_Gls' n).
  Proof. 
    rewrite /get_Gls'. apply NoDup_elements.
  Qed.

  (* TODO: move *)
  Lemma NoDup_remove {A: Type} (l: list A)
    (ND: NoDup l):
    forall a EQ, NoDup (remove EQ a l).
  Proof. 
    intros a ?. revert a. induction l.
    { done. }
    intros. simpl. destruct EQ.
    { subst. apply IHl. by inversion ND. }
    econstructor.
    2: { apply IHl. by inversion ND. }
    inversion ND. subst.
    intros IN%elem_of_list_In%in_remove.
    apply H2. apply elem_of_list_In, IN. 
  Qed. 

  Lemma gls'_NoDup n: NoDup (gls' n).
  Proof. 
    rewrite /gls'. destruct decide.
    - apply NoDup_remove. apply get_Gls'_NoDup.
    - apply NoDup_ListNoDup.
      eapply NoDup_app_remove_l.
      erewrite take_drop.
      apply NoDup_ListNoDup. apply get_Gls'_NoDup.
  Qed. 

  Lemma ρlg_i_dom_inj n:
    forall i j, i < n -> j < n -> ρlg_i n i = ρlg_i n j -> i = j. 
  Proof.
    rewrite /ρlg_i.
    rewrite -{1 2}(gls'_len n). apply NoDup_nth.
    apply NoDup_ListNoDup. apply gls'_NoDup. 
  Qed.

End GroupRolesInstantiation.


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

  (* Lemma ρlg_tl_inj: Inj eq eq ρlg_tl. *)
  (* Proof.  *)
  (*   intros ??. rewrite /ρlg_tl. EQ.  *)


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

  Context {TlLM': forall gs, LiveModel Gtl Mtl (LSI_groups_fixed gs)}.  
  Context (TlLM_LFP': ∀ gs: gset Gtl, gs ≠ ∅ → LMFairPre (TlLM' gs)).
  (* Context (TlEM': forall gs (NE: gs ≠ ∅), ExtModel (LM_Fair (LF := TlLM_LFP' _ NE))). *)

  Definition TlLM := TlLM' lib_gs. 
  Definition TlLM_LFP := TlLM_LFP' _ lib_gs_ne.
  Definition TlLM_FM := LM_Fair (LF := TlLM_LFP).

  Context `(TlEM_FL: @FairLock TlLM_FM tl_FLP tl_FLE).
  Definition TlEM := FL_EM tl_FLE. 

  (* TODO: reorganize the premises so those below don't depend
     on the client's choice of lib_gs *)
  Let tl_state := fmstate TlLM_FM. 
  Let tl_role := fmrole TlLM_FM.
  Let tl_erole := @ext_role _ TlEM.

  (* Existing Instances tl_FLP tl_FLE.  *)

  Inductive flag_state := | fs_U | fs_S | fs_O. 
  Definition client_state: Type := tl_state * flag_state.

  (* Inductive cl_role_kind := | cl_lift | cl_au | cl_al | cl_cl. *)
  (* Definition client_role: Type := cl_role_kind * cl_id.  *)
  Definition client_role: Type := tl_erole + cl_id. 

  (* Let allow_unlock_impl := allow_unlock_impl _ _ _ _ _ _ (FairLock := TlEM_FL).  *)
  (* Let allow_lock_impl := allow_lock_impl _ _ _ _ _ _ (FairLock := TlEM_FL).  *)

  Definition ρ_cl c: client_role := inr c. 
  Definition ρ_lib ρlg: client_role := inl $ inl ρlg.
  Definition ρ_ext er: client_role := inl $ inr $ env er (EM := TlEM). 

  
  Inductive client_trans: client_state -> option client_role -> client_state -> Prop :=
  | ct_lib_step tl1 tl2 c flag
        (LIB_STEP: fmtrans TlLM_FM tl1 (Some (ρlg_tl c)) tl2):
      (* client_trans (tl1, flag) (Some (cl_lift, c)) (tl2, flag) *)
      client_trans (tl1, flag) (Some $ ρ_lib (ρlg_tl c)) (tl2, flag)
  | ct_flag_US tl 
      (LOCK: has_lock_st (ρlg_tl cl_L) tl)
      (DIS: ¬ active_st (ρlg_tl cl_L) tl):
    (* client_trans (tl, fs_U) (Some (cl_cl, cl_L)) (tl, fs_S) *)
    client_trans (tl, fs_U) (Some $ ρ_cl cl_L) (tl, fs_S)
  | ct_au_L tl (ρlg := ρlg_l)
      (LOCK: has_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl):
    client_trans (tl, fs_S) (Some $ ρ_ext $ flU (ρlg: fmrole TlLM_FM)) (allow_unlock_impl ρlg tl, fs_S)
  | ct_au_R tl fs fs'
      (ρlg := ρlg_r)
      (FS: fs = fs_U /\ fs' = fs_U \/ fs = fs_S /\ fs' = fs_O)
      (LOCK: has_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl):
    (* client_trans (tl, fs) (Some (cl_au, cl_R)) (allow_unlock_impl tl, fs') *)
    client_trans (tl, fs) (Some $ ρ_ext $ flU (ρlg: fmrole TlLM_FM)) (allow_unlock_impl ρlg tl, fs')
  | ct_al_R tl fs
      (ρlg := ρlg_r)
      (CANL: can_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl)
      (NO: fs ≠ fs_O):
    (* client_trans (tl, fs) (Some (cl_al, cl_R)) (allow_lock_impl ρlg tl, fs) *)
    client_trans (tl, fs) (Some $ ρ_ext $ flL (ρlg: fmrole TlLM_FM)) (allow_lock_impl ρlg tl, fs)
  .

  (* Instance cl_role_kind_dec: EqDecision cl_role_kind. *)
  (* Proof. solve_decision. Qed.  *)
  Instance flag_state_dec: EqDecision flag_state.
  Proof. solve_decision. Qed.   
  Instance cl_id_dec: EqDecision cl_id.
  Proof. solve_decision. Qed.

  Ltac fin_type_countable all_values :=
    unshelve eapply finite.finite_countable;
    refine {| finite.enum := all_values |};
    [ repeat (apply NoDup_cons; split; [set_solver| ]); apply NoDup_nil_2 |
     by intros x; destruct x; set_solver]. 
       
  (* Instance cl_role_kind_cnt: Countable cl_role_kind. *)
  (* Proof. fin_type_countable [cl_lift; cl_au; cl_al; cl_cl]. Qed.  *)
  Instance flag_state_cnt: Countable flag_state.
  Proof. fin_type_countable [fs_U; fs_S; fs_O]. Qed. 
  Instance cl_id_cnt: Countable cl_id.
  Proof. fin_type_countable [cl_L; cl_R]. Qed. 
  
  (* Lemma client_role_Cnt: Countable client_role. *)
    
  (*   unshelve eapply prod_countable; try apply _.   *)

  Lemma ρlg_dom_dec (ρlg: Gtl):
    {c | ρlg = ρlg_tl c} + (forall c, ρlg ≠ ρlg_tl c).
  Proof. 
    destruct (decide (ρlg = ρlg_tl cl_L)) as [-> | ?].
    { left. eauto. } 
    destruct (decide (ρlg = ρlg_tl cl_R)) as [-> | ?].
    { left. eauto. }
    right. intros c. by destruct c.
  Qed. 

  
  Instance client_step_ex_dec (st: client_state) (ρ: client_role):
    Decision (exists st', client_trans st (Some ρ) st').
  Proof.
    destruct st as [tl_st flag].
    destruct ρ as [er | c].
    2: { destruct (decide (has_lock_st (ρlg_tl cl_L) tl_st (M := TlLM_FM) /\ ¬ active_st (ρlg_tl cl_L) tl_st (M := TlLM_FM) /\ flag = fs_U /\ c = cl_L)) as [(?&?&->&->)| ].
         + left. eexists (_, _). econstructor; eauto.
         + right. intros [? STEP]. inversion STEP; subst. tauto. }
    destruct er as [ρlg | [ι]]. 
    { destruct (ρlg_dom_dec ρlg).
      2: { right. intros [? STEP]. inversion STEP. subst.
           eapply n; eauto. }
      destruct s as [c ->]. 
      pose proof TlLM_LFP. (* why it's not inferred? *)
      destruct (decide (exists tl_st', locale_trans tl_st (ρlg_tl c) tl_st' (LM := TlLM))) as [STEP | NOSTEP]. 
      + left. destruct STEP as [? STEP].
        eexists (_, _). eapply ct_lib_step. apply STEP.
      + right. intros [? STEP]. inversion STEP. subst.
        apply ρlg_tl_inj in H3. subst. 
        eapply NOSTEP. eexists. apply LIB_STEP. }

    destruct ι.
    - destruct (decide (ρ = ρlg_tl cl_L)) as [-> | ?].
      { destruct (decide (has_lock_st (ρlg_tl cl_L) tl_st (M := TlLM_FM) /\ ¬ active_st (ρlg_tl cl_L) tl_st (M := TlLM_FM) /\ flag = fs_S)) as [(?&?&->)| ]. 
        * left. eexists (_, _). eapply ct_au_L; eauto.
        * right. intros [? STEP]. inversion STEP; subst; try tauto.
          by eapply ρlg_lr_neq. }
      destruct (decide (ρ = ρlg_tl cl_R)) as [-> | ?].
      { destruct (decide (has_lock_st (ρlg_tl cl_R) tl_st (M := TlLM_FM) /\ ¬ active_st (ρlg_tl cl_R) tl_st (M := TlLM_FM) /\ flag ≠ fs_O)) as [(?&?&?)| ].
        * left. eexists (_, if decide (flag = fs_U) then fs_U else fs_O). eapply ct_au_R; eauto.
          destruct flag;
            (rewrite decide_True; tauto) || (rewrite decide_False; try tauto; congruence).
        * right. intros [? STEP]. inversion STEP; subst; try tauto.
          all: apply n0; set_solver. }
      right. intros [? STEP]. inversion STEP; subst; try tauto.
    - destruct (decide (ρ = ρlg_tl cl_R)) as [-> | ?].
      2: { right. intros [? STEP]. inversion STEP; subst; try tauto. }
      destruct (decide (can_lock_st (ρlg_tl cl_R) tl_st (M := TlLM_FM) /\ ¬ active_st (ρlg_tl cl_R) tl_st (M := TlLM_FM) /\ flag ≠ fs_O)) as [(?&?&?) | NOSTEP].
      + left. eexists (_, _). econstructor; eauto.
      + right. intros [? STEP]. inversion STEP; subst. tauto.
  Qed.

  Definition client_lr (st: client_state): gset (client_role) :=
    filter (fun r => (@bool_decide _ (client_step_ex_dec st r) = true))
           (* (set_map ρlg_tl) *)
           (* {[ ρlg_l; ρlg_r *)
           (list_to_set $
              f ← [ρ_lib ∘ ρlg_tl; ρ_ext ∘ flU ∘ ρlg_tl; ρ_ext ∘ flL ∘ ρlg_tl; ρ_cl];
              c ← [cl_L; cl_R];
              mret (f c)). 

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
    - pose proof (@LS_eqdec _ _ _ _ _ _ TlLM_LFP). (* not inferred? *)
      solve_decision.
    - pose proof (@inhLM _ _ _ _ _ _ TlLM_LFP) as [δ]. 
      apply (populate (δ, fs_U)).
    - intros. apply client_lr_spec. eauto.
  Defined.

  (* Definition project_tl_label (oρ: option $ fmrole client_model_impl): *)
  (*   option (@ext_role _ TlEM) := *)
  (*   match oρ with | Some (inl l) => Some $ Some l | _ => None end.  *)
    
  (*   match oρ with *)
  (*   | Some (cl_lift, c) => Some $ inl $ ρlg_tl c *)
  (*   | Some (cl_au, c) => Some $ inr $ @env _ TlEM flU *)
  (*   | Some (cl_al, c) => Some $ inr $ @env _ TlEM (flL ((ρlg_tl c): fmrole TlLM_FM)) *)
  (*   | _ => None  *)
  (*   end.  *)

  Definition project_tl_trace (tr: mtrace client_model_impl): 
    elmftrace (ELM := TlEM) :=
    project_nested_trace fst 
      (* (fun oρ => option_fmap _ _ Some (project_tl_label oρ)) *)
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

  Lemma client_model_fair_term (tr: mtrace client_model_impl)
    (* lmtr *)
    (* (OUTER_CORR: outer_LM_trace_exposing lmtr tr) *)
    :
    mtrace_fairly_terminating tr.
  Proof.
    intros. red. intros VALID FAIR.
    pose proof (trace_has_len tr) as [len LEN].
    
    forward eapply trace_prop_split with (P := fun '(s, _) => s.2 = fs_U) as (i'_s & STEPs & NOs).
    2: by apply LEN. 
    { solve_decision. }

    assert (exists i_s, i'_s = NOnum i_s) as [i_s ->]. 
    { 
    
    



End ClientDefs. 
