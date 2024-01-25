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

(* TODO: move *)
Ltac contra_dec name :=
  match goal with
  | |- ?G => destruct (decide G) as [| name]; [done| ]
  end. 


Section SizeLookup.
  Context `{FS: FinSet A C}.
  Context {LE: LeibnizEquiv C}.

  Lemma nth_sized_contra (i: nat) (c: C)
    (DOM : i < size c) (I: elements c !! i = None):
    False.
  Proof.    
    apply lookup_ge_None_1 in I.
    unshelve erewrite <- size_list_to_set in I.
    6: exact FS. 
    2: { apply NoDup_elements. }
    rewrite list_to_set_elements_L in I. lia. 
  Qed.  

  Definition nth_sized (i: nat) (c: C) (DOM: i < size c): A.
    destruct (elements c !! i) eqn:I.
    { exact a. }
    exfalso.
    apply (nth_sized_contra i c DOM I).
  Defined.

  (* Lemma nth_sized_elem_of a (c: C): *)
  (*   a ∈ c <-> exists i, elements c !! i = Some a.  *)
  (* Proof. *)
  (*   rewrite -elem_of_elements. *)
  (*   by rewrite elem_of_list_lookup. *)
  (* Qed.      *)

  Lemma nth_sized_elem_of a (c: C):
    a ∈ c <-> exists i DOM, nth_sized i c DOM = a /\ i < size c. 
  Proof.
    rewrite -elem_of_elements.
    rewrite /nth_sized.
    rewrite elem_of_list_lookup. apply exist_proper. intros i.
    (* destruct (elements c !! i).  *)
  Admitted. 

  (* Lemma enum_sized (c: C): *)
  (*   (* gls' n = map (ρlg_i n) (seq 0 n).  *) *)
  (*   c = map  *)
  (* Proof. *)
  (*   pose proof (gls'_len n) as LEN'.  *)
  (*   apply nth_ext with (d := g0) (d' := g0). *)
  (*   { by rewrite fmap_length seq_length. } *)

  (*   intros i DOM.     *)
  (*   eapply Some_inj. *)
  (*   rewrite -nth_error_nth'; [| done]. *)
  (*   rewrite -nth_error_nth'.  *)
  (*   2: { rewrite fmap_length seq_length. congruence. } *)
  (*   rewrite nth_error_map. *)
  (*   rewrite nth_error_seq; [| congruence]. *)
  (*   simpl. rewrite /ρlg_i. *)
  (*   by apply nth_error_nth'. *)
  (* Qed. *)

End SizeLookup.


(* TODO: replace 'Tl' prefixes with 'Fl' *)
Section ClientDefs.
  
  Context {Gtl: Type} `{Countable Gtl}.
  (* Context (get_Gtls: forall n, { gls: gset Gtl | size gls = n}). *)
  Context (lib_gs: gset Gtl).
  Context (SIZE2: size lib_gs = 2). 
  
  Inductive cl_id := | cl_L | cl_R.
  Definition cl_id_nat c := match c with | cl_L => 0 | cl_R => 1 end.

  Lemma cin_lt c: cl_id_nat c < 2.
  Proof. destruct c; simpl; lia. Qed.  

  (* Definition lib_gs: gset Gtl := gls get_Gtls 2. *)
  Definition ρlg_tl (c: cl_id): Gtl.
    apply (nth_sized (cl_id_nat c) lib_gs).
    rewrite SIZE2. apply cin_lt.
  Defined.

  Definition ρlg_l: Gtl := ρlg_tl cl_L. 
  Definition ρlg_r: Gtl := ρlg_tl cl_R. 

  (* Require Import Coq.Program.Equality. *)
  (* Require Import Coq.Program.Tactics. *)

  Lemma lib_gs_ρlg:
    lib_gs = {[ ρlg_l; ρlg_r ]}.
  Proof.
    apply set_eq. intros.
    rewrite nth_sized_elem_of.
    rewrite /ρlg_l /ρlg_r. 
  Admitted. 

  Lemma lib_gs_ne: lib_gs ≠ ∅.
  Proof.
    intros ->. pose proof SIZE2 as S. by rewrite size_empty in S.
  Qed. 

  Lemma ρlg_lr_neq: ρlg_l ≠ ρlg_r.
  Proof.
    intros EQ. 
  (*   intros EQ%ρlg_i_dom_inj; [done|..].  *)
  (*   all: simpl; lia. *)
  (* Qed.  *)
  Admitted. 

  (* Lemma ρlg_in_lib_gs: forall c, ρlg_tl c ∈ lib_gs. *)
  (* Proof.  *)
  (*   rewrite lib_gs_ρlg. intros c. *)
  (*   destruct c; set_solver.  *)
  (* Qed. *)

  Lemma ρlg_tl_inj: Inj eq eq ρlg_tl.
  Proof.
  Admitted.

  Context {Mtl: FairModel}.
  (* Context {Tl_nexts: forall tl_st, next_states tl_st (M := Mtl)}. *)
  (* Context (Mtl_TERM: ∀ mtr: mtrace Mtl, mtrace_fairly_terminating mtr).  *)

  (* Context {TlLM: LiveModel Gtl Mtl (LSI_groups_fixed lib_gs)}. *)
  Context {TlLSI: fmstate Mtl -> @groups_map _ Mtl _ _ -> @fuel_map Mtl -> Prop} {TlLSI_LGF: forall st tm fm, TlLSI st tm fm -> LSI_groups_fixed lib_gs st tm fm}. 
  Context {TlLM: LiveModel Gtl Mtl TlLSI}.
  Context (TlLM_LFP: LMFairPre TlLM).
  (* Context (TlEM': forall gs (NE: gs ≠ ∅), ExtModel (LM_Fair (LF := TlLM_LFP' _ NE))). *)

  (* Definition TlLM := TlLM' lib_gs.  *)
  (* Definition TlLM_LFP := TlLM_LFP' _ lib_gs_ne. *)
  Definition TlLM_FM := LM_Fair (LF := TlLM_LFP).

  Context (TlLM_nexts: forall δ_lib, @next_states TlLM_FM δ_lib).

  Context {tl_FLP : FairLockPredicates TlLM_FM}. 
  Context {tl_FLE: @FairLockExt TlLM_FM tl_FLP}. 
  Let TlEM := FL_EM tl_FLE.
  Context (TlEM_EXT_KEEPS: ext_keeps_asg (ELM := TlEM)).

  Context (TlEM_FL: @FairLock TlLM_FM tl_FLP tl_FLE (fun tr => forall g, fair_by_group (ELM_ALM TlEM_EXT_KEEPS) g tr)).

  Context (Mtl_EM: ExtModel Mtl). 
  Context {proj_ext : @EI _ TlEM → @EI _ Mtl_EM}. 
  Hypothesis PROJ_KEEP_EXT:
    forall δ1 ι δ2, (@ETs _ TlEM) ι δ1 δ2 -> 
                (@ETs _ Mtl_EM) (proj_ext ι) (ls_under δ1) (ls_under δ2). 

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
  | ct_au_L tl (ρlg := ρlg_l)
      (LOCK: does_unlock ρlg tl)
      (* (DIS: ¬ active_st ρlg tl) *)
      (* (DIS: ¬ role_enabled_model (ρlg: fmrole TlLM_FM) tl) *)
      (DIS: disabled_st (ρlg: fmrole TlLM_FM) tl)
    :
    client_trans (tl, fs_U) (Some $ ρ_ext $ flU (ρlg: fmrole TlLM_FM)) (allow_unlock_impl ρlg tl, fs_S)
  | ct_au_R tl fs fs'
      (ρlg := ρlg_r)
      (FS: fs = fs_U /\ fs' = fs_U \/ (fs = fs_S \/ fs = fs_S') /\ fs' = fs_O)
      (LOCK: does_unlock ρlg tl)
      (* (DIS: ¬ active_st ρlg tl) *)
      (* (DIS: ¬ role_enabled_model (ρlg: fmrole TlLM_FM) tl) *)
      (DIS: disabled_st (ρlg: fmrole TlLM_FM) tl)
    :
    client_trans (tl, fs) (Some $ ρ_ext $ flU (ρlg: fmrole TlLM_FM)) (allow_unlock_impl ρlg tl, fs')
  | ct_al_R tl fs fs'
      (ρlg := ρlg_r)
      (CANL: does_lock ρlg tl)
      (* (DIS: ¬ active_st ρlg tl) *)
      (* (NO: fs ≠ fs_O) *)
      (* (DIS: ¬ role_enabled_model (ρlg: fmrole TlLM_FM) tl) *)
      (DIS: disabled_st (ρlg: fmrole TlLM_FM) tl)
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
      { destruct (decide (does_unlock (ρlg_tl cl_L) tl_st1 (M := TlLM_FM) /\ disabled_st (ρlg_tl cl_L) tl_st1 (M := TlLM_FM) /\ tl_st2 = allow_unlock_impl ((ρlg_tl cl_L): fmrole TlLM_FM) tl_st1 /\ flag1 = fs_U /\ flag2 = fs_S)) as [(?&?&->&->&->)| ]. 
        * left. eapply ct_au_L; eauto.
        * right. intros STEP. inversion STEP; subst; try tauto.
          by eapply ρlg_lr_neq. }
      destruct (decide (ρ = ρlg_tl cl_R)) as [-> | ?].
      { destruct (decide (does_unlock (ρlg_tl cl_R) tl_st1 (M := TlLM_FM) /\ disabled_st (ρlg_tl cl_R) tl_st1 (M := TlLM_FM) /\ tl_st2 = allow_unlock_impl ((ρlg_tl cl_R): fmrole TlLM_FM) tl_st1 /\ (flag1 = fs_U /\ flag2 = fs_U \/ (flag1 = fs_S \/ flag1 = fs_S') /\ flag2 = fs_O))) as [(?&?&->&?)| ].
        * left. eapply ct_au_R; eauto.
        * right. intros STEP. inversion STEP; subst; try tauto.
          apply n0; set_solver. }
      right. intros STEP. inversion STEP; subst; tauto.
    - destruct (decide (ρ = ρlg_tl cl_R)) as [-> | ?].
      2: { right. intros STEP. inversion STEP; subst; tauto. }
      destruct (decide (does_lock (ρlg_tl cl_R) tl_st1 (M := TlLM_FM) /\ disabled_st (ρlg_tl cl_R) tl_st1 (M := TlLM_FM) /\ tl_st2 = allow_lock_impl ((ρlg_tl cl_R): fmrole TlLM_FM) tl_st1 /\ (flag1 = fs_U /\ flag2 = fs_U \/ flag1 = fs_S /\ flag2 = fs_S'))) as [(?&?&->&?) | NOSTEP].
      + left. econstructor; eauto.
      + right. intros STEP. inversion STEP; subst. tauto.
  Qed.

  Lemma client_model_step_fin (s1 : client_state):
    {nexts: list (client_state) | forall s2 oρ, client_trans s1 oρ s2 -> s2 ∈ nexts}.
  Proof.
    destruct s1 as (δ_lib, f).
    pose proof (TlLM_nexts δ_lib) as [nexts_lib IE_LIB].
    (* pose proof (role_LM_step_dom_all δ_lib ((ls_under δ_lib) :: ie_lib) (elements lib_gs) (LM := TlLM)) as STEPS_LIB. *)

    (* set nexts_lib := (map fst (enumerate_next δ_lib ((ls_under δ_lib) :: ie_lib) (elements lib_gs) (LM := TlLM))). *)
    (* fold nexts_lib in STEPS_LIB. *)
    
    set (nexts_tl :=
           nexts_lib ++
           map (flip allow_unlock_impl δ_lib) (elements lib_gs) ++
           map (flip allow_lock_impl δ_lib) (elements lib_gs)). 
    set nexts := f ← all_flag_states; δ ← nexts_tl; mret (δ, f). 
    
    exists nexts. 
    intros [δ' f'] oρ TRANS. simpl in TRANS.
    subst nexts. rewrite elem_of_list_bind.
    eexists. split; [| by apply all_flag_states_spec].
    rewrite elem_of_list_bind. eexists. split.
    { apply elem_of_list_ret. reflexivity. }
    subst nexts_tl. apply elem_of_app. 
    inversion TRANS; subst.
    - left. eauto. 
    - right.
      apply elem_of_app. left.      
      (* rewrite lib_gs_ρlg.  *) (* TODO: why does it break now? *)
      eapply elem_of_proper; [reflexivity| ..].
      { f_equiv. rewrite lib_gs_ρlg. reflexivity. }
      apply elem_of_list_fmap. eexists. split; eauto.
      apply elem_of_elements. set_solver.
    - right.
      apply elem_of_app. left.
      (* rewrite lib_gs_ρlg. *)
      eapply elem_of_proper; [reflexivity| ..].
      { f_equiv. rewrite lib_gs_ρlg. reflexivity. }

      apply elem_of_list_fmap. eexists. split; eauto.
      apply elem_of_elements. set_solver.
    - right.
      apply elem_of_app. right.
      (* rewrite lib_gs_ρlg. *)
      eapply elem_of_proper; [reflexivity| ..].
      { f_equiv. rewrite lib_gs_ρlg. reflexivity. }

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

  Lemma client_trace_tl_steps  (tr: mtrace client_model_impl)
    (VALID: mtrace_valid tr):
    ∀ i res, tr !! i = Some res → is_tl_step res \/ is_end_state res.
  Proof.
    intros i [[tl_st f] [[ρ st']| ]] RES.
    2: { right. eexists. eauto. }
    left.
    pose proof RES as STEP'. eapply trace_valid_steps' in STEP'; eauto. 
    inversion STEP'; subst; try done.
    all: try by repeat eexists.
  Qed.

  Let client_tl_traces_match :=
        lm_model_traces_match
      (transA := @ext_trans _ TlEM)
      ((option_fmap _ _ inl): option (@ext_role _ TlEM) -> option $ fmrole client_model_impl)
      (fun c δ_lib => fst c = δ_lib). 

  Lemma tl_trace_construction (tr: mtrace client_model_impl)
    (VALID: mtrace_valid tr):
    client_tl_traces_match tr (project_tl_trace tr). 
  Proof.
    do 2 red.
    rewrite /out_A_labels_match. simpl.
    eapply traces_match_impl; cycle 1.
    { intros *. intros X. apply X. }
    { eapply nested_trace_construction.
      { done. }
      { intros * ITH. apply client_trace_tl_steps in ITH as [LIB | ?]; [| eauto| tauto].
        red in LIB. unfold_slm LIB. destruct Pstep as [? <-].
        left. do 3 eexists. eauto. }
      intros. destruct ℓ; [| done]. destruct c; [| done].
      inversion H1. subst.
      inversion H0; subst; simpl in *.
      - econstructor. auto.
      - econstructor. simpl.
        (* apply not_live_not_active in DIS; auto.   *)
        eapply allows_unlock_impl_spec; auto.
      - econstructor. simpl. 
        (* apply not_live_not_active in DIS; auto.   *)
        eapply allows_unlock_impl_spec; auto.
      - econstructor. simpl. 
        (* apply not_live_not_active in DIS; auto.   *)
        eapply allows_lock_impl_spec; auto. }
    simpl. intros. destruct ℓ1; [| done]. destruct c; [| done].
    by inversion H0.
  Qed.

  Definition is_UU_step (step: model_trace_step client_model_impl) :=
    exists tl1 oℓ tl2, step = ((tl1, fs_U), Some (oℓ, (tl2, fs_U))).

  (* TODO: move; how to generalize it? *)
  Section UnusedRoles.
    
    Definition get_lifted (ρ: client_role) :=
          match ρ with 
          | inl (inr (env (flU ρlg)))
          | inl (inr (env (flL ρlg)))
          | inl (inl ρlg) => Some ρlg
          | _ => None
          end. 

    (* Lemma client_trans_keeps_unused st1 ρ st2 *)
    (*   (STEP: client_trans st1 ρ st2): *)
    (*   forall ρlg, is_unused ρlg st1.1 <-> is_unused ρlg st2.1. *)
    Lemma client_trans_keeps_unused ρlg:
      label_kept_state (fun (st: fmstate client_model_impl) => is_unused ρlg st.1) (fun _ => True).
    Proof. 
      red. intros. 
      enough (exists r, fmtrans (@ext_model_FM _ TlEM) st.1 r st'.1) as [??]. 
      { eapply step_keeps_unused; eauto. }
      inversion STEP; subst; simpl in *; eauto.
      - eexists. left. simpl. eauto.
      - exists (Some $ inr $ env $ ((flU (ρlg0: fmrole TlLM_FM)): @EI _ TlEM)).
        econstructor. simpl.
        (* apply not_live_not_active in DIS; auto.   *)
        apply allows_unlock_impl_spec; eauto. 
      - exists (Some $ inr $ env $ ((flU (ρlg0: fmrole TlLM_FM)): @EI _ TlEM)).
        econstructor. simpl.
        (* apply not_live_not_active in DIS; auto. *)
        apply allows_unlock_impl_spec; eauto. 
      - exists (Some $ inr $ env $ ((flL (ρlg0: fmrole TlLM_FM)): @EI _ TlEM)).
        econstructor. simpl.
        (* apply not_live_not_active in DIS; auto. *)
        apply allows_lock_impl_spec; eauto.
    Qed.

    (* TODO: move partially to fair_lock *)
    Lemma client_trace_keeps_unused (tr: mtrace client_model_impl) i si
      (VALID : mtrace_valid tr)
      (ITH: tr S!! i = Some si):
      (* forall ρlg, is_unused ρlg si.1 <-> is_unused ρlg (trfirst tr).1.  *)
      forall ρlg, is_unused ρlg (trfirst tr).1 -> is_unused ρlg si.1.       
    Proof.
      intros ρlg. generalize dependent si. induction i.
      { intros. rewrite state_lookup_0 in ITH. inversion ITH. auto. }
      rewrite -Nat.add_1_r. intros si' ITH'. 
      pose proof (trace_has_len tr) as [len LEN].  
      destruct (proj2 (trace_lookup_dom_strong _ _ LEN i)) as (sj & ρ & sj'_ & JTH). 
      { eapply state_lookup_dom; eauto. }    
      apply state_label_lookup in JTH as (JTH & JTH'_ & JTHρ).
      rewrite ITH' in JTH'_. inversion JTH'_. subst sj'_. clear JTH'_.   
      specialize (IHi _ JTH). intros ?%IHi.
      eapply client_trans_keeps_unused; eauto.  
      eapply trace_valid_steps''; eauto.
    Qed.

    Definition unused_not_ρlg (st: client_state) :=
      (forall ρlg, (¬ exists c, ρlg = ρlg_tl c) -> is_unused ρlg st.1). 

    Lemma client_trace_ρlg_not_unused (st: client_state) ρlg
      (USED: ¬ is_unused ρlg st.1)
      (* (INIT : is_init_cl_state (trfirst tr)) *)
      (UN: unused_not_ρlg st)
      :      
      ρlg ∈ lib_gs. 
    Proof.
      contra_dec NIN.
      destruct USED. 
      apply UN. intros [c ->]. apply NIN.
      rewrite lib_gs_ρlg. destruct c; set_solver.
    Qed.

    Lemma unused_not_ρlg_trace_preserved (tr: mtrace client_model_impl)
      (UN0: unused_not_ρlg (trfirst tr))
      (VALID : mtrace_valid tr):
      forall i st, tr S!! i = Some st -> unused_not_ρlg st.
    Proof.
      intros i. induction i.
      { rewrite state_lookup_0. set_solver. }
      (* intros st' I'TH. *)
      rewrite -Nat.add_1_r. intros si' ITH'. 
      pose proof (trace_has_len tr) as [len LEN].  
      destruct (proj2 (trace_lookup_dom_strong _ _ LEN i)) as (sj & ρ & sj'_ & JTH). 
      { eapply state_lookup_dom; eauto. }    
      apply state_label_lookup in JTH as (JTH & JTH'_ & JTHρ).
      rewrite ITH' in JTH'_. inversion JTH'_. subst sj'_. clear JTH'_.   
      specialize (IHi _ JTH).
      red. intros ? UN%IHi.
      eapply client_trans_keeps_unused; eauto.  
      eapply trace_valid_steps''; eauto.
    Qed. 
      
  End UnusedRoles. 

  Definition is_init_cl_state (st: client_state) :=
      (forall c, let ρlg := ρlg_tl c in does_lock ρlg st.1 /\ active_st ρlg st.1) /\
        (forall ρlg, is_unused ρlg st.1 <-> ¬ exists c, ρlg = ρlg_tl c) /\
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
    pose proof (ls_inv tl_st) as IN. apply TlLSI_LGF in IN.
    specialize (IN g). specialize_full IN. 
    (* forward eapply (ls_inv tl_st g) as IN. *)
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
         eapply TlLSI_LGF; [apply tl_st| ]. 
         (* apply (ls_inv tl_st).  *)
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
      pose proof (mapped_roles_dom_fuels_gen (rearrange_roles_map (ls_tmap δ2) (dom (ls_tmap δ0)) τ0) ((ls_fuel δ2))) as R.             
      erewrite <- (proj1 R).
      2: { apply rrm_tmap_fuel_same_doms. }
      pose proof (ls_inv δ2) as LSI2. red in LSI2. 
      specialize (LSI2 _ ltac:(eauto)).
      by rewrite -mapped_roles_dom_fuels in LSI2. 
  Qed.
    
  Local Instance client_LF: LMFairPre client_model.
  esplit; apply _.
  Defined.

  Definition client_LM_trace_exposing tr :=
    exists lmtr,
    outer_LM_trace_exposing TlEM_EXT_KEEPS
      ((inl ∘ inl): Gtl -> fmrole client_model_impl) (option_fmap _ _ inl) (λ st tl_st, st.1 = tl_st)
      (LMo := client_model)
      lmtr
      tr
  .

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


  Ltac fs_le_simpl FS := rewrite /fs_le in FS; simpl in FS.
  Ltac fs_le_unfold :=
    match goal with
    | FS: fs_le ?x ?y |- _ => fs_le_simpl FS
    | FS: ¬ fs_le ?x ?y |- _ => fs_le_simpl FS
    | FS: strict fs_le ?x ?y |- _ => rewrite /strict in FS; fs_le_simpl FS
    | FS: ¬ strict fs_le ?x ?y |- _ => rewrite /strict in FS; fs_le_simpl FS
    end.
  
  Ltac fs_le_solver :=
    repeat fs_le_unfold; rewrite /fs_le ?/strict; simpl; try lia. 

  (* TODO: refactor lemmas below *)

  (* TODO: move, rename *)
  Lemma kept2:
  @label_kept_state client_model_impl
    (@role_enabled_model client_model_impl (ρ_ext (@flU TlLM_FM ρlg_r)))
    (other_step ((ρ_ext (@flU TlLM_FM ρlg_r)): fmrole client_model_impl)). 
  Proof.
    red. intros [tl_st f] ? [tl_st' f'] **. simpl in STEP.
    destruct oℓ' as [ρ | ].
    2: { by inversion STEP. }
    assert (ρ ≠ ρ_ext (flU (ρlg_r: fmrole TlLM_FM))) as NEQ' by congruence.
    
    assert ((f ≠ fs_O) /\
              does_unlock ρlg_r tl_st /\ disabled_st (ρlg_r: fmrole TlLM_FM) tl_st) as PREρlg.
    { red in Pst. simpl in Pst. apply client_lr_spec in Pst as [? STEP'].      
      inversion STEP'; subst; repeat split; try tauto.
      { congruence. }
      clear -FS. set_solver. }
    
    pose proof (ct_au_R tl_st' f' (match f' with | fs_U => fs_U | _ => fs_O end)) as STEPr.
    simpl in STEPr. rewrite !curry_uncurry_prop in STEPr.
    red. simpl. apply client_lr_spec.
    eexists. apply STEPr. clear STEPr. apply and_assoc. split.
    { apply proj1 in PREρlg.
      inversion STEP; subst; try tauto. 
      all: destruct f'; tauto. }
 
    inversion STEP; subst.
    - eapply step_keeps_unlock_dis.
      { split; try by apply PREρlg. }
      2: { left. eauto. }
      simpl. 
      rewrite /ρlg_r.
      congruence. 
    - edestruct ρlg_lr_neq.
      eapply has_lock_st_excl with (ρlg1 := ρlg_l); eauto.
      all: by apply PREρlg.
    - done.
    - edestruct does_lock_unlock_incompat; eauto. apply PREρlg.
  Qed.
        
  Lemma kept2':
  @label_kept_state client_model_impl
    (@role_enabled_model client_model_impl (ρ_ext (@flL TlLM_FM ρlg_r)))
    (other_step ((ρ_ext (@flL TlLM_FM ρlg_r)): fmrole client_model_impl)). 
  Proof.
    red. intros [tl_st f] ? [tl_st' f'] **. simpl in STEP.
    destruct oℓ' as [ρ | ].
    2: { by inversion STEP. }
    assert (ρ ≠ ρ_ext (flL (ρlg_r: fmrole TlLM_FM))) as NEQ' by congruence.
    
    assert ((fs_le fs_S f) /\
              does_lock ρlg_r tl_st /\ disabled_st (ρlg_r: fmrole TlLM_FM) tl_st) as PREρlg.
    { red in Pst. simpl in Pst. apply client_lr_spec in Pst as [? STEP'].      
      inversion STEP'; subst; repeat split; try tauto.
      destruct f; try fs_le_solver; set_solver. }
    
    pose proof (ct_al_R tl_st' f' (match f' with | fs_U => fs_U | _ => fs_S' end)) as STEPr.
    simpl in STEPr. rewrite !curry_uncurry_prop and_comm in STEPr. 
    red. simpl. apply client_lr_spec.
    eexists. apply STEPr. clear STEPr. split.
    { destruct PREρlg as (LE & LOCK & DIS). inversion STEP; subst; try tauto.
      - destruct f'; try fs_le_solver; tauto. 
      - subst ρlg. edestruct does_lock_unlock_incompat; eauto. }
 
    inversion STEP; subst.
    - eapply step_keeps_lock_dis.
      { split; try by apply PREρlg. }
      2: { left. eauto. }
      simpl. 
      rewrite /ρlg_r.
      congruence. 
    - subst ρlg.
      eapply step_keeps_lock_dis.
      { split; try by apply PREρlg. }
      2: { Unshelve. 2: exact (Some (inr $ env $ (flU (ρlg_l: fmrole TlLM_FM): @EI _ TlEM))).
           econstructor. simpl. 
           (* apply not_live_not_active in DIS; eauto.  *)
           eapply allows_unlock_impl_spec; eauto. }
      congruence. 
    - edestruct does_lock_unlock_incompat; eauto. apply PREρlg.
    - subst ρlg. congruence. 
  Qed.
        
  Lemma kept1:
  @label_kept_state client_model_impl
    (@role_enabled_model client_model_impl (ρ_ext (@flU TlLM_FM ρlg_l)))
    (other_step (ρ_ext (@flU TlLM_FM ρlg_l): fmrole client_model_impl)).
  Proof.
    red. intros [tl_st f] ? [tl_st' f'] **. simpl in STEP.
    destruct oℓ' as [ρ | ].
    2: { by inversion STEP. }
    assert (ρ ≠ ρ_ext (flU (ρlg_l: fmrole TlLM_FM))) as NEQ' by congruence.
    
    assert (f = fs_U /\ does_unlock ρlg_l tl_st /\ disabled_st (ρlg_l: fmrole TlLM_FM) tl_st) as [-> PREρlg].
    { red in Pst. simpl in Pst. apply client_lr_spec in Pst as [? STEP'].
      inversion STEP'; subst; eauto.
      edestruct ρlg_lr_neq; eauto. }      
    
    pose proof (ct_au_L tl_st') as STEPr.
    pattern fs_U in STEPr. erewrite (forall_eq_gen _ fs_U) in STEPr.
    simpl in STEPr. repeat setoid_rewrite curry_uncurry_prop in STEPr.
    red. simpl. apply client_lr_spec.
    eexists. apply STEPr. apply and_assoc.
    inversion STEP; subst.
    - split; [done| ]. 

      eapply step_keeps_unlock_dis.
      { split; try by apply PREρlg. }
      2: { left. eauto. }
      simpl. 
      rewrite /ρlg_l.
      congruence. 
    - done. 
    - edestruct ρlg_lr_neq. eapply has_lock_st_excl with (ρlg1 := ρlg_l); eauto. 
      all: by apply PREρlg.
    - destruct FS as [[? ->] | [[=] ?]]. 
      split; [done| ].
      eapply step_keeps_unlock_dis. 
      { split; try by apply PREρlg. }
      2: { Unshelve. 2: exact (Some (inr $ env $ (flL (ρlg: fmrole TlLM_FM): @EI _ TlEM))).
           econstructor. simpl.
           (* apply not_live_not_active in DIS; eauto.  *)
           eapply allows_lock_impl_spec; eauto. }
      congruence. 
  Qed.

  (* Lemma kept1': *)
  (* @label_kept_state client_model_impl *)
  (*   (@role_enabled_model client_model_impl (ρ_ext (@flL TlLM_FM ρlg_l))) *)
  (*   (other_step (ρ_ext (@flL TlLM_FM ρlg_l): fmrole client_model_impl)). *)
  (* Proof. *)
  (*   red. intros [tl_st f] ? [tl_st' f'] **. simpl in STEP. *)
  (*   destruct oℓ' as [ρ | ]. *)
  (*   2: { by inversion STEP. } *)
  (*   assert (ρ ≠ ρ_ext (flL (ρlg_l: fmrole TlLM_FM))) as NEQ' by congruence. *)

  (*   assert (f = fs_U /\ does_unlock ρlg_l tl_st /\ disabled_st (ρlg_l: fmrole TlLM_FM) tl_st) as [-> PREρlg]. *)
  (*   { red in Pst. simpl in Pst. apply client_lr_spec in Pst as [? STEP']. *)
  (*     inversion STEP'; subst; eauto. *)
  (*     edestruct ρlg_lr_neq; eauto. }       *)
    
  (*   pose proof (ct_au_L tl_st') as STEPr. *)
  (*   pattern fs_U in STEPr. erewrite (forall_eq_gen _ fs_U) in STEPr. *)
  (*   simpl in STEPr. repeat setoid_rewrite curry_uncurry_prop in STEPr. *)
  (*   red. simpl. apply client_lr_spec. *)
  (*   eexists. apply STEPr. apply and_assoc. *)
  (*   inversion STEP; subst. *)
  (*   - split; [done| ].  *)

  (*     eapply step_keeps_unlock_dis. *)
  (*     { split; try by apply PREρlg. } *)
  (*     2: { left. eauto. } *)
  (*     simpl.  *)
  (*     rewrite /ρlg_l. *)
  (*     congruence.  *)
  (*   - done.  *)
  (*   - edestruct ρlg_lr_neq. eapply has_lock_st_excl with (ρlg1 := ρlg_l); eauto.  *)
  (*     all: by apply PREρlg. *)
  (*   - destruct FS as [[? ->] | [[=] ?]].  *)
  (*     split; [done| ]. *)
  (*     eapply step_keeps_unlock_dis.  *)
  (*     { split; try by apply PREρlg. } *)
  (*     2: { Unshelve. 2: exact (Some (inr $ env $ (flL (ρlg: fmrole TlLM_FM): @EI _ TlEM))). *)
  (*          econstructor. simpl. *)
  (*          (* apply not_live_not_active in DIS; eauto.  *) *)
  (*          eapply allows_lock_impl_spec; eauto. } *)
  (*     congruence.  *)
  (* Qed. *)

  Lemma left_kept_disabled:
  @label_kept_state client_model_impl
    (fun st => does_lock ρlg_l st.1 /\ disabled_st ρlg_l st.1)
    (fun _ => True).
  Proof using.
    red. intros δ * [LOCK DIS] _ STEP. 
    inversion STEP; subst; simpl in *; try subst ρlg. 
    { destruct c.
      { destruct DIS. eapply fm_live_spec; eauto. simpl. eauto. }
      eapply step_keeps_lock_dis; eauto.
      2: { simpl. left. simpl. eauto. }
      congruence. }
    { edestruct does_lock_unlock_incompat; eauto. }
    { eapply step_keeps_lock_dis; eauto.
      2: { right. Unshelve.
           2: { apply env. eapply (flU (ρlg_r: fmrole TlLM_FM)). }
           simpl. by apply allows_unlock_impl_spec. }
      congruence. }
    { eapply step_keeps_lock_dis; eauto.
      2: { right. Unshelve.
           2: { apply env. eapply (flL (ρlg_r: fmrole TlLM_FM)). }
           simpl. by apply allows_lock_impl_spec. }
      simpl. intros [=EQ]. by apply symmetry, ρlg_lr_neq in EQ. }
  Qed. 



  (* Lemma tl_subtrace_fair lmtr (tr str: mtrace client_model_impl) k *)
  (*   (OUTER_CORR : client_LM_trace_exposing lmtr tr) *)
  (*   (LEN1': trace_len_is str NOinfinity) *)
  (*   (SUB1 : subtrace tr k NOinfinity = Some str) *)
  (*   (MATCH : client_tl_traces_match str (project_tl_trace str)) *)
  (*   : *)
  (*   ∀ g: Gtl, fair_by_group (ELM_ALM TlEM_EXT_KEEPS) g (project_tl_trace str).  *)
  (* Proof. *)
  (*   forward eapply outer_exposing_subtrace; eauto. *)
  (*   intros [? EXP']. *)
  (*   eapply inner_LM_trace_fair_aux_group. *)
  (*   - apply _. *)
  (*   - done. *)
  (*   - by apply EXP'.  *)
  (*   - simpl. intros ?? [=<-]. *)
  (*     by apply EXP'. *)
  (*   - by apply EXP'. *)
  (*   - by apply MATCH. *)
  (* Qed. *)

  Lemma tl_group_fair (tr: mtrace client_model_impl) 
    (OUTER_CORR : client_LM_trace_exposing tr)
    (MATCH : client_tl_traces_match tr (project_tl_trace tr))
    :
    ∀ g: Gtl, fair_by_group (ELM_ALM TlEM_EXT_KEEPS) g (project_tl_trace tr). 
  Proof.
    (* forward eapply outer_exposing_subtrace; eauto. *)
    destruct OUTER_CORR as [? CORR]. 
    eapply inner_LM_trace_fair_aux_group.
    - apply _.
    - done.
    - by apply CORR. 
    - simpl. intros ?? [=<-].
      by apply CORR. 
    - by apply CORR. 
    - by apply MATCH.
  Qed.

  (* TODO: move *)
  Lemma in_lib_gs_ex ρlg
    (IN: ρlg ∈ lib_gs):
    exists c, ρlg = ρlg_tl c.
  Proof.
    rewrite lib_gs_ρlg !elem_of_union !elem_of_singleton in IN.
    destruct IN as [-> | ->]; eauto. 
  Qed. 

  Lemma client_trace_locks_released
    (ctr : mtrace client_model_impl)
    (ttr: elmftrace)
    i
    c
    (MATCH: client_tl_traces_match ctr ttr)
    (FAIR : ∀ ρ, fair_model_trace ρ ctr)
    (* (INIT : is_init_cl_state (trfirst ctr)) *)
    (UN: forall i st, ctr S!! i = Some st -> unused_not_ρlg st)
    (VALID : mtrace_valid ctr)
    (CEN: forall j st c',
        let ρ' := ρlg_tl c': fmrole TlLM_FM in
        ctr S!! j = Some st -> does_unlock ρ' st.1 -> disabled_st ρ' st.1 ->
                  (i <= j -> c' ≠ c) -> role_enabled_model ((ρ_ext $ flU ρ'): fmrole client_model_impl) st)
    :
    eventual_release ttr (ρlg_tl c) i.
  Proof.
    red. intros ρlg j tl_st **.
    eapply traces_match_state_lookup_2 in JTH as (st&JTH&EQ).
    2: by apply MATCH.
    destruct st as [? f]. simpl in EQ. subst.
    
    set (ρ := ρ_ext $ flU ρlg: fmrole client_model_impl).
    enough (role_enabled_model ρ ((tl_st, f): fmstate client_model_impl) /\
              @label_kept_state client_model_impl
                (@role_enabled_model client_model_impl ρ)
                (other_step ρ)) as [EN KEPT]. 
    { forward eapply kept_state_fair_step.
      5: by apply JTH.
      3: { intros ? P. apply P. }      
      2: { apply KEPT. }
      all: eauto.
      intros (k&?&[[LEk STEP] MIN]&KTH&ENk).

      apply trace_label_lookup_simpl' in STEP as (? & [δ' f'] & KTH').
      exists (k + 1), δ'. repeat split.
      2: lia.
      { apply state_label_lookup in KTH' as (?&KTH'&?).
        eapply traces_match_state_lookup_1 in KTH' as (? & KTH' & EQ).
        2: { eauto. }
        rewrite KTH'. simpl in EQ. subst. auto. }
      
      eapply trace_state_lookup_simpl in KTH; eauto. subst.
      eapply trace_valid_steps' in KTH'.
      2: { eauto. }
      inversion KTH'; subst.
      all: eapply au_impl_spec; eauto;
        apply allows_unlock_impl_spec; eauto. }

    pose proof JTH as JTH_.
    apply UN in JTH. 
    eapply client_trace_ρlg_not_unused in JTH.
    2: { intros ?. eapply unused_does_unlock_incompat; eauto. }
        
    split.
    2: { 
      rewrite lib_gs_ρlg !elem_of_union !elem_of_singleton in JTH.
      destruct JTH as [-> | ->]; subst ρ; [apply kept1| apply kept2]. }

    apply in_lib_gs_ex in JTH as [c' ->].
    eapply CEN; eauto. intros LE ->. tauto. 
  Qed.
    

  Lemma first_tl_subtrace_finite
  (tr : mtrace client_model_impl)
  (* (lmtr : lm_fair_traces.lmftrace) *)
  (OUTER_CORR : client_LM_trace_exposing tr)
  (VALID : mtrace_valid tr)
  (INIT : is_init_cl_state (trfirst tr))
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
    
    destruct (decide (i'_s = NOinfinity)) as [INF| ]. 
    2: { destruct i'_s; set_solver. }

    forward eapply subtrace_state_lookup with (k := 0) as TR0'; eauto.
    { subst. done. }
    simpl in TR0'. rewrite !state_lookup_0 in TR0'.
    inversion TR0' as [TR0]. clear TR0'.

    forward eapply (lock_progress (project_tl_trace str) (ρlg_tl cl_L) 0 (trfirst str).1).
    { by eapply traces_match_valid2. }
    { subst i'_s.
      destruct OUTER_CORR as [??]. 
      forward eapply outer_exposing_subtrace as [??]; eauto.
      eapply tl_group_fair; eauto. red. eauto. }
    { rewrite state_lookup_0. by rewrite project_nested_trfirst. }
    { rewrite TR0. apply INIT. }
    { rewrite TR0. apply INIT. }
    { subst. 
      eapply client_trace_locks_released; eauto.
      { eapply fair_by_subtrace; eauto. }
      { intros. erewrite subtrace_state_lookup in H0; try done. simpl in H0. 
        eapply unused_not_ρlg_trace_preserved; eauto.
        clear -INIT. apply proj2, proj1 in INIT. set_solver. }
      { eapply (subtrace_valid tr); eauto. }
      simpl. intros * JTH U DIS AFTER. specialize (AFTER ltac:(lia)).
      destruct c'; [done| ]. 

      destruct st as [? f]. simpl in *. 
      assert (f = fs_U) as ->.
      { apply trace_state_lookup_simpl' in JTH as (step&JTH&ST).
        erewrite subtrace_lookup in JTH; eauto.
        2: done.
        simpl in JTH. apply STEPs in JTH; [| done].
        destruct JTH as (?&?&?&[=]). subst. by inversion ST. }

      simpl. red. eapply fm_live_spec.
      eapply ct_au_R; eauto. }
    
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
  Proof with (unfold fs_le in *; simpl in *; try auto || lia).
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

    pose proof (INF' 0) as (i & ? & LE1 & ITH & [? ->]).
    apply trace_label_lookup_simpl' in ITH as ([? f1]&[? f1']&ITH).
    assert (fs_le f1' fs_S') as S1.
    { pose proof ITH as STEP. 
      apply trace_state_lookup in ITH.
      forward eapply (client_trace_fs_mono tr 0 i); eauto.
      { by rewrite state_lookup_0. }
      intros.
      eapply trace_valid_steps' in STEP; eauto.
      eapply LT in STEP.
      2: { destruct ((trfirst tr).2), f1; auto... }
      destruct STEP. destruct ((trfirst tr).2), f1, f1'; auto... }
 
    pose proof (INF' (S i)) as (j & ? & LE2 & JTH & [? ->]).
    apply trace_label_lookup_simpl' in JTH as ([? f2]&[? f2']&JTH).
    assert (f2' = fs_O) as ->. 
    { pose proof JTH as STEP. 
      apply trace_state_lookup in JTH.
      forward eapply (client_trace_fs_mono tr (S i) j); eauto.
      { rewrite -Nat.add_1_r. 
        apply state_label_lookup in ITH as (?&?&?). eauto. }
      intros. simpl in *. 
      eapply trace_valid_steps' in STEP; eauto.
      eapply LT in STEP.
      2: { destruct f1', f2; auto... }
      destruct STEP. destruct f1', f2, f2'; auto... }

    exists (S j). intros k ? ? KTH [? ->].
    apply trace_label_lookup_simpl' in KTH as ([? f3]&[? f3']&KTH).
    pose proof KTH as STEP. 
    apply trace_state_lookup in KTH.
    forward eapply (client_trace_fs_mono tr (S j) k); eauto.
    { rewrite -Nat.add_1_r. 
      apply state_label_lookup in JTH as (?&?&?). eauto. }
    intros. simpl in *. destruct f3...  
    eapply trace_valid_steps' in STEP; eauto.
    simpl in STEP. inversion STEP; subst.
    all: clear -FS; set_solver. 
  Qed. 
   
  (* TODO: move *)
  Lemma trace_state_lookup_S {St L: Type} (tr: trace St L) i st1 ℓ st2 
    (ITH: tr !! i = Some (st1, Some (ℓ, st2))):
    tr S!! (S i) = Some st2.
  Proof.
    apply state_label_lookup in ITH as (?&?&?).
    rewrite -Nat.add_1_r. done. 
  Qed.

  (* TODO: move *)
  Instance fs_le_dec x y: Decision (fs_le x y).
  Proof. 
    destruct x, y; simpl; rewrite /fs_le; solve_decision.
  Qed.

  (* TODO: move? *)
  Ltac add_case C name :=
    match goal with
    | |- ?G => assert (C -> G) as name
    end.

  Lemma r_ext_enabled (st: fmstate client_model_impl)
    (UN: does_unlock ρlg_r st.1)
    (DIS: disabled_st ρlg_r st.1)
    (NO: st.2 ≠ fs_O):
  role_enabled_model ((ρ_ext (flU (ρlg_r: fmrole TlLM_FM))): fmrole client_model_impl) st.
  Proof.
    destruct st. simpl in NO.  
    red. eapply fm_live_spec. econstructor; eauto.
    Unshelve. 2: exact (if (decide (f = fs_U)) then fs_U else fs_O).
    destruct f; try tauto.
    { left. by rewrite decide_True. }
    all: right; rewrite decide_False; set_solver.
  Qed.


  Lemma ρlg_r_term (tr: mtrace client_model_impl)
    (FAIR : ∀ ρ, fair_model_trace ρ tr)
    (IN_UN: forall i st, tr S!! i = Some st -> unused_not_ρlg st)
    (EXP: client_LM_trace_exposing tr)
    (VALID: mtrace_valid tr)
    (FLAG: forall i st, tr S!! i = Some st -> fs_le st.2 fs_S)
    (NOLOCKl: forall i st, tr S!! i = Some st ->
                      ¬ (does_unlock ρlg_l st.1 /\ disabled_st ρlg_l st.1))

    :
  ∃ (i : nat) (δ : tl_state),
    tr S!! i = Some (δ, fs_O) ∧ disabled_st ρlg_r δ.
  Proof.
    forward eapply tl_trace_construction as MATCH; eauto.
    assert (∀ g, fair_by_group (ELM_ALM TlEM_EXT_KEEPS) g (project_tl_trace tr)) as FAIR_G.
    { eapply tl_group_fair; eauto. }
    pose proof MATCH as VALID'%traces_match_valid2. 
    
    add_case (exists i δ, tr S!! i = Some (δ, fs_O)) FO.
    { intros [i_ O]. pattern i_ in O. apply min_prop_dec in O as (i & [δ ITH] & MIN).
      2: { admit. }
      clear i_. 
      pose proof ITH as ITH'.
      eapply traces_match_state_lookup_1 in ITH' as (δ_ & ITH' & EQ); [| eauto].
      simpl in EQ. subst δ_. 
      destruct (decide (active_st (ρlg_r: fmrole TlLM_FM) δ)); eauto.

      cut (∃ n st', i < n /\ project_tl_trace tr S!! n = Some st' /\ disabled_st ρlg_r st').
      { intros (j & ? & LTj & JTH & DIS).
        eapply traces_match_state_lookup_2 in JTH as (st & JTH & EQ); [| eauto].
        destruct st. simpl in EQ. subst.
        forward eapply (client_trace_fs_mono tr i j); eauto.
        { lia. }
        simpl. intros. destruct f; try by fs_le_solver.
        eauto. }
      
      destruct (does_lock_unlock_trichotomy δ ρlg_r) as [L | [U | UN]]; cycle -1.
      { edestruct unused_active_incompat; eauto. }
      - forward eapply (lock_progress (project_tl_trace tr) ρlg_r i).
        6: { eapply client_trace_locks_released; eauto.
             intros. destruct c'.
             { edestruct NOLOCKl; eauto. }
             destruct (Nat.le_gt_cases i j) as [LE | LT].
             { tauto. }
             subst ρ'. apply r_ext_enabled; auto.
             destruct st. simpl. intros ->.
             specialize_full MIN.
             { eauto. }
             lia. }
        all: eauto.
        intros (?&?&?&?&?&?). eauto.  
      - forward eapply (unlock_termination (project_tl_trace tr) ρlg_r i); eauto.
        intros (?&?&?&?&?&?). eauto. }

    add_case (exists i δ, tr S!! i = Some (δ, fs_S')) FS'.
    { intros (i & [δ ITH]).      
        
  Admitted. 

  (* Lemma  *)
  (* tr : mtrace client_model_impl *)
  (* VALID : mtrace_valid tr *)
  (* LEN : trace_len_is tr NOinfinity *)
  (* m : nat *)
  (* str : trace client_model_impl (option (fmrole client_model_impl)) *)
  (* SUB : subtrace tr (S m) NOinfinity = Some str *)
  (* ============================ *)
  (* ∀ (i : nat) (res : model_trace_step client_model_impl), *)
  (*   str !! i = Some res → is_tl_step res ∨ is_end_state res *)

  Lemma client_model_fair_term (tr: mtrace client_model_impl)
    (* lmtr *)
    (OUTER_CORR: client_LM_trace_exposing tr)
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

    assert (ρ = Some $ ρ_ext $ flU (ρlg_l: fmrole TlLM_FM)) as ->.
    { inversion STEP; subst; try done.
      all: clear -FS; set_solver. }
    
    forward eapply (tl_trace_construction str) as MATCH. 
    { subst. eapply (subtrace_valid tr); eauto. done. }    

    assert (exists p st_p, tr S!! p = Some st_p /\ does_lock ρlg_l st_p.1 /\ disabled_st ρlg_l st_p.1 /\ S m <= p) as (p & st_p & PTH & Ll & DISl & LEp).
    { inversion STEP; subst.
      2: { subst ρlg. edestruct ρlg_lr_neq; eauto. }
      apply state_label_lookup in MTH as (_&M'TH&_).
      rewrite Nat.add_1_r (plus_n_O (S m)) in M'TH. 
      erewrite <- subtrace_state_lookup in M'TH; eauto.
      forward eapply allows_unlock_impl_spec. intros AU%proj2. specialize_full AU.
      { eauto. }
      apply au_impl_spec in AU. 
      forward eapply (unlock_termination (project_tl_trace str) (ρlg_l) 0).
      { eapply traces_match_valid2; eauto. }
      { destruct OUTER_CORR as [??]. 
        forward eapply outer_exposing_subtrace as [??]; eauto.
        eapply tl_group_fair; eauto. red. eauto. }
      { apply traces_match_first in MATCH.
        rewrite state_lookup_0. rewrite state_lookup_0 in M'TH.
        apply Some_inj in M'TH. rewrite M'TH in MATCH.
        rewrite -MATCH. simpl. reflexivity. }
      { apply AU. }
      { apply AU. }
      intros (p&?&?&PTH&?&?).
      eapply traces_match_state_lookup_2 in PTH as (?&PTH&?).
      2: by apply MATCH.
      simpl in *. subst.
      exists (S m + p). eexists. erewrite <- subtrace_state_lookup; eauto.
      repeat split; eauto. lia. }    

    enough (exists t δ_t, p <= t /\ str S!! t = Some (δ_t, fs_O) /\ disabled_st ρlg_r δ_t) as FIN.
    { destruct FIN as (t & δ_t & LEt & TTH & DISr).
      apply trace_state_lookup_simpl' in TTH as [[? step] [TTH EQ]].
      simpl in EQ. subst. destruct step as [[ρ δ_t']|].
      2: { forward eapply trace_lookup_dom_eq; eauto.
           intros X%proj1. specialize_full X; eauto. congruence. }
      clear STEP. pose proof TTH as STEP. eapply trace_valid_steps' in STEP; eauto. 
      2: { eapply traces_match_valid1; eauto. }
      inversion STEP; subst.
      2, 3: clear -FS; set_solver.
      enough (disabled_st (ρlg_tl c) δ_t) as DIS. 
      { destruct DIS. eapply fm_live_spec; eauto. }
      destruct c.
      2: { done. }
      
      forward eapply (@steps_keep_state_inf _ tr) with (P := fun c => does_lock (ρlg_l: fmrole TlLM_FM) c.1 /\ disabled_st (ρlg_l: fmrole TlLM_FM) c.1) (Pl := fun _ => True). 
      { eauto. } 
      { eexists. split; [apply PTH| ]. eauto. }
      2: done.
      3: { erewrite <- subtrace_state_lookup. 
           { eapply trace_state_lookup. apply TTH. }
           all: eauto. }
      2: { lia. }
      2: { simpl. apply proj2. }
      apply left_kept_disabled. }

    destruct (after p str) as [rtr| ] eqn:AFTERp.
    2: { apply terminating_trace_equiv in LEN2. apply proj1 in LEN2.
         edestruct LEN2 as [? ?]; [| done].
         red. eauto. }
 
    forward eapply (ρlg_r_term rtr) as (t & δ_t & TTH & DISr).
    { intros. eapply fair_by_after; eauto.
      eapply fair_by_subtrace; eauto. }
    { intros.
      erewrite state_lookup_after in H0; eauto. 
      erewrite subtrace_state_lookup in H0; try done. simpl in H0. 
      eapply unused_not_ρlg_trace_preserved; eauto.
      clear -INIT. apply proj2, proj1 in INIT. set_solver. }
    { destruct OUTER_CORR as [??].
      forward eapply outer_exposing_subtrace as [??]; eauto. 
      eapply outer_exposing_after; eauto. }
    { subst. eapply trace_valid_after; eauto. 
      eapply (subtrace_valid tr); eauto. done. }    
    { intros * ITH.
      erewrite state_lookup_after in ITH; eauto. 
      forward eapply client_trace_fs_mono.
      3: { apply trace_state_lookup_S in MTH.
           erewrite (plus_n_O (S m)), <- subtrace_state_lookup in MTH; eauto. }
      3: { apply ITH. }
      all: eauto. 
      { eapply (subtrace_valid tr); eauto. done. }
      lia. }
    { intros.
      apply Nat.le_sum in LEp as [d ->].
      erewrite <- subtrace_state_lookup in PTH; eauto.
      forward eapply (@steps_keep_state_inf _ str). 
      { eapply (subtrace_valid tr); eauto. done. }
      2: by apply left_kept_disabled.
      { eauto. }
      { done. }
      2: { erewrite state_lookup_after in H0; eauto. }
      { lia. }
      simpl. intros [? ?] [? ?]. edestruct does_lock_unlock_incompat; eauto. }

    erewrite state_lookup_after in TTH; eauto. 
    do 2 eexists. split; [| split].
    2: by apply TTH.
    { lia. }
    eauto. 
  Qed. 

End ClientDefs. 
