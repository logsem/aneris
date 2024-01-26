From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness Require Import trace_helpers.
From stdpp Require Import finite.
From trillium.fairness.ext_models Require Import ext_models destutter_ext.
From trillium.fairness.examples.ticketlock Require Import fair_lock group_roles.
From trillium.fairness.heap_lang Require Export lang.
From trillium.fairness Require Import lemmas trace_len fuel lm_fair lm_fair_traces subtrace comp_utils my_omega lm_fairness_preservation lm_fairness_preservation_wip trace_lookup fairness_finiteness.
From trillium.fairness.heap_lang Require Import simulation_adequacy_lm_ext.

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


Class FLSubmodel := {
    Gtl: Type;
    eqdGtl :> EqDecision Gtl;
    cntGtl :> Countable Gtl;
    lib_gs: gset Gtl;
    SIZE2: size lib_gs = 2;

    Mtl: FairModel;
    TlLSI: fmstate Mtl -> @groups_map _ Mtl _ _ -> @fuel_map Mtl -> Prop;
    TlLSI_LGF: forall st tm fm, TlLSI st tm fm -> LSI_groups_fixed lib_gs st tm fm;
    TlLM: LiveModel Gtl Mtl TlLSI;

    TlLM_LFP: LMFairPre TlLM;
    TlLM_FM := LM_Fair (LF := TlLM_LFP);

    TlLM_nexts: forall δ_lib, @next_states TlLM_FM δ_lib;
    tl_FLP :> FairLockPredicates TlLM_FM;
    tl_FLE :> @FairLockExt TlLM_FM tl_FLP;

    TlEM := FL_EM tl_FLE;
    TlEM_EXT_KEEPS: ext_keeps_asg (ELM := TlEM);
    TlEM_FL :> @FairLock TlLM_FM tl_FLP tl_FLE (fun tr => forall g, fair_by_group (ELM_ALM TlEM_EXT_KEEPS) g tr);

    Mtl_EM: ExtModel Mtl;
    proj_ext : @EI _ TlEM → @EI _ Mtl_EM;
    PROJ_KEEP_EXT: forall δ1 ι δ2, (@ETs _ TlEM) ι δ1 δ2 -> 
                (@ETs _ Mtl_EM) (proj_ext ι) (ls_under δ1) (ls_under δ2);
  }.
  

Set Implicit Arguments. 

(* TODO: replace 'Tl' prefixes with 'Fl' *)
Section ClientDefs.
  
  (* Context {Gtl: Type} `{Countable Gtl}. *)
  (* Context (lib_gs: gset Gtl). *)
  (* Context (SIZE2: size lib_gs = 2).    *)
  (* Context {Mtl: FairModel}. *)

  (* Context {TlLSI: fmstate Mtl -> @groups_map _ Mtl _ _ -> @fuel_map Mtl -> Prop} {TlLSI_LGF: forall st tm fm, TlLSI st tm fm -> LSI_groups_fixed lib_gs st tm fm}.  *)
  (* Context {TlLM: LiveModel Gtl Mtl TlLSI}. *)
  (* Context (TlLM_LFP: LMFairPre TlLM). *)

  (* Definition TlLM_FM := LM_Fair (LF := TlLM_LFP). *)

  (* Context (TlLM_nexts: forall δ_lib, @next_states TlLM_FM δ_lib). *)

  (* Context {tl_FLP : FairLockPredicates TlLM_FM}.  *)
  (* Context {tl_FLE: @FairLockExt TlLM_FM tl_FLP}.  *)
  (* Let TlEM := FL_EM tl_FLE. *)
  (* Context (TlEM_EXT_KEEPS: ext_keeps_asg (ELM := TlEM)). *)

  (* Context (TlEM_FL: @FairLock TlLM_FM tl_FLP tl_FLE (fun tr => forall g, fair_by_group (ELM_ALM TlEM_EXT_KEEPS) g tr)). *)

  (* Context (Mtl_EM: ExtModel Mtl).  *)
  (* Context {proj_ext : @EI _ TlEM → @EI _ Mtl_EM}.  *)
  (* Hypothesis PROJ_KEEP_EXT: *)
  (*   forall δ1 ι δ2, (@ETs _ TlEM) ι δ1 δ2 ->  *)
  (*               (@ETs _ Mtl_EM) (proj_ext ι) (ls_under δ1) (ls_under δ2).  *)
  Context {FLS: FLSubmodel}. 

  Inductive cl_id := | cl_L | cl_R.
  Definition cl_id_nat c := match c with | cl_L => 0 | cl_R => 1 end.

  Lemma cin_lt c: cl_id_nat c < 2.
  Proof. destruct c; simpl; lia. Qed.  

  Definition ρlg_tl (c: cl_id): Gtl.
    apply (nth_sized (cl_id_nat c) lib_gs).
    rewrite SIZE2. apply cin_lt.
  Defined.

  Definition ρlg_l: Gtl := ρlg_tl cl_L. 
  Definition ρlg_r: Gtl := ρlg_tl cl_R. 

  Lemma lib_gs_ρlg:
    lib_gs = {[ ρlg_l; ρlg_r ]}.
  Proof.
    apply set_eq. intros.
    rewrite nth_sized_elem_of.
    rewrite /ρlg_l /ρlg_r. 
  Admitted. 

  (* lib_gs *)
  (* About lib_gs. *)
  Lemma lib_gs_ne: lib_gs ≠ ∅.
  Proof.
    destruct FLS. simpl.  
    intros ->. by rewrite size_empty in SIZE3.
  Qed. 

  Lemma ρlg_lr_neq: ρlg_l ≠ ρlg_r.
  Proof.
    intros EQ. 
  (*   intros EQ%ρlg_i_dom_inj; [done|..].  *)
  (*   all: simpl; lia. *)
  (* Qed.  *)
  Admitted. 

  Lemma ρlg_tl_inj: Inj eq eq ρlg_tl.
  Proof.
  Admitted.

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
  | ct_au_L tl (ρlg := ρlg_l: fmrole TlLM_FM)
      (LOCK: does_unlock ρlg tl)
      (* (DIS: ¬ active_st ρlg tl) *)
      (* (DIS: ¬ role_enabled_model (ρlg: fmrole TlLM_FM) tl) *)
      (DIS: disabled_st (ρlg: fmrole TlLM_FM) tl)
    :
    client_trans (tl, fs_U) (Some $ ρ_ext $ flU (ρlg: fmrole TlLM_FM)) (allow_unlock_impl ρlg tl, fs_S)
  | ct_au_R tl fs fs'
      (ρlg := ρlg_r: fmrole TlLM_FM)
      (FS: fs = fs_U /\ fs' = fs_U \/ (fs = fs_S \/ fs = fs_S') /\ fs' = fs_O)
      (LOCK: does_unlock ρlg tl)
      (* (DIS: ¬ active_st ρlg tl) *)
      (* (DIS: ¬ role_enabled_model (ρlg: fmrole TlLM_FM) tl) *)
      (DIS: disabled_st (ρlg: fmrole TlLM_FM) tl)
    :
    client_trans (tl, fs) (Some $ ρ_ext $ flU (ρlg: fmrole TlLM_FM)) (allow_unlock_impl ρlg tl, fs')
  | ct_al_R tl fs fs'
      (ρlg := ρlg_r: fmrole TlLM_FM)
      (CANL: does_lock ρlg tl)
      (* (DIS: ¬ active_st ρlg tl) *)
      (* (NO: fs ≠ fs_O) *)
      (* (DIS: ¬ role_enabled_model (ρlg: fmrole TlLM_FM) tl) *)
      (DIS: disabled_st (ρlg: fmrole TlLM_FM) tl)
      (FS: fs = fs_U /\ fs' = fs_U \/ fs = fs_S /\ fs' = fs_S')
    :
    client_trans (tl, fs) (Some $ ρ_ext $ flL (ρlg: fmrole TlLM_FM)) (allow_lock_impl ρlg tl, fs')
  .

  Global Instance flag_state_dec: EqDecision flag_state.
  Proof. solve_decision. Qed.   
  Global Instance cl_id_dec: EqDecision cl_id.
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

  Instance client_eq: EqDecision client_state.
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
        apply ρlg_tl_inj in H. subst. 
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
      2: { symmetry. eapply ex_det_iff. intros ? ([??]&?). symmetry. apply H0. }
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

  Global Instance client_LSI_dec: 
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
    
  Global Instance client_LF: LMFairPre client_model.
  esplit; apply _.
  Defined.

End ClientDefs. 
