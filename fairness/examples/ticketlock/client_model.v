From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fair_termination.
From trillium.fairness Require Import trace_helpers.
(* TODO: rearrange the code *)
From trillium.fairness Require Import lemmas trace_len trace_lookup fuel lm_fair.
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

  Lemma gls'_ρlg n:
    gls' n = map (ρlg_i n) (seq 0 n). 
  Proof.
    assert (length (gls' n) = n) as LEN'. 
    { rewrite /gls'. destruct decide.
      - rewrite length_remove_NoDup.
        2: { rewrite /get_Gls'. apply NoDup_elements. }
        rewrite decide_True; [| done].
        rewrite get_Gls'_len. lia. 
      - rewrite skipn_length.
        rewrite get_Gls'_len. lia. }
    
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

  Lemma lib_gs_ρlg:
    lib_gs = {[ ρlg_l; ρlg_r ]}.
  Proof.
    rewrite /lib_gs /ρlg_l /ρlg_r.
    rewrite gls_ρlg. simpl. set_solver.
  Qed. 

  Lemma lib_gs_ne: lib_gs ≠ ∅.
  Proof. rewrite lib_gs_ρlg. set_solver. Qed.

  Lemma ρlg_in_lib_gs: forall c, ρlg_tl c ∈ lib_gs.
  Proof. 
    rewrite lib_gs_ρlg. intros c.
    destruct c; set_solver. 
  Qed. 

  Context {Mtl: FairModel}.  

  Context {TlLM': forall gs, LiveModel Gtl Mtl (LSI_groups_fixed gs)}.  
  Context (TlLM_LFP': ∀ gs: gset Gtl, gs ≠ ∅ → LMFairPre (TlLM' gs)).
  Context (TlEM': forall gs (NE: gs ≠ ∅), ExtModel (LM_Fair (LF := TlLM_LFP' _ NE))).

  Definition TlLM := TlLM' lib_gs. 
  Definition TlLM_LFP := TlLM_LFP' _ lib_gs_ne.
  Definition TlLM_FM := LM_Fair (LF := TlLM_LFP).
  Definition TlEM := TlEM' _ lib_gs_ne.

  (* TODO: reorganize the premises so those below don't depend
     on the client's choice of lib_gs *)
  Let tl_st := fmstate TlLM_FM. 
  Let tl_role := fmrole TlLM_FM.
  Let tl_erole := @ext_role _ TlEM.

  Context
    {allows_unlock: tl_st → tl_st → Prop}
    {allows_lock: tl_role → tl_st → tl_st → Prop}
    {tl_active_exts: tl_st → gset (fl_EI (M := TlLM_FM))}
    (tl_active_exts_spec: ∀ st ι,
        ι ∈ tl_active_exts st ↔ (∃ st', @fl_ETs _ allows_unlock allows_lock ι st st')). 
  Context {can_lock_st has_lock_st active_st: tl_role → tl_st → Prop}. 
  Context {is_init_st: tl_st → Prop}.

  Context (TlEM_FL: @FairLock TlLM_FM _ _ _ tl_active_exts_spec
                      can_lock_st has_lock_st active_st is_init_st).

  Inductive flag_state := | fs_U | fs_S | fs_O. 
  Definition client_state: Type := tl_st * flag_state.

  (* Inductive cl_role := | cl_l | cl_r.  *)
  Inductive cl_role_kind := | cl_lift | cl_au | cl_al | cl_cl.
  Definition client_role: Type := cl_role_kind * cl_id. 

  (* (* Definition ρ_cl: client_role := inr ρy. *) *)
  (* Definition ρ_lib i: client_role := inl $ ρlg_tl i. *)
  (* Definition ρ_ext i: client_role := inr $ env (eiG ρlg) (EM := TlEM). *)

  Let allow_unlock_impl := allow_unlock_impl _ _ _ _ _ _ (FairLock := TlEM_FL). 
  Let allow_lock_impl := allow_lock_impl _ _ _ _ _ _ (FairLock := TlEM_FL). 
  
  Inductive client_trans: client_state -> option client_role -> client_state -> Prop :=
  | ct_lib_step tl1 tl2 c flag
        (LIB_STEP: fmtrans TlLM_FM tl1 (Some (ρlg_tl c)) tl2):
      client_trans (tl1, flag) (Some (cl_lift, c)) (tl2, flag)
  | ct_flag_US tl 
      (LOCK: has_lock_st (ρlg_tl cl_L) tl)
      (DIS: ¬ active_st (ρlg_tl cl_L) tl):
    client_trans (tl, fs_U) (Some (cl_cl, cl_L)) (tl, fs_S)
  | ct_au_L tl (ρlg := ρlg_l)
      (LOCK: has_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl):
    client_trans (tl, fs_S) (Some (cl_au, cl_L)) (allow_unlock_impl tl, fs_S)
  | ct_au_R tl fs
      (ρlg := ρlg_r)
      (fs' := match fs with | fs_U => fs_U | _ => fs_O end) (* fs=O is impossible though*)
      (LOCK: has_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl):
    client_trans (tl, fs) (Some (cl_au, cl_R)) (allow_unlock_impl tl, fs')
  | ct_al_R tl fs
      (ρlg := ρlg_r)
      (CANL: can_lock_st ρlg tl)
      (DIS: ¬ active_st ρlg tl)
      (NO: fs ≠ fs_O):
    client_trans (tl, fs) (Some (cl_al, cl_R)) (allow_lock_impl ρlg tl, fs)
  . 

End ClientDefs. 
