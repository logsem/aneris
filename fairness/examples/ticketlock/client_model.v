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
  
  Definition lib_gs: gset Gtl := gls get_Gtls 2.
  Definition ρlg_tl i := ρlg_i get_Gtls 2 i.
  Definition ρlg_l := ρlg_tl 0.
  Definition ρlg_r := ρlg_tl 1. 

  Lemma lib_gs_ρlg:
    lib_gs = {[ ρlg_l; ρlg_r ]}.
  Proof.
    rewrite /lib_gs /ρlg_l /ρlg_r.
    rewrite gls_ρlg. simpl. set_solver.
  Qed. 

  Lemma lib_gs_ne: lib_gs ≠ ∅.
  Proof. rewrite lib_gs_ρlg. set_solver. Qed.

  Lemma ρlg_in_lib_gs: forall i (LT: i < 2), ρlg_tl i ∈ lib_gs.
  Proof. 
    rewrite lib_gs_ρlg. simpl. intros i DOM.
    destruct i as [| i]; [| destruct i].
    1, 2: set_solver.
    lia. 
  Qed. 

  Context {Mtl: FairModel}.  

  Context {TlLM': forall gs, LiveModel Gtl Mtl (LSI_groups_fixed gs)}.  
  Context (TlLM_LFP': ∀ gs: gset Gtl, gs ≠ ∅ → LMFairPre (TlLM' gs)).
  Context `{TlEM': forall gs (NE: gs ≠ ∅), ExtModel (LM_Fair (LF := TlLM_LFP' _ NE))}. 

  Definition TlLM := TlLM' lib_gs. 
  Definition TlLM_LFP := TlLM_LFP' _ lib_gs_ne.
  Definition TlLM_FM := LM_Fair (LF := TlLM_LFP).
  Definition TlEM := TlEM' _ lib_gs_ne. 

  Let tl_st := fmstate TlLM_FM. 
  Let lib_role := fmrole TlLM_FM.
  Let lib_erole := @ext_role _ TlEM.

  Inductive flag_state := | fs_U | fs_S | fs_O. 
  Definition client_state: Type := tl_st * flag_state.

  (* Inductive cl_role := | cl_l | cl_r.  *)
  (* we don't really need roles besides those provided by library:
     every client thread corresponds to an exact pair of a library' and ext roles.
     The only problem is that it complicates (?) subtraces projection a bit. *)

  Definition client_role: Type := lib_erole. 

  (* Definition ρ_cl: client_role := inr ρy. *)
  Definition ρ_lib i: client_role := inl $ ρlg_tl i.
  (* TODO: move tl_ETs-related stuff to the level of FairLock *)
  Definition ρ_ext i: client_role := inr $ env (eiG ρlg) (EM := TlEM).
  
  (* Inductive client_trans: client_state -> option client_role -> client_state -> Prop := *)
  (* | ct_y_step_3 lb: *)
  (*   client_trans (lb, 3) (Some ρ_cl) (lb, 2) *)
  (* (* TODO: allow arbitrary library's LM roles *) *)
  (* | ct_lib_ext lb (STOP: lm_is_stopped ρlg lb): *)
  (*   client_trans (lb, 2) (Some ρ_ext) (reset_lm_st ρlg lb ρlg_in_lib_gs, 1) *)
  (* | ct_lib_step lb1 lb2 (LIB_STEP: fmtrans lf lb1 (Some ρlg) lb2): *)
  (*   client_trans (lb1, 1) (Some ρ_lib) (lb2, 1) *)
  (* | ct_y_step_1 (lb: fmstate lf) *)
  (*               (* (LIB_NOSTEP: 0 ∉ live_roles _ lb) *) *)
  (*               (LIB_NOROLES: ls_tmap lb (LM := lib_model lib_gs) !! ρlg = Some ∅) *)
  (*   : *)
  (*   client_trans (lb, 1) (Some ρ_cl) (lb, 0) *)
  (* . *)


End ClientDefs. 
