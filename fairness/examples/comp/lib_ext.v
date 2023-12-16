From iris.proofmode Require Import tactics.
From trillium.fairness.ext_models Require Import ext_models. 
From trillium.fairness Require Import lm_fair.
From trillium.fairness.examples.comp Require Import lib. 

Close Scope Z_scope.


Section ExtModelInner.

  (* TODO: try to find an appropriate definition for functional relations,
       try to remove duplication between function and relation
       (maybe change ETs definition?) *)
  Definition reset_st_impl (st: fmstate lib_model_impl): fmstate lib_model_impl := 1. 
  
  Definition reset_st (st: fmstate lib_model_impl): option (fmstate lib_model_impl) :=
    if (decide (st = 0)) then Some (reset_st_impl st) else None.
  Definition reset_st_rel: relation (fmstate lib_model_impl) :=
    fun x y => reset_st x = Some y. 

  Definition lib_EI := unit.     
  Definition lib_ETs (ι: lib_EI) := reset_st_rel.

  (* TODO: avoid duplication *)
  Definition lib_active_exts (st: fmstate lib_model_impl): gset lib_EI := 
    if (decide (st = 0)) then {[ () ]} else ∅. 
  
  Lemma lib_active_exts_spec st ι:
    ι ∈ lib_active_exts st <-> ∃ st', lib_ETs ι st st'.
  Proof using.  
    rewrite /lib_active_exts /lib_ETs /reset_st_rel /reset_st.
    destruct st; [erewrite !decide_True | erewrite !decide_False]; set_solver.
  Qed. 

  Instance ExtLib: ExtModel lib_model_impl := 
    Build_ExtModel lib_model_impl _ _ _ _ _ lib_active_exts_spec.

End ExtModelInner.

Section ExtModelLM.
  Context {gs: gset lib_grole} {NE: gs ≠ ∅}.
  Let lf := lib_fair _ NE. 

  Definition lm_is_stopped (ρlg: fmrole lf) (δ: fmstate lf) := 
    ls_under δ = 0 /\ (* TODO: get rid of this duplication *)
    ρl ∉ dom (ls_mapping δ) /\
    (* ρlg ∈ dom (ls_tmap δ (LM := lib_model gs)). *)
    ls_tmap δ !! ρlg = Some ∅. 

  Definition reset_lm_st (ρlg: fmrole lf) (δ: fmstate lf)
    (IN: ρlg ∈ gs)
    : fmstate lf.
    Set Printing Coercions.
    set tm' :=
        let tm_ := (fun ρs => ρs ∖ {[ ρl ]}) <$> (ls_tmap δ) in
        <[ ρlg := {[ ρl ]} ]> tm_. 
    eapply (build_LS_ext (reset_st_impl (ls_under δ)) (<[ρl := lm_fl (lib_model gs) δ]> (ls_fuel δ)) _ tm').
    - intros. rewrite dom_insert.
      subst tm'. simpl. setoid_rewrite lookup_insert_Some.
      setoid_rewrite lookup_fmap_Some.
      rewrite elem_of_union elem_of_singleton.
      split.
      + intros _. 
        exists ρlg. exists {[ ρl ]}. split; [| set_solver]. left. done.
      + intros (?&?&[PROP DOM]). destruct PROP as [[<- <-] | PROP].
        * apply elem_of_singleton in DOM. subst. eauto.
        * destruct PROP as [NEQ (? & <- & TM)].
          right. rewrite -ls_same_doms.
          apply elem_of_dom. exists x.
          eapply ls_mapping_tmap_corr.
          exists x1. split; set_solver.
    - intros ???? NEQ TM'1 TM'2. subst tm'. simpl in *.
      rewrite !lookup_insert_Some in TM'1, TM'2.
      rewrite !lookup_fmap_Some in TM'1, TM'2.
      destruct TM'1 as [[<- <-] | TM'1], TM'2 as [[<- <-] | TM'2].
      + congruence.
      + set_solver.
      + set_solver.
      + destruct TM'1 as [NEQ1 (?&<-&TM1)], TM'2 as [NEQ2 (?&<-&TM2)].
        apply disjoint_difference_r2, disjoint_difference_l2.
        eapply ls_tmap_disj; [| apply TM1| apply TM2]. congruence.
    - red. intros. subst tm'. simpl.
      rewrite dom_insert dom_fmap. apply union_subseteq. split; [set_solver| ].
      apply δ. 
    Unshelve.
    + simpl.
      Transparent lib_model_impl.
      set_solver.
  Defined.

  (* Definition reset_lm_st (ρlg: fmrole lib_fair) (δ: fmstate lib_fair): option (fmstate lib_fair) := *)
  (*   match decide (lm_is_stopped ρlg δ) with *)
  (*   | left STOP => Some (reset_lm_st_impl ρlg δ STOP) *)
  (*   | _ => None *)
  (*   end. *)

  Definition reset_lm_st_rel ρlg: relation (fmstate lf) :=
    fun x y => lm_is_stopped ρlg x /\ exists IN, reset_lm_st ρlg x IN = y.

  Inductive lib_lm_EI := eiG (ρlg: lib_grole).

  Instance lib_lm_EI_eqdec: EqDecision lib_lm_EI.
  Proof. solve_decision. Qed. 

  Instance lib_lm_EI_cnt: Countable lib_lm_EI.
  Proof.
    apply inj_countable' with
      (f := fun ι => match ι with | eiG ρlg => ρlg end)
      (g := eiG).
    intros. by destruct x. 
  Qed.  

  (* TODO: avoid duplication *)
  Definition lib_lm_active_exts (δ: fmstate lf): gset lib_lm_EI := 
    (* set_map eiG $ filter (flip lm_is_stopped δ) (dom (ls_tmap δ (LM := (lib_model gs)))).  *)
    set_map eiG $ filter (flip lm_is_stopped δ) gs. 
  
  Definition lib_lm_ETs '(eiG ρlg) := reset_lm_st_rel ρlg. 

  Definition lib_lm_projEI (_: lib_lm_EI) := (tt: lib_EI).

  Lemma lib_lm_active_exts_spec:
    ∀ δ ι, ι ∈ lib_lm_active_exts δ ↔ (∃ δ' : lf, lib_lm_ETs ι δ δ'). 
  Proof using.
    intros. 
    destruct ι. simpl.
    rewrite /lib_lm_active_exts /reset_lm_st_rel.
    erewrite <- set_map_properties.elem_of_map_inj_gset.
    2: { red. by intros ??[=]. }    
    rewrite elem_of_filter. simpl.
    rewrite ex_and_comm. apply Morphisms_Prop.and_iff_morphism; [done| ].
    split; try eauto.
    by intros (?&?&<-).
    Unshelve. done. 
  Qed.

  Definition ExtLibLM: ExtModel (LM_Fair (LM := lib_model gs)) :=
    Build_ExtModel (LM_Fair (LM := lib_model gs)) _ _ _ _ _ lib_lm_active_exts_spec. 

  Lemma lib_proj_keep_ext:
    ∀ (δ1 : LM_Fair) ι (δ2 : LM_Fair), 
      @ETs _ ExtLibLM ι δ1 δ2 → @ETs _ ExtLib (lib_lm_projEI ι) (ls_under δ1) (ls_under δ2). 
  Proof.
    intros. simpl in *. destruct ι; simpl in *.
    simpl. rewrite /lib_lm_projEI. simpl. do 2 red.
    red in H. revert H. 
    intros [? (?&<-)]. simpl.
    rewrite /reset_st. rewrite decide_True; [| by apply H].
    done. 
  Qed.

  Lemma reset_lm_st_map (ρlg: fmrole lf) (δ: fmstate lf) (IN: ρlg ∈ gs)
    (STOP: lm_is_stopped ρlg δ):
    ls_mapping (reset_lm_st ρlg δ IN) = <[ρl := ρlg]> (ls_mapping δ).
  Proof.
    apply build_LS_ext_spec_mapping. simpl.
    red. intros ρ g. rewrite lookup_insert_Some.
    setoid_rewrite lookup_insert_Some. setoid_rewrite lookup_fmap_Some.
    split.
    - intros [[<- <-] | [NEQ MAP]].
      + eexists. split; [left; eauto| ]. done.
      + destruct STOP as (?&?&?). 
        eapply (ls_mapping_tmap_corr δ) in MAP as (?&?&?).
        destruct (decide (ρlg = g)).
        { subst g. set_solver. } 
        eexists. split; [| eauto]. right. split; eauto.
        eexists. split; eauto.
        apply difference_disjoint_L.
        apply disjoint_singleton_r. intros IN'.
        apply H0. apply elem_of_dom. exists g.
        eapply ls_mapping_tmap_corr; eauto.
    - intros (R & PROP & INR).
      destruct PROP as [[<- <-] | PROP].
      + apply elem_of_singleton in INR. subst. tauto.
      + right. destruct PROP as [NEQ (?&<-&TM)].
        split.
        * set_solver.
        * eapply (ls_mapping_tmap_corr δ). eexists. split; eauto.
          set_solver.
  Qed.
    

  Lemma lib_keeps_asg: ∀ (δ1 : LM_Fair) (ι : env_role) (δ2 : LM_Fair) ρ τ (f : nat),
     @ext_trans _ ExtLibLM δ1 (Some (inr ι)) δ2
     → ls_mapping δ1 !! ρ = Some τ
       → ls_fuel δ1 !! ρ = Some f
         → ls_mapping δ2 !! ρ = Some τ ∧ ls_fuel δ2 !! ρ = Some f.
  Proof.
    intros. inversion H. subst.
    simpl in REL. destruct ι0. simpl in REL.
    red in REL. destruct REL as [STOP [IN <-]].
    simpl. 
    rewrite reset_lm_st_map; auto.
    red in STOP. destruct STOP as (?&NIN&DOMg).
    split.
    - rewrite lookup_insert_ne; auto. intros <-.
      apply NIN. apply elem_of_dom. set_solver.
    - rewrite lookup_insert_ne; auto. intros <-.
      apply NIN. apply elem_of_dom. set_solver.
  Qed.

  Lemma lib_reset_premise lb (STOP: lm_is_stopped ρlg lb) (IN: ρlg ∈ gs):
    lib_ls_premise gs (reset_lm_st ρlg lb IN).
  Proof. 
    red. repeat split; simpl.
    - rewrite lookup_insert. done. 
    - simpl. rewrite lookup_insert. done. 
  Qed. 

End ExtModelLM. 
