From iris.proofmode Require Import tactics.
From trillium.fairness.ext_models Require Import ext_models. 
From trillium.fairness Require Import lm_fair fuel_ext.
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
    ρlg ∈ dom (ls_tmap δ (LM := lib_model gs)).

  (* TODO: implement it via ls_tmap*)
  Definition reset_lm_st (ρlg: fmrole lf) (δ: fmstate lf)
    (IN: ρlg ∈ gs)
    : fmstate lf.
    refine 
      {| ls_under := reset_st_impl (ls_under δ); 
        ls_mapping := <[ρl := ρlg]> (ls_mapping δ);
        ls_fuel := <[ρl := lm_fl (lib_model gs) δ]> (ls_fuel δ) |}.
    - (* TODO: merge model files, get rid of this *)
      Transparent lib_model_impl. 
      set_solver.
    - rewrite !dom_insert_L. by rewrite ls_same_doms.
    - red. intros.
      done.
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

  (* TODO: move, find existing? *)
  Lemma iff_and_impl_helper {A B: Prop} (AB: A -> B):
    A /\ B <-> A.
  Proof. tauto. Qed.     
  Lemma iff_True_helper {A: Prop}:
    (A <-> True) <-> A.
  Proof. tauto. Qed.     
  Lemma iff_False_helper {A: Prop}:
    (A <-> False) <-> ¬ A.
  Proof. tauto. Qed.
  Lemma ex_and_comm {T: Type} (A: Prop) (B: T -> Prop):
    (exists t, A /\ B t) <-> A /\ exists t, B t.
  Proof. split; intros (?&?&?); eauto. Qed. 

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
    red in STOP. destruct STOP as (?&NIN&DOMg). split.
    - rewrite lookup_insert_ne; auto. intros <-.
      apply NIN. apply elem_of_dom. set_solver.
    - rewrite lookup_insert_ne; auto. intros <-.
      apply NIN. apply elem_of_dom. set_solver.
  Qed.

End ExtModelLM. 
