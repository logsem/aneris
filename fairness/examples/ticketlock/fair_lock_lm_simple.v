From trillium.fairness.examples.ticketlock Require Import fair_lock_simple.
From trillium.fairness.ext_models Require Import ext_models destutter_ext. 
From iris.proofmode Require Import tactics.
From stdpp Require Import base.
From trillium.fairness Require Import  lm_fair_traces trace_helpers fuel lm_fair lm_fairness_preservation trace_lookup.


Section FairLockLM.
  
  Context `(FL: @FairLock M FLP FLE inner_fair_ext_model_trace).

  Let R := fmrole M.
  (* For the lock model (and others that also don't fork),
     we suppose that every group contains up to one role, 
     and this role uniquely corresponds to that group.
     Therefore, LM here only provides stuttering steps. *)
  Inductive FlG := | asG (r: R).
  Let G := FlG. 

  Global Instance G_eqdec: EqDecision G.
  solve_decision.
  Qed.

  Global Instance G_cnt: Countable G.
  eapply inj_countable' with (f := fun '(asG ρ) => ρ) (g := asG).
  by intros []. 
  Qed.

  Global Instance G_inh: Inhabited G.
  pose proof (fmrole_inhabited M) as [ρ]. 
  apply (populate (asG ρ)).
  Qed. 

  Context `(LM: LiveModel G M LSI). 
  Context (LF: LMFairPre LM).
  Context {LSI_DEC: forall s tm f, Decision (LSI s tm f)}.

  Definition ls_map_restr (rm: @roles_map G M) := forall ρ g,
      rm !! ρ = Some g -> g = asG ρ. 

  Context {MAP_RESTR: forall (δ: lm_ls LM), ls_map_restr (ls_mapping δ)}.

  Context {UNUSED_NOT_DOM: forall ρ (δ: lm_ls LM), 
        is_unused ρ (ls_under δ) <-> asG ρ ∉ dom $ ls_tmap δ}. 

  Lemma not_unused_dom: forall ρ (δ: lm_ls LM), 
      ¬ is_unused ρ (ls_under δ) <-> asG ρ ∈ dom $ ls_tmap δ.
  Proof.
    intros. 
    specialize (UNUSED_NOT_DOM ρ δ). 
    apply not_iff_compat in UNUSED_NOT_DOM. rewrite UNUSED_NOT_DOM.
    tauto.
  Qed.

  Let LMF := LM_Fair (LF := LF).

  (* Let lift_prop1 (P: R -> fmstate M -> Prop):  *)
  (*   fmrole LMF -> lm_ls LM -> Prop :=  *)
  (*       fun g δ => let '(asG ρ) := g in *)
  (*                g ∈ dom $ ls_tmap δ /\ *)
  (*                P ρ (ls_under δ).  *)
  Let lift_prop1 (P1 P2: R -> fmstate M -> Prop): 
    fmrole LMF -> lm_ls LM -> Prop := 
        fun g δ => let '(asG ρ) := g in
                 let st := ls_under δ in
                 g ∈ dom $ ls_tmap δ /\
                 (P1 ρ st /\ (role_enabled_model ρ st \/ ¬ role_enabled_model g δ) \/
                  P2 ρ st /\ ¬ role_enabled_model ρ st /\ role_enabled_model g δ). 

  (*TODO: move *)
  Lemma gset_singleton_dec `{Countable K}:
    forall (g: gset K), {k | g = {[ k ]}} + (forall k, g ≠ {[ k ]}).
  Proof.
    intros. 
    destruct (decide (g = ∅)) as [-> | NE].
    { right. set_solver. }
    apply finitary.set_choose_L' in NE as [k IN].
    erewrite union_difference_singleton_L with (x := k) (Y := g); auto.
    destruct (decide (g ∖ {[k]} = ∅)) as [-> | NE']. 
    2: { apply finitary.set_choose_L' in NE' as [k' IN'].
         right. intros k''.
         intros EQ. apply (@f_equal _ _ size) in EQ.
         rewrite size_union in EQ; [| set_solver].
         rewrite !size_singleton in EQ.
         assert (size (g ∖ {[k]}) = 0) as S0 by lia.
         apply size_empty_inv in S0. set_solver. }
    rewrite union_empty_r_L. left. eauto.
  Qed. 

  Instance lift_prop1_dec P1 P2
    (DECP1: forall ρ st, Decision (P1 ρ st)) (DECP2: forall ρ st, Decision (P2 ρ st)):
    forall g δ, Decision (lift_prop1 P1 P2 g δ).
  Proof. 
    intros [g] δ. rewrite /lift_prop1.
    solve_decision. 
  Qed.

  (* TODO: move, find existing? *)
  Instance gtb_dec: forall x y, Decision (x > y).
  Proof. 
    intros. 
    destruct (lt_eq_lt_dec x y) as [[? | ->] | ?].
    3: by left.
    all: right; lia.
  Qed.

  (* Let active_st '(asG ρ) δ := *)
  (*       ls_tmap δ !! (asG ρ) = Some {[ ρ ]} /\ *)
  (*       lift_prop1 active_st (asG ρ) δ. *)

  (* Let disabled_st '(asG ρ) (δ: lm_ls LM) := *)
  (*       ls_tmap δ !! (asG ρ) = Some ∅ /\ *)
  (*       lift_prop1 disabled_st (asG ρ) δ. *)

  Instance FLP_LMF: FairLockPredicates LMF.
  refine {| 
      does_lock := lift_prop1 does_lock does_unlock;
      does_unlock := lift_prop1 does_unlock does_lock;
      (* fair_lock.active_st := active_st; *)
      (* fair_lock.disabled_st := disabled_st; *)
      is_unused := fun g δ => g ∉ dom $ ls_tmap δ;
    |}.
  (* - intros [?] ?. solve_decision. *)
  (* - intros [?] ?. rewrite /disabled_st. solve_decision. *)
  Defined.

  Definition lift_prop2 (P: fmrole M -> fmstate M -> fmstate M -> Prop):
    fmrole LMF -> lm_ls LM -> lm_ls LM -> Prop :=
        fun '(asG ρ) δ1 δ2 =>
            ls_tmap δ1 !! (asG ρ) = Some ∅ /\
            ls_tmap δ2 = <[ asG ρ := {[ ρ ]} ]> (ls_tmap δ1) /\
            ls_fuel δ2 = <[ ρ := lm_fl LM (ls_under δ2) ]> (ls_fuel δ1) /\
            P ρ (ls_under δ1) (ls_under δ2).

  Definition au_impl := lift_prop2 au_impl. 
  Definition al_impl := lift_prop2 al_impl. 

  Instance lift_prop2_dec P
    (DECP: forall ρ st1 st2, Decision (P ρ st1 st2)):
    forall g δ1 δ2, Decision (lift_prop2 P g δ1 δ2).
  Proof.
    intros [g] δ1 δ2. rewrite /lift_prop2.
    solve_decision.
  Qed.

  Instance allows_lock_ex_dec:
    forall δ g, Decision (∃ δ', al_impl g δ δ').
  Proof using LSI_DEC FLP FL.
    clear MAP_RESTR UNUSED_NOT_DOM.
    intros δ [ρ]. simpl.
    eapply Decision_iff_impl.
    { setoid_rewrite allows_lock_impl_spec. reflexivity. }
    destruct (decide (ls_tmap δ !! asG ρ = Some ∅ /\
                      does_lock ρ δ ∧ disabled_st ρ δ)).
    2: { right. set_solver. }
    destruct (let st' := (allow_lock_impl ρ δ) in build_ls_ext st' (<[asG ρ:={[ρ]}]> (ls_tmap δ)) (<[ρ:=lm_fl LM st']> (ls_fuel δ)) (H0 := LSI_DEC)).
    { left. destruct e as [δ2 (?&?&?)]. exists δ2.
      repeat split; try by apply a || eauto.
      congruence. }
    right. intros (?&?&?&?&?&?&?).
    destruct n. eexists. repeat split; eauto. congruence.
  Qed.

  Instance allows_unlock_ex_dec:
    forall δ g, Decision (∃ δ', au_impl g δ δ').
  Proof using LSI_DEC FLP FL.
    clear MAP_RESTR UNUSED_NOT_DOM.
    intros δ [ρ]. simpl.
    eapply Decision_iff_impl.
    { setoid_rewrite allows_unlock_impl_spec. reflexivity. }
    destruct (decide (ls_tmap δ !! asG ρ = Some ∅ /\
                      does_unlock ρ δ ∧ disabled_st ρ δ)).
    2: { right. set_solver. }
    destruct (let st' := (allow_unlock_impl ρ δ) in build_ls_ext st' (<[asG ρ:={[ρ]}]> (ls_tmap δ)) (<[ρ:=lm_fl LM st']> (ls_fuel δ)) (H0 := LSI_DEC)).
    { left. destruct e as [δ2 (?&?&?)]. exists δ2.
      repeat split; try by apply a || eauto.
      congruence. }
    right. intros (?&?&?&?&?&?&?).
    destruct n. eexists. repeat split; eauto. congruence.
  Qed.

  Let tl_active_exts (δ: fmstate LMF): gset fl_EI := 
      set_map (flU (M := LMF)) 
          (filter (fun g => exists δ', au_impl g δ δ') (dom (ls_tmap δ)))
      ∪
      set_map (flL (M := LMF)) 
          (filter (fun g => exists δ', al_impl g δ δ') (dom (ls_tmap δ))).
    

  (* TODO: move*)
  From trillium.fairness Require Import partial_ownership.
  Hypothesis LSI_LIFTS_STEP: forall (δ1: lm_ls LM) ρ st2,
      fmtrans _ (ls_under δ1) (Some ρ) st2 ->
      LSI st2 (ls_tmap δ1) (ls_fuel δ1). 
  Hypothesis M_STRONG_LR: FM_strong_lr M.
  Hypothesis STEP_NO_EN: forall st1 ρ st2,
      fmtrans M st1 (Some ρ) st2 ->
      live_roles _ st2 ⊆ live_roles _ st1. 
 Hypothesis DROP_PRES_LSI: forall st rem, fuel_drop_preserves_LSI st rem (LSI := LSI). 

  (* TODO: move? generalize? *)
  Lemma enabled_group_singleton ρ δ:
    role_enabled_model ((asG ρ): fmrole LMF) δ <->
    (* role_enabled_model ρ (ls_under δ) \/ *)
    (* default 0 (ls_fuel δ !! ρ) > 0. *)
    ρ ∈ dom (ls_mapping δ).
  Proof.
    split; intros EN.
    { red in EN. apply LM_live_roles_strong in EN as [? STEP].
      red in STEP. destruct STEP as (ℓ & STEP & MATCH).
      destruct ℓ; simpl in MATCH; subst; simpl in STEP.
      - destruct STEP as (STEP & MAP & _).
        apply MAP_RESTR in MAP. inversion MAP. subst.
        apply ls_mapping_dom. eapply fm_live_spec; eauto.
      - destruct STEP as ([ρ_ MAP] & DECR & NINCR & _).
        pose proof MAP as MAP'%MAP_RESTR. inversion MAP'. subst ρ_. clear MAP'.
        eapply elem_of_dom. eauto.
      - done. }
    apply elem_of_dom in EN as [g MAP].
    pose proof MAP as MAP'%MAP_RESTR. subst g.
    destruct (decide (ρ ∈ live_roles _ (ls_under δ))) as [EN | DIS].
    - red. apply M_STRONG_LR in EN as [st2 STEP].
      unshelve eapply fm_live_spec.
      { refine {| ls_under := st2; ls_tmap := ls_tmap δ; ls_fuel := ls_fuel δ; |}.
        2,3: by apply δ. 
        { etrans; [eapply STEP_NO_EN; eauto| ]. apply δ. }
        eapply LSI_LIFTS_STEP; eauto. }
      simpl. exists (Take_step ρ (asG ρ)). split; [| done]. simpl.
      (* repeat split; eauto. *)
      (* + red. simpl. intros ρ' DECR.   *)
      admit.
    - red. unshelve eapply fm_live_spec.
      { refine {| ls_under := ls_under δ; ls_fuel := delete ρ (ls_fuel δ); |}.
        { pose proof (ls_fuel_dom δ). set_solver. }
        3: { eapply DROP_PRES_LSI with (rem := {[ ρ ]}). apply δ. }
        { intros ?. apply mapped_roles_dom_fuels_gen.
          rewrite /mapped_roles.
          admit. }
        red. intros. admit. }
      simpl. exists (Silent_step (asG ρ)). split; [| done].
      simpl. repeat split; eauto.
      + red. simpl. intros ρ' DOM1 DOM2 DECR.
        simpl. 
  Admitted.

  Lemma disabled_group_singleton ρ δ:
    ¬ role_enabled_model ((asG ρ): fmrole LMF) δ <-> ρ ∉ dom (ls_mapping δ).
  Proof. 
    apply not_iff_compat. apply enabled_group_singleton.
  Qed. 

  Lemma disabled_group_disabled_role ρ δ:
    ¬ role_enabled_model ((asG ρ): fmrole LMF) δ -> ¬ role_enabled_model ρ (ls_under δ). 
  Proof.
    by intros ? ?%ls_mapping_dom%enabled_group_singleton.
  Qed.

  Instance FLE_LMF: @FairLockExt LMF FLP_LMF.
  refine {|
      fair_lock_simple.au_impl := au_impl;
      fair_lock_simple.al_impl := al_impl;
      fair_lock_simple.fl_active_exts := tl_active_exts;
    |}.
  { simpl. intros [ρ] * AU. red in AU. simpl in AU.
    destruct AU as (TM0 & TM' & FUEL' & AU).
    apply au_impl_spec in AU. 
    red. repeat split.
    - by apply elem_of_dom.
    - left. split.
      + apply AU.
      + right. apply LM_map_empty_notlive. by left.
    - apply LM_map_empty_notlive. by left.
    - rewrite TM'. set_solver.
    - left. split.
      + apply AU.
      + left. apply AU.
    - apply enabled_group_singleton.
      eapply mim_in_2 with (v := asG ρ); eauto. 
      { apply (ls_mapping_tmap_corr st2). }
      rewrite TM'. rewrite lookup_insert. set_solver. }
  (* TODO: refactor *)
  { simpl. intros [ρ] * AU. red in AU. simpl in AU.
    destruct AU as (TM0 & TM' & FUEL' & AU).
    apply al_impl_spec in AU. 
    red. repeat split.
    - by apply elem_of_dom.
    - left. split.
      + apply AU. 
      + right. apply LM_map_empty_notlive. by left.
    - apply LM_map_empty_notlive. by left.
    - rewrite TM'. set_solver.
    - left. split.
      + apply AU.
      + left. apply AU.
    - apply enabled_group_singleton.
      eapply mim_in_2 with (v := asG ρ); eauto. 
      { apply (ls_mapping_tmap_corr st2). }
      rewrite TM'. rewrite lookup_insert. set_solver. }
  
  intros. simpl.
  unfold tl_active_exts.
  rewrite elem_of_union.
  rewrite !elem_of_map. repeat setoid_rewrite elem_of_filter.
  erewrite exist_proper.
  2: { intros g. rewrite and_assoc.
       apply iff_and_impl_helper.
       intros [-> [? AU]]. do 2 red in AU.
       destruct g. apply elem_of_dom.
       by rewrite (proj1 AU). }
  rewrite or_comm. 
  erewrite exist_proper.
  2: { intros g. rewrite and_assoc.
       apply iff_and_impl_helper.
       intros [-> [? AU]]. do 2 red in AU.
       destruct g. apply elem_of_dom.
       by rewrite (proj1 AU). }
  destruct ι; try set_solver. 
  Defined.

  Lemma LM_EM_EXT_KEEPS: ext_keeps_asg
                              (ELM := (FL_EM FLE_LMF)).
  Proof.
    red. intros δ1 [ι] δ2 ρ g f STEP MAP FUEL.
    assert (g = asG ρ) as ->.
    { eapply MAP_RESTR; eauto. }
    inversion STEP; subst.
    destruct ι as [[ρ'] | [ρ']]; simpl in REL; destruct REL as (TM1 & TM2 & FM & ST).
    - assert (ρ ≠ ρ') as NEQ.
      { apply ls_mapping_tmap_corr in MAP as (Rg & TM & IN).
        intros ->. rewrite TM in TM1. set_solver. }
      split.
      2: { rewrite FM. rewrite lookup_insert_ne; eauto. }
      apply ls_mapping_tmap_corr. rewrite TM2 lookup_insert_ne; [| congruence].
      apply ls_mapping_tmap_corr. eauto.
    - assert (ρ ≠ ρ') as NEQ.
      { apply ls_mapping_tmap_corr in MAP as (Rg & TM & IN).
        intros ->. rewrite TM1 in TM. set_solver. }
      split.
      2: { rewrite FM. rewrite lookup_insert_ne; eauto. }
      apply ls_mapping_tmap_corr. rewrite TM2 lookup_insert_ne; [| congruence].
      apply ls_mapping_tmap_corr. eauto.
  Qed. 

  Let proj_ext (ι: @EI _ (FL_EM FLE_LMF)): @EI _ (FL_EM FLE) :=
        match ι with
        | flU (asG ρ) => flU ρ
        | flL (asG ρ) => flL ρ
        end. 
    
  Local Lemma PROJ_KEEP_EXT:
    forall δ1 ι δ2, (@ETs _ (FL_EM FLE_LMF)) ι δ1 δ2 -> 
                (@ETs _ (FL_EM FLE)) (proj_ext ι) (ls_under δ1) (ls_under δ2).
  Proof. 
    intros ? ι ? STEP. 
    destruct ι as [[ρ]| [ρ]]; simpl in *; set_solver. 
  Qed. 
  
  (* TODO: move, generalize *)
  Lemma upto_state_lookup_unfold2 i δ
    (lmtr: mtrace (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF)))
    (mtr: trace M (option ext_role))
    (UPTO: upto_stutter_eauxtr proj_ext lmtr mtr)
    (ITH : lmtr S!! i = Some δ):
    exists lmtr_i i' mtr_i',
              after i lmtr = Some lmtr_i /\
              after i' mtr = Some mtr_i' /\
              upto_stutter ls_under (EUsls proj_ext) lmtr_i mtr_i' /\
              mtr S!! i' = Some (ls_under δ).
  Proof. 
    pose proof ITH as (lmtr_i & AFTERi & TRi)%state_lookup_after'.
    pose proof AFTERi as X. eapply upto_stutter_after' in X as (i' & mtr_i' & AFTERi' & UPTOi); eauto.
    do 3 eexists. do 3 (try split; eauto).
    rewrite -TRi.
    erewrite state_lookup_after_0; eauto.
    f_equal. eapply upto_stutter_trfirst; eauto.
  Qed. 

  (* TODO: move, generalize *)
  Lemma upto_state_lookup_unfold1 i' st
    (lmtr: mtrace (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF)))
    (mtr: trace M (option ext_role))
    (UPTO: upto_stutter_eauxtr proj_ext lmtr mtr)
    (ITH : mtr S!! i' = Some st):
    exists mtr_i' i lmtr_i,
              after i lmtr = Some lmtr_i /\
              after i' mtr = Some mtr_i' /\
              upto_stutter ls_under (EUsls proj_ext) lmtr_i mtr_i' /\
              st = ls_under (trfirst lmtr_i) /\ 
              prefix_states_upto ls_under lmtr mtr i i'.
  Proof. 
    pose proof ITH as (mtr_i' & AFTERi' & TRi')%state_lookup_after'.
    pose proof AFTERi' as X. eapply upto_stutter_after_strong in X as (i & lmtr_i & AFTERi & UPTOi & PRE); eauto.
    do 3 eexists. do 4 (try split; eauto).
    rewrite -TRi'.
    eapply upto_stutter_trfirst; eauto.
  Qed. 
  
  Definition others_or_burn ρ' (fl_ctr: G -> @EI _ (FL_EM FLE_LMF)) :=
    (λ δ1 oℓ δ2,
       match oℓ with
       | Some (inl g) => next_TS_role δ1 g δ2 ≠ Some ρ'
       | Some (inr (env e)) => e ≠ fl_ctr (asG ρ')
       | None => True
       end).

  Instance oob_dec: forall ρ fl_ctr δ1 ℓ δ2, Decision (others_or_burn ρ fl_ctr δ1 ℓ δ2). 
  Proof. 
    rewrite /others_or_burn. destruct ℓ as [[|]|]; try solve_decision.
    intros. destruct e; solve_decision. 
  Qed. 

  Lemma others_or_burn_keep_lock ρ':
    label_kept_state_gen
    (λ st' : fmstate (@ext_model_FM _ (FL_EM FLE_LMF)),
       does_unlock ρ' (ls_under st') ∧ fair_lock_simple.disabled_st ρ' (ls_under st'))
    (others_or_burn ρ' (flU: @fmrole LMF -> @EI _ (FL_EM FLE_LMF))).
  Proof.
    red. intros. simpl in STEP. inversion STEP; subst.
    - simpl in STEP0. unfold_LMF_trans STEP0.
      + eapply step_keeps_unlock_dis. 
        { apply P1. }
        2: { simpl. left. simpl. apply STEP1. }                   
        red. simpl. congruence. 
      + repeat apply proj2 in STEP1. congruence.
    - simpl in PSTEP.      
      destruct ι; simpl in REL; red in REL.
      + destruct ρ as [ρ]. 
        eapply step_keeps_unlock_dis.
        { apply P1. }
        2: { simpl. right. Unshelve. 2: exact (flU ρ).
             apply REL. }
        red. simpl.
        congruence. 
      + destruct ρ as [ρ]. 
        eapply step_keeps_unlock_dis.
        { apply P1. }
        2: { simpl. right. Unshelve. 2: exact (flL ρ).
             apply REL. }
        red. simpl.
        congruence.
  Qed. 
 

  Lemma others_or_burn_keep_can_lock ρ':
    label_kept_state_gen
    (λ st' : fmstate (@ext_model_FM _ (FL_EM FLE_LMF)),
       does_lock ρ' (ls_under st') ∧ fair_lock_simple.disabled_st ρ' (ls_under st'))
    (others_or_burn ρ' (flL: @fmrole LMF -> @EI _ (FL_EM FLE_LMF))).
  Proof.
    red. intros. simpl in STEP. inversion STEP; subst.
    - simpl in STEP0. unfold_LMF_trans STEP0.
      + eapply step_keeps_lock_dis. 
        { apply P1. }
        2: { simpl. left. simpl. apply STEP1. }                   
        red. simpl. congruence. 
      + repeat apply proj2 in STEP1. congruence.
    - simpl in PSTEP.      
      destruct ι; simpl in REL; red in REL.
      + destruct ρ as [ρ]. 
        eapply step_keeps_lock_dis.
        { apply P1. }
        2: { simpl. right. Unshelve. 2: exact (flU ρ).
             apply REL. }
        red. simpl.
        congruence. 
      + destruct ρ as [ρ]. 
        eapply step_keeps_lock_dis.
        { apply P1. }
        2: { simpl. right. Unshelve. 2: exact (flL ρ).
             apply REL. }
        red. simpl.
        congruence.
  Qed. 

  (* TODO: move *)
  Lemma ex_det_iff2 {A B: Type} (P: A -> B -> Prop) a b
    (DET: forall a' b', P a' b' -> a' = a /\ b' = b):
    (exists a' b', P a' b') <-> P a b.
  Proof. 
    split; [| by eauto].
    intros (?&?&PP). pose proof PP. 
    by apply DET in PP as [-> ->].  
  Qed.

  (* TODO: move *)
  Lemma ex_det_iff3 {A B C: Type} (P: A -> B -> C -> Prop) a b c 
    (DET: forall a' b' c', P a' b' c' -> a' = a /\ b' = b /\ c' = c):
    (exists a' b' c', P a' b' c') <-> P a b c.
  Proof. 
    split; [| by eauto].
    intros (?&?&?&PP). pose proof PP. 
    by apply DET in PP as (-> & -> & ->).  
  Qed.

  Lemma unmapped_empty (ρ: fmrole M) (δ: lm_ls LM)
    (USED: ¬ fair_lock_simple.is_unused ρ (ls_under δ))
    (UNMAP: ρ ∉ dom (ls_mapping δ)):
    ls_tmap δ !! (asG ρ) = Some ∅.
  Proof.
    destruct (ls_tmap δ !! asG ρ) eqn:Rρ.
    2: { destruct USED. apply UNUSED_NOT_DOM.
         by apply not_elem_of_dom. } 
    simpl. destruct (decide (g = ∅)) as [-> | NE]; [done| ].
    apply set_choose_L in NE as [ρ' IN].
    assert (ρ' = ρ) as ->.
    { forward eapply (proj2 (ls_mapping_tmap_corr δ ρ' (asG ρ))).
      { eauto. }
      intros ?%MAP_RESTR. congruence. }
    edestruct UNMAP. apply elem_of_dom. exists (asG ρ).
    eapply ls_mapping_tmap_corr; eauto.
  Qed.

  Lemma disable_lmtr
    (lmtr: elmftrace (ELM := FL_EM FLE_LMF))
    (ρ' : fmrole M)
  (st' : fmstate M)
  (VALID: mtrace_valid lmtr)
  (HAS_LOCK : does_unlock ρ' st')
  (DIS : fair_lock_simple.disabled_st ρ' st')
  (FAIR: ∀ g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g lmtr)
  (i : nat)
  (lmtr_i : elmftrace (ELM := FL_EM FLE_LMF))
  (AFTERi : after i lmtr = Some lmtr_i)
  (ITH' : st' = ls_under (trfirst lmtr_i))
    :
(exists i' st', i <= i' /\
                        lmtr S!! i' = Some st' /\ does_unlock ρ' st' /\
                        (* ¬ role_enabled_model ρ' st' /\ *)
                        ρ' ∉ dom (ls_mapping st') /\
                        ∀ (k : nat) (st' : fmstate ext_model_FM),
                          0 <= k <= i' - i
                          → lmtr_i S!! k = Some st'
                          → (λ δ: lm_ls LM,
                                does_unlock ρ' (ls_under δ)
                                ∧ fair_lock_simple.disabled_st ρ' (ls_under δ)) st').
  Proof.
    assert (lmtr S!! i = Some (trfirst lmtr_i)) as ITH.
    { rewrite -(state_lookup_0 lmtr_i).
      erewrite (state_lookup_after lmtr lmtr_i); eauto. }
        
    destruct (decide (ls_mapping (trfirst lmtr_i) !! ρ' = Some (asG ρ'))).
    2: { exists i, (trfirst lmtr_i).
         do 2 (split; [eauto| ]). split.
         { simpl.
           (* split; [| *)
           by rewrite -ITH'.
         }
         split.
         { intros [? MAP]%elem_of_dom. apply n. rewrite MAP.
           apply MAP_RESTR in MAP. subst. done. }
         intros. assert (k = 0) as -> by lia.
         erewrite state_lookup_after in H0; eauto.
         rewrite Nat.add_0_r ITH in H0. inversion H0. subst.
         eauto using disabled_not_live. }
    
    assert (mtrace_valid lmtr_i) as VALIDi.
    { eapply trace_valid_after; eauto. }
    
    assert (∀ g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g lmtr_i) as FAIRi.
    { intros. eapply fair_by_after; eauto. apply FAIR. }
    
    apply group_fairness_implies_step_or_unassign with (ρ := ρ') in FAIRi; [| done].
    
    apply fair_by_gen_equiv in FAIRi.
    red in FAIR. specialize (FAIRi 0). specialize_full FAIRi.
    { erewrite state_lookup_after; eauto.
      rewrite Nat.add_0_r ITH. simpl.
      eapply elem_of_dom; eauto. }
    simpl in FAIRi. destruct FAIRi as [m_ FAIRi].
    pattern m_ in FAIRi. eapply min_prop_dec in FAIRi as [m [FAIRi MIN]].
    2: { intros. destruct (lmtr_i !! n) as [[s step] |] eqn:N; rewrite N.
         2: { right; set_solver. }
         eapply Decision_iff_impl.
         { erewrite ex_det_iff2.
           2: { intros ?? [[=] ?]. subst. split; reflexivity. }
           reflexivity. }
         solve_decision. }
    destruct FAIRi as (δ_m & step_m & MTH & FAIRi).
    red in FAIRi.
    
    Set Printing Coercions.
    subst st'.
    
    assert (
        ∀ (k : nat) (st' : fmstate ext_model_FM),
          0 <= k <= m
          → lmtr_i S!! k = Some st'
          → (λ δ : LiveState G M LSI,
                does_unlock ρ' (ls_under δ)
                ∧ fair_lock_simple.disabled_st ρ' (ls_under δ)) st') as KEEP.
    { eapply steps_keep_state_gen.
      { eauto. }
      { eexists. split; eauto. rewrite state_lookup_0. reflexivity. }
      { apply others_or_burn_keep_lock. }
      intros * [_ ?] KTH.
      destruct oℓ'; [| done]. simpl.
      pose proof KTH as STEP. eapply trace_valid_steps' in STEP; [| eauto].
      simpl in STEP.
      destruct f as [| [ι]].
      - intros EQ. specialize (MIN k). specialize_full MIN; [| lia].
        do 2 eexists. split; [done| ].
        red. right. simpl. red. simpl. do 3 eexists. repeat split; eauto.
      - intros ->. specialize (MIN k). specialize_full MIN; [| lia].
        assert (ls_tmap st1 !! (asG ρ') = Some ∅) as NOρ.
        { inversion STEP; subst; simpl in REL; apply REL. }
        do 2 eexists. split; [done| ].
        left. intros (?& MAP)%elem_of_dom.
        assert (x = asG ρ') as ->.
        { by apply MAP_RESTR in MAP. }
        eapply ls_mapping_tmap_corr in MAP as (?&?&?).
        rewrite NOρ in H0. set_solver. 
    }
    
    clear HAS_LOCK DIS.
    pose proof (KEEP m) as KEEPm. specialize_full KEEPm.
    { split; [lia| reflexivity]. }
    { eapply trace_state_lookup. apply MTH. }
    destruct KEEPm as [HAS_LOCK DIS].
    
    destruct FAIRi as [UNMAP| STEP].
    2: { simpl in STEP. red in STEP.
         destruct STEP as (?&?&?&->&<-&STEP).
         apply next_TS_spec_pos in STEP.
         edestruct disabled_not_live; eauto.
         eapply fm_live_spec. apply STEP. }
    
    exists (i + m). eexists. split; [lia| ].
    split; [| split]; [| | split| ..].
    { apply trace_state_lookup in MTH.
      erewrite state_lookup_after in MTH; [| eauto]. apply MTH. }
    { eauto. }
    { eauto. }
    intros ??.
    rewrite Nat.sub_add'. apply KEEP.
  Qed.

  Lemma has_lock_excl_lift: forall tl_st ρlg1 ρlg2,
      does_unlock ρlg1 tl_st -> disabled_st ρlg1 tl_st ->
      does_unlock ρlg2 tl_st -> disabled_st ρlg2 tl_st ->
      ρlg1 = ρlg2.
  Proof.
    intros δ [ρ1] [ρ2].
    simpl. intros [DOM1 UNLOCK1] DIS1 [DOM2 UNLOCK2] DIS2.
    f_equal.
    destruct UNLOCK1 as [UNLOCK1 | ?].
    2: { red in DIS1. tauto. }  
    destruct UNLOCK2 as [UNLOCK2 | ?].
    2: { red in DIS2. tauto. }
    destruct UNLOCK1 as [? [EN | DIS1']].
    { apply ls_mapping_dom, enabled_group_singleton in EN. done. } 
    destruct UNLOCK2 as [? [EN | DIS2']].
    { apply ls_mapping_dom, enabled_group_singleton in EN. done. }
    eapply has_lock_st_excl; eauto.
    all: red; by intros ?%ls_mapping_dom%enabled_group_singleton.
  Qed.     


  (* (* TODO: refactor *) *)
  (* Lemma can_lock_dis_kept: *)
  (*   ∀ ρ : fmrole LMF, *)
  (*   @label_kept_state (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF)) *)
  (*     (λ st : fmstate (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF)), *)
  (*        @does_lock LMF FLP_LMF ρ st ∧ @fair_lock_simple.disabled_st LMF FLP_LMF ρ st) *)
  (*     (* (@other_proj LMF FLE_LMF ρ) *) *)
  (*     (fun oℓ => oℓ ≠ Some (inr (env ((@flL _ ρ): @EI _ (@FL_EM _ _ FLE_LMF))))) *)
  (* . *)
  (* Proof. *)
    (* red. intros [ρ] δ oℓ δ' [LOCK DIS] OTHER STEP. *)
    (* simpl in STEP. *)
    (* destruct (decide (others_or_burn ρ (flL: @fmrole LMF -> @EI _ (FL_EM FLE_LMF)) δ oℓ δ')). *)
    (* { forward eapply (@others_or_burn_keep_can_lock ρ δ).  *)
    (* inversion STEP; subst. *)
    (* - rename ρ0 into g'. simpl in STEP0. unfold_LMF_trans STEP0. *)
    (*   2: { simpl in STEP1. pose proof STEP1 as SS. repeat apply proj2 in STEP1. *)
    (*         rewrite -STEP1. repeat split; try tauto. *)
    (*         apply unmapped_empty. *)
    (*         { intros ?. rewrite STEP1 in LOCK. *)
    (*           edestruct unused_can_lock_incompat; eauto. apply LOCK. } *)
    (*         intros IN.  *)
    (*         pose proof SS. *)
    (*         do 3 apply proj2 in SS. apply proj1 in SS. *)
    (*         repeat rewrite -ls_same_doms in SS. *)
    (*         set_solver. } *)
 
  (* TODO: refactor *)
  Lemma does_lock_dis_kept:
    ∀ ρ : fmrole LMF,
    @label_kept_state (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF))
      (λ st : fmstate (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF)),
         @does_lock LMF FLP_LMF ρ st ∧ @fair_lock_simple.disabled_st LMF FLP_LMF ρ st)
      (fun oℓ => oℓ ≠ Some (inr (env ((@flL _ ρ): @EI _ (@FL_EM _ _ FLE_LMF)))))
  .
  Proof.
    red. intros [ρ] δ oℓ δ' [LOCK DIS] OTHER STEP.
    simpl in STEP. 
    destruct LOCK as [DOM [LOCK | ]].
    2: { red in DIS. tauto. }
    pose proof DIS as DIS'%disabled_group_disabled_role. 
    destruct LOCK as [LOCK [? | ?]]; [done| ]. 
    assert (ρ ∉ dom (ls_mapping δ)) as ND. 
    { by eapply disabled_group_singleton. }

        
    inversion STEP; subst.
    -
      assert (does_lock ρ (ls_under δ') /\ fair_lock_simple.disabled_st ρ (ls_under δ') /\ ls_tmap δ' !! asG ρ = Some ∅) as (?&?&?).
      { simpl in STEP0, LOCK, DIS.
        simpl in OTHER.  destruct ρ0 as [ρ'].
        unfold_LMF_trans STEP0.
        2: { simpl in STEP1. pose proof STEP1 as SS. repeat apply proj2 in STEP1.
            rewrite -STEP1. repeat split; try tauto.
            apply unmapped_empty.
            { intros ?. rewrite STEP1 in LOCK.
              edestruct unused_does_lock_incompat; eauto. }
            intros IN. 
            pose proof SS.
            do 3 apply proj2 in SS. apply proj1 in SS.
            repeat rewrite -ls_same_doms in SS.
            set_solver. }
        forward eapply (step_keeps_lock_dis ρ (ls_under δ)).
        { split; [apply LOCK | apply DIS']. }
        2: { left. apply STEP1. }
        { congruence. }
        intros [??]. repeat split; eauto.
        simpl in STEP1.
        apply unmapped_empty.
        { intros ?. edestruct unused_does_lock_incompat; eauto. }
        intros IN.
        repeat apply proj2 in STEP1. specialize (STEP1 ρ). specialize_full STEP1.
        { apply elem_of_difference. repeat rewrite -ls_same_doms. split; [done| ].
          intros IN'. done. }
        apply elem_of_difference, proj1 in STEP1.
        by destruct DIS'. }
      
      simpl. repeat split; eauto.
      { by apply elem_of_dom. }
      { left. split; [done| ]. right. apply LM_map_empty_notlive. by left. }
      apply LM_map_empty_notlive. by left. 
    - forward eapply (step_keeps_lock_dis ρ δ) as KEPT. 
      { split; [apply LOCK| apply DIS']. }
      2: { right. eapply PROJ_KEEP_EXT; eauto. }
      { simpl. simpl in OTHER.
        destruct ι; simpl; simpl in OTHER; red; destruct ρ0; congruence. }
      intros. 
      destruct ι; simpl in REL; red in REL.
      + destruct ρ0 as [ρ']. assert (ρ' ≠ ρ).
        { intros ->. repeat apply proj2 in REL. apply au_impl_spec in REL.
          red in REL. eapply does_lock_unlock_incompat; eauto. apply REL. } 
        simpl in *.
        enough (ls_tmap δ' !! asG ρ = Some ∅).
        { repeat split; eauto; try by apply KEPT.
          { eapply elem_of_dom; eauto. }
          { left. split; [apply KEPT| ]. right. apply LM_map_empty_notlive. by left. }
          apply LM_map_empty_notlive. by left. }
        
        pose proof REL as REL_. 
        apply proj2, proj1 in REL.
        rewrite REL.
        rewrite lookup_insert_ne; [| congruence].
        apply unmapped_empty; try done.
        intros ?. eapply unused_does_lock_incompat; eauto. 
      + destruct ρ0 as [ρ']. assert (ρ' ≠ ρ) by set_solver. 
        simpl in *.
        enough (ls_tmap δ' !! asG ρ = Some ∅).
        { repeat split; eauto; try by apply KEPT.
          { eapply elem_of_dom; eauto. }
          { left. split; [apply KEPT| ]. right. apply LM_map_empty_notlive. by left. }
          apply LM_map_empty_notlive. by left. }
        apply proj2, proj1 in REL. rewrite REL.
        rewrite lookup_insert_ne; try congruence.
        apply unmapped_empty; try done.
        intros ?. eapply unused_does_lock_incompat; eauto. 
  Qed.

  (* TODO: refactor *)
  Lemma does_unlock_dis_kept:
    ∀ ρ : fmrole LMF,
    @label_kept_state (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF))
      (λ st : fmstate (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF)),
         @does_unlock LMF FLP_LMF ρ st ∧ @fair_lock_simple.disabled_st LMF FLP_LMF ρ st)
      (fun oℓ => oℓ ≠ Some (inr (env ((@flU _ ρ): @EI _ (@FL_EM _ _ FLE_LMF)))))
  .
  Proof.
    red. intros [ρ] δ oℓ δ' [LOCK DIS] OTHER STEP.
    simpl in STEP. 
    destruct LOCK as [DOM [LOCK | ]].
    2: { red in DIS. tauto. }
    pose proof DIS as DIS'%disabled_group_disabled_role. 
    destruct LOCK as [LOCK [? | ?]]; [done| ]. 
    assert (ρ ∉ dom (ls_mapping δ)) as ND. 
    { by eapply disabled_group_singleton. }
        
    inversion STEP; subst.
    -
      assert (does_unlock ρ (ls_under δ') /\ fair_lock_simple.disabled_st ρ (ls_under δ') /\ ls_tmap δ' !! asG ρ = Some ∅) as (?&?&?).
      { simpl in STEP0, LOCK, DIS.
        simpl in OTHER.  destruct ρ0 as [ρ'].
        unfold_LMF_trans STEP0.
        2: { simpl in STEP1. pose proof STEP1 as SS. repeat apply proj2 in STEP1.
            rewrite -STEP1. repeat split; try tauto.
            apply unmapped_empty.
            { intros ?. rewrite STEP1 in LOCK.
              edestruct unused_does_unlock_incompat; eauto. }
            intros IN. 
            pose proof SS.
            do 3 apply proj2 in SS. apply proj1 in SS.
            repeat rewrite -ls_same_doms in SS.
            set_solver. }
        forward eapply (step_keeps_unlock_dis ρ (ls_under δ)).
        { split; [apply LOCK | apply DIS']. }
        2: { left. apply STEP1. }
        { congruence. }
        intros [??]. repeat split; eauto.
        simpl in STEP1.
        apply unmapped_empty.
        { intros ?. edestruct unused_does_unlock_incompat; eauto. }
        intros IN.
        repeat apply proj2 in STEP1. specialize (STEP1 ρ). specialize_full STEP1.
        { apply elem_of_difference. repeat rewrite -ls_same_doms. split; [done| ].
          intros IN'. done. }
        apply elem_of_difference, proj1 in STEP1.
        by destruct DIS'. }
      
      simpl. repeat split; eauto.
      { by apply elem_of_dom. }
      { left. split; [done| ]. right. apply LM_map_empty_notlive. by left. }
      apply LM_map_empty_notlive. by left. 
    - forward eapply (step_keeps_unlock_dis ρ δ) as KEPT. 
      { split; [apply LOCK| apply DIS']. }
      2: { right. eapply PROJ_KEEP_EXT; eauto. }
      { simpl. simpl in OTHER.
        destruct ι; simpl; simpl in OTHER; red; destruct ρ0; congruence. }
      intros. 
      destruct ι; simpl in REL; red in REL; cycle 1. 
      + destruct ρ0 as [ρ']. assert (ρ' ≠ ρ).
        { intros ->. repeat apply proj2 in REL. apply al_impl_spec in REL.
          red in REL. eapply does_lock_unlock_incompat; eauto. apply REL. } 
        simpl in *.
        enough (ls_tmap δ' !! asG ρ = Some ∅).
        { repeat split; eauto; try by apply KEPT.
          { eapply elem_of_dom; eauto. }
          { left. split; [apply KEPT| ]. right. apply LM_map_empty_notlive. by left. }
          apply LM_map_empty_notlive. by left. }
        
        pose proof REL as REL_. 
        apply proj2, proj1 in REL.
        rewrite REL.
        rewrite lookup_insert_ne; [| congruence].
        apply unmapped_empty; try done.
        intros ?. eapply unused_does_unlock_incompat; eauto. 
      + destruct ρ0 as [ρ']. assert (ρ' ≠ ρ) by set_solver. 
        simpl in *.
        enough (ls_tmap δ' !! asG ρ = Some ∅).
        { repeat split; eauto; try by apply KEPT.
          { eapply elem_of_dom; eauto. }
          { left. split; [apply KEPT| ]. right. apply LM_map_empty_notlive. by left. }
          apply LM_map_empty_notlive. by left. }
        apply proj2, proj1 in REL. rewrite REL.
        rewrite lookup_insert_ne; try congruence.
        apply unmapped_empty; try done.
        intros ?. eapply unused_does_unlock_incompat; eauto. 
  Qed.

    
  Lemma ev_rel_inner (lmtr: elmftrace (ELM := FL_EM FLE_LMF))
    (mtr: trace M (option ext_role))
    (ρ : R)
    (UPTO : upto_stutter ls_under (EUsls proj_ext) lmtr mtr)
    (VALID: mtrace_valid lmtr)
    (FAIR: ∀ g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g lmtr)
    (EV_REL : eventual_release lmtr (asG ρ) 0):
  eventual_release mtr ρ 0.
  Proof.
    (* red in EV_REL.  *)
    red. intros.
    forward eapply upto_state_lookup_unfold1 as (mtr_i' & i & lmtr_i & AFTERi & AFTERi' & UPTOi & ITH' & PREi); eauto.
    
    assert (lmtr S!! i = Some (trfirst lmtr_i)) as ITH.
    { rewrite -(state_lookup_0 lmtr_i).
      erewrite (state_lookup_after lmtr lmtr_i); eauto. }
        
    forward eapply disable_lmtr as D; eauto.
    clear HAS_LOCK DIS.
    destruct D as (m & δ_m & LEi & MTH & HAS_LOCK & UNMAP & BETWEEN). 

    assert (ls_tmap δ_m !! asG ρ' = Some ∅) as DOMρ'.
    { apply unmapped_empty; auto. intros UN. 
      edestruct unused_does_unlock_incompat; eauto. } 

    forward eapply LM_map_empty_notlive as DISg'; [by left| ].
    (* eapply eventual_release_strenghten in EV_REL. *)
    forward eapply eventual_release_strenghten2 with (ρ' := asG ρ': fmrole LMF).
    { apply does_unlock_dis_kept. }
    { apply has_lock_excl_lift. }    
    (* pose proof (@eventual_release_strenghten2 _ _ _ _ _ _ EV_REL) as ER. clear EV_REL.  *)
    (* specialize (ER (asG ρ')). specialize_full ER. *)
    { apply EV_REL. }
    { apply MTH. }
    { simpl. split; [eapply elem_of_dom; eauto| tauto]. } 
    { done. 
      (* split; eauto.  *)
      (* red. split; [by eapply elem_of_dom| ].  *)
      (* eapply (BETWEEN (m - i)). *)
      (* { lia. } *)
      (* erewrite state_lookup_after; eauto. *)
      (* rewrite -Nat.le_add_sub; eauto. }  *)
    }
    { intros _. specialize (AFTER ltac:(lia)). destruct AFTER as [NEQ AFTER].
      split; [congruence| ]. 
      intros.
      assert (k <= i \/ i <= k <= i + m) as [BEFORE | CUR] by lia. 
      2: {
           intros [LOCK2 DIS2].
           specialize (BETWEEN (k - i)). specialize_full BETWEEN.
           { lia. }
           { erewrite state_lookup_after; eauto.
             rewrite -Nat.le_add_sub; eauto. lia. }

           simpl in LOCK2. destruct LOCK2 as [DOM [LOCK2 | ?]]. 
           2: { red in DIS2. tauto. }
           destruct LOCK2 as [? [EN | ?]]. 
           { by apply ls_mapping_dom, enabled_group_singleton in EN. }
           eapply NEQ. eapply (has_lock_st_excl st_k (FairLock := FL)); eauto.
           all: try tauto.
           by apply disabled_group_disabled_role. }
      
      move PREi at bottom. red in PREi.
      setoid_rewrite pred_at_trace_lookup in PREi. specialize_full PREi.
      { apply BEFORE. }
      { eexists. eauto. }
      destruct PREi as (p & (st&PTH&->) & LT').
      apply AFTER in PTH; [| lia].
      intros [LOCK DIS]. apply PTH.
      split.
      2: { eapply disabled_group_disabled_role; eauto. }
      simpl in LOCK. destruct LOCK as [? [? | ?]].
      2: { red in DIS. tauto. }
      tauto. }
    { done. }

    intros ER. 
    destruct ER as (p & δ_p & ? & ? & PTH).
        
    (* pose proof PTH as PTH_.  *)
    
    assert (i <= p) as [d ->]%Nat.le_sum by lia.
    erewrite <- @trace_lookup_after in PTH; eauto.

    eapply upto_stutter_trace_label_lookup in PTH; eauto.
    simpl in PTH. destruct PTH as [c CTH].
    apply trace_label_lookup_simpl' in CTH as (?&?&CTH).
    erewrite trace_lookup_after in CTH; eauto.
    exists (j + c + 1). eexists. repeat split.
    { apply state_label_lookup in CTH as (?&?&?). eauto. }
    { lia. }
    eapply trace_valid_steps' in CTH; eauto.
    2: { eapply destutter_ext.upto_preserves_validity; eauto.
         apply PROJ_KEEP_EXT. }
    inversion CTH; subst. simpl in REL.
    apply au_impl_spec in REL. apply REL. 
  Qed. 

  Instance oob_lookup_dec: ∀ x (lmtr: elmftrace (ELM := FL_EM FLE_LMF)) ρ flc,
    Decision
      (∃ (δ1 : LiveState G M LSI) (ℓ : option (G + env_role)) 
         (δ2 : LiveState G M LSI),
         lmtr !! x = Some (δ1, Some (ℓ, δ2)) ∧ ¬ others_or_burn ρ flc δ1 ℓ δ2).
  Proof. 
    intros k lmtr ρ flc. destruct (lmtr !! k) as [[? [[ℓ ?]|]] | ] eqn:K.
    2, 3: right; set_solver.
    eapply Decision_iff_impl.
    { erewrite ex_det_iff3.
      2: { intros ??? [[=] ?]. subst. repeat split; reflexivity. }
      reflexivity. }
    solve_decision. 
  Qed. 

  Lemma final_steps ρ i (P P': R → fmstate M → Prop) flc
    (lmtr: mtrace (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF)))
    (δ : LiveState G M LSI)
    (DISM : fair_lock_simple.disabled_st ρ (ls_under δ))
    (* (LOCK : has_lock_st ρ (ls_under δ)) *)
    (Pi: P ρ (ls_under δ))
    (DTH : lmtr S!! i = Some δ)
    (USED: forall ρ st, P ρ st -> ¬ is_unused ρ st)
    (KEPT: forall ρ, label_kept_state_gen
             (λ st : fmstate (@ext_model_FM _ (FL_EM FLE_LMF)),
                 P ρ (ls_under st) ∧ fair_lock_simple.disabled_st ρ (ls_under st)) (others_or_burn ρ flc))
    (FAIR: ∀ g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g lmtr)
    (VALID: mtrace_valid lmtr)
    (FLC_PROJ: forall (g: fmrole LMF), proj_role (inr $ env $ flc g) = g)
    :
    ∃ (n : nat) (st' : fmstate ext_model_FM),
      i <= n
      ∧ lmtr S!! n = Some st'
      ∧ lift_prop1 P P' (asG ρ) st' ∧ fair_lock_simple.disabled_st (asG ρ) st'.
  Proof.
    destruct (decide (ρ ∈ dom (ls_mapping δ))) as [MAP | UNMAP]. 
    2: { eapply unmapped_empty in UNMAP.
         2: { eauto. }
         exists i, δ. split; [lia| ].
         repeat split; try done. 
         { eapply elem_of_dom; eauto. }
         { left. split; auto. right. apply LM_map_empty_notlive. by left. }
         apply LM_map_empty_notlive. by left. }

    apply group_fairness_implies_step_or_unassign with (ρ := ρ) in FAIR; [| done].
    apply fair_by_gen_equiv, fair_by_gen'_strong_equiv in FAIR. 
    2, 3: solve_decision. 
    red in FAIR.
    specialize (FAIR i). specialize_full FAIR.
    { by rewrite DTH. }
    
    destruct FAIR as (p & δ' & step' & PTH & STEPp & MINp).
    rewrite /fairness_sat_gen in MINp. 

    edestruct (list_exist_dec (fun m => exists δ1 ℓ δ2, lmtr !! m = Some (δ1, Some (ℓ, δ2)) /\ ¬ others_or_burn ρ flc δ1 ℓ δ2) (seq i p)) as [EXT | NOEXT].
    { solve_decision. }
    - destruct EXT as [k_ EXT].
      pattern k_ in EXT. eapply min_prop_dec in EXT as [k [EXT MINk]]; [clear k_|].
      2: { solve_decision. }
      destruct EXT as [DOMk (?&ℓ&?&KTH&STEP)].
      apply elem_of_seq in DOMk. 

      forward eapply steps_keep_state_gen.
      3: { apply KEPT. }
      2: { eexists. split; [apply DTH| ]. eauto. }
      { auto. }
      3: { eapply trace_state_lookup. apply KTH. }
      2: { split; [| reflexivity]. lia. }
      { intros. destruct (decide (others_or_burn ρ flc st1 oℓ' st2)); [done| ].
        specialize (MINk k0). specialize_full MINk; [| lia].
        split; eauto.
        apply elem_of_seq. lia. }
      intros [LOCKk DISk].

      assert (ls_tmap x !! asG ρ = Some ∅).
      { 

        rewrite /others_or_burn in STEP. destruct ℓ as [r| ].
        2: { simpl in STEP. tauto. }
        destruct r.
        { apply NNP_P in STEP.
          edestruct disabled_not_live; eauto. 
          apply next_TS_spec_pos in STEP. eapply fm_live_spec.
          apply STEP. }
        destruct e. 
        simpl in STEP. apply NNP_P in STEP. 
        eapply trace_valid_steps' in KTH; eauto. inversion KTH.
        revert STEP. subst. intros STEP.
        pose proof (FLC_PROJ (asG ρ)). simpl in H. rewrite -STEP in H. 
        destruct i0; subst; simpl in REL.
        - apply REL.
        - apply REL. }

      exists k. eexists. repeat split. 
      { lia. }        
      { eapply trace_state_lookup; eauto. }
      { apply not_unused_dom. eauto. }
      all: auto.
      { left. split; auto. right. apply LM_map_empty_notlive. by left. }
      apply LM_map_empty_notlive. by left.       
    - forward eapply steps_keep_state_gen.
      3: { apply KEPT. }
      2: { eexists. split; [eapply DTH| ]. eauto. }
      { eauto. }
      3: { eapply trace_state_lookup. apply PTH. }
      2: { split; [lia| ]. reflexivity. }
      { intros. destruct (decide (others_or_burn ρ flc st1 oℓ' st2)); [done| ].
        edestruct NOEXT. exists k. split; eauto. 
        apply elem_of_seq. lia. }
      intros [LOCKp DISp].

      red in STEPp. destruct STEPp as [UNMAP | STEP]. 
      +
        assert (¬ role_enabled_model ((asG ρ): fmrole LMF) δ').
        { apply LM_map_empty_notlive. left.
          eapply unmapped_empty; eauto. }
        do 2 eexists. repeat split.
        2: { eapply trace_state_lookup, PTH. }
        { lia. }
        all: eauto.
        1: apply not_unused_dom; by eauto.
      + red in STEP. destruct STEP as (?&?&?&[=]&<-&STEP); subst.
        apply next_TS_spec_pos in STEP.
        eapply disabled_not_live in DISp. destruct DISp.
        eapply fm_live_spec. apply STEP.
  Qed. 
 
    
  Lemma FL_LM_progress:
    @fl_lock_progress _ FLP_LMF (FL_EM FLE_LMF) (fun tr => forall g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g tr). 
  Proof.
    red. intros lmtr [ρ] i δ **.
   
    simpl in CAN_LOCK. destruct CAN_LOCK as [DOM [L | U]].
    2: { pose proof (group_fairness_implies_step_or_unassign _ _ VALID FAIR) as FAIR'.
         specialize (FAIR' ρ). red in FAIR'.
         apply fair_by_gen_equiv, fair_by_gen'_strong_equiv in FAIR'.
         2, 3: solve_decision. 
         specialize (FAIR' i). specialize_full FAIR'.
         { rewrite ITH. simpl.
           do 2 red in ACT. apply LM_live_roles_strong in ACT as [? STEP]. 
           apply locale_trans_ex_role in STEP as [ρ_ IN].
           pose proof IN as EQ%MAP_RESTR.
           eapply elem_of_dom. set_solver. }

         forward eapply final_steps with (P := does_unlock) (P' := does_lock).
         { apply U. }
         { apply U. }
         { apply ITH. }
         { intros. intros ?. eapply unused_does_unlock_incompat; eauto. }
         { apply others_or_burn_keep_lock. }
         { done. }
         { done. }
         { done. }
         intros (n&?&?&?&?&?). exists n. eexists. split; [| eauto].
         apply Nat.le_lteq in H as [? | ->]; [done| ].
         congruence. }

    destruct L as [L [EN | DIS]].
    2: { by red in ACT. } 

    pose proof (group_fairness_implies_role_fairness _ _ VALID FAIR) as FAIR'.
    pose proof (can_destutter_eauxtr proj_ext _ VALID) as [mtr UPTO].
    forward eapply destutter_ext.upto_preserves_validity as VALIDm; eauto. 
    { apply PROJ_KEEP_EXT. }
    forward eapply destutter_ext.upto_stutter_fairness as FAIRm; eauto.
    { eapply ELM_ALM_afair_by_next; eauto. }
    pose proof (@lock_progress _ _ _ _ FL) as PROGRESSm.    
    red in PROGRESSm.

    forward eapply upto_state_lookup_unfold2 as (lmtr_i & i' & mtr_i' & AFTERi & AFTERi' & UPTOi & ITH'); eauto. 
      
    specialize (PROGRESSm mtr_i' ρ 0 (ls_under δ)).
    specialize_full PROGRESSm; eauto.
    { eapply trace_valid_after; eauto. }
    { do 2 red. intros. eapply fair_by_after; eauto. by apply FAIRm. }
    { erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r. }
    { eapply ev_rel_after in EV_REL; eauto.
      eapply ev_rel_inner; eauto.
      - eapply trace_valid_after; eauto. 
      - intros. eapply fair_by_after; eauto. apply FAIR. }

    destruct PROGRESSm as (d' & st & NZ & DTH' & LOCK & DISM).
    eapply upto_stutter_state_lookup in DTH' as (d & δ' & DTH & CORRd); [| by apply UPTOi].
    subst st.
    erewrite state_lookup_after in DTH; eauto.

    assert (d > 0) as NZd.
    { destruct d; [| lia].
      rewrite Nat.add_0_r ITH in DTH. inversion DTH. subst δ'.
      edestruct does_lock_unlock_incompat; eauto. } 
    
    forward eapply final_steps with (P' := does_lock); eauto.
    { intros ** ?. eapply unused_does_unlock_incompat; eauto. }
    { apply others_or_burn_keep_lock. }
    { done. }
    intros (n&?&?&?&?&?). exists n. eexists. split; [| eauto].
    lia. 
  Qed.

  Lemma FL_LM_unlock:
    @fl_unlock_termination _ FLP_LMF (FL_EM FLE_LMF) (fun tr => forall g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g tr). 
  Proof.
    red. intros lmtr [ρ] i δ **.
    rename CAN_LOCK into LOCK. 

    simpl in LOCK. destruct LOCK as [DOM [L | U]].
    2: { pose proof (group_fairness_implies_step_or_unassign _ _ VALID FAIR) as FAIR'.
         specialize (FAIR' ρ). red in FAIR'.
         apply fair_by_gen_equiv, fair_by_gen'_strong_equiv in FAIR'.
         2, 3: solve_decision. 
         specialize (FAIR' i). specialize_full FAIR'.
         { rewrite ITH. simpl.
           do 2 red in ACT. apply LM_live_roles_strong in ACT as [? STEP]. 
           apply locale_trans_ex_role in STEP as [ρ_ IN].
           pose proof IN as EQ%MAP_RESTR.
           eapply elem_of_dom. set_solver. }

         forward eapply final_steps with (P := does_lock) (P' := does_unlock).
         { apply U. }
         { apply U. }
         { apply ITH. }
         { intros. intros ?. eapply unused_does_lock_incompat; eauto. }
         { apply others_or_burn_keep_can_lock. }
         { done. }
         { done. }
         { done. }
         intros (n&?&?&?&?&?). exists n. eexists. split; [| eauto].
         apply Nat.le_lteq in H as [? | ->]; [done| ].
         congruence. }

    destruct L as [L [EN | DIS]].
    2: { by red in ACT. } 

    pose proof (group_fairness_implies_role_fairness _ _ VALID FAIR) as FAIR'.
    pose proof (can_destutter_eauxtr proj_ext _ VALID) as [mtr UPTO].
    forward eapply destutter_ext.upto_preserves_validity as VALIDm; eauto. 
    { apply PROJ_KEEP_EXT. }
    forward eapply destutter_ext.upto_stutter_fairness as FAIRm; eauto.
    { eapply ELM_ALM_afair_by_next; eauto. }
    pose proof (@unlock_termination _ _ _ _ FL) as PROGRESSm.
    red in PROGRESSm.

    forward eapply upto_state_lookup_unfold2 as (lmtr_i & i' & mtr_i' & AFTERi & AFTERi' & UPTOi & ITH'); eauto. 
      
    specialize (PROGRESSm mtr_i' ρ 0 (ls_under δ)).
    specialize_full PROGRESSm; eauto.
    { eapply trace_valid_after; eauto. }
    { do 2 red. intros. eapply fair_by_after; eauto. by apply FAIRm. }
    { erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r. }
    
    destruct PROGRESSm as (d' & st & NZ & DTH' & UNLOCK & DISM).
    eapply upto_stutter_state_lookup in DTH' as (d & δ' & DTH & CORRd); [| by apply UPTOi].
    subst st.
    erewrite state_lookup_after in DTH; eauto.

    assert (d > 0) as NZd.
    { destruct d; [| lia].
      rewrite Nat.add_0_r ITH in DTH. inversion DTH. subst δ'.
      edestruct does_lock_unlock_incompat; eauto. }
    clear dependent δ. rename δ' into δ. 

    forward eapply final_steps with (P' := does_unlock); eauto.
    { intros ** ?. eapply unused_does_lock_incompat; eauto. }
    { apply others_or_burn_keep_can_lock. }
    { done. }
    intros (n&?&?&?&?&?). exists n. eexists. split; [| eauto]. lia. 
  Qed.

  (* Lemma FL_LM_term: *)
  (*   @fl_trace_termination _ FLP_LMF (FL_EM FLE_LMF) (fun tr => forall g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g tr).  *)
  (* Proof. *)
  (*   red. intros lmtr **.  *)
  (*   pose proof (group_fairness_implies_role_fairness _ _ VALID FAIR) as FAIR'. *)
  (*   pose proof (can_destutter_eauxtr proj_ext _ VALID) as [mtr UPTO]. *)
  (*   forward eapply destutter_ext.upto_preserves_validity as VALIDm; eauto.  *)
  (*   { apply PROJ_KEEP_EXT. } *)
  (*   forward eapply destutter_ext.upto_stutter_fairness as FAIRm; eauto. *)
  (*   { eapply ELM_ALM_afair_by_next; eauto. } *)

  (*   eapply destutter_ext.upto_stutter_finiteness; eauto. *)
  (*   apply trace_termination; eauto. *)
  (*   { eapply ext_bounded_inner; eauto. } *)
  (*   intros. *)

  (*   red. intros. *)

  (*   forward eapply upto_state_lookup_unfold1 as (mtr_i' & i' & lmtr_i & AFTERi & AFTERi' & UPTOi & ITH' & ?); eauto.  *)

  (*   forward eapply disable_lmtr as D; eauto. *)
  (*   destruct D as (m & δ_m & LEi & MTH & HAS_LOCK' & UNMAP & BETWEEN). *)

  (*   assert (ls_tmap δ_m !! asG ρ' = Some ∅) as DOMρ'. *)
  (*   { apply unmapped_empty; auto. intros UN.  *)
  (*     edestruct unused_has_lock_incompat; eauto. }  *)

  (*   move EV_REL at bottom. *)
  (*   specialize (EV_REL (asG ρ) (S m)). red in EV_REL. specialize_full EV_REL; eauto. *)
  (*   { Unshelve. 2: exact (asG ρ'). simpl. split; auto. *)
  (*     eapply elem_of_dom; eauto. } *)
  (*   { split; eauto.  *)
  (*     red. split; [by eapply elem_of_dom| ].  *)
  (*     eapply (BETWEEN (m - i')). *)
  (*     { lia. } *)
  (*     erewrite state_lookup_after; eauto. *)
  (*     rewrite -Nat.le_add_sub; eauto. }  *)
  (*   { lia. } *)

  (*   destruct EV_REL as (p & δ_p & PTH & LEm & ENp). *)
  (*   assert (i' <= p) as [d ->]%Nat.le_sum by lia.  *)
  (*   erewrite <-state_lookup_after in PTH; eauto. *)
  (*   eapply upto_stutter_state_lookup' in PTH as [c CTH]; eauto. *)
  (*   exists (j + c). eexists. repeat split. *)
  (*   { erewrite <- state_lookup_after; eauto. } *)
  (*   { lia. } *)
  (*   apply ENp. *)
  (* Qed. *)


  (* TODO: is it possible to avoid delegating this to user? *)
  Context {allow_unlock_impl: G -> lm_ls LM -> lm_ls LM}.
  Hypothesis (allows_unlock_impl_spec: forall g δ δ', au_impl g δ δ' <->
             (allow_unlock_impl g δ = δ' /\ (does_unlock g δ /\ disabled_st g δ))).
  Hypothesis (allow_unlock_post: forall g δ, 
                 does_unlock g δ /\ disabled_st g δ ->
                 let δ' := allow_unlock_impl g δ in
                 does_unlock g δ' /\ active_st g δ'). 

  Context {allow_lock_impl: G -> lm_ls LM -> lm_ls LM}.
  Hypothesis (allows_lock_impl_spec: forall g δ δ', al_impl g δ δ' <->
             (allow_lock_impl g δ = δ' /\ (does_lock g δ /\ disabled_st g δ))).

    
  Lemma unused_kept_LM:
  ∀ ρ : fmrole LMF,
    @label_kept_state (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF))
      (λ st : fmstate (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF)),
         @is_unused LMF FLP_LMF ρ st)
      (λ _ : option (fmrole (@ext_model_FM LMF (@FL_EM LMF _ FLE_LMF))), True).
  Proof.
    intros [ρ] δ oℓ δ' UNUSED _ STEP.
    inversion STEP; subst.
    - simpl in STEP0.
      unfold_LMF_trans STEP0.
      2: { simpl in STEP1. repeat apply proj2 in STEP1.
           apply UNUSED_NOT_DOM in UNUSED.
           rewrite STEP1 in UNUSED. by apply UNUSED_NOT_DOM. }
      simpl. apply UNUSED_NOT_DOM.  
      eapply step_keeps_unused; [| done| ].
      2: { left. apply STEP1. }
      by apply UNUSED_NOT_DOM. 
    - simpl. apply UNUSED_NOT_DOM.  
      eapply step_keeps_unused; [| done| ].
      2: { right. eapply PROJ_KEEP_EXT; eauto. }
      by apply UNUSED_NOT_DOM.
  Qed. 

  Instance FL_LM: FairLock LMF FLP_LMF FLE_LMF (fun tr => forall g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g tr).
  refine {| 
      fair_lock_simple.allow_unlock_impl := allow_unlock_impl;
      fair_lock_simple.allow_lock_impl := allow_lock_impl;
    |}. 
  (* 16: { apply FL_LM_term. } *)
  15: { apply FL_LM_unlock. }
  14: { apply FL_LM_progress. }
  - simpl. apply allows_unlock_impl_spec. 
  - simpl. apply allows_lock_impl_spec.
  - apply does_unlock_dis_kept. 
  - apply does_lock_dis_kept.
  - admit. 
  - apply unused_kept_LM.
  - intros ? []. simpl. tauto.
  - intros ? []. simpl. tauto.
  - intros ? []. simpl. intros ? (?&?&?)%LM_live_role_map_notempty.
    destruct H. by apply elem_of_dom. 
  - intros ? []. simpl. intros ? (?&?&?)%LM_live_role_map_notempty.
    destruct H. by apply elem_of_dom. 
  - done. 
  - apply has_lock_excl_lift. 
  - intros ? []. simpl.
    intros [? R1] [? R2].
    destruct R1, R2.
    2, 3: tauto. 
    { eapply does_lock_unlock_incompat; [apply H1| apply H2]. }
    { eapply does_lock_unlock_incompat; [apply H2| apply H1]. }
  Qed. 

End FairLockLM.
