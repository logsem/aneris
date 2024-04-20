From iris.proofmode Require Import tactics.
From stdpp Require Import base.
From trillium.fairness Require Import fuel lm_fair.
From trillium.fairness.lm_rules Require Import resources_updates.

(* TODO: move *)
Section RestrLM.
  Context {M: FairModel}. 
  Let R := fmrole M.

  Inductive SG := | asG (r: R).
  Let G := SG. 

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
  Let LMF := LM_Fair (LF := LF).

  (* Context {LSI_DEC: forall s tm f, Decision (LSI s tm f)}. *)

  Definition ls_map_restr (rm: @roles_map G M) := forall ρ g,
      rm !! ρ = Some g -> g = asG ρ. 

  Definition enabled_group_singleton ρ δ :=
    role_enabled_model ((asG ρ): fmrole LMF) δ <->
    ρ ∈ dom (ls_mapping δ).

  
  Lemma egs_helper
    (MAP_RESTR: forall (δ: lm_ls LM), ls_map_restr (ls_mapping δ))
    (LSI_LIFTS_STEP: forall (δ1: lm_ls LM) ρ st2,
      fmtrans _ (ls_under δ1) (Some ρ) st2 ->
      LSI st2 (ls_tmap δ1) (ls_fuel δ1))
    (LSI_FUEL_INDEP: LSI_fuel_independent (LSI := LSI))
    (M_STRONG_LR: FM_strong_lr M)
    (DROP_PRES_LSI: forall st rem, fuel_drop_preserves_LSI st rem (LSI := LSI))
    (STEP_NO_EN: forall st1 ρ st2,
      fmtrans M st1 (Some ρ) st2 ->
      live_roles _ st2 ⊆ live_roles _ st1)
    :
    forall ρ δ, enabled_group_singleton ρ δ.
  Proof using.
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
      pose proof MAP as [f F]%mk_is_Some%ls_same_doms'. 
      assert (exists δ': lm_ls LM, ls_under δ' = st2 /\ ls_tmap δ' = ls_tmap δ /\ ls_fuel δ' = <[ ρ := min (lm_fl LM st2) f ]> (ls_fuel δ)) as [δ' (ST' & TM' & F')]. 
      {
        unshelve eexists {| ls_under := st2 |}.
        7: repeat split; reflexivity. 
        3: by apply δ. 
        { etrans; [eapply STEP_NO_EN; eauto| ].
          rewrite dom_insert_L. pose proof (ls_fuel_dom δ). set_solver. }
        2: { apply LSI_FUEL_INDEP with (F := ls_fuel δ). 
             eapply LSI_LIFTS_STEP; eauto. }
        intros. rewrite -(ls_tmap_fuel_same_doms δ).
        apply mk_is_Some, ls_same_doms', elem_of_dom in MAP. 
        rewrite dom_insert_L. set_solver. } 
      (* rewrite ST' in *.  *)
      (* subst.  *)
      apply fm_live_spec with (s' := δ'). simpl.
      exists (Take_step ρ (asG ρ)). split; [| done]. simpl.
      Set Printing Coercions.
      repeat split; eauto; try congruence. 
      + red. rewrite !F'. intros ρ' DOM DOM' DEC.
        inversion DEC; subst.
        * symmetry in Hsametid. apply MAP_RESTR in Hsametid. congruence.
        * destruct Hneqtid. f_equal.
          rewrite /ls_mapping. congruence.
      + red. rewrite !F'. intros.
        apply elem_of_dom in H as [? F2]. 
        destruct (decide (ρ' = ρ)) as [-> | NEQ].
        2: { left. rewrite lookup_insert_ne; [| done].
             rewrite F2. simpl. lia. }
        left. rewrite lookup_insert F. simpl. lia. 
      + rewrite !F' ST'. simpl. intros.
        rewrite lookup_insert. simpl. lia. 
      + intros ?. rewrite F' dom_insert_L.
        apply mk_is_Some, elem_of_dom in F. set_solver. 
      + rewrite F' dom_insert_L.
        apply mk_is_Some, elem_of_dom in F. set_solver. 
    - red.
      assert (exists δ': lm_ls LM, ls_under δ' = ls_under δ /\ ls_tmap δ' = (fun rs => rs ∖ {[ ρ ]}) <$> ls_tmap δ /\ ls_fuel δ' = delete ρ (ls_fuel δ)) as [δ' (ST' & TM' & F')]. 
      { unshelve eexists (MkLiveState _ _ _ _ _ _ _).
        8: repeat split; simpl; reflexivity.
        - pose proof (ls_fuel_dom δ). set_solver. 
        - intros. apply mapped_roles_dom_fuels_gen. 
          rewrite groups_map_difference. 
          rewrite dom_delete_L. f_equal.
          apply mapped_roles_dom_fuels_gen. apply δ. 
        - red. intros * NEQ (?&<-&TM1)%lookup_fmap_Some (?&<-&TM2)%lookup_fmap_Some.
          eapply disjoint_subseteq.
          { apply _. }
          3: { eapply ls_tmap_disj; eauto. }
          all: set_solver. 
        - eapply DROP_PRES_LSI, δ. }
      apply fm_live_spec with (s' := δ'). simpl.
      simpl. exists (Silent_step (asG ρ)). split; [| done].
      simpl. repeat split; eauto.
      + red. rewrite !F'. simpl. intros ρ' DOM1 DOM2 DECR.
        apply dom_delete, elem_of_difference in DOM2.
        rewrite not_elem_of_singleton in DOM2. apply proj2 in DOM2. 
        inversion DECR.
        * subst. symmetry in Hsametid. apply MAP_RESTR in Hsametid. congruence.
        * subst. destruct Hissome as [g MAP'].
          pose proof MAP' as ?%MAP_RESTR. subst.
          rewrite -ls_same_doms elem_of_dom in DOM1.
          destruct DOM1 as [? MAP1].
          pose proof MAP1 as ?%MAP_RESTR. subst. congruence.
      + red. rewrite !ST' !F'. intros ρ' DOM'. 
        destruct (decide (ρ' = ρ)) as [-> | ?].
        * repeat right. set_solver.
        * left. apply elem_of_dom in DOM' as [? F1].
          rewrite lookup_delete_ne; [| done].
          rewrite F1. simpl. lia.
      + rewrite F'. set_solver.
  Qed.

  Section MapRestr.
    Hypothesis (MAP_RESTR: forall (δ: lm_ls LM), ls_map_restr (ls_mapping δ)).

    Lemma unmapped_empty' (ρ: fmrole M) (δ: lm_ls LM):
      ρ ∉ dom (ls_mapping δ) <-> default ∅ (ls_tmap δ !! (asG ρ)) = ∅.
    Proof.
      destruct (decide (default ∅ (ls_tmap δ !! asG ρ) = ∅)) as [T | T]. 
      { simpl. split; [done| ]. intros _ DOM.
        apply elem_of_dom in DOM as [? DOM].
        pose proof DOM as ->%MAP_RESTR.
        apply ls_mapping_tmap_corr in DOM as (?&X&?).
        rewrite X in T. simpl in T. set_solver. }
      destruct (ls_tmap δ !! asG ρ) as [S| ] eqn:TM; [| done].
      simpl in *. split; [| done]. intros. 
      apply set_choose_L in T as [ρ' IN].
      forward eapply (proj2 (ls_mapping_tmap_corr δ ρ' (asG ρ))).
      { eauto. }
      intros T.
      pose proof T as [=]%MAP_RESTR. subst.
      destruct H. by apply elem_of_dom.
    Qed. 
    
    Lemma unmapped_empty_dom (ρ: fmrole M) (δ: lm_ls LM)
      (DOM: asG ρ ∈ dom (ls_tmap δ))
      :
      ρ ∉ dom (ls_mapping δ) <-> ls_tmap δ !! asG ρ = Some ∅.
    Proof.
      rewrite unmapped_empty'.
      apply elem_of_dom in DOM as [? DOM]. rewrite DOM. simpl.
      intuition; congruence.
    Qed. 

  End MapRestr.

  Section EnabledSingleton.
  
    Hypothesis EGS: forall ρ δ, enabled_group_singleton ρ δ.

    Lemma disabled_group_singleton ρ δ:
      ¬ role_enabled_model ((asG ρ): fmrole LMF) δ <-> ρ ∉ dom (ls_mapping δ).
    Proof. 
      apply not_iff_compat. apply EGS. 
    Qed. 
    
    Lemma disabled_group_disabled_role ρ δ:
      ¬ role_enabled_model ((asG ρ): fmrole LMF) δ -> ¬ role_enabled_model ρ (ls_under δ). 
    Proof.
      by intros ? ?%ls_mapping_dom%EGS.
    Qed.

  End EnabledSingleton.


End RestrLM.
