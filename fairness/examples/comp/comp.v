From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import resources actual_resources.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness Require Import utils.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness Require Import lm_fair. 
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.comp Require Import lib lib_ext client_defs.
From trillium.fairness.heap_lang Require Export lang lm_lsi_hl_wp tactics proofmode_lsi wp_tacs.
From trillium.fairness.examples.comp Require Import comp_lib_pmp.


Close Scope Z_scope. 

Section ClientSpec.
  Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} {cpG: clientPreGS Σ}.
  Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ client_model_impl}.
  Context {relies_on: locale heap_lang -> locale heap_lang -> iProp Σ}. 
  Notation " τ '⤞' g" := (relies_on τ g) (at level 20). 


  Definition client: val :=
  λ: <>,
    let: "x" := ref #2 in
    "x" <- #1 ;;
    lib_fun #() ;;
    "x" <- #0 ;;
    Skip
  .

  (* Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (EM := EM) (iLM := client_model) (PMPP := PMPP) (eGS := heap_fairnessGS))). *)
  Notation "'LSG' Einvs" := (LM_steps_gen Einvs (EM := EM) (iLM := client_model) (PMPP := PMPP) (eGS := heap_fairnessGS) (relies_on := relies_on)) (at level 10).

  (* TODO: move to library, weaken Σ requirement *)
  Lemma lib_premise `{clientGS Σ} (lb: lm_ls (lib_model lib_gs))
    (LB_INFO: lib_ls_premise lib_gs lb):
    ⊢ (frag_model_is (ls_under lb) -∗ frag_fuel_is (ls_fuel lb) -∗ frag_mapping_is (ls_tmap lb) -∗
    frag_model_is (1: fmstate lib_model_impl) ∗ frag_mapping_is {[ρlg := {[ρl]}]} ∗ frag_fuel_is {[ρl := lm_fl (lib_model lib_gs) lb]})%I.
  Proof.
    iIntros "LST LF LM".
    destruct LB_INFO as (LIBF & -> & LIBM).
    iFrame "LST". iSplitL "LM".
    { rewrite -frag_mapping_is_big_sepM.
      2: { intros E. by rewrite E in LIBM. }
      erewrite big_opM_insert_delete'; eauto.
      iDestruct "LM" as "[??]". iFrame. }
    rewrite -frag_fuel_is_big_sepM.
    2: { intros E. by rewrite E in LIBF. }
    erewrite big_opM_insert_delete'; eauto.
    iDestruct "LF" as "[??]". iFrame.
  Qed.

  Lemma init_client_inv lb0 n:
    partial_model_is (lb0, n)  ={∅}=∗
    ∃ (cG: clientGS Σ), client_inv ∗
                        frag_fuel_is (ls_fuel lb0) (fG := cl_lib_Σ) ∗
                        frag_mapping_is (ls_tmap lb0) (fG := cl_lib_Σ)∗
                        frag_model_is lb0 (fG := cl_lib_Σ)∗
                        frag_free_roles_are ∅ (fG := cl_lib_Σ)∗
                        y_frag_model_is n.
  Proof using cpG.
    iIntros "ST".
        
    iMod (lm_msi_init lb0 ∅) as (fG) "(MSI_LIB & FRAG_LIB & FRAG_MAP & FRAG_FUEL & FRAG_FR)".
    { set_solver. }

    iMod (own_alloc ((● (Excl' n) ⋅ ◯ _))) as (γ_st) "[AUTH_Y FRAG_Y]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }

    set (cG := {|
                cl_pre_inG := cpG;
                cl_y_st_name := γ_st;
                cl_lib_Σ := fG;
              |}).
 
    iMod (inv_alloc Ns _  (∃ st, client_inv_impl st) with "[-FRAG_LIB FRAG_Y FRAG_MAP FRAG_FR FRAG_FUEL]") as "#INV".
    { iNext. rewrite /client_inv_impl.
      iExists (_, _). iFrame. }

    iModIntro. iExists _. iFrame. done.
  Qed.


  (* TODO: problems with Countable instance *)
  (* Set Printing All. *)
  (* Lemma fuel_reorder_preserves_client_LSI: *)
  (*   fuel_reorder_preserves_LSI (LSI := client_LSI).  *)
  Lemma fuel_reorder_preserves_client_LSI:
    @fuel_reorder_preserves_LSI (locale heap_lang) _ _ client_model_impl client_LSI.
  Proof.
    red. rewrite /client_LSI. intros * EQ1 EQ2 EQ3.
    intros ? LSI1 IN2. rewrite <- EQ2. auto. 
  Qed.

  Lemma client_LSI_fuel_independent:
    (* @LSI_fuel_independent (LSI := client_LSI). *)
    @LSI_fuel_independent (locale heap_lang) _ _ client_model_impl client_LSI.
  Proof.
    red. rewrite /client_LSI. intros.
    set_solver.
  Qed.

  (* TODO: move, remove duplicates  *)
  Ltac pure_step FS indep :=
    try rewrite sub_comp;
    iApply wp_lift_pure_step_no_fork; auto;
    [apply indep| ..];
    [| iSplitR; [done| ]; do 3 iModIntro; iFrame "RON"; iSplitL "FUELS"];
    [| solve_fuels_S FS |];
    [solve_map_not_empty| ];
    iIntros "RON FUELS"; simpl; try rewrite sub_comp.

  Lemma client_spec (Einvs: coPset) (lb0: fmstate lf) f
    (FB: f >= client_fl)
    (* TODO: get rid of these restrictions *)
    (DISJ_INV1: Einvs ## ↑Ns)
    (* (DISJ_INV2: Einvs ## ↑nroot.@"spinlock"): *)
    
    (* (LB0_INFO: lib_ls_premise lb0) *)
    (LB0_INFO: lm_is_stopped ρlg lb0)
    :
    LSG Einvs -∗
    {{{ partial_model_is (lb0, 3)  ∗
        partial_free_roles_are {[ ρ_lib; ρ_ext ]} ∗
        0 ⤞ 0 ∗
        has_fuels 0 {[ ρ_cl := f ]} (PMPP := PMPP)  }}}
      client #() @ 0
    {{{ RET #(); 0 ⤞ 0 ∗ partial_mapping_is {[ 0 := ∅ ]} }}}.
  Proof using cpG.
    unfold client_fl in *.
    iIntros "#PMP" (Φ) "!> (ST & FREE & RON & FUELS) POST". rewrite /client.

    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρ_cl := f]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    iPoseProof (LM_steps_gen_nofork_sub with "PMP") as "PMP'".
    pure_step FS client_LSI_fuel_independent.

    wp_bind (ref _)%E.
    iApply (wp_alloc_nostep with "[$] [RON FUELS]").
    { apply client_LSI_fuel_independent. }
    2: { solve_fuels_S FS. }
    { solve_map_not_empty. }
    iNext. iIntros (l) "(L & MT & RON & FUELS) /=".
    
    do 2 pure_step FS client_LSI_fuel_independent.
    (* Set Printing Implicit. Unshelve. *)

    pose proof (live_roles_3 lb0) as LIVE3.
    pose proof (live_roles_2 lb0) as LIVE2.
    rewrite decide_True in LIVE2; [ | done].

    wp_bind (_ <- _)%E.
    iApply (wp_store_step_keep with "[$] [L ST RON FUELS FREE]").
    { set_solver. }
    8: { iFrame "L RON ST FREE". iNext.
         rewrite map_fmap_singleton. iFrame. }
    { econstructor. }
    3: { rewrite dom_singleton. reflexivity. }
    2: { rewrite LIVE3 LIVE2.
         apply union_subseteq_l'. set_solver. }
    2: { set_solver. }
    { Unshelve. 2: exact {[ ρ_ext := lm_fl client_model (lb0, 2) ]}.
      repeat split; rewrite ?LIVE3 ?LIVE2.
      1-3, 5-7: set_solver.
      intros. assert (ρ' = ρ_ext) as -> by set_solver.
      rewrite lookup_singleton. simpl. lia. }
    { set_solver. }
    { red. intros. simpl. red.
      intros lg [? IN]. simpl in IN.
      assert (lg = ρlg) as ->.
      { unshelve eapply elem_of_singleton.
        { exact (gset lib_grole). }
        all: try by apply _. 
        apply elem_of_subseteq_singleton.
        etrans; [| apply (ls_inv lb0)].
        apply elem_of_subseteq_singleton.
        apply ls_mapping_tmap_corr in IN as (?&?&?).
        eapply @elem_of_dom; eauto. apply _. }
      red in LB0_INFO. do 2 apply proj2 in LB0_INFO.
      apply ls_mapping_tmap_corr in IN as (?&IN&?).
      rewrite LB0_INFO in IN. clear -H3 IN. set_solver. }

    iNext. iIntros "(L & ST & RON & FUELS & FR)".
    rewrite LIVE3 LIVE2.
    iDestruct (partial_free_roles_are_Proper with "FR") as "FR".
    { rewrite !dom_singleton.
      Unshelve. 2: exact ({[ρ_lib; ρ_cl]}). set_solver. }

    simpl. clear FS.
    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρ_ext := client_fl]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. unfold client_fl.
      intros ??[? ?]%lookup_singleton_Some. lia. }

    pure_step FS client_LSI_fuel_independent. 

    set (lb' := reset_lm_st ρlg lb0 ρlg_in_lib_gs).
    pose proof (live_roles_1 lb') as LIVE1.
    rewrite decide_True in LIVE1.
    2: { apply lib_premise_dis. by apply lib_reset_premise. }
           
    iApply (wp_lift_pure_step_no_fork_take_step_stash).
    { done. }
    (* { reflexivity. } *)
    9: iSplitL "PMP"; [by iApply "PMP'"| ]; iFrame "ST RON FUELS FR".
    { set_solver. }
    3: { rewrite dom_fmap dom_singleton. reflexivity. }
    5: { by econstructor. }
    2: { Unshelve. 3: exact {[ρ_lib := client_fl]}. 2: exact ⊤.       
         rewrite LIVE2 LIVE1. set_solver. }
    2: { set_solver. }
    2: { set_solver. }
    2: { red. intros.
         red. 
         intros lg [? IN]. simpl in IN.
         assert (lg = ρlg) as ->.
         { apply ls_mapping_tmap_corr in IN.
           destruct IN as (?&TM&IN). 
           rewrite /reset_lm_st in TM. simpl in TM.
           apply lookup_insert_Some in TM. destruct TM as [TM | TM].
           { symmetry. apply TM. }
           destruct TM as [NEQ TM]. 
           simpl in TM. apply lookup_fmap_Some in TM.
           destruct TM as (?&<-&TM).
           red in LB0_INFO. apply proj2, proj1 in LB0_INFO.
           destruct LB0_INFO. apply elem_of_dom.
           exists lg. eapply ls_mapping_tmap_corr. eexists. split; eauto.
           set_solver. }

         fold ρ_lib. 
         rewrite /mapped_roles. rewrite map_img_insert_L.
         rewrite flatten_gset_union flatten_gset_singleton.
         set_solver. }
    { repeat split; rewrite ?LIVE2 ?LIVE1.
      1-3, 5-7: set_solver. 
      intros. simpl. assert (ρ' = ρ_lib) as -> by set_solver.
      rewrite lookup_singleton. simpl. lia. }
    do 3 iModIntro. iIntros "ST FR RON FUELS".
    rewrite LIVE2 LIVE1.
    iDestruct (partial_free_roles_are_Proper with "FR") as "FR".
    { Unshelve. 2: exact {[ ρ_cl; ρ_ext ]}. set_solver. } 
    simpl.    

    iApply fupd_wp.
    iPoseProof (init_client_inv with "ST") as "inv".
    iMod (fupd_mask_mono with "inv") as (?) "(#INV & LF & LM & LST & LFR & YST)".
    { set_solver. }
    iModIntro.

    wp_bind (lib_fun #())%E.
    (* iDestruct "FUELS" as "[MAP FUELS]".  *)
    iDestruct (has_fuels_equiv with "FUELS") as "[MAP FUELS]".
    
    (* iApply (lib_spec (PMPP := lib_PMPP) with "[] [LST YST LF LM FR MAP RON FUELS]"); cycle 1.  *)
    iDestruct (partial_free_roles_are_sep with "FR") as "[FR FR']"; [set_solver| ].
    iApply (lib_spec (PMPP := lib_PMPP) with "[] [LST YST LF LM FR RON MAP FUELS]"); cycle 1. 
    { iApply lib_PMP; [done| ]. iSplit; done. }
    {
      (* simpl. *)
      iDestruct (lib_premise with "LST LF LM") as "(LST & LF & LM)"; eauto.
      { by apply lib_reset_premise. }
      rewrite has_fuels_equiv. simpl.
      rewrite !dom_singleton_L !big_sepM_singleton.
      iFrame.
      do 2 iExists _. iFrame "FR". iFrame.

      iLeft.
      iSplitR.
      { iPureIntro. split; reflexivity. }
      iExists _. iFrame. iPureIntro. rewrite /client_fl. lia. }
    2: { unfold lib_fl. lia. }
 
    iNext. iIntros "(RON & LMAP & LFR')". simpl.
                                                                                        rewrite /relies_on_lib. iDestruct "RON" as (? ?) "(? & MAP & RON & FR & YST)".
                                                                                        (* wp_bind (Rec _ _ (_ ;; _) _). *)
    (* Unset Printing Notations. *)
                                                                                        
    wp_bind (Rec BAnon BAnon (RecV BAnon BAnon (LitV LitUnit) (LitV LitUnit))
             (Store (LitV l) (LitV 0%Z))). 
                                                                                        (Rec BAnon BAnon
          (Rec BAnon BAnon (RecV BAnon BAnon (LitV LitUnit) (LitV LitUnit))
             (Store (LitV l) (LitV 0%Z))) (LitV LitUnit))
    red. simpl. red. simpl. red. 









        
    iDestruct "LMAP" as (???) "(%LIBM & LM & MATCH & MAP & FR & YST)".
    assert (L = ∅) as -> by set_solver.
    iDestruct "MATCH" as "[[%?] | (_&[->->]&FUEL')]"; [set_solver| ]. clear LIBM.
                                      
    iAssert (has_fuels 0 {[ ρ_cl := 15 ]})%I with "[FUEL' MAP]" as "FUELS".
    { rewrite /has_fuels.
      rewrite !dom_singleton_L !big_sepS_singleton.
      rewrite lookup_singleton. iFrame. iExists _. iFrame. done. }
    
    simpl. clear FS.
    rewrite (sub_0_id {[ ρ_cl := _ ]}).
    assert (fuels_ge ({[ ρ_cl := 15 ]}: gmap (fmrole client_model_impl) nat) 10) as FS.
    { red. intros ??[? ?]%lookup_singleton_Some. lia. }

    do 2 pure_step FS client_LSI_fuel_independent.
    
    wp_bind (_ <- _)%E.

    iApply wp_atomic.
    iInv Ns as ((lb, y)) "inv" "CLOS". rewrite {1}/client_inv_impl.
    iDestruct "inv" as "(>ST & >YST_AUTH & > inv')".
    iAssert (⌜ y = 1 ⌝)%I as %->.
    { iCombine "YST_AUTH YST" as "Y". iDestruct (own_valid with "Y") as %V.
      apply auth_both_valid_discrete in V as [EQ%Excl_included _]. done. }
    iAssert (⌜ ls_tmap lb !! ρlg = Some ∅ ⌝)%I as %LIB_END.
    { iApply (frag_mapping_same with "[inv'] LM").
      rewrite /model_state_interp. iFrame.
      iDestruct "inv'" as (?) "(?&?&_)". iFrame.  }

    pose proof (live_roles_1 lb) as LIVE1'.
    (* rewrite !(decide_False, decide_True) in LIVE1'. -- TODO: how to do it in ssr?*)
    erewrite decide_False, decide_True in LIVE1'; eauto.
    2: { apply LM_map_empty_notlive. eauto. }
    
    pose proof (live_roles_0 lb) as LIVE0.
    
    iModIntro.
    iApply (wp_store_step_singlerole_keep with "[$] [L ST FUELS]").
    { set_solver. }
    (* { reflexivity. } *)
    6: { iFrame "L ST". iNext.
         iApply has_fuel_fuels. rewrite map_fmap_singleton. iFrame. }
    2: { by apply ct_y_step_1. }
    3: { rewrite LIVE1' LIVE0. set_solver. }
    { Unshelve. 2: exact 7. simpl. rewrite /client_fl. lia. }
    { lia. }
    { red. intros. simpl. red.
      intros ? [? MAP].
      apply (ls_mapping_tmap_corr) in MAP as (? & TMAP' & ?).
      assert (ρlg = gi) as <- by (by destruct ρlg, gi).
      set_solver. }

    (* rewrite LIVE0. erewrite decide_False; [| set_solver]. *)
    iNext. iIntros "(L & ST & FUELS)".
    iMod (y_update_model _ _ 0 with "YST_AUTH YST") as "[YST_AUTH YST]".
    
    iMod ("CLOS" with "[YST_AUTH ST inv']") as "_".
    { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. }
    iModIntro.
    
    iDestruct (has_fuel_fuels with "FUELS") as "FUELS".
    simpl. clear FS.
    rewrite (sub_0_id {[ ρ_cl := _ ]}).
    assert (fuels_ge ({[ ρ_cl := 7 ]}: gmap (fmrole client_model_impl) nat) 7) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    do 2 pure_step FS client_LSI_fuel_independent.

    iApply wp_atomic.
    iInv Ns as ((lb'', y)) "inv" "CLOS". rewrite {1}/client_inv_impl.
    iDestruct "inv" as "(>ST & >YST_AUTH & > inv')".
    iAssert (⌜ y = 0 ⌝)%I as %->.
    { iCombine "YST_AUTH YST" as "Y". iDestruct (own_valid with "Y") as %V.
      apply auth_both_valid_discrete in V as [EQ%Excl_included _]. done. }
    iAssert (⌜ ls_tmap lb'' !! ρlg = Some ∅ ⌝)%I as %LIB_END''.
    { iApply (frag_mapping_same with "[inv'] LM").
      rewrite /model_state_interp. iFrame.
      iDestruct "inv'" as (?) "(?&?&_)". iFrame.  }
    (* Unshelve. 2: exact (⊤ ∖ ↑Ns).  *)
    iModIntro.
    
    iApply (wp_lift_pure_step_no_fork_remove_role {[ ρ_cl ]} ((lb'', 0): fmstate client_model_impl) _ _ _ _ _ _ _ (sub 3 <$> {[ρ_cl := 7]}) (iLM := client_model)); eauto.
    { solve_map_not_empty. }
    { set_solver. }
    { rewrite live_roles_0. set_solver. }
    { red. intros. red. intros.
      red in H0. specialize (H0 _ H1). simpl in H1.
      destruct H1  as [? IN]. 
      assert (gi = ρlg) as ->.
      { unshelve eapply elem_of_singleton.
        { exact (gset lib_grole). }
        all: try by apply _. 
        apply elem_of_subseteq_singleton.
        etrans; [| apply (ls_inv lb'')].
        apply elem_of_subseteq_singleton.
        apply ls_mapping_tmap_corr in IN as (?&?&?).
        eapply @elem_of_dom; eauto. apply _. }
      apply ls_mapping_tmap_corr in IN as (?&?&?).
      rewrite LIB_END'' in H1. clear -H2 H1. set_solver. }
    iFrame "PMP'". do 3 iModIntro. iFrame.
    iSplitL "FUELS".
    { solve_fuels_S FS. }
    iIntros "ST FUELS".

    simpl. iApply wp_value'.
    iMod ("CLOS" with "[ST YST_AUTH inv']") as "_".
    { rewrite /client_inv_impl. iNext. iExists (_, _). iFrame. }
    iModIntro. iApply "POST".
    iDestruct (has_fuels_equiv with "FUELS") as "[MAP FUEL]".
    iApply partial_mapping_is_Proper; [| by iFrame].
    f_equiv. rewrite map_fmap_singleton dom_singleton_L.
    rewrite difference_diag_L.
    rewrite dom_filter_comm.
    by rewrite dom_singleton_L filter_singleton_not.
  Qed.
 
End ClientSpec.
