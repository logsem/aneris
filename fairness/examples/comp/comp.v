From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import resources actual_resources.
From trillium.fairness.heap_lang Require Import notation heap_lang_defs wp_tacs sswp_logic.
From trillium.fairness Require Import utils.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth auth gmap gset excl.
From iris.bi Require Import bi.
From trillium.fairness Require Import lm_fair fairness model_plug fuel. 
From trillium.fairness.lm_rules Require Import resources_updates.
From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness.examples.comp Require Import client_defs tracker lib_interface.
From trillium.fairness.heap_lang Require Export lang model_logic.
(* From trillium.fairness.examples.comp Require Import comp_lib_pmp. *)
  

Close Scope Z_scope.

(* Set Implicit Arguments.  *)

Section AuxDefs.
  Context {lib: LibInterface} {ρlg: fmrole libM}.

  Let LM__cl := client_model (ρlg := ρlg).
  Let M__cl := client_model_impl (ρlg := ρlg).
  Let ST := fmstate M__cl.
  Let R := fmrole M__cl.
  Let STl := fmstate libM.
  Let Rl := fmrole libM.

  Definition sets_corr `{inG Σ set_pair_RA} γ (lb: fmstate libM) : iProp Σ := 
    ∃ (R__cur R__free: gset (fmrole M__cl)), 
      own γ ((● (Excl' (R__cur, R__free))): (set_pair_RA)) ∗
      ⌜ role_enabled_model (ρlg: Rl) lb ∧ R__cur = {[ ρ_lib (ρlg := ρlg) ]} ∧ R__free = {[ ρ_cl]}  ∨ 
        ¬ role_enabled_model (ρlg: Rl) lb ∧ R__cur = {[ ρ_cl ]} ∧ R__free = {[ ρ_lib (ρlg := ρlg)]}⌝.

End AuxDefs.

Section ClientDefs.
  (* Context `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} {cG: clientGS Σ}. *)
  Context {lib: LibInterface} {ρlg: fmrole libM}.
  Let LM__cl := client_model (ρlg := ρlg).
  Let M__cl := client_model_impl (ρlg := ρlg).
  Context `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM} 
    {cfG: clientFairnessGS Σ (ρlg := ρlg)} {cG: clientGS Σ (ρlg := ρlg)}.
  
  (* Notation "'lib_inn_role'" := (fmrole lib_model_impl). *)
  (* Notation "'lib_inn_state'" := (fmstate lib_model_impl). *)
  (* Notation "'lib_state'" := (fmstate lib_fair). *)
  Let ST := fmstate M__cl.
  Let R := fmrole M__cl.

  Let STl := fmstate libM.
  Let Rl := fmrole libM. 

  Definition y_auth_model_is (y: nat): iProp Σ :=
    own (@cl_y_st_name _ _ _ cG) (● Excl' y).

  Definition y_frag_model_is (y: nat): iProp Σ :=
    own (@cl_y_st_name _ _ _ cG) (◯ Excl' y).

  Let lg := @libGSΣ _ _ _ cG.

  Definition client_inv_impl (st: ST) : iProp Σ :=
    let (lb, y) := st in
    partial_model_is st (LM := LM__cl) ∗
    y_auth_model_is y ∗
    (* model_state_interp lb (fG := cl_lib_Σ) ∗ *)
    lib_msi lb (libGS0 := lg) ∗
    tracked cl_tracker_name (sets_corr cl_set_pair_name lb). 

  Definition Ns := nroot .@ "client".

  (* Definition client_inv: iProp Σ := *)
  (*   inv Ns (∃ (st: ST), client_inv_impl st). *)
  Definition client_inv_WIP: iProp Σ :=
    ∃ (st: ST), client_inv_impl st.

End ClientDefs.

Section ClientSpec.
  Context (lib: LibInterface) (ρlg: fmrole libM).
  Let LM__cl := client_model (ρlg := ρlg). 
  Let M__cl := client_model_impl (ρlg := ρlg). 
  Let ST := fmstate M__cl.
  Let R := fmrole M__cl.
  Let STl := fmstate libM.
  Let Rl := fmrole libM. 

  Instance LFP__cl: LMFairPre LM__cl.
  Proof. Admitted.
  Definition FM__cl := LM_Fair (LF := LFP__cl). 

  Context `{EM: ExecutionModel heap_lang M__G} `{@heapGS Σ _ EM} {cpG: clientPreGS Σ (ρlg := ρlg)} {cfG: clientFairnessGS Σ (ρlg := ρlg)}.

  Definition client: val :=
  λ: <>,
    let: "x" := ref #2 in
    "x" <- #1 ;;
    lib_fun #() ;;
    "x" <- #0 ;;
    Skip
  .

  (* (* TODO: move to library, weaken Σ requirement *) *)
  (* Lemma lib_premise `{clientGS Σ} (lb: lm_ls (lib_model lib_gs)) *)
  (*   (LB_INFO: lib_ls_premise lib_gs lb): *)
  (*   ⊢ (frag_model_is (ls_under lb) -∗ frag_fuel_is (ls_fuel lb) -∗ frag_mapping_is (ls_tmap lb) -∗ *)
  (*   frag_model_is (1: fmstate lib_model_impl) ∗ frag_mapping_is {[ρlg := {[ρl]}]} ∗ frag_fuel_is {[ρl := lm_fl (lib_model lib_gs) lb]})%I. *)
  (* Proof. *)
  (*   iIntros "LST LF LM". *)
  (*   destruct LB_INFO as (LIBF & -> & LIBM). *)
  (*   iFrame "LST". iSplitL "LM". *)
  (*   { rewrite -frag_mapping_is_big_sepM. *)
  (*     2: { intros E. by rewrite E in LIBM. } *)
  (*     erewrite big_opM_insert_delete'; eauto. *)
  (*     iDestruct "LM" as "[??]". iFrame. } *)
  (*   rewrite -frag_fuel_is_big_sepM. *)
  (*   2: { intros E. by rewrite E in LIBF. } *)
  (*   erewrite big_opM_insert_delete'; eauto. *)
  (*   iDestruct "LF" as "[??]". iFrame. *)
  (* Qed. *)

  (* Let lg := @libGSΣ _ _ _ cG. *)
  (* Let tk := cl_tracker_name _ _ (clientGS := cG).  *)

  Lemma init_client_inv n:
    partial_model_is (lib_st0, n) ==∗
    ∃ (cG: clientGS Σ),
      client_inv_WIP (cG := cG) ∗ y_frag_model_is n ∗ 
      lib_post ρlg (libGS0 := libGSΣ) ∗ own (cl_tracker_name (ρlg := ρlg)) (◯E tr_free) ∗ own cl_set_pair_name (● (Excl' (∅, ∅)) ⋅ ◯ (Excl' (∅, ∅))).
  Proof using.
    iIntros "ST".
        
    unshelve iMod (lib_init $! ρlg) as (l) "(MSI_LIB & POST)".
    { apply cpG. }

    iMod (own_alloc ((● (Excl' n) ⋅ ◯ _))) as (γ_st) "[AUTH_Y FRAG_Y]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }

 
    (* iMod (inv_alloc Ns _  (∃ st, client_inv_impl st) with "[-FRAG_LIB FRAG_Y FRAG_MAP FRAG_FR FRAG_FUEL]") as "#INV". *)
    (* { iNext. rewrite /client_inv_impl. *)
    (*   iExists (_, _). iFrame. } *)
    
    iMod (own_alloc ((● (Excl' (∅, ∅)) ⋅ ◯ _): set_pair_RA)) as (γ_s) "[AUTH_S FRAG_S]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }

    iMod (init_tracker (sets_corr γ_s lib_st0)) as (γ_t) "[AUTH_TR FRAG_TR]".

    iModIntro. 
    unshelve iExists ({| cl_y_st_name := γ_st; cl_tracker_name := γ_t;
                         cl_set_pair_name := γ_s; |}); auto.
    iFrame. rewrite /client_inv_WIP. 
    iCombine "AUTH_S FRAG_S" as "?". iFrame. 
    iExists (_, _). rewrite /client_inv_impl. iFrame.
  Qed.


  (* TODO: problems with Countable instance *)
  (* Set Printing All. *)
  (* Lemma fuel_reorder_preserves_client_LSI: *)
  (*   fuel_reorder_preserves_LSI (LSI := client_LSI).  *)
  Lemma fuel_reorder_preserves_client_LSI:
    @fuel_reorder_preserves_LSI (locale heap_lang) _ _
      (client_model_impl (ρlg := ρlg)) client_LSI.
  Proof.
    done. 
    (* red. rewrite /client_LSI. intros * EQ1 EQ2 EQ3. *)
    (* intros ? LSI1 IN2. rewrite <- EQ2. auto.  *)
  Qed.

  Lemma client_LSI_fuel_independent:
    @LSI_fuel_independent (locale heap_lang) _ _ 
      (client_model_impl (ρlg := ρlg)) client_LSI.
  Proof.
    done. 
    (* red. rewrite /client_LSI. intros. *)
    (* set_solver. *)
  Qed.

  Lemma client_model_step_preserves_LSI st1 st2 ρ fm1 fm2:
    model_step_preserves_LSI st1 ρ st2 fm1 fm2 (LSI := client_LSI (ρlg := ρlg)).
  Proof. 
    done.
  Qed. 
          
  (*   (δ, 3) ρ_cl (δ, 2) (sub 1 <$> {[ρ_cl := f]}) ?Goal1 *)


  (* (* TODO: move, remove duplicates  *) *)
  (* Ltac pure_step FS indep := *)
  (*   try rewrite sub_comp; *)
  (*   iApply wp_lift_pure_step_no_fork; auto; *)
  (*   [apply indep| ..]; *)
  (*   [| iSplitR; [done| ]; do 3 iModIntro; iFrame "RON"; iSplitL "FUELS"]; *)
  (*   [| solve_fuels_S FS |]; *)
  (*   [solve_map_not_empty| ]; *)
  (*   iIntros "RON FUELS"; simpl; try rewrite sub_comp. *)

  Let msi: fmstate FM__cl -> iProp Σ := model_state_interp (LM := LM__cl).
  Let lr (δ: fmstate FM__cl) := dom (ls_tmap δ). 
  Definition CWP := @cwp _ _ EM _ heap_fairnessGS _ msi lr _. 
  
  Lemma cl_impl_lift:
  ∀ (δ1 δ2: fmstate FM__cl) (g0 : locale heap_lang) (R2 : gset
                                                     (fmrole client_model_impl)),
    locale_trans δ1 g0 δ2 (LM := LM__cl) → ls_tmap δ2 = <[g0:=R2]> (ls_tmap δ1) → lr δ2 ⊆ lr δ1.
  Proof using.
    clear dependent Σ. 
    intros ???? STEP TM.
    apply locale_trans_dom in STEP.
    rewrite /lr. rewrite TM dom_insert_L. set_solver.
  Qed. 

  Local Ltac pure_step FS indep :=
    try rewrite sub_comp;
    iApply (cwp_model_sswp_step with "[] [FUELS] [-]");
    [done| ..];
    [iApply fuel_keep_step_local_rule;
     apply cl_impl_lift| ..];
    [iNext; iApply bi.sep_assoc; iSplit;
      [| solve_fuels_S FS];
      iPureIntro; split; [| apply indep];
      set_solver| ];
    simpl. 

  (* TODO: rename sets of invariants *)
  Lemma client_spec s E (Einvs: coPset) g f
    (FB: f >= client_fl)
    (* TODO: get rid of these restrictions *)
    (DISJ_INV1: Einvs ## ↑Ns)
    (INV_SUB: Einvs ⊆ E)
    (* (DISJ_INV2: Einvs ## ↑nroot.@"spinlock"): *)
    :
    (* {{{ partial_model_is (lb0, 3)  ∗ *)
    (*     partial_free_roles_are {[ ρ_lib; ρ_ext ]} ∗ *)
    (*     has_fuels 0 {[ ρ_cl := f ]} (PMPP := PMPP)  }}} *)
    (*   client #() @ 0 *)
    (* {{{ RET #(); partial_mapping_is {[ 0 := ∅ ]} }}}. *)
    ⊢ (□ ∀ Φ,
      (partial_model_is (lib_st0, 3) ∗ 
       partial_free_roles_are {[ ρ_lib (ρlg := ρlg); ρ_ext (ρlg := ρlg) ]} ∗
       has_fuels g {[ ρ_cl := f ]}) -∗
      ▷ (∀ y, partial_mapping_is {[ g := ∅ ]} -∗ Φ y) -∗
      CWP (client #()) Φ s E Einvs 0 g).
  Proof using cpG.
    unfold client_fl in *.
    iIntros "!> %Φ (ST & FREE & FUELS) POST". rewrite /client.

    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρ_cl := f]}: gmap (fmrole M__cl) nat) 10) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    (* pure_step FS client_LSI_fuel_independent. *)
    (* Ltac pure_step FS indep := *)
    pure_step FS client_LSI_fuel_independent.    
    iApply sswp_pure_step; [done| ].
    iNext. iIntros "FUELS". simpl.

    (* TODO: replace with iMod *)
    iApply (cwp_elim_bupd with "[-ST]"). 
    2: { iApply (init_client_inv with "ST"). }
    iIntros "[%cg (INV_CL & Y_FRAG & LIB_POST & TRACK)]".
    

    cwp_bind (ref #2)%E.

    (* TODO: replace with invariant opening *)
    rewrite /client_inv_WIP /client_inv_impl.
    iDestruct "INV_CL" as ((δ & y)) "(ST & Y & LIB_MSI & TK)".
    iDestruct (lib_post_dis with "[LIB_MSI LIB_POST]") as "%DIS"; [iFrame| ]. 

    iAssert (⌜y = 3⌝)%I as %->.
    { admit. } 
    
    try rewrite sub_comp.    
    iApply (cwp_model_sswp_step with "[] [ST FUELS FREE] [-]");
    [done| ..];
    [ iApply model_step_local_rule; 
      apply cl_impl_lift| ..].
    { iNext; iFrame "ST FUELS FREE"; iPureIntro.
      do 6 (try split).
      5: by econstructor.
      6: by apply client_model_step_preserves_LSI. 
      Unshelve. 
      7: exact ({[ ρ_cl ]}).
      6: exact ({[ ρ_ext (ρlg := ρlg) := client_fl ]}).
      2-4: set_solver.
      { rewrite live_roles_2 live_roles_3.
        rewrite decide_True; auto. set_solver. }
      red. rewrite live_roles_2 live_roles_3.
      repeat (rewrite decide_True; [| done]). rewrite !map_fmap_singleton !dom_singleton_L.
      do 5 (try split).
      1-3, 5-6: set_solver. 
      intros ?. intros [->%elem_of_singleton ?]%elem_of_difference.
      rewrite lookup_singleton. simpl. done. }
    iApply wp_alloc. iIntros "!> %x X _".
    rewrite live_roles_3 live_roles_2. repeat (rewrite decide_True; [| done]).
    iIntros "(FUELS & ST & FREE)".
    iDestruct (frag_free_roles_are_proper {[ ρ_cl; ρ_lib (ρlg := ρlg) ]} with "FREE") as "FREE".
    { set_solver. }

    iApply cwp_value.

    clear FS. 
    rewrite (sub_0_id {[ _ := _ ]}).    
    assert (fuels_ge ({[ρ_ext (ρlg := ρlg) := client_fl]}: gmap (fmrole M__cl) nat) 10) as FS.
    { red. rewrite /client_fl. intros ??[<- ?]%lookup_singleton_Some. lia. }

    cwp_bind (Rec _ _ _)%E.
    pure_step FS client_LSI_fuel_independent.
    iApply sswp_pure_step; [done| ].
    iNext. iIntros "FUELS". simpl.

    iApply cwp_value.
    
    pure_step FS client_LSI_fuel_independent.
    iApply sswp_pure_step; [done| ].
    iNext. iIntros "FUELS". simpl.

    cwp_bind (_ <- _)%E.
    pose proof DIS as [δ' RESET]%lib_reset_dom. 

    assert (ρlg ∈ live_roles libM δ') as LIVE'.
    { eapply lib_reset_cod. red. eauto. } 

    iApply (cwp_model_sswp_step with "[] [ST FUELS FREE] [-]").
    { done. }
    { iApply model_step_local_rule. apply cl_impl_lift. }
    { iNext; iFrame "ST FUELS FREE"; iPureIntro.
      do 6 (try split).
      5: by econstructor.
      6: by apply client_model_step_preserves_LSI. 
      Unshelve. 
      7: exact ({[ ρ_ext (ρlg := ρlg) ]}).
      6: exact ({[ ρ_lib (ρlg := ρlg) := client_fl ]}).
      2-4: set_solver.
      { rewrite live_roles_2 live_roles_1.
        (* pose proof (lib_strong_lr δ' ρlg). *)
        rewrite decide_True; auto. 
        rewrite decide_True; auto. set_solver. }
      red. rewrite live_roles_2 live_roles_1.
      rewrite !decide_bool_decide.
      rewrite (bool_decide_eq_true_2 _ LIVE') (bool_decide_eq_true_2 _ DIS).
      do 5 (try split).
      1-3, 5-6: set_solver.
      rewrite !dom_singleton_L. 
      intros ? [->%elem_of_singleton ?]%elem_of_difference.
      rewrite lookup_singleton. simpl. done. }
    iApply (wp_store with "X").
    iNext. iIntros "X (FUELS & ST & FREE)".
    iDestruct (frag_free_roles_are_proper {[ ρ_cl; ρ_ext (ρlg := ρlg) ]} with "FREE") as "FREE".
    { rewrite live_roles_1 live_roles_2. do 2 (rewrite decide_True; eauto). 
      set_solver. }

    iApply cwp_value.

    clear FS. 
    rewrite (sub_0_id {[ _ := _ ]}).    
    assert (fuels_ge ({[ρ_lib (ρlg := ρlg) := client_fl]}: gmap (fmrole M__cl) nat) 10) as FS.
    { red. rewrite /client_fl. intros ??[<- ?]%lookup_singleton_Some. lia. }
   
    cwp_bind (Rec _ _ _)%E.
    pure_step FS client_LSI_fuel_independent.
    iApply sswp_pure_step; [done| ].
    iNext. iIntros "FUELS". simpl.

    iApply cwp_value.

    pure_step FS client_LSI_fuel_independent.
    iApply sswp_pure_step; [done| ].
    iNext. iIntros "FUELS". simpl.

    cwp_bind (lib_fun #())%E.

    (* TODO: this should be already done before, as a result of keeping invariant *)
    iAssert (y_auth_model_is 1 ∗ y_frag_model_is 1 ∗ lib_msi δ' ∗ lib_pre ρlg)%I with "[Y Y_FRAG LIB_MSI LIB_POST]" as "(Y & Y_FRAG & LIB_MSI & LIB_PRE)".
    { admit. }

    iMod (

      
      repeat (rewrite decide_True; [| done]). rewrite !map_fmap_singleton !dom_singleton_L.
      do 5 (try split).
      1-3, 5-6: set_solver. 
      intros ?. intros [->%elem_of_singleton ?]%elem_of_difference.
      rewrite lookup_singleton. simpl. done. }

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
                                                                                        
    (* wp_bind (Rec BAnon BAnon (RecV BAnon BAnon (LitV LitUnit) (LitV LitUnit)) *)
    (*          (Store (LitV l) (LitV 0%Z))).  *)
    (*                                                                                     (Rec BAnon BAnon *)
    (*       (Rec BAnon BAnon (RecV BAnon BAnon (LitV LitUnit) (LitV LitUnit)) *)
    (*          (Store (LitV l) (LitV 0%Z))) (LitV LitUnit)) *)
    (* red. simpl. red. simpl. red.  *)

    iApply wp_atomic.
    { admit. }
    iInv Ns as ((lb, y)) "inv" "CLOS". rewrite {1}/client_inv_impl.
    iDestruct "inv" as "(>ST & >YST_AUTH & > inv')".



        
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
