From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre ewp.
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
From trillium.fairness.heap_lang Require Export ewp_model_logic lang.
From trillium.fairness.lm_rules Require Import model_step.
  

Close Scope Z_scope.

(* Set Implicit Arguments.  *)

(* Section AuxDefs. *)
(*   Context {lib: LibInterface} {ρlg: fmrole libM}. *)

(*   Let LM__cl := client_model (ρlg := ρlg). *)
(*   Let M__cl := client_model_impl (ρlg := ρlg). *)
(*   Let ST := fmstate M__cl. *)
(*   Let R := fmrole M__cl. *)
(*   Let STl := fmstate libM. *)
(*   Let Rl := fmrole libM. *)

(*   Definition sets_corr `{inG Σ set_pair_RA} γ (lb: fmstate libM) : iProp Σ :=  *)
(*     ∃ (R__cur R__free: gset (fmrole M__cl)),  *)
(*       own γ ((● (Excl' (R__cur, R__free))): (set_pair_RA)) ∗ *)
(*       ⌜ role_enabled_model (ρlg: Rl) lb ∧ R__cur = {[ ρ_lib (ρlg := ρlg) ]} ∧ R__free = {[ ρ_cl]}  ∨  *)
(*         ¬ role_enabled_model (ρlg: Rl) lb ∧ R__cur = {[ ρ_cl ]} ∧ R__free = {[ ρ_lib (ρlg := ρlg)]}⌝. *)

(* End AuxDefs. *)

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

  Definition MSI__lib (lb: fmstate libM) := lib_msi lb (libGS0 := lg). 
  Definition MSI__cl := model_state_interp (LM := LM__cl). 

  Definition client_inv_impl (st: ST) : iProp Σ :=
    let (lb, y) := st in
    partial_model_is st (LM := LM__cl) ∗
    y_auth_model_is y ∗
    (* model_state_interp lb (fG := cl_lib_Σ) ∗ *)
    MSI__lib lb
    .
    (* ∗ *)
    (* tracked cl_tracker_name (sets_corr cl_set_pair_name lb).  *)

  Definition Ns := nroot .@ "client".

  Definition client_inv: iProp Σ :=
    inv Ns (∃ (st: ST), client_inv_impl st).
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
      lib_post ρlg (libGS0 := libGSΣ).
  Proof using cpG.
    iIntros "ST".
        
    unshelve iMod (lib_init $! ρlg) as (l) "(MSI_LIB & POST)".
    { apply cpG. }

    iMod (own_alloc ((● (Excl' n) ⋅ ◯ _))) as (γ_st) "[AUTH_Y FRAG_Y]".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }

    iMod (own_alloc ((● (Excl' n) ⋅ ◯ _))) as (γ_t) "TT".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }
    iMod (own_alloc ((● (Excl' n) ⋅ ◯ _))) as (γ_s) "SS".
    { apply auth_both_valid_discrete. split; [| done]. reflexivity. }

    iModIntro. 
    unshelve iExists ({| cl_y_st_name := γ_st; cl_tracker_name := γ_t;
                         cl_set_pair_name := γ_s; |}); auto.
    iFrame. rewrite /client_inv_WIP. 
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
  Let step_restr st1 st2 := lr st2 ⊆ lr st1. 
  Let PI (p: state) := gen_heap_interp p.(heap). 

  Let ewp'_instance_helper := ewp' (PI := PI) (MSI := msi) (step_restr := step_restr).  
  Existing Instance ewp'_instance_helper. 
  
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

  (* Local Ltac pure_step FS indep := *)
  (*   try rewrite sub_comp; *)
  (*   iApply (sswp_MU_cwp with "[] [FUELS] [-]"); *)
  (*   [done| ..]; *)
  (*   [iApply fuel_keep_step_local_rule; *)
  (*    apply cl_impl_lift| ..]; *)
  (*   [iNext; iApply bi.sep_assoc; iSplit; *)
  (*     [| solve_fuels_S FS]; *)
  (*     iPureIntro; split; [| apply indep]; *)
  (*     set_solver| ]; *)
  (*   simpl.  *)

  Notation "'EWP' e @ s ; ρ ; E {{ Φ } }" := (ewp s E ρ e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'EWP' e @ s ; ρ ; E {{ v , Q } }" := (ewp s E ρ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  s ;  ρ ;  E  {{  v ,  Q  } } ']' ']'") : bi_scope.

  (* Let lib_step_restr (δ1 δ2: fmstate libM) := live_roles _ δ2 ⊆ live_roles _ δ1.  *)
  (* Let ewp'_lib {cG: clientGS Σ} :=  *)
  (*       ewp' *)
  (*         (PI := PI) *)
  (*         (MSI := MSI__lib (cG := cG) (ρlg := ρlg)) *)
  (*         (step_restr := lib_step_restr).  (*  *) *)

  (* TODO: move *)
  Lemma ite_neg `{Decision P} {A: Type} (x y : A):
    (if decide (¬ P) then x else y) = if decide P then y else x.
  Proof.
    symmetry. destruct decide.
    - rewrite decide_False; [done| ]. tauto.
    - by rewrite decide_True. 
  Qed.

  Lemma update_client_state {cG: clientGS Σ (ρlg := ρlg)}
    g__cl (lb lb': fmstate libM) f
    (LIB_STEP: fmtrans libM lb (Some ρlg) lb')
    (F_BOUND: f ≤ client_fl)
    (dis' := ¬ role_enabled_model (ρlg: fmrole libM) lb')
    :    
    ⊢
    partial_model_is (lb, 1) -∗
    partial_free_roles_are {[ρ_cl]} -∗
    has_fuels g__cl {[ρ_lib (ρlg := ρlg) := f]} -∗    
    let post := has_fuels g__cl (if decide dis' then {[ρ_cl := client_fl]} else {[ρ_lib (ρlg := ρlg) := f]}) ∗
                partial_model_is (lb', 1) ∗
                partial_free_roles_are (if decide dis' then {[ρ_lib (ρlg := ρlg)]} else {[ρ_cl]}) in
    @LMU _ _ (MSI__cl: fmstate FM__cl -> iProp Σ) (fun δ => dom (ls_tmap δ)) g__cl post.
  Proof using.
    clear dependent PI M__G. 
    rewrite /LMU. iIntros "ST FR FUELS" (δ) "MSI". 
    Local Ltac dEq := destruct (decide (_ = _)).
    Local Ltac dEl := rewrite ?ite_neg; unfold role_enabled_model; destruct (decide (_ ∈ _)).

    rewrite /MSI__cl. iDestruct (model_agree' with "MSI ST") as "%".
    (* Set Printing Coercions. *)
    
    pose proof (live_roles_1 lb (ρlg := ρlg)) as LIVE. rewrite decide_True in LIVE.
    2: { eapply fm_live_spec; eauto. }
    pose proof (live_roles_1 lb' (ρlg := ρlg)) as LIVE'.

    iPoseProof (actual_update_step_still_alive_gen with "[$] [$] [$] [$]") as "STEP".
    5: { apply ct_lib_step. eauto. }
    { rewrite LIVE LIVE'.
      apply union_subseteq_l'.
      dEl; set_solver. }
    { rewrite dom_singleton.
      assert ((if (decide dis')
              then {[ ρ_lib (ρlg := ρlg) ]}
              else (∅: gset (fmrole M__cl))) ⊆ {[ρ_lib (ρlg := ρlg)]}) as IN.
      { dEl; set_solver. }
      apply IN. }
    { rewrite LIVE. set_solver. }
    all: eauto.
    { Unshelve.
      2: exact (if decide dis'
                then {[ ρ_cl := client_fl ]}
                else {[ ρ_lib (ρlg := ρlg) := f ]}).
      dEl; set_solver. }
    { repeat split; rewrite ?LIVE ?LIVE';  clear -F_BOUND. 
      - dEl.
        2: { set_solver. }
        intros _.
        rewrite lookup_singleton. simpl. lia. 
      - dEl; set_solver. 
      - set_solver.
      - dEl; [set_solver| ].
        intros. assert (ρ' = ρ_cl) as -> by set_solver.
        rewrite lookup_singleton. simpl. lia.
      - dEl; set_solver.
      - dEl; set_solver.
      - dEl; set_solver. }    
    (* { red. simpl. intros. red.  *)
    (*   simpl. intros g' [? IN']. *)
    (*   apply ls_mapping_tmap_corr in IN' as (?&TM'&?). *)
    (*   pose proof (lib_tmap_dom_restricted lb') as DOML. *)
    (*   specialize (DOML g'). specialize_full DOML. *)
    (*   { apply elem_of_dom. eauto. } *)
    (*   apply elem_of_singleton in DOML. subst g'. *)
    (*   rewrite decide_False. *)
    (*   2: { apply P_NNP. apply egsg_lib. rewrite TM'. set_solver. } *)
    (*   rewrite /mapped_roles. apply flatten_gset_spec. *)
    (*   exists ({[ ρ_lib ]}). split; [| apply elem_of_singleton; reflexivity]. *)
    (*   rewrite elem_of_map_img. exists g. *)
    (*   by rewrite lookup_insert dom_singleton_L. } *)
    { apply client_model_step_preserves_LSI. }
      
    rewrite LIVE LIVE'.
    iMod "STEP" as (?) "(%TRANS & FUEL & ST & MSI & FREE & %RESTR)".
    iModIntro. iExists _. iFrame.
    iSplitL.
    { iApply partial_free_roles_are_Proper; [| iFrame].
      rewrite !dom_singleton_L. 
      dEl; tauto || set_solver. }
    iPureIntro. split.
    - eexists. split; [apply TRANS| ]. done.
    - rewrite RESTR. rewrite dom_insert_L.
      forward eapply locale_trans_dom.
      { eexists. split; [apply TRANS| ]. done. }
      set_solver.
   Qed.

  (* TODO: do we need to require MSI to be timeless?
     Or add ▷ on MSI we get after the step in EWP? *)

  (* TODO: unify with model_agree ? *)
  Lemma y_model_agree {cG: clientGS Σ} y1 y2:
    ⊢ y_auth_model_is y1 -∗ y_frag_model_is (ρlg := ρlg) y2 -∗ ⌜y1 = y2⌝.
  Proof.
    iIntros "Ha Hf".
    by iDestruct (own_valid_2 with "Ha Hf") as
      %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  (* TODO: unify with update_model ? *)
  Lemma y_update_model {cG: clientGS Σ} y1 y2 y:
    y_auth_model_is y1 -∗ y_frag_model_is y2 ==∗ y_auth_model_is y ∗ y_frag_model_is (ρlg := ρlg) y.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[??]" ; eauto.
    - by apply auth_update, option_local_update, (exclusive_local_update _ (Excl y)).
    - iModIntro. iFrame.
  Qed.

  Lemma lift_lib_spec {cG: clientGS Σ (ρlg := ρlg)} s (g__cl: fmrole FM__cl)
    E__lib Φ (f: nat) e
    (NV: to_val e = None)
    (DIS: ↑Ns ## E__lib)
    (FUEL_BOUND: f ≤ client_fl):
    ⊢
      (∀ v δ, Φ v -∗ MSI__lib δ -∗ ⌜ ¬ role_enabled_model ρlg δ ⌝) -∗
      client_inv -∗
      has_fuels g__cl {[ ρ_lib (ρlg := ρlg) := f ]} -∗ 
      partial_free_roles_are {[ ρ_cl ]} -∗
      (* EWP (lib_fun #()) @ s ; g__cl ; E {{ v, Φ v }}. *)
      y_frag_model_is 1 -∗      
      @ewp _ _ _ _ (ewp'_lib (l := libGSΣ)) s E__lib ρlg e Φ -∗
      EWP e @ s ; g__cl ; (E__lib ∪ ↑Ns) 
        {{ v, Φ v ∗ has_fuels g__cl {[ ρ_cl := f ]} ∗ partial_free_roles_are {[ ρ_lib (ρlg := ρlg) ]} ∗ y_frag_model_is 1 }}.
  Proof.
    iIntros "POST_DIS #INV_CL FUELS FREE Y1 EWP_LIB".
    iLöb as "IH" forall (e NV).
    rewrite (ewp_unfold _ _ _ g__cl) /ewp_pre. simpl. rewrite NV. 
    iIntros (σ1 δ__cl) "PI MSI_cl".

    iInv "INV_CL" as ([lb y]) "INV" "CLOS".
    rewrite /client_inv_impl. iDestruct "INV" as "(>ST & >Y_AUTH & LIB_MSI)". 
    
    rewrite ewp_unfold /ewp_pre. simpl. rewrite NV.
    iSpecialize ("EWP_LIB" with "PI LIB_MSI").
    rewrite difference_union_distr_l_L.
    rewrite difference_disjoint_L; [| done]. rewrite difference_diag_L union_empty_r_L.
    iMod "EWP_LIB" as "[%NS EWP_LIB]". iModIntro. iSplitL ""; [done| ].
    iIntros (e' σ' efs Hstep).
    iSpecialize ("EWP_LIB" with "[//]").
    iMod "EWP_LIB". do 2 iModIntro. iMod "EWP_LIB". iModIntro.
    iMod "EWP_LIB" as (lb') "(PI & MSI_lib & %TRANS__lib & %RESTR__lib & EWP_LIB & ->)".

    iDestruct (y_model_agree with "Y_AUTH Y1") as "->". 
    pose proof update_client_state as U. simpl in U.
    iPoseProof (U with "[$] [$] [$]") as "LMU"; eauto.
    iMod ("LMU" with "MSI_cl") as (δ') "((FUELS & ST & FREE) & MSI & %TRANS & %RESTR)".
    iExists _. iFrame "PI MSI". 
    do 2 (iApply fupd_frame_l; iSplitR; eauto). iApply fupd_frame_r; iSplitL; eauto.

    destruct (to_val e') eqn:VAL'.
    { rewrite ewp_unfold /ewp_pre /= VAL'. iMod "EWP_LIB".
      iPoseProof ("POST_DIS" with "[$][$]") as "%".
      rewrite !decide_True; auto.  

      iMod ("CLOS" with "[ST Y_AUTH MSI_lib]") as "_".
      { iNext. iExists (_, _). iFrame. }
      iModIntro.
      rewrite ewp_unfold /ewp_pre /= VAL'. iModIntro. iFrame.
      (* Set Printing Implicit. *)
      admit. }

    destruct decide as [DIS' | EN'].
    2: { iMod ("CLOS" with "[ST Y_AUTH MSI_lib]") as "_".
         { iNext. iExists (_, _). iFrame. }
         iModIntro.
         iApply ("IH" with "[//] [$][$][$][$][$]"). }


    (* TODO: is it possible to show the contradiction below in a more general way?*)

    iMod ("CLOS" with "[ST Y_AUTH MSI_lib]") as "_".
    { iNext. iExists (_, _). iFrame. }
    iModIntro. 
    rewrite ewp_unfold /ewp_pre /= VAL'.
    rewrite (ewp_unfold _ _ _ g__cl) /ewp_pre /= VAL'.
    iIntros (σ2 δ__cl2) "PI MSI_cl".
    iInv "INV_CL" as ([lb2 y2]) "INV" "CLOS".
    rewrite /client_inv_impl. iDestruct "INV" as "(>ST & >Y_AUTH & LIB_MSI)".
    rewrite difference_union_distr_l_L.
    rewrite difference_disjoint_L; [| done]. rewrite difference_diag_L union_empty_r_L.
    iSpecialize ("EWP_LIB" with "PI LIB_MSI").
    iMod "EWP_LIB" as "[%NS2 EWP_LIB]". iModIntro. iSplitL ""; [done| ].
    iIntros (? ? ? ?).
    iSpecialize ("EWP_LIB" with "[//]").
    iMod "EWP_LIB". do 2 iModIntro. iMod "EWP_LIB". iModIntro.
    iMod "EWP_LIB" as (lb'') "(PI & MSI_lib & %TRANS__lib' & ? & EWP_LIB & ->)".

    (* TODO: move*)
    iAssert (⌜ ρ_lib ∉ live_roles M__cl (lb2, y2) ⌝)%I as "%DIS2".
    { iDestruct (has_fuel_in' with "[$][$]") as "%". 
      rewrite /msi /model_state_interp. iDestruct "MSI_cl" as (FR) "(?&?&FR&?&%)".
      iDestruct (free_roles_inclusion with "[$][$]") as "%".
      rewrite -ls_same_doms in H2.
      iPoseProof (model_agree with "[$][$]") as "%ST2". 
      iPureIntro. intros LIVE.
      pose proof (ls_mapping_dom δ__cl2). rewrite ST2 in H4.
      specialize (H4 _ LIVE). set_solver. }
    iDestruct (y_model_agree with "Y_AUTH Y1") as "->".  
    exfalso. destruct DIS2. eapply fm_live_spec.
    eapply ct_lib_step; eauto. 
  Admitted. 
    

  (* TODO: why does it require specifying the role? *)
  Ltac pure_step ρ FS indep :=
    try rewrite sub_comp;
    (* iApply (sswp_MU_cwp with "[FUELS] [-]").  *)
    iApply (sswp_MU_ewp _ ρ);
    iApply sswp_pure_step; [done| ]; simpl;
    iNext;
    iApply (LMU_mono with "[-FUELS]");
    [| iApply local_rule_LMU;
       [iApply fuel_keep_step_local_rule; apply cl_impl_lift | 
        iApply bi.sep_assoc; iSplit; [| solve_fuels_S FS]; iPureIntro; split; [| apply indep]; set_solver]];
    iIntros "FUELS".


  (* TODO: rename sets of invariants *)
  Lemma client_spec E (g: fmrole FM__cl) f
    (FB: f >= client_fl)
    (INV: E__lib ∪ ↑Ns ⊆ E)
    (DISJ_INV1: E__lib ## ↑Ns)    
    :
    ⊢ (□ ∀ Φ,
      (partial_model_is (lib_st0, 3) ∗ 
       partial_free_roles_are {[ ρ_lib (ρlg := ρlg); ρ_ext (ρlg := ρlg) ]} ∗
       has_fuels g {[ ρ_cl := f ]}) -∗
      ▷ (∀ y, partial_mapping_is {[ g := ∅ ]} -∗ Φ y) -∗
      EWP (client #()) @ NotStuck ; g ; E {{ v, Φ v }}). 
  Proof using cpG.
    unfold client_fl in *.
    iIntros "!> %Φ (ST & FREE & FUELS) POST". rewrite /client.

    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρ_cl := f]}: gmap (fmrole M__cl) nat) 10) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    pure_step g FS client_LSI_fuel_independent.

    iMod (init_client_inv with "ST") as "[%cg (INV_CL & Y_FRAG & LIB_POST)]".
    iAssert (|={E}=> client_inv)%I with "[INV_CL]" as "INV_CL".
    { rewrite /client_inv. iApply inv_alloc. done. }
    iApply (fupd_ewp _ E). iMod "INV_CL" as "#INV_CL". iModIntro.

    ewp_bind (ref #2)%E.

    (* iApply ewp_atomic. *)
    iApply sswp_MU_ewp_fupd. iInv "INV_CL" as ([lb3 y]) "INV" "CLOS". iModIntro.
    iApply wp_alloc. iNext. iIntros (x) "X _".
    rewrite /client_inv_impl. iDestruct "INV" as "(ST & Y_AUTH & LIB_MSI)".
    iAssert (⌜ y = 3 ⌝)%I as "->".
    { admit. }
    iDestruct (lib_post_dis with "[LIB_MSI LIB_POST]") as "%DIS"; [by iFrame| ].  
    iApply (LMU_mono with "[-FUELS ST FREE]").
    2: { iApply local_rule_LMU.
         { iApply model_step_local_rule. apply cl_impl_lift. }
         iFrame. iPureIntro.
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
    rewrite live_roles_3 live_roles_2. repeat (rewrite decide_True; [| done]).
    iIntros "(FUELS & ST & FREE)".
    iDestruct (frag_free_roles_are_proper {[ ρ_cl; ρ_lib (ρlg := ρlg) ]} with "FREE") as "FREE".
    { set_solver. }
    iAssert (|==> y_auth_model_is 2 ∗ y_frag_model_is 2)%I with "[Y_AUTH Y_FRAG]" as "Y".
    { admit. }
    iMod "Y" as "[Y_AUTH Y_FRAG]". 
    iMod ("CLOS" with "[ST Y_AUTH LIB_MSI]") as "_".
    { iNext. iExists (_, _). iFrame. }
    iModIntro.

    iApply ewp_value.

    clear FS. 
    rewrite (sub_0_id {[ _ := _ ]}).    
    assert (fuels_ge ({[ρ_ext (ρlg := ρlg) := client_fl]}: gmap (fmrole M__cl) nat) 10) as FS.
    { red. rewrite /client_fl. intros ??[<- ?]%lookup_singleton_Some. lia. }
    ewp_bind (Rec _ _ _)%E.
    pure_step g FS client_LSI_fuel_independent.

    iApply ewp_value.

    pure_step g FS client_LSI_fuel_independent.

    ewp_bind (_ <- _)%E.
    iApply sswp_MU_ewp_fupd. iInv "INV_CL" as ([lb2 y]) "INV" "CLOS". iModIntro. 
    iApply (wp_store with "X"). iNext. iIntros "X".
    rewrite /client_inv_impl. iDestruct "INV" as "(ST & Y_AUTH & LIB_MSI)".
    iDestruct (lib_post_dis with "[LIB_MSI LIB_POST]") as "%DIS2"; [by iFrame| ].
    pose proof DIS2 as [lb1 RESET]%lib_reset_dom. 
    assert (ρlg ∈ live_roles libM lb1) as LIVE'.
    { eapply lib_reset_cod. red. eauto. }
    iAssert (⌜ y = 2 ⌝)%I as "->".
    { admit. }
    iApply (LMU_mono with "[-FUELS ST FREE]").
    2: { iApply local_rule_LMU.
         { iApply model_step_local_rule. apply cl_impl_lift. }
         iFrame. iPureIntro.
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
         rewrite (bool_decide_eq_true_2 _ LIVE') (bool_decide_eq_true_2 _ DIS2).
         do 5 (try split).
         1-3, 5-6: set_solver.
         rewrite !dom_singleton_L. 
         intros ? [->%elem_of_singleton ?]%elem_of_difference.
         rewrite lookup_singleton. simpl. done. }
    iIntros "(FUELS & ST & FREE)".
    iDestruct (frag_free_roles_are_proper {[ ρ_cl; ρ_ext (ρlg := ρlg) ]} with "FREE") as "FREE".
    { rewrite live_roles_1 live_roles_2. do 2 (rewrite decide_True; eauto). 
      set_solver. }
    iAssert (|==> y_auth_model_is 1 ∗ y_frag_model_is 1)%I with "[Y_AUTH Y_FRAG]" as "Y".
    { admit. }
    iMod "Y" as "[Y_AUTH Y_FRAG]".
    iMod (lib_reset with "LIB_MSI LIB_POST [//]") as "[LIB_MSI LIB_PRE]".

    iMod ("CLOS" with "[ST Y_AUTH LIB_MSI]") as "_".
    { iNext. iExists (_, _). iFrame. }
    iModIntro. iApply ewp_value.

    clear FS. 
    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρ_lib (ρlg := ρlg) := client_fl]}: gmap (fmrole M__cl) nat) 10) as FS.
    { red. rewrite /client_fl. intros ??[<- ?]%lookup_singleton_Some. lia. }
    ewp_bind (Rec _ _ _)%E.
    pure_step g FS client_LSI_fuel_independent.

    iApply ewp_value.

    pure_step g FS client_LSI_fuel_independent.

    ewp_bind (lib_fun #())%E.
    iDestruct (partial_free_roles_are_sep with "FREE") as "[FREE_cl FREE_ext]".
    { set_solver. }
    iApply (ewp_strong_mono with "[LIB_PRE FUELS FREE_cl Y_FRAG]"). 
    1, 2: reflexivity. 
    { iApply ewp_mask_mono; [apply INV| ].
      iApply (lift_lib_spec with "[][][FUELS][$][$]").
      4: { iIntros (??) "G ?". iApply lib_post_dis. iFrame. iApply "G". }
      5: { rewrite map_fmap_singleton. iFrame. }
      5: { iApply (lib_spec with "[$]"). iNext. iIntros. iFrame. }
      all: auto. lia. }
    simpl. iIntros (v) "(LIB_POST & FUELS & FREE & Y_FRAG)".
    iModIntro.

    clear FS. 
    rewrite (sub_0_id {[ _ := _ ]}).
    assert (fuels_ge ({[ρ_cl := 13]}: gmap (fmrole M__cl) nat) 10) as FS.
    { red. rewrite /client_fl. intros ??[<- ?]%lookup_singleton_Some. lia. }
    ewp_bind (Rec _ _ _)%E.
    pure_step g FS client_LSI_fuel_independent.

    iApply ewp_value.

    pure_step g FS client_LSI_fuel_independent.

    (* TODO: restore proofs below? *)
    
    (* pose proof (live_roles_1 lb) as LIVE1'. *)
    (* (* rewrite !(decide_False, decide_True) in LIVE1'. -- TODO: how to do it in ssr?*) *)
    (* erewrite decide_False, decide_True in LIVE1'; eauto. *)
    (* 2: { apply LM_map_empty_notlive. eauto. } *)
    
    (* pose proof (live_roles_0 lb) as LIVE0. *)
    
    (* iModIntro. *)
    (* iApply (wp_store_step_singlerole_keep with "[$] [L ST FUELS]"). *)
    (* { set_solver. } *)
    (* (* { reflexivity. } *) *)
    (* 6: { iFrame "L ST". iNext. *)
    (*      iApply has_fuel_fuels. rewrite map_fmap_singleton. iFrame. } *)
    (* 2: { by apply ct_y_step_1. } *)
    (* 3: { rewrite LIVE1' LIVE0. set_solver. } *)
    (* { Unshelve. 2: exact 7. simpl. rewrite /client_fl. lia. } *)
    (* { lia. } *)
    (* { red. intros. simpl. red. *)
    (*   intros ? [? MAP]. *)
    (*   apply (ls_mapping_tmap_corr) in MAP as (? & TMAP' & ?). *)
    (*   assert (ρlg = gi) as <- by (by destruct ρlg, gi). *)
    (*   set_solver. } *)

    (* (* rewrite LIVE0. erewrite decide_False; [| set_solver]. *) *)
    (* iNext. iIntros "(L & ST & FUELS)". *)
    (* iMod (y_update_model _ _ 0 with "YST_AUTH YST") as "[YST_AUTH YST]". *)
    
    (* iMod ("CLOS" with "[YST_AUTH ST inv']") as "_". *)
    (* { iNext. iExists (_, _). rewrite /client_inv_impl. iFrame. } *)
    (* iModIntro. *)
    
    (* iDestruct (has_fuel_fuels with "FUELS") as "FUELS". *)
    (* simpl. clear FS. *)
    (* rewrite (sub_0_id {[ ρ_cl := _ ]}). *)
    (* assert (fuels_ge ({[ ρ_cl := 7 ]}: gmap (fmrole client_model_impl) nat) 7) as FS. *)
    (* { red. intros ??[<- ->]%lookup_singleton_Some. lia. } *)

    (* do 2 pure_step FS client_LSI_fuel_independent. *)

    (* iApply wp_atomic. *)
    (* iInv Ns as ((lb'', y)) "inv" "CLOS". rewrite {1}/client_inv_impl. *)
    (* iDestruct "inv" as "(>ST & >YST_AUTH & > inv')". *)
    (* iAssert (⌜ y = 0 ⌝)%I as %->. *)
    (* { iCombine "YST_AUTH YST" as "Y". iDestruct (own_valid with "Y") as %V. *)
    (*   apply auth_both_valid_discrete in V as [EQ%Excl_included _]. done. } *)
    (* iAssert (⌜ ls_tmap lb'' !! ρlg = Some ∅ ⌝)%I as %LIB_END''. *)
    (* { iApply (frag_mapping_same with "[inv'] LM"). *)
    (*   rewrite /model_state_interp. iFrame. *)
    (*   iDestruct "inv'" as (?) "(?&?&_)". iFrame.  } *)
    (* (* Unshelve. 2: exact (⊤ ∖ ↑Ns).  *) *)
    (* iModIntro. *)
    
    (* iApply (wp_lift_pure_step_no_fork_remove_role {[ ρ_cl ]} ((lb'', 0): fmstate client_model_impl) _ _ _ _ _ _ _ (sub 3 <$> {[ρ_cl := 7]}) (iLM := client_model)); eauto. *)
    (* { solve_map_not_empty. } *)
    (* { set_solver. } *)
    (* { rewrite live_roles_0. set_solver. } *)
    (* { red. intros. red. intros. *)
    (*   red in H0. specialize (H0 _ H1). simpl in H1. *)
    (*   destruct H1  as [? IN].  *)
    (*   assert (gi = ρlg) as ->. *)
    (*   { unshelve eapply elem_of_singleton. *)
    (*     { exact (gset lib_grole). } *)
    (*     all: try by apply _.  *)
    (*     apply elem_of_subseteq_singleton. *)
    (*     etrans; [| apply (ls_inv lb'')]. *)
    (*     apply elem_of_subseteq_singleton. *)
    (*     apply ls_mapping_tmap_corr in IN as (?&?&?). *)
    (*     eapply @elem_of_dom; eauto. apply _. } *)
    (*   apply ls_mapping_tmap_corr in IN as (?&?&?). *)
    (*   rewrite LIB_END'' in H1. clear -H2 H1. set_solver. } *)
    (* iFrame "PMP'". do 3 iModIntro. iFrame. *)
    (* iSplitL "FUELS". *)
    (* { solve_fuels_S FS. } *)
    (* iIntros "ST FUELS". *)

    (* simpl. iApply wp_value'. *)
    (* iMod ("CLOS" with "[ST YST_AUTH inv']") as "_". *)
    (* { rewrite /client_inv_impl. iNext. iExists (_, _). iFrame. } *)
    (* iModIntro. iApply "POST". *)
    (* iDestruct (has_fuels_equiv with "FUELS") as "[MAP FUEL]". *)
    (* iApply partial_mapping_is_Proper; [| by iFrame]. *)
    (* f_equiv. rewrite map_fmap_singleton dom_singleton_L. *)
    (* rewrite difference_diag_L. *)
    (* rewrite dom_filter_comm. *)
    (* by rewrite dom_singleton_L filter_singleton_not. *)
    
  Admitted. 
 
End ClientSpec.
