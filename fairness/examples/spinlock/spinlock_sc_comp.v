From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From trillium.fairness.examples.spinlock Require Import spinlock_sc spinlock_sc_comp_model spinlock_sc_comp_pmp.


Close Scope Z_scope.

Opaque spinlock_model_impl.
Opaque spinlock_model.
Opaque program. 
Opaque program_init_fuels.
Opaque spinlock_model_impl. 
Opaque sm_fuel. 

Section LocksCompositionCode.

  Definition comp: val :=
  λ: <>,
    let: "x" := ref #1 in
    "x" <- #1 ;;
    Fork (program #()) ;;
    program #() ;;
    "x" <- #2
  .

End LocksCompositionCode. 



Section LocksCompositionProofs.
  Context `{LM: LiveModel heap_lang M} `{!heapGS Σ LM} {COMP_PRE: compPreG Σ}.
  Context `{PMPP: @PartialModelPredicatesPre _ _ _ Σ comp_model_impl}.

  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).
  
  Let Ns := nroot .@ "comp".

  Definition comp_inv (γ: gname) : iProp Σ :=
    inv Ns (comp_inv_impl γ (PMPP := PMPP)). 

  Definition comp_free_roles_init: gset (fmrole comp_model_impl) :=
    let sl_roles := live_roles _ program_init_state in
    set_map (inl ∘ inl) sl_roles ∪
    set_map (inl ∘ inr) sl_roles.

  Let prog_fuels (key_lift: fmrole spinlock_model_impl -> fmrole comp_model_impl):
    gmap (fmrole comp_model_impl) nat :=
    (*     list_to_map $ (fun '(k, v) => (key_lift k, v)) <$> map_to_list program_init_fuels. *)
    kmap key_lift program_init_fuels. 

  Lemma prog_fuels_equiv ρ f lift (INJ: Inj eq eq lift):
    (prog_fuels lift) !! (lift ρ) = Some f <-> program_init_fuels !! ρ = Some f.
  Proof using.
    rewrite /prog_fuels. by rewrite lookup_kmap. 
  Qed. 

  Close Scope Z_scope. 
  Notation "'sub' d" := (fun n => n - d) (at level 10). 
  Notation "'add' d" := (fun n => n + d) (at level 10). 

  Lemma sub_comp `{Countable K} (fs: gmap K nat) (d1 d2: nat):
    (sub d1 ∘ sub d2) <$> fs = sub (d1 + d2) <$> fs.
  Proof.
    apply leibniz_equiv. apply map_fmap_proper; [| done].
    intros ??->. apply leibniz_equiv_iff.
    rewrite /compose. lia. 
  Qed.

  Lemma sub_0_id `{Countable K} (fs: gmap K nat):
    fs = sub 0 <$> fs.
  Proof.
    rewrite -{1}(map_fmap_id fs).
    apply leibniz_equiv. apply map_fmap_proper; [| done].
    intros ??->. apply leibniz_equiv_iff.
    simpl. lia.
  Qed.

  Ltac solve_fuels_ge_1 FS := 
    intros ?? [? [<- GE]]%lookup_fmap_Some; apply FS in GE; simpl; lia.
  
  Ltac solve_fuels_S FS := 
    iDestruct (has_fuels_gt_1 with "FUELS") as "F";
    [| rewrite -map_fmap_compose; by iFrame];
    solve_fuels_ge_1 FS. 
  
  Ltac pure_step FS :=
    try rewrite sub_comp;
    iApply wp_lift_pure_step_no_fork; auto;
    [| iSplitR; [done| ]; do 3 iModIntro; iSplitL "FUELS"];
    [| solve_fuels_S FS |];
    [by intros ?%fmap_empty_iff| ];
    iIntros "FUELS"; simpl; rewrite sub_comp. 

    
  Lemma valid_fm f d c:
    valid_new_fuelmap (sub d <$> {[inr ρc := f]})
    ({[inr ρc := add_fuel_1 + add_fuel_2 + add_fuel_3]} ∪ ((add add_fuel_1) <$> prog_fuels (inl ∘ inl))
     ∪ ((add (add_fuel_1 + add_fuel_2)) <$> prog_fuels (inl ∘ inr))) (None, None, Some (S c))
    (Some program_init_state, Some program_init_state, Some (S c)) 
    (inr ρc) (LM := comp_model).
  Proof.
    red. repeat split.
    2, 4-6: set_solver. 
    - simpl. intros _.
      erewrite lookup_union_Some_l; try set_solver.
      unfold add_fuel_1, add_fuel_2. simpl. lia. 
    - intros ρ [IN NIN]%elem_of_difference.
      repeat (rewrite dom_union in IN; apply elem_of_union in IN as [IN|IN]).
      { done. }
      + apply elem_of_dom in IN as [f' IN].          
        erewrite lookup_union_Some_l; [| erewrite lookup_union_Some_r]; eauto.
        * apply lookup_fmap_Some in IN as [? [<- IN]].
          rewrite /prog_fuels in IN.
          apply lookup_kmap_Some in IN as [ρ0 [-> IN]]; [| by apply _].
          apply program_init_fuels_max in IN. simpl.
          unfold add_fuel_1, add_fuel_2. lia. 
        * by apply map_disjoint_singleton_l.
      (* TODO: refactor *)
      + apply elem_of_dom in IN as [f' IN]. simpl. 
        erewrite lookup_union_Some_r; eauto.
        * apply lookup_fmap_Some in IN as [? [<- IN]].
          rewrite /prog_fuels in IN.
          apply lookup_kmap_Some in IN as [ρ0 [-> IN]]; [| by apply _].
          apply program_init_fuels_max in IN. simpl.
          unfold add_fuel_1, add_fuel_2. lia. 
        * apply map_disjoint_union_l. split; [by apply map_disjoint_singleton_l|].
          rewrite -!kmap_fmap. apply map_disjoint_spec.
          intros ??? [? [-> ?]]%lookup_kmap_Some [? [? ?]]%lookup_kmap_Some.
          2, 3: by apply _.
          discriminate.
  Qed.
    
  Lemma valid_fm' f d:
    valid_new_fuelmap (sub d <$> {[inr ρc := f]})
    (((add add_fuel_1) <$> prog_fuels (inl ∘ inl)) ∪
      ((add (add_fuel_1 + add_fuel_2)) <$> prog_fuels (inl ∘ inr))) (None, None, Some 0)
    (Some program_init_state, Some program_init_state, Some 0)
    (inr ρc) (LM := comp_model).
  Proof.
    red. repeat split.
    all: try set_solver.
    intros ρ [IN NIN]%elem_of_difference.
    repeat (rewrite dom_union in IN; apply elem_of_union in IN as [IN|IN]).
    + apply elem_of_dom in IN as [f' IN].
      erewrite lookup_union_Some_l; eauto.
      apply lookup_fmap_Some in IN as [? [<- IN]].
      rewrite /prog_fuels in IN.
      apply lookup_kmap_Some in IN as [ρ0 [-> IN]]; [| by apply _].
      apply program_init_fuels_max in IN. simpl.
      unfold add_fuel_1, add_fuel_2. lia.
    (* TODO: refactor *)
    + apply elem_of_dom in IN as [f' IN]. simpl.
      erewrite lookup_union_Some_r; eauto.
      * apply lookup_fmap_Some in IN as [? [<- IN]].
        rewrite /prog_fuels in IN.
        apply lookup_kmap_Some in IN as [ρ0 [-> IN]]; [| by apply _].
        apply program_init_fuels_max in IN. simpl.
        unfold add_fuel_1, add_fuel_2. lia.
      * rewrite -!kmap_fmap. apply map_disjoint_spec.
        intros ??? [? [-> ?]]%lookup_kmap_Some [? [? ?]]%lookup_kmap_Some.
        2, 3: by apply _.
        discriminate.
  Qed.
    

  (* TODO: move to resources.v *)
  Notation "'iM'" := comp_model_impl. 
  Lemma fuels_ge_union_l (fs1 fs2: gmap (fmrole iM) nat) b
    (GE: fuels_ge (fs1 ∪ fs2) b) (DISJ: fs1 ##ₘ fs2):
    fuels_ge fs1 b.
  Proof. 
    intros ???. eapply GE. erewrite lookup_union_Some_l; eauto. 
  Qed.  
  
  (* TODO: move to resources.v *)
  Lemma fuels_ge_union_r (fs1 fs2: gmap (fmrole iM) nat) b
    (GE: fuels_ge (fs1 ∪ fs2) b) (DISJ: fs1 ##ₘ fs2):
    fuels_ge fs2 b.
  Proof. 
    intros ???. eapply GE. erewrite lookup_union_Some_r; eauto. 
  Qed.  

  Lemma fuels_ge_union (fs1 fs2: gmap (fmrole iM) nat) b
    (GE1: fuels_ge fs1 b) (GE2: fuels_ge fs2 b):
    fuels_ge (fs1 ∪ fs2) b.
  Proof using. 
    red. intros ??[?|[_?]]%lookup_union_Some_raw; [by eapply GE1| by eapply GE2].
  Qed.

  Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (LM := LM) (iLM := comp_model) (PMPP := PMPP))).


  Let lift_sl_role_right (ρ: sl_role): comp_role := (inl ∘ inr) ρ.

  (* TODO: replace call2_inv_impl with this *)
  Definition call2_inv_impl'
    (γ_τρs γ_fs: gname)
    (τ: locale heap_lang) (ρ__next: comp_role):
    iProp Σ :=
    ∃ (R__cur: gset sl_role) (F: gmap sl_role nat),
      let R__cur' := set_map lift_sl_role_right R__cur in
      auth_τ_roles_are γ_τρs R__cur ∗
      auth_call_fuel_is γ_fs F ∗ 
      ([∗ map] ρ ↦ f ∈ F, lift_sl_role_right ρ ↦F f) ∗
      ⌜ dom F = R__cur ⌝ ∗ (
        (∃ (R__next1 R__next2: gset (comp_role)) (f__next: nat),
          partial_mapping_is {[ τ := R__cur' ∪ R__next1]} ∗
          partial_free_roles_are R__next2  ∗
          ⌜ R__next1 ∪ R__next2 = {[ ρ__next ]} ⌝ ∗
          (⌜if (decide (ρ__next ∈ R__next1)) 
            then (forall ρ f, F !! ρ = Some f -> f <= f__next)
            else sm_fuel <= f__next ⌝) ∗
          ρ__next ↦F f__next)
          ∨
          frag_τ_roles_are γ_τρs R__cur). 

  (* Lemma dom_set_map_kmap *)
  (*   (fs: gmap comp_role nat) *)
  (*   (lift: sl_role -> comp_role) *)
  (*   (INJ: Inj eq eq lift) *)
  (*   (DOM: dom  *)


  Lemma alloc_call2_inv τ
    (* (F: gmap comp_role nat) *)
    (F': gmap sl_role nat) (f_next: nat) (FUELnext: sm_fuel <= f_next)
    (* (DOM: exists (D: gset sl_role), dom F = set_map lift_sl_role_right D ∪ ({[ inr ρc ]}: gset comp_role)) *)
    (* (NEXT: exists f, F !! inr ρc = Some f /\ sm_fuel <= f) *)
    :
    let F := kmap lift_sl_role_right F' ∪ {[ inr ρc := f_next ]} in
    forall E, ⊢ (has_fuels τ F ={E}=∗ 
           ∃ γ_τρs γ_fs, inv (nroot .@ "call2") (call2_inv_impl' γ_τρs γ_fs τ (inr ρc)) ∗
           frag_call_fuel_is γ_fs F' ∗
           frag_τ_roles_are γ_τρs (dom F'))%I.
  Proof.
    intros. 
    iMod (own_alloc (_: τ_roles_cmra)) as (γ_τρs) "[AUTH1 FRAG1]".
    { apply auth_both_valid_2; [| reflexivity].
      Unshelve. 2: exact (Some (Excl (gset.GSet (dom F')))). done. }
    
    iMod (own_alloc (_: call_fuels_cmra)) as (γ_fs) "[AUTH2 FRAG2]".
    { apply auth_both_valid_2; [| reflexivity].
      Unshelve. 2: exact (Excl <$> F'). 
      admit. }
    iIntros "[ROLES FUEL]".
    iMod partial_free_roles_empty as "FR". 
    iMod (inv_alloc (nroot .@ "call2") _ (call2_inv_impl' γ_τρs γ_fs τ (inr ρc)) with "[AUTH1 AUTH2 ROLES FUEL FR]") as "INV".
    { iNext. rewrite /call2_inv_impl'.
      subst F. rewrite dom_union_L.
      iDestruct (big_sepS_union with "FUEL") as "[FUEL_D FUEL_NEXT]".
      { rewrite dom_kmap. set_solver. }
      do 2 iExists _.
      iFrame. iApply bi.sep_assoc. iSplitL "FUEL_D".
      - iSplitL.
        2: { iPureIntro. subst. set_solver. }
        subst. iDestruct (big_sepM_dom with "FUEL_D") as "FUEL".
        rewrite big_opM_kmap.
        iApply big_opM_proper; [..| by iFrame].
        intros. iStartProof.
        erewrite lookup_union_Some_l.
        2: { by rewrite lookup_kmap. }
        iSplit.
        + iIntros. iExists _. by iFrame.
        + iIntros "[% [%EQ ?]]". by inversion EQ.
      - subst. 
        (* apply dom_singleton_inv_L in DOM2 as [? ->]. *)
        (* apply lookup_singleton_Some in NEXT as [_ ->].
        rewrite dom_singleton_L. *)
        iLeft. do 3 iExists _. rewrite dom_kmap. iFrame.
        iSplitR.
        + iPureIntro. set_solver.
        + erewrite decide_True; [| set_solver].
          rewrite dom_singleton_L big_opS_singleton.
          erewrite lookup_union_r. 
          2: { apply lookup_kmap_None; [apply _| ]. set_solver. }
          iDestruct "FUEL_NEXT" as (?) "[%EQ ?]".
          apply lookup_singleton_Some in EQ as [_ ->]. iFrame.
          iPureIntro. intros.
          assert (f0 <= sm_fuel) by admit.
          lia. }
    iModIntro. do 2 iExists _. iFrame.
  Admitted. 

  Lemma comp_spec tid Einvs
    (* TODO: get rid of these restrictions *)
    (DISJ_INV1: Einvs ## ↑Ns) (DISJ_INV2: Einvs ## ↑nroot.@"spinlock"):
    PMP Einvs -∗
    {{{ partial_model_is (None, None, Some 1)  ∗ 
        partial_free_roles_are comp_free_roles_init ∗ 
        has_fuels tid {[ inr ρc:=5 ]} (PMPP := PMPP)  }}}
      comp #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using COMP_PRE.
    iIntros "#PMP" (Φ) "!> (ST & FREE & FUELS) POST". rewrite /comp.
    rewrite (sub_0_id {[ _ := _ ]}). 
    (* iDestruct (has_fuels_ge_S_exact with "FUELS") as "FUELS". *)
    (* { compute_done. } *)
    assert (fuels_ge ({[inr ρc := 5]}: gmap (fmrole comp_model_impl) nat) 5) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    iMod (own_alloc ((● (Excl' None, Excl' None, Excl' (Some 1)) ⋅ ◯ _))) as (γ) "[AUTH (ST1 & ST2 & STC)]".
    { apply auth_both_valid_discrete. split; [| done].
      rewrite cmra_assoc pair_split_L. apply cmra_mono; [| reflexivity].
      rewrite (pair_split_L _ (Excl' None)). by rewrite pair_op_1. }

    iApply fupd_wp. 
    iMod (inv_alloc Ns _  (comp_inv_impl γ) with "[ST AUTH]") as "#COMP".
    { iNext. rewrite /comp_inv_impl /comp_st_auth.
      iExists _. iFrame. by simpl. }
    iModIntro.

    pure_step FS. 

    wp_bind (ref #1)%E.
    iApply (wp_alloc_nostep with "[$] [FUELS]").
    2: set_solver. 
    2: { solve_fuels_S FS. }
    { set_solver. }
    iNext. iIntros (l) "(L & MT & FUELS) /=". 
    
    pure_step FS. 
    pure_step FS. 

    wp_bind (_ <- _)%E.
    iApply wp_atomic. 
    iInv Ns as (((ost1, ost2), osc)) "(>ST & >AUTH)" "CLOS".
    
    iAssert (⌜ _ ⌝)%I with "[ST1 ST2 STC AUTH]" as "%EQ".
    { iCombine "ST1 ST2 STC" as "ST".
      rewrite !ucmra_unit_right_id_L !ucmra_unit_left_id_L.
      rewrite /comp_st_auth. simpl.
      iCombine "AUTH ST" as "OWN". iDestruct (own_valid with "OWN") as %[INCL ?]%auth_both_valid_discrete.
      iPureIntro. 
      apply pair_included in INCL as [[??]%pair_included ?].
      apply Excl_included, leibniz_equiv_iff in H0, H1, H2.
      exact (conj (conj H0 H1) H2). }
    destruct EQ as [[<- <-] <-].

    iModIntro. 
    iApply (wp_store_step_keep _ _ _ _ _ _ _ _ _  with "[] [L ST FUELS FREE]").
    8: by iFrame.
    { set_solver. }
    { eapply (cl_sl_init _ program_init_state program_init_state). }
    { apply valid_fm. }
    2: by apply empty_subseteq.
    2, 3: set_solver.
    2: { iFrame. }
    { set_solver. }
    
    iNext. iIntros "(L & ST & FUELS & FR)".
    iDestruct (partial_free_roles_are_Proper with "FR") as "FR".
    { Unshelve. 2: exact ∅.
      simpl. rewrite /comp_free_roles_init. set_solver. }

    iMod (update_sl1 _ _ (Some program_init_state) with "[ST1 AUTH]") as "[ST1 AUTH]"; [by iFrame| ].
    iMod (update_sl2 _ _ (Some program_init_state) with "[ST2 AUTH]") as "[ST2 AUTH]"; [by iFrame| ].
    
    iMod ("CLOS" with "[ST AUTH]") as "_".
    { iNext. rewrite /comp_inv_impl. iExists _. iFrame. }
    iModIntro. 

    clear FS. 
    assert (fuels_ge ({[inr ρc := add_fuel_1 + add_fuel_2 + add_fuel_3]}
               ∪ (Init.Nat.add add_fuel_1 <$> prog_fuels (inl ∘ inl))
               ∪ (Init.Nat.add (add_fuel_1 + add_fuel_2) <$>
                  prog_fuels (inl ∘ inr))) add_fuel_1) as FS.
    { repeat apply fuels_ge_union.
      (* all: intros ?? [? [<- ?]]%lookup_fmap_Some; lia. *)
      all: admit. 
    }
    rewrite (sub_0_id (_ ∪ _)).

    unfold add_fuel_1 in *. 
    pure_step FS.
    pure_step FS. 

    Ltac solve_disjoint :=
      apply map_disjoint_spec; rewrite /prog_fuels; intros ??? IN1 IN2;
      repeat (apply lookup_fmap_Some in IN1 as [? [<- IN1]]);
      repeat (apply lookup_fmap_Some in IN2 as [? [<- IN2]]);
      try (apply lookup_singleton_Some in IN1 as [<- <-]);
      try (apply lookup_singleton_Some in IN2 as [<- <-]);
      try (apply lookup_kmap_Some in IN1 as [? [-> ?]]; [| by apply _]);
      try (apply lookup_kmap_Some in IN2 as [? [? ?]]; [| by apply _]);
      done.

    wp_bind (Fork _).
    iApply (wp_fork_nostep_alt with "[ST1] [ST2 STC POST] [FUELS]").
    4: iSplitR; [done| ].
    3: set_solver. 
    5: { 
         iDestruct (has_fuels_gt_1 with "FUELS") as "F". 
         2: { rewrite -map_fmap_compose. rewrite !map_fmap_union.
              rewrite map_union_comm.
              2: { apply map_disjoint_union_l. split; solve_disjoint. }
              rewrite map_union_assoc.
              by iFrame. } 
         solve_fuels_ge_1 FS. }
    { apply map_disjoint_union_l. split; solve_disjoint. }
    { set_solver. }
    { iIntros (tid') "!# FUELS".
      iMod (partial_free_roles_empty) as "FR". 
      iApply (program_spec with "[] [ST1 FUELS FR]"). 
      2: { iApply sl1_PMP; eauto. }
      { apply disjoint_union_l. split; [set_solver| ].
        by apply ndot_ne_disjoint. }
      2: { iNext. iIntros.
           simpl. by rewrite map_fmap_singleton set_map_empty. }
      iFrame. iSplitL "FR". 
      { simpl. by rewrite set_map_empty. }
      Unshelve. 2: exact (⌜ True ⌝)%I. iSplitR; [done| ].
      iApply has_fuels_sl1. iApply has_fuels_proper; [reflexivity| | by iFrame].
      rewrite -map_fmap_compose. erewrite map_fmap_equiv_ext.
      2: { intros. simpl. transitivity x; [apply leibniz_equiv_iff; lia| ].
           reflexivity. }
      rewrite map_fmap_id. done. }

    iNext. iIntros "FUELS". iModIntro.

    clear FS. 
    rewrite /add_fuel_2. rewrite -map_fmap_union.

    replace (add 6) with (add 5) by admit. 
    assert (6 + add_fuel_3 = add 5 sm_fuel).
    { admit. }
    simpl in H. rewrite H. clear H. 
 
    assert (fuels_ge ((add 5 <$> prog_fuels (inl ∘ inr)) ∪ {[inr ρc := add 5 sm_fuel]}) 5) as FS.
    (* { all: intros ?? [? [<- ?]]%lookup_fmap_Some; lia. } *)
    { admit. }

    pure_step FS.
    pure_step FS.
    
    iMod (partial_free_roles_empty) as "FR".

    iApply fupd_wp. 
    iMod (alloc_call2_inv with "[FUELS]") as (??) "(#INV2 & FUELS & ROLES)".
    2: { iApply has_fuels_proper; [..| by iFrame]; [reflexivity| ].
         rewrite !map_fmap_union. rewrite map_fmap_singleton.
         apply fin_maps.union_proper; [| reflexivity].
         rewrite /prog_fuels. rewrite -!kmap_fmap.
         f_equal. }
    { lia. }
    rewrite !dom_fmap_L. 
    iModIntro. 

    wp_bind (program _). iApply (program_spec_fr with "[] [ST2 FUELS ROLES FR]").
    2: { iApply sl2_call_PMP.
         { apply DISJ_INV1. }
         replace call2_inv_impl' with call2_inv_impl by admit.
         iSplit; done. }
    { repeat (apply disjoint_union_l; split); eauto.
      all: by apply ndot_ne_disjoint. }
    { iFrame. iSplitL "FR". 
      { simpl. by rewrite set_map_empty. }
      Unshelve. 2: exact (⌜ True ⌝)%I. iSplitR; [done| ].
      (* TODO: extract lemma *)
      rewrite /has_fuels. iSplitL "ROLES"; simpl.
      - iApply big_sepM_singleton. rewrite decide_True; done. 
      - rewrite /frag_call_fuel_is.
        rewrite -!map_fmap_compose.
        rewrite -(gmap.big_opM_singletons (_ <$> _)).
        rewrite big_opM_auth_frag. rewrite big_opM_fmap. 
        iDestruct (big_opM_own with "FUELS") as "FUELS".
        { set_solver. }
        iApply big_sepM_dom. iApply big_sepM_proper; [| by iFrame].
        iIntros. simpl. rewrite Nat.add_sub. iSplit. 
        + iIntros "[% [% ?]]". assert (x = f) as -> by congruence.
          rewrite map_fmap_singleton. iFrame.
        + iIntros. iExists _. iSplit; eauto. by rewrite map_fmap_singleton. }

    iNext. iIntros "[ROLES FR] //=".
    rewrite big_opM_singleton decide_True; [| done].

    iApply fupd_wp.
    iInv "INV2" as ">INV2_IMPL" "CLOS". rewrite {2}/call2_inv_impl'.
    iDestruct "INV2_IMPL" as (??) "(AUTHc & FUELc & FUELS & <- & DIS)".
    iDestruct "DIS" as "[DIS| ROLES']".
    2: { 
         (* TODO: make a lemma *)
         rewrite /frag_τ_roles_are.
         iCombine "ROLES ROLES'" as "C".
         iDestruct (own_valid with "C") as "%V".
         by apply auth_frag_valid_1 in V. }
    iDestruct "DIS" as (?? f_next) "(ROLE & FR' & %R_NEXT & %F_NEXT & F_NEXT)".
    iAssert (⌜ F = ∅ ⌝)%I as %->.
    { iCombine "AUTHc ROLES" as "R". 
      iDestruct (own_valid with "R") as "%V".
      apply auth_both_valid_discrete in V as [LE _].
      apply @Excl_included, gset.GSet_inj in LE. 
      iPureIntro. apply dom_empty_inv. set_solver. }
    rewrite {2}dom_empty set_map_empty union_empty_l.
      
    
    2: { iNext. iIntros.
         simpl. by rewrite map_fmap_singleton set_map_empty. }
    iApply has_fuels_sl2. iApply has_fuels_proper; [reflexivity| | by iFrame].
    rewrite -!map_fmap_compose. erewrite map_fmap_equiv_ext.
    2: { intros. simpl. rewrite Nat.sub_0_r. reflexivity. }
    rewrite map_fmap_id. done. }
    
    iNext. iIntros "FUELS". iModIntro.
    iApply "POST". iDestruct "FUELS" as "[??]". 
    by rewrite fmap_empty dom_empty_L.
  Qed. 


End LocksCompositionProofs.


