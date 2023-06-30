From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From trillium.fairness.examples.spinlock Require Import spinlock_sc.


Close Scope Z_scope.
 
Opaque spinlock_model_impl.
Opaque spinlock_model.
Opaque program. 
Opaque program_init_fuels.
Opaque spinlock_model_impl. 
Opaque sm_fuel. 

Section LocksCompositionModel.


  Let sl_st := fmstate spinlock_model_impl.
  Let sl_role := fmrole spinlock_model_impl.

  (* TODO: how many 'option's should be there? *)
  Definition comp_state: Type := option sl_st * option sl_st * option nat.

  Inductive c_role := ρc. 
  Definition comp_role: Type := (sl_role + sl_role) + c_role.

  Inductive comp_trans: comp_state -> option comp_role -> comp_state -> Prop :=
  | ct_sl_step_1 s s' ρ os2 oc
      (STEP1: fmtrans spinlock_model_impl s (Some ρ) s'):
    comp_trans (Some s, os2, oc) (Some $ inl $ inl ρ) (Some s', os2, oc)
  | ct_sl_step_2 s s' ρ os1 oc
      (STEP2: fmtrans spinlock_model_impl s (Some ρ) s'):
    comp_trans (os1, Some s, oc) (Some $ inl $ inr ρ) (os1, Some s', oc)
  | cl_c_step os1 os2 c:
    comp_trans (os1, os2, Some (S c)) (Some $ inr ρc) (os1, os2, Some c)
  | cl_sl_init oc s1 s2:
    comp_trans (None, None, oc) (Some $ inr ρc) (Some s1, Some s2, oc)
  .

  Global Instance c_role_EqDec: EqDecision c_role.
  Proof. solve_decision. Defined.

  (* Global Instance comp_role_EqDec: EqDecision comp_role. *)
  (* Proof. solve_decision. Qed. *)

  Global Instance c_role_Cnt: Countable c_role.
  Proof.
    eapply @inj_countable' with (f := fun _ => ()) (g := fun _ => ρc).
    { apply unit_countable. }
    by intros [].
  Defined. 
    
  Global Instance comp_role_Cnt: Countable comp_role.
  Proof using. 
    (* Set Printing All. *)
    rewrite /comp_role.
    apply sum_countable. 
  Defined. 

  
  (* Compute (from_option S 55 None).  *)

  Definition comp_lr (st: comp_state): gset (comp_role) :=
    let get_lr (s: option sl_st) := from_option (live_roles _) ∅ s in 
    match st with 
    | (os1, os2, oc) => set_map (inl ∘ inl) (get_lr os1) ∪
                       set_map (inl ∘ inr) (get_lr os2) ∪
                       if (bool_decide ((os1, os2) = (None, None)) || (0 <? (from_option id 0 oc)))
                       then {[ inr ρc ]} else ∅ 
    end.
                                  

  (* TODO: proven in ticketlock dir *)
  Lemma set_map_compose_gset {A1 A2 A3: Type}
    `{EqDecision A1} `{EqDecision A2} `{EqDecision A3}
    `{Countable A1} `{Countable A2} `{Countable A3}
    (f: A2 -> A3) (g: A1 -> A2) (m: gset A1):
    set_map (f ∘ g) m (D:=gset _) = set_map f (set_map g m (D:= gset _)).
  Proof using. Admitted. 

  Definition comp_model_impl: FairModel.
  Proof.
    refine ({|
        fmstate := comp_state; 
        fmrole := comp_role;
        fmtrans := comp_trans;
        live_roles := comp_lr;
    |}).
    intros ??? TRANS. rewrite /comp_lr. inversion TRANS; subst.
    1: do 2 apply elem_of_union_l. 2: apply elem_of_union_l, elem_of_union_r. 
    1, 2: rewrite set_map_compose_gset; do 2 apply elem_of_map_2;
          eapply fm_live_spec; done. 
    all: apply elem_of_union_r; rewrite orb_true_intro; set_solver. 
  Defined.

  (* TODO: generalize? *)
  Definition comp_model: LiveModel heap_lang comp_model_impl :=
    {| lm_fl _ := max 5 (sm_fuel + 3); |}.  

  (* Definition comp_st_init (n: nat): fmstate comp_model_impl :=  *)
  (*   (None: option sl_st, None: option sl_st, n).  *)

End LocksCompositionModel.


Section LocksCompositionCode.

  (* Definition comp: expr := *)
  (*   let: "l" := newlock #() in *)
  (*   ((Fork (client "l") ) ;; (Fork (client "l") )). *)

  Definition comp: val :=
  λ: <>,
    let: "x" := ref #1 in
    "x" <- #1 ;;
    (Fork (program #()) ;;
     Fork (program #()) ;;
     "x" <- #2).

  Canonical Structure sl_ofe := optionO (leibnizO (fmstate spinlock_model_impl)).
  Canonical Structure cnt_ofe := optionO natO.  
  Definition comp_cmra: ucmra := authUR (prodUR (prodUR (excl' sl_ofe) (excl' sl_ofe)) (excl' cnt_ofe)). 

  Class compPreG Σ := {
      sl1PreG :> spinlockPreG Σ;
      sl2PreG :> spinlockPreG Σ;
      slSplitG :> inG Σ comp_cmra;
  }.
  

End LocksCompositionCode. 



Section LocksCompositionProofs.
  Context `{LM: LiveModel heap_lang Mdl} `{!heapGS Σ LM} {COMP_PRE: compPreG Σ}.
  Context `{PMPP: @PartialModelPredicatesPre _ Mdl _ _ Σ comp_model_impl}.

  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

  Definition comp_st_auth (γ: gname) (st: fmstate comp_model_impl): iProp Σ := 
      own γ ((● (Excl' (fst $ fst st: sl_ofe), Excl' (snd $ fst st: sl_ofe), Excl' (snd st))): comp_cmra).  

  Definition comp_inv_impl (γ: gname) : iProp Σ :=
    ∃ st, partial_model_is st ∗ comp_st_auth γ st. 

  Let Ns := nroot .@ "comp".

  Definition comp_inv (γ: gname) : iProp Σ :=
    inv Ns (comp_inv_impl γ). 

  Definition comp_free_roles_init: gset (fmrole comp_model_impl) :=
    let sl_roles := live_roles _ program_init_state in
    set_map (inl ∘ inl) sl_roles ∪
    set_map (inl ∘ inr) sl_roles.

(*   Print Instances cmra.  *)
(* big_opM op *)
  (* Let foo_big_opM_singletons := gmap.big_opM_singletons (K := fmrole spinlock_model_impl) (A := nat). *)

  (* Lemma rsmi_ofe: Ofe *)

  (* Instance foo: Countable (fmrole spinlock_model_impl). *)
  (* Proof. Admitted.  *)
  (* Canonical Structure rsmiO := *)
  (*   leibnizO (fmrole spinlock_model_impl). *)

  (* Let add_roles: gmap (fmrole spinlock_model_impl) nat := *)
  (*       [^ op map] ρ ↦ f ∈ program_init_fuels, ({[ ρ := f ]}). *)
  (*       (* ([^ op map] k↦x ∈ program_init_fuels, {[k := x]}).  *) *)
  (*       (* big_opM op gmap *)         *)

  (* TODO: exists? *)
  (* Definition gmap_map_keys {A B: Type} (m: gmap A B) *)

  Let prog_fuels (key_lift: fmrole spinlock_model_impl -> fmrole comp_model_impl):
    gmap (fmrole comp_model_impl) nat :=
    (*     list_to_map $ (fun '(k, v) => (key_lift k, v)) <$> map_to_list program_init_fuels. *)
    kmap key_lift program_init_fuels. 

  Lemma prog_fuels_equiv ρ f lift (INJ: Inj eq eq lift):
    (prog_fuels lift) !! (lift ρ) = Some f <-> program_init_fuels !! ρ = Some f.
  Proof using.
    rewrite /prog_fuels. by rewrite lookup_kmap. 
  Qed. 

  Let lift_sl_st_left (s: fmstate spinlock_model_impl): fmstate comp_model_impl := 
        (Some s, None, None). 
  Let lift_sl_role_left (ρ: fmrole spinlock_model_impl): fmrole comp_model_impl := 
        (inl ∘ inl) ρ.
 
  Notation "'has_fuels_' '<' ctx '>'" := (has_fuels (PMPP := ctx)) (at level 20, format "has_fuels_  < ctx >"). 

  Notation "'PMP'" := (@PartialModelPredicates _ _ LM _ _ _ _ _ comp_model PMPP).

  Close Scope Z_scope. 
  Notation "'sub' d" := (fun n => n - d) (at level 10). 

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

  Lemma update_sl1 γ s1 s1' s2 s3:
    own γ (◯ (Excl' s1, ε, ε)) ∗ comp_st_auth γ (s1, s2, s3) ==∗
    own γ (◯ (Excl' s1', ε, ε)) ∗ comp_st_auth γ (s1', s2, s3).
  Proof using. 
    rewrite /comp_st_auth. simpl. iIntros "?".
    iApply own_op. iApply own_update; [| by iApply own_op].
    do 2 rewrite (cmra_comm (◯ _)). apply auth_update.
    do 2 (apply prod_local_update; simpl; try done). 
    apply option_local_update. by apply exclusive_local_update.
  Qed.     

  Lemma update_sl2 γ s2 s2' s1 s3:
    own γ (◯ (ε, Excl' s2, ε)) ∗ comp_st_auth γ (s1, s2, s3) ==∗
    own γ (◯ (ε, Excl' s2', ε)) ∗ comp_st_auth γ (s1, s2', s3).
  Proof using. 
    rewrite /comp_st_auth. simpl. iIntros "?".
    iApply own_op. iApply own_update; [| by iApply own_op].
    do 2 rewrite (cmra_comm (◯ _)). apply auth_update.
    do 2 (apply prod_local_update; simpl; try done). 
    apply option_local_update. by apply exclusive_local_update.
  Qed.

  Lemma valid_fm f d:
    valid_new_fuelmap (sub d <$> {[inr ρc := f]})
    ({[inr ρc := 3]} ∪ ((plus 3) <$> prog_fuels (inl ∘ inl))
     ∪ ((plus 3) <$> prog_fuels (inl ∘ inr))) (None, None, Some 2)
    (Some program_init_state, Some program_init_state, Some 2) 
    (inr ρc) (LM := comp_model).
  Proof.
    red. repeat split; try set_solver. 
    - simpl. intros _.
      erewrite lookup_union_Some_l; try set_solver.
      simpl. lia.
    - intros ρ [IN NIN]%elem_of_difference.
      repeat (rewrite dom_union in IN; apply elem_of_union in IN as [IN|IN]).
      { done. }
      + apply elem_of_dom in IN as [f' IN].          
        erewrite lookup_union_Some_l; [| erewrite lookup_union_Some_r]; eauto.
        * apply lookup_fmap_Some in IN as [? [<- IN]].
          rewrite /prog_fuels in IN.
          apply lookup_kmap_Some in IN as [ρ0 [-> IN]]; [| by apply _].
          apply program_init_fuels_max in IN. simpl. lia. 
        * by apply map_disjoint_singleton_l.
      (* TODO: refactor *)
      + apply elem_of_dom in IN as [f' IN]. simpl. 
        erewrite lookup_union_Some_r; eauto.
        * apply lookup_fmap_Some in IN as [? [<- IN]].
          rewrite /prog_fuels in IN.
          apply lookup_kmap_Some in IN as [ρ0 [-> IN]]; [| by apply _].
          apply program_init_fuels_max in IN. simpl. lia. 
        * apply map_disjoint_union_l. split; [by apply map_disjoint_singleton_l|].
          rewrite -!kmap_fmap. apply map_disjoint_spec.
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

  Lemma comp_spec tid (P: iProp Σ):
    PMP -∗
    {{{ partial_model_is (None, None, Some 2)  ∗ 
        partial_free_roles_are comp_free_roles_init ∗ 
        has_fuels tid {[ inr ρc:=5 ]} (PMPP := PMPP)  }}}
      comp #() @ tid
    {{{ RET #(); tid ↦M ∅ }}}.
  Proof using.
    iIntros "#PMP" (Φ) "!> (ST & FREE & FUELS) POST". rewrite /comp.
    rewrite (sub_0_id {[ _ := _ ]}). 
    (* iDestruct (has_fuels_ge_S_exact with "FUELS") as "FUELS". *)
    (* { compute_done. } *)
    assert (fuels_ge ({[inr ρc := 5]}: gmap (fmrole comp_model_impl) nat) 5) as FS.
    { red. intros ??[<- ->]%lookup_singleton_Some. lia. }

    iMod (own_alloc ((● (Excl' None, Excl' None, Excl' (Some 2)) ⋅ ◯ _))) as (γ) "[AUTH (ST1 & ST2 & STC)]".
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
    2: { solve_fuels_S FS. }
    { set_solver. }
    iNext. iIntros (l) "(L & MT & FUELS) /=". 
    
    pure_step FS. 
    pure_step FS. 

    (* iApply fupd_wp.  *)
    (* iInv Ns as (((ost1, ost2), osc)) "(>ST & >AUTH)". *)
    (* iApply fupd_mono.  *)
    (* iApply fupd_frame_l. iSplit  *)
    
    (* iApply (wp_lift_pure_step_no_fork_take_step); [done| ..]. *)
    (* 3: { eapply (cl_sl_init _ program_init_state program_init_state). } *)
    (* { apply valid_fm. } *)

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
    { eapply (cl_sl_init _ program_init_state program_init_state). }
    { apply valid_fm. }
    2: by apply empty_subseteq.
    2, 3: set_solver.
    2: done.
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
    assert (forall lift, fuels_ge (Init.Nat.add 3 <$> prog_fuels lift) 3) as FS'.
    { intros. intros ??[? [<- ?]]%lookup_fmap_Some. lia. } 
    assert (fuels_ge ({[inr ρc := 3]} ∪ (Init.Nat.add 3 <$> prog_fuels (inl ∘ inl))
               ∪ (Init.Nat.add 3 <$> prog_fuels (inl ∘ inr))) 3) as FS.
    { apply fuels_ge_union; [apply fuels_ge_union| ].
      { red. intros ??[<- ->]%lookup_singleton_Some. lia. }
      all: apply FS'. }
    rewrite (sub_0_id (_ ∪ _ ∪ _)).

    pure_step FS.
    pure_step FS. 

    wp_bind (Fork _).
    iApply (wp_fork_nostep_alt with "[ST1] [] [FUELS]").
    5: { iDestruct (has_fuels_gt_1 with "FUELS") as "F". 
         2: { rewrite -map_fmap_compose. rewrite !map_fmap_union. by iFrame. } 
         solve_fuels_ge_1 FS. }
    { rewrite -map_fmap_union. apply map_disjoint_spec. rewrite /prog_fuels.
      intros ??? [? [<- ?]]%lookup_fmap_Some [? [<- ?]]%lookup_fmap_Some.
      apply lookup_fmap_Some in H0 as [? [<- ?]].
      apply lookup_kmap_Some in H0 as [? [-> ?]]; [| by apply _].
      done. }
    { set_solver. }
    { iSplitR; [done| ]. iIntros (tid') "!# FUELS".   
    { set_solver. }
    { iIntros (tid'). iNext. iIntros "FUELS". simpl.

      clear.
      Set Printing Implicit.
      unshelve iApply program_spec.
      clear. 
      


End LocksCompositionProofs.
