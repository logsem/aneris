From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From trillium.fairness.examples.spinlock Require Import spinlock_sc spinlock_sc_comp_model.


Opaque spinlock_model_impl.
Opaque spinlock_model.
Opaque program. 
Opaque program_init_fuels.
Opaque spinlock_model_impl. 
Opaque sm_fuel. 

Canonical Structure sl_ofe := optionO (leibnizO (fmstate spinlock_model_impl)).
Canonical Structure cnt_ofe := optionO natO.  
Definition comp_cmra: ucmra := authUR (prodUR (prodUR (excl' sl_ofe) (excl' sl_ofe)) (excl' cnt_ofe)). 

Class compPreG Σ := {
    sl1PreG :> spinlockPreG Σ;
    sl2PreG :> spinlockPreG Σ;
    slSplitG :> inG Σ comp_cmra;
}.


Section SlPMP.
  Context `{LM: LiveModel heap_lang M} `{!heapGS Σ LM} {COMP_PRE: compPreG Σ}.
  Context `{PMPP: @PartialModelPredicatesPre _ _ _ Σ comp_model_impl}.

  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

  Definition comp_st_auth (γ: gname) (st: fmstate comp_model_impl): iProp Σ := 
      own γ ((● (Excl' (fst $ fst st: sl_ofe), Excl' (snd $ fst st: sl_ofe), Excl' (snd st))): comp_cmra).  

  Definition comp_sl1_st_frag (γ: gname) (st: fmstate spinlock_model_impl): iProp Σ := 
      own γ ((◯ (Excl' (Some st: sl_ofe), ε, ε)): comp_cmra).  

  Definition comp_sl2_st_frag (γ: gname) (st: fmstate spinlock_model_impl): iProp Σ := 
      own γ ((◯ (ε, Excl' (Some st: sl_ofe), ε)): comp_cmra).  

  Let lift_sl_role_left (ρ: fmrole spinlock_model_impl): fmrole comp_model_impl := 
        (inl ∘ inl) ρ.
  Let lift_sl_role_right (ρ: fmrole spinlock_model_impl): fmrole comp_model_impl := 
        (inl ∘ inr) ρ.
 
  Definition comp_inv_impl (γ: gname) : iProp Σ :=
    ∃ st, partial_model_is st ∗ comp_st_auth γ st. 

  Let Ns := nroot .@ "comp".

  Definition comp_inv (γ: gname) : iProp Σ :=
    inv Ns (comp_inv_impl γ). 

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

  (* Notation "'PartialModelPredicates_' '<' ctx '>'" := (@PartialModelPredicates _ _ LM _ _ _ _ _ spinlock_model PMPP). *)

  (* @PartialModelPredicates heap_lang M LM Nat.eq_dec nat_countable Σ *)
  (*   (@heap_fairnessGS Σ M LM heapGS0) spinlock_model_impl spinlock_model  *)
  (*   ?PMPP *)

  (* Lemma set_map_disjoint  *)
  (*   `{Elements A C, Singleton B D, Empty D, Union D} *)
  (*   `{ElemOf A C} `{ElemOf B D} *)
  (*   `{Singleton B D} *)
  (*   (s1 s2: C) (f: A -> B) *)
  (*   (DISJ: s1 ## s2): *)
  (*   (set_map f s1: D) ## (set_map f s2: D). *)
  (* TODO: generalize, upstream *)
  (* TODO: one-directional version that doesn't require Inj *)
  Lemma set_map_disjoint {A B: Type} `{Countable A} `{Countable B}
    (s1 s2: gset A) (f: A -> B)
    (INJ: Inj eq eq f):
    s1 ## s2 <-> (set_map f s1: gset B) ## (set_map f s2: gset B). 
  Proof using. set_solver. Qed. 

  Definition sl1_PMPP (γ: gname):
    @PartialModelPredicatesPre heap_lang _ _ Σ spinlock_model_impl.
  refine
    {|
        partial_model_is := comp_sl1_st_frag γ;
        partial_free_roles_are := partial_free_roles_are ∘ set_map lift_sl_role_left;
        partial_fuel_is := partial_fuel_is ∘ kmap lift_sl_role_left;
        partial_mapping_is := partial_mapping_is ∘ (fmap (set_map lift_sl_role_left));
    |}.
  - intros. simpl. rewrite kmap_union. apply PMPP. 
    apply map_disjoint_kmap; auto. apply _.
  - intros. simpl. rewrite set_map_union. apply PMPP. set_solver.
  - iIntros. simpl. rewrite set_map_empty. iStopProof. apply PMPP. 
  Defined.

  (* TODO: is there a way to unify these definitions
     and subsequent proofs for them? *)
  Definition sl2_PMPP (γ: gname):
    @PartialModelPredicatesPre heap_lang _ _ Σ spinlock_model_impl.
  refine
    {|
        partial_model_is := comp_sl2_st_frag γ;
        partial_free_roles_are := partial_free_roles_are ∘ set_map lift_sl_role_right;
        partial_fuel_is := partial_fuel_is ∘ kmap lift_sl_role_right;
        partial_mapping_is := partial_mapping_is ∘ (fmap (set_map lift_sl_role_right));
    |}.
  - intros. simpl. rewrite kmap_union. apply PMPP. 
    apply map_disjoint_kmap; auto. apply _.
  - intros. simpl. rewrite set_map_union. apply PMPP. set_solver.
  - iIntros. simpl. rewrite set_map_empty. iStopProof. apply PMPP. 
  Defined.


  (* TODO: move to upstream *)
  Lemma big_opM_kmap {M_ : ofe} {o : M_ → M_ → M_}
    {Monoid0 : Monoid o}
    {K1 K2 : Type}
    (PO: Proper (equiv ==> equiv ==> equiv) o) (* TODO: problem with notation *)
    `{EqDecision K1} `{Countable K1} `{EqDecision K2} `{Countable K2} {A: Type} 
    (h : K1 → K2) {INJ: Inj eq eq h} (f : K2 → A → M_) (m : gmap K1 A):
  ([^ o map] k↦y ∈ (kmap h m), f k y) ≡ ([^ o map] k↦y ∈ m, f (h k) y).
  (* ([^ o map] k↦y ∈ (kmap h m), f k y) = ([^ o map] k↦y ∈ m, f (h k) y).  *)
  Proof.
    pattern m. apply map_ind.
    { simpl. rewrite kmap_empty. simpl. by rewrite !big_opM_empty. }
    intros. erewrite big_opM_insert; auto.
    etrans.
    { eapply big_opM_proper_2.
      { rewrite insert_union_singleton_l kmap_union kmap_singleton.
        (* reflexivity.  *)
        apply leibniz_equiv_iff. reflexivity. }
      intros. rewrite H5. reflexivity. }
    rewrite big_opM_union.
    2: { apply map_disjoint_singleton_l_2. by rewrite lookup_kmap. }
    rewrite H2. 
    f_equiv. by rewrite big_opM_singleton. 
  Qed. 

  (* TODO: move to upstream *)
  Lemma big_opS_kmap {M_ : ofe} {o : M_ → M_ → M_}
    {Monoid0 : Monoid o}
    {K1 K2 : Type}
    (PO: Proper (equiv ==> equiv ==> equiv) o) (* TODO: problem with notation *)
    `{Countable K1} `{Countable K2} 
    (h : K1 → K2) {INJ: Inj eq eq h} (f : K2 → M_) (m : gset K1):
  ([^ o set] k ∈ (set_map h m), f k) ≡ ([^ o set] k ∈ m, f (h k)).
  Proof.
    pattern m. apply set_ind.
    { solve_proper. }
    { rewrite set_map_empty. by rewrite !big_opS_empty. } 

    intros. erewrite big_opS_insert; auto.
    (* TODO: refactor *)
    etrans.
    { etrans. 
      { eapply big_opS_proper'; [reflexivity| ].
        by rewrite set_map_union_L set_map_singleton_L. }
      rewrite big_opS_union; [| set_solver].
      rewrite big_opS_singleton. reflexivity. }
    by rewrite H2. 
  Qed.

  Lemma has_fuels_sl1 tid γ (fs: gmap (fmrole spinlock_model_impl) nat):
        has_fuels tid fs (PMPP := sl1_PMPP γ) ⊣⊢
    has_fuels tid (kmap lift_sl_role_left fs) (PMPP := PMPP).
  Proof using. 
    rewrite /has_fuels. iApply bi.sep_proper.
    - simpl. rewrite map_fmap_singleton. by rewrite dom_kmap.
    - simpl. rewrite dom_kmap_L. rewrite big_opS_kmap.
      apply big_opS_proper. intros. apply bi.exist_proper. 
      red. intros. rewrite kmap_singleton lookup_kmap. done.
  Qed.  

  Lemma has_fuels_sl2 tid γ (fs: gmap (fmrole spinlock_model_impl) nat):
        has_fuels tid fs (PMPP := sl2_PMPP γ) ⊣⊢
    has_fuels tid (kmap lift_sl_role_right fs) (PMPP := PMPP).
  Proof using. 
    rewrite /has_fuels. iApply bi.sep_proper.
    - simpl. rewrite map_fmap_singleton. by rewrite dom_kmap.
    - simpl. rewrite dom_kmap_L. rewrite big_opS_kmap.
      apply big_opS_proper. intros. apply bi.exist_proper. 
      red. intros. rewrite kmap_singleton lookup_kmap. done.
  Qed.  


  (* TODO: generalize, upstream *)
  Lemma set_map_difference {A B:Type} `{Countable A} `{Countable B}
    (f : A → B) (X Y : gset A)
    (INJ: Inj eq eq f):
      (set_map f (X ∖ Y): gset B) ≡ set_map f X ∖ set_map f Y.
  Proof using.
    simpl. split; [| set_solver]. 
    intros [? [[=->] [? ?]%elem_of_difference]]%elem_of_map_1.
    apply elem_of_difference. split; [set_solver| ].
    intros [? [EQ ?]]%elem_of_map_1. set_solver.
  Qed. 

  Ltac role_cases_ext :=
    intros [[IN | IN]%elem_of_union | ?osc]%elem_of_union;
    [.. | (destruct osc as [?n| ]; [destruct n| ]; simpl; set_solver)];
    try (apply elem_of_map in IN as [? [[=->] IN]]). 

  Lemma vfm_sl1 fs1 fs2 s1 s2 ρ ost2 osc
    (VFM: valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := spinlock_model)):
  valid_new_fuelmap (kmap lift_sl_role_left fs1) (kmap lift_sl_role_left fs2)
    (Some s1, ost2, osc) (Some s2, ost2, osc) (inl (inl ρ)) (LM := comp_model).
  Proof using.
    replace (inl (inl ρ)) with (lift_sl_role_left ρ); [| done]. 
    (* destruct VFM.  *)
    repeat (split; simpl).
    - role_cases_ext.  
      apply VFM in IN.
      rewrite lookup_kmap. pose proof (sm_fuel_max s2). 
      destruct (fs2 !! x); [simpl in *; lia | done].
    - intros. rewrite !lookup_kmap.
      apply (proj1 (proj2 VFM)).
      { set_solver. }
      rewrite !dom_kmap in H0. 
      apply elem_of_intersection in H0 as [[? [[=->] ?]]%elem_of_map_1 [? [[=->] ?]]%elem_of_map_1].
      set_solver.
    - rewrite dom_kmap. apply elem_of_map_2.
      apply VFM.
    - intros ? [IN2 NIN1]%elem_of_difference.
      rewrite dom_kmap in IN2. apply elem_of_map_1 in IN2 as [? [[=->] ?]].
      rewrite lookup_kmap.
      do 3 apply proj2 in VFM. apply proj1 in VFM.
      assert (x ∈ dom fs2 ∖ dom fs1) as X. 
      { apply elem_of_difference. split; auto.
        intros ?. apply NIN1. rewrite dom_kmap. set_solver. }
      specialize (VFM x X).
      pose proof (sm_fuel_max s2).
      destruct (fs2 !! x); [simpl in *; lia | done].
    - intros ?? IN. rewrite !dom_kmap in IN. 
      apply elem_of_intersection in IN as [[? [[=->] ?]]%elem_of_map_1 [? [[=->] ?]]%elem_of_map_1].
      rewrite !lookup_kmap. apply VFM; auto. set_solver.
    - simpl. do 5 apply proj2 in VFM. apply proj1 in VFM.
      apply union_subseteq. rewrite !dom_kmap. set_solver.
    - do 6 apply proj2 in VFM. rewrite !dom_kmap.
      apply elem_of_subseteq. intros ? [? [[=->] ?]]%elem_of_map_1.
      specialize (VFM x0 H0). apply elem_of_union in VFM as [[[? | ?]%elem_of_union | ?]%elem_of_union | ?].
      + repeat (apply elem_of_union; left). apply elem_of_difference. split.
        * set_solver.
        * role_cases_ext. set_solver. 
      + set_solver.
      + apply elem_of_union; left. apply elem_of_union; right.
        apply elem_of_difference. split; [set_solver| ].
        role_cases_ext. set_solver.
      + apply elem_of_union; right.
        apply elem_of_intersection. split; [| set_solver].
        apply elem_of_difference. split; [set_solver| ].
        role_cases_ext. set_solver. 
  Qed.

  Lemma vfm_sl2 fs1 fs2 s1 s2 ρ ost1 osc
    (VFM: valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := spinlock_model)):
  valid_new_fuelmap (kmap lift_sl_role_right fs1) (kmap lift_sl_role_right fs2)
    (ost1, Some s1, osc) (ost1, Some s2, osc) (lift_sl_role_right ρ) (LM := comp_model).
  Proof using.
    Ltac simpl_3rd :=
      rewrite !bool_decide_eq_false_2; try done; rewrite !orb_false_l.
    
    repeat (split; simpl).
    - simpl_3rd. role_cases_ext. 
      apply VFM in IN.
      rewrite lookup_kmap. pose proof (sm_fuel_max s2). 
      destruct (fs2 !! x); [simpl in *; lia | done].
    - intros. rewrite !lookup_kmap.
      apply (proj1 (proj2 VFM)).
      { set_solver. }
      rewrite !dom_kmap in H0. 
      apply elem_of_intersection in H0 as [[? [[=->] ?]]%elem_of_map_1 [? [[=->] ?]]%elem_of_map_1].
      set_solver.
    - rewrite dom_kmap. apply elem_of_map_2.
      apply VFM.
    - intros ? [IN2 NIN1]%elem_of_difference.
      rewrite dom_kmap in IN2. apply elem_of_map_1 in IN2 as [? [[=->] ?]].
      rewrite lookup_kmap.
      do 3 apply proj2 in VFM. apply proj1 in VFM.
      assert (x ∈ dom fs2 ∖ dom fs1) as X. 
      { apply elem_of_difference. split; auto.
        intros ?. apply NIN1. rewrite dom_kmap. set_solver. }
      specialize (VFM x X).
      pose proof (sm_fuel_max s2).
      destruct (fs2 !! x); [simpl in *; lia | done].
    - intros ?? IN. rewrite !dom_kmap in IN. 
      apply elem_of_intersection in IN as [[? [[=->] ?]]%elem_of_map_1 [? [[=->] ?]]%elem_of_map_1].
      rewrite !lookup_kmap. apply VFM; auto. set_solver.
    - simpl. do 5 apply proj2 in VFM. apply proj1 in VFM.
      simpl_3rd. apply union_subseteq. rewrite !dom_kmap. set_solver. 
    - do 6 apply proj2 in VFM. rewrite !dom_kmap.
      apply elem_of_subseteq. intros ? [? [[=->] ?]]%elem_of_map_1.
      specialize (VFM x0 H0). apply elem_of_union in VFM as [[[? | ?]%elem_of_union | ?]%elem_of_union | ?].
      + repeat (apply elem_of_union; left).
        apply elem_of_difference. split.
        * set_solver.
        * simpl_3rd. role_cases_ext. set_solver. 
      + set_solver.
      + apply elem_of_union; left. apply elem_of_union; right.
        apply elem_of_difference. split; [set_solver| ].
        simpl_3rd. role_cases_ext. set_solver.
      + simpl_3rd. apply elem_of_union; right.
        apply elem_of_intersection. split; [| set_solver].
        apply elem_of_difference. split; [set_solver| ]. 
        role_cases_ext. set_solver. 
  Qed. 

  Lemma kmap_filter_disj
    (fs1 fs2: gmap (fmrole spinlock_model_impl) nat)
    (lift: fmrole spinlock_model_impl -> fmrole comp_model_impl)
    (INJ: Inj eq eq lift)
    (DISJ12: fs1 ##ₘ fs2):
  kmap lift (filter (λ '(k, _), k ∈ dom fs2) (fs1 ∪ fs2))
  =
    ((filter (λ '(k, _), k ∈ ((set_map lift (dom fs2)): gset (fmrole comp_model_impl))) (kmap lift (fs1 ∪ fs2))): gmap (fmrole comp_model_impl) nat).
  Proof using.
    simpl.
    rewrite kmap_union. rewrite !map_filter_union; auto.
    2: { apply map_disjoint_kmap; [apply _| set_solver]. }        
    rewrite kmap_union.
    rewrite !gmap_filter_dom_id.
    apply leibniz_equiv.
    eapply fin_maps.union_proper.
    2: { symmetry. apply leibniz_equiv_iff. apply map_filter_id.
         intros ?? IN. rewrite -dom_kmap. eapply elem_of_dom_2; eauto. }
    etrans.
    { apply leibniz_equiv_iff, kmap_empty_iff; [by apply _| ].
      apply map_filter_empty_iff. red. intros ???%elem_of_dom_2 ?.
      apply map_disjoint_dom in DISJ12. set_solver. }
    symmetry. apply leibniz_equiv_iff.
    apply map_filter_empty_iff. red. intros ??? IN2.
    rewrite -dom_kmap in IN2. apply elem_of_dom in IN2 as [? ?].  
    apply (map_disjoint_kmap lift) in DISJ12. 
    eapply map_disjoint_spec in DISJ12; eauto.
  Qed.

  Notation "'has_fuels_' '<' ctx '>'" := (has_fuels (PMPP := ctx)) (at level 20, format "has_fuels_  < ctx >"). 

  Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (LM := LM) (iLM := comp_model) (PMPP := PMPP))).

  Lemma sl1_PMP Einvs (γ: gname) (DISJ_INV: Einvs ## ↑Ns):
    PMP Einvs ∗ (inv Ns (comp_inv_impl γ)) ⊢
    PartialModelPredicates (Einvs ∪ ↑Ns) (LM := LM) (iLM := spinlock_model) (PMPP := (sl1_PMPP γ)). 
  Proof. 
    iIntros "[#PMP #COMP]". iApply @Build_PartialModelPredicates.

    iModIntro. repeat iSplitR.
    - iIntros "* FUELS_SL MSI".
      iMod (update_no_step_enough_fuel with "PMP [FUELS_SL] [MSI]") as "-#UPD".
      2: by eauto.
      3: done. 
      2: { iDestruct (has_fuels_sl1 with "FUELS_SL") as "foo".
           rewrite kmap_fmap. iFrame. }
      { intros ?%dom_empty_iff_L%kmap_empty_iff; [set_solver| apply _]. }
      iDestruct "UPD" as (??) "([% %]&?&?)".
      iModIntro. do 2 iExists _. iSplitR; [done| ]. iFrame.
      iApply has_fuels_sl1. iApply has_fuels_proper; [..| iFrame]; [done| ].
      rewrite !difference_empty_L.
      by rewrite !gmap_filter_dom_id. 
    - iIntros "* FUELS_SL MSI".
      
      iMod (update_fork_split with "PMP [FUELS_SL] [MSI]") as "-#UPD".
      all: eauto. 
      4: { iDestruct (has_fuels_sl1 with "FUELS_SL") as "foo".
           rewrite kmap_fmap. iFrame. }
      3: { rewrite dom_kmap_L. rewrite -DOM.
           rewrite set_map_union_L. reflexivity. }
      { set_solver. }
      { intros ?%kmap_empty_iff; [done| apply _]. }
      iDestruct "UPD" as (?) "(F2&F1&FIN&?&%)".
      iModIntro. iExists _. iFrame.
      (* pose proof @dom_union_inv_L.  *)
      pose proof (dom_union_inv_L fs _ _ DISJ (eq_Symmetric _ _ DOM)) as (fs1 & fs2 & FS12 & DISJ12 & DOM1 & DOM2). 
      iSplitL "F2".
      { simpl. iApply has_fuels_sl1. iApply has_fuels_proper; [reflexivity| | iFrame].
        subst fs R1 R2. apply leibniz_equiv_iff.
        eapply kmap_filter_disj; [apply _ | done]. }
      iSplitL "F1".
      { simpl. iApply has_fuels_sl1. iApply has_fuels_proper; [reflexivity| | iFrame].
        rewrite map_union_comm in FS12; auto.  
        subst fs R1 R2. apply leibniz_equiv_iff.
        eapply kmap_filter_disj; [apply _ | done]. }
      iSplitL; [| done].
      iIntros "NO". iApply "FIN". 
      simpl. by rewrite map_fmap_singleton set_map_empty.
    - iIntros "*". iIntros "FUELS ST MSI FR".
      iInv Ns as (((ost1, ost2), osc)) "(>ST_COMP & >AUTH)" "CLOS".
      rewrite difference_union_distr_l_L difference_diag_L.
      rewrite difference_disjoint_L; [| done]. rewrite union_empty_r_L. 
      iAssert (⌜ ost1 = Some s1 ⌝)%I as %->.
      { simpl. rewrite /comp_sl1_st_frag. 
        iCombine "AUTH ST" as "OWN". iDestruct (own_valid with "OWN") as %[INCL ?]%auth_both_valid_discrete.
        iPureIntro. 
        apply pair_included in INCL as [[INCL ?]%pair_included ?]. 
        by apply Excl_included, leibniz_equiv_iff in INCL. } 
      iDestruct (update_step_still_alive with "PMP [FUELS] ST_COMP MSI FR") as "UPD".
      10: { by iApply has_fuels_sl1. }
      8: { apply ct_sl_step_1. eauto. }
      { simpl. set_solver. }
      { rewrite dom_kmap. eapply set_map_mono; [| apply STASH]. done. }
      { simpl.
        rewrite /lift_sl_role_left. rewrite /lift_sl_role_left.  (* TODO: why twice? *)
        apply disjoint_intersection_L. 
        repeat (apply disjoint_union_l; split).
        - set_solver.
        - set_solver.
        - destruct osc; [destruct n| ]; simpl; set_solver. }
      2, 3, 4: done.
      { apply disjoint_intersection_L, (set_map_disjoint _ _ lift_sl_role_left) in NOS2; [| by apply _].
        rewrite -dom_kmap in NOS2. 
        apply disjoint_intersection_L. by apply NOS2. }
      { by apply vfm_sl1. }
      iMod "UPD" as (??) "(% & FUELS & M2 & MSI & FR)". 
      iMod (update_sl1 _ _ (Some s2) with "[ST AUTH]") as "[ST AUTH]"; [by iFrame| ].
      iMod ("CLOS" with "[M2 AUTH]") as "_".
      { iNext. rewrite /comp_inv_impl. iExists _. iFrame. }
      iModIntro. do 2 iExists _. iFrame. iSplitR; [done| ].
      iSplitL "FUELS".
      + by iApply has_fuels_sl1.
      + simpl. iApply partial_free_roles_are_Proper; [| iFrame].
        rewrite set_map_union.
        apply sets.union_proper; [| done].
        rewrite set_map_difference. apply difference_proper; [done| ].
        rewrite -!union_assoc. rewrite difference_union_distr_l. etrans. 
        2: { symmetry. eapply sets.union_proper; [reflexivity| ].
             Unshelve. 2: exact ∅. set_solver. }
        rewrite union_empty_r. rewrite difference_union_distr_r.
        etrans.
        2: { apply sets.intersection_proper; [reflexivity| ].
             symmetry. apply difference_disjoint.
             destruct osc as [?n| ]; [destruct n| ]; simpl; set_solver. }
        rewrite -set_map_difference. set_solver.
    - iIntros "* MSI FR FUELS". 
      iDestruct (has_fuels_sl1 with "FUELS") as "FUELS". simpl.
      iDestruct (partial_free_roles_fuels_disj with "PMP MSI FR FUELS") as %DISJ.
      rewrite dom_kmap in DISJ. iPureIntro.
      eapply set_map_disjoint; eauto. apply _. 
  Qed. 

  Lemma sl2_PMP Einvs (γ: gname) (DISJ_INV: Einvs ## ↑Ns):
    PMP Einvs ∗ (inv Ns (comp_inv_impl γ)) ⊢
    PartialModelPredicates (Einvs ∪ ↑Ns) (LM := LM) (iLM := spinlock_model) (PMPP := (sl2_PMPP γ)). 
  Proof. 
    iIntros "[#PMP #COMP]". iApply @Build_PartialModelPredicates.

    iModIntro. repeat iSplitR.
    - iIntros "* FUELS_SL MSI".
      iMod (update_no_step_enough_fuel with "PMP [FUELS_SL] [MSI]") as "-#UPD".
      2: by eauto.
      3: done. 
      2: { iDestruct (has_fuels_sl2 with "FUELS_SL") as "foo".
           rewrite kmap_fmap. iFrame. }
      { intros ?%dom_empty_iff_L%kmap_empty_iff; [set_solver| apply _]. }
      iDestruct "UPD" as (??) "([% %]&?&?)".
      iModIntro. do 2 iExists _. iSplitR; [done| ]. iFrame.
      iApply has_fuels_sl2. iApply has_fuels_proper; [..| iFrame]; [done| ].
      rewrite !difference_empty_L.
      by rewrite !gmap_filter_dom_id. 
    - iIntros "* FUELS_SL MSI".
      
      iMod (update_fork_split with "PMP [FUELS_SL] [MSI]") as "-#UPD".
      all: eauto. 
      4: { iDestruct (has_fuels_sl2 with "FUELS_SL") as "foo".
           rewrite kmap_fmap. iFrame. }
      3: { rewrite dom_kmap_L. rewrite -DOM.
           rewrite set_map_union_L. reflexivity. }
      { set_solver. }
      { intros ?%kmap_empty_iff; [done| apply _]. }
      iDestruct "UPD" as (?) "(F2&F1&FIN&?&%)".
      iModIntro. iExists _. iFrame.
      (* pose proof @dom_union_inv_L.  *)
      pose proof (dom_union_inv_L fs _ _ DISJ (eq_Symmetric _ _ DOM)) as (fs1 & fs2 & FS12 & DISJ12 & DOM1 & DOM2). 
      iSplitL "F2".
      { simpl. iApply has_fuels_sl2. iApply has_fuels_proper; [reflexivity| | iFrame].
        subst fs R1 R2. apply leibniz_equiv_iff.
        eapply kmap_filter_disj; [apply _ | done]. }
      iSplitL "F1".
      { simpl. iApply has_fuels_sl2. iApply has_fuels_proper; [reflexivity| | iFrame].
        rewrite map_union_comm in FS12; auto.  
        subst fs R1 R2. apply leibniz_equiv_iff.
        eapply kmap_filter_disj; [apply _ | done]. }
      iSplitL; [| done].
      iIntros "NO". iApply "FIN". 
      simpl. by rewrite map_fmap_singleton set_map_empty.
    - iIntros "*". iIntros "FUELS ST MSI FR".
      iInv Ns as (((ost1, ost2), osc)) "(>ST_COMP & >AUTH)" "CLOS".
      rewrite difference_union_distr_l_L difference_diag_L.
      rewrite difference_disjoint_L; [| done]. rewrite union_empty_r_L. 
      iAssert (⌜ ost2 = Some s1 ⌝)%I as %->.
      { simpl. rewrite /comp_sl1_st_frag. 
        iCombine "AUTH ST" as "OWN". iDestruct (own_valid with "OWN") as %[INCL ?]%auth_both_valid_discrete.
        iPureIntro. 
        apply pair_included in INCL as [[? INCL]%pair_included ?]. 
        by apply Excl_included, leibniz_equiv_iff in INCL. } 
      iDestruct (update_step_still_alive with "PMP [FUELS] ST_COMP MSI FR") as "UPD".
      10: { by iApply has_fuels_sl2. }
      8: { apply ct_sl_step_2. eauto. }
      { simpl. simpl_3rd. set_solver. }
      { rewrite dom_kmap. eapply set_map_mono; [| apply STASH]. done. }
      { simpl.
        rewrite /lift_sl_role_right. rewrite /lift_sl_role_right.  (* TODO: why twice? *)
        simpl_3rd. 
        apply disjoint_intersection_L. 
        repeat (apply disjoint_union_l; split).
        - set_solver.
        - set_solver.
        - destruct osc; [destruct n| ]; simpl; set_solver. }
      2, 3, 4: done.
      { apply disjoint_intersection_L, (set_map_disjoint _ _ lift_sl_role_right) in NOS2; [| by apply _].
        rewrite -dom_kmap in NOS2. 
        apply disjoint_intersection_L. by apply NOS2. }
      { by apply vfm_sl2. }
      iMod "UPD" as (??) "(% & FUELS & M2 & MSI & FR)". 
      iMod (update_sl2 _ _ (Some s2) with "[ST AUTH]") as "[ST AUTH]"; [by iFrame| ].
      iMod ("CLOS" with "[M2 AUTH]") as "_".
      { iNext. rewrite /comp_inv_impl. iExists _. iFrame. }
      iModIntro. do 2 iExists _. iFrame. iSplitR; [done| ].
      iSplitL "FUELS".
      + by iApply has_fuels_sl2.
      + simpl. iApply partial_free_roles_are_Proper; [| iFrame].
        rewrite set_map_union.
        apply sets.union_proper; [| done].
        rewrite set_map_difference. apply difference_proper; [done| ].
        repeat (rewrite difference_union_distr_l). 
        rewrite (subseteq_empty_difference _ (_ ∪ _ ∪ _)); [| set_solver].
        rewrite union_empty_l union_comm. simpl_3rd.         
        rewrite (subseteq_empty_difference _ (_ ∪ _ ∪ _)); [| set_solver].
        rewrite union_empty_l. rewrite !difference_union_distr_r.
        rewrite subseteq_intersection_1.
        2: { eapply subseteq_proper; [reflexivity| ..].
             { apply difference_disjoint.
               destruct osc as [?n| ]; [destruct n| ]; simpl; set_solver. }
             set_solver. }
        rewrite intersection_comm. rewrite subseteq_intersection_1.
        { rewrite -set_map_difference. set_solver. }
        set_solver.
    - iIntros "* MSI FR FUELS". 
      iDestruct (has_fuels_sl2 with "FUELS") as "FUELS". simpl.
      iDestruct (partial_free_roles_fuels_disj with "PMP MSI FR FUELS") as %DISJ.
      rewrite dom_kmap in DISJ. iPureIntro.
      eapply set_map_disjoint; eauto. apply _. 
  Qed. 

End SlPMP. 
