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
  Context `{LM: LiveModel heap_lang M} `{!heapGS Σ LM} {COMP_PRE: compPreG Σ}.
  Context `{PMPP: @PartialModelPredicatesPre _ _ _ Σ comp_model_impl}.

  Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

  Definition comp_st_auth (γ: gname) (st: fmstate comp_model_impl): iProp Σ := 
      own γ ((● (Excl' (fst $ fst st: sl_ofe), Excl' (snd $ fst st: sl_ofe), Excl' (snd st))): comp_cmra).  

  Definition comp_sl1_st_frag (γ: gname) (st: fmstate spinlock_model_impl): iProp Σ := 
      own γ ((◯ (Excl' (Some st: sl_ofe), ε, ε)): comp_cmra).  

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

  Let lift_sl_role_left (ρ: fmrole spinlock_model_impl): fmrole comp_model_impl := 
        (inl ∘ inl) ρ.
  Let lift_sl_role_right (ρ: fmrole spinlock_model_impl): fmrole comp_model_impl := 
        (inl ∘ inr) ρ.
 
  Notation "'has_fuels_' '<' ctx '>'" := (has_fuels (PMPP := ctx)) (at level 20, format "has_fuels_  < ctx >"). 

  Notation "'PMP'" := (fun Einvs => (PartialModelPredicates Einvs (LM := LM) (iLM := comp_model) (PMPP := PMPP))).

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

  (* (* TODO: generalize*) *)
  (* Lemma roles_kmap_filter (fs: gmap (fmrole spinlock_model_impl) nat): *)
  (* kmap lift_sl_role_left (filter (λ '(k, _), k ∈ dom fs) fs) *)
  (* ≡ filter (λ '(k, _), k ∈ dom (kmap lift_sl_role_left fs)) *)
  (*     (kmap lift_sl_role_left fs).  *)

  Section KmapMagic.

  (* TODO: without this explicit definition the following lemma  *)
  (*    fails to instantiate some typeclasses *)
  (* Let kmap_: (fmrole spinlock_model_impl -> fmrole comp_model_impl) → *)
  (*                    (gmap (fmrole spinlock_model_impl) nat) → (gmap (fmrole comp_model_impl) nat). *)
  (*   refine (kmap (K2 := fmrole comp_model_impl) (K1 := fmrole spinlock_model_impl)). *)
  (* Defined. *)

    Notation "'kmap_'" := kmap. 

  (* Context (kmap_: (fmrole spinlock_model_impl -> fmrole comp_model_impl) → *)
  (*                    (gmap (fmrole spinlock_model_impl) nat) → (gmap (fmrole comp_model_impl) nat)). *)
  
(*   Lemma kmap_filter_dom (fs : gmap (fmrole spinlock_model_impl) nat) *)
(* (f : fmrole spinlock_model_impl → fmrole iM) *)
(*   (H1 : Inj eq eq f) *)
(*   (X : ∀ i : fmrole iM, Decision (∃ j : fmrole spinlock_model_impl, i = f j)): *)
(*   kmap_ f (filter (λ '(k, _), k ∈ dom fs) fs) *)
(*   = filter (λ '(k, _), k ∈ dom (kmap_ f fs)) (kmap_ f fs). *)
(*   Proof using.  *)
(*     rewrite /kmap_. *)
(*     (* TODO: refactor *) *)
(*     apply map_eq. intros. *)
(*     (* destruct i.  *) *)
(*     destruct (@decide (exists j, i = f j)). *)
(*     { done. } *)
(*     2: { etrans; [| etrans]; [| exact (eq_refl None) |]. *)
(*          - apply lookup_kmap_None; [apply _| ]. *)
(*            intros. destruct n. eauto. *)
(*          - symmetry. apply map_filter_lookup_None. left. *)
(*            apply lookup_kmap_None; [apply _| ]. *)
(*            intros. destruct n. eauto. } *)
(*     destruct e as [? ->]. rewrite lookup_kmap. *)
(*     destruct (decide (x ∈ dom fs)). *)
(*     + pose proof e as [? EQ]%elem_of_dom. *)
(*       repeat (erewrite map_filter_lookup_Some_2; eauto). *)
(*       { by rewrite lookup_kmap. } *)
(*       rewrite dom_kmap. set_solver. *)
(*     + pose proof n as ?%not_elem_of_dom_1. *)
(*       repeat (rewrite map_filter_lookup_None_2; eauto). *)
(*       rewrite lookup_kmap. eauto. *)
(*   Qed. *)
    
  End KmapMagic.   

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

  Lemma comp_spec tid Einvs (P: iProp Σ)
    (* TODO: get rid of these restrictions *)
    (DISJ_INV1: Einvs ## ↑Ns) (DISJ_INV2: Einvs ## ↑nroot.@"spinlock"):
    PMP Einvs -∗
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
    iApply (wp_fork_nostep_alt with "[ST1] [] [FUELS]").
    5: { rewrite -map_union_assoc map_union_comm.
         2: { apply map_disjoint_union_r. split; solve_disjoint. }
         rewrite -map_union_assoc map_union_comm. 
         2: { apply map_disjoint_union_r. split; solve_disjoint. }
         iDestruct (has_fuels_gt_1 with "FUELS") as "F". 
         2: { rewrite -map_fmap_compose. rewrite !map_fmap_union. by iFrame. } 
         solve_fuels_ge_1 FS. }
    { apply map_disjoint_union_l. split; solve_disjoint. }
    { set_solver. }
    { iSplitR; [done| ]. iIntros (tid') "!# FUELS".
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
      2: { intros. simpl. rewrite Nat.sub_0_r. reflexivity. }
      rewrite map_fmap_id. done. }
    
      


End LocksCompositionProofs.
