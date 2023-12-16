From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness trace_utils trace_lookup utils.


Section TmapDisj.
  Context `{Countable K} `{Countable V}. 

  Definition tmap_disj (tm: gmap K (gset V)) :=
    forall (k1 k2: K) (S1 S2: gset V) (NEQ: k1 ≠ k2),
      tm !! k1 = Some S1 -> tm !! k2 = Some S2 -> S1 ## S2.

  Lemma forall_prod_helper {A B: Type} (P: A -> B -> Prop):
    (forall a b, P a b) <-> (forall ab: A * B, P ab.1 ab.2).
  Proof.
    split; [by eauto|]. intros PP ??.
    apply (PP (a, b)).
  Qed.    
  
  Global Instance tmap_disj_dec tm: Decision (tmap_disj tm).
  Proof.
    set pairs := let d := elements (dom tm) in
                 k1 ← d; k2 ← d;
                 if (decide (k1 = k2)) then [] else [(k1, k2)]. 
    set alt := Forall (fun '(k1, k2) => (default ∅ (tm !! k1)) ## (default ∅ (tm !! k2))) pairs.
    apply Decision_iff_impl with (P := alt); [| solve_decision].
    rewrite /alt. rewrite Forall_forall. 
    rewrite /pairs.
    repeat setoid_rewrite elem_of_list_bind.
    repeat setoid_rewrite elem_of_elements.
    rewrite /tmap_disj.
    repeat setoid_rewrite elem_of_dom.
    rewrite forall_prod_helper. apply forall_proper. intros [k1 k2]. simpl.
    erewrite ex_det_iff with (a := k1).
    2: { intros ?. erewrite ex_det_iff with (a := k2).
         2: { intros ?. destruct decide; set_solver. }
         destruct decide; set_solver. }
    erewrite ex_det_iff with (a := k2).
    2: { intros ?. destruct decide; set_solver. }
    destruct decide; [set_solver| ].
    destruct (tm !! k1), (tm !! k2); set_solver.
  Qed. 

End TmapDisj.


Section LsMapping.
  Context {G: Type}.
  Context {M: FairModel}.
  Context `{Countable G}.
  
  Definition ls_mapping_impl (tmap: gmap G (gset (fmrole M))): gmap M.(fmrole) G :=
    let tmap_l := map_to_list tmap in
    let tmap_flat := flat_map (fun '(τ, R) => map (pair τ) (elements R)) tmap_l in
    let tmap_rev := (fun '(τ, ρ) => (ρ, τ)) <$> tmap_flat in
    list_to_map tmap_rev.

  Lemma ls_mapping_tmap_corr_impl tmap (DISJ: tmap_disj tmap):
    maps_inverse_match (ls_mapping_impl tmap) tmap.
  Proof.
    red. intros. rewrite /ls_mapping_impl.
    etransitivity.
    { symmetry. apply elem_of_list_to_map.
      rewrite -list_fmap_compose.
      rewrite fmap_flat_map.
      rewrite flat_map_concat_map. apply concat_NoDup.
      { intros. apply list_lookup_fmap_Some in H0 as [[??] [? ->]].
        simpl. rewrite -list_fmap_compose.
        apply NoDup_fmap_2; [apply _| ].
        apply NoDup_elements. }
      intros.
      apply list_lookup_fmap_Some in H1 as [[??] [? ->]].
      apply list_lookup_fmap_Some in H2 as [[??] [? ->]].
      simpl. apply elem_of_disjoint.
      intros ? [[??] [-> ?]]%elem_of_list_fmap_2 [[??] [? ?]]%elem_of_list_fmap_2.
      simpl in H4. subst.
      apply elem_of_list_fmap_2 in H3 as [? [[=] ?]].
      apply elem_of_list_fmap_2 in H5 as [? [[=] ?]].
      subst.
      assert (tmap !! g = Some g0).
      { eapply elem_of_map_to_list. eapply elem_of_list_lookup_2; eauto. }
      assert (tmap !! g1 = Some g2).
      { eapply elem_of_map_to_list. eapply elem_of_list_lookup_2; eauto. }
      assert (g ≠ g1).
      { intros <-.
        pose proof (NoDup_fst_map_to_list tmap).
        eapply NoDup_alt in H5.
        { apply H0, H5. }
        all: apply list_lookup_fmap_Some; eauto. }
      pose proof (@DISJ _ _ _ _ H5 H3 H4).
      set_solver. }
    etransitivity.
    { apply elem_of_list_fmap. }
    transitivity ((v, k)
       ∈ flat_map (λ '(τ, R), map (pair τ) (elements R)) (map_to_list tmap)).
    { split.
      - intros (?&?&?). destruct x. congruence.
      - intros. exists (v, k). eauto. }
    rewrite elem_of_list_In.
    rewrite in_flat_map.

    split.
    - intros [[??][IN1 IN2]].
      apply elem_of_list_In, elem_of_map_to_list in IN1.
      apply in_map_iff in IN2 as [? [[=] yy]]. subst.
      eexists. split; eauto.
      apply elem_of_list_In in yy. set_solver.
    - intros [? [??]]. exists (v, x). split.
      + by apply elem_of_list_In, elem_of_map_to_list.
      + apply in_map_iff. eexists. split; eauto.
        apply elem_of_list_In. set_solver.
  Qed.

End LsMapping.

Section fairness.
  Context {G: Type}.
  Context {M: FairModel}.
  Context `{Countable G}.

  Context {LSI: fmstate M -> gmap G (gset (fmrole M)) -> gmap (fmrole M) nat -> Prop}.
  Context `{forall s tm f, Decision (LSI s tm f)}.

  Record LiveState := MkLiveState {
    ls_under:> M.(fmstate);

    ls_fuel: gmap (fmrole M) nat;
    ls_fuel_dom: M.(live_roles) ls_under ⊆ dom ls_fuel;

    (* ls_mapping: gmap M.(fmrole) G; *)
    (* ls_same_doms: dom ls_mapping = dom ls_fuel; *)
    ls_tmap: gmap G (gset (fmrole M));
    ls_tmap_fuel_same_doms:
      forall ρ, ρ ∈ dom ls_fuel <-> exists τ R, ls_tmap !! τ = Some R /\ ρ ∈ R;
    ls_tmap_disj: tmap_disj ls_tmap;
      (* forall (τ1 τ2: G) (S1 S2: gset (fmrole M)) (NEQ: τ1 ≠ τ2), *)
      (*   ls_tmap !! τ1 = Some S1 -> ls_tmap !! τ2 = Some S2 -> S1 ## S2; *)

    ls_inv: LSI ls_under ls_tmap ls_fuel;
  }.


  Definition fuel_map := gmap (fmrole M) nat.
  Definition groups_map := gmap G (gset (fmrole M)).
  Definition roles_map := gmap (fmrole M) G. 

  Arguments ls_under {_}.
  Arguments ls_fuel {_}.
  Arguments ls_fuel_dom {_}.
  (* Arguments ls_mapping {_}. *)
  (* Arguments ls_same_doms {_}. *)
  Arguments ls_tmap {_}.
  Arguments ls_tmap_fuel_same_doms {_}.
  Arguments ls_tmap_disj {_}.

  Definition ls_mapping (δ: LiveState): gmap M.(fmrole) G :=
    ls_mapping_impl δ.(ls_tmap).

  Definition ls_mapping_tmap_corr (δ: LiveState) :=
    ls_mapping_tmap_corr_impl (@ls_tmap δ) (@ls_tmap_disj δ). 
    
  Lemma ls_same_doms δ: dom (ls_mapping δ) = dom (@ls_fuel δ).
  Proof.
    pose proof (@ls_tmap_fuel_same_doms δ). apply set_eq.
    intros. split; intros.
    - apply H1. apply elem_of_dom in H2 as [? ?].
      apply ls_mapping_tmap_corr in H2. eauto.
    - apply H1 in H2 as [? H2]. apply ls_mapping_tmap_corr in H2.
      eapply elem_of_dom; eauto.
  Qed.

  Lemma ls_mapping_dom (m: LiveState):
    M.(live_roles) m.(ls_under) ⊆ dom (ls_mapping m).
  Proof. rewrite ls_same_doms. apply ls_fuel_dom. Qed.

  Definition mapped_roles (tm: groups_map): gset (fmrole M) :=
    flatten_gset (map_img tm). 

  Lemma mapped_roles_dom_fuels_gen
    (tm: groups_map) (fm: fuel_map)
    (DOMS: forall ρ, ρ ∈ dom fm <-> exists τ R, tm !! τ = Some R /\ ρ ∈ R):
    dom fm = mapped_roles tm. 
  Proof. 
    apply set_eq. intros ρ.
    rewrite DOMS.
    rewrite /mapped_roles. rewrite flatten_gset_spec.
    rewrite ex2_comm. apply exist_proper. intros R.
    rewrite elem_of_map_img. set_solver. 
  Qed.

  Lemma mapped_roles_dom_fuels δ:
    dom (@ls_fuel δ) = mapped_roles (@ls_tmap δ).
  Proof.
    apply mapped_roles_dom_fuels_gen.
    apply δ. 
  Qed.   

  Inductive FairLabel {Roles} :=
  | Take_step: Roles -> G -> FairLabel
  | Silent_step: G -> FairLabel
  | Config_step: FairLabel
  .
  Arguments FairLabel : clear implicits.

  Global Instance FL_eqdec: EqDecision (@FairLabel (fmrole M)).
  Proof. solve_decision. Qed.

  Global Instance FL_cnt: Countable (@FairLabel (fmrole M)).
  Proof. 
    set (FL_alt := (G * (fmrole M) + G + unit)%type).
    set (to_alt := fun fl => match fl with
                          | Take_step ρ τ => inl $ inl (τ, ρ)
                          | Silent_step τ => inl $ inr τ
                          | Config_step => (inr tt): FL_alt
                          end).
    set (from_alt := fun (fl': FL_alt) => match fl' with
                             | inl (inl (τ, ρ)) => Take_step ρ τ
                             | inl (inr τ) => Silent_step τ
                             | inr _ => Config_step
                             end).
    eapply (inj_countable' to_alt from_alt).
    intros. by destruct x. 
  Qed. 

  Definition less (x y: option nat) :=
    match x, y with
    | Some x, Some y => x < y
    | _, _ => False
    end.

  Inductive must_decrease (ρ': M.(fmrole)) (oρ: option M.(fmrole)) (a b: LiveState):
    option G -> Prop :=
  | Same_tid tid (Hneqρ: Some ρ' ≠ oρ) (Hsametid: Some tid = (ls_mapping a) !! ρ'):
      must_decrease ρ' oρ a b (Some tid)
  | Change_tid otid (Hneqtid: (ls_mapping a) !! ρ' ≠ (ls_mapping b) !! ρ')
               (Hissome: is_Some (ls_mapping b !! ρ')):
    must_decrease ρ' oρ a b otid
  (* | Zombie otid (Hismainrole: oρ = Some ρ') (Hnotalive: ρ' ∉ live_roles _ b) (Hnotdead: ρ' ∈ dom b.(ls_fuel)): *)
  (*   must_decrease ρ' oρ a b otid *)
  .

  Global Instance must_decrease_dec:
    forall a oρ st1 st2 og, Decision (must_decrease a oρ st1 st2 og).
  Proof. 
    intros.
    destruct (decide (@ls_mapping st1 !! a ≠ @ls_mapping st2 !! a /\ is_Some (@ls_mapping st2 !! a))).
    { left. apply Change_tid; apply a0. }
    destruct og.
    2: { right. intros DECR. inversion DECR; tauto. }
    destruct (decide (Some a ≠ oρ /\ Some g = @ls_mapping st1 !! a)).
    - left. econstructor; apply a0.
    - right. intros DECR. inversion DECR; tauto.
  Qed.


  Definition fuel_decr (tid: option G) (oρ: option M.(fmrole))
             (a b: LiveState) :=
    ∀ ρ', ρ' ∈ dom a.(ls_fuel) -> ρ' ∈ dom b.(ls_fuel) →
          must_decrease ρ' oρ a b tid ->
          oless (b.(ls_fuel) !! ρ') (a.(ls_fuel) !! ρ').

  Definition fuel_must_not_incr oρ (a b: LiveState) :=
    (* ∀ ρ', ρ' ∈ dom a.(ls_fuel) -> Some ρ' ≠ oρ -> *)
    (*       (oleq (b.(ls_fuel) !! ρ') (a.(ls_fuel) !! ρ') *)
    (*             ∨ (ρ' ∉ dom b.(ls_fuel) ∧ ρ' ∉ M.(live_roles) a.(ls_under))). *)
    ∀ ρ', ρ' ∈ dom a.(ls_fuel) -> 
          (oleq (b.(ls_fuel) !! ρ') (a.(ls_fuel) !! ρ') ∨
           oρ = Some ρ' /\ (ρ' ∉ dom b.(ls_fuel) \/ ρ' ∈ M.(live_roles) b.(ls_under)) \/
           (ρ' ∉ dom b.(ls_fuel) ∧ ρ' ∉ M.(live_roles) a.(ls_under))).

  Definition ls_trans fuel_limit (a: LiveState) ℓ (b: LiveState): Prop :=
    match ℓ with
    | Take_step ρ tid =>
      M.(fmtrans) a (Some ρ) b
      ∧ (ls_mapping a) !! ρ = Some tid
      ∧ fuel_decr (Some tid) (Some ρ) a b
      ∧ fuel_must_not_incr (Some ρ) a b
      ∧ (ρ ∈ live_roles _ b -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ (∀ ρ, ρ ∈ dom b.(ls_fuel) ∖ dom a.(ls_fuel) -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ dom b.(ls_fuel) ∖ dom a.(ls_fuel) ⊆ live_roles _ b ∖ live_roles _ a
    | Silent_step tid =>
      (∃ ρ, (ls_mapping a) !! ρ = Some tid)
      ∧ fuel_decr (Some tid) None a b
      ∧ fuel_must_not_incr None a b
      ∧ dom b.(ls_fuel) ⊆ dom a.(ls_fuel)
      ∧ a.(ls_under) = b.(ls_under)
    | Config_step =>
      M.(fmtrans) a None b
      ∧ fuel_decr None None a b
      ∧ fuel_must_not_incr None a b
      ∧ (∀ ρ, ρ ∈ M.(live_roles) b ∖ M.(live_roles) a -> oleq (b.(ls_fuel) !! ρ) (Some (fuel_limit b)))
      ∧ False (* TODO: add support for config steps later! *)
    end.

  Record LiveModel := {
      lm_fl : M → nat;
      lm_ls := LiveState;
      lm_lbl := FairLabel M.(fmrole);
      lm_ls_trans := ls_trans lm_fl;
    }.

  Global Instance lm_ls_trans_dec `{LM: LiveModel}
    {M_TRANS_DEC: ∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2)}
    {M_ST_DEC: EqDecision (fmstate M)}
    st1 l st2:
    Decision (lm_ls_trans LM st1 l st2).
  Proof.
    destruct l; simpl. 
    3: { right. intros []. tauto. }
    - solve_decision. 
    - repeat apply and_dec; try solve_decision.
      destruct (@ls_tmap st1 !! g) eqn:TMAP.
      2: { right. intros [? MAP].
           apply ls_mapping_tmap_corr in MAP as (?&SOME&?).
           by rewrite TMAP in SOME. }
      destruct (decide (g0 = ∅)) as [-> |NEMPTY].
      { right. intros [? MAP].
        apply (ls_mapping_tmap_corr) in MAP as (?&SOME&?).
        rewrite TMAP in SOME. set_solver. }
      left. apply set_choose_L in NEMPTY as [ρ ?].
      exists ρ. apply (ls_mapping_tmap_corr). eauto. 
  Defined. 
    
  Definition live_model_model `(LM : LiveModel) : Model := {|
    mstate := lm_ls LM;
    mlabel := lm_lbl LM;
    mtrans := lm_ls_trans LM;
  |}. 
  
  Definition fair_lbl_matches_group (ℓ: @FairLabel (fmrole M)) (τ: G) := 
    match ℓ with
    | Take_step _ τ' | Silent_step τ' => τ = τ'
    | Config_step => False
    end. 

  Global Instance fair_lbl_match_Dec: 
    forall ℓ τ, Decision (fair_lbl_matches_group ℓ τ).
  Proof.
    intros. destruct ℓ; simpl; solve_decision.
  Qed.  

  Lemma ls_same_doms' (δ: LiveState):
    forall ρ, is_Some (@ls_mapping δ !! ρ) <-> is_Some (@ls_fuel δ !! ρ).
  Proof. 
    intros. rewrite -!elem_of_dom. by rewrite ls_same_doms.
  Qed.

  (* Program Definition initial_ls `{LM: LiveModel} (s0: M) (ζ0: G) *)
  (*   (f0 := gset_to_gmap (LM.(lm_fl) s0) (M.(live_roles) s0)) *)
  (*   (m0 := gset_to_gmap ζ0 (M.(live_roles) s0)) *)
  (*   (LSI0: LSI s0 m0 f0)  *)
  (*   : LM.(lm_ls) := *)
  (*   {| ls_under := s0; *)
  (*      ls_fuel := f0; *)
  (*      ls_mapping := m0; *)
  (*   |}. *)
  (* Next Obligation.  *)
  (*   simpl. intros. apply reflexive_eq. rewrite dom_gset_to_gmap //. *)
  (* Qed. *)
  (* Next Obligation.  *)
  (*   simpl. intros. apply reflexive_eq. rewrite !dom_gset_to_gmap //.  *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   done. *)
  (* Qed.  *)

  (* TODO: get rid of these functions *)
  Section Legacy.

    Definition build_LS_ext 
    (st: fmstate M) (fuel: gmap (fmrole M) nat)
    (LIVE_FUEL: live_roles _ st ⊆ dom fuel)
    (tmap: gmap G (gset (fmrole M)))
    (TMAP_FUEL_SAME_DOMS: forall ρ, ρ ∈ dom (fuel) <-> exists τ R, tmap !! τ = Some R /\ ρ ∈ R)
    (LS_TMAP_DISJ: forall (τ1 τ2: G) (S1 S2: gset (fmrole M)) (NEQ: τ1 ≠ τ2),
      tmap !! τ1 = Some S1 -> tmap !! τ2 = Some S2 -> S1 ## S2)
    (LS_INV: LSI st tmap fuel) :=
      {| ls_under := st;
         ls_fuel := fuel;
         ls_fuel_dom := LIVE_FUEL;
         ls_tmap := tmap;
         ls_tmap_fuel_same_doms := TMAP_FUEL_SAME_DOMS;
         ls_tmap_disj := LS_TMAP_DISJ;
         ls_inv := LS_INV; |}.
    
    Lemma build_LS_ext_spec_st st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV:
      @ls_under (build_LS_ext st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV) = st.
    Proof. done. Qed. 

    Lemma build_LS_ext_spec_fuel st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV:
      @ls_fuel (build_LS_ext st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV) = fuel.
    Proof. done. Qed. 

    Lemma build_LS_ext_spec_tmap st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV:
      @ls_tmap (build_LS_ext st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV) = tmap.
    Proof. done. Qed. 

    Lemma build_LS_ext_spec_mapping st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV
      rmap (MATCH: maps_inverse_match rmap tmap):
      ls_mapping (build_LS_ext st fuel LIVE_FUEL tmap TMAP_FUEL_SAME_DOMS LS_TMAP_DISJ LS_INV) = rmap. 
    Proof. 
      eapply maps_inverse_match_uniq1.
      - apply ls_mapping_tmap_corr. 
      - by rewrite build_LS_ext_spec_tmap.
    Qed.

  End Legacy.

  Definition initial_ls_LSI {LM: LiveModel} s0 (g: G) :=
    let f0 := gset_to_gmap (LM.(lm_fl) s0) (M.(live_roles) s0) in
    (* let m0 := gset_to_gmap g (M.(live_roles) s0) in *)
    let tm0 := {[ g := M.(live_roles) s0 ]}: groups_map in
    LSI s0 tm0 f0.

  (* TODO: use Program after changing the definition of LiveState *)
  Definition initial_ls' {LM: LiveModel} (s0: M) (ζ0: G)
    (f0 := gset_to_gmap (LM.(lm_fl) s0) (M.(live_roles) s0))
    (tm0 := {[ ζ0 := M.(live_roles) s0 ]}: gmap G (gset (fmrole M)))
    (LSI0: @initial_ls_LSI LM s0 ζ0)
    : LM.(lm_ls).
    assert (tmap_disj tm0) as DISJ0.
    { subst tm0. intros ????. repeat setoid_rewrite lookup_singleton_Some.
      by intros ? [-> <-] [-> <-]. }
    unshelve eapply (@build_LS_ext  s0 f0 _ tm0 _ _); eauto. 
    - simpl. intros. apply reflexive_eq. rewrite dom_gset_to_gmap //.
    - intros. subst tm0. setoid_rewrite lookup_singleton_Some.
      subst f0. rewrite dom_gset_to_gmap.
      split.
      + intros; eauto.
      + intros (?&?&[-> <-]&?); eauto.
  Defined. 

  Lemma initial_ls'_mapping `{LM: LiveModel} s0 g LSI0:
    ls_mapping (initial_ls' s0 g LSI0 (LM := LM)) = gset_to_gmap g (live_roles M s0).
  Proof.
    rewrite /initial_ls'. erewrite build_LS_ext_spec_mapping; [reflexivity| ].
    apply maps_inverse_match_exact. 
  Qed. 


  Local Ltac SS' := eapply elem_of_dom; eauto. 

  Lemma others_step_fuel_decr `{LM: LiveModel} ρ f f' τ δ ℓ δ'
    (STEP: lm_ls_trans LM δ ℓ δ')
    (Hfuel : @ls_fuel δ !! ρ = Some f)
    (Hmapping : @ls_mapping δ !! ρ = Some τ)
    (Hζ: ¬ fair_lbl_matches_group ℓ τ)
    (FUEL: @ls_fuel δ' !! ρ = Some f'):
    f' ≤ f.
  Proof.
    simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
    + destruct STEP as (?&?&?&Hnoninc&?).
      unfold fuel_must_not_incr in Hnoninc.
      have Hneq: Some ρ ≠ Some ρ0 by congruence.
      specialize (Hnoninc ρ ltac:(SS')).
      unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
      rewrite FUEL in Hnoninc.
      destruct Hnoninc as [?|[?|C]]. 
      3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
      all: set_solver. 
    + destruct STEP as (?&?&Hnoninc&?).
      unfold fuel_must_not_incr in Hnoninc.
      have Hneq: Some ρ ≠ None by congruence.
      specialize (Hnoninc ρ ltac:(SS')).
      unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
      rewrite FUEL in Hnoninc. 
      destruct Hnoninc as [?|[?|C]]. 
      3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
      all: set_solver.
    + destruct STEP as [_ [_ [Hnoninc _]]].
      have HnotNone: Some ρ ≠ None by congruence.
      specialize (Hnoninc ρ ltac:(SS')).
      unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
      rewrite FUEL in Hnoninc. 
      destruct Hnoninc as [?|[?|C]]. 
      3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
      all: set_solver.
  Qed. 
  
  Lemma owner_change_fuel_decr `{LM: LiveModel} ρ f f'
    δ ℓ δ'
    τ τ''
    (STEP: lm_ls_trans LM δ ℓ δ')
    (Hfuel: @ls_fuel δ !! ρ = Some f)
    (Hmapping: @ls_mapping δ !! ρ = Some τ)
    (Hζ'' : @ls_mapping δ' !! ρ = Some τ'')
    (Hchange : τ ≠ τ'')
    (FUEL: @ls_fuel δ' !! ρ = Some f'):
    f' < f.
  Proof.
    destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
    + destruct STEP as (?&?&Hdec&?&?).
      unfold fuel_decr in Hdec. simplify_eq.
      have Hmd: must_decrease ρ (Some ρ0) δ δ' (Some ζ0).
      { econstructor 2. congruence. rewrite Hζ''; eauto. }
      specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
      unfold oleq in Hdec. rewrite Hfuel in Hdec.
      by rewrite FUEL in Hdec. 
    + destruct STEP as (?&Hdec&_).
      unfold fuel_decr in Hdec. simplify_eq.
      have Hmd: must_decrease ρ None δ δ' (Some ζ0).
      { econstructor 2. congruence. rewrite Hζ''; eauto. }
      specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
      unfold oleq in Hdec. rewrite Hfuel in Hdec.
      by rewrite FUEL in Hdec.
    + destruct STEP as [_ [Hdec _]].
      unfold fuel_decr in Hdec.
      have Hmd: must_decrease ρ None δ δ' None.
      { econstructor. congruence. rewrite Hζ''. eauto. }
      specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
      unfold oleq in Hdec. rewrite Hfuel in Hdec.
      by rewrite FUEL in Hdec.
  Qed.

  Lemma fuel_must_not_incr_fuels oρ'
    (δ1 δ2: LiveState)
    ρ f1 f2
    (KEEP: fuel_must_not_incr oρ' δ1 δ2)
    (FUEL1: @ls_fuel δ1 !! ρ = Some f1)
    (FUEL2: @ls_fuel δ2 !! ρ = Some f2)
    (OTHER: oρ' ≠ Some ρ):
    f2 <= f1.
  Proof using.
    red in KEEP. specialize (KEEP ρ ltac:(by apply elem_of_dom)).
    destruct KEEP as [LE|[?|KEEP]].
    + rewrite FUEL1 FUEL2 in LE. simpl in LE. lia. 
    + tauto. 
    + apply proj1 in KEEP. destruct KEEP. eapply elem_of_dom; eauto.
  Qed.

  Lemma step_nonincr_fuels {LM: LiveModel} 
    ℓ (δ1 δ2: LiveState)
    ρ f1 f2
    (STEP: lm_ls_trans LM δ1 ℓ δ2)
    (FUEL1: @ls_fuel δ1 !! ρ = Some f1)
    (FUEL2: @ls_fuel δ2 !! ρ = Some f2)
    (OTHER: forall g, ℓ ≠ Take_step ρ g):
    f2 <= f1.
  Proof.
    destruct ℓ. 
    all: eapply fuel_must_not_incr_fuels; eauto; [apply STEP|..]; congruence.
  Qed. 

End fairness.

Definition LSI_True `{Countable G} {M: FairModel}:
  M → @groups_map G M _ _ → @fuel_map M → Prop :=
  fun _ _ _ => True.

Global Instance lsi_true_model_inh `{Countable G}
  `{INH: Inhabited G} `{LM: @LiveModel G M _ _ LSI_True}: 
  Inhabited (lm_ls LM).
Proof. 
  destruct INH as [g]. 
  pose proof (fmstate_inhabited M) as [s].
  eapply populate, (initial_ls' s g). done.
Qed.


Definition LSI_groups_fixed `{Countable G} {M : FairModel}  (gs: gset G):
  fmstate M → groups_map (M := M) → fuel_map (M := M) → Prop := 
  fun _ tm _ => dom tm ⊆ gs.

Global Instance LSI_gf_dec `{Countable G} M gs:
  forall s tm fm, Decision (LSI_groups_fixed gs s tm fm (G := G) (M := M)).
Proof.
  intros. rewrite /LSI_groups_fixed. solve_decision.
Qed. 


(* Arguments LiveState : clear implicits. *)
(* Arguments LiveModel : clear implicits. *)
Arguments LiveState _ _ {_} {_} _.
Arguments LiveModel _ _ {_ _} _.
(* Arguments live_model_model _ _ {_ _} _. *)

(* Definition live_model_to_model : forall G M LSI, LiveModel G M LSI -> Model := *)
(*   λ G M LSI lm, live_model_model G LSI lm. *)
(* Coercion live_model_to_model : LiveModel >-> Model. *)
(* Arguments live_model_to_model {_ _}. *)

Definition live_model_to_model : forall G M `{_: Countable G} LSI, LiveModel G M LSI -> Model :=
  λ G M LSI e c lm, live_model_model lm.
Coercion live_model_to_model : LiveModel >-> Model.
Arguments live_model_to_model _ _ {_ _}.
