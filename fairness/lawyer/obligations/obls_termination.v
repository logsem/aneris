Require Import Coq.Program.Wf.
Require Import Relation_Operators.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len my_omega utils_multisets utils_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model wf_utils obls_pf wf_ms obligations_wf.
From stdpp Require Import relations.


Section Termination.
  Context `{OP: ObligationsParams Degree Level Locale LIM_STEPS}.
  Let OM := ObligationsModel.

  Context (tr: obls_trace).
  Hypothesis (VALID: obls_trace_valid tr). 
  Hypothesis (WF: forall i δ, tr S!! i = Some δ -> om_st_wf δ).
  
  Hypothesis (LVL_WF: wf (strict lvl_le)).
  
  Definition sig_val_at sid i := 
    from_option (fun δ => from_option snd true (ps_sigs δ !! sid)) true (tr S!! i). 
    
  Definition sig_is_set_at sid i := 
    from_option (fun δ => from_option (eq true ∘ snd) False (ps_sigs δ !! sid)) False (tr S!! i). 

  Definition never_set_after sid c := 
    forall i, c <= i -> is_Some (tr S!! i) -> sig_val_at sid i = false.

  (* (* TODO: get rid of excessive negations *) *)
  (* Definition eventually_set sid := *)
  (*   forall c, ¬ never_set_after sid c. *)

  Definition sb_prop sid n :=
    (¬ exists i, sig_is_set_at sid i) /\ n = 0 \/
    (exists i, sig_is_set_at sid i /\ i <= n). 
    (* forall i, eventually_set sid -> n <= i -> sig_val_at sid i = true.  *)

  Context {set_before: SignalId -> nat}.
  Hypothesis (SET_BEFORE_SPEC: forall sid, sb_prop sid (set_before sid)).

  (* TODO: clean up similar definitions *)
  Definition loc_step_with (τ: Locale) :=
    fun δ1 δ2 => loc_step δ1 τ δ2.
  
  Definition lvl_at (sid_i: SignalId * nat): option Level :=
    let '(sid, i) := sid_i in
    δ ← tr S!! i;
    '(l, b) ← ps_sigs δ !! sid;
    mret l. 
    (* from_option (fun δ => from_option fst lvl__def (ps_sigs _ δ !! sid)) lvl__def (tr S!! i). *)

  Definition lvl_opt_lt (x y: option Level) :=
    match x, y with
    | Some x, Some y => strict lvl_le x y
    | Some _, None => True
    | _, _ => False
    end. 
    
  Definition tr_sig_lt: relation (SignalId * nat) :=
    MR lvl_opt_lt lvl_at. 
  
  Lemma never_set_after_after sid i j
    (LE: i <= j):
    never_set_after sid i -> never_set_after sid j.
  Proof using.
    rewrite /never_set_after. intros NEVER m LE'.
    eapply NEVER. lia. 
  Qed.

  Definition phase_ge := flip phase_le. 
  Definition PF (π: Phase) := PF' set_before (phase_ge π).
  Definition TPF (π: Phase) := TPF' tr set_before (phase_ge π).

  Lemma other_expect_ms_le π__ow δ1 τ δ2 k
    (OTHER: let π := default π0 (ps_phases δ1 !! τ) in
            (* phases_incompat π__ow π *)
            phases_disj π__ow π
    ):
    expect_ms_le set_before (phase_ge π__ow) δ1 τ δ2 k. 
  Proof using.
    clear LVL_WF SET_BEFORE_SPEC WF VALID.
    red. intros sid π' d EXP. 
    rewrite /PF /PF'.
    inversion EXP; subst.
    destruct δ1. simpl in *.
    subst new_cps0.
    
    rewrite !mset_filter_disj_union mset_map_disj_union.
    rewrite !mset_filter_singleton.
    rewrite decide_False.
    2: { rewrite LOC_PHASE in OTHER. simpl in OTHER.
         eapply phases_disj_not_le; eauto. by symmetry. }
    
    rewrite mset_map_empty. apply ms_le_disj_union; [apply _| ..].
    + eapply ms_le_Proper; [reflexivity| | reflexivity]. mss.
    + apply ms_le_exp_mono; [lia | reflexivity].
  Qed.

  Lemma min_owner_expect_ms_le δ1 π δ2 k τ__e
    (SET_BOUND: forall sid π__e d, expects_ep δ1 τ__e δ2 sid π__e d ->
                           let n := (LIM_STEPS + 2) * set_before sid in
                           k < n)
    (WF1: om_st_wf δ1)
    (DOM: π ∈ (map_img (ps_phases δ1): gset Phase))
    :
    expect_ms_le set_before (phase_ge π) δ1 τ__e δ2 k. 
  Proof using.
    clear LVL_WF SET_BEFORE_SPEC WF VALID.
    intros. red. intros sid π' d EXP. 
    rewrite /PF /PF'.
    
    inversion EXP; subst.
    pose proof (other_expect_ms_le π δ1 τ__e (update_cps new_cps δ1) k) as OTHER. 
    destruct δ1. simpl in *. subst new_cps0.
    
    apply elem_of_map_img in DOM as [τ PHτ].
    destruct (decide (τ = τ__e)) as [-> | NEQ].
    2: { eapply OTHER; [| done].
         eapply om_wf_ph_disj; eauto. simpl. by rewrite LOC_PHASE. }

    rewrite !mset_filter_disj_union mset_map_disj_union.
    rewrite !mset_filter_singleton.

    rewrite LOC_PHASE in PHτ. inversion PHτ. subst π__max. 
    
    rewrite decide_True; [| red; reflexivity].
    rewrite mset_map_singleton. simpl. 
    
    rewrite -gmultiset_disj_union_assoc. apply ms_le_disj_union; [apply _| ..].
    { reflexivity. }
    rewrite (union_difference_singleton_L _ _ EP).
    
    rewrite filter_union_L.
    rewrite !gset_singleton_if_equiv.
    rewrite decide_True; [| tauto].
    
    rewrite (union_comm_L {[ _ ]} _).
    rewrite !approx_expects_add.
    2, 3: set_solver.
    simpl. rewrite gmultiset_disj_union_comm.
    rewrite -gmultiset_disj_union_assoc.
    apply ms_le_disj_union; [apply _| ..].
    { apply ms_le_exp_mono; [lia | reflexivity]. }
    
    move SET_BOUND at bottom. specialize_full SET_BOUND; [by eauto| ].
    eapply ms_le_Proper; [reflexivity| ..| reflexivity].
    rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.
  Qed.

  Lemma never_set_after_eq_false sid c:
    never_set_after sid c -> forall i δ, c <= i -> tr S!! i = Some δ ->
      exists l, ps_sigs δ !! sid = Some (l, false).
  Proof using.
    intros NEVER i ? LE ITH.
    red in NEVER. specialize (NEVER _ LE ltac:(eauto)).
    rewrite /sig_val_at in NEVER. rewrite ITH in NEVER. simpl in *.
    destruct (ps_sigs δ !! sid) as [[??]|] eqn:SIG; try done.
    simpl in NEVER. subst. eauto. 
  Qed. 

  Lemma never_set_owned s c
    (NEVER_SET: never_set_after s c):
    forall i δ, c <= i -> tr S!! i = Some δ -> 
         map_Exists (fun τ obs => s ∈ obs) (ps_obls δ).
  Proof using WF.
    intros i ? LE ITH. 
    eapply never_set_after_eq_false in NEVER_SET as (?&?); eauto. 
    eapply obls_assigned_equiv; eauto. 
    eapply WF; eauto.
  Qed.

  (* TODO: move *)
  Section MoreWF.

    Definition sig_st_le (st1 st2: option $ @SignalState Level) :=
      match st1, st2 with
      | Some (l1, b1), Some (l2, b2) => l1 = l2 /\ bool_le b1 b2
      | None, _ => True
      | _, _ => False
      end.    

    Lemma loc_step_sig_st_le_pres sid st: 
      preserved_by loc_step_ex (fun δ => sig_st_le st (ps_sigs δ !! sid)).
    Proof using.
      do 2 red. intros δ1 δ2 SIG_LE [τ STEP].
      pose proof (next_sig_id_fresh (default ∅ (ps_obls δ1 !! τ) ∪ (dom $ ps_sigs δ1))) as FRESH.
      inv_loc_step STEP; destruct δ1; try done; simpl in *.
      - subst new_sigs0.
        destruct (decide (sid = s0)) as [-> | ?].
        2: { rewrite lookup_insert_ne. apply SIG_LE. done. }
        rewrite lookup_insert.
        apply not_elem_of_union, proj2, not_elem_of_dom_1 in FRESH. rewrite FRESH in SIG_LE.
        by destruct st as [[??]|]; done.
      - subst new_sigs0.
        destruct (decide (sid = x)) as [-> | ?].
        2: { rewrite lookup_insert_ne; [| done]. apply SIG_LE. }
        rewrite lookup_insert.
        rewrite SIG in SIG_LE. destruct st as [[??]| ]; try done.
        simpl in SIG_LE. destruct SIG_LE as [-> ?].
        split; auto. destruct b; done.
    Qed.

    Lemma fork_step_sig_st_le_pres τ sid st:
      preserved_by (fork_step_of τ) (fun δ => sig_st_le st (ps_sigs δ !! sid)).
    Proof using. 
      do 2 red. intros δ1 δ2 SIG_LE STEP.
      red in STEP. destruct STEP as (?&?&STEP). 
      inversion STEP; destruct δ1; done.
    Qed.

    Global Instance sig_st_le_refl_PO: PartialOrder sig_st_le.
    Proof using.
      split; [split| ].
      - intros ost. destruct ost as [[??]|]; done.
      - intros [[??]|] [[??]|] [[??]|]; try done. simpl.
        intros [-> ?] [-> ?]. destruct b, b0, b1; tauto.
      - intros [[??]|] [[??]|]; try done. simpl.
        intros [-> ?] [? ?]. destruct b, b0; tauto.
    Qed.

    Lemma sig_st_le_lookup_helper i j δi δj s
      (LE: i <= j)
      (ITH: tr S!! i = Some δi)
      (JTH: tr S!! j = Some δj):
      sig_st_le (ps_sigs δi !! s) (ps_sigs δj !! s).
    Proof using VALID.
      forward eapply pres_by_valid_trace; eauto.
      { intros. apply loc_step_sig_st_le_pres with (sid := s). }
      { intros. apply fork_step_sig_st_le_pres. }
      { rewrite ITH. simpl. reflexivity. }
      by rewrite JTH.
    Qed.       

    Lemma loc_steps_rep_phase_exact_pres δ1 δ2 τ oπ k
      (PH: ps_phases δ1 !! τ = oπ)
      (STEPS: nsteps loc_step_ex k δ1 δ2):
      ps_phases δ2 !! τ = oπ.
    Proof using.
      forward eapply pres_by_loc_step_implies_rep.
      { apply loc_step_phases_pres. }
      intros P. red in P. rewrite /preserved_by in P. specialize_full P; eauto.
      { reflexivity. }
      red in P. rewrite P. done.
    Qed. 

    Lemma phases_not_le δ (WF0: om_st_wf δ) τ1 τ2 π1 π2
      (P1: ps_phases δ !! τ1 = Some π1)
      (P2: ps_phases δ !! τ2 = Some π2)
      (PH_LE: phase_le π1 π2):
      τ1 = τ2 /\ π1 = π2.
    Proof using.
      destruct (decide (τ1 = τ2)) as [-> | ?].
      { rewrite P1 in P2. inversion P2. done. }
      edestruct (om_wf_ph_disj δ); eauto. tauto. 
    Qed.

    Lemma other_loc_step_pres_obls τ R τs
      (OTHER: τs ≠ τ):
      preserved_by (loc_step_with τs) (fun δ => ps_obls δ !! τ = Some R /\ om_st_wf δ).
    Proof using.
      red. intros δ1 δ2 [OB WF1] STEP.
      split.
      2: { eapply wf_preserved_by_loc_step; eauto. red. eauto. } 
      inv_loc_step STEP; destruct δ1; try done; simpl in *.
      - subst new_obls0. rewrite lookup_insert_ne; done.
      - subst new_obls0. rewrite lookup_insert_ne; done.
    Qed.

    Lemma other_fork_step_pres_obls' τ R τs
      (OTHER: τs ≠ τ):
      preserved_by (fork_step_of τs) (fun δ => ps_obls δ !! τ = Some R /\ om_st_wf δ).
    Proof using.
      red. intros ?? [OB WF1] (?&?&STEP).
      split.
      2: { eapply wf_preserved_by_fork_step; eauto. red. eauto. }
      inversion STEP. subst. destruct δ1; simpl in *.
      subst new_obls0.
      rewrite lookup_insert_ne.
      2: { intros ->. destruct FRESH'.
           apply om_wf_dpo in WF1. rewrite WF1. 
           by eapply elem_of_dom. }
      rewrite lookup_insert_ne; done. 
    Qed.  

    (* Context `(STEP: om_trans δ1 τ δ2). *)
    Context (δ1 δ2: ProgressState).    
    Context (WF1: om_st_wf δ1).

    Lemma om_step_wf_dom τ (LOC_STEP: loc_step δ1 τ δ2):
      τ ∈ dom $ ps_obls δ1.
    Proof using WF1.
      enough (τ ∈ dom $ ps_obls δ1 \/ τ ∈ dom $ ps_phases δ1 \/
              is_Some (ps_obls δ1 !! τ) \/ is_Some (ps_phases δ1 !! τ)) as IN.
      { rewrite -!elem_of_dom in IN. rewrite om_wf_dpo in IN; eauto. tauto. }
      inv_loc_step LOC_STEP; eauto.
    Qed.

  End MoreWF.

  Lemma signal_false_between δ1 δ2 δ' s l n m τ
    (F1: ps_sigs δ1 !! s = Some (l, false))
    (F2: ps_sigs δ2 !! s = Some (l, false))
    (STEPS1: nsteps (obls_any_step_of τ) n δ1 δ')
    (STEPS2: nsteps (obls_any_step_of τ) m δ' δ2):
    ps_sigs δ' !! s = Some (l, false).
  Proof using.
    forward eapply pres_by_rel_implies_rep.
    { apply pres_by_loc_fork_steps_implies_any_pres.
      - apply (loc_step_sig_st_le_pres s).
      - apply fork_step_sig_st_le_pres. }    
    intros SIG1. red in SIG1. specialize_full SIG1.
    2: { apply STEPS1. }
    { rewrite F1. reflexivity. } 

    forward eapply pres_by_rel_implies_rep.
    { apply pres_by_loc_fork_steps_implies_any_pres.
      - apply (loc_step_sig_st_le_pres s).
      - apply fork_step_sig_st_le_pres. }    
    intros SIG2. red in SIG2. specialize_full SIG2.
    2: { apply STEPS2. }
    { reflexivity. }
    rewrite F2 in SIG2.

    destruct (ps_sigs δ' !! s) as [[??]| ]; try done.
    simpl in SIG1, SIG2. destruct SIG1, SIG2; subst.
    destruct b; tauto.
  Qed.

  (* TODO: rephrase in terms of preserved_by? *)
  Lemma expected_signal_created_before δ1 δ2 τ n sid l
    (NSTEPS: nsteps (loc_step_with τ) n δ1 δ2)
    (* (NSTEPS: nsteps (loc_step_ex) n δ1 δ2) *)
    (SIG2: ps_sigs δ2 !! sid = Some (l, false))
    (LT2: lt_locale_obls l τ δ2):
    ps_sigs δ1 !! sid = Some (l, false).
  Proof using.
    clear WF VALID SET_BEFORE_SPEC LVL_WF set_before.
    assert (sid ∉ default ∅ (ps_obls δ2 !! τ)) as NO2.
    { intros IN2. 
      destruct (ps_obls δ2 !! τ) eqn:OBLS2; [| done]. simpl. 
      do 2 red in LT2. specialize (LT2 l).
      rewrite OBLS2 in LT2. simpl in LT2.
      specialize_full LT2.
      2: { by apply strict_ne in LT2. }
      apply extract_Somes_gset_spec.
      apply elem_of_map. eexists. split; eauto.
      by rewrite SIG2. }
    clear LT2. generalize dependent δ2. induction n.
    { by intros ? ->%nsteps_0. }
    
    intros δ2 (δ' & STEPS & STEP)%rel_compose_nsteps_next SIG2 NO2.
    forward eapply (loc_step_sig_st_le_pres sid).
    intros LE'. red in LE'. specialize_full LE'; [| eauto |]. 
    { reflexivity. }
    { red. eauto. }
    rewrite SIG2 in LE'.

    assert (ps_sigs δ' !! sid = Some (l, false)) as SIG'.
    { destruct (ps_sigs δ' !! sid) as [[??]| ] eqn:SIG'.
      { simpl in LE'. destruct LE' as [??]. subst. destruct b; tauto. }
      clear dependent δ1. 
      red in STEP.
      inv_loc_step STEP; destruct δ'; simpl in *; subst.
      all: try by rewrite SIG2 in SIG'.
      + subst new_sigs0. rewrite lookup_insert_ne in SIG2.
        { by rewrite SIG2 in SIG'. }
        intros ->. subst new_obls0.
        destruct NO2. rewrite lookup_insert. simpl. set_solver.
      + subst new_sigs0. rewrite lookup_insert_ne in SIG2.
        { by rewrite SIG2 in SIG'. }       
        intros ->. by rewrite SIG' in SIG. }
    clear LE'. 

    eapply IHn; eauto.
    destruct (ps_obls δ' !! τ) eqn:OBLS'; [| done]. simpl. intros IN'.
    inv_loc_step STEP; destruct δ'; simpl in *; subst.
    all: try by rewrite OBLS' in NO2. 
    + subst new_sigs0 new_obls0.
      destruct NO2. subst cur_loc_obls0. rewrite OBLS' lookup_insert. set_solver.
    + subst new_sigs0 new_obls0.
      subst cur_loc_obls0.
      destruct (decide (x = sid)) as [-> | ?].
      { rewrite lookup_insert in SIG2. done. }
      rewrite lookup_insert_ne in SIG2; [| done].
      destruct NO2. rewrite OBLS'. simpl. rewrite lookup_insert. simpl. set_solver.
  Qed.

  (* (* TODO: rephrase in terms of preserved_by? *) *)
  (* Lemma expected_signal_created_before δ1 δ2 τ n sid l *)
  (*   (NSTEPS: nsteps (loc_step_with τ) n δ1 δ2) *)
  (*   (* (NSTEPS: nsteps (loc_step_ex) n δ1 δ2) *) *)
  (*   (SIG2: ps_sigs δ2 !! sid = Some (l, false)) *)
  (*   (LT2: lt_locale_obls l τ δ2): *)
  (*   ps_sigs δ1 !! sid = Some (l, false). *)
  (* Proof using. *)
  (*   clear WF VALID SET_BEFORE_SPEC LVL_WF set_before. *)
  (*   assert (sid ∉ default ∅ (ps_obls δ2 !! τ)) as NO2. *)
  (*   { intros IN2.  *)
  (*     destruct (ps_obls δ2 !! τ) eqn:OBLS2; [| done]. simpl.  *)
  (*     do 2 red in LT2. specialize (LT2 l). *)
  (*     rewrite OBLS2 in LT2. simpl in LT2. *)
  (*     specialize_full LT2. *)
  (*     2: { by apply strict_ne in LT2. } *)
  (*     apply extract_Somes_gset_spec. *)
  (*     apply elem_of_map. eexists. split; eauto. *)
  (*     by rewrite SIG2. } *)
  (*   clear LT2. generalize dependent δ2. induction n. *)
  (*   { by intros ? ->%nsteps_0. } *)
    
  (*   intros δ2 (δ' & STEPS & STEP)%rel_compose_nsteps_next SIG2 NO2. *)
  (*   forward eapply (loc_step_sig_st_le_pres sid). *)
  (*   intros LE'. red in LE'. specialize_full LE'; [| eauto |].  *)
  (*   { apply sig_st_le_refl. } *)
  (*   { red. eauto. } *)
  (*   rewrite SIG2 in LE'. *)

  (*   assert (ps_sigs δ' !! sid = Some (l, false)) as SIG'. *)
  (*   { destruct (ps_sigs δ' !! sid) as [[??]| ] eqn:SIG'. *)
  (*     { simpl in LE'. destruct LE' as [??]. subst. destruct b; tauto. } *)
  (*     clear dependent δ1.  *)
  (*     red in STEP. *)
  (*     inv_loc_step STEP; destruct δ'; simpl in *; subst. *)
  (*     + by rewrite SIG2 in SIG'. *)
  (*     + by rewrite SIG2 in SIG'. *)
  (*     + subst new_sigs0. rewrite lookup_insert_ne in SIG2. *)
  (*       { by rewrite SIG2 in SIG'. } *)
  (*       intros ->. subst new_obls0. *)
  (*       destruct NO2. rewrite lookup_insert. simpl. set_solver. *)
  (*     + subst new_sigs0. rewrite lookup_insert_ne in SIG2. *)
  (*       { by rewrite SIG2 in SIG'. }        *)
  (*       intros ->. by rewrite SIG' in SIG. *)
  (*     + by rewrite SIG2 in SIG'. *)
  (*     + by rewrite SIG2 in SIG'. } *)
  (*   clear LE'.  *)

  (*   eapply IHn; eauto. *)
  (*   destruct (ps_obls δ' !! τ) eqn:OBLS'; [| done]. simpl. intros IN'. *)
  (*   inv_loc_step STEP; destruct δ'; simpl in *; subst.  *)
  (*   + by rewrite OBLS' in NO2.  *)
  (*   + by rewrite OBLS' in NO2. *)
  (*   + subst new_sigs0 new_obls0. *)
  (*     destruct NO2. subst cur_loc_obls0. rewrite OBLS' lookup_insert. set_solver. *)
  (*   + subst new_sigs0 new_obls0. *)
  (*     subst cur_loc_obls0. *)
  (*     destruct (decide (x = sid)) as [-> | ?]. *)
  (*     { rewrite lookup_insert in SIG2. done. } *)
  (*     rewrite lookup_insert_ne in SIG2; [| done]. *)
  (*     destruct NO2. rewrite OBLS'. simpl. rewrite lookup_insert. simpl. set_solver. *)
  (*   + rewrite OBLS' in NO2. done. *)
  (*   + rewrite OBLS' in NO2. done.  *)
  (* Qed. *)

  Definition asg_bound sid πb δ :=
    (* map_Forall (fun obls_ => sid ∉ obls_) (ps_obls δ) \/ *)
    (exists l, ps_sigs δ !! sid = Some (l, true)) \/
    exists τ π, sid ∈ default ∅ (ps_obls δ !! τ) /\
            ps_phases δ !! τ = Some π /\
            phase_le πb π.

  Lemma loc_step_pres_asg_bound sid πb:
    preserved_by (loc_step_ex) (fun δ => asg_bound sid πb δ /\ om_st_wf δ).
  Proof using.
    clear set_before WF SET_BEFORE_SPEC LVL_WF VALID.

    red. intros δ1 δ2 [AB WF1] STEP'.
    pose proof STEP' as [τ STEP]. 
    split.
    2: { eapply wf_preserved_by_loc_step; eauto. } 

    destruct AB as [SET | AB].
    { destruct SET as [l SID]. red.
      left. eapply (loc_step_sig_st_le_pres sid) in STEP'.
      2: { reflexivity. }
      rewrite SID in STEP'.
      destruct (ps_sigs δ2 !! sid) as [[??]|] eqn:ST; try done.
      simpl in STEP'. destruct STEP' as [-> ?]. 
      destruct b; try done. eauto. }

    red.
    pose proof (@next_sig_id_fresh (default ∅ (ps_obls δ1 !! τ) ∪ (dom $ ps_sigs δ1))) as FRESH. 
    inv_loc_step STEP; destruct δ1; try (right; done).
    - right. subst new_obls0.
      destruct AB as (?&?&?&PH&?).
      destruct (decide (sid = s0)) as [-> | OLD].
      + destruct FRESH. 
        apply elem_of_union. right. 
        eapply om_wf_obls_are_sigs; eauto. simpl.
        eapply flatten_gset_spec. eexists. split; eauto.
        eapply elem_of_map_img; eauto.
        apply om_wf_dpo in WF1.
        apply mk_is_Some, elem_of_dom in PH.
        red in WF1. rewrite WF1 in PH. simpl in PH.
        apply elem_of_dom in PH as [? OB].
        exists x0. rewrite OB. done.
      + subst new_ps. 
        destruct (decide (x0 = τ)) as [-> | NEQ].
        * exists τ. rewrite lookup_insert. simpl. eexists. split; eauto.
          set_solver.
        * exists x0. rewrite lookup_insert_ne; [| done]. eauto.
    - simpl in *.
      destruct (decide (x = sid)) as [-> | NEQ].
      { left. subst new_sigs0. rewrite lookup_insert. eauto. }
      right. move AB at bottom. destruct AB as (?&?&?&?&?).
      destruct (decide (x0 = τ)) as [-> | NEQ'].
      + exists τ. rewrite lookup_insert. simpl. eexists. split; eauto.
        set_solver.
      + exists x0. rewrite lookup_insert_ne; [| done]. eauto.
  Qed.

  Lemma fork_step_pres_asg_bound sid πb τ:
    preserved_by (fork_step_of τ) (fun δ => asg_bound sid πb δ /\ om_st_wf δ).
  Proof using.
    clear tr set_before WF SET_BEFORE_SPEC LVL_WF VALID.

    red. intros δ1 δ2 [AB WF1] STEP.
    split.
    2: { eapply wf_preserved_by_fork_step; eauto. }

    destruct AB as [SET | AB].
    { destruct SET as [l SID]. red.
      left. eapply (fork_step_sig_st_le_pres _ sid) in STEP.
      2: { reflexivity. }
      rewrite SID in STEP.
      destruct (ps_sigs δ2 !! sid) as [[??]|] eqn:ST; try done.
      simpl in STEP. destruct STEP as [-> ?]. 
      destruct b; try done. eauto. }

    destruct STEP as (?&?&STEP). inversion STEP; subst. red. right.
    move AB at bottom. destruct AB as (?&?&?&PH&?).
    destruct δ1; try (right; done); simpl in *.
    subst new_obls0 cur_obls0 obls' new_phases0. 
    destruct (decide (x1 = τ)) as [-> | NEQ'].
    2: { exists x1, x2. rewrite lookup_insert_ne.
         2: { intros <-. destruct FRESH'. by apply elem_of_dom. }
         rewrite lookup_insert_ne; [| done].
         rewrite lookup_insert_ne. 
         2: { intros <-. destruct FRESH'. by apply elem_of_dom. }
         rewrite lookup_insert_ne; [| done].
         eauto. }
    rewrite LOC_PHASE in PH. inversion PH. subst x2. 
    destruct (decide (sid ∈ cur_obls ∩ x0)).
    { exists x. rewrite !lookup_insert. simpl. eexists. split; eauto.
      split; eauto. etrans; eauto. apply phase_lt_fork. }
    exists τ. eexists. rewrite lookup_insert_ne.
    2: { intros ->. destruct FRESH'. by apply elem_of_dom. }
    rewrite lookup_insert. simpl. 
    rewrite lookup_insert_ne.
    2: { intros ->. destruct FRESH'. by apply elem_of_dom. }
    rewrite lookup_insert. simpl.
    split; [set_solver|  ]. split; eauto.
    etrans; eauto. apply phase_lt_fork.
  Qed. 

  Lemma signal_created_never_set sid i
    (CR: sid ∈ dom $ from_option ps_sigs ∅ (tr S!! i))
    (NOT_SET: ¬ exists j, sig_is_set_at sid j):
    never_set_after sid i.
  Proof using VALID.
    red. intros k LEik [? KTH].
    destruct (tr S!! i) eqn:ITH; [| done]. simpl in CR.
    rewrite /sig_val_at. rewrite KTH. simpl. 
    forward eapply sig_st_le_lookup_helper with (s := sid); eauto.
    apply elem_of_dom in CR as [[? b] Sm]. rewrite Sm.
    destruct (ps_sigs x !! sid) as [[? b']| ] eqn:Sk; try done. simpl.
    destruct b'; [| done].
    edestruct NOT_SET. exists k. red. rewrite KTH /= Sk. done.
  Qed.

  Lemma sig_is_set_at_after sid i
    (SET: sig_is_set_at sid i):
    forall j, i <= j -> is_Some (tr S!! j) -> sig_is_set_at sid j.
  Proof using VALID.
    intros ? LE [δj JTH].
    red. rewrite JTH. simpl.
    red in SET. destruct (tr S!! i) as [δi| ] eqn:ITH; [| done]. simpl in SET.
    eapply sig_st_le_lookup_helper with (s := sid) in LE; eauto.
    destruct (ps_sigs δi !! sid) as [[??]| ] eqn:Si; [| done].
    destruct (ps_sigs δj !! sid) as [[??]| ] eqn:Sj; [| done].
    simpl in *. destruct b, b0; tauto.
  Qed.

  (* TODO: move *)
  Ltac by_classical_contradiction cname :=
    match goal with
    | |- ?goal => destruct (Classical_Prop.classic (goal)) as [| cname]; first done; exfalso
    end.

  Lemma sig_st_le_dom_sub δ1 δ2
    (SIG_LE: forall sid, sig_st_le (ps_sigs δ1 !! sid) (ps_sigs δ2 !! sid)):
    dom $ ps_sigs δ1 ⊆ dom $ ps_sigs δ2.
  Proof using.
    apply elem_of_subseteq. intros s [[??] SIG]%elem_of_dom.
    specialize (SIG_LE s). rewrite SIG in SIG_LE.
    destruct (ps_sigs δ2 !! s) eqn:SIG2; [| done].
    eapply elem_of_dom; eauto.
  Qed.

  (* TODO: move *)
  Lemma update_cps_same_sigs δ cps':
    ps_sigs (update_cps cps' δ) = ps_sigs δ.
  Proof using. by destruct δ. Qed.

  Lemma owm_loc_step_ms_le
  (πτ : Phase)
  (τ : Locale)
  (τs : mlabel ObligationsModel)
  (n : nat)
  (s : SignalId)
  (δk : ProgressState)
  (PH : ps_phases δk !! τ = Some πτ)
  (NTH : tr S!! n = Some δk)
  (NEVER_SET : never_set_after s n)
  (MIN : minimal_in_prop tr_sig_lt (s, n)
          (λ sn, is_Some (tr S!! sn.2) /\ never_set_after sn.1 sn.2 ∧ n ≤ sn.2))
  (OWNER : s ∈ default ∅ (ps_obls δk !! τ))
  (δ'' : ProgressState)
  (k : nat)
  (IDTH' : tr S!! (n + 1) = Some δ'')
  (BOUND : S k ≤ LIM_STEPS)
  (ls : Level)
  (SIGsn : ps_sigs δk !! s = Some (ls, false))
  (SIGsn' : ps_sigs δ'' !! s = Some (ls, false))
  (δ' mb : ProgressState)
  (STEPS : nsteps (λ p1 p2 : ProgressState, loc_step_ex p1 p2) k δk δ')
  (STEP : loc_step_ex δ' mb)
  (SIG_LE'' : ∀ sid, sig_st_le (ps_sigs mb !! sid) (ps_sigs δ'' !! sid))
  (SF : ps_sigs mb !! s = Some (ls, false))
  (SIG' : ps_sigs δ' !! s = Some (ls, false))
  :
  ms_le deg_le (PF' set_before (phase_ge πτ) ((LIM_STEPS + 2) * n + S k) mb)
    (PF' set_before (phase_ge πτ) ((LIM_STEPS + 2) * n + k) δ').
  Proof using VALID WF SET_BEFORE_SPEC.
    clear LVL_WF.
    destruct STEP as [τc STEP]. 
    
    eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
    { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
    
    assert (ps_phases δ' !! τ = Some πτ) as PHδ'.
    { eapply loc_steps_rep_phase_exact_pres; eauto. }
    
    replace πτ with (default π0 (ps_phases δ' !! τ)).
    2: { rewrite PHδ'. done. }

    assert (om_st_wf δ') as WF'. 
    { eapply pres_by_loc_step_implies_rep.
      3: { apply STEPS. }
      { apply wf_preserved_by_loc_step. }
      eauto. }

    destruct (decide (τc = τ)) as [-> | NEQ]. 
    2: { eapply other_expect_ms_le; eauto.
         rewrite PHδ'.
         apply om_step_wf_dom in STEP; [rewrite -om_wf_dpo in STEP| ]; eauto.
         apply elem_of_dom in STEP as [π' PH']. rewrite PH'. simpl.
         symmetry. eapply om_wf_ph_disj; eauto. }
    
    apply min_owner_expect_ms_le.
    3: { rewrite PHδ'. simpl. eapply elem_of_map_img. eauto. }
    2: done.

    intros sid π d EXP. simpl.
    inversion EXP. subst.
    rewrite PHδ' in LOC_PHASE. inversion LOC_PHASE. subst π__max.
    
    enough (set_before sid > n) as GT. 
    { apply PeanoNat.Nat.le_succ_l in GT. 
      apply Nat.le_sum in GT as [u EQ]. rewrite EQ. lia. }
        
    move NEVER_SET at bottom. red in NEVER_SET.
    specialize (NEVER_SET _ ltac:(reflexivity)).
    rewrite /sig_val_at in NEVER_SET. rewrite NTH in NEVER_SET. simpl in NEVER_SET. 

    assert (s ∈ default ∅ (ps_obls δ' !! τ)) as OBL'.
    { unshelve eapply (pres_by_rel_implies_rep _ _ _ _ _ _) in STEPS.
      { apply (loc_step_pres_asg_bound s πτ). }
      2: { split.
           2: { eapply WF; eauto. }
           red. right. exists τ, πτ. set_solver. }           
      simpl in STEPS. destruct STEPS as [ASG' _]. red in ASG'.
      destruct ASG' as [[? ?] | PH']; [congruence| ].
      destruct PH' as (τ' & π' & IN' & PH' & LE').
      destruct (decide (τ' = τ)) as [| NEQ]; [congruence| ].
      eapply om_wf_ph_disj in NEQ; eauto.
      eapply phases_disj_not_le in LE'; [done| ].
      symmetry. eapply NEQ; eauto. }

    pose proof OBLS_LT as OL. 
    specialize (OBLS_LT ls). specialize_full OBLS_LT.
    { apply extract_Somes_gset_spec.
      destruct (ps_obls δ' !! τ) as [obs| ] eqn:OBLS'; [| set_solver].
      simpl in OBL'. simpl. apply elem_of_map. eexists. split; eauto.
      rewrite SIG'. done. }
    
    red. destruct (Nat.lt_ge_cases n (set_before sid)) as [?|GE]; [done| ].

    assert (exists i, sig_is_set_at sid i) as EVsid.
    { by_classical_contradiction X.

      specialize (SIG_LE'' sid). rewrite update_cps_same_sigs SIG in SIG_LE''.
      destruct (ps_sigs δ'' !! sid) as [[??]| ] eqn:SIG''; [| done].
      simpl in SIG_LE''. destruct SIG_LE'' as [-> ?]. 
      
      forward eapply (signal_created_never_set _ (n + 1)); eauto.
      { rewrite IDTH'. simpl. eapply elem_of_dom; eauto. }
      intros NEVER_SET'.
      
      move MIN at bottom. red in MIN.      
      specialize (MIN (sid, n + 1)).
      specialize (MIN ltac:(split; eauto; split; [done| simpl; lia])). 
      
      eapply never_set_after_eq_false in NEVER_SET'; [| reflexivity| eauto].
      destruct NEVER_SET' as (?&NCsig).
      rewrite /tr_sig_lt /MR in MIN. simpl in MIN.
      rewrite NTH in MIN. simpl in MIN. rewrite IDTH' in MIN. simpl in MIN.
      
      rewrite NCsig SIGsn in MIN. simpl in MIN.
      rewrite SIG'' in NCsig. inversion NCsig. by subst. }
       
    generalize (SET_BEFORE_SPEC sid). rewrite /sb_prop. intros [? | SETsid]; [tauto| ].
    destruct SETsid as (f & SETf & LEf_sb).
    forward eapply sig_is_set_at_after with (j := n).
    { eauto. }
    { lia. }
    { eauto. }
    rewrite /sig_is_set_at NTH /=. destruct (ps_sigs δk !! sid) as [[??]|] eqn:SIDn; [| done].
    simpl. intros <-.
    unshelve eapply (pres_by_rel_implies_rep _ _ _ _ _ _) in STEPS.
    { apply loc_step_sig_st_le_pres. }
    2: { simpl. eapply reflexive_eq. symmetry. apply SIDn. }
    simpl in STEPS. rewrite SIG in STEPS. tauto. 
  Qed.

  Lemma owm_om_trans_ms_le πτ τ τs n s δ0
    (NTH: tr S!! n = Some δ0)
    (PH: ps_phases δ0 !! τ = Some πτ)
    (NEVER_SET : never_set_after s n)
    (MIN: minimal_in_prop tr_sig_lt (s, n) 
            (λ sn, is_Some (tr S!! sn.2) /\ never_set_after sn.1 sn.2 /\ n <= sn.2))
    (OWNER: s ∈ default ∅ (ps_obls δ0 !! τ))
    (LBL: tr L!! n = Some τs):
    let b := bool_decide (τs = τ) in
    let R := if b then ms_lt deg_le else ms_le deg_le in
    R (TPF πτ (S n)) (TPF πτ n).
  Proof using VALID WF SET_BEFORE_SPEC.
    clear LVL_WF. 
    forward eapply (proj1 (label_lookup_states' _ _)); eauto. intros [δ' NTH'] b R.
    
    eapply om_trans_ms_rel with (bd := b); auto.
    { intros * ??? B ?.
      rewrite Nat.add_succ_r Nat.add_0_r.
      apply state_label_lookup in H as (NTH_&?&LBL_).
      rewrite LBL in LBL_. inversion LBL_. subst τ0. 
      rewrite NTH in NTH_. inversion NTH_. subst δ0. 
      destruct B as (?&?&B). inversion B. subst. 
      assert (ps_phases mb !! τ = Some πτ) as PH'.
      { eapply loc_steps_rep_phase_exact_pres; eauto. }

      subst b. rewrite bool_decide_decide. destruct decide; subst. 
      - eapply burns_cp_own_ms_lt; eauto.
        do 2 red. congruence. 
      - eapply burns_cp_ms_le; eauto. }
    
    (* TODO: extract the lemma below? *)
    
    clear δ' NTH'.
    intros τ' IDTHl. 
    red. intros δk δk' mb mf k ITH BOUND NSTEPS BSTEP FSTEP.
    apply state_label_lookup in ITH as (IDTH & IDTH' & _). 
    rewrite NTH in IDTH. inversion IDTH. subst δ0. clear IDTH. 
    rewrite LBL in IDTHl. inversion IDTHl. subst τ'. clear IDTHl.

    pose proof (never_set_after_eq_false _ _ NEVER_SET _ _ ltac:(reflexivity) NTH) as X.
    destruct X as (ls&SIGsn).
    pose proof (never_set_after_eq_false _ _ NEVER_SET (n + 1) _ ltac:(lia) IDTH') as X.
    destruct X as (?&SIGsn').

    forward eapply sig_st_le_lookup_helper with (i := n) (j := n + 1) (s := s); eauto; [lia| ].
    rewrite SIGsn SIGsn'. simpl. intros [<- _].   

    assert (forall sid, sig_st_le (ps_sigs mb !! sid) (ps_sigs δk' !! sid)) as SIG_LE''.
    { intros.
      etrans.
      { eapply loc_step_sig_st_le_pres; [reflexivity| ].
        red. eexists. red. left. eauto. }
      inversion FSTEP as [? F| ]; subst.
      2: { reflexivity. }
      destruct F as (?&?&F).
      eapply fork_step_sig_st_le_pres; [reflexivity| ].
      eexists. eauto. }      

    apply clos_refl_nsteps in FSTEP as [r FSTEP]. 
    forward eapply signal_false_between; [apply SIGsn | apply SIGsn'| ..].
    { eapply nsteps_mono; [| apply NSTEPS].
      do 2 red. rewrite /obls_any_step_of. eauto. }
    { apply rel_compose_nsteps_next'. eexists. split. 
      - red. left. red. exists τs. red. left. eauto.
      - eapply nsteps_mono; [| apply FSTEP].
        do 2 red. rewrite /obls_any_step_of. eauto. }
    intros SIGmb. 
    
    clear dependent mf. rename δk' into δ''.
    
    generalize dependent mb. induction k.
    { intros ? ->%nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    intros mb (δ' & STEPS & STEP)%nsteps_inv_r SIG_LE'' SF.

    assert (ps_sigs δ' !! s = Some (ls, false)) as SIG'.
    { eapply signal_false_between; [apply SIGsn | apply SF| ..].
      - eapply nsteps_mono; [| apply STEPS].
        do 2 red. rewrite /obls_any_step_of. eauto.
      - apply nsteps_1. left. eauto.
      (* TODO: get rid of it *)
      Unshelve. exact τ. 
    }
    specialize (IHk ltac:(lia) _ STEPS).
    specialize_full IHk.
    2: done.
    { intros. etrans; [| by apply SIG_LE''].
      eapply loc_step_sig_st_le_pres; eauto. reflexivity. }

    etrans; eauto.
    eapply owm_loc_step_ms_le; eauto. 
  Qed.

  Lemma loc_step_pres_phase_eq τ π:
    preserved_by loc_step_ex (fun δ => ps_phases δ !! τ = Some π).
  Proof using.
    red. intros ?? PH STEP.
    eapply loc_step_phases_pres in STEP; [| reflexivity].
    by rewrite STEP.
  Qed.
    
  Lemma other_fork_step_pres_phase_eq τ π τs
    (OTHER: τs ≠ τ):
    preserved_by (fork_step_of τs) (fun δ => ps_phases δ !! τ = Some π).
  Proof using.
    red. intros ?? PH (?&?&STEP).
    inversion STEP. subst. destruct δ1; simpl in *.
    subst new_phases0.
    rewrite lookup_insert_ne.
    2: { intros ->. destruct FRESH'. by eapply elem_of_dom. }
    rewrite lookup_insert_ne; done. 
  Qed.  
    

  Definition s_ow (s: SignalId) (i: nat) := 
    let π := 
      δ ← tr S!! i;
      let owners := dom $ filter (fun '(_, obs) => s ∈ obs) (ps_obls δ) in
      let ow_phs := extract_Somes_gset $ set_map (fun τ => ps_phases δ !! τ) owners: gset Phase in
      ow ← gset_pick ow_phs;
      mret ow
    in default π0 π.

  Lemma S_OWNER s i π τ δ
    (ITH: tr S!! i = Some δ)
    (PH: ps_phases δ !! τ = Some π)
    (OW: s ∈ default ∅ (ps_obls δ !! τ)):
    s_ow s i = π.
  Proof using WF.
    clear dependent set_before LVL_WF VALID. 
    intros. rewrite /s_ow. rewrite ITH. simpl.
    destruct (ps_obls δ !! τ) as [obls| ] eqn:OBLS; [| done]. simpl in OW.
    erewrite <- map_difference_union with (m2 := (ps_obls δ)).
    2: { eapply map_singleton_subseteq_l; eauto. }
    rewrite map_filter_union.
    2: { apply map_disjoint_dom. set_solver. }
    rewrite map_filter_singleton decide_True; [| done].
    rewrite (proj2 (map_filter_empty_iff _ _)).
    2: { red. intros τ' ? LOC' IN'.
         apply lookup_difference_Some in LOC'. destruct LOC' as [OBLS' ?%lookup_singleton_None].
         edestruct @om_wf_obls_disj; eauto.
         - by rewrite OBLS.
         - by rewrite OBLS'. }
    rewrite map_union_empty dom_singleton_L.
    rewrite set_map_singleton_L. rewrite PH.
    rewrite extract_Somes_gset_singleton. rewrite gset_pick_singleton.
    done.
  Qed.

  Definition asg_to_or_set s τ := 
    fun δ => s ∈ default ∅ (ps_obls δ !! τ) \/ from_option snd false (ps_sigs δ !! s) = true.

  Lemma asg_to_or_set_pres_loc s τ:
    preserved_by loc_step_ex (fun δ => asg_to_or_set s τ δ /\ om_st_wf δ).
  Proof using.
    clear dependent WF VALID set_before LVL_WF.
    red. intros δ1 δ2 [P1 WF1] [τs STEP].
    split.
    2: { eapply wf_preserved_by_loc_step; eauto. red. eauto. }
    red in P1. destruct P1 as [ASG | SET].
    2: { destruct (ps_sigs δ1 !! s) as [[??]|] eqn:SIG; [| done]. simpl in SET. subst.
         pattern τs in STEP. apply ex_intro in STEP.
         eapply (loc_step_sig_st_le_pres s) in STEP; [| reflexivity].
         rewrite SIG in STEP. destruct (ps_sigs δ2 !! s) as [[??]|] eqn:SIG'; [| done].
         simpl in STEP. destruct b; [| tauto].
         right. by rewrite SIG'. }

    destruct (ps_obls δ1 !! τ) as [obs |] eqn:OBLS; [| done].
    destruct (decide (τs = τ)) as [-> | ?].
    2: { left. eapply other_loc_step_pres_obls in STEP as [OBLS' ?]; eauto.
         by rewrite OBLS'. }
    add_case (ps_obls δ2 = ps_obls δ1) SAME_OBLS.
    { left. congruence. }
    inv_loc_step STEP; destruct δ1; try by apply SAME_OBLS.
    - red. subst new_ps new_obls0. simpl. rewrite lookup_insert. simpl.
      subst cur_loc_obls0. simpl. left. rewrite OBLS. set_solver.
    - red. subst new_ps. simpl. subst new_obls0 new_sigs0. simpl.
      rewrite lookup_insert. simpl. subst cur_loc_obls0. simpl.
      destruct (decide (s = x)) as [-> | ?].
      + right. by rewrite lookup_insert.
      + left. rewrite OBLS. set_solver.
  Qed.
  
  Lemma asg_to_or_set_pres_fork s τ τs
    (OTHER: τ ≠ τs):
    preserved_by (fork_step_of τs) (fun δ => asg_to_or_set s τ δ /\ om_st_wf δ).
  Proof using.
    red. intros δ1 δ2 [P1 WF1] STEP.
    split; [| eapply wf_preserved_by_fork_step; eauto].
    destruct P1 as [ASG | SIG].
    - left. destruct (ps_obls δ1 !! τ) eqn:OBLS; [| done].
      eapply other_fork_step_pres_obls' in STEP; eauto.
      by destruct STEP as [-> ?].
    - right. destruct (ps_sigs δ1 !! s) as [[??]|] eqn:SG; [| done].
      eapply (fork_step_sig_st_le_pres _ s) in STEP; [| reflexivity].
      simpl in SIG. subst. rewrite SG in STEP. 
      destruct (ps_sigs δ2 !! s) as [[??]|]; try done.
      simpl in STEP. destruct b; tauto.
  Qed. 

  Lemma obls_phases_pres_helper i j δi δj (* obs π *)
    τ
    (* (OBLS: ps_obls δi !! τ = Some obs) *)
    (* (PH: ps_phases δi !! τ = Some π) *)
    (LE: i <= j)
    (ITH: tr S!! i = Some δi) (JTH: tr S!! j = Some δj)
    (OTHER: ∀ k, i <= k < j → tr L!! k ≠ Some τ):
    (* ps_obls δj !! τ = ps_obls δi !! τ /\ *)
    (forall s, asg_to_or_set s τ δi -> asg_to_or_set s τ δj) /\
    (forall π, ps_phases δi !! τ = Some π -> ps_phases δj !! τ = Some π).
  Proof using WF VALID.
    split.
    - intros s ASG. 
      forward eapply (pres_by_valid_trace_strong tr i j); eauto.
      { apply asg_to_or_set_pres_loc. }
      3: { intros ?? DOM L'.
           specialize (OTHER _ DOM). rewrite L' in OTHER.
           pattern τ0 in OTHER. apply OTHER. }
      2: { rewrite ITH. simpl. split; eauto. }
      { simpl. intros. apply asg_to_or_set_pres_fork. congruence. }
      rewrite JTH. simpl. tauto.  
    - intros π PH. 
      forward eapply (pres_by_valid_trace_strong tr i j); eauto. 
      2: { apply (other_fork_step_pres_phase_eq τ π). }
      { eapply loc_step_pres_phase_eq. }
      { by rewrite ITH. }
      { intros. simpl. intros ->. edestruct OTHER; eauto. }
      rewrite JTH. simpl. done. 
  Qed.

  Lemma min_tr_sig_after s i j
    (MIN: minimal_in_prop tr_sig_lt (s, i)
            (λ sn, is_Some (tr S!! sn.2) /\ never_set_after sn.1 sn.2 ∧ i ≤ sn.2))
    (AFTER: i <= j): minimal_in_prop tr_sig_lt (s, j)
                      (λ sn, is_Some (tr S!! sn.2) /\ never_set_after sn.1 sn.2 ∧ j ≤ sn.2).
  Proof using VALID.
    red. intros [s' k]. simpl. intros (CTH & NEVERj & LEjk) SIG_LTk.
    apply (MIN (s', k)).
    { split; eauto. split; simpl; [| lia]. done. }
    
    revert SIG_LTk.
    rewrite /tr_sig_lt /MR /lvl_opt_lt /lvl_at.
    destruct (tr S!! k) as [δk| ] eqn:KTH; [| done]. simpl.
    destruct (ps_sigs δk !! s') as [[l' b']| ] eqn:SIGk; [| done]. simpl.
    destruct (tr S!! j) as [δj| ] eqn:JTH; rewrite JTH; simpl in *. 
    2: { intros.
         eapply mk_is_Some, @state_lookup_prev in KTH; eauto.
         rewrite JTH in KTH. by inversion KTH. }
    pose proof JTH as ITH%mk_is_Some. eapply state_lookup_prev in ITH as [δi ITH]; eauto.
    rewrite ITH. simpl. 
    forward eapply sig_st_le_lookup_helper with (s := s) as SIG_LE.
    { apply AFTER. }
    all: eauto. 
    destruct (ps_sigs δi !! s) as [[??]| ] eqn:SIGi, (ps_sigs δj !! s) as [[??]| ]eqn:SIGj; simpl in *; try done. 
    destruct SIG_LE. congruence.
  Qed. 
  
  (* Lemma pres_by_valid_trace_strong (tr: obls_trace) i j (P: nat -> Prop) *)
  (*   (LE: i <= j) *)
  (*   (VALID: obls_trace_valid tr) *)
  (*   (PRES: forall i τ, P i -> P (i + 1)) *)
  (*   (Pi: P i) *)
  (*   (Tij: forall k, i <= k < j -> exists τ, tr L!! k = Some τ /\ T τ) *)
  (*   : *)
  (*   P j. *)
  (* Proof using. *)
  (*   apply Nat.le_sum in LE as [d ->]. induction d. *)
  (*   { rewrite Nat.add_0_r. done. } *)
  (*   rewrite -plus_n_Sm. *)

  (*   rewrite -Nat.add_1_r. *)
  (*   specialize (Tij (i + d) ltac:(lia)). destruct Tij as (τid & Lid & Tid).  *)
  (*   eapply PRES; eauto.  *)
  (*   apply IHd. intros. *)
  (*   eapply mk_is_Some, label_lookup_prev with (j := k) in Lid as [τk Tk]; [| lia]. *)
  (*   eexists. split; eauto. eapply  *)
    
    
  (*   eapply Tij; eauto. lia. *)
  (*   - eapply Tij; eauto.   *)


  (*   destruct (tr S!! S (i + d)) eqn:NEXT; [| done]. simpl. *)
  (*   forward eapply (proj1 (next_state_lookup _ _)); eauto. *)
  (*   intros [[? CUR] [? LBL]]. *)
  (*   rewrite CUR in IHd. simpl in IHd. *)
  (*   forward eapply trace_valid_steps''; eauto. *)
  (*   { rewrite Nat.add_1_r. eauto. } *)
  (*   intros STEP. *)
  (*   pose proof (Tij (i + d) _ ltac:(lia) LBL). *)
  (*   eapply pres_by_loc_fork_steps_implies_om_trans; eauto. *)
  (*   2: { apply STEP. } *)
  (*   apply IHd. intros. eapply Tij; eauto. lia.   *)
  (* Qed. *)

  (* (* TODO: move *) *)
  (* Lemma pres_by_loc_fork_steps_implies_om_trans τ P *)
  (*   (PPRES: preserved_by (loc_step_with τ) P) *)
  (*   (FPRES: preserved_by_fork τ P) *)
  (*   : *)
  (*   preserved_by_om_trans τ P.  *)
  (* Proof using. *)
  (*   do 2 red. intros δ1 δ2 P1 STEP.  *)
  (*   red in STEP. destruct STEP as (?&PSTEP&FSTEP). *)
  (*   eapply pres_by_loc_step_implies_progress in PPRES.  *)
  (*   do 2 red in PPRES. specialize_full PPRES; eauto. *)
  (*   inversion FSTEP; subst; try done. *)
  (*   eapply FPRES; eauto.  *)
  (* Qed. *)


  Lemma next_step_rewind τ i δ0 j s δj
    (ITH: tr S!! i = Some δ0)
    (OBLS: s ∈ default ∅ (ps_obls δ0 !! τ))
    (UNSET: never_set_after s i)
    (MIN: minimal_in_prop tr_sig_lt (s, i)
            (λ ab : SignalId * nat, is_Some (tr S!! ab.2) /\ never_set_after ab.1 ab.2 /\ i <= ab.2))

    (LE: i <= j)
    (NOτ: forall k, i <= k < j -> tr L!! k ≠ Some τ)
    (* ms_le deg_le (TPF π j) (TPF π i). *)
    (OTF := λ i, TPF (s_ow s i) i)
    (JTH: tr S!! j = Some δj)
    :
      ms_le deg_le (OTF j) (OTF i) /\ s_ow s j = s_ow s i /\
      ps_phases δj !! τ = ps_phases δ0 !! τ /\
      s ∈ default ∅ (ps_obls δj !! τ).
  Proof using WF VALID SET_BEFORE_SPEC.
    clear LVL_WF.

    rewrite /OTF. 

    destruct (ps_obls δ0 !! τ) as [obs| ] eqn:OBLS0.
    2: { set_solver. }
    simpl in OBLS0.    

    pose proof OBLS0 as PH0%mk_is_Some%elem_of_dom.
    erewrite <- om_wf_dpo in PH0; eauto. apply elem_of_dom in PH0 as [π PH0].
    forward eapply S_OWNER; [apply ITH| ..]; eauto.
    { by rewrite OBLS0. }
    intros <-.

    generalize dependent δj. apply Nat.le_sum in LE as [d ->]. induction d.
    { rewrite Nat.add_0_r. intros.
      rewrite ITH in JTH. inversion JTH. subst.
      rewrite OBLS0. set_solver. }

    intros δj' JTH'.
    forward eapply state_lookup_prev with (j := i + d); eauto; [lia| ].
    intros [δj JTH]. 

    specialize_full IHd.
    { intros. apply NOτ. lia. }
    { eauto. }
    destruct IHd as (LE & OW_EQ & PH_EQ & ASGs).
    rewrite -OW_EQ -PH_EQ.

    rewrite -plus_n_Sm in JTH'. 
    pose proof JTH' as [τj LBLj]%mk_is_Some%label_lookup_states'.
    forward eapply pres_by_loc_fork_steps_implies_om_trans with (τ := τj).
    2: { eapply other_fork_step_pres_phase_eq. 
         intros ?. rewrite H in LBLj. eapply NOτ in LBLj; eauto. lia. }
    { apply loc_step_pres_phase_eq. }
    rewrite PH0 in PH_EQ. 
    move/(_ δj δj' PH_EQ) =>PH_EQ'. specialize_full PH_EQ'.
    { red. eapply trace_valid_steps''; eauto.
      rewrite -JTH'. f_equal. lia. }
    rewrite PH_EQ'.

    forward eapply pres_by_loc_fork_steps_implies_om_trans with (τ := τj).
    2: { eapply (asg_to_or_set_pres_fork s).
         apply not_eq_sym. intros ?. rewrite H in LBLj. eapply NOτ in LBLj; eauto. lia. }
    { apply asg_to_or_set_pres_loc. }
    move/(_ δj δj') =>ASG'. specialize_full ASG'.
    { split; [| by eapply WF; eauto].
      left. eauto. }
    { red. eapply trace_valid_steps''; eauto.
      rewrite -JTH'. f_equal. lia. }
    destruct ASG' as [[ASG' | SET'] WF'].
    2: { forward eapply never_set_after_eq_false with (i := S (i + d)); eauto.
         { lia. }
         intros [? SIGj']. by rewrite SIGj' in SET'. }

    forward eapply S_OWNER as OW_EQ'; eauto. rewrite plus_n_Sm in OW_EQ'.  
    repeat split; eauto.
    2: { congruence. }

    rewrite OW_EQ' OW_EQ.
    etrans; eauto. 
    
    replace (ms_le deg_le) with (if (bool_decide (τj = τ)) then ms_lt deg_le else ms_le deg_le).
    2: { rewrite bool_decide_eq_false_2; [done| ].
         intros ->. apply NOτ in LBLj; [done| ]. lia. }
    rewrite -plus_n_Sm. rewrite OW_EQ. 

    eapply owm_om_trans_ms_le; eauto.
    2: { eapply min_tr_sig_after; eauto. lia. }
    eapply never_set_after_after; [| apply UNSET]. lia. 
  Qed.

  Lemma fresh_phase_is_fork δ1 τ δ2 π
    (WF1: om_st_wf δ1)
    (STEP: om_trans δ1 τ δ2)
    (FRESH: π ∈ (map_img (ps_phases δ2): gset Phase) ∖ (map_img (ps_phases δ1): gset Phase)):
    exists π0, ps_phases δ1 !! τ = Some π0 /\ is_fork π0 π.
  Proof using.
    clear WF SET_BEFORE_SPEC LVL_WF VALID.
    red in STEP. destruct STEP as (δ' & PSTEP & FSTEP).
    
    forward eapply pres_by_loc_step_implies_progress.
    { apply loc_step_phases_pres. }
    intros PH_EQ. do 2 red in PH_EQ. specialize_full PH_EQ; eauto.
    { reflexivity. }
    red in PH_EQ. rewrite -PH_EQ in FRESH. 

    forward eapply pres_by_loc_step_implies_progress.
    { apply wf_preserved_by_loc_step. }
    intros WF'. do 2 red in WF'. specialize_full WF'; eauto.

    inversion FSTEP; [| set_solver].
    subst. destruct H as (?&?&FORK). inversion FORK. subst.
    destruct δ'. simpl in *.
    rewrite -PH_EQ. eexists. split; eauto. 
    revert FRESH. subst new_phases0. rewrite map_img_insert_L.
    rewrite delete_notin.
    2: { apply not_elem_of_dom. rewrite dom_insert.
         apply not_elem_of_union. split; auto.
         apply not_elem_of_singleton. intros ->.
         destruct FRESH'. eapply elem_of_dom. eauto. }
    rewrite map_img_insert_L.
    rewrite !difference_union_distr_l.
    rewrite difference_disjoint.
    2: { apply disjoint_singleton_l.
         intros [τ1 IN1]%elem_of_map_img.
         edestruct phases_not_le; [apply WF'| ..]; simpl.
         { apply LOC_PHASE. }
         { apply IN1. }
         { apply phase_lt_fork. }
         pose proof (phase_lt_fork π0 1) as [??]%strict_spec_alt. done. }
    rewrite difference_disjoint.
    2: { apply disjoint_singleton_l.
         intros [τ' IN']%elem_of_map_img.
         edestruct phases_not_le; [apply WF'| ..]; simpl.
         { apply LOC_PHASE. }
         { apply IN'. }
         { apply phase_lt_fork. }
         pose proof (phase_lt_fork π0 0) as [??]%strict_spec_alt. done. }
    rewrite subseteq_empty_difference.
    2: { apply map_subseteq_img, delete_subseteq. }

    rewrite union_empty_r_L elem_of_union !elem_of_singleton.
    rewrite /is_fork. intros [-> | ->]; eauto.
  Qed.

  Lemma om_trans_cps_bound δ1 τ δ2 π cp τ' π'
    (WF1: om_st_wf δ1)
    (PH: ps_phases δ1 !! τ = Some π)
    (STEP: om_trans δ1 τ δ2)
    (IN2 : cp ∈ ps_cps δ2)
    (PH': ps_phases δ2 !! τ' = Some π')
    (LE: phase_le π π')
    (LEcp : phase_le cp.1 π'):
    phase_le cp.1 π.
  Proof using.    
    destruct (decide (π' = π)) as [-> | NEQ].
    { done. }
    
    forward eapply (om_trans_wf_pres _ δ1) as WF2; eauto.

    assert (π' ∉ (map_img (ps_phases δ1): gset Phase)) as FRESHπ'.
    { intros IN.
      rename π' into π''.
      apply elem_of_map_img in IN as (τ'' & T'').
      destruct (decide (τ'' = τ)) as [-> | ?]; [set_solver| ].      
      edestruct @om_wf_ph_disj.
      { eapply WF1; eauto. }
      all: eauto. }

    assert (is_fork π π') as [d PH_FORK]; [| subst π'].
    { eapply fresh_phase_is_fork in STEP; eauto.
      2: { apply elem_of_difference. split; eauto. apply elem_of_map_img. eauto. }
      destruct STEP as (? & PH0 & ?). congruence. }

    apply phase_le_ext_split in LEcp as [EQ | ?]; [| done]. 

    red in STEP. destruct STEP as (δ' & PSTEP & FSTEP).
      
    forward eapply pres_by_loc_step_implies_progress.
    { apply loc_step_phases_pres. }
    intros PH_EQ. do 2 red in PH_EQ. specialize_full PH_EQ; eauto.
    { reflexivity. }
    red in PH_EQ. rewrite -PH_EQ in PH.
    
    forward eapply pres_by_loc_step_implies_progress.
    { apply wf_preserved_by_loc_step. }
    intros WF'. do 2 red in WF'. specialize_full WF'.
    2: { red. eauto. }
    all: eauto.
    
    assert (ps_cps δ2 = ps_cps δ') as CPS2.
    { inversion FSTEP; [| done].
      subst. destruct H as (?&?&FORK). inversion FORK. subst.
      by destruct δ'. }
    
    rewrite CPS2 in IN2.
    apply om_wf_cps_ph_bound in WF'. red in WF'. simpl in WF'.
    destruct WF'. do 3 eexists. split; [| split]; eauto.
    rewrite EQ. apply phase_lt_fork.
  Qed. 

  (* TODO: unify with previous *)
  Lemma om_trans_eps_bound δ1 τ δ2 π ep τ' π'
    (WF1: om_st_wf δ1)
    (PH: ps_phases δ1 !! τ = Some π)
    (STEP: om_trans δ1 τ δ2)
    (IN2 : ep ∈ ps_eps δ2)
    (PH': ps_phases δ2 !! τ' = Some π')
    (LE: phase_le π π')
    (LEcp : phase_le ep.1.2 π'):
    phase_le ep.1.2 π.
  Proof using.    
    destruct (decide (π' = π)) as [-> | NEQ].
    { done. }
    
    forward eapply (om_trans_wf_pres _ δ1) as WF2; eauto.

    assert (π' ∉ (map_img (ps_phases δ1): gset Phase)) as FRESHπ'.
    { intros IN.
      rename π' into π''.
      apply elem_of_map_img in IN as (τ'' & T'').
      destruct (decide (τ'' = τ)) as [-> | ?]; [set_solver| ].      
      edestruct @om_wf_ph_disj.
      { eapply WF1; eauto. }
      all: eauto. }

    assert (is_fork π π') as [d PH_FORK]; [| subst π'].
    { eapply fresh_phase_is_fork in STEP; eauto.
      2: { apply elem_of_difference. split; eauto. apply elem_of_map_img. eauto. }
      destruct STEP as (? & PH0 & ?). congruence. }

    apply phase_le_ext_split in LEcp as [EQ | ?]; [| done]. 

    red in STEP. destruct STEP as (δ' & PSTEP & FSTEP).
      
    forward eapply pres_by_loc_step_implies_progress.
    { apply loc_step_phases_pres. }
    intros PH_EQ. do 2 red in PH_EQ. specialize_full PH_EQ; eauto.
    { reflexivity. }
    red in PH_EQ. rewrite -PH_EQ in PH.
    
    forward eapply pres_by_loc_step_implies_progress.
    { apply wf_preserved_by_loc_step. }
    intros WF'. do 2 red in WF'. specialize_full WF'.
    2: { red. eauto. }
    all: eauto.
    
    assert (ps_eps δ2 = ps_eps δ') as EPS2.
    { inversion FSTEP; [| done].
      subst. destruct H as (?&?&FORK). inversion FORK. subst.
      by destruct δ'. }
    
    rewrite EPS2 in IN2.
    apply om_wf_eps_ph_bound in WF'. red in WF'. simpl in WF'.
    destruct WF'. do 3 eexists. split; [| split]; eauto.
    rewrite EQ. apply phase_lt_fork.
  Qed.
  
  Lemma min_owner_PF_decr s c
    (FAIR: ∀ τ, obls_trace_fair τ tr)
    (UNSET: never_set_after s c)
    (MIN: minimal_in_prop tr_sig_lt (s, c)
            (λ ab : SignalId * nat, is_Some (tr S!! ab.2) /\ never_set_after ab.1 ab.2 /\ c <= ab.2))
    (OTF := λ i, TPF (s_ow s i) i):
    ∀ d, c ≤ d -> is_Some (tr S!! d) → ∃ j, d < j ∧ ms_lt deg_le (OTF j) (OTF d).
  Proof using VALID WF SET_BEFORE_SPEC.
    clear LVL_WF.
    intros d LE [δ DTH].
    pose proof (never_set_owned _ _ UNSET) as OWN. specialize (OWN _ _ LE DTH).
    (* destruct (tr S!! d) as [δ| ] eqn:DTH. *)
    (* 2: { simpl in OWN. by apply map_Exists_empty in OWN. } *)
    simpl in OWN. rewrite map_Exists_lookup in OWN. 
    destruct OWN as [τ OWN]. 
    destruct (ps_obls δ !! τ) as [obs| ] eqn:OBLSd.
    2: { set_solver. }
    destruct OWN as (? & [=<-] & OWN). 
    pose proof (FAIR τ) as F. apply fair_by_equiv, fair_by'_strenghten in F.
    2: { solve_decision. }
    red in F. specialize (F d). specialize_full F.
    { rewrite DTH. simpl. red. rewrite OBLSd. simpl. set_solver. }
    destruct F as (m & (δm & MTH & STEP) & MINm).
    
    assert (exists π, ps_phases δ !! τ = Some π) as [π PH].
    { apply mk_is_Some, elem_of_dom in OBLSd.
      rewrite -om_wf_dpo in OBLSd; eauto.
      by apply elem_of_dom. }
    
    assert (∀ k, d <= k < d + m → tr L!! k ≠ Some τ) as OTHER_STEPS.
    { intros k BOUNDk Kτ.
      specialize (MINm (k - d)).
      specialize_full MINm; [| lia].
      rewrite -Nat.le_add_sub; [| lia].
      forward eapply (proj1 (label_lookup_states _ _)); eauto. intros [[? KTH] _].
      eexists. split; eauto. red. right. eauto. } 
    
    forward eapply next_step_rewind with (τ := τ).
    { apply DTH. }
    { rewrite OBLSd. done. }
    { eapply never_set_after_after; [| eauto]. lia. }
    4: { apply MTH. }
    { eapply min_tr_sig_after; eauto. }
    { lia. }
    { intros. apply OTHER_STEPS. lia. } 
    
    intros (TPFle & OW_EQm & PHm & OWm).
    
    (* assert (ps_obls δm !! τ = Some obs) as OBLSm. *)
    (* { forward eapply (pres_by_valid_trace_strong tr d (d + m)).  *)
    (*   4: { eapply (other_fork_step_pres_obls' τ obs). } *)
    (*   3: { apply other_loc_step_pres_obls. } *)
    (*   all: try done.  *)
    (*   { lia. } *)
    (*   { rewrite DTH. simpl. eauto. } *)
    (*   { simpl. intros. set_solver. } *)
    (*   simpl. rewrite MTH. simpl. tauto. } *)

    red in STEP. destruct STEP as [NOOBS | STEP]. 
    { rewrite /has_obls in NOOBS. set_solver. }
    destruct STEP as (?&LBL&<-).
    forward eapply (proj1 (label_lookup_states' _ _)); eauto.
    rewrite -Nat.add_1_r. intros [δm' MTH'].
    
    (* forward eapply (trace_valid_steps'' _ _ VALID (d + m)) as STEP; eauto. *)
    (* simpl in STEP. *)
    
    (* assert (ps_phases δm !! τ = Some π) as PHm. *)
    (* { forward eapply (pres_by_valid_trace_strong tr d (d + m)).  *)
    (*   4: { apply (other_fork_step_pres_phase_eq τ π). } *)
    (*   3: { intros. apply (loc_step_pres_phase_eq τ π). } *)
    (*   all: try done.  *)
    (*   { lia. } *)
    (*   { rewrite DTH. done. } *)
    (*   { set_solver. } *)
    (*   by rewrite MTH. } *)
    rewrite PH in PHm. 

    forward eapply (owm_om_trans_ms_le π τ τ (d + m)); eauto.
    { eapply never_set_after_after; [| eauto]. lia. }
    { eapply min_tr_sig_after; [eauto| ]. lia. }
    rewrite bool_decide_eq_true_2; [| done]. simpl. 
    
    (* forward eapply (owm_om_trans_ms_lt π τ (d + m)); eauto. *)
    (* { eapply never_set_after_after; [| apply UNSET]. lia. } *)
    (* { red. intros [??] [N' LE'] ?. simpl in LE', N'. *)
    (*   move MIN at bottom. red in MIN. *)
    (*   specialize (MIN (_, _) ltac:(split; [apply N'| simpl; lia])). *)
    (*   pose proof (never_set_after_eq_false _ _ UNSET c ltac:(lia)) as X. *)
    (*   pose proof (never_set_after_eq_false _ _ UNSET (d + m) ltac:(lia)) as Y. *)
    (*   destruct X as (?&l&CTH&SIGc), Y as (?&l_&DMTH&SIGdm). *)

    (*   forward eapply pres_by_valid_trace with (i := c) (j := d + m); eauto. *)
    (*   { intros. apply (loc_step_sig_st_le_pres _ s (Some (l, false))). } *)
    (*   { intros. apply fork_step_sig_st_le_pres. } *)
    (*   { rewrite CTH. simpl. by rewrite SIGc. } *)
    (*   { lia. } *)
    (*   rewrite DMTH. simpl. rewrite SIGdm. simpl. intros [<- _]. *)

    (*   clear -H MIN SIGc SIGdm DMTH CTH. *)
    (*   unfold tr_sig_lt, MR, lvl_at in *. *)
    (*   (* rewrite DMTH. simpl. rewrite SIGdm. simpl. *) *)
    (*   rewrite CTH in MIN. simpl in MIN. rewrite SIGc in MIN. simpl in MIN. *)
    (*   apply MIN. rewrite DMTH in H. simpl in H. rewrite SIGdm in H. done. } *)
    (* { by rewrite OBLSm. } *)
    
    intros LT.
    exists (S (d + m)). split; [lia| ].
    rewrite /OTF /TPF /TPF'. erewrite (S_OWNER _ d); eauto.
    2: { by rewrite OBLSd. }

    (* eapply strict_transitive_l; [| apply TPFle].  *)
    eapply strict_transitive_l.
    2: { rewrite OW_EQm in TPFle.
         rewrite /TPF /TPF' in TPFle.
         forward eapply (S_OWNER s); [apply DTH| ..]; eauto.
         { by rewrite OBLSd. }
         intros OWd.
         rewrite OWd in TPFle.
         apply TPFle. }
    eapply strict_transitive_r; [| apply LT].
    
    (* forward eapply (obls_transfer_phase δm τ) with (τs := τ).  *)
    (* { eapply trace_valid_steps''; eauto. } *)
    (* { rewrite OBLSm. done. } *)
    (* { eauto. } *)
    forward eapply pres_by_loc_fork_steps_implies_om_trans.
    { apply loc_step_pres_asg_bound. }
    { apply fork_step_pres_asg_bound. }
    intros PRES. do 2 red in PRES. specialize_full PRES.
    { split; [| by apply (WF (d + m))].
      red. right. exists τ, π. simpl. do 2 (split; [done| ]).
      reflexivity. }
    { red. eapply trace_valid_steps''; eauto. }
    apply proj1 in PRES. red in PRES. destruct PRES as [[l NO_OWN] | OWN'].
    { pose proof (UNSET (d + m + 1) ltac:(lia)) as U.
      rewrite /sig_val_at in U. rewrite MTH' in U. simpl in U.
      rewrite NO_OWN in U. specialize_full U; done. }
    
    destruct OWN' as (τ' & π' & OWN' & PH' & LE').
    destruct (ps_obls δm' !! τ') as [obs'| ] eqn:OBLSd'.
    2: { set_solver. }
    
    erewrite S_OWNER.
    3: { apply PH'. }
    2: { rewrite -MTH'. f_equal. lia. }
    2: { rewrite OBLSd'. done. } 
    
    (* TODO: extract? *)
    rewrite /TPF /TPF' /PF'.
    generalize ((LIM_STEPS + 2) * S (d + m)) as N. intros.
    rewrite plus_n_Sm -Nat.add_1_r Nat.add_assoc MTH'. simpl.
    apply ms_le_disj_union; [apply _| ..].
    - apply ms_le_sub, mset_map_sub.
      apply mset_filter_subseteq_mono_strong.
      intros [pi de] IN' LEpi.

      replace pi with (pi, de).1; [| done].
      eapply (om_trans_cps_bound δm); eauto.
      eapply trace_valid_steps''; eauto.
    - apply ms_le_exp_mono; [lia| ].
      apply gset_filter_subseteq_mono_strong. 
      intros ep IN' LEpi.
      destruct ep as [[? pi]?] eqn:EP.

      replace pi with ep.1.2 by (by subst). 
      eapply (om_trans_eps_bound δm); eauto.
      2, 3: by subst. 
      eapply trace_valid_steps''; eauto.
  Qed.


  Lemma tr_sig_lt_wf: wf tr_sig_lt.
  Proof using LVL_WF.
    apply measure_wf.
    assert (forall b, Acc lvl_opt_lt (Some b)) as ACC. 
    { intros. pattern b. eapply well_founded_induction; [apply LVL_WF| ].
      clear b. intros b IH.
      constructor. intros [a| ] LT; [| done].
      by apply IH. }

    red. intros [b| ]; [by apply ACC| ].
    constructor. intros [b| ] LT; [| done].
    by apply ACC.
  Qed.
  
  Theorem signals_eventually_set
    (FAIR: forall τ, obls_trace_fair τ tr)
    (DEG_WF: wf (strict deg_le)):
    (* ¬ exists sid c, never_set_after sid c.  *)
    forall sid,
      (* eventually_set sid.  *)
      ¬ (exists c, is_Some (tr S!! c) /\ never_set_after sid c).
  Proof using LVL_WF VALID WF SET_BEFORE_SPEC.
    intros sid. red. intros (m & MTH & UNSET).
    (* red in UNSET.  *)

    assert (exists ab, is_Some (tr S!! ab.2) /\ never_set_after ab.1 ab.2 /\ m <= ab.2) as MIN. 
    { exists (sid, m). eauto. }

    eapply sets_have_min in MIN; [| apply tr_sig_lt_wf]. clear sid UNSET. 
    apply ex_prod in MIN. simpl in MIN. destruct MIN as (s & c & (CTH & [UNSET LEm]) & MIN).
    
    set (OTF i := TPF (s_ow s i) i).
    
    set (R := MR (ms_lt deg_le) (fun i => OTF (c + i))). 
    forward eapply well_founded_ind with (R := R) (P := fun _ => False).
    4: done.
    3: exact 0.
    { eapply measure_wf. apply ms_lt_wf; try done. apply _. }
    
    intros i NEXT.
    (* pose proof (min_owner_PF_decr (c + i) ltac:(lia)) as D. *)
    forward eapply min_owner_PF_decr with (d := c + i); eauto.
    { red. intros [??] (NTH & N & LE) ?.
      eapply MIN; eauto. split; auto.
      simpl. split; eauto. simpl in *. lia. }
    { lia. }
    { destruct (tr S!! (c + i)) eqn:CITH; [done| ].
      forward eapply (trace_has_len tr) as [len LEN]; eauto.
      eapply state_lookup_dom_neg in CITH; eauto.
      destruct len; [done| ]. simpl in CITH.
      destruct n.
      { by apply trace_len_0_inv in LEN. }
      forward eapply (proj2 (state_lookup_dom _ _ LEN (max c n))).
      { simpl. edestruct Nat.lt_ge_cases as [LT | GE]; [by apply LT| ].
        apply Nat.max_le in GE as [GE | ?]; [| lia]. 
        forward eapply (proj2 (state_lookup_dom_neg _ _ LEN _)).
        { simpl. apply GE. }
        intros NOC. rewrite NOC in CTH. by apply is_Some_None in CTH. }
      intros [δ' LAST].
      red in UNSET. specialize_full UNSET.
      2: { eexists. apply LAST. }
      { lia. }
      rewrite /sig_val_at in UNSET. rewrite LAST /= in UNSET.
      destruct (ps_sigs δ' !! s) as [[??]|] eqn:SIGlast; [| done]. simpl in UNSET. subst.

      eapply obls_assigned_equiv in SIGlast.
      2: { eapply om_wf_asg. eapply WF; eauto. }
      destruct SIGlast as (τ & obs & OB & OBs).
      specialize (FAIR τ). apply fair_by_equiv in FAIR. red in FAIR.
      specialize (FAIR (c `max` n)). specialize_full FAIR.
      { rewrite LAST. simpl. red. rewrite OB. set_solver. }
      destruct FAIR as (k & ? & LAST_ & SAT).
      destruct k.
      2: { forward eapply (proj2 (state_lookup_dom_neg _ _ LEN (c `max` n + S k))).
           { simpl. lia. }
           intros EMP. by rewrite EMP in LAST_. }
      rewrite Nat.add_0_r in LAST_ SAT. rewrite LAST in LAST_. inversion LAST_. subst.
      destruct SAT as [SET | STEP]. 
      - destruct SET. red. rewrite OB. set_solver.
      - destruct STEP as (?&STEP&<-).
        eapply mk_is_Some, label_lookup_dom in STEP; eauto. simpl in STEP. lia. }
      
    intros (j & AFTER & DECR).
    apply (NEXT (j - c)). red. red.
    rewrite -Nat.le_add_sub; [| lia]. done.
  Qed.

  Let any_phase (_: Phase) := True.
  Definition APF := TPF' tr set_before any_phase.

  Lemma any_expect_ms_le δ1 τ δ2 k
    (SET_BOUND: forall sid π d, expects_ep δ1 τ δ2 sid π d ->
                  let n := (LIM_STEPS + 2) * set_before sid in
                  k < n)
    :
    expect_ms_le set_before any_phase δ1 τ δ2 k. 
  Proof using SET_BEFORE_SPEC VALID.
    clear LVL_WF WF.
    intros. red. intros sid π' d EXP. 
    rewrite /PF /PF'.
    
    inversion EXP; subst.
    destruct δ1. simpl in *. subst new_cps0.
    rewrite !mset_filter_True.
    2, 3: intros [??]; done.
    rewrite gset_filter_True.
    2: intros ((?&?)&?); done.      
    
    rewrite mset_map_disj_union.
    rewrite mset_map_singleton. simpl. 
    
    (* rewrite mset_map_disj_union. *)
    rewrite -gmultiset_disj_union_assoc. apply ms_le_disj_union; [apply _| ..].
    { reflexivity. }
    rewrite (union_difference_singleton_L _ _ EP).
    
    rewrite (union_comm_L {[ _ ]} _).
    rewrite !approx_expects_add.
    2, 3: set_solver.
    simpl. rewrite gmultiset_disj_union_comm.
    rewrite -gmultiset_disj_union_assoc.
    apply ms_le_disj_union; [apply _| ..].
    { apply ms_le_exp_mono; [lia | reflexivity]. }
    
    move SET_BOUND at bottom. specialize_full SET_BOUND; [by eauto| ].
    eapply ms_le_Proper; [reflexivity| ..| reflexivity].
    rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.
  Qed.
  
  (* TODO: try to unify with similar lemmas? *)
  Lemma om_trans_all_ms_lt n
    (DOM: is_Some (tr S!! (S n)))
    (* (ALL_SET: ∀ sid, eventually_set sid) *)
    (ALL_SET: forall sid, ¬ (exists c, is_Some (tr S!! c) /\ never_set_after sid c))
    :
    ms_lt deg_le (APF (S n)) (APF n).
  Proof using VALID SET_BEFORE_SPEC.
    destruct DOM as [δ' NTH']. 
    
    eapply om_trans_ms_rel with (bd := true); auto.
    { intros δ δ'_ τ mb mf k NTH BOUND PSTEPS BURNS FORKS. 
      rewrite Nat.add_succ_r Nat.add_0_r.
      apply state_label_lookup in NTH as (NTH_&NTH'_&LBL_).
      rewrite Nat.add_1_r NTH' in NTH'_. inversion NTH'_. subst δ'_. 
      destruct BURNS as (?&?&BURNS).
      inversion BURNS. subst. 
      eapply burns_cp_own_ms_lt with (πb := x); done. }
    
    (* TODO: extract the lemma below? *)
    
    (* clear δ' NTH'.  *)
    intros τ' IDTHl. 
    red. intros δn δn' mb mf k ITH%state_label_lookup BOUND NSTEPS BSTEP FSTEP.
    destruct ITH as (ITH & ITH' & _).
    rewrite Nat.add_1_r NTH' in ITH'. inversion ITH'. subst. clear ITH'.

    (* TODO: get rid of duplicate *)
    assert (forall sid, sig_st_le (ps_sigs mb !! sid) (ps_sigs δn' !! sid)) as SIG_LE''.
    { intros.
      etrans.
      { eapply loc_step_sig_st_le_pres; [reflexivity| ].
        red. eexists. red. left. eauto. }
      inversion FSTEP as [? F| ]; subst.
      2: { reflexivity. }
      destruct F as (?&?&F).
      eapply fork_step_sig_st_le_pres; [reflexivity| ].
      eexists. eauto. }
    
    clear dependent BSTEP FSTEP. 
    
    generalize dependent mb. induction k.
    { intros ? ->%nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    intros δ'' (δ' & STEPS & [τ STEP])%nsteps_inv_r SIG_LE'''.
    specialize (IHk ltac:(lia) _ STEPS). specialize_full IHk.
    { intros. etrans; [| apply SIG_LE'''].
      eapply loc_step_sig_st_le_pres; [reflexivity| ]. red. eauto. }    
    
    etrans; eauto.
    eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
    { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
    
    eapply any_expect_ms_le. 
    
    intros sid π d EXP. simpl.
    inversion EXP. subst.
    
    enough (set_before sid > n) as GT.
    { apply PeanoNat.Nat.le_succ_l in GT. 
      apply Nat.le_sum in GT as [u EQ]. rewrite EQ. lia. }
    
    red.
    clear LE. 
    edestruct Nat.lt_ge_cases as [LT | LE]; [apply LT| ].   
    pose proof SET_BEFORE_SPEC as SB.

    specialize (SB sid). red in SB.
    specialize (ALL_SET sid).
    destruct SB as [[SB ?] | SB].
    { destruct ALL_SET. exists (S n). split.
      { by apply label_lookup_states'. }
      red. intros j LEj [δj JTH]. rewrite /sig_val_at JTH. simpl.
      rewrite update_cps_same_sigs in SIG_LE'''. specialize (SIG_LE''' sid).
      rewrite SIG in SIG_LE'''.
      destruct (ps_sigs δn' !! sid) as [[??]|] eqn:SIG'; [| done].
      eapply sig_st_le_lookup_helper with (s := sid) in LEj; eauto.
      rewrite SIG' in LEj. destruct (ps_sigs δj !! sid) as [[??]|] eqn:SIGj; [| done].
      simpl in *. destruct SIG_LE''' as [-> ?], LEj as [-> ?]. 
      destruct b0; try tauto.
      destruct SB. exists j. red. rewrite JTH. simpl. by rewrite SIGj. }

    (* TODO: unify with previous case? *)
    destruct SB as (f & SETf & LEf_sb).
    forward eapply sig_is_set_at_after with (j := n).
    { eauto. }
    { lia. }
    { eauto. }
    rewrite /sig_is_set_at ITH /=.
    destruct (ps_sigs δn !! sid) as [[??]|] eqn:SIDn; [| done].
    simpl. intros <-.
    unshelve eapply (pres_by_rel_implies_rep _ _ _ _ _ _) in STEPS.
    { apply loc_step_sig_st_le_pres. }
    2: { simpl. eapply reflexive_eq. symmetry. apply SIDn. }
    simpl in STEPS. rewrite SIG in STEPS. tauto. 
    
  Qed. 

  Theorem trace_terminates
    (FAIR: forall τ, obls_trace_fair τ tr)
    (DEG_WF: wf (strict deg_le)):
    terminating_trace tr. 
  Proof using WF VALID SET_BEFORE_SPEC LVL_WF.
    set (R := MR (ms_lt deg_le) APF).    
    forward eapply well_founded_ind with (R := R) (P := fun _ => terminating_trace tr).
    4: done.
    3: exact 0. 
    { eapply measure_wf. eapply ms_lt_wf; eauto. apply _. }
    intros i NEXT.

    destruct (tr S!! (S i)) eqn:ITH'.
    2: { pose proof (trace_has_len tr) as [len ?]. 
         eapply state_lookup_dom_neg in ITH'; eauto.
         lia_NO' len.
         eapply terminating_trace_equiv; eauto. }

    forward eapply om_trans_all_ms_lt; eauto.
    by apply signals_eventually_set. 
  Qed. 

End Termination.


(* TODO: merge the sections *)
Section TerminationFull.
  Context `{OP: ObligationsParams Degree Level Locale LIM_STEPS}.
  Let OM := ObligationsModel.

  Context (tr: obls_trace).
  Hypothesis (VALID: obls_trace_valid tr) (FAIR: ∀ τ, obls_trace_fair τ tr).

  Lemma set_before_ex
    :
    forall sid, exists b, sb_prop tr sid b. 
  Proof using VALID.
    intros sid.
    destruct (Classical_Prop.classic (exists c, sig_is_set_at tr sid c)) as [[c USED] | UNUSED].
    2: { exists 0. red. intros. left. split; auto. }
    exists c. red. right. eexists. split; eauto.      
  Qed.

  Theorem obls_fair_trace_terminate
    (TR_WF: ∀ i δ, tr S!! i = Some δ → om_st_wf δ)
    (LVL_WF: wf (strict lvl_le))
    (DEG_WF: wf (strict deg_le)):
    terminating_trace tr.
  Proof using VALID FAIR.
    Require Import Coq.Logic.ClassicalChoice.
    pose proof (choice _ set_before_ex) as [sb ?].
    eapply trace_terminates; eauto. 
  Qed.

End TerminationFull.
