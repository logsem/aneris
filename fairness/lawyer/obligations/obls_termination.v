Require Import Coq.Program.Wf.
Require Import Relation_Operators.
From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len.
From trillium.fairness.lawyer.obligations Require Import obligations_model multiset_utils obls_utils wf_utils obls_pf.
From stdpp Require Import relations.


Section Termination.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP.

  Context (tr: obls_trace OP).
  
  Hypothesis (LVL_WF: wf (strict lvl_le)).
  
  Context `{Inhabited Level}. 
  Let lvl__def := @inhabitant Level _. 
  
  Definition never_set_after sid c := 
    forall i, c <= i -> from_option (fun δ => from_option snd true (ps_sigs _ δ !! sid)) false (tr S!! i) = false.
  
  Context {set_before: SignalId -> nat}.
  Hypothesis (SET_BEFORE_SPEC: 
               forall sid i,
                 (forall c, ¬ never_set_after sid c) ->
                 set_before sid <= i ->
                 from_option (fun δ => from_option snd false (ps_sigs _ δ !! sid)) false (tr S!! i) = true).
  
  Definition lvl_at (sid_i: SignalId * nat): Level :=
    let '(sid, i) := sid_i in
    from_option (fun δ => from_option fst lvl__def (ps_sigs _ δ !! sid)) lvl__def (tr S!! i).

  Definition tr_sig_lt: relation (SignalId * nat) := MR (strict lvl_le) lvl_at. 
  
  Lemma tr_sig_lt_wf: wf tr_sig_lt.
  Proof using LVL_WF. apply measure_wf. apply LVL_WF. Qed.
  
  Lemma never_set_after_after sid i j
    (LE: i <= j):
    never_set_after sid i -> never_set_after sid j.
  Proof using.
    rewrite /never_set_after. intros NEVER m LE'.
    eapply NEVER. lia. 
  Qed.
  
  Definition phase_ge := flip phase_le. 
  Definition PF (π: Phase) := PF' OP set_before (phase_ge π).
  Definition TPF (π: Phase) := TPF' OP tr set_before (phase_ge π).
  
  Let π0 := nroot. 
  
  Lemma other_expect_ms_le π__ow δ1 τ δ2 k
    (OTHER: let π := default π0 (ps_phases _ δ1 !! τ) in
            phases_incompat π__ow π):
    expect_ms_le OP set_before (phase_ge π__ow) δ1 τ δ2 k. 
  Proof using.
    clear LVL_WF SET_BEFORE_SPEC. 
    red. intros sid π' d EXP. 
    rewrite /PF /PF'.
    inversion EXP; subst.
    destruct δ1. simpl in *.
    subst new_cps0.
    
    rewrite !mset_filter_disj_union mset_map_disj_union.
    rewrite !mset_filter_singleton.
    rewrite decide_False.
    2: { rewrite LOC_PHASE in OTHER. simpl in OTHER.
         red in OTHER. tauto. }
    
    rewrite mset_map_empty. apply ms_le_disj_union.
    + eapply ms_le_Proper; [reflexivity| | reflexivity]. mss.
    + apply ms_le_exp_mono; [lia | reflexivity].
  Qed.

  Lemma min_owner_expect_ms_le δ1 τ δ2 k
    (SET_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                           let n := (LIM_STEPS + 2) * set_before sid in
                           k < n)
    :
    let π__ow := default π0 (ps_phases _ δ1 !! τ) in
    expect_ms_le OP set_before (phase_ge π__ow) δ1 τ δ2 k. 
  Proof using.
    clear LVL_WF SET_BEFORE_SPEC.
    intros. red. intros sid π' d EXP. 
    rewrite /PF /PF'.
    
    inversion EXP; subst.
    destruct δ1. simpl in *. subst new_cps0.
    subst π__ow. rewrite LOC_PHASE. simpl. 
    
    rewrite !mset_filter_disj_union mset_map_disj_union.
    rewrite !mset_filter_singleton.
    rewrite decide_True; [| red; reflexivity].
    rewrite mset_map_singleton. simpl. 
    
    rewrite -gmultiset_disj_union_assoc. apply ms_le_disj_union.
    { apply ms_le_refl. }
    rewrite (union_difference_singleton_L _ _ EP).
    
    rewrite filter_union_L.
    rewrite !gset_singleton_if_equiv.
    rewrite decide_True; [| tauto].
    
    rewrite (union_comm_L {[ _ ]} _).
    rewrite !approx_expects_add.
    2, 3: set_solver.
    simpl. rewrite gmultiset_disj_union_comm.
    rewrite -gmultiset_disj_union_assoc.
    apply ms_le_disj_union.
    { apply ms_le_exp_mono; [lia | reflexivity]. }
    
    move SET_BOUND at bottom. specialize_full SET_BOUND; [by eauto| ].
    eapply ms_le_Proper; [reflexivity| ..| apply ms_le_refl].
    rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.
  Qed.

  Lemma never_set_owned s c
    (NEVER_SET: never_set_after s c):
    forall i, c <= i ->
         map_Exists (fun τ obs => s ∈ obs) (from_option (ps_obls _) ∅ (tr S!! i)). 
  Proof using OM. Admitted. 

  Lemma other_om_trans_ms_le πτ τ n
    (VALID: obls_trace_valid OP tr)
    (PH: from_option (fun δ => ps_phases _ δ !! τ = Some πτ) False (tr S!! n))
    (NOτ: tr L!! n ≠ Some τ):
    ms_le deg_le (TPF πτ (S n)) (TPF πτ n).
  Proof using.
    destruct (tr S!! (S n)) as [δ'| ] eqn:NEXT.
    2: { rewrite /TPF /TPF'. rewrite NEXT. simpl. apply empty_ms_le. }
    
    eapply om_trans_ms_rel with (bd := false); auto.
    { intros.
      rewrite Nat.add_succ_r. rewrite Nat.add_0_r.  
      destruct H4 as (?&?&?). eapply burns_cp_ms_le; eauto. }
    
    (* TODO: extract the lemma below? *)
    
    intros δ τ' IDTHl. 
    red. intros δk k IDTH BOUND NSTEPS. 
    rewrite IDTHl in NOτ.
    assert (τ' ≠ τ) as X by (by intros ->). clear NOτ. rename X into NOτ. 
    
    generalize dependent δk. induction k.
    { intros ? ->%obls_utils.nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    clear δ' NEXT. 
    intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
    specialize (IHk ltac:(lia) _ STEPS).
    etrans; eauto.
    eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
    { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
    apply other_expect_ms_le. simpl. 
    assert (exists π', ps_phases _ δ' !! τ' = Some π') as [π' PH'].
    { (* follows from DPO and the fact that
         loc_step only applies to locales in either phases or obls *)
      admit. }
    rewrite PH'. simpl.
    rewrite IDTH in PH. simpl in PH. 
    
    assert (ps_phases _ δ' !! τ = Some πτ) as PHδ'.
    { (* phase preserved by loc steps *)
      admit. }
    
    (* should add a WF condition for pairwise phase incompatibility *)
    admit.
  Admitted.
  
  Lemma next_step_rewind τ π i δ0 j
    (VALID: obls_trace_valid OP tr)
    (ITH: tr S!! i = Some δ0)
    (PH: ps_phases _ δ0 !! τ = Some π)
    (LE: i <= j)
    (NOτ: forall k, i <= k < j -> tr L!! k ≠ Some τ):
    ms_le deg_le (TPF π j) (TPF π i).
  Proof using. 
    apply Nat.le_sum in LE as [d ->]. induction d.
    { rewrite Nat.add_0_r. reflexivity. }
    specialize_full IHd.
    { intros. apply NOτ. lia. }
    etrans; eauto.
    rewrite -plus_n_Sm.
    
    destruct (tr S!! (S (i + d))) as [δ'| ] eqn:NEXT.
    2: { rewrite /TPF /TPF'. rewrite NEXT. simpl. apply empty_ms_le. }
    forward eapply (state_lookup_prev _ _ ltac:(eauto) _ (PeanoNat.Nat.le_succ_diag_r _)).
    intros [δ IDTH].
    
    eapply other_om_trans_ms_le; eauto.
    2: { specialize (NOτ (i + d) ltac:(lia)). done. }
    rewrite IDTH. simpl. 
    
    (* phase preserved by non-τ steps *)
    admit. 
  Admitted.      

  Lemma other_sig_exp_lim (δ : ObligationsModel OP) (i : nat) (τ : Locale)
    (s : SignalId) (δ' : ProgressState OP) (sid : SignalId) (l : Level)
    (ITH : tr S!! i = Some δ)
    (NEVER_SET : never_set_after s i)
    (MIN: minimal_in_prop tr_sig_lt (s, i) (λ sn, never_set_after sn.1 sn.2))
    (OWNER: s ∈ default ∅ (ps_obls _ δ !! τ))
    (OBLS_LT : lt_locale_obls OP l τ δ'):
    i < set_before sid.
  Proof using. 
    red in OBLS_LT. red in OBLS_LT.
    
    move NEVER_SET at bottom. red in NEVER_SET.
    specialize (NEVER_SET _ ltac:(reflexivity)).
    rewrite ITH in NEVER_SET. simpl in NEVER_SET. 
    destruct (ps_sigs OP δ !! s) as [[ls ?]|] eqn:SIG__min; [| done].
    simpl in NEVER_SET. subst. 
    
    assert (ps_sigs _ δ' !! s = Some (ls, false)) as SIG' by admit.
    assert (s ∈ default ∅ (ps_obls _ δ' !! τ)) as OBL' by admit.
    specialize (OBLS_LT ls). specialize_full OBLS_LT.
    { apply extract_Somes_gset_spec.
      destruct (ps_obls OP δ' !! τ) as [obs| ] eqn:OBLS'; [| set_solver].
      simpl in OBL'. simpl. apply elem_of_map. eexists. split; eauto.
      rewrite SIG'. done. }      
    
    red. destruct (Nat.lt_ge_cases i (set_before sid)) as [?|GE]; [done| ].   
    
    (* either it was there when the big step started,
       or it's a new signal, but then the thread holds an obligation
       and cannot wait on it *)
    assert (ps_sigs OP δ !! sid = Some (l, false)) as SIG0 by admit.
    
    pose proof (SET_BEFORE_SPEC sid i). specialize_full H1; [| done| ].
    2: { rewrite ITH in H1. simpl in H1.
         rewrite SIG0 in H1. done. }
    
    intros c NEVER_SET_.
    assert (never_set_after sid i) as NEVER_SET' by admit. clear NEVER_SET_.
    move MIN at bottom. red in MIN. specialize (MIN (_, _) NEVER_SET').
    rewrite /tr_sig_lt /MR in MIN. simpl in MIN.
    rewrite ITH in MIN. simpl in MIN. rewrite SIG0 SIG__min in MIN. simpl in MIN.
    specialize (MIN OBLS_LT).
    edestruct @strict_not_both; eauto. 
  Admitted.

  Lemma owm_om_trans_ms_lt πτ τ n s δ0
    (NTH: tr S!! n = Some δ0)
    (VALID: obls_trace_valid OP tr)
    (PH: ps_phases _ δ0 !! τ = Some πτ)
    (NEVER_SET : never_set_after s n)
    (MIN: minimal_in_prop tr_sig_lt (s, n) (λ sn, never_set_after sn.1 sn.2))
    (OWNER: s ∈ default ∅ (ps_obls _ δ0 !! τ))
    (LBL: tr L!! n = Some τ):
    ms_lt deg_le (TPF πτ (S n)) (TPF πτ n).
  Proof using.
    forward eapply (proj1 (label_lookup_states' _ _)); eauto. intros [δ' NTH']. 
    
    eapply om_trans_ms_rel with (bd := true); auto.
    { intros.
      rewrite Nat.add_succ_r Nat.add_0_r.
      apply state_label_lookup in H1 as (NTH_&?&LBL_).
      rewrite LBL in LBL_. inversion LBL_. subst τ0. 
      rewrite NTH in NTH_. inversion NTH_. subst δ0. 
      destruct H4 as (?&?&?).
      
      inversion H4. subst. 
      assert (ps_phases _ mb !! τ = Some πτ) as PH'.
      { (* phases are preserved by loc steps *)
        admit. 
      }
      rewrite LOC_PHASE in PH'. inversion PH'. subst π__max.  
      
      eapply burns_cp_own_ms_lt with (πb := x); eauto. }
    
    (* TODO: extract the lemma below? *)
    
    clear δ' NTH'. 
    intros δ τ' IDTHl. 
    red. intros δk k IDTH BOUND NSTEPS.
    rewrite NTH in IDTH. inversion IDTH. subst δ. 
    rewrite LBL in IDTHl. inversion IDTHl. subst τ'. clear IDTHl. 
    
    generalize dependent δk. induction k.
    { intros ? ->%obls_utils.nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    (* clear δ' NEXT.  *)
    intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
    specialize (IHk ltac:(lia) _ STEPS).
    etrans; eauto.
    eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
    { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
    
    assert (ps_phases _ δ' !! τ = Some πτ) as PHδ'.
    { (* phase preserved by loc steps *)
      admit. }
    
    replace πτ with (default π0 (ps_phases OP δ' !! τ)).
    2: { rewrite PHδ'. done. }
    
    apply min_owner_expect_ms_le. simpl.
    
    intros sid π d EXP. simpl.
    inversion EXP. subst.
    rewrite PHδ' in LOC_PHASE. inversion LOC_PHASE. subst π__max.
    
    enough (set_before sid > n).
    { apply PeanoNat.Nat.le_succ_l in H1. 
      apply Nat.le_sum in H1 as [u EQ]. rewrite EQ. lia. }
    
    eapply other_sig_exp_lim; eauto.
  Admitted.

  Lemma obls_transfer_phase δ1 τ δ2 s τs πs
    (STEP: om_trans _ δ1 τ δ2)
    (OBL: s ∈ default ∅ (ps_obls _ δ1 !! τs))
    (PH: ps_phases _ δ1 !! τ = Some πs):
    map_Forall (fun _ obls_ => s ∉ obls_) (ps_obls _ δ2) \/
      exists τ' π',
        s ∈ default ∅ (ps_obls _ δ2 !! τ') /\
        ps_phases _ δ2 !! τ' = Some π' /\
        phase_le πs π'.
  Proof using. Admitted.

  (* TODO: introduce general theorems about preservation of state/transition properties by omTrans *)
  Goal True. Admitted.

  (* Lemma om_trans_new_cps δ1 τ δ2 *)
  (*   (STEP: om_trans _ δ1 τ δ2) *)
  (*   (πτ := default π0 (ps_phases _ δ1 !! τ)) *)
  (*   : *)
  (*   forall cp, cp ∈ ps_cps _ δ2 ∖ ps_cps _ δ1 -> cp.1 = πτ. *)
  (* Proof using. Admitted.  *)
  
  (* Lemma om_trans_new_eps δ1 τ δ2 *)
  (*   (STEP: om_trans _ δ1 τ δ2) *)
  (*   (πτ := default π0 (ps_phases _ δ1 !! τ)) *)
  (*   : *)
  (*   forall ep, ep ∈ ps_eps _ δ2 ∖ ps_eps _ δ1 -> phase_le (ep.1.2) πτ. *)
  (* Proof using. Admitted. *)
  
  (* TODO: add to Wf *)
  Lemma cps_phase_bound δ:
    ¬ (exists τ π cp,
          ps_phases _ δ !! τ = Some π /\
            cp ∈ ps_cps _ δ /\
            phase_lt π cp.1).
  Proof using. Admitted. 
  
  Lemma om_trans_cps_bound δ1 τ δ2 πτ cp π'
    (PH: ps_phases _ δ1 !! τ = Some πτ)
    (STEP: om_trans _ δ1 τ δ2)
    (IN2 : cp ∈ ps_cps _ δ2)
    (LEcp : phase_le cp.1 π')
    (FRESHπ': π' ∉ (map_img (ps_phases _ δ1) : gset Phase)):
    phase_le cp.1 πτ.
  Proof using. Admitted.

  Definition s_ow (s: SignalId) (i: nat) := 
    let π := 
      δ ← tr S!! i;
      let owners := dom $ filter (fun '(_, obs) => s ∈ obs) (ps_obls _ δ) in
      let ow_phs := extract_Somes_gset $ set_map (fun τ => ps_phases _ δ !! τ) owners: gset Phase in
      ow ← gset_pick ow_phs;
      mret ow
    in default π0 π.

  (* TODO: move to Wf *)
  Lemma OBLS_DISJ: ∀ (τ1 τ2 : Locale) (δ : ProgressState OP),
      τ1 ≠ τ2
      → default ∅ (ps_obls OP δ !! τ1) ## default ∅ (ps_obls OP δ !! τ2).
  Proof using. Admitted. 

  Lemma S_OWNER s i π τ δ
    (ITH: tr S!! i = Some δ)
    (PH: ps_phases _ δ !! τ = Some π)
    (OW: s ∈ default ∅ (ps_obls _ δ !! τ)):
    s_ow s i = π.
  Proof using.
    clear dependent set_before LVL_WF. 
    intros. rewrite /s_ow. rewrite ITH. simpl.
    destruct (ps_obls OP δ !! τ) as [obls| ] eqn:OBLS; [| done]. simpl in OW.
    erewrite <- map_difference_union with (m2 := (ps_obls OP δ)).
    2: { eapply map_singleton_subseteq_l; eauto. }
    rewrite map_filter_union.
    2: { apply map_disjoint_dom. set_solver. }
    rewrite map_filter_singleton decide_True; [| done].
    rewrite (proj2 (map_filter_empty_iff _ _)).
    2: { red. intros τ' ? LOC' IN'.
         apply lookup_difference_Some in LOC'. destruct LOC' as [OBLS' ?%lookup_singleton_None].
         specialize (OBLS_DISJ τ τ' δ).
         pose proof (@OBLS_DISJ  _ _ δ H1) as D. rewrite OBLS OBLS' in D.
         set_solver. }
    rewrite map_union_empty dom_singleton_L.
    rewrite set_map_singleton_L. rewrite PH.
    rewrite extract_Somes_gset_singleton. rewrite gset_pick_singleton.
    done.
  Qed.

  Lemma min_owner_PF_decr s c
    (VALID: obls_trace_valid OP tr)
    (FAIR: ∀ τ, obls_trace_fair OP τ tr)
    (UNSET: never_set_after s c)
    (MIN: minimal_in_prop tr_sig_lt (s, c)
            (λ ab : SignalId * nat, never_set_after ab.1 ab.2))
    (OTF := λ i, TPF (s_ow s i) i):
    ∀ d, c ≤ d → ∃ j, d < j ∧ ms_lt deg_le (OTF j) (OTF d).
  Proof using.
    intros d LE.
    pose proof (never_set_owned _ _ UNSET) as OWN. specialize (OWN _ LE).  
    destruct (tr S!! d) as [δ| ] eqn:DTH.
    2: { simpl in OWN. by apply map_Exists_empty in OWN. }
    simpl in OWN. rewrite map_Exists_lookup in OWN. 
    destruct OWN as [τ OWN]. 
    destruct (ps_obls OP δ !! τ) as [obs| ] eqn:OBLSd.
    2: { set_solver. }
    destruct OWN as (? & [=<-] & OWN). 
    pose proof (FAIR τ) as F. apply fair_by_equiv, fair_by'_strenghten in F.
    2: { solve_decision. }
    red in F. specialize (F d). specialize_full F.
    { rewrite DTH. simpl. red. rewrite OBLSd. simpl. set_solver. }
    destruct F as (m & (δm & MTH & STEP) & MINm).
    
    assert (exists π, ps_phases _ δ !! τ = Some π) as [π PH].
    { (* follows from DPO *)
      admit. }
    
    (* rewrite /OTF in EMP. erewrite S_OWNER in EMP; eauto. *)
    (* 2: { rewrite OBLSd. set_solver. }  *)
    
    forward eapply next_step_rewind. 
    { eauto. }
    { apply DTH. }
    { eauto. }
    { apply (Nat.le_add_r _ m). }
    { intros k BOUNDk Kτ.
      specialize (MINm (k - d)).
      specialize_full MINm; [| lia].
      rewrite -Nat.le_add_sub; [| lia].
      forward eapply (proj1 (label_lookup_states _ _)); eauto. intros [[? KTH] _].
      eexists. split; eauto. red. right. eauto. }
    intros TPFle.
    
    (* rewrite EMP in TPFle. apply ms_le_empty in TPFle. *)
    
    red in STEP. destruct STEP.
    { (* steps in between keep the obligation assigned *)
      admit. }
    destruct H1 as (?&LBL&<-).
    forward eapply (proj1 (label_lookup_states' _ _)); eauto.
    rewrite -Nat.add_1_r. intros [δm' MTH'].
    
    (* forward eapply (trace_valid_steps'' _ _ VALID (d + m)) as STEP; eauto. *)
    (* simpl in STEP. *)
    
    assert (ps_obls OP δm !! τ = Some obs) as OBLSm.
    { (* obligations haven't been changed with other threads' steps *)
      admit. }
    
    assert (ps_phases OP δm !! τ = Some π) as PHm.
    { (* phase is kept by other steps *)
      admit. }
    
    forward eapply (owm_om_trans_ms_lt π τ (d + m)); eauto.
    { admit. }
    { (* tr_sig_lt doesn't depend on concrete index *)
      admit. }
    { by rewrite OBLSm. }
    
    intros LT.
    exists (S (d + m)). split; [lia| ].
    rewrite /OTF /TPF /TPF'. erewrite (S_OWNER _ d); eauto.
    2: { by rewrite OBLSd. }
    eapply strict_transitive_l; [| apply TPFle]. 
    eapply strict_transitive_r; [| apply LT].
    
    forward eapply (obls_transfer_phase δm τ) with (τs := τ). 
    { eapply trace_valid_steps''; eauto. }
    { rewrite OBLSm. done. }
    { eauto. }
    intros [NO_OWN | OWN'].
    { apply map_not_Exists in NO_OWN. destruct NO_OWN.
      erewrite @f_equal. 
      { eapply never_set_owned.
        { eapply never_set_after_after; [| apply UNSET ].
          etrans; [apply LE| ]. apply (Nat.le_add_r _ (m + 1)). }
        reflexivity. }
      rewrite Nat.add_assoc. rewrite MTH'. done. }
    
    destruct OWN' as (τ' & π' & OWN' & PH' & LE').
    destruct (ps_obls OP δm' !! τ') as [obs'| ] eqn:OBLSd'.
    2: { set_solver. }
    
    erewrite S_OWNER.
    3: { apply PH'. }
    2: { rewrite -MTH'. f_equal. lia. }
    2: { rewrite OBLSd'. done. } 
    
    (* TODO: extract? *)
    rewrite /TPF /TPF' /PF'.
    generalize ((LIM_STEPS + 2) * S (d + m)) as N. intros.
    rewrite plus_n_Sm -Nat.add_1_r Nat.add_assoc MTH'. simpl.
    apply ms_le_disj_union.
    - apply ms_le_sub, mset_map_sub.
      apply mset_filter_subseteq_mono_strong.
      intros [pi de] IN' LEpi.
      destruct (decide (π' = π)) as [-> | NEQ]; [done| ].
      assert (π' ∉ (map_img (ps_phases _ δm): gset Phase)) as FRESHπ'.
      { (* should follow from phase incompatibility for δm *)
        admit. }
      replace pi with (pi, de).1; [| done]. eapply om_trans_cps_bound; eauto.
      eapply trace_valid_steps''; eauto.  
    - apply ms_le_exp_mono; [lia| ].
      admit.
  Admitted.       
  
  Theorem signals_eventually_set
    (VALID: obls_trace_valid OP tr)
    (FAIR: forall τ, obls_trace_fair _ τ tr):
    ¬ exists sid c, never_set_after sid c. 
  Proof using.
    intros EX. apply ex_prod' in EX.
    eapply sets_have_min in EX; [| apply tr_sig_lt_wf].
    apply ex_prod in EX. simpl in EX. destruct EX as (s & c & UNSET & MIN).
    
    set (OTF i := TPF (s_ow s i) i).
    
    set (R := MR (ms_lt deg_le) (fun i => OTF (c + i))). 
    forward eapply well_founded_ind with (R := R) (P := fun _ => False).
    4: done.
    3: exact 0.
    { eapply measure_wf.
      admit. }
    intros i NEXT.
    (* pose proof (min_owner_PF_decr (c + i) ltac:(lia)) as D. *)
    forward eapply min_owner_PF_decr with (d := c + i); eauto.
    { lia. }
    intros (j & AFTER & DECR).
    apply (NEXT (j - c)). red. red.
    rewrite -Nat.le_add_sub; [| lia]. done. 
    
  Admitted.

  Let any_phase (_: Phase) := True.
  Definition APF := TPF' OP tr set_before any_phase.

  (* TODO: move *)
  Lemma gset_filter_True `{Countable K} (g: gset K)
    (P: K -> Prop)
    `{∀ x, Decision (P x)}
    (TRUE: forall k, k ∈ g -> P k):
    filter P g = g.
  Proof using. clear -TRUE. set_solver. Qed. 
  
  Lemma any_expect_ms_le δ1 τ δ2 k
    (SET_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                  let n := (LIM_STEPS + 2) * set_before sid in
                  k < n)
    :
    expect_ms_le OP set_before any_phase δ1 τ δ2 k. 
  Proof using SET_BEFORE_SPEC.
    clear LVL_WF.
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
    rewrite -gmultiset_disj_union_assoc. apply ms_le_disj_union.
    { apply ms_le_refl. }
    rewrite (union_difference_singleton_L _ _ EP).
    
    rewrite (union_comm_L {[ _ ]} _).
    rewrite !approx_expects_add.
    2, 3: set_solver.
    simpl. rewrite gmultiset_disj_union_comm.
    rewrite -gmultiset_disj_union_assoc.
    apply ms_le_disj_union.
    { apply ms_le_exp_mono; [lia | reflexivity]. }
    
    move SET_BOUND at bottom. specialize_full SET_BOUND; [by eauto| ].
    eapply ms_le_Proper; [reflexivity| ..| apply ms_le_refl].
    rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.
  Qed.
  
  (* TODO: try to unify with similar lemmas? *)
  Lemma om_trans_all_ms_lt n
    (* (NTH: tr S!! n = Some δ0) *)
    (VALID: obls_trace_valid OP tr)
    (* (PH: ps_phases _ δ0 !! τ = Some πτ) *)
    (* (NEVER_SET : never_set_after s n) *)
    (* (MIN: minimal_in_prop tr_sig_lt (s, n) (λ sn, never_set_after sn.1 sn.2)) *)
    (* (OWNER: s ∈ default ∅ (ps_obls _ δ0 !! τ)) *)
    (* (LBL: tr L!! n = Some τ) *)
    (DOM: is_Some (tr S!! (S n)))
    :
    ms_lt deg_le (APF (S n)) (APF n).
  Proof using.
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
    
    clear δ' NTH'. 
    intros δ τ' IDTHl. 
    red. intros δk k IDTH BOUND NSTEPS.
    
    generalize dependent δk. induction k.
    { intros ? ->%obls_utils.nsteps_0.
      rewrite Nat.add_0_r. reflexivity. }
    intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
    specialize (IHk ltac:(lia) _ STEPS).
    etrans; eauto.
    eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
    { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
    
    eapply any_expect_ms_le. 
    
    intros sid π d EXP. simpl.
    inversion EXP. subst.
    
    enough (set_before sid > n).
    { apply PeanoNat.Nat.le_succ_l in H1. 
      apply Nat.le_sum in H1 as [u EQ]. rewrite EQ. lia. }
    
    red.
    clear LE. 
    edestruct Nat.lt_ge_cases as [LT | LE]; [apply LT| ].   
    pose proof SET_BEFORE_SPEC as SB.
    assert (∀ c, ¬ never_set_after sid c) as SET by admit. 
    specialize (SB _ _ SET LE).
    rewrite IDTH in SB. simpl in SB.
    
    destruct (ps_sigs OP δ !! sid) as [[??]| ] eqn:SIG0; [| done].
    simpl in SB. subst. 
    (* signal cannot be unset *)
    assert (ps_sigs OP δ !! sid = Some (l, false)) as SIG0'.
    { admit. }
    congruence. 
    
  Admitted. 

  Lemma obls_fair_trace_terminate:
    obls_trace_valid OP tr ->
    (∀ τ, obls_trace_fair OP τ tr) ->
    terminating_trace tr.
  Proof using.
    
  Admitted. 

End Termination.
