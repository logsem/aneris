From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len.
From trillium.fairness.lawyer.obligations Require Import obligations_model multiset_utils obls_utils.
From stdpp Require Import relations.
Require Import Coq.Program.Wf.
Require Import Relation_Operators.

Definition maximal {A C : Type} {H : ElemOf A C} (R : relation A) (x : A) (X : C) :=
  minimal (flip R) x X.

Section WfSetMin.
  Context {A: Type}.

  Definition minimal_in_prop (R : relation A) (x : A) (P : A -> Prop) :=
    ∀ y, P y → R y x → R x y. 
  
  Context {R: relation A}.
  Hypothesis (WF: wf R).

  Theorem sets_have_min (P: A -> Prop)
    (NE: exists a, P a):
    exists a, P a /\ minimal_in_prop R a P.
  Proof. Admitted.
  
End WfSetMin.


Section Termination.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP.

  Section SignalsEventuallySet.
    Context (tr: obls_trace OP).

    Hypothesis (LVL_WF: wf (strict lvl_le)).
    
    Context (lvl__def: Level). 

    Definition lvl_at (sid_i: SignalId * nat): Level :=
      let '(sid, i) := sid_i in
      from_option (fun δ => from_option fst lvl__def (ps_sigs _ δ !! sid)) lvl__def (tr S!! i).

    Definition tr_sig_lt: relation (SignalId * nat) := MR (strict lvl_le) lvl_at. 

    Lemma tr_sig_lt_wf: wf tr_sig_lt.
    Proof using LVL_WF. apply measure_wf. apply LVL_WF. Qed.

    Definition never_set_after sid c := 
      forall i, c <= i -> from_option (fun δ => from_option snd true (ps_sigs _ δ !! sid)) true (tr S!! i) = false. 

    Context {set_before: SignalId -> nat}.

    Definition approx_expects (k: nat) (eps: gset (@ExpectPermission Degree)) :=
      ([^op set] ep ∈ eps, let '(sid, π, d) := ep in
        ((LIM_STEPS + 2) * set_before sid - k) *: {[+ d +]}
      ).

    Instance cmp_phase'_dec: forall (x y: Phase * Degree),
        Decision (phase_le x.1 y.1).
    Proof using.
      intros [??] [??]. simpl.
      rewrite /phase_le. solve_decision.
    Qed. 

    Local Instance cmp_phase'_dec' π0:
      ∀ x : Phase * Degree, Decision ((λ '(π, _), phase_le π π0) x). 
    Proof using.
      intros [??]. simpl.
      rewrite /phase_le. solve_decision.
    Qed.

    Local Instance cmp_phase'_dec'' π0:
    ∀ x : SignalId * Phase * Degree, Decision ((λ '(_, π, _), phase_le π π0) x).
    Proof using.
      intros [[??]?]. rewrite /phase_le. solve_decision.
    Qed. 

    Let π0 := namespaces.nroot. 
    Definition PF (π: Phase) (k: nat) (δ: ProgressState OP) :=
      (mset_map snd ∘ (mset_filter (fun '(π_, _) => phase_le π_ π)) ∘ (ps_cps OP)) δ
        ⊎
      approx_expects k (filter (fun '(_, π_, _) => phase_le π_ π) (ps_eps OP δ)). 

    Definition TPF (π: Phase) (i: nat): gmultiset Degree :=
      from_option (PF π ((LIM_STEPS + 2) * i)) ∅ (tr S!! i).

    Lemma ms_le_exp_le m n eps
      (LE: m <= n):
      ms_le deg_le (approx_expects n eps) (approx_expects m eps).
    Proof using. 
      rewrite /approx_expects.
      eapply big_opS_ms_le. intros [[??]?].
      apply ms_le_sub.
      apply scalar_mul_le. lia.
    Qed.

    Lemma ms_le_PF_le m n π δ
      (LE: m <= n):
      ms_le deg_le (PF π n δ) (PF π m δ).
    Proof using.
      apply ms_le_disj_union.
      + apply ms_le_sub. apply mset_map_sub. apply mset_filter_subseteq_mono. mss.
      + apply ms_le_exp_le. lia.
    Qed. 

    Lemma approx_expects_add k eps e 
      (FRESH: e ∉ eps):
      let n := ((LIM_STEPS + 2) * set_before (fst $ fst e) - k) in
      approx_expects k (eps ∪ {[ e ]}) = approx_expects k eps ⊎ n *: {[+ e.2 +]}.
    Proof using.
      rewrite (union_comm_L _ {[ e ]}).
      rewrite /approx_expects.
      rewrite -leibniz_equiv_iff. 
      rewrite big_opS_insert; auto.
      rewrite gmultiset_op gmultiset_disj_union_comm. f_equiv.
      destruct e as [[??]?]. done.
    Qed.

    Definition phases_incompat π1 π2 := ¬ phase_le π1 π2 /\ ¬ phase_le π2 π1. 

    Definition loc_step_no_exp_all δ1 τ δ2 :=
      (exists π δ, burns_cp OP δ1 τ δ2 π δ) \/
      (exists π δ δ' n, exchanges_cp OP δ1 τ δ2 π δ δ' n) \/
      (exists l, creates_signal OP δ1 τ δ2 l) \/
      (exists s, sets_signal OP δ1 τ δ2 s) \/
      (exists s π δ δ', creates_ep OP δ1 τ δ2 s π δ δ').

    Lemma loc_step_split δ1 τ δ2:
      loc_step OP δ1 τ δ2 <->
      (loc_step_no_exp_all δ1 τ δ2 \/ (exists sid π d, expects_ep OP δ1 τ δ2 sid π d)).
    Proof using.
      clear set_before. 
      rewrite /loc_step_no_exp_all. split.
      - intros [T|[T|[T|[T|[T|T]]]]]; tauto.
      - intros [[T|[T|[T|[T|T]]]] | ?]; red; tauto.
    Qed. 
      
    Lemma loc_step_no_exp_all_ms_le π__ow δ1 τ δ2 k
      (STEP: loc_step_no_exp_all δ1 τ δ2)
      :
      ms_le deg_le (PF π__ow (S k) δ2) (PF π__ow k δ1).
    Proof using.
      clear LVL_WF.
      rewrite /PF.
      destruct STEP as [T|[T|[T|[T|T]]]]. 
      - destruct T as (?&?&T). inversion T; subst. 
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. apply mset_filter_subseteq_mono. mss.
        + apply ms_le_exp_le. lia.
      - destruct T as (?&?&?&?&T). inversion T; subst. 
        destruct δ1. simpl in *. 
        apply ms_le_disj_union.
        + subst new_cps0.
          rewrite !mset_filter_disj_union mset_map_disj_union.
          rewrite !mset_filter_difference. 
          rewrite !mset_filter_mul_comm.
          rewrite !mset_filter_singleton. 
          destruct decide.
          2: { rewrite decide_False; [| tauto].
               rewrite multiset_difference_empty gmultiset_scalar_mul_empty.
               rewrite mset_map_empty.
               eapply ms_le_Proper; [reflexivity | | reflexivity].
               mss. }
          rewrite decide_True; [| tauto].
          rewrite mset_map_sub_diff. 
          2: { apply gmultiset_singleton_subseteq_l.
               by apply mset_filter_spec. }
          rewrite mset_map_mul !mset_map_singleton. simpl.
          apply ms_le_exchange.
          * apply _. 
          * eapply elem_of_mset_map. eexists (_, _). split; eauto.
            apply mset_filter_spec. split; eauto. 
          * done. 
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.  
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_le. lia. 
      - destruct T as (?&?&?&?&T). inversion T; subst.
        destruct δ1. simpl in *.
        subst new_cps0 new_eps0.
        
        rewrite !mset_filter_difference. 
        rewrite !mset_filter_singleton.        
        rewrite filter_union_L.
        destruct decide.
        2: { rewrite filter_singleton_not_L; [| tauto].
             rewrite multiset_difference_empty. rewrite union_empty_r_L.
             apply ms_le_disj_union.
             + apply ms_le_sub. reflexivity. 
             + apply ms_le_exp_le. lia. }

        rewrite filter_singleton_L; [| tauto]. 

        rewrite mset_map_sub_diff. 
        2: { apply gmultiset_singleton_subseteq_l.
             by apply mset_filter_spec. }
        rewrite mset_map_singleton. simpl.

        destruct (decide ((x, x0, x2) ∈ ps_eps)).
        { rewrite union_comm_L subseteq_union_1_L; [| set_solver].
          apply ms_le_disj_union.
          + apply ms_le_sub. mss. 
          + apply ms_le_exp_le. lia. }
        
        forward eapply (approx_expects_add (S k)) as ->.
        { by intros [??]%elem_of_filter. } 
        rewrite (gmultiset_disj_union_comm _ ((_ - _) *: _)) gmultiset_disj_union_assoc. 
        apply ms_le_disj_union; revgoals. 
        + apply ms_le_exp_le. lia. 
        + simpl. apply ms_le_exchange.
          * apply _. 
          * eapply elem_of_mset_map. eexists (_, _). split; eauto.
            apply mset_filter_spec. split; eauto. 
          * done. 
    Qed.

    Definition expect_ms_le π δ1 τ δ2 k :=
      forall sid π' d,
        expects_ep _ δ1 τ δ2 sid π' d ->
        ms_le deg_le (PF π (S k) δ2) (PF π k δ1). 

    Lemma loc_step_ms_le π δ1 τ δ2 k
      (STEP: loc_step _ δ1 τ δ2)
      (EXP_CASE: expect_ms_le π δ1 τ δ2 k)
      :
      ms_le deg_le (PF π (S k) δ2) (PF π k δ1).
    Proof using.
      clear LVL_WF.
      apply loc_step_split in STEP as [NOEXP | EXP].
      - eapply loc_step_no_exp_all_ms_le; eauto.
      - destruct EXP as (?&?&?&?). eapply EXP_CASE; eauto.
    Qed. 

    Lemma other_expect_ms_le π__ow δ1 τ δ2 k
      (OTHER: let π := default π0 (ps_phases _ δ1 !! τ) in
              phases_incompat π__ow π):
      expect_ms_le π__ow δ1 τ δ2 k. 
    Proof using.
      clear LVL_WF. 
      red. intros sid π' d EXP. 
      rewrite /PF.
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
      + apply ms_le_exp_le. lia. 
    Qed.

    Lemma min_owner_expect_ms_le δ1 τ δ2 k
      (SET_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                  let n := (LIM_STEPS + 2) * set_before sid in
                  k < n)
      :
      let π__ow := default π0 (ps_phases _ δ1 !! τ) in
      expect_ms_le π__ow δ1 τ δ2 k. 
    Proof using.
      clear LVL_WF. 
      intros. red. intros sid π' d EXP. 
      rewrite /PF.

      inversion EXP; subst.
      destruct δ1. simpl in *. subst new_cps0.
      subst π__ow. rewrite LOC_PHASE. simpl. 
      
      rewrite !mset_filter_disj_union mset_map_disj_union.
      rewrite !mset_filter_singleton.
      rewrite decide_True; [| reflexivity]. rewrite mset_map_singleton. simpl. 

      (* rewrite mset_map_disj_union. *)
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
      { apply ms_le_exp_le. lia. }

      move SET_BOUND at bottom. specialize_full SET_BOUND; [by eauto| ].
      eapply ms_le_Proper; [reflexivity| ..| apply ms_le_refl].
      rewrite -gmultiset_scalar_mul_S_r. f_equiv. lia.
    Qed.

    Definition nsteps_keep_ms_le π δ i τ :=
      forall δ' k
      (ITH: tr S!! i = Some δ)
      (BOUND : k ≤ LIM_STEPS)
      (STEPS: nsteps (λ p1 p2, loc_step OP p1 τ p2) k δ δ'),
      ms_le deg_le (PF π ((LIM_STEPS + 2) * i + k) δ') (PF π ((LIM_STEPS + 2) * i) δ).

    Lemma forks_locale_ms_le π δ1 τ δ2 τ' R k
      (FORK: forks_locale OP δ1 τ δ2 τ' R):
      ms_le deg_le (PF π (S k) δ2) (PF π k δ1).
    Proof using.
      rewrite /PF.
      inversion FORK; subst. 
      destruct δ1. simpl in *.
      apply ms_le_disj_union.
      + apply ms_le_sub. apply mset_map_sub. mss. 
      + apply ms_le_exp_le. lia.
    Qed.

    Lemma om_trans_ms_rel (bd: bool) π i
      (rel := (if bd then ms_lt deg_le else ms_le deg_le): relation (gmultiset Degree))
      (VALID: obls_trace_valid OP tr)
      (BURN_REL:
        forall δ δ' τ mb mf k,
          tr !! i = Some (δ, Some (τ, δ')) ->
          k ≤ LIM_STEPS ->
          nsteps (λ p1 p2, loc_step OP p1 τ p2) k δ mb ->
          (∃ π δ, burns_cp OP mb τ mf π δ) ->
          clos_refl (ProgressState OP) (λ p1 p2, ∃ τ' R, forks_locale OP p1 τ p2 τ' R) mf δ' ->
          rel (PF π ((LIM_STEPS + 2) * i + LIM_STEPS + 1) mf) (PF π ((LIM_STEPS + 2) * i + LIM_STEPS) mb))
      (NSTEPS_LE: forall δ τ,
          tr L!! i = Some τ ->
          nsteps_keep_ms_le π δ i τ)
      (DOM: is_Some (tr S!! (S i))):
      rel (TPF π (S i)) (TPF π i).
    Proof using.
      rewrite /TPF. simpl.
      forward eapply (proj2 (label_lookup_states' _ _)) as [τ ITHl]; eauto.  
      forward eapply (state_lookup_prev _ _ DOM _ (PeanoNat.Nat.le_succ_diag_r _)).
      intros [δ ITH]. destruct DOM as [δ' ITH']. rewrite ITH ITH'. simpl. 

      forward eapply trace_valid_steps'' as STEP; eauto.
      { rewrite Nat.add_1_r. eauto. }
      simpl in STEP. red in STEP. destruct STEP as (mf & PSTEP & FSTEP).
      red in PSTEP. destruct PSTEP as (k & BOUND & (mb & PSTEP & BSTEP)).

      eapply BURN_REL in BSTEP; eauto.
      2: { eapply state_label_lookup; eauto. rewrite Nat.add_1_r. eauto. }
      eapply NSTEPS_LE in PSTEP; eauto. 

      assert (ms_le deg_le (PF π ((LIM_STEPS + 2) * S i) δ')
            (PF π ((LIM_STEPS + 2) * i + LIM_STEPS + 1) mf)).
      { inversion FSTEP.
        2: { subst mf.
             rewrite /PF. apply ms_le_disj_union.
             - reflexivity.
             - apply ms_le_exp_le. lia. }
        destruct H0 as (?&?&?). 
        subst y. eapply ms_le_Proper; [| reflexivity| eapply forks_locale_ms_le; eauto].
        f_equiv. apply leibniz_equiv_iff. lia. }  

      destruct bd; subst rel.
      - eapply strict_transitive_l; [| apply PSTEP]. 
        eapply strict_transitive_r; [apply H0| ]. 
        eapply strict_transitive_l; [apply BSTEP| ].
        apply ms_le_PF_le. lia.
      - etrans; [| apply PSTEP].
        etrans; [apply H0| ].
        etrans; [apply BSTEP| ].
        apply ms_le_PF_le. lia.
    Qed.

    Lemma never_set_owned s c
      (NEVER_SET: never_set_after s c):
      forall i, c <= i -> exists τ, s ∈ from_option (fun δ => default ∅ (ps_obls _ δ !! τ)) ∅ (tr S!! i).
    Proof. Admitted. 

    Lemma burns_cp_ms_le δ1 τ δ2 π π' d k
      (STEP: burns_cp OP δ1 τ δ2 π' d):
      ms_le deg_le (PF π (S k) δ2) (PF π k δ1).
    Proof using.
      clear LVL_WF. 
      rewrite /PF. 
      inversion STEP; subst.
      destruct δ1. simpl in *.
      apply ms_le_disj_union.
      + apply ms_le_sub. apply mset_map_sub.
        apply mset_filter_subseteq_mono. mss. 
      + apply ms_le_exp_le. lia.
    Qed.        

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
      2: { rewrite /TPF. rewrite NEXT. simpl. apply empty_ms_le. }
      apply (om_trans_ms_rel false); auto.
      { intros.
        rewrite Nat.add_succ_r. rewrite Nat.add_0_r.  
        destruct H3 as (?&?&?). eapply burns_cp_ms_le; eauto. }

      (* TODO: extract the lemma below? *)

      intros δ τ' IDTHl. 
      red. intros δk k IDTH BOUND NSTEPS.
      specialize (NOτ (i + d) ltac:(lia)). rewrite IDTHl in NOτ.
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
      assert (ps_phases _ δ !! τ = Some π) as PHδ.
      { (* phase preserved by non-τ steps *)
        admit. }
      assert (ps_phases _ δ' !! τ = Some π) as PHδ'.
      { (* phase preserved by loc steps *)
        admit. }
      (* should add a WF condition for pairwise phase incompatibility *)
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
      assert (τ__def: Locale) by admit. 

      set (s_ow (i: nat) :=
             let π := 
               δ ← tr S!! i;
               let owners := dom $ filter (fun '(_, obs) => s ∈ obs) (ps_obls _ δ) in
               let ow_phs := extract_Somes_gset $ set_map (fun τ => ps_phases _ δ !! τ) owners: gset Phase in
               ow ← gset_pick ow_phs;
               mret ow
             in
             default π0 π).

      set (OTF i := TPF (s_ow i) i).
      enough (exists d, c <= d /\ OTF d = ∅) as (d & LE & EMP). 
      { eapply never_set_owned in UNSET; [| apply LE].
        destruct (tr S!! d) as [δ| ] eqn:DTH; [| set_solver]. simpl in UNSET.
        destruct UNSET as [τ OWN]. 
        destruct (ps_obls OP δ !! τ) as [obs| ] eqn:OBLSd; [| done]. simpl in OWN.
        pose proof (FAIR τ) as F. apply fair_by_equiv, fair_by'_strenghten in F.
        2: { solve_decision. }
        red in F. specialize (F d). specialize_full F.
        { rewrite DTH. simpl. red. rewrite OBLSd. simpl. set_solver. }
        destruct F as (m & (δm & MTH & STEP) & MINm).

        assert (exists π, ps_phases _ δ !! τ = Some π) as [π PH].
        { (* follows from DPO *)
          admit. }
        (* rewrite /OTF /s_ow in EMP. *)
        (* rewrite DTH in EMP. simpl in EMP. *)
        (* setoid_rewrite elem_of_list_ret in EMP.  *)
        (* rewrite PH in EMP.  *)
        
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
        (* show that π is exactly the phase in EMP *)
        (* show that new TPF is also empty *)
        (* show the contradiction when the next step decreases it *)
        admit. 
        }
      
      admit.
    Admitted.        


    Lemma tr_loc_step_nsteps_ms_le π δ i τ δ' k
      (ITH: tr S!! i = Some δ)
      (BOUND : k ≤ LIM_STEPS)
      (STEPS: nsteps (λ p1 p2, loc_step OP p1 τ p2) k δ δ'):
      ms_le deg_le (PF π (2 * (LIM_STEPS + 2) * i + k) δ') (PF π (2 * (LIM_STEPS + 2) * i) δ).
    Proof using.
      generalize dependent δ'.
      induction k.
      { intros ? ->%obls_utils.nsteps_0.
        rewrite Nat.add_0_r. reflexivity. }
      intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
      specialize (IHk ltac:(lia) _ STEPS).
      etrans; eauto.

      eapply ms_le_Proper; [| | eapply loc_step_ms_le]; eauto.
      { rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
      red. 

      eapply loc_step_ms_le. 

      (* follows from well-formedness of state *)
      assert (ps_phases OP δ !! τ = Some π__ow) as PH by admit. rewrite PH. simpl. 
      (* follows from preservation of phases before fork *)
      assert (ps_phases OP δ' !! τ = Some π__ow) as PH' by admit. 
      
      eapply ms_le_Proper; [| | eapply min_owner_loc_step_ms_le]; eauto.
      { rewrite PH'.
        rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
      { rewrite PH'. simpl. reflexivity. }

      intros sid π d EXP. simpl.
      inversion EXP. subst.
      rewrite PH' in LOC_PHASE. inversion LOC_PHASE. subst π__max.

      enough (set_before sid > i).
      { apply PeanoNat.Nat.le_succ_l in H0. 
        apply Nat.le_sum in H0 as [u EQ]. rewrite EQ. lia. }

      clear -NEVER_SET ITH OBLS_LT SET_BEFORE_SPEC MIN.

      foobar.



    Hypothesis (SET_BEFORE_SPEC: 
                 forall sid i,
                   (forall c, ¬ never_set_after sid c) ->
                   set_before sid <= i ->
                   from_option (fun δ => from_option snd false (ps_sigs _ δ !! sid)) false (tr S!! i) = true).

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

      pose proof (SET_BEFORE_SPEC sid i). specialize_full H0; [| done| ].
      2: { rewrite ITH in H0. simpl in H0.
           rewrite SIG0 in H0. done. }

      intros c NEVER_SET_.
      assert (never_set_after sid i) as NEVER_SET' by admit. clear NEVER_SET_.
      move MIN at bottom. red in MIN. specialize (MIN (_, _) NEVER_SET').
      rewrite /tr_sig_lt /MR in MIN. simpl in MIN.
      rewrite ITH in MIN. simpl in MIN. rewrite SIG0 SIG__min in MIN. simpl in MIN.
      specialize (MIN OBLS_LT).
      edestruct @strict_not_both; eauto. 
    Admitted.
      

    (* TODO: remove this copy? *)
    Lemma tr_loc_step_nsteps_ms_le δ i τ δ' k
      (ITH: tr S!! i = Some δ)
      (BOUND : k ≤ LIM_STEPS)
      (STEPS: nsteps (λ p1 p2, loc_step OP p1 τ p2) k δ δ'):
      let π__ow := default π0 (ps_phases _ δ !! τ) in
      ms_le deg_le (PF π__ow (2 * (LIM_STEPS + 2) * i + k) δ') (PF π__ow (2 * (LIM_STEPS + 2) * i) δ).
    Proof using.
      generalize dependent δ'.
      induction k.
      { intros ? ->%obls_utils.nsteps_0.
        rewrite Nat.add_0_r. reflexivity. }
      intros δ'' (δ' & STEPS & STEP)%nsteps_inv_r.
      specialize (IHk ltac:(lia) _ STEPS).
      etrans; eauto.

      (* follows from well-formedness of state *)
      assert (ps_phases OP δ !! τ = Some π__ow) as PH by admit. rewrite PH. simpl. 
      (* follows from preservation of phases before fork *)
      assert (ps_phases OP δ' !! τ = Some π__ow) as PH' by admit. 
      
      eapply ms_le_Proper; [| | eapply min_owner_loc_step_ms_le]; eauto.
      { rewrite PH'.
        rewrite -PeanoNat.Nat.add_succ_comm. simpl. reflexivity. }
      { rewrite PH'. simpl. reflexivity. }

      intros sid π d EXP. simpl.
      inversion EXP. subst.
      rewrite PH' in LOC_PHASE. inversion LOC_PHASE. subst π__max.

      enough (set_before sid > i).
      { apply PeanoNat.Nat.le_succ_l in H0. 
        apply Nat.le_sum in H0 as [u EQ]. rewrite EQ. lia. }

      clear -NEVER_SET ITH OBLS_LT SET_BEFORE_SPEC MIN.
      
   
  End SignalsEventuallySet.


  Lemma obls_fair_trace_terminate (tr: obls_trace OP):
    obls_trace_valid OP tr ->
    (∀ τ, obls_trace_fair OP τ tr) ->
    terminating_trace tr.
  Proof using.
    
  Admitted. 


End Termination.
