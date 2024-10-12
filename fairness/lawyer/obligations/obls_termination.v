Require Import Coq.Program.Wf.
Require Import Relation_Operators.
From stdpp Require Import namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len.
From trillium.fairness.lawyer.obligations Require Import obligations_model multiset_utils obls_utils wf_utils.
From stdpp Require Import relations.


Section Termination.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context `{Countable Locale}. 
  Let OM := ObligationsModel OP.

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
    rewrite /loc_step_no_exp_all. split.
    - intros [T|[T|[T|[T|[T|T]]]]]; tauto.
    - intros [[T|[T|[T|[T|T]]]] | ?]; red; tauto.
  Qed. 

  Section SignalsEventuallySet.
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
      
    Definition approx_expects (k: nat) (eps: gset (@ExpectPermission Degree)) :=
      ([^op set] ep ∈ eps, let '(sid, π, d) := ep in
        ((LIM_STEPS + 2) * set_before sid - k) *: {[+ d +]} ).

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

    Definition PF (π: Phase) (k: nat) (δ: ProgressState OP) :=
      (mset_map snd ∘ (mset_filter (fun '(π_, _) => phase_le π_ π)) ∘ (ps_cps OP)) δ
        ⊎
      approx_expects k (filter (fun '(_, π_, _) => phase_le π_ π) (ps_eps OP δ)). 

    Definition TPF (π: Phase) (i: nat): gmultiset Degree :=
      from_option (PF π ((LIM_STEPS + 2) * i)) ∅ (tr S!! i).

    Lemma ms_le_exp_mono m n X Y
      (LE: m <= n)
      (SUB: X ⊆ Y)
      :
      ms_le deg_le (approx_expects n X) (approx_expects m Y).
    Proof using.
      clear -LE SUB. 
      rewrite /approx_expects.
      apply union_difference_L in SUB. rewrite SUB.
      rewrite big_opS_union; [| set_solver].
      etrans.
      2: { rewrite gmultiset_op. apply ms_le_sub. 
           apply gmultiset_disj_union_subseteq_l. }      
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
      + apply ms_le_exp_mono; [lia | reflexivity].
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

    Lemma exchange_cp_ms_le π__ow δ1 τ δ2 k π d d' n
      (EXC: exchanges_cp OP δ1 τ δ2 π d d' n):
      ms_le deg_le (PF π__ow (S k) δ2) (PF π__ow k δ1).
    Proof using.
      clear -EXC. rewrite /PF. 
      inversion EXC; subst. 
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
      + apply ms_le_exp_mono; [lia | reflexivity].
    Qed.

    Lemma create_ep_ms_le π__ow δ1 τ δ2 k s π d d'
      (CREATE: creates_ep OP δ1 τ δ2 s π d d'):
      ms_le deg_le (PF π__ow (S k) δ2) (PF π__ow k δ1).
    Proof using.
      clear -CREATE. 
      rewrite /PF. inversion CREATE; subst.
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
           + apply ms_le_exp_mono; [lia | reflexivity]. }
      
      rewrite filter_singleton_L; [| tauto]. 
      
      rewrite mset_map_sub_diff. 
      2: { apply gmultiset_singleton_subseteq_l.
           by apply mset_filter_spec. }
      rewrite mset_map_singleton. simpl.
      
      destruct (decide ((s, π, d') ∈ ps_eps)).
      { rewrite union_comm_L subseteq_union_1_L; [| set_solver].
        apply ms_le_disj_union.
        + apply ms_le_sub. mss. 
        + apply ms_le_exp_mono; [lia | reflexivity]. }
      
      forward eapply (approx_expects_add (S k)) as ->.
      { by intros [??]%elem_of_filter. } 
      rewrite (gmultiset_disj_union_comm _ ((_ - _) *: _)) gmultiset_disj_union_assoc. 
      apply ms_le_disj_union; revgoals. 
      + apply ms_le_exp_mono; [lia | reflexivity].
      + simpl. apply ms_le_exchange.
        * apply _. 
        * eapply elem_of_mset_map. eexists (_, _). split; eauto.
          apply mset_filter_spec. split; eauto. 
        * done.
    Qed.

    Lemma loc_step_no_exp_all_ms_le π__ow δ1 τ δ2 k
      (STEP: loc_step_no_exp_all δ1 τ δ2)
      :
      ms_le deg_le (PF π__ow (S k) δ2) (PF π__ow k δ1).
    Proof using.
      clear -STEP OM.
      destruct STEP as [T|[T|[T|[T|T]]]]. 
      - destruct T as (?&?&T). inversion T; subst. 
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. apply mset_filter_subseteq_mono. mss.
        + apply ms_le_exp_mono; [lia | reflexivity].
      - destruct T as (?&?&?&?&T).
        eapply exchange_cp_ms_le; eauto. 
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_mono; [lia | reflexivity].
      - destruct T as (?&T). inversion T; subst.
        destruct δ1. simpl in *.  
        apply ms_le_disj_union.
        + apply ms_le_sub. apply mset_map_sub. mss. 
        + apply ms_le_exp_mono; [lia | reflexivity].
      - destruct T as (?&?&?&?&T). eapply create_ep_ms_le; eauto. 
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

    Let π0 := nroot. 

    Lemma other_expect_ms_le π__ow δ1 τ δ2 k
      (OTHER: let π := default π0 (ps_phases _ δ1 !! τ) in
              phases_incompat π__ow π):
      expect_ms_le π__ow δ1 τ δ2 k. 
    Proof using.
      clear LVL_WF SET_BEFORE_SPEC. 
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
      + apply ms_le_exp_mono; [lia | reflexivity].
    Qed.

    Lemma min_owner_expect_ms_le δ1 τ δ2 k
      (SET_BOUND: forall sid π d, expects_ep OP δ1 τ δ2 sid π d ->
                  let n := (LIM_STEPS + 2) * set_before sid in
                  k < n)
      :
      let π__ow := default π0 (ps_phases _ δ1 !! τ) in
      expect_ms_le π__ow δ1 τ δ2 k. 
    Proof using.
      clear LVL_WF SET_BEFORE_SPEC.
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
      { apply ms_le_exp_mono; [lia | reflexivity]. }

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
      + apply ms_le_exp_mono; [lia | reflexivity].
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
             - apply ms_le_exp_mono; [lia | reflexivity]. }
        destruct H1 as (?&?&?). 
        subst y. eapply ms_le_Proper; [| reflexivity| eapply forks_locale_ms_le; eauto].
        f_equiv. apply leibniz_equiv_iff. lia. }  

      destruct bd; subst rel.
      - eapply strict_transitive_l; [| apply PSTEP]. 
        eapply strict_transitive_r; [apply H1| ]. 
        eapply strict_transitive_l; [apply BSTEP| ].
        apply ms_le_PF_le. lia.
      - etrans; [| apply PSTEP].
        etrans; [apply H1| ].
        etrans; [apply BSTEP| ].
        apply ms_le_PF_le. lia.
    Qed.

    Lemma never_set_owned s c
      (NEVER_SET: never_set_after s c):
      forall i, c <= i ->
           map_Exists (fun τ obs => s ∈ obs) (from_option (ps_obls _) ∅ (tr S!! i)). 
    Proof using OM. Admitted. 

    Lemma burns_cp_ms_le δ1 τ δ2 π π' d k
      (STEP: burns_cp OP δ1 τ δ2 π' d):
      ms_le deg_le (PF π (S k) δ2) (PF π k δ1).
    Proof using.
      clear LVL_WF SET_BEFORE_SPEC. 
      rewrite /PF. 
      inversion STEP; subst.
      destruct δ1. simpl in *.
      apply ms_le_disj_union.
      + apply ms_le_sub. apply mset_map_sub.
        apply mset_filter_subseteq_mono. mss. 
      + apply ms_le_exp_mono; [lia | reflexivity].
    Qed.        

    Lemma other_om_trans_ms_le πτ τ n
      (VALID: obls_trace_valid OP tr)
      (PH: from_option (fun δ => ps_phases _ δ !! τ = Some πτ) False (tr S!! n))
      (NOτ: tr L!! n ≠ Some τ):
      ms_le deg_le (TPF πτ (S n)) (TPF πτ n).
    Proof using.
      destruct (tr S!! (S n)) as [δ'| ] eqn:NEXT.
      2: { rewrite /TPF. rewrite NEXT. simpl. apply empty_ms_le. }
     
      apply (om_trans_ms_rel false); auto.
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
      2: { rewrite /TPF. rewrite NEXT. simpl. apply empty_ms_le. }
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

    Lemma burns_cp_own_ms_lt δ1 τ δ2 πτ πb d k
      (PH: ps_phases _ δ1 !! τ = Some πτ)
      (STEP: burns_cp OP δ1 τ δ2 πb d):
      ms_lt deg_le (PF πτ (S k) δ2) (PF πτ k δ1).
    Proof using.
      clear tr SET_BEFORE_SPEC LVL_WF.
      rewrite /PF. 
      inversion STEP; subst.
      destruct δ1. simpl in *.

      eapply ms_le_lt_disj_union. 
      2: { apply ms_le_exp_mono; [ | reflexivity]. apply Nat.le_succ_diag_r. }
      
      apply strict_spec_alt.
      
      split. 
      { apply ms_le_sub. apply mset_map_sub.
        apply mset_filter_subseteq_mono. mss. }
      rewrite mset_filter_difference mset_filter_singleton.  
      rewrite mset_map_sub_diff. 

      2: { rewrite decide_True.
           2: { set_solver. }
           apply gmultiset_singleton_subseteq_l.
           apply mset_filter_spec. split; [done| ]. set_solver. }
      rewrite decide_True; [| set_solver]. 
      rewrite mset_map_singleton. simpl.
      apply gmultiset_disj_union_difference' in CP. rewrite CP.
      
      rewrite mset_filter_disj_union mset_filter_singleton decide_True; [| set_solver].
      rewrite mset_map_disj_union mset_map_singleton. simpl.
      mss. 
    Qed.         

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
      
      apply (om_trans_ms_rel true); auto.
      { intros.
        rewrite Nat.add_succ_r Nat.add_0_r.
        apply state_label_lookup in H1 as (NTH_&?&LBL_).
        rewrite LBL in LBL_. inversion LBL_. subst τ0. 
        rewrite NTH in NTH_. inversion NTH_. subst δ0. 
        destruct H4 as (?&?&?). 
        eapply burns_cp_own_ms_lt; eauto.
        rewrite -PH.
        (* phases are preserved by loc steps *)
        admit. }

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
             in
             default π0 π.

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
      rewrite /OTF. erewrite (S_OWNER _ d); eauto.
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
      rewrite /TPF.
      generalize ((LIM_STEPS + 2) * S (d + m)) as N. intros.
      rewrite plus_n_Sm -Nat.add_1_r Nat.add_assoc MTH'. simpl.
      rewrite /PF. apply ms_le_disj_union.
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
   
  End SignalsEventuallySet.


  Lemma obls_fair_trace_terminate (tr: obls_trace OP):
    obls_trace_valid OP tr ->
    (∀ τ, obls_trace_fair OP τ tr) ->
    terminating_trace tr.
  Proof using.
    
  Admitted. 


End Termination.
