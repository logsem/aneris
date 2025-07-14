Require Import Relation_Operators.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.traces Require Import inftraces trace_lookup.
From fairness Require Import utils_multisets utils_tactics.
From lawyer.obligations Require Import obligations_model.
From stdpp Require Import relations.


Ltac inv_loc_step_of_no_exp STEP :=
  destruct STEP as [T|[T|[T|T]]];
  [destruct T as (?π&?d&T) |
    destruct T as (?l&T) |
    destruct T as (?s&T) |
    destruct T as (?s&?π&?d&?d'&T)
  ];
  inversion T; subst. 

Ltac inv_loc_step_with_no_exp STEP :=
  destruct STEP as [T | T]; [inv_loc_step_of_no_exp T | inv_loc_step0 T]. 

Section PhaseFuel.
  Context `{OP: ObligationsParams Degree Level Locale LIM_STEPS}.
  Let OM := ObligationsModel.

  Definition loc_step_of_no_exp δ1 τ δ2 :=
    (exists π δ, burns_cp δ1 τ δ2 π δ) \/
    (exists l, creates_signal δ1 τ δ2 l) \/
    (exists s, sets_signal δ1 τ δ2 s) \/
    (exists s π δ δ', creates_ep δ1 τ δ2 s π δ δ')
  .

  Definition loc_step_with_no_exp δ1 τ δ2 :=
    loc_step_of_no_exp δ1 τ δ2 \/ loc_step0 δ1 δ2.

  Lemma loc_step_of_no_exp_weaken δ1 τ δ2
    (STEP: loc_step_of_no_exp δ1 τ δ2):
    loc_step_of δ1 τ δ2.
  Proof using.
    destruct STEP as [?|[?|[?|?]]]; red; eauto.
  Qed.
  
  Lemma loc_step_with_split δ1 τ δ2:
    loc_step_with δ1 τ δ2 <->
    (loc_step_with_no_exp δ1 τ δ2 \/ (exists sid π d, expects_ep δ1 τ δ2 sid π d)).
  Proof using.
    rewrite /loc_step_with_no_exp. split.
    - intros [T|T]; [inv_loc_step_of T| ].
      all: try by left; left; red; eauto.
      + left; left; red; eauto. set_solver.
      + by eauto. 
      + by eauto. 
    - intros [[T|?]|?]; red; eauto.
      2: { left. red. eauto. }
      left. red.
      destruct T as [?|[?|[?|?]]]; eauto.      
  Qed.
    
  Context (tr: obls_trace).
  
  Context (sig_bound: SignalId -> nat).
  
  Definition approx_expects (k: nat) (eps: gset (@ExpectPermission Degree)) :=
    ([^disj_union set] ep ∈ eps, let '(sid, π, d) := ep in
                         ((LIM_STEPS + 2) * sig_bound sid - k) *: {[+ d +]} ).
  
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

  Context (P: Phase -> Prop).
  Context `{forall π, Decision (P π)}. 
  
  Definition PF' (k: nat) (δ: ProgressState) :=
    (mset_map snd ∘ (mset_filter (fun '(π_, _) => P π_)) ∘ (ps_cps)) δ
      ⊎
      approx_expects k (filter (fun '(_, π_, _) => P π_) (ps_eps δ)).
  
  Definition TPF' (i: nat): gmultiset Degree :=
    from_option (PF' ((LIM_STEPS + 2) * i)) ∅ (tr S!! i).
 
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
    2: { apply ms_le_sub. 
         apply gmultiset_disj_union_subseteq_l. }      
    apply big_opS_ms_le; [apply _| ]. 
    intros [[??]?].
    apply ms_le_sub.
    apply scalar_mul_le. lia.
  Qed.
  
  Global Existing Instance deg_PO | 10. 

  Lemma ms_le_PF_le m n δ
    (LE: m <= n):
    ms_le deg_le (PF' n δ) (PF' m δ).
  Proof using.
    apply ms_le_disj_union; [apply _| ..].
    + apply ms_le_sub. apply mset_map_sub. apply mset_filter_subseteq_mono. mss.
    + apply ms_le_exp_mono; [lia | reflexivity].
  Qed. 
  
  Lemma approx_expects_add k eps e 
    (FRESH: e ∉ eps):
    let n := ((LIM_STEPS + 2) * sig_bound (fst $ fst e) - k) in
    approx_expects k (eps ∪ {[ e ]}) = approx_expects k eps ⊎ n *: {[+ e.2 +]}.
  Proof using.
    rewrite (union_comm_L _ {[ e ]}).
    rewrite /approx_expects.
    rewrite -leibniz_equiv_iff. 
    rewrite big_opS_insert; auto.
    rewrite gmultiset_disj_union_comm. f_equiv.
    destruct e as [[??]?]. done.
  Qed.
  
  Lemma exchange_cp_ms_le δ1 δ2 k π d d' n
    `{forall π, Decision (P π)}
    (EXC: exchanges_cp δ1 δ2 π d d' n):
    ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
  Proof using.
    clear -EXC OM. rewrite /PF'. 
    inversion EXC; subst. 
    destruct δ1. simpl in *. 
    apply ms_le_disj_union; [apply _| ..].
    + subst new_cps0.
      rewrite !mset_filter_disj_union mset_map_disj_union.
      rewrite !mset_filter_difference. 
      rewrite !mset_filter_mul_comm.
      rewrite !mset_filter_singleton. 
      destruct decide.
      2: { rewrite multiset_difference_empty gmultiset_scalar_mul_empty.
           rewrite mset_map_empty.
           eapply ms_le_Proper; [reflexivity | | reflexivity].
           mss. }
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
  
  Lemma create_ep_ms_le δ1 τ δ2 k s π d d'
    (CREATE: creates_ep δ1 τ δ2 s π d d'):
    ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
  Proof using.
    clear -CREATE OM.
    rewrite /PF'. inversion CREATE; subst.
    destruct δ1. simpl in *.
    subst new_cps0 new_eps0.
    
    rewrite !mset_filter_difference. 
    rewrite !mset_filter_singleton.        
    rewrite filter_union_L.
    destruct decide.
    2: { rewrite filter_singleton_not_L; [| tauto].
         rewrite multiset_difference_empty. rewrite union_empty_r_L.
         apply ms_le_disj_union; [apply _| ..].
         + apply ms_le_sub. reflexivity. 
         + apply ms_le_exp_mono; [lia | reflexivity]. }
    
    rewrite filter_singleton_L; [| tauto]. 
    
    rewrite mset_map_sub_diff. 
    2: { apply gmultiset_singleton_subseteq_l.
         by apply mset_filter_spec. }
    rewrite mset_map_singleton. simpl.
    
    destruct (decide ((s, π, d') ∈ ps_eps)).
    { rewrite union_comm_L subseteq_union_1_L; [| set_solver].
      apply ms_le_disj_union; [apply _| ..].
      + apply ms_le_sub. mss. 
      + apply ms_le_exp_mono; [lia | reflexivity]. }
    
    forward eapply (approx_expects_add (S k)) as ->.
    { by intros [??]%elem_of_filter. } 
    rewrite (gmultiset_disj_union_comm _ ((_ - _) *: _)) gmultiset_disj_union_assoc. 
    apply ms_le_disj_union; [apply _| ..]; revgoals. 
    + apply ms_le_exp_mono; [lia | reflexivity].
    + simpl. apply ms_le_exchange.
      * apply _. 
      * eapply elem_of_mset_map. eexists (_, _). split; eauto.
        apply mset_filter_spec. split; eauto. 
      * done.
  Qed.
  
  Lemma loc_step0_ms_le δ1 δ2 k
    (STEP: loc_step0 δ1 δ2)
    :
    ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
  Proof using.
    clear -STEP OM.
    inv_loc_step0 STEP. 
    - eapply exchange_cp_ms_le; eauto. 
    - inversion T; subst. destruct δ1. simpl.
      apply ms_le_disj_union; [apply _| ..].
      + apply ms_le_sub. apply mset_map_sub. mss. 
      + apply ms_le_exp_mono; [lia | reflexivity]. 
  Qed.
  
  Lemma loc_step_with_no_exp_ms_le δ1 τ δ2 k
    (STEP: loc_step_with_no_exp δ1 τ δ2)
    :
    ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
  Proof using.
    clear -STEP OM.
    inv_loc_step_with_no_exp STEP. 
    - destruct δ1. simpl in *.
      apply ms_le_disj_union; [apply _| ..].
      + apply ms_le_sub. apply mset_map_sub. apply mset_filter_subseteq_mono. mss.
      + apply ms_le_exp_mono; [lia | reflexivity].
    - destruct δ1. simpl in *.
      apply ms_le_disj_union; [apply _| ..].
      + apply ms_le_sub. apply mset_map_sub. mss. 
      + apply ms_le_exp_mono; [lia | reflexivity].
    - destruct δ1. simpl in *.  
      apply ms_le_disj_union; [apply _| ..].
      + apply ms_le_sub. apply mset_map_sub. mss. 
      + apply ms_le_exp_mono; [lia | reflexivity].
    - eapply create_ep_ms_le; eauto.
    - apply loc_step0_ms_le. red. left. eauto. 
    - apply loc_step0_ms_le. red. eauto. 
  Qed.
  
  Definition expect_ms_le δ1 τ δ2 k :=
    forall sid π' d,
      expects_ep δ1 τ δ2 sid π' d ->
      ms_le deg_le (PF' (S k) δ2) (PF' k δ1). 
  
  Lemma loc_step_ms_le δ1 τ δ2 k
    (STEP: loc_step_with δ1 τ δ2)
    (EXP_CASE: expect_ms_le δ1 τ δ2 k)
    :
    ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
  Proof using.
    apply loc_step_with_split in STEP as [NOEXP | EXP].
    - eapply loc_step_with_no_exp_ms_le; eauto.
    - destruct EXP as (?&?&?&?). eapply EXP_CASE; eauto.
  Qed.
  
  Definition nsteps_keep_ms_le i τ
    :=
    forall δ δ' mb mf k
      (ITH: tr !! i = Some (δ, Some (τ, δ')))
      (BOUND : k ≤ LIM_STEPS)
      (STEPS: nsteps (λ p1 p2, loc_step_ex p1 p2) k δ mb)
      (BSTEP: (∃ π δ, burns_cp mb τ mf π δ))
      (FSTEP: clos_refl (ProgressState) (λ p1 p2, ∃ τ' R, forks_locale p1 τ p2 τ' R) mf δ'),
      ms_le deg_le (PF' ((LIM_STEPS + 2) * i + k) mb) (PF' ((LIM_STEPS + 2) * i) δ).

  
  Lemma forks_locale_ms_le δ1 τ δ2 τ' R k
    (FORK: forks_locale δ1 τ δ2 τ' R):
    ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
  Proof using.
    rewrite /PF'.
    inversion FORK; subst. 
    destruct δ1. simpl in *.
    apply ms_le_disj_union; [apply _| ..].
    + apply ms_le_sub. apply mset_map_sub. mss. 
    + apply ms_le_exp_mono; [lia | reflexivity].
  Qed.
  
  Lemma om_trans_ms_rel (bd: bool) i
    (rel := (if bd then ms_lt deg_le else ms_le deg_le): relation (gmultiset Degree))
    (VALID: obls_trace_valid tr)
    (BURN_REL:
      forall δ δ' τ mb mf k,
        tr !! i = Some (δ, Some (τ, δ')) ->
        k ≤ LIM_STEPS ->
        nsteps (λ p1 p2, loc_step_ex p1 p2) k δ mb ->
        (∃ π δ, burns_cp mb τ mf π δ) ->
        clos_refl (ProgressState) (λ p1 p2, ∃ τ' R, forks_locale p1 τ p2 τ' R) mf δ' ->
        rel (PF' ((LIM_STEPS + 2) * i + LIM_STEPS + 1) mf) (PF' ((LIM_STEPS + 2) * i + LIM_STEPS) mb))
    (NSTEPS_LE: forall τ,
        tr L!! i = Some τ ->
        nsteps_keep_ms_le i τ)
    (DOM: is_Some (tr S!! (S i))):
    rel (TPF' (S i)) (TPF' i).
  Proof using.
    rewrite /TPF'. simpl.
    forward eapply (proj2 (label_lookup_states' _ _)) as [τ ITHl]; eauto.  
    forward eapply (state_lookup_prev _ _ DOM _ (PeanoNat.Nat.le_succ_diag_r _)).
    intros [δ ITH]. destruct DOM as [δ' ITH']. rewrite ITH ITH'. simpl. 
    
    forward eapply trace_valid_steps'' as STEP; eauto.
    { rewrite Nat.add_1_r. eauto. }
    simpl in STEP. red in STEP. destruct STEP as (mf & PSTEP & FSTEP).
    red in PSTEP. destruct PSTEP as (k & BOUND & (mb & PSTEP & BSTEP)).
    
    rewrite /nsteps_keep_ms_le in NSTEPS_LE. specialize_full NSTEPS_LE; eauto.
    { eapply state_label_lookup; eauto. rewrite Nat.add_1_r. eauto. }

    eapply BURN_REL in BSTEP; eauto.
    2: { eapply state_label_lookup; eauto. rewrite Nat.add_1_r. eauto. }

    assert (ms_le deg_le (PF' ((LIM_STEPS + 2) * S i) δ')
              (PF' ((LIM_STEPS + 2) * i + LIM_STEPS + 1) mf)) as LE. 
    { inversion FSTEP as [? FORK | ]. 
      2: { subst mf.
           rewrite /PF'. apply ms_le_disj_union; [apply _| ..].
           - reflexivity.
           - apply ms_le_exp_mono; [lia | reflexivity]. }
      destruct FORK as (?&?&?). 
      subst y. eapply ms_le_Proper; [| reflexivity| eapply forks_locale_ms_le; eauto].
      f_equiv. apply leibniz_equiv_iff. lia. }  
    
    destruct bd; subst rel.
    - eapply strict_transitive_l; [| apply NSTEPS_LE]. 
      eapply strict_transitive_r; [apply LE| ]. 
      eapply strict_transitive_l; [apply BSTEP| ].
      apply ms_le_PF_le. lia.
    - etrans; [| apply NSTEPS_LE].
      etrans; [apply LE| ].
      etrans; [apply BSTEP| ].
      apply ms_le_PF_le. lia.
  Qed.
  
  Lemma burns_cp_ms_le δ1 τ δ2 π' d k
    (STEP: burns_cp δ1 τ δ2 π' d):
    ms_le deg_le (PF' (S k) δ2) (PF' k δ1).
  Proof using.
    rewrite /PF'. 
    inversion STEP; subst.
    destruct δ1. simpl in *.
    apply ms_le_disj_union; [apply _| ..].
    + apply ms_le_sub. apply mset_map_sub.
      apply mset_filter_subseteq_mono. mss. 
    + apply ms_le_exp_mono; [lia | reflexivity].
  Qed.        
  
  Lemma burns_cp_own_ms_lt δ1 τ δ2 πτ πb d k
    (PH: ps_phases δ1 !! τ = Some πτ)
    (Pτ: P πb)
    (STEP: burns_cp δ1 τ δ2 πb d):
    ms_lt deg_le (PF' (S k) δ2) (PF' k δ1).
  Proof using.
    rewrite /PF'. 
    inversion STEP; subst.
    destruct δ1. simpl in *.
    
    eapply ms_le_lt_disj_union; [apply _| ..].
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
  
End PhaseFuel.
