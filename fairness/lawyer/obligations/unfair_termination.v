Require Import Coq.Program.Wf.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset gmultiset.
From trillium.fairness Require Import locales_helpers inftraces fairness trace_len my_omega utils_multisets utils_tactics obligations_wf obls_pf obls_termination.
From trillium.fairness.lawyer.obligations Require Import obligations_model wf_utils wf_ms.


Section ConstantTimeTermination.

  Context `{OP: ObligationsParams unit Empty_set Locale LIM_STEPS}.
  Let OM := ObligationsModel.

  Definition fuel_left δ: nat := size (ps_cps δ).

  Let PF'0 := PF' (fun _ => 0) (fun _ => True). 
  Let TPF'0 tr := TPF' tr (fun _ => 0) (fun _ => True). 

  Lemma nsteps_keep_ms_le_0 tr i τ:
    nsteps_keep_ms_le tr (λ _ : SignalId, 0) (λ _ : Phase, True) i τ.
  Proof using.
    red. intros.
    clear -STEPS. remember ((LIM_STEPS + 2) * i) as n. clear Heqn.
    generalize dependent mb. induction k.
    { intros. apply nsteps_0 in STEPS as ->.
      rewrite Nat.add_0_r. reflexivity. }
    intros.
    apply rel_compose_nsteps_next in STEPS as (δ' & STEPS & STEP).
    etrans.
    2: { eapply IHk; eauto. }
    rewrite Nat.add_succ_r. 
    red in STEP. destruct STEP as [[τ STEP] | STEP]. 
    2: by apply loc_step0_ms_le.  
    eapply loc_step_ms_le; eauto.
    { red. eauto. }
    red. intros. inversion H. subst. done.
  Qed.      

  Lemma om_trans0_ms_lt (tr: obls_trace)
    (VALID: obls_trace_valid tr)
    i
    (DOM: is_Some (tr S!! S i))
    :
    ms_lt deg_le
      (TPF'0 tr (S i))
      (TPF'0 tr i).
  Proof using.
    eapply om_trans_ms_rel with (bd := true); auto.
    { intros ????????? (π & d & BURNS) ?.
      inversion BURNS. subst. 
      rewrite Nat.add_1_r. 
      eapply burns_cp_own_ms_lt; eauto. }    
    intros. apply nsteps_keep_ms_le_0.
  Qed.

  Lemma PF'0_is_fuel k δ :
    PF'0 k δ ≡ mset_map snd (ps_cps δ).
  Proof using.
    rewrite /PF'0 /PF'.
    rewrite gmultiset_disj_union_Proper; [| reflexivity| ].
    2: { Unshelve. 2: exact ∅.
         rewrite /approx_expects. simpl.
         rewrite Nat.mul_0_r Nat.sub_0_l. simpl.
         etrans. 
         { eapply @big_opS_proper'; [| reflexivity].
           Unshelve. 2: exact (fun _ => ∅).
           red. intros [[]]. set_solver. }
         (* TODO: rename that lemma *)
         by rewrite multiplicity_big_DU_set_empty. }
    rewrite gmultiset_disj_union_right_id.
    rewrite /compose. rewrite mset_filter_True; [done| ].
    by intros [??].
  Qed.

  Lemma TPF'_is_fuel tr k:
    TPF'0 tr k ≡ mset_map snd (from_option ps_cps ∅ (tr S!! k)).
  Proof using.
    rewrite /TPF'0 /TPF'.
    destruct (tr S!! k) eqn:KTH; [| set_solver]. simpl.
    rewrite -PF'0_is_fuel. reflexivity. 
  Qed.

  Lemma cp0_simpl (δ: mstate OM) ED C:
    ((mset_map snd (ps_cps δ)): @gmultiset unit ED C) = fuel_left δ *: {[+ tt +]}.
  Proof using.
    rewrite /fuel_left. remember (ps_cps δ) as X. clear HeqX. 
    pattern X. apply gmultiset_ind; clear X.
    { mss. }
    intros [? []] X IH.
    rewrite mset_map_disj_union. rewrite mset_map_singleton. simpl.
    rewrite IH.
    rewrite gmultiset_size_disj_union gmultiset_size_singleton.
    simpl. mss.
  Qed.

  Lemma forall_unit_helper (P: unit -> Prop):
    (forall x, P x) <-> P ().
  Proof using.
    split.
    - eauto.
    - by intros ? [].
  Qed.

  (* TODO: generalize, move *)
  Lemma scalar_mul_singleton_ms_le m n ED C:
    ms_le deg_le ((m *: {[+ () +]}): @gmultiset unit ED C) (n *: {[+ () +]})
    <-> m <= n.
  Proof using.
    rewrite /ms_le.
    setoid_rewrite multiplicity_scalar_mul.
    rewrite forall_unit_helper.
    rewrite ex_det_iff. 
    2: { intros [] ?. reflexivity. }
    rewrite multiplicity_singleton.
    lia.
  Qed.

  Lemma fuel_left_decr (tr: obls_trace) i δ1 δ2
    (VALID: obls_trace_valid tr)
    (ITH: tr S!! i = Some δ1)
    (ITH': tr S!! (S i) = Some δ2):
    fuel_left δ2 < fuel_left δ1.
  Proof using.
    pose proof (om_trans0_ms_lt _ VALID i ltac:(eauto)) as LT.
    red in LT. rewrite !TPF'_is_fuel in LT.
    rewrite ITH ITH' in LT. simpl in LT.
    rewrite !cp0_simpl in LT.
    apply strict_spec_alt in LT as [LE NEQ].
    apply scalar_mul_singleton_ms_le in LE.
    apply Nat.le_lteq in LE as [? | ?]; [done| ].
    destruct NEQ. congruence.
  Qed.

  Definition trace_len_le {St L: Type} (tr: trace St L) (n: nat) :=
    exists len, trace_len_is tr (NOnum len) /\ len <= n.     

  Lemma always_terminates_within_bound (tr: obls_trace)
    (VALID: obls_trace_valid tr)
    (TR_WF: ∀ i δ, tr S!! i = Some δ → om_st_wf δ):
    trace_len_le tr (fuel_left (trfirst tr) + 1).
  Proof using.
    remember (fuel_left (trfirst tr)) as F.
    symmetry in HeqF. apply Nat.eq_le_incl in HeqF. 
    generalize dependent tr. induction F.
    { simpl. intros. exists 1. split; [| lia].
      destruct tr.
      { apply trace_len_singleton. }
      pose proof (trace_valid_steps' _ _ VALID 0 _ _ _ ltac:(eauto)) as STEP.
      simpl in HeqF.
      eapply fuel_left_decr with (i := 0) in VALID.
      2: done. 
      2: { rewrite state_lookup_cons. apply state_lookup_0. }
      lia. }

    intros. destruct tr.
    { exists 1. split; [| lia]. apply trace_len_singleton. }
    simpl in HeqF.

    pose proof VALID as VALID'.
    apply trace_valid_cons_inv in VALID' as [VALID_ STEP].
    specialize (IHF _ VALID_). specialize_full IHF.
    { intros. eapply TR_WF. erewrite <- state_lookup_cons in H. apply H. }
    { simpl. 
      eapply fuel_left_decr with (i := 0) in VALID.
      2: done.
      2: { rewrite state_lookup_cons. apply state_lookup_0. }
      
      remember (fuel_left (trfirst tr)) as X. rewrite -HeqX. 
      remember (fuel_left s) as Y.
      lia. }

    destruct IHF as [len [LEN ?]].
    exists (S len). split; [| lia].
    eapply trace_len_cons in LEN. apply LEN.
  Qed.     
  
End ConstantTimeTermination.


Section UnfairTermination.
  Context `{OP: ObligationsParams Degree Empty_set Locale LIM_STEPS}.
  Let OM := ObligationsModel.

  Context (tr: obls_trace).
  Hypothesis 
    (VALID: obls_trace_valid tr)
    (TR_WF: ∀ i δ, tr S!! i = Some δ → om_st_wf δ)
    (DEG_WF: wf (strict deg_le))
  .

  Lemma no_obls_wo_lvls δ (WF: om_st_wf δ):
    forall τ, default ∅ (ps_obls δ !! τ) = ∅.
  Proof using.
    clear -WF. 
    intros τ. destruct (ps_obls δ !! τ) as [R| ] eqn:OB; [| done]. simpl.
    destruct (set_choose_or_empty R) as [[s IN]| ]; [| set_solver].
    pose proof (om_wf_obls_are_sigs _ WF s) as SIG.
    rewrite flatten_gset_spec in SIG.
    setoid_rewrite elem_of_map_img in SIG. specialize (SIG ltac:(set_solver)).
    apply elem_of_dom in SIG as [[??] ?]. done.
  Qed.

  Lemma always_fair_wo_lvls:
    forall τ, obls_trace_fair τ tr.
  Proof using TR_WF.
    intros τ. red.
    apply fair_by_equiv. intros n OB.
    destruct (tr S!! n) eqn:NTH; rewrite NTH in OB; [| done]. 
    simpl in OB. red in OB.
    destruct OB. apply no_obls_wo_lvls.
    eapply TR_WF; eauto.
  Qed.

  Lemma always_term_wo_lvls:
    terminating_trace tr. 
  Proof using VALID TR_WF DEG_WF.
    apply obls_fair_trace_terminate; auto.
    2: { done. }
    apply always_fair_wo_lvls. 
  Qed.

End UnfairTermination.
