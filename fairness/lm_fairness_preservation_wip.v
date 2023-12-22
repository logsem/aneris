From stdpp Require Import option.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Import inftraces fairness fuel traces_match trace_utils.
From trillium.fairness Require Import lm_fairness_preservation lm_fair lm_fair_traces utils.
Require Import Coq.Logic.Classical.
From trillium.fairness Require Import trace_lookup trace_len my_omega lemmas trace_helpers utils.


(* TODO: move *)
Section LMTraceHelpers.
  Context `{CNT: Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {LF: LMFairPre LM}.

  Context {A: Type} {transA: lm_ls LM -> A -> lm_ls LM -> Prop}
    {AM: AlmostLM transA}.

  Local Ltac gd t := generalize dependent t.

  Lemma role_fuel_decreases (tr: atrace) δ0 ρ f0
    (ST0: tr S!! 0 = Some δ0)
    (FUEL0: ls_fuel δ0 !! ρ = Some f0)
    (NOρ: forall i δ τ δ',
        tr !! i = Some (δ, Some (am_lift_G τ, δ')) ->
                      next_TS_role δ τ δ' ≠ Some ρ)
    (ASGρ: ∀ i δ, tr S!! i = Some δ → ρ ∈ dom (ls_mapping δ))
    (VALID: trace_valid transA tr):
    forall i δ f, 
      tr S!! i = Some δ -> ls_fuel δ !! ρ = Some f -> f <= f0. 
  Proof.
    induction i; intros δ f ST FUEL. 
    { assert (δ0 = δ) as -> by congruence. 
      assert (f0 = f) as -> by congruence. 
      done. }
    
    pose proof (trace_has_len tr) as [len LEN]. 
    destruct (proj2 (trace_lookup_dom_strong _ _ LEN i)) as (δ' & ℓ & δ_ & STEP).
    { eapply mk_is_Some, state_lookup_dom in ST; eauto. 
      my_omega.lia_NO len. }
    
    pose proof (trace_valid_steps' _ _ VALID _ _ _ _ STEP) as TRANS. 
    apply state_label_lookup in STEP as (ST' & ST_ & LBL).
    assert (δ_ = δ) as ->; [| clear ST_].
    { rewrite Nat.add_1_r in ST_. congruence. }
    
    specialize (ASGρ _ _ ST'). rewrite ls_same_doms in ASGρ.
    pose proof ASGρ as ASGρ_.
    apply elem_of_dom in ASGρ as [f' FUEL'].
    specialize (IHi _ _ ST' FUEL').
    etrans; [| apply IHi].

    destruct (decide (exists g, am_lift_G g = ℓ)).
    2: { eapply am_transA_keep_fuel in FUEL'; eauto.
         rewrite FUEL in FUEL'. inversion FUEL'. lia. }
    destruct e. subst ℓ. apply am_lift_LM_step in TRANS. 

    unfold_LMF_trans TRANS.
    - destruct (decide (f1 = ρ)).
      2: { eapply step_nonincr_fuels in STEP; eauto. congruence. }
      subst. edestruct NOρ; eauto.  
      eapply state_label_lookup. rewrite Nat.add_1_r. eauto.
    - by eapply step_nonincr_fuels in STEP; eauto.
  Qed.

  Lemma role_fuel_decreases_nth (tr: atrace) δ0 ρ f0 n
    (ST0: tr S!! n = Some δ0)
    (FUEL0: ls_fuel δ0 !! ρ = Some f0)
    (NOρ: forall i δ τ δ', n <= i -> tr !! i = Some (δ, Some (am_lift_G τ, δ')) ->
                      next_TS_role δ τ δ' ≠ Some ρ)
    (ASGρ: ∀ i δ, n <= i -> tr S!! i = Some δ → ρ ∈ dom (ls_mapping δ))
    (VALID: trace_valid transA tr):
    forall i δ f, 
      n <= i -> tr S!! i = Some δ -> ls_fuel δ !! ρ = Some f -> f <= f0. 
  Proof.
    intros i δ f LE ITH FUEL.
    apply Nat.le_sum in LE as [d ->]. 
    pose proof ST0 as (atr & AFTER & HEAD)%state_lookup_after'.
    eapply role_fuel_decreases. 
    - erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r.
    - eauto.
    - intros. eapply (NOρ (n + i)); eauto.
      { lia. }
      erewrite <- @trace_lookup_after; eauto.
    - intros. eapply (ASGρ (n + i)); eauto.
      { lia. }
      rewrite -H. symmetry. eapply state_lookup_after; eauto.
    - eapply trace_valid_after; eauto. 
    - erewrite state_lookup_after; eauto.
    - eauto.
  Qed. 

  Local Ltac by_contradiction_classic C :=
    match goal with
    | |- ?goal => destruct (classic goal) as [?|C]; first done; exfalso
    end.

  Lemma owner_fixed_eventually 
    (tr: @atrace _ _ _ _ _ LM A) ρ n
    (NOρ: forall i δ τ δ', n ≤ i -> tr !! i = Some (δ, Some (am_lift_G τ, δ')) ->
                      next_TS_role δ τ δ' ≠ Some ρ)
    (ASGρ : ∀ m δ, n <= m -> tr S!! m = Some δ → ρ ∈ dom (ls_mapping δ))
    (VALID: trace_valid transA tr) :
  ∃ j g, n ≤ j ∧ ∀ k δ, j ≤ k → tr S!! k = Some δ → ls_mapping δ !! ρ = Some g.
  Proof.
    pose proof (trace_has_len tr) as [len LEN].
    assert (forall m, NOmega.le len (NOnum m) -> ∃ j g, n ≤ j ∧ 
                ∀ k δ, j ≤ k → tr S!! k = Some δ → ls_mapping δ !! ρ = Some g)
             as OVER. 
    { intros.
      assert (g: G) by eapply inhabitant.
      exists (max m n), g. split; [lia| ].
      intros ?? LEnk KTH.
      eapply mk_is_Some, state_lookup_dom in KTH; eauto.
      lia_NO len. }
    
    destruct (tr S!! n) as [δ|] eqn:NTH.
    2: { apply (OVER n). eapply state_lookup_dom_neg; eauto. }
    
    pose proof (ASGρ _ _ ltac:(eauto) NTH) as FUEL.
    rewrite ls_same_doms in FUEL. apply elem_of_dom in FUEL as [f FUEL].

    assert (exists j, n = j /\ n <= j) as (j & EQ & LE) by (exists n; lia).
    rewrite EQ in NTH. clear EQ. 
    gd δ. gd j. pattern f. apply lt_wf_ind. clear f. intros f IH. intros.
    
    by_contradiction_classic CHANGE.
    pose proof CHANGE as CHANGE_.
    pose proof FUEL as [g MAP']%mk_is_Some%ls_same_doms'. 
    apply not_ex_all_not with (n := j) in CHANGE.
    apply not_ex_all_not with (n := g) in CHANGE.
    apply not_and_or in CHANGE as [? | CHANGE]; [lia| ].

    apply not_all_ex_not in CHANGE as [m_ CHANGE].
    pattern m_ in CHANGE. apply min_prop_dec in CHANGE.
    2: { clear -LF.
         intros k.
         apply not_dec.
         destruct (tr S!! k) as [δ| ] eqn:KTH.
         2: { apply (Decision_iff_impl True); [split; done| apply _]. }
         destruct (decide (j <= k)) as [LE| ]. 
         2: { left. lia. }
         destruct (ls_mapping δ !! ρ) as [g'| ] eqn:MAP.
         2: { right. intros PP. specialize (PP _ LE eq_refl). congruence. }
         destruct (decide (g' = g)).
         - subst. left. intros. congruence.
         - right. intros PP. specialize (PP _ LE eq_refl). congruence. }
    clear m_. destruct CHANGE as (m & CHANGE & MIN). 
    
    apply not_all_ex_not in CHANGE as [δm' CHANGE].
    apply imply_to_and in CHANGE as [LEjm CHANGE]. 
    apply imply_to_and in CHANGE as [MTH' CHANGE].
    
    apply le_lt_eq_dec in LEjm as [LTjm| ->].
    2: { congruence. }
    destruct m; [lia| ].     
    
    forward eapply (proj2 (trace_lookup_dom_strong _ _ LEN m)).
    { eapply state_lookup_dom; eauto. by rewrite Nat.add_1_r. }
    intros (δm & ℓ & δm'_ & STEP).

    forward eapply trace_valid_steps' as TRANS; [| apply STEP|]; eauto.
    apply state_label_lookup in STEP as (MTH & MTH'_ & LBL).
    rewrite Nat.add_1_r MTH' in MTH'_. inversion MTH'_. subst δm'_. clear MTH'_.

    pose proof ASGρ as ASGm. 
    specialize_full ASGm.
    2: { apply MTH. }
    { lia. }
    apply elem_of_dom in ASGm as [g_ MAP]. 

    destruct (decide (g_ = g)) as [->| ]. 
    2: { subst. specialize (MIN m). specialize_full MIN; [| lia].
         intros MAPP. specialize (MAPP _ ltac:(lia) MTH). congruence. }

    pose proof ASGρ as ASGm'. 
    specialize_full ASGm'.
    2: { apply MTH'. }
    { lia. }
    apply elem_of_dom, ls_same_doms' in ASGm' as [f' FUEL']. 


    destruct (decide (exists g, am_lift_G g = ℓ)).
    2: { apply CHANGE. eapply am_transA_keep_mapping; eauto. }
    destruct e. subst ℓ. apply am_lift_LM_step in TRANS. 

    apply CHANGE_. eapply IH.
    3: { apply FUEL'. }
    3: { eauto. }
    2: { lia. }

    pose proof MAP as [f_ FUEL_]%mk_is_Some%ls_same_doms'.

    forward eapply role_fuel_decreases_nth with (n := j) (i := m); eauto.
    { intros. eapply NOρ; [| apply H0]. lia. }
    { intros. eapply ASGρ; [| apply H0]. lia. }
    { lia. }
    intros LE'.

    unfold_LMF_trans TRANS. 
    - do 2 apply proj2 in STEP. apply proj1 in STEP.
      red in STEP. specialize (STEP ρ). rewrite FUEL' FUEL_ in STEP.
      specialize_full STEP; [..| simpl in *; lia].
      1, 2: by eapply elem_of_dom.
      apply Change_tid; [congruence|].
      apply elem_of_dom. eapply (ASGρ (S m)); eauto. lia.
    - apply proj2 in STEP. apply proj1 in STEP.
      red in STEP. specialize (STEP ρ). rewrite FUEL' FUEL_ in STEP.
      specialize_full STEP; [..| simpl in *; lia].
      1, 2: by eapply elem_of_dom.
      apply Change_tid; [congruence|].
      apply elem_of_dom. eapply (ASGρ (S m)); eauto. lia.
  Qed.

End LMTraceHelpers.

Section UptoStutterAt. 
  Context `{CNT: Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {LF: LMFairPre LM}. 

  Local Set Printing Coercions.

  Definition upto_stutter_auxtr_at
    auxtr (mtr: mtrace M) n m :=
    exists atr_aux atr_m, 
      after n auxtr = Some atr_aux /\
      after m mtr = Some atr_m /\ 
      upto_stutter_auxtr atr_aux atr_m (LM := LM).
    
  Lemma upto_stutter_step_correspondence_alt auxtr (mtr: mtrace M)
    (Po: lm_ls LM -> option (option G * lm_ls LM) -> Prop)
    (Pi: M -> option (option (fmrole M) * M) -> Prop)
    (LIFT: forall δ ostep, Po δ ostep -> Pi (ls_under δ) (match ostep with 
                                              | Some (ℓ, δ') => match (Usls δ ℓ δ') with | Some r => Some (r, ls_under δ') | None => None end
                                              | None => None
                                              end))
    (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ))
    :
    upto_stutter_auxtr auxtr mtr (LM := LM) ->
    forall n so stepo,
      auxtr !! n = Some (so, stepo) ->
      Po so stepo ->
    exists m si stepi,
      mtr !! m = Some (si, stepi) /\ Pi si stepi /\
      upto_stutter_auxtr_at auxtr mtr n m.       
  Proof.
    intros UPTO n so stepo NTH Pon.
    destruct (proj2 (trace_lookup_after_weak auxtr so n)) as (atr&AFTER&A0); [by eauto| ].
    edestruct upto_stutter_step_correspondence as (m&amtr&s&stepi&AFTERm&Pm&?); eauto.
    { erewrite trace_lookup_after; eauto. by rewrite Nat.add_0_r. }
    do 3 eexists. repeat split.
    - erewrite trace_lookup_after in Pm; [| apply AFTERm].
      rewrite Nat.add_0_r in Pm. apply Pm. 
    - apply H.
    - red. do 2 eexists. repeat split; [..| apply H]; eauto. 
  Qed.    

End UptoStutterAt. 


Section InnerLMTraceFairness.
  Context `{CNTi: Countable Gi}.
  Context `{LMi: LiveModel Gi Mi LSIi}.
  Context `{CNTo: Countable Go}.
  Context `{LMo: LiveModel Go Mo LSIo}.
  Context {LFi: LMFairPre LMi} {LFo: LMFairPre LMo}.

  Context {Ai: Type} {transAi: lm_ls LMi -> Ai -> lm_ls LMi -> Prop}
    {AMi: AlmostLM transAi}.

  Context (lift_Ai: Ai -> option $ fmrole Mo).
  Hypothesis (INJlg: Inj eq eq lift_Ai). 
  Hypothesis (LIFT_SOME: forall gi, is_Some (lift_Ai (am_lift_G gi))). 

  Context (state_rel: fmstate Mo → lm_ls LMi → Prop).

  Let lm_model_traces_match :=
    lm_exaux_traces_match_gen
      (transA := transAi)
      (fmtrans Mo)
      (lift_Ai)
      state_rel.
  
  Local Ltac gd t := generalize dependent t.

  Definition inner_obls_exposed (lmtr_o: lmftrace (LM := LMo)) :=
    forall k δo_k gi, lmtr_o S!! k = Some δo_k ->
                 (exists (δi: LiveState Gi Mi LSIi) (ρi: fmrole Mi),
                    state_rel (ls_under δo_k) δi /\
                    ls_mapping δi !! ρi = Some gi) ->
                 exists r, lift_Ai (am_lift_G gi) = Some r /\ r ∈ dom (ls_mapping δo_k). 

  
  Lemma inner_obls_exposed_after tr atr a
    (INNER_OBLS: inner_obls_exposed tr)
    (AFTER: after a tr = Some atr):
    inner_obls_exposed atr.
  Proof using.
    red. intros ??? L.
    erewrite state_lookup_after in L; eauto.
  Qed. 
 
  Lemma inner_LM_trace_fair_aux_group (lmtr_i: atrace) (tr_o: mtrace Mo)
    (lmtr_o: lmftrace (LM := LMo)):
    upto_stutter_auxtr lmtr_o tr_o ->
    (∀ gi r, (lift_Ai $ am_lift_G gi) = Some r -> fair_aux_SoU (LM_ALM LMo) r lmtr_o) ->
    inner_obls_exposed lmtr_o -> 
    infinite_trace tr_o ->
    lm_model_traces_match tr_o lmtr_i ->
    (forall τ, fair_by_group AMi τ lmtr_i).
  Proof.
    intros UPTO FAIRlmo INNER_EXP INF MATCH.
    intros gi.
    set (fairness_cond := fun ρ st => exists gi, lift_Ai (am_lift_G gi) = Some ρ /\
                                              (∃ δi ρi,
         state_rel st δi ∧ ls_mapping δi !! ρi = Some gi)). 
    assert (forall ρ, fair_by fairness_cond role_match ρ tr_o).
    { clear gi.
      intros. red. intros n (st & NTH & COND)%pred_at_trace_lookup.
      red in COND. destruct COND as (gi & LIFTgi & (δi & ρi & STATES & MAPi)).
      
      pose proof NTH as (atr_o & AFTER & A0)%state_lookup_after'.
      setoid_rewrite pred_at_sum. rewrite AFTER.
      eapply upto_stutter_after in AFTER as (m & almtr_o & AFTER' & UPTO'); eauto.
      eapply inner_obls_exposed_after in INNER_EXP; eauto.
      specialize (FAIRlmo _ _ LIFTgi). eapply fair_by_gen_after in FAIRlmo; eauto. 
      clear dependent tr_o. clear dependent lmtr_o. clear m. 

      pose proof INNER_EXP as IE. 
      red in IE. specialize (IE 0 (trfirst almtr_o) gi).
      specialize_full IE.
      { apply state_lookup_0. }
      { do 2 eexists. split; eauto.
        Set Printing Coercions.
        erewrite <- upto_stutter_trfirst; eauto.
        congruence. }
      destruct IE as (ρ' & LIFT' & DOMρ).
      rewrite LIFTgi in LIFT'. inversion LIFT'. subst ρ'.
      red in FAIRlmo. specialize (FAIRlmo 0). specialize_full FAIRlmo.
      { by apply pred_at_state_trfirst. } 
      destruct FAIRlmo as (m & δo & stepo & MTH & FAIR). simpl in MTH.
      pattern δo, stepo in FAIR. 

      assert (almtr_o S!! m = Some δo) as MTH'.
      { eapply trace_state_lookup_simpl'; eauto. }        

      destruct FAIR as [UNMAP | STEP].
      { 
        assert (exists k st', ls_under δo = st' /\ atr_o S!! k = Some st') as (k & st' & CORR & KTH). 
        { pose proof MTH' as FF. 
          eapply upto_stutter_state_lookup' in FF as [??]; eauto. }
        exists k. apply pred_at_trace_lookup. eexists. split; eauto.
        red. left. intros F. apply UNMAP.
        red in F. destruct F as (gi' & LIFT'' & DOM).
        rewrite -LIFTgi in LIFT''. apply INJlg in LIFT''.
        red in INNER_EXP. specialize (INNER_EXP _ _ gi' MTH').
        rewrite CORR in INNER_EXP. specialize (INNER_EXP DOM).
        destruct INNER_EXP as (?&?&?). congruence. }

      set (Pi := fun (st: fmstate Mo) (ostep: option (option (fmrole Mo) * fmstate Mo)) => (∃ oℓ st', ostep = Some (oℓ, st') ∧ role_match ρ oℓ)). 
      forward eapply upto_stutter_step_correspondence_alt with (Pi := Pi).
      3: { apply UPTO'. }
      3: { apply MTH. }
      3: { apply STEP. }
      2: { intros. red in H. by destruct H as (?&?&?&?). }
      { intros. red in H. destruct H as (?&?&?&->&<-&?).
        red.
        rewrite /Usls. 
        rewrite /am_lift_G. simpl. rewrite H.
        do 2 eexists. split; eauto. }
      intros (k & st' & step & KTH & PROP & UPTO'').
      red in PROP. destruct PROP as (oℓ & st'' & -> & MATCH). 
      exists k. apply pred_at_trace_lookup. eexists. split.
      { eapply trace_state_lookup_simpl'; eauto. }
      simpl. red. right.
      apply state_label_lookup in KTH as (?&?&?). 
      eauto. }

    eapply model_fairness_preserved'.
    3: by apply MATCH.
    { apply _. }
    { by apply INF. }
    2: { by apply H. }

    red. intros. red. intros. red.
    destruct lift_Ai eqn:AA.
    2: { destruct (LIFT_SOME g). congruence. }
    red. eexists. split; eauto.   
  Qed.

  Lemma inner_LM_trace_fair_aux (lmtr_i: atrace) (tr_o: mtrace Mo) 
    (lmtr_o: lmftrace (LM := LMo)):
    upto_stutter_auxtr lmtr_o tr_o -> 
    (∀ gi r, (lift_Ai $ am_lift_G gi) = Some r -> fair_aux_SoU (LM_ALM LMo) r lmtr_o) ->
    inner_obls_exposed lmtr_o ->
    infinite_trace tr_o ->
    lm_model_traces_match tr_o lmtr_i ->
    (∀ ρ : fmrole Mi, afair_by_next_TS _ ρ lmtr_i). 
  Proof. 
    intros. revert ρ. apply group_fairness_implies_role_fairness.
    { by eapply traces_match_infinite_trace. }
    { by eapply traces_match_valid2. }
    eapply inner_LM_trace_fair_aux_group; eauto.
  Qed. 

End InnerLMTraceFairness. 
