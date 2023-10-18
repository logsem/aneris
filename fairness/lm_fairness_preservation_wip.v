From stdpp Require Import option.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness fuel traces_match trace_utils.
From trillium.fairness Require Export lm_fairness_preservation. 
Require Import Coq.Logic.Classical.

(* TODO: move these files to trillium.fairness *)
From trillium.fairness.examples.comp Require Export trace_lookup trace_len my_omega lemmas trace_helpers.

From Paco Require Import paco1 paco2 pacotac.


(* TODO: rename *)
Section Foobar. 
  Context `{LM: LiveModel G M LSI}.
  Context `{Countable G}.

  Local Set Printing Coercions.

  Definition upto_stutter_auxtr_at `{LM: LiveModel G M LSI}
    auxtr (mtr: mtrace M) n m :=
    exists atr_aux atr_m, 
      after n auxtr = Some atr_aux /\
      after m mtr = Some atr_m /\ 
      upto_stutter_auxtr atr_aux atr_m (LM := LM).
    
  Lemma upto_stutter_step_correspondence_alt auxtr (mtr: mtrace M)
    (Po: LiveState G M LSI -> option (mlabel LM) -> Prop)
    (Pi: M -> option (option (fmrole M)) -> Prop)
    (LIFT: forall δ oℓ, Po δ oℓ -> Pi (ls_under δ) (match oℓ with 
                                              | Some ℓ => Ul ℓ (LM := LM)
                                              | None => None
                                              end))
    (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ))
    :
    upto_stutter_auxtr auxtr mtr (LM := LM) ->
    forall n, pred_at auxtr n Po ->
    exists m, pred_at mtr m Pi /\ upto_stutter_auxtr_at auxtr mtr n m. 
  Proof.
    intros UPTO n NTH.
    forward eapply pred_at_after_is_Some as [atr AFTER]; eauto.
    rewrite (plus_n_O n) pred_at_sum AFTER in NTH. 
    forward eapply upto_stutter_step_correspondence as (m&?&AFTERm&Pm&?); eauto.
    exists m. split.
    - rewrite (plus_n_O m) pred_at_sum AFTERm. apply Pm.
    - red. eauto.
  Qed.    

End Foobar. 


Section InnerLMTraceFairness.
  Context `{LMi: LiveModel Gi Mi LSIi}.
  Context `{INH_Gi: Inhabited Gi, EQ_Gi: EqDecision Gi}. 

  Context `{LMo: LiveModel Go Mo LSIo}.

  Context (lift_Gi: Gi -> fmrole Mo).
  Hypothesis (INJlg: Inj eq eq lift_Gi). 

  Context (state_rel: fmstate Mo → lm_ls LMi → Prop).

  Let lm_model_traces_match :=
    lm_exaux_traces_match_gen
      (fmtrans Mo)
      lift_Gi
      state_rel.


  Local Ltac gd t := generalize dependent t.

  Definition inner_obls_exposed (lmtr_o: auxtrace (LM := LMo)) :=
    forall k δo_k gi, lmtr_o S!! k = Some δo_k ->
                 (exists (δi: LiveState Gi Mi LSIi) (ρi: fmrole Mi),
                    state_rel (ls_under δo_k) δi /\
                    ls_mapping δi !! ρi = Some gi) ->
                 lift_Gi gi ∈ dom (ls_mapping δo_k). 
   

  (* TODO: rename? *)
  Lemma eventual_step_or_unassign lmtr_o mtr_o lmtr_i ρ gi δi f
    (MATCH: lm_model_traces_match mtr_o lmtr_i)
    (CORRo: upto_stutter_auxtr lmtr_o mtr_o (LM := LMo))
    (FAIR_SOU: forall gi, fair_aux_SoU (lift_Gi gi) lmtr_o (LM := LMo))
    (INNER_OBLS: inner_obls_exposed lmtr_o)
    (NOρ : ∀ (m : nat) (ℓ : lm_lbl LMi),
          lmtr_i L!! m = Some ℓ → ∀ go' : Gi, ℓ ≠ Take_step ρ go')
  (ASGρ : ∀ (k : nat) (δi_k : lm_ls LMi),
           lmtr_i S!! k = Some δi_k → ls_mapping δi_k !! ρ = Some gi)
  (ST0: lmtr_i S!! 0 = Some δi)
  (FUEL0: ls_fuel δi !! ρ = Some f):
    ∃ m, pred_at lmtr_i m (steps_or_unassigned ρ).
  Proof.    
    Local Set Printing Coercions.
    gd lmtr_i. gd δi. gd mtr_o. gd lmtr_o.
    pattern f. apply lt_wf_ind. clear f. intros f IH. intros. 
    pose proof (traces_match_first _ _ _ _ _ _ MATCH) as REL0.
    pose proof (upto_stutter_trfirst _ _ _ _ CORRo) as CORR0. 
    pose proof (ASGρ _ _ ST0) as MAPi. 
    
    pose proof (INNER_OBLS 0 (trfirst lmtr_o) gi) as OBLS0. specialize_full OBLS0.
    { apply state_lookup_0. }
    { do 2 eexists. split; eauto.
      rewrite -CORR0. rewrite state_lookup_0 in ST0. congruence. }
    
    pose proof (FAIR_SOU gi 0) as FAIR. specialize_full FAIR.
    { by apply pred_at_state_trfirst. }
    destruct FAIR as [n_lo STEPlo].
    
    simpl in STEPlo. apply pred_at_trace_lookup' in STEPlo as (δo_n & stepo & STLo & SOUn).
    
    rewrite /steps_or_unassigned in SOUn. destruct SOUn as [UNASG | [go STEP]].
    { forward eapply upto_stutter_state_lookup'; eauto.
      { eapply trace_state_lookup_simpl'; eauto. }
      intros [n_mo STmo]. simpl in STmo.
      forward eapply traces_match_state_lookup_1; [apply MATCH| apply STmo| ].
      intros (δi_n & STlmi & RELn).
      red in INNER_OBLS. specialize_full INNER_OBLS.
      { eapply trace_state_lookup_simpl'. eauto. }
      { eauto. }
      simpl in INNER_OBLS. congruence. }
    
    (* destruct stepo as [[? δo_n']|]; [| done]. *)
    destruct stepo as [[? δo_n']|].
    2: { simpl in *. by destruct STEP. }
    
    simpl in STEP. destruct STEP as [[=->] STEP]. 
    inversion STEP. subst. clear STEP. rename x into go. 
    
    forward eapply upto_stutter_step_correspondence_alt with 
      (Po := fun δ oℓ => δ = δo_n /\ oℓ = Some (Take_step (lift_Gi gi) go))
      (Pi := fun st ooρ => st = ls_under δo_n /\ ooρ = Some $ Some $ lift_Gi gi).
    { by intros ?? [-> ->]. }
    { by intros ?[??]. }
    { apply CORRo. }
    { apply pred_at_trace_lookup'. eauto. } 
    intros (n_mo & STEPmo & UPTO').
    
    (* apply pred_at_trace_lookup in STEPmo as (st_mo & STmo & -> & Lmo). *)
    apply pred_at_trace_lookup' in STEPmo as (? & step_ & STEPmo & -> & LBL).
    destruct step_ as [[ℓ_mo st_mo']|]; simpl in LBL; [| done].
    inversion LBL. subst ℓ_mo. clear LBL.
    pose proof STEPmo as (STmo & Lmo & STmo')%state_label_lookup.
    
    forward eapply traces_match_label_lookup_1; [apply MATCH| ..]; eauto. 
    intros (ℓ_lm & Llmi & LBL_MATCH).
    simpl in LBL_MATCH. destruct LBL_MATCH as (? & LIFT_EQ & MATCHgi).
    apply INJlg in LIFT_EQ. subst x.
    
    apply trace_label_lookup_simpl' in Llmi as (δi_n_mo & δi_n_mo' & STEPlmi).
    assert (forall δ n, lmtr_i S!! n = Some δ -> exists f', ls_fuel δ !! ρ = Some f' /\ f' <= f) as NOFUEL.  
    { intros δ n ST. 
      pose proof (ASGρ _ _ ST) as ASG.
      apply mk_is_Some, ls_same_doms' in ASG as [f' FUEL].
      forward eapply role_fuel_decreases with (i := n); eauto.
      2: { eapply traces_match_LM_preserves_validity; eauto. }  
      intros ?? ST'. apply ASGρ in ST'. by apply elem_of_dom. }
    
    forward eapply auxtrace_valid_steps' as TRANS; [| apply STEPlmi|]; eauto.
    { eapply traces_match_LM_preserves_validity; eauto. }
    
    pose proof STEPlmi as (ST&ST'&LBL)%state_label_lookup. 
    pose proof (NOFUEL _ _ ST) as (f_ & NOFUEL1 & LE_). 
    pose proof (NOFUEL _ _ ST') as (f_' & NOFUEL2 & LE_'). 

    assert (f_' < f -> ∃ m, pred_at lmtr_i m (steps_or_unassigned ρ)) as IH_APP.
    {
      clear -UPTO' STEPmo IH STLo ST' STEPlmi FAIR_SOU INNER_OBLS NOFUEL2 MATCH NOρ ASGρ.
      intros LT. 
      red in UPTO'. destruct UPTO' as (atr_lmo & atr_mo & AFTERlmo & AFTERmo & UPTO').
      apply trace_lookup_after_strong in STEPmo as (atr_mo' & AFTERmo' & HEADmo').
      rewrite AFTERmo in AFTERmo'. inversion AFTERmo'. subst atr_mo. 
      apply trace_lookup_after_strong in STLo as (atr_lo' & AFTERlo' & HEADlo').
      rewrite AFTERlmo in AFTERlo'. inversion AFTERlo'. subst atr_lmo.
      clear AFTERmo' AFTERlo'. 
      
      specialize IH with (m := f_') (lmtr_o := atr_lo') (mtr_o := atr_mo') (δi := δi_n_mo').
      apply trace_lookup_after_strong in STEPlmi as (atr_lmi & AFTERlmi & HEADlmi).
      specialize IH with (lmtr_i := atr_lmi).
      apply after_S_tr_cons in AFTERmo, AFTERlmo, AFTERlmi. 
      specialize_full IH.
      * lia. 
      * intros. eapply fair_by_after; eauto. apply FAIR_SOU. 
      * red. intros.
        erewrite state_lookup_after in H; eauto. 
      * punfold UPTO'; [| apply upto_stutter_mono].
        inversion UPTO'; subst; try done.
        inversion H7; eauto. done.
      * done. 
      * eapply traces_match_after' in AFTERmo as (?&A'&?); [| apply MATCH].
        rewrite AFTERlmi in A'. by inversion A'.
      * intros. eapply NOρ.
        rewrite -H. symmetry. eapply label_lookup_after; eauto.
      * intros. eapply ASGρ. 
        rewrite -H. symmetry. eapply state_lookup_after; eauto.
      * rewrite -ST'.
        rewrite (plus_n_O (_ + _)).
        rewrite -Nat.add_1_r in AFTERlmi. 
        eapply state_lookup_after; eauto.
      * destruct IH as [m PM].
        eexists (S n_mo + m). apply pred_at_sum.
        by rewrite AFTERlmi. }
     
    destruct ℓ_lm as [ρ' g| | ]; subst. 
    3: done. 
    - destruct (decide (ρ' = ρ)). 
      { subst. edestruct NOρ; eauto. }
      eapply IH_APP. 
      
      simpl in TRANS. destruct TRANS as (_&_&DECR&_).
      red in DECR. specialize (DECR ρ). specialize_full DECR. 
      1, 2: eapply elem_of_dom; eauto.
      { left; [congruence| ]. symmetry. eapply ASGρ; eauto. }
      rewrite NOFUEL1 NOFUEL2 /= in DECR. lia. 
    - eapply IH_APP; eauto.

      simpl in TRANS. destruct TRANS as (_&DECR&_).
      red in DECR. specialize (DECR ρ). specialize_full DECR. 
      1, 2: eapply elem_of_dom; eauto.
      { left; [congruence| ]. symmetry. eapply ASGρ; eauto. }
      rewrite NOFUEL1 NOFUEL2 /= in DECR.
       lia.
  Qed. 

  Lemma inner_obls_exposed_after tr atr a
    (INNER_OBLS: inner_obls_exposed tr)
    (AFTER: after a tr = Some atr):
    inner_obls_exposed atr.
  Proof using.
    red. intros ??? L.
    erewrite state_lookup_after in L; eauto.
  Qed. 
 

  (* TODO: rename? *)
  Lemma eventual_step_or_unassign_nth lmtr_o mtr_o lmtr_i ρ gi δi f n
    (MATCH: lm_model_traces_match mtr_o lmtr_i)
    (CORRo: upto_stutter_auxtr lmtr_o mtr_o (LM := LMo))
    (FAIR_SOU: forall gi, fair_aux_SoU (lift_Gi gi) lmtr_o (LM := LMo))
    (INNER_OBLS: inner_obls_exposed lmtr_o)
    (NOρ : ∀ (m : nat) (ℓ : lm_lbl LMi),
          n <= m -> lmtr_i L!! m = Some ℓ → ∀ go' : Gi, ℓ ≠ Take_step ρ go')
  (ASGρ : ∀ (k : nat) (δi_k : lm_ls LMi),
           n <= k -> lmtr_i S!! k = Some δi_k → ls_mapping δi_k !! ρ = Some gi)
  (ST0: lmtr_i S!! n = Some δi)
  (FUEL0: ls_fuel δi !! ρ = Some f):
    ∃ m, n <= m /\ pred_at lmtr_i m (steps_or_unassigned ρ).
  Proof.
    pose proof ST0 as X. eapply traces_match_state_lookup_2 in X as (st_mo_n & STm0 & REL0); [| apply MATCH].
    pose proof STm0 as (atr_mo_n & AFTERmo_n & HEADmo_n)%state_lookup_after'.
    pose proof AFTERmo_n as X. eapply upto_stutter_after in X as (k & atr_lmo_k & AFTERlmo_k & UPTOkn); eauto.
    pose proof AFTERmo_n as X. eapply traces_match_after' in X as (atr_lmi_n & AFTERlmi_n & MATCH'); eauto.

    (* TODO: unify with IH usage in eventual_step_or_unassign *)
    forward eapply eventual_step_or_unassign with (lmtr_o := atr_lmo_k) (mtr_o := atr_mo_n) (lmtr_i := atr_lmi_n); eauto.
    * intros. eapply fair_by_after; eauto. apply FAIR_SOU. 
    * eapply inner_obls_exposed_after; eauto.
    (* * punfold UPTOkn; [| apply upto_stutter_mono]. *)
    (*   inversion UPTOkn; subst; try done. *)
    (*   inversion H7; eauto. done. *)
    (* * done.  *)
    (* * eapply traces_match_after' in AFTERmo as (?&A'&?); [| apply MATCH]. *)
    (*   rewrite AFTERlmi in A'. by inversion A'. *)
    * intros. eapply NOρ. 
      2: { rewrite -H. symmetry. eapply label_lookup_after; eauto. }
      lia.
    * intros. eapply ASGρ. 
      2: { rewrite -H. symmetry. eapply state_lookup_after; eauto. }
      lia. 
    * rewrite -ST0.
      erewrite state_lookup_after; eauto.
    * intros [m PM].
      eexists (n + m). split; [lia| ].
      apply pred_at_sum. by rewrite AFTERlmi_n.
  Qed.

  Local Ltac by_contradiction_classic C :=
    match goal with
    | |- ?goal => destruct (classic goal) as [?|C]; first done; exfalso
    end.

  Lemma DNE_iff (P: Prop):
    P <-> ¬ ¬ P.
  Proof. 
    tauto. (* due to classic usage *)
  Qed. 

  (* TODO: is it possible to express the general principle of induction by burning fuel? *)
  Lemma owner_fixed_eventually `{LM: LiveModel G M LSI} `{Inhabited G} `{EqDecision G}
    (tr: auxtrace (LM := LM)) ρ n
    (NOρ: ∀ m ℓ, n ≤ m → tr L!! m = Some ℓ → ∀ g, ℓ ≠ Take_step ρ g)
    (ASGρ : ∀ m δ, n <= m -> tr S!! m = Some δ → ρ ∈ dom (ls_mapping δ))
    (VALID: auxtrace_valid tr) :
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
    2: { clear -EqDecision0.
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

    forward eapply auxtrace_valid_steps' as TRANS; [| apply STEP|]; eauto.
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

    apply CHANGE_. eapply IH.
    3: { apply FUEL'. }
    3: { eauto. }
    2: { lia. }

    pose proof MAP as [f_ FUEL_]%mk_is_Some%ls_same_doms'.

    forward eapply role_fuel_decreases_nth with (n := j) (i := m); eauto.
    { intros. eapply NOρ; [| apply H1]. lia. }
    { intros. eapply ASGρ; [| apply H1]. lia. }
    { lia. }
    intros LE'. 
    
    destruct ℓ; simpl in TRANS. 
    3: { by repeat apply proj2 in TRANS. }
    - do 2 apply proj2 in TRANS. apply proj1 in TRANS.
      red in TRANS. specialize (TRANS ρ). rewrite FUEL' FUEL_ in TRANS.
      specialize_full TRANS; [..| simpl in *; lia].
      1, 2: by eapply elem_of_dom.
      apply Change_tid; [congruence|].
      apply elem_of_dom. eapply (ASGρ (S m)); eauto. lia.
    - apply proj2 in TRANS. apply proj1 in TRANS.
      red in TRANS. specialize (TRANS ρ). rewrite FUEL' FUEL_ in TRANS.
      specialize_full TRANS; [..| simpl in *; lia].
      1, 2: by eapply elem_of_dom.
      apply Change_tid; [congruence|].
      apply elem_of_dom. eapply (ASGρ (S m)); eauto. lia.
  Qed.

  (* TODO: is it possible to unify this proof with those in lm_fairness_preservation? *)
  (* TODO: renaming of arguments? *)
  Lemma inner_LM_trace_fair_aux (lmtr_i: auxtrace (LM := LMi)) (tr_o: mtrace Mo) 
    (lmtr_o: auxtrace (LM := LMo)):
    upto_stutter_auxtr lmtr_o tr_o -> 
    (∀ gi, fair_aux_SoU (lift_Gi gi) lmtr_o) ->
    inner_obls_exposed lmtr_o -> (* TODO: should become unnecessary with LM state invariants *)
    infinite_trace tr_o ->
    lm_model_traces_match tr_o lmtr_i ->
    (∀ ρ, fair_model_trace ρ tr_o) -> (forall ρ, fair_aux ρ lmtr_i (LM := LMi)).
  Proof. 
    intros UPTO FAIR_SOU INNER_OBLS INF MATCH FAIRo ρ.
    destruct (classic (fair_aux ρ lmtr_i)) as [| UNFAIR]; [done| exfalso].

    rewrite /fair_aux in UNFAIR. 
    apply not_all_ex_not in UNFAIR as [n UNFAIR].
    apply imply_to_and in UNFAIR as [ENn UNFAIR].
    pose proof (not_ex_all_not _ _ UNFAIR) as X. simpl in X.
    clear UNFAIR. rename X into UNFAIR.

    assert (trace_len_is tr_o NOinfinity) as INF'.
    { pose proof (trace_has_len tr_o) as [? LEN].
      eapply infinite_trace_equiv in INF; eauto. by subst. }
    assert (trace_len_is lmtr_i NOinfinity) as INF''.
    { pose proof (trace_has_len lmtr_i) as [li ?].
      forward eapply traces_match_same_length as INF''; [| |by apply MATCH|]; eauto.
      by subst. }

    erewrite forall_proper in UNFAIR.
    2: { intros. apply pred_at_neg. by apply INF''. }
    simpl in UNFAIR. 
    setoid_rewrite pred_at_trace_lookup' in UNFAIR. 

    assert (forall m δi_m, n <= m -> lmtr_i S!! m = Some δi_m -> role_enabled ρ (ls_under δi_m)) as EN.
    { intros. apply Nat.le_sum in H as [d ->].
      specialize (UNFAIR d) as (? & ? & MTH & UNFAIR).
      eapply trace_state_lookup_simpl in MTH; eauto. subst.
      apply Decidable.not_or in UNFAIR.
      tauto. }
    assert (forall m ℓ, n <= m -> lmtr_i L!! m = Some ℓ -> forall go', ℓ ≠ Take_step ρ go') as NOρ.
    { intros. apply Nat.le_sum in H as [d ->].
      specialize (UNFAIR d) as (? & ? & MTH & UNFAIR).
      eapply trace_label_lookup_simpl in MTH as (?&?&EQ); eauto.
      inversion EQ. subst.
      apply Decidable.not_or, proj2 in UNFAIR.
      simpl in UNFAIR. intros ->. apply UNFAIR.
      eexists. split; eauto. red. eauto. }
      
    clear ENn. 

    assert (exists j go, n <= j /\ forall k δi_k, j <= k -> lmtr_i S!! k = Some δi_k ->
                                       ls_mapping δi_k !! ρ = Some go) 
      as (j & go & LE & ASGρ). 
    { eapply owner_fixed_eventually; eauto.
      2: { eapply traces_match_LM_preserves_validity; eauto. }
      intros. eapply ls_mapping_dom, EN; eauto. } 

    assert (is_Some (lmtr_i S!! j)) as [δi_j JTH].
    { eapply state_lookup_dom; eauto. done. }
    assert (is_Some (ls_fuel δi_j !! ρ)) as [f FUEL].
    { apply elem_of_dom. rewrite -ls_same_doms.
      apply ls_mapping_dom.
      eapply EN; eauto. }

    forward eapply eventual_step_or_unassign_nth with (n := j); eauto.
    { intros. eapply (NOρ m); eauto. lia. }
    
    rewrite /steps_or_unassigned. setoid_rewrite <- pred_at_or. 
    intros (m & LEjm & [UNMAP | STEP]).
    - apply pred_at_trace_lookup in UNMAP as (?&MTH&UNMAP).
      edestruct UNMAP; eauto. apply elem_of_dom. eauto.  
    - apply pred_at_trace_lookup in STEP as (?&MTH&[? STEP]).
      destruct STEP as [? [? ->]]. 
      edestruct (NOρ m); eauto. lia. 
  Qed. 
    
End InnerLMTraceFairness. 
