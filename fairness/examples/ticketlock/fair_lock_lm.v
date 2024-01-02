From trillium.fairness.examples.ticketlock Require Import fair_lock.
From trillium.fairness.ext_models Require Import ext_models destutter_ext. 
From iris.proofmode Require Import tactics.
From stdpp Require Import base.
From trillium.fairness Require Import  lm_fair_traces trace_helpers fuel lm_fair lm_fairness_preservation trace_lookup.


(* TODO: move *)
Lemma ev_rel_after `(FLP: FairLockPredicates M) `(EM: ExtModel M) tr ρ i atr
  (* j atr *)
  (EV_REL : eventual_release tr ρ i)
  (AFTER: after i tr = Some atr)
  :
  (* eventual_release atr ρ (i - j). *)
  eventual_release atr ρ 0.
Proof.
  red. intros ρ' k **. red in EV_REL.
  specialize_full EV_REL.
  { erewrite state_lookup_after in JTH; eauto. }
  all: eauto.
  { intros LE. specialize_full AFTER0; [lia| ]. destruct AFTER0 as [? RESTR].
    split; auto.
    intros. destruct BETWEEN as [[d ->]%Nat.le_sum LE2].  
    eapply RESTR.
    2: { erewrite state_lookup_after; eauto. }
    lia. }
  destruct EV_REL as (?&?&?&[d ->]%Nat.le_sum&?).
  do 2 eexists. repeat split.
  { erewrite state_lookup_after with (k := k + d); eauto.
    by rewrite Nat.add_assoc. }
  { lia. }
  done.
Qed. 



Section FairLockLM.
  
  Context `(FL: @FairLock M FLP FLE).

  Let R := fmrole M.
  (* For the lock model (and others that also don't fork),
     we suppose that every group contains up to one role, 
     and this role uniquely corresponds to that group.
     Therefore, LM here only provides stuttering steps. *)
  Inductive G := | asG (r: R).

  Instance G_eqdec: EqDecision G.
  solve_decision.
  Qed.

  Instance G_cnt: Countable G.
  eapply inj_countable' with (f := fun '(asG ρ) => ρ) (g := asG).
  by intros []. 
  Qed.  

  Context `(LM: LiveModel G M LSI). 
  Context (LF: LMFairPre LM).

  Let LMF := LM_Fair (LF := LF).

  Let lift_prop1 (P: R -> fmstate M -> Prop): 
    fmrole LMF -> lm_ls LM -> Prop := 
        fun g δ => let '(asG ρ) := g in
                 P ρ (ls_under δ). 
          (* exists ρ, *)
          (*   ls_tmap (δ: fmstate LMF) !! g = Some {[ ρ ]} /\ *)
          (*   P ρ (ls_under δ). *)

  (*TODO: move *)
  Lemma gset_singleton_dec `{Countable K}:
    forall (g: gset K), {k | g = {[ k ]}} + (forall k, g ≠ {[ k ]}).
  Proof.
    intros. 
    destruct (decide (g = ∅)) as [-> | NE].
    { right. set_solver. }
    apply finitary.set_choose_L' in NE as [k IN].
    erewrite union_difference_singleton_L with (x := k) (Y := g); auto.
    destruct (decide (g ∖ {[k]} = ∅)) as [-> | NE']. 
    2: { apply finitary.set_choose_L' in NE' as [k' IN'].
         right. intros k''.
         intros EQ. apply (@f_equal _ _ size) in EQ.
         rewrite size_union in EQ; [| set_solver].
         rewrite !size_singleton in EQ.
         assert (size (g ∖ {[k]}) = 0) as S0 by lia.
         apply size_empty_inv in S0. set_solver. }
    rewrite union_empty_r_L. left. eauto.
  Qed. 

  Instance lift_prop1_dec P
    (DECP: forall ρ st, Decision (P ρ st)):
    forall g δ, Decision (lift_prop1 P g δ).
  Proof. 
    intros [g] δ. rewrite /lift_prop1.
    solve_decision. 
  Qed.

  Let wf_placeholder: lm_ls LM -> Prop.
  Admitted.

  (* TODO: move, find existing? *)
  Instance gtb_dec: forall x y, Decision (x > y).
  Proof. 
    intros. 
    destruct (lt_eq_lt_dec x y) as [[? | ->] | ?].
    3: by left.
    all: right; lia.
  Qed. 

  Instance FLP_LMF: FairLockPredicates LMF.
  refine {| 
      can_lock_st := lift_prop1 can_lock_st;
      has_lock_st := lift_prop1 has_lock_st;
      (* active_st := fun '(asG ρ) δ =>  *)
      (*       ls_tmap (δ: fmstate LMF) !! (asG ρ) = Some {[ ρ ]} /\ *)
      (*       (active_st ρ (ls_under δ) \/ default 0 (ls_fuel δ !! ρ) > 0); *)
      active_st := lift_prop1 active_st;
      is_unused := lift_prop1 is_unused;
      state_wf := wf_placeholder;
    |}.
  (* intros [?] ?. solve_decision.  *)
  Defined.

  Let lift_prop2 (P: fmrole M -> fmstate M -> fmstate M -> Prop):
    fmrole LMF -> lm_ls LM -> lm_ls LM -> Prop := 
        fun '(asG ρ) δ1 δ2 =>
            ls_tmap δ1 !! (asG ρ) = Some ∅ /\
            ls_tmap δ2 !! (asG ρ) = Some {[ ρ ]} /\              
            P ρ (ls_under δ1) (ls_under δ2).

  (* Let LM_active_exts (δ: fmstate LMF): gset (@fl_EI LMF) := *)
  (*       let active_under := fl_active_exts (ls_under δ) in *)
  (*       let g: G := @inhabitant G _ in *)
  (*       let lift := fun ι => match ι with *)
  (*                         | flU ρ => flU (default g (ls_mapping δ !! ρ)) (M := LMF) *)
  (*                         | flL ρ => flL (default g (ls_mapping δ !! ρ)) (M := LMF) *)
  (*                         end in *)
  (*       set_map lift active_under. *)

  Let allows_unlock := lift_prop2 allows_unlock. 
  Let allows_lock := lift_prop2 allows_lock.

  Instance lift_prop2_dec P
    (DECP: forall ρ st1 st2, Decision (P ρ st1 st2)):
    forall g δ1 δ2, Decision (lift_prop2 P g δ1 δ2).
  Proof.
    intros [g] δ1 δ2. rewrite /lift_prop2.
    solve_decision. 
  Qed.

  Instance allows_lock_ex_dec:
    forall δ g, Decision (∃ δ', allows_lock g δ δ'). 
  Proof using.
    intros δ [ρ]. simpl.
    eapply Decision_iff_impl. 
    { setoid_rewrite allows_lock_impl_spec.
      reflexivity. }
    destruct (decide (ls_tmap δ !! asG ρ = Some ∅ /\
                      can_lock_st ρ δ ∧ ¬ active_st ρ δ)). 
    2: { right. set_solver. }
    left. eexists {|        
        ls_under := allow_lock_impl ρ δ;
        ls_tmap := <[ asG ρ := {[ ρ ]} ]> (ls_tmap δ);
        ls_fuel := <[ ρ := 0 ]> (ls_fuel δ);
 |}.
    repeat split; eauto; try by apply a.
    simpl. by rewrite lookup_insert.
    Unshelve.
    1-4: admit. 
  Admitted. 


  Instance allows_unlock_ex_dec:
    forall δ g, Decision (∃ δ', allows_unlock g δ δ'). 
  Proof using.
    intros δ [ρ]. simpl.
    eapply Decision_iff_impl. 
    { setoid_rewrite allows_unlock_impl_spec.
      2: { admit. }
      reflexivity. }
    destruct (decide (ls_tmap δ !! asG ρ = Some ∅ /\
                      has_lock_st ρ δ ∧ ¬ active_st ρ δ)). 
    2: { right. set_solver. }
    left. eexists {|        
        ls_under := allow_unlock_impl ρ δ;
        ls_tmap := <[ asG ρ := {[ ρ ]} ]> (ls_tmap δ);
        ls_fuel := <[ ρ := 0 ]> (ls_fuel δ);
 |}.
    repeat split; eauto; try by apply a.
    simpl. by rewrite lookup_insert.
    Unshelve.
    1-4: admit. 
  Admitted. 

  Let tl_active_exts (δ: fmstate LMF): gset fl_EI := 
      set_map (flU (M := LMF)) 
          (filter (fun g => exists δ', allows_unlock g δ δ') (dom (ls_tmap δ)))
      ∪
      set_map (flL (M := LMF)) 
          (filter (fun g => exists δ', allows_lock g δ δ') (dom (ls_tmap δ))).
    

  Instance FLE_LMF: FairLockExt LMF.
  refine {|
      fair_lock.allows_unlock := allows_unlock;
      fair_lock.allows_lock := allows_lock;
      fair_lock.fl_active_exts := tl_active_exts;
    |}. 
  intros. simpl.
  unfold tl_active_exts.
  rewrite elem_of_union.
  rewrite !elem_of_map. repeat setoid_rewrite elem_of_filter.
  erewrite exist_proper.
  2: { intros g. rewrite and_assoc.
       apply iff_and_impl_helper.
       intros [-> [? AU]]. do 2 red in AU.
       destruct g. apply elem_of_dom.
       by rewrite (proj1 AU). }
  rewrite or_comm. 
  erewrite exist_proper.
  2: { intros g. rewrite and_assoc.
       apply iff_and_impl_helper.
       intros [-> [? AU]]. do 2 red in AU.
       destruct g. apply elem_of_dom.
       by rewrite (proj1 AU). }
  destruct ι; set_solver. 
  Defined.

  Lemma LM_EM_EXT_KEEPS: ext_keeps_asg
                              (ELM := (FL_EM FLE_LMF)).
  Proof.
    red.
  Admitted. 

  Let proj_ext (ι: @EI _ (FL_EM FLE_LMF)): @EI _ (FL_EM FLE) :=
        match ι with
        | flU (asG ρ) => flU ρ
        | flL (asG ρ) => flL ρ
        end. 
    
  Local Lemma PROJ_KEEP_EXT:
    forall δ1 ι δ2, (@ETs _ (FL_EM FLE_LMF)) ι δ1 δ2 -> 
                (@ETs _ (FL_EM FLE)) (proj_ext ι) (ls_under δ1) (ls_under δ2).
  Proof. 
    intros ? ι ? STEP. 
    destruct ι as [[ρ]| [ρ]]; simpl in *; apply STEP.
  Qed. 


  
  (* TODO: move, generalize *)
  Lemma upto_state_lookup_unfold2 i δ
    (lmtr: mtrace (@ext_model_FM LMF (@FL_EM LMF FLE_LMF)))
    (mtr: trace M (option ext_role))
    (UPTO: upto_stutter_eauxtr proj_ext lmtr mtr)
    (ITH : lmtr S!! i = Some δ):
    exists lmtr_i i' mtr_i',
              after i lmtr = Some lmtr_i /\
              after i' mtr = Some mtr_i' /\
              upto_stutter ls_under (EUsls proj_ext) lmtr_i mtr_i' /\
              mtr S!! i' = Some (ls_under δ).
  Proof. 
    pose proof ITH as (lmtr_i & AFTERi & TRi)%state_lookup_after'.
    pose proof AFTERi as X. eapply upto_stutter_after' in X as (i' & mtr_i' & AFTERi' & UPTOi); eauto.
    do 3 eexists. do 3 (try split; eauto).
    rewrite -TRi.
    erewrite state_lookup_after_0; eauto.
    f_equal. eapply upto_stutter_trfirst; eauto.
  Qed. 

  (* TODO: move, generalize *)
  Lemma upto_state_lookup_unfold1 i' st
    (lmtr: mtrace (@ext_model_FM LMF (@FL_EM LMF FLE_LMF)))
    (mtr: trace M (option ext_role))
    (UPTO: upto_stutter_eauxtr proj_ext lmtr mtr)
    (ITH : mtr S!! i' = Some st):
    exists mtr_i' i lmtr_i,
              after i lmtr = Some lmtr_i /\
              after i' mtr = Some mtr_i' /\
              upto_stutter ls_under (EUsls proj_ext) lmtr_i mtr_i' /\
              st = ls_under (trfirst lmtr_i). 
  Proof. 
    pose proof ITH as (mtr_i' & AFTERi' & TRi')%state_lookup_after'.
    pose proof AFTERi' as X. eapply upto_stutter_after in X as (i & lmtr_i & AFTERi & UPTOi); eauto.
    do 3 eexists. do 3 (try split; eauto).
    rewrite -TRi'.
    eapply upto_stutter_trfirst; eauto.
  Qed. 

  Lemma others_or_burn_keep_lock ρ':
    label_kept_state_gen
    (λ st' : fmstate (@ext_model_FM _ (FL_EM FLE_LMF)),
       has_lock_st ρ' (ls_under st') ∧ ¬ role_enabled_model ρ' (ls_under st'))
    (λ δ1 oℓ δ2,
       match oℓ with
       | Some (inl g) => next_TS_role δ1 g δ2 ≠ Some ρ'
       | _ => other_proj (asG ρ') oℓ
       end).
  Proof.
    red. intros. simpl in STEP. inversion STEP; subst.
    - simpl in STEP0. unfold_LMF_trans STEP0.
      + eapply step_keeps_lock_dis.
        { split; [admit| ].
          apply P1. }
        2: { simpl. left. simpl. apply STEP1. }                   
        red. simpl. intros ->. congruence. 
      + repeat apply proj2 in STEP1. congruence.
    - destruct ι; simpl in REL; red in REL.
      + destruct ρ as [ρ]. 
        eapply step_keeps_lock_dis.
        { split; [admit| ].
          apply P1. }
        2: { simpl. right. Unshelve. 2: exact (flU ρ).
             apply REL. }
        red. simpl.
        intros ->. simpl in PSTEP. congruence.
      + destruct ρ as [ρ]. 
        eapply step_keeps_lock_dis.
        { split; [admit| ].
          apply P1. }
        2: { simpl. right. Unshelve. 2: exact (flL ρ).
             apply REL. }
        red. simpl.
        intros ->. simpl in PSTEP. congruence.  
  Admitted. 

  Lemma ev_rel_inner (lmtr: elmftrace (ELM := FL_EM FLE_LMF))
    (mtr: trace M (option ext_role))
    (ρ : R)
    (UPTO : upto_stutter ls_under (EUsls proj_ext) lmtr mtr)
    (VALID: mtrace_valid lmtr)
    (FAIR: ∀ g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g lmtr)
    (EV_REL : eventual_release lmtr (asG ρ) 0):
  eventual_release mtr ρ 0.
  Proof.
    red in EV_REL. 
    red. intros.
    forward eapply upto_state_lookup_unfold1 as (mtr_i' & i & lmtr_i & AFTERi & AFTERi' & UPTOi & ITH'); eauto.
    
    assert (lmtr S!! i = Some (trfirst lmtr_i)) as ITH.
    { rewrite -(state_lookup_0 lmtr_i).
      erewrite (state_lookup_after lmtr lmtr_i); eauto. }
    
    
    assert (exists i' st', i <= i' /\
                        lmtr S!! i' = Some st' /\ has_lock_st ρ' st' /\
                        (* ¬ role_enabled_model ρ' st' /\ *)
                        ρ' ∉ dom (ls_mapping st') /\
                        ∀ (k : nat) (st' : fmstate ext_model_FM),
                          0 <= k <= i' - i
                          → lmtr_i S!! k = Some st'
                          → (λ δ : LiveState G M LSI,
                                has_lock_st ρ' (ls_under δ)
                                ∧ ¬ role_enabled_model ρ' (ls_under δ)) st').
    { destruct (decide (ls_mapping (trfirst lmtr_i) !! ρ' = Some (asG ρ'))).
      2: { exists i, (trfirst lmtr_i).
           do 2 (split; [eauto| ]). split. 
           { simpl. by rewrite -ITH'. }
           split. 
           { intros [? MAP]%elem_of_dom. apply n. rewrite MAP. 
             admit. (* employ a corresponding LSI *) }
           intros. assert (k = 0) as -> by lia.
           erewrite state_lookup_after in H0; eauto.
           rewrite Nat.add_0_r ITH in H0. inversion H0. subst. auto. }
      
      assert (mtrace_valid lmtr_i) as VALIDi.
      { eapply trace_valid_after; eauto. }

      assert (∀ g, fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g lmtr_i) as FAIRi.
      { intros. eapply fair_by_after; eauto. apply FAIR. }      
      
      apply group_fairness_implies_step_or_unassign with (ρ := ρ') in FAIRi; [| done].
      
      apply fair_by_gen_equiv in FAIRi.
      red in FAIR. specialize (FAIRi 0). specialize_full FAIRi.
      { erewrite state_lookup_after; eauto.
        rewrite Nat.add_0_r ITH. simpl.
        eapply elem_of_dom; eauto. }
      simpl in FAIRi. destruct FAIRi as [m_ FAIRi]. 
      pattern m_ in FAIRi. eapply min_prop_dec in FAIRi as [m [FAIRi MIN]].
      2: { admit. }
      destruct FAIRi as (δ_m & step_m & MTH & FAIRi).
      red in FAIRi.
      
      Set Printing Coercions.
      subst st'.
      
      assert (
          ∀ (k : nat) (st' : fmstate ext_model_FM),
            0 <= k <= m
            → lmtr_i S!! k = Some st'
            → (λ δ : LiveState G M LSI,
                  has_lock_st ρ' (ls_under δ)
                  ∧ ¬ role_enabled_model ρ' (ls_under δ)) st') as KEEP. 
      { eapply steps_keep_state_gen. 
        { eauto. }
        { eexists. split; eauto. rewrite state_lookup_0. reflexivity. }
        { apply others_or_burn_keep_lock. }
        { intros * [_ ?] KTH.
          destruct oℓ'; [| done]. simpl. 
          pose proof KTH as STEP. eapply trace_valid_steps' in STEP; [| eauto].
          simpl in STEP. 
          destruct f as [| [ι]]. 
          - intros EQ. specialize (MIN k). specialize_full MIN; [| lia].
            do 2 eexists. split; [done| ].
            red. right. simpl. red. simpl. do 3 eexists. repeat split; eauto.
          - intros EQ. specialize (MIN k). specialize_full MIN; [| lia].
            simpl in EQ. 
            assert (ls_tmap st1 !! (asG ρ') = Some ∅) as NOρ.
            { destruct ι; subst; inversion STEP; subst; simpl in REL; apply REL. }
            do 2 eexists. split; [done| ].
            left. intros (?& MAP)%elem_of_dom.
            assert (x = asG ρ') as ->.
            { admit. (* LSI *) }
            eapply ls_mapping_tmap_corr in MAP as (?&?&?). 
            set_solver. }
      }
      
      clear HAS_LOCK DIS.
      pose proof (KEEP m) as KEEPm. specialize_full KEEPm. 
      { split; [lia| reflexivity]. }
      { eapply trace_state_lookup. apply MTH. }
      destruct KEEPm as [HAS_LOCK DIS].
      
      destruct FAIRi as [UNMAP| STEP]. 
      2: { simpl in STEP. red in STEP.
           destruct STEP as (?&?&?&->&<-&STEP). 
           apply next_TS_spec_pos in STEP.
           simpl in STEP. 
           destruct DIS. red. eapply fm_live_spec.
           apply STEP. }
      
      exists (i + m). eexists. split; [lia| ]. 
      split; [| split]; [| | split| ..].
      { apply trace_state_lookup in MTH.
        erewrite state_lookup_after in MTH; [| eauto]. apply MTH. }
      { eauto. }
      { eauto. }
      intros ??.
      rewrite Nat.sub_add'. apply KEEP. }
    
    clear HAS_LOCK DIS.      
    destruct H as (m & δ_m & LEi & MTH & HAS_LOCK & UNMAP & BETWEEN). 
    
    specialize (EV_REL (asG ρ')). specialize_full EV_REL.
    { apply MTH. }
    { eauto. }
    { intros [? STEP]%LM_live_roles_strong.
      apply locale_trans_ex_role in STEP as [ρ'_ MAP].
      assert (ρ'_ = ρ') as ->.
      { admit. (* LSI *) }
      by apply UNMAP, elem_of_dom. } 
    { intros _. specialize (AFTER ltac:(lia)). destruct AFTER as [NEQ AFTER].
      split; [congruence| ].
      intros.
      assert (k <= i \/ i <= k <= i + m) as [BEFORE | CUR] by lia. 
      2: { intros LOCK2.
           specialize (BETWEEN (k - i)). specialize_full BETWEEN.
           { lia. }
           { erewrite state_lookup_after; eauto.
             rewrite -Nat.le_add_sub; eauto. lia. }
           apply proj1 in BETWEEN. simpl in LOCK2.
           eapply NEQ. eapply has_lock_st_excl; eauto. }
      (* The prefix of mtr corresponding to this prefix of lmtr
         doesn't have locks of ρ, according to AFTER.
         Need to split trace more precisely, stating that both pre- and postfixes       of traces a re related by upto_stutter
       *)
      admit. }
    
    destruct EV_REL as (p & δ_p & PTH & LEm & ENp).
    assert (i <= p) as [d ->]%Nat.le_sum by lia. 
    erewrite <-state_lookup_after in PTH; eauto.
    eapply upto_stutter_state_lookup' in PTH as [c CTH]; eauto.
    exists (j + c). eexists. repeat split.
    { erewrite <- state_lookup_after; eauto. }
    { lia. }
    apply ENp.
  Admitted.
    


  Lemma FL_LM_progress:
    @fair_lock_progress _ FLP_LMF (FL_EM FLE_LMF).
  Proof.
    red. intros lmtr [ρ] i δ **.
    clear FAIR. 
    assert (∀ g: G,
               fair_by_group (ELM_ALM LM_EM_EXT_KEEPS) g lmtr) as FAIR. 
    { admit. (* parametrize FairLock with the desired notion of fairness *) }
    pose proof (group_fairness_implies_role_fairness _ _ VALID FAIR) as FAIR'.
    pose proof (can_destutter_eauxtr proj_ext _ VALID) as [mtr UPTO].
    forward eapply destutter_ext.upto_preserves_validity as VALIDm; eauto. 
    { apply PROJ_KEEP_EXT. }
    forward eapply destutter_ext.upto_stutter_fairness as FAIRm; eauto.
    { eapply ELM_ALM_afair_by_next; eauto. }
    pose proof (@lock_progress _ _ _ FL) as PROGRESSm.    
    red in PROGRESSm.

    forward eapply upto_state_lookup_unfold2 as (lmtr_i & i' & mtr_i' & AFTERi & AFTERi' & UPTOi & ITH'); eauto. 
      
    specialize (PROGRESSm mtr_i' ρ 0 (ls_under δ)).
    specialize_full PROGRESSm; eauto.
    { eapply trace_valid_after; eauto. }
    { admit. }
    { do 2 red. intros. eapply fair_by_after; eauto. by apply FAIRm. }
    { erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r. }
    { eapply ev_rel_after in EV_REL; eauto.
      eapply ev_rel_inner; eauto.
      - eapply trace_valid_after; eauto. 
      - intros. eapply fair_by_after; eauto. apply FAIR. }

    clear dependent δ. 
    destruct PROGRESSm as (d' & st & NZ & DTH' & LOCK & DISM).
    eapply upto_stutter_state_lookup in DTH' as (d & δ & DTH & CORRd); [| by apply UPTOi].
    subst st.
    erewrite state_lookup_after in DTH; eauto.
    
    destruct (decide (ρ ∈ dom (ls_mapping δ))) as [MAP | UNMAP]. 
    2: { exists (i + d), δ. repeat split; try done. 
         { enough (d > 0); [lia| ]. red.
           admit. }
         apply LM_map_empty_notlive.
         destruct (ls_tmap δ !! asG ρ) eqn:Rρ; [| tauto].
         left. destruct (decide (g = ∅)) as [-> | NE]; [done| ].
         apply set_choose_L in NE as [ρ' IN].
         assert (ρ' = ρ) as -> by admit.
         edestruct UNMAP. apply elem_of_dom. exists (asG ρ).
         eapply ls_mapping_tmap_corr; eauto. }
    
    apply group_fairness_implies_step_or_unassign with (ρ := ρ) in FAIR; [| done].
    apply fair_by_gen_equiv, fair_by_gen'_strong_equiv in FAIR. 
    2, 3: solve_decision. 
    red in FAIR.
    specialize (FAIR (i + d)). specialize_full FAIR.
    { by rewrite DTH. }
    
    destruct FAIR as (p & δ' & step' & PTH & STEPp & MINp).
    rewrite /fairness_sat_gen in MINp.
    
    

  Instance FL_LM: FairLock LMF FLP_LMF FLE_LMF.
  esplit.
  12: { red. simpl. 
  

End FairLockLM.
