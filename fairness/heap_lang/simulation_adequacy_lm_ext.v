From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fuel fuel_termination fairness_finiteness fair_termination_natural utils lm_fair lm_fairness_preservation fair_termination trace_len lemmas.
From trillium.fairness.heap_lang Require Import simulation_adequacy_lm.
From trillium.fairness.ext_models Require Import ext_models destutter_ext.
From trillium.fairness Require Import trace_lookup.
From Paco Require Import paco1 paco2 pacotac.


Section adequacy_general.
  Context `{CNT: Countable G}. 
  Context `{LM: LiveModel G M LSI}.

  Context {EM: ExtModel M}.
  Context {LF: LMFairPre LM}.
  Context {ELM: ExtModel LM_Fair}.

  Context {proj_ext : @EI _ ELM → @EI _ EM}. 
  Hypothesis (EXT_KEEP_ASG: forall δ1 ι δ2 ρ τ f,
                 @ext_trans _ ELM δ1 (Some $ inr ι) δ2 -> 
                 ls_mapping δ1 !! ρ = Some τ ->
                 ls_fuel δ1 !! ρ = Some f ->
                 ls_mapping δ2 !! ρ = Some τ /\ ls_fuel δ2 !! ρ = Some f). 
  Hypothesis PROJ_KEEP_EXT:
    forall δ1 ι δ2, (@ETs _ ELM) ι δ1 δ2 -> 
                (@ETs _ EM) (proj_ext ι) (ls_under δ1) (ls_under δ2). 

  Context {Mout: FairModel}. 
  Context {state_rel : fmstate Mout → lm_ls LM → Prop}. 
  Context {lift_erole: @ext_role _ ELM -> fmrole Mout}.
  Let lift_erole' := option_fmap _ _ lift_erole. 

  (* TODO: try to unify with lm_model_traces_match *)
  Definition ext_lm_model_traces_match: mtrace Mout -> elmftrace -> Prop :=
    traces_match 
      (out_A_labels_match lift_erole')
      state_rel
      (fmtrans Mout)
      ext_trans. 

  Lemma upto_stutter_ext_eventual_step (eauxtr: elmftrace) emtr
    (Hupto: upto_stutter_eauxtr proj_ext eauxtr emtr)
    (INF: infinite_trace eauxtr)
    (VALID: emtrace_valid eauxtr):
    exists i δ ℓ atr, after i eauxtr = Some (δ -[ℓ]-> atr) /\
              upto_stutter_eauxtr proj_ext (δ -[ℓ]-> atr) emtr /\
               (∃ ρ', EUsls proj_ext δ ℓ (trfirst atr) = Some ρ').
  Proof.
    remember (Ψ (trfirst eauxtr)) as f. generalize dependent eauxtr.
    pattern f. eapply lt_wf_ind. clear f. intros f IH.
    intros. destruct eauxtr.
    { destruct (INF 1); done. }
    simpl in Heqf. 
    apply trace_valid_cons_inv in VALID as [VALID STEP].
    destruct (EUsls proj_ext s ℓ (trfirst eauxtr)) eqn:EU. 
    { exists 0. do 3 eexists. eauto. } 
    eapply (fuel_dec_unless_step proj_ext) in STEP.
    destruct STEP as [STEP | [DECR EQ]]. 
    { exists 0. do 3 eexists. eauto. }
    punfold Hupto; [| apply upto_stutter_mono].
    inversion Hupto; subst.
    2: { by rewrite EU in H4. }
    Set Printing Coercions.
    specialize (IH _ DECR eauxtr). specialize_full IH; try done. 
    { by pfold. }
    { eapply infinite_cons; eauto. }
    destruct IH as (i & ?&?&?&?&?&?).
    exists (S i). do 3 eexists. eauto.
  Qed. 
          
  Lemma upto_stutter_ext_bounded (eauxtr: elmftrace) emtr
    (EXT_FIN: ext_trans_bounded eauxtr)
    (Hupto: upto_stutter_eauxtr proj_ext eauxtr emtr)
    (VALID: emtrace_valid eauxtr):
    ext_trans_bounded emtr.
  Proof.
    do 2 red in EXT_FIN. destruct EXT_FIN as [n EXT_FIN].
    destruct (infinite_or_finite eauxtr) as [INF| FIN]. 
    2: { eapply fin_trans_bounded. eapply upto_stutter_terminating_trace; eauto. }
    pose proof (INF n) as [atr AFTER]. 
    eapply upto_stutter_after' in Hupto as (m & atr2 & AFTER2 & UPTO'); eauto.
    exists m. intros i ℓ LE ITH. intros [ι ->]. 
    apply trace_label_lookup_simpl' in ITH as (s1 & s2 & ITH).
    apply trace_lookup_after_strong in ITH as (atri & AFTERi & Ai).
    apply Nat.le_sum in LE as [d ->].
    rewrite after_sum' AFTER2 in AFTERi. 
    eapply upto_stutter_after in UPTO' as (k & atrk & AFTERk & UPTO''); eauto.
    forward eapply (upto_stutter_ext_eventual_step _  _ UPTO'').
    { do 2 (eapply infinite_trace_after''; eauto). }
    { do 2 (eapply trace_valid_after; eauto). }
    intros (?&?&?&?&?&?&?&?).
    punfold H0; [| apply upto_stutter_mono]. inversion H0; subst.
    { by rewrite H1 in H5. }
    rewrite H1 in H9. inversion H9. subst. clear H9. 
    destruct x1; simpl in H1; [| done]. destruct f.
    { destruct lm_fair_traces.next_TS_role; congruence. }
    destruct e. inversion H1. subst. clear H1.
    destruct (EXT_FIN (n + k + x) (Some (inr (env i)))).
    { lia. }
    2: { eauto. }
    rewrite -plus_assoc. 
    erewrite <- label_lookup_after; eauto.
    erewrite <- label_lookup_after; eauto.
    rewrite <- (Nat.add_0_r x). erewrite <- label_lookup_after; eauto.
    done.
  Qed. 
    
  Theorem simulation_adequacy_terminate_general'_ext
    (otr: mtrace Mout) (eauxtr : elmftrace)
    :    
    (∀ emtr: @emtrace _ EM, ext_trans_bounded emtr -> emtrace_valid emtr -> inner_fair_ext_model_trace emtr -> terminating_trace emtr) ->
    ext_trans_bounded eauxtr ->
    (∀ ρ : fmrole M, fair_by_next_TS_ext ρ eauxtr) ->
    ext_lm_model_traces_match otr eauxtr ->
    mtrace_fairly_terminating otr.
  Proof.
    intros Hterm EXT_FIN Hfairaux Hmatch.
    red. intros VALID FAIR. 
    destruct (infinite_or_finite otr) as [Hinf|] =>//.
    pose proof Hmatch as Hvalaux%traces_match_valid2.
    destruct (can_destutter_eauxtr proj_ext eauxtr (LM := LM)) as [mtr Hupto] =>//.
    have Hfairm := upto_stutter_fairness _ _ _ Hupto Hfairaux.

    have Hmtrvalid := upto_preserves_validity _ _ _ _ Hupto Hvalaux.
    specialize (Hmtrvalid PROJ_KEEP_EXT). 

    eapply upto_stutter_ext_bounded in EXT_FIN; eauto.     
    have Htermtr := Hterm _ EXT_FIN Hmtrvalid Hfairm. 
    eapply traces_match_preserves_termination =>//.
    eapply upto_stutter_finiteness =>//.
  Qed.

End adequacy_general.