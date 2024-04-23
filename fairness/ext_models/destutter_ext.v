From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Import inftraces fairness trace_utils.
From trillium.fairness Require Import fuel lm_fair lm_fair_traces.
From trillium.fairness.ext_models Require Import ext_models.

(* TODO: is it possible to unify usual and ext-aware versions of these proofs? *)

Section destuttering_auxtr.
  Context `{Countable G}. 
  Context `{LM: LiveModel G M LSI}.
  Context {EM: ExtModel M}.
  (* Let EMF := ext_model_FM (EM := EM).  *)
  Context {LF: LMFairPre LM}.

  (* Let LMF := LM_Fair (LM := LM). *)
  Context {ELM: ExtModel LM_Fair}.

  Context (proj_ext: (@EI _ ELM) -> (@EI _ EM)).   

  (* Definition EUsls (_: lm_ls LM) (ℓ: ELM.(mlabel)) (_: lm_ls LM): *)
  (*   option (option (@ext_role _ EM)) := *)
  (*   match ℓ with *)
  (*   | inl (Take_step ρ _) => Some (Some (inl ρ)) *)
  (*   | inr e => Some $ Some $ inr $ env $ proj_ext $ e *)
  (*   | _ => None *)
  (*   end. *)
  Definition EUsls (δ1: lm_ls LM) (oτ: option (@ext_role _ ELM)) (δ2: lm_ls LM):
    option $ option $ @ext_role _ EM :=
    match oτ with 
    | Some (inl τ) => match (next_TS_role δ1 τ δ2) with 
                     | Some ρ => Some $ Some (inl ρ)
                     | None => None
                     end
    | Some (inr (env ι)) => Some $ Some $ inr $ env $ proj_ext ι
    | None => None
    end. 

  Definition Ψ (δ: LiveState G M LSI) :=
    size δ.(ls_fuel) + [^ Nat.add map] ρ ↦ f ∈ δ.(ls_fuel (G := G)), f.


  Lemma fuel_dec_unless_lm_step δ τ δ'
    (* (Htrans : lm_ls_trans LM δ ℓ δ') *)
    (Htrans: locale_trans δ τ δ'):
    (∃ ρ' : fmrole M, EUsls δ (Some $ inl τ) δ' = Some $ Some $ inl ρ') ∨
    Ψ δ' < Ψ δ ∧ ls_under δ = ls_under δ'.
  Proof.
    unfold_LMF_trans Htrans. 
    (* destruct ℓ as [| tid' |]; *)
    (*   [left; eexists; done| right | inversion Htrans; naive_solver ]. *)
    { left. simpl. rewrite N. eauto. } 

    destruct STEP as (Hne&Hdec&Hni&Hincl&Heq&NGNE).
    right. rewrite -> Heq in *. split; last done.
    
    destruct (decide (dom $ ls_fuel δ = dom $ ls_fuel δ')) as [Hdomeq|Hdomneq].
    - destruct Hne as [ρ Hρtid].

      assert (ρ ∈ dom $ ls_fuel δ) as Hin by rewrite -ls_same_doms elem_of_dom //.
      pose proof Hin as Hin'. pose proof Hin as Hin''.
      apply elem_of_dom in Hin as [f Hf].
      rewrite Hdomeq in Hin'. apply elem_of_dom in Hin' as [f' Hf'].
      rewrite /Ψ -!size_dom Hdomeq.
      apply Nat.add_lt_mono_l.

      rewrite /Ψ (big_opM_delete (λ _ f, f) (ls_fuel δ') ρ) //.
      rewrite (big_opM_delete (λ _ f, f) (ls_fuel  δ) ρ) //.
      apply Nat.add_lt_le_mono.
      { rewrite /fuel_decr in Hdec. specialize (Hdec ρ). rewrite Hf Hf' /= in Hdec.
        apply Hdec; [set_solver | set_solver | by econstructor]. }
      apply big_addM_leq_forall => ρ' Hρ'.
      rewrite dom_delete_L in Hρ'.
      have Hρneqρ' : ρ ≠ ρ' by set_solver.
      rewrite !lookup_delete_ne //.
      destruct (decide (ρ' ∈ dom δ.(ls_fuel))) as [Hin|Hnotin]; last set_solver.
      rewrite /fuel_must_not_incr in Hni.
      destruct (Hni ρ' ltac:(done)); [done|set_solver].
    - assert (size $ ls_fuel δ' < size $ ls_fuel δ).
      { rewrite -!size_dom. apply subset_size. set_solver. }
      apply Nat.add_lt_le_mono =>//.
      apply big_addM_leq_forall => ρ' Hρ'.
      destruct (Hni ρ' ltac:(set_solver)); [done|set_solver].
  Qed.

  Lemma fuel_dec_unless_step δ r δ'
    (Htrans : ext_trans δ r δ'):
    (∃ ρ' : option (@ext_role _ EM), EUsls δ r δ' = Some ρ') ∨
    Ψ δ' < Ψ δ ∧ ls_under δ = ls_under δ'.
  Proof. 
    inversion Htrans.
    { subst. eapply fuel_dec_unless_lm_step in STEP; eauto.
      destruct STEP as [[? STEP]| ?]; [| tauto].
      left. eauto. }
    subst.
    left. eauto.
  Qed.

  Lemma fuel_dec_unless
    (* (auxtr: auxtrace (LM := LM)) *)
          (eauxtr: elmftrace)
    :
    mtrace_valid eauxtr ->
    dec_unless ls_under EUsls Ψ eauxtr.
  Proof.
    intros Hval n. revert eauxtr Hval. induction n; intros eauxtr Hval; last first.
    { edestruct (after (S n) eauxtr) as [eauxtrn|] eqn:Heq; rewrite Heq =>//.
      simpl in Heq. simplify_eq. destruct eauxtrn as [|δ ℓ eauxtr']=>//; last first.            
      destruct eauxtr; [done| ].
      apply trace_valid_cons_inv in Hval as [VAL _].
      specialize (IHn _ VAL). rewrite Heq // in IHn. 
    }
    rewrite after_0_id. destruct eauxtr; [done| ].
    apply trace_valid_cons_inv in Hval as [VAL ?]; simplify_eq =>//.
    eapply fuel_dec_unless_step; eauto. 
  Qed.

  Definition upto_stutter_eauxtr :=
    upto_stutter (ls_under (G:=G) (M:=M) (LSI := LSI)) EUsls.

  Lemma can_destutter_eauxtr (eauxtr: elmftrace):
    mtrace_valid eauxtr →
    ∃ mtr, upto_stutter_eauxtr eauxtr mtr.
  Proof.
    intros ?. eapply can_destutter.
    eapply fuel_dec_unless =>//.
  Qed.

End destuttering_auxtr.

Section upto_preserves.
  Context `{CNT: Countable G}. 
  Context `{LM: LiveModel G M LSI}.
  Context {EM: ExtModel M}.
  Context {LF: LMFairPre LM}.
  (* Let LMF := LM_Fair (LM := LM). *)
  Context {ELMF: ExtModel LM_Fair}.
  Context (proj_ext: (@EI _ ELMF) -> (@EI _ EM)). 

  Hypothesis PROJ_KEEP_EXT:
    forall δ1 ι δ2, (@ETs _ ELMF) ι δ1 δ2 -> 
                (@ETs _ EM) (proj_ext ι) (ls_under δ1) (ls_under δ2). 

  (* TODO: here and for similar lemmas:
     try to unify usual and external versions *)
  Lemma upto_preserves_validity (eauxtr : elmftrace (LM := LM)) mtr:
    upto_stutter_eauxtr proj_ext eauxtr mtr ->
    mtrace_valid eauxtr ->
    emtrace_valid mtr.
  Proof.
    revert eauxtr mtr. pcofix CH. intros eauxtr mtr Hupto Hval.
    punfold Hupto. 
    2: { apply upto_stutter_mono. } 
    induction Hupto as [| |btr str δ ????? IH].
    - pfold. constructor.
    - apply IHHupto. eapply trace_valid_cons_inv; eauto. 
    - pfold; constructor=>//.
      + subst.
        (* inversion Hval as [| A B C Htrans E F ] =>//. *)
        apply trace_valid_cons_inv in Hval as [VAL Htrans].  
        inversion Htrans.
        * subst. simpl in H0.
          destruct next_TS_role eqn:N; [| done]. inversion H0. subst.
          apply next_TS_spec_pos in N. 
          econstructor.
          pclearbot. apply upto_stutter_trfirst in IH.
          rewrite IH. apply N.
        * subst.
          simpl in H0. inversion H0. subst. 
          constructor.
          replace (trfirst str) with (ls_under (trfirst btr)).
          2: { (* TODO: a faster way? *)
               inversion IH; [| pclearbot; done].
               symmetry. eapply upto_stutter_trfirst; eauto. }           
          eapply PROJ_KEEP_EXT; eauto. 
      + right. eapply CH.        
        { destruct IH =>//. }
        eapply trace_valid_cons_inv; eauto.        
  Qed.

  Lemma ext_bounded_inner (eauxtr : elmftrace (LM := LM)) mtr:
    upto_stutter_eauxtr proj_ext eauxtr mtr ->
    ext_trans_bounded eauxtr ->
    ext_trans_bounded mtr. 
  Proof.
    intros UPTO BOUND.
    do 2 red in BOUND. destruct BOUND as [n BOUND].
    destruct (after n eauxtr) as [atr| ] eqn:AFTER.
    2: { apply fin_trans_bounded.
         eapply upto_stutter_terminating_trace; eauto.
         red. eauto. }
    pose proof AFTER as AFTER'. eapply upto_stutter_after' in AFTER'; eauto.
    destruct AFTER' as (n' & atr' & AFTER' & UPTO').
    red. exists n'. intros i ? LE ITH. intros [? ->].
    apply Nat.le_sum in LE as [d ->].
    erewrite <- label_lookup_after in ITH; eauto.
    apply trace_label_lookup_simpl' in ITH as (?&?&ITH). 
    eapply upto_stutter_trace_lookup' in ITH; eauto.
    destruct ITH as (p&?&oℓ&?&PTH&<-&<-&LBL).
    destruct oℓ as [[|] |]; [..| done]; simpl in LBL.
    { destruct next_TS_role; done. }
    destruct e. inversion LBL. subst. 
    eapply BOUND.
    2: { eapply trace_label_lookup_simpl'. do 2 eexists.
         erewrite <- trace_lookup_after; eauto. }
    { lia. }
    eauto.
  Qed. 

End upto_preserves.

Section upto_stutter_preserves_fairness_and_termination.
  (* Context `{LM: LiveModel G M LSI}. *)
  (* Context `{Countable G}. *)
  Context `{CNT: Countable G}. 
  Context `{LM: LiveModel G M LSI}.
  Context {EM: ExtModel M}.
  Context {LMFP: LMFairPre LM}.
  (* Let LMF := LM_Fair (LM := LM). *)
  Context {ELM: ExtModel LM_Fair}.
  Context (proj_ext: (@EI _ ELM) -> (@EI _ EM)). 

  (* Notation upto_stutter_aux := (upto_stutter (ls_under (LSI := LSI)) (Ul (LM := LM))). *)

  (* Lemma upto_stutter_step_correspondence (eauxtr: eauxtrace (LM := LM)) (emtr: emtrace (EM := EM)) *)
  (*   (Po: LiveState _ _ LSI -> option (mlabel ELM) -> Prop) *)
  (*   (Pi: M -> option (option (ext_role (EM := EM))) -> Prop) *)
  (*   (LIFT: forall δ oℓ, Po δ oℓ -> Pi (ls_under δ) (match oℓ with  *)
  (*                                             | Some ℓ => EUl proj_ext ℓ (LM := LM) *)
  (*                                             | None => None *)
  (*                                             end)) *)
  (*   (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ)) *)
  (*   : *)
  (*   upto_stutter_eauxtr proj_ext eauxtr emtr (LM := LM) -> *)
  (*   forall n atr_aux, *)
  (*     after n eauxtr = Some atr_aux -> *)
  (*     pred_at atr_aux 0 Po -> *)
  (*   exists m atr_m, *)
  (*     after m emtr = Some atr_m /\ pred_at atr_m 0 Pi /\  *)
  (*     upto_stutter_eauxtr proj_ext atr_aux atr_m. *)
  (* Proof. *)
  (*   intros Hupto n. generalize dependent eauxtr. generalize dependent emtr.  *)
  (*   induction n as [|n]; intros eauxtr emtr Hupto atr_aux AFTER A0. *)
  (*   - rewrite after_0_id in AFTER. assert (atr_aux = emtr) as -> by congruence. *)
  (*     do 2 eexists. split; [| split]; [..| by eauto]. *)
  (*     { by erewrite after_0_id. } *)
  (*     punfold Hupto. inversion Hupto; simplify_eq. *)
  (*     4: { apply upto_stutter_mono'. } *)
  (*     + rename A0 into Hpa. *)
  (*       rewrite /pred_at /=. rewrite /pred_at //= in Hpa. *)
  (*       by apply LIFT in Hpa.  *)
  (*     + rewrite -> !pred_at_0 in A0. *)
  (*       rewrite /pred_at /=. destruct eauxtr; simpl in *; try congruence. *)
  (*       * apply LIFT in A0. congruence. *)
  (*       * apply LIFT in A0. destruct ℓ; simpl in *; try done. *)
  (*         destruct l; [done| ..].            *)
  (*         all: subst; eapply PI0; eauto. *)
  (*     + rewrite -> !pred_at_0 in A0. *)
  (*       apply pred_at_0. rewrite <- H0. *)
  (*       by eapply LIFT in A0.  *)
  (*   - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq. *)
  (*     3: { apply upto_stutter_mono'. } *)
  (*     + simpl in AFTER.  *)
  (*       eapply IHn; eauto. *)
  (*       by pfold. *)
  (*     + simpl in AFTER. *)
  (*       assert (upto_stutter_eauxtr proj_ext btr str) as UPTO'. *)
  (*       { inversion IH; eauto. done. }  *)
  (*       specialize (IHn str btr UPTO' _ AFTER A0) as (m & ?&?&?). *)
  (*       exists (S m). eauto.  *)
  (* Qed. *)

  (* Lemma upto_stutter_step_correspondence (eauxtr: eauxtrace (LM := LM)) (emtr: emtrace (EM := EM)) *)
  (*   (Po: LiveState _ _ LSI -> option (mlabel ELM) -> Prop) *)
  (*   (Pi: M -> option (option (ext_role (EM := EM))) -> Prop) *)
  (*   (LIFT: forall δ oℓ, Po δ oℓ -> Pi (ls_under δ) (match oℓ with  *)
  (*                                             | Some ℓ => EUl proj_ext ℓ (LM := LM) *)
  (*                                             | None => None *)
  (*                                             end)) *)
  (*   (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ)) *)
  (*   : *)
  (*   upto_stutter_eauxtr proj_ext eauxtr emtr (LM := LM) -> *)
  (*   forall n atr_aux, *)
  (*     after n eauxtr = Some atr_aux -> *)
  (*     pred_at atr_aux 0 Po -> *)
  (*   exists m atr_m, *)
  (*     after m emtr = Some atr_m /\ pred_at atr_m 0 Pi /\  *)
  (*     upto_stutter_eauxtr proj_ext atr_aux atr_m. *)
  (* Proof. *)
  Lemma upto_stutter_step_correspondence (eauxtr: elmftrace (LM := LM)) (emtr: emtrace (EM := EM))
    (Po: lm_ls LM -> option (option (@ext_role _ ELM) * lm_ls LM) -> Prop)
    (Pi: M -> option (option (ext_role (EM := EM)) * M) -> Prop)
    (LIFT: forall δ ostep, Po δ ostep -> Pi (ls_under δ) (match ostep with 
                                              | Some (ℓ, δ') => match (EUsls proj_ext δ ℓ δ') with | Some r => Some (r, ls_under δ') | None => None end
                                              | None => None
                                              end))
    (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ))
    :
    upto_stutter_eauxtr proj_ext eauxtr emtr (LM := LM) ->
    forall n atr_aux so stepo,
      after n eauxtr = Some atr_aux ->
      (* pred_at atr_aux 0 Po -> *)
      atr_aux !! 0 = Some (so, stepo) ->
      Po so stepo ->
    exists m atr_m si stepi,
      after m emtr = Some atr_m /\ 
      (* pred_at atr_m 0 Pi /\  *)
      atr_m !! 0 = Some (si, stepi) /\
      Pi si stepi /\
      upto_stutter_eauxtr proj_ext atr_aux atr_m.
  Proof.
    intros Hupto n. generalize dependent eauxtr. generalize dependent emtr. 
    induction n as [|n]; intros auxtr mtr Hupto atr_aux os ostep AFTER O0 A0.
    - rewrite after_0_id in AFTER. assert (atr_aux = mtr) as -> by congruence.
      (* do 4 eexists. *)
      exists 0, auxtr.
      pose proof (trace_lookup_0 auxtr) as [stepi STEPI].
      exists (trfirst auxtr), stepi.
      do 3 (split; eauto). 
      punfold Hupto. inversion Hupto; simplify_eq.
      4: { apply upto_stutter_mono. }
      + rename A0 into Hpa.
        rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
        destruct ostep; [done| ].
        specialize (LIFT _ _ Hpa). simpl in LIFT.
        rewrite trace_lookup_0_singleton in O0. inversion O0. 
        rewrite trace_lookup_0_singleton in STEPI. inversion STEPI. 
        congruence. 
      +
        (* rewrite -> !pred_at_0 in A0. *)
        rewrite /pred_at /=.
        destruct auxtr; try congruence.
        * apply LIFT in A0. 
          simpl.
          rewrite trace_lookup_0_singleton in STEPI. inversion STEPI.
          subst.           
          rewrite trace_lookup_0_cons in O0. inversion O0. subst.
          rewrite H0 H in A0. congruence. 
        * apply LIFT in A0.
          simpl in H2. subst.
          rewrite trace_lookup_0_cons in O0.
          inversion O0. subst. simpl. 
          rewrite H0 H in A0.
          simpl in H1. subst. rewrite H0.  
          destruct stepi; eauto. 
      + 
        (* rewrite -> !pred_at_0 in A0. *)
        simpl. 
        (* apply pred_at_0. rewrite <- H1. *)
        eapply LIFT in A0.
        rewrite trace_lookup_0_cons in O0. inversion O0. subst.
        rewrite H0 in A0.
        simpl in STEPI.
        pose proof (trace_lookup_0_cons (ls_under os) ℓ' str).
        simpl in H. rewrite STEPI in H. inversion H. subst.
        red in H1. try pclearbot.
        apply upto_stutter_trfirst in H1. by rewrite H1.
    - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
      3: { apply upto_stutter_mono. } 
      + simpl in AFTER. 
        eapply IHn; eauto.
        by pfold.
      + simpl in AFTER.
        assert (upto_stutter_eauxtr proj_ext btr str) as UPTO'.
        { inversion IH; eauto. done. } 
        specialize (IHn str btr UPTO').
        specialize (IHn _ os ostep AFTER O0 A0). 
        destruct IHn as (m&?&?&?&?&?&?&?). 
        exists (S m). do 3 eexists. eauto. 
  Qed.

  Lemma upto_stutter_fairness_0 ρ eauxtr (mtr: emtrace (EM := EM)):
    upto_stutter_eauxtr proj_ext eauxtr mtr ->
    (∃ n s ostep, eauxtr !! n = Some (s, ostep ) /\ 
                  (¬role_enabled (LSI := LSI) ρ s ∨
                     (* pred_at eauxtr n (λ _ ℓ, ∃ ζ, ℓ = Some $ inl (Take_step ρ ζ)) *)
            (* step_by_next_TS ρ s ostep *)
                     ∃ (τ : G) (δ2 : lm_ls LM),
    ostep = Some (Some (inl τ), δ2) ∧ next_TS_role s τ δ2 = Some ρ
                  )
    ) ->
    ∃ m, pred_at mtr m (λ δ _, ¬role_enabled_model ρ δ)
         ∨ pred_at mtr m (λ _ ℓ, ℓ = Some $ Some $ inl ρ).
  Proof.
    (* repeat setoid_rewrite <- pred_at_or.  *)
    (* intros UPTO [n NTH]. *)
    (* pose proof NTH as [atr AFTER]%pred_at_after_is_Some.  *)
    (* rewrite (plus_n_O n) in NTH.  *)
    (* rewrite pred_at_sum AFTER in NTH.  *)
    (* eapply upto_stutter_step_correspondence in NTH; eauto.  *)
    (* - destruct NTH as (m & atr_m & AFTERm & Pm & UPTO'). *)
    (*   exists m. rewrite (plus_n_O m) pred_at_sum AFTERm. apply Pm.  *)
    (* - intros ?? Po. destruct Po as [?| [? ->]]; eauto. *)
    (* - intros. destruct H; [| done]. eauto. *)
    repeat setoid_rewrite <- pred_at_or. 
    intros UPTO (n & so & stepo & NTH & PROP).
    (* pose proof NTH as [atr AFTER]%pred_at_after_is_Some.  *)
    pose proof (proj2 (trace_lookup_after_weak eauxtr so n)) as (atr & AFTER & A0); [by eauto| ].
    rewrite (plus_n_O n) in NTH. 

    (* rewrite pred_at_sum AFTER in NTH. *)
    erewrite <- @trace_lookup_after in NTH; eauto.  
    (* apply pred_at_trace_lookup' in NTH as (so & stepo & A0 & PROP). *)
    pattern so, stepo in PROP. 
    
    eapply upto_stutter_step_correspondence in PROP; eauto. 
    - destruct PROP as (m & atr_m & si & stepi & AFTERm & B0 & Pi & UPTO').
      exists m. rewrite (plus_n_O m). repeat rewrite pred_at_sum AFTERm.
      apply pred_at_or. 
      eapply pred_at_trace_lookup'.
      do 2 eexists. split; [eauto| ].
      pattern si. pattern stepi. apply Pi. 
    - intros ?? Po. simpl. destruct Po as [?| ?]; eauto.
      right. destruct H as [? H].
      destruct ostep.
      2: { by destruct H as (?&?&?). }
      simpl in *. destruct H as (?&[=]&[=]). subst.
      simpl. rewrite H2. done. 
    - intros. destruct H; eauto. done. 
  Qed.

  Definition fair_by_next_TS_ext: fmrole M -> elmftrace (LM := LM) -> Prop :=
    fair_by_gen role_enabled 
      (fun ρ s ostep => ∃ (τ : G) (δ2 : lm_ls LM),
           ostep = Some (Some (inl τ), δ2) ∧ next_TS_role s τ δ2 = Some ρ).

  Lemma upto_stutter_fairness (eauxtr: elmftrace (LM := LM)) (emtr: emtrace (EM := EM)):
    upto_stutter_eauxtr proj_ext eauxtr emtr ->
    (* (∀ ρ, fair_eaux ρ eauxtr) -> *)
    (forall ρ, fair_by_next_TS_ext ρ eauxtr) ->
    (* (∀ ρ, fair_model_trace ρ emtr). *)
    inner_fair_ext_model_trace emtr. 
  Proof.
    intros Hupto Hfa.
    do 2 red. intros ? [ρ ->].
    do 2 red. intros n Hpmod.
    unfold pred_at in Hpmod.
    destruct (after n emtr) as [emtr'|] eqn:Heq
    (* ; last done. *)
    .
    2: { by rewrite Heq in Hpmod. }
    rewrite Heq in Hpmod.
    (* Set Printing Implicit. *)
    assert (role_enabled_model (inl ρ) (trfirst emtr') (M := (@ext_model_FM _ EM))).
    { by destruct emtr'. }
    clear Hpmod. rename H into Hpmod. 

    destruct (upto_stutter_after _ _ n Hupto Heq) as (n'&auxtr'&Heq'&Hupto').
    have Hre: role_enabled_model ρ (trfirst emtr')
      (* by destruct emtr'. *)
    .
    { red. red in Hpmod. simpl in Hpmod. set_solver. }
    specialize (Hfa ρ).
    have Henaux : role_enabled ρ (trfirst auxtr').
    { have HUs: ls_under (trfirst auxtr') = trfirst emtr'.
      - punfold Hupto'; [| by apply upto_stutter_mono]. 
        by inversion Hupto'.
      - unfold role_enabled, role_enabled_model in *.
        rewrite HUs //. }
    (* have Hfa' := (fair_by_gen_after ρ eauxtr n' auxtr' Hfa Heq' 0). *)
    assert (fair_by_next_TS_ext ρ auxtr') as Hfa'.
    { eapply fair_by_gen_after; eauto. }
    have Hpredat: pred_at auxtr' 0 (λ δ _, role_enabled ρ δ).
    { rewrite /pred_at /=. destruct auxtr'; done. }
    (* destruct (upto_stutter_fairness_0 ρ auxtr' emtr' Hupto' (Hfa' Hpredat)) as (m&Hres). *)
    destruct (upto_stutter_fairness_0 ρ auxtr' emtr' Hupto') as(m&Hres).
    { apply pred_at_trace_lookup in Hpredat as EN.
      do 2 red in Hfa. specialize (Hfa n').
      destruct Hfa.
      { apply pred_at_trace_lookup.
        exists (trfirst auxtr'). split; auto.
        erewrite (plus_n_O n'), <- state_lookup_after; eauto.
        by rewrite state_lookup_0. }
      destruct H as (?&?&NNTH&FS).
      erewrite <- trace_lookup_after in NNTH; eauto. }
    
    exists m. rewrite !(pred_at_sum _ n) Heq //.
    rewrite /fairness_sat. 
    rewrite pred_at_or in Hres.
    eapply pred_at_iff; [| apply Hres].
    intros. simpl. apply Morphisms_Prop.or_iff_morphism.
    - apply not_iff_compat. rewrite {1}/role_enabled_model. simpl. set_solver.
    - split; [intros (?&->&[=->])| intros ->]; subst; eauto.
      exists (Some (inl ρ)). split; done. 
  Qed.

  Lemma upto_stutter_finiteness eauxtr (emtr: emtrace (EM := EM)):
    upto_stutter_eauxtr proj_ext eauxtr emtr ->
    terminating_trace emtr ->
    terminating_trace eauxtr.
  Proof.
    intros Hupto [n Hfin].
    have [n' ?] := upto_stutter_after_None _ _ n Hupto Hfin.
    eexists; done.
  Qed.

End upto_stutter_preserves_fairness_and_termination.

(* TODO: move, unify with non-ext version? *)
From trillium.fairness Require Import lm_fairness_preservation.
Lemma ELM_ALM_afair_by_next `{Countable G}`(LM: LiveModel G M LSI) {LF: LMFairPre LM}
  {ELM: ExtModel (@LM_Fair _ _ _ _ _ _ LF)} auxtr
  (KEEPS: ext_keeps_asg):
  (∀ ρ, afair_by_next_TS (ELM_ALM KEEPS) ρ auxtr) <-> ∀ ρ, fair_by_next_TS_ext ρ auxtr.
Proof.
  apply forall_proper. intros.
  apply fair_by_gen_Proper; try reflexivity.
  red. intros ??->. intros ??->. intros ??->.
  rewrite /step_by_next_TS /astep_by_next_TS. simpl.
  split.
  - intros (?&?&?&->&<-&<-). eauto.
  - intros (?&?&->&?). do 3 eexists. eauto. 
Qed. 
