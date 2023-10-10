From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness trace_utils.
From trillium.fairness Require Export fuel lm_fair. 
From trillium.fairness.ext_models Require Export ext_models.
(* ext_lm_fair.  *)

Section ExtLM.
  (** The differences with Ext(LM_Fair) are:
      - this is not a FairModel, so there is no notion of "roles" and enabledness
      - following from previous, (inl) transitions are made with FairLabel
      This additional construction is needed because the destuttering proof
      would be hard to conduct using LM_Fair-like traces *)

  Context `{LM: LiveModel G M LSI}.
  Context `{EM: ExtModel M}.

  Context `{Countable G} `{EqDecision M}.
  Context `{∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2)}.
  Context `{Inhabited (lm_ls LM)} `{Inhabited G}.
  Let LMF := LM_Fair (LM := LM). 
  Context `{ELMF: ExtModel LMF}.

  Definition elm_role := (lm_lbl LM + (@EI _ ELMF))%type. 

  (* TODO: change name? *)
  Inductive elm_trans: lm_ls LM -> elm_role -> lm_ls LM -> Prop :=
  | elm_lm_step s1 ℓ s2 (STEP: lm_ls_trans LM s1 ℓ s2):
    elm_trans s1 (inl ℓ) s2
  | elm_ext_step s1 s2 ι (REL: ETs ι s1 s2):
    elm_trans s1 (inr ι) s2.   

End ExtLM.


Section fuel_dec_unless.
  Context `{LM: LiveModel G Mdl LSI}.
  Context `{Countable G}.
  
  Lemma fuel_must_not_incr_fuels oρ'
    (δ1 δ2: LiveState G Mdl LSI)
    ρ f1 f2
    (KEEP: fuel_must_not_incr oρ' δ1 δ2)
    (FUEL1: ls_fuel δ1 !! ρ = Some f1)
    (FUEL2: ls_fuel δ2 !! ρ = Some f2)
    (OTHER: oρ' ≠ Some ρ):
    f2 <= f1.
  Proof.
    red in KEEP. specialize (KEEP ρ ltac:(by apply elem_of_dom)).
    destruct KEEP as [LE|[?|KEEP]].
    + rewrite FUEL1 FUEL2 in LE. simpl in LE. lia. 
    + tauto. 
    + apply proj1 in KEEP. destruct KEEP. eapply elem_of_dom; eauto.
  Qed.

  Lemma step_nonincr_fuels ℓ
    (δ1 δ2: LiveState G Mdl LSI)
    ρ f1 f2
    (STEP: lm_ls_trans LM δ1 ℓ δ2)
    (FUEL1: ls_fuel δ1 !! ρ = Some f1)
    (FUEL2: ls_fuel δ2 !! ρ = Some f2)
    (OTHER: forall g, ℓ ≠ Take_step ρ g):
    f2 <= f1.
  Proof.
    destruct ℓ. 
    all: eapply fuel_must_not_incr_fuels; eauto; [apply STEP|..]; congruence.
  Qed. 


  Definition Ul (ℓ: LM.(mlabel)) :=
    match ℓ with
    | Take_step ρ _ => Some (Some ρ)
    | _ => None
    end.

  Definition Ψ (δ: LiveState G Mdl LSI) :=
    size δ.(ls_fuel) + [^ Nat.add map] ρ ↦ f ∈ δ.(ls_fuel (G := G)), f.

  Lemma fuel_dec_unless0 δ ℓ (auxtr' : trace (lm_ls LM) (lm_lbl LM))
    (Hval : auxtrace_valid (δ -[ ℓ ]-> auxtr')):
  (∃ ℓ' : option (fmrole Mdl), Ul ℓ = Some ℓ')
  ∨ Ψ (trfirst auxtr') < Ψ δ ∧ ls_under δ = ls_under $ trfirst auxtr'.
  Proof.
    inversion Hval as [|??? Htrans Hmatch]; simplify_eq =>//.
    destruct ℓ as [| tid' |];
      [left; eexists; done| right | inversion Htrans; naive_solver ].
    destruct Htrans as (Hne&Hdec&Hni&Hincl&Heq).
    rewrite -> Heq in *. split; last done.

    destruct (decide (dom $ ls_fuel δ = dom $ ls_fuel (trfirst auxtr'))) as [Hdomeq|Hdomneq].
    - destruct Hne as [ρ Hρtid].

      assert (ρ ∈ dom $ ls_fuel δ) as Hin by rewrite -ls_same_doms elem_of_dom //.
      pose proof Hin as Hin'. pose proof Hin as Hin''.
      apply elem_of_dom in Hin as [f Hf].
      rewrite Hdomeq in Hin'. apply elem_of_dom in Hin' as [f' Hf'].
      rewrite /Ψ -!size_dom Hdomeq.
      apply Nat.add_lt_mono_l.

      rewrite /Ψ (big_opM_delete (λ _ f, f) (ls_fuel (trfirst _)) ρ) //.
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
      (* destruct (Hni ρ' ltac:(done) ltac:(done)); [done|set_solver]. *)
      destruct (Hni ρ' ltac:(done)); [done|set_solver].
    - assert (size $ ls_fuel (trfirst auxtr') < size $ ls_fuel δ).
      { rewrite -!size_dom. apply subset_size. set_solver. }
      apply Nat.add_lt_le_mono =>//.
      apply big_addM_leq_forall => ρ' Hρ'.
      (* destruct (Hni ρ' ltac:(set_solver) ltac:(done)); [done|set_solver]. *)
      destruct (Hni ρ' ltac:(set_solver)); [done|set_solver].
  Qed. 

  Lemma fuel_dec_unless (auxtr: auxtrace (LM := LM)) :
    auxtrace_valid auxtr ->
    dec_unless ls_under Ul Ψ auxtr.
  Proof.
    intros Hval n. revert auxtr Hval. induction n; intros auxtr Hval; last first.
    { edestruct (after (S n) auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
      simpl in Heq. simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.
      inversion Hval as [|???? Hmatch]; simplify_eq =>//.
      specialize (IHn _ Hmatch). rewrite Heq // in IHn. }
    rewrite after_0_id. destruct auxtr; [done| ].
    by apply fuel_dec_unless0. 
  Qed.

End fuel_dec_unless.

Section destuttering_auxtr.
  Context `{LM: LiveModel G M LSI}.

  Context `{Countable G}.

  (* Why is [LM] needed here? *)
  Definition upto_stutter_auxtr :=
    upto_stutter (ls_under (G:=G) (M:=M) (LSI := LSI)) (Ul (LM := LM)).

  Lemma can_destutter_auxtr auxtr:
    auxtrace_valid auxtr →
    ∃ mtr, upto_stutter_auxtr auxtr mtr.
  Proof.
    intros ?. eapply can_destutter.
    eapply fuel_dec_unless =>//.
  Qed.

End destuttering_auxtr.

Section upto_preserves.
  Context `{LM: LiveModel G M LSI}.
  Context `{Countable G}.

  Lemma upto_stutter_mono' :
    monotone2 (upto_stutter_ind (ls_under (LSI := LSI)) (Ul (LM:=LM))).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_preserves_validity (auxtr : auxtrace (LM := LM)) mtr:
    upto_stutter_auxtr auxtr mtr ->
    auxtrace_valid auxtr ->
    mtrace_valid mtr.
  Proof.
    revert auxtr mtr. pcofix CH. intros auxtr mtr Hupto Hval.
    punfold Hupto.
    induction Hupto as [| |btr str δ ????? IH].
    - pfold. constructor.
    - apply IHHupto. inversion Hval. assumption.
    - pfold; constructor=>//.
      + subst. inversion Hval as [| A B C Htrans E F ] =>//. subst. unfold ls_trans in *.
        destruct ℓ; try done. simpl in *. simplify_eq.
        destruct Htrans as [??].
        have <- //: ls_under $ trfirst btr = trfirst str.
        { destruct IH as [IH|]; last done. punfold IH. inversion IH =>//. }
      + right. eapply CH.
        { destruct IH =>//. }
        subst. by inversion Hval.
  Qed.

End upto_preserves.

Section upto_stutter_preserves_fairness_and_termination.
  Context `{LM: LiveModel G M LSI}.
  Context `{Countable G}.

  Notation upto_stutter_aux := (upto_stutter (ls_under (LSI := LSI)) (Ul (LM := LM))).

  Lemma upto_stutter_mono'' : (* TODO fix this proliferation *)
    monotone2 (upto_stutter_ind (ls_under (LSI := LSI)) (Ul (LM:=LM))).
  Proof.
    unfold monotone2. intros x0 x1 r r' IN LE.
    induction IN; try (econstructor; eauto; done).
  Qed.
  Hint Resolve upto_stutter_mono' : paco.

  Lemma upto_stutter_step_correspondence auxtr (mtr: mtrace M)
    (Po: LiveState _ _ LSI -> option (mlabel LM) -> Prop)
    (Pi: M -> option (option (fmrole M)) -> Prop)
    (LIFT: forall δ oℓ, Po δ oℓ -> Pi (ls_under δ) (match oℓ with 
                                              | Some ℓ => Ul ℓ (LM := LM)
                                              | None => None
                                              end))
    (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ))
    :
    upto_stutter_auxtr auxtr mtr (LM := LM) ->
    forall n atr_aux,
      after n auxtr = Some atr_aux ->
      pred_at atr_aux 0 Po ->
    exists m atr_m,
      after m mtr = Some atr_m /\ pred_at atr_m 0 Pi /\ 
      upto_stutter_auxtr atr_aux atr_m.
  Proof.
    intros Hupto n. generalize dependent auxtr. generalize dependent mtr. 
    induction n as [|n]; intros auxtr mtr Hupto atr_aux AFTER A0.
    - rewrite after_0_id in AFTER. assert (atr_aux = mtr) as -> by congruence.
      do 2 eexists. split; [| split]; [..| by eauto].
      { by erewrite after_0_id. }
      punfold Hupto. inversion Hupto; simplify_eq.
      + rename A0 into Hpa.
        rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
        by apply LIFT in Hpa. 
      + rewrite -> !pred_at_0 in A0.
        rewrite /pred_at /=. destruct auxtr; simpl in *; try congruence.
        * apply LIFT in A0. congruence.
        * apply LIFT in A0. destruct ℓ; simpl in *; try done.
          all: subst; eapply PI0; eauto.
      + rewrite -> !pred_at_0 in A0.
        apply pred_at_0. rewrite <- H1.
        by eapply LIFT in A0. 
    - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
      + simpl in AFTER. 
        eapply IHn; eauto.
        by pfold.
      + simpl in AFTER.
        assert (upto_stutter_auxtr btr str) as UPTO'.
        { inversion IH; eauto. done. } 
        specialize (IHn str btr UPTO' _ AFTER A0) as (m & ?&?&?).
        exists (S m). eauto. 
  Qed.

  (* Lemma upto_stutter_fairness_0 ρ auxtr (mtr: mtrace M): *)
  (*   upto_stutter_aux auxtr mtr -> *)
  (*   (* role_enabled_model ρ (trfirst mtr) -> *) *)
  (*   (∃ n, pred_at auxtr n (λ δ _, ¬role_enabled (G := G) ρ δ) *)
  (*         ∨ pred_at auxtr n (λ _ ℓ, ∃ ζ, ℓ = Some (Take_step ρ ζ))) -> *)
  (*   ∃ m, pred_at mtr m (λ δ _, ¬role_enabled_model ρ δ) *)
  (*        ∨ pred_at mtr m (λ _ ℓ, ℓ = Some $ Some ρ). *)
  (*   Proof. *)
  (*     intros Hupto (* Hre *) [n Hstep]. *)
  (*     revert auxtr mtr Hupto (* Hre *) Hstep. *)
  (*     induction n as [|n]; intros auxtr mtr Hupto (* Hre *) Hstep. *)
  (*     - punfold Hupto. inversion Hupto; simplify_eq. *)
  (*       + destruct Hstep as [Hpa|[??]]; try done. *)
  (*         exists 0. left. rewrite /pred_at /=. rewrite /pred_at //= in Hpa. *)
  (*       + rewrite -> !pred_at_0 in Hstep. exists 0. *)
  (*         destruct Hstep as [Hstep| [tid Hstep]]; [left|right]. *)
  (*         * rewrite /pred_at /=. destruct mtr; simpl in *; try congruence. *)
  (*         * exfalso. injection Hstep => Heq. rewrite -> Heq in *. *)
  (*           unfold Ul in *. congruence. *)
  (*       + rewrite -> !pred_at_0 in Hstep. exists 0. *)
  (*         destruct Hstep as [Hstep| [tid Hstep]]; [left|right]. *)
  (*         * rewrite /pred_at //=. *)
  (*         * rewrite /pred_at //=. injection Hstep. intros Heq. simplify_eq. *)
  (*           unfold Ul in *. congruence. *)
  (*     - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq. *)
  (*       + destruct Hstep as [?|?]; done. *)
  (*       + rewrite -> !pred_at_S in Hstep. *)
  (*         eapply IHn; eauto. *)
  (*         by pfold. *)
  (*       + destruct (decide (ℓ' = Some ρ)). *)
  (*         * simplify_eq. *)
  (*           exists 0. right. rewrite pred_at_0 //. *)
  (*         * have Hw: ∀ (P: nat -> Prop), (∃ n, P (S n)) -> (∃ n, P n). *)
  (*           { intros P [x ?]. by exists (S x). } *)
  (*           apply Hw. setoid_rewrite pred_at_S. *)
  (*           eapply IHn; eauto. *)
  (*           { destruct IH as [|]; done. } *)
  (*   Qed. *)


  Lemma upto_stutter_fairness_0 ρ auxtr (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    (∃ n, pred_at auxtr n (λ δ _, ¬role_enabled (LSI := LSI) ρ δ)
          ∨ pred_at auxtr n (λ _ ℓ, ∃ ζ, ℓ = Some (Take_step ρ ζ))) ->
    ∃ m, pred_at mtr m (λ δ _, ¬role_enabled_model ρ δ)
         ∨ pred_at mtr m (λ _ ℓ, ℓ = Some $ Some ρ).
  Proof.
    repeat setoid_rewrite <- pred_at_or. 
    intros UPTO [n NTH].
    pose proof NTH as [atr AFTER]%pred_at_after_is_Some. 
    rewrite (plus_n_O n) in NTH. 
    rewrite pred_at_sum AFTER in NTH. 
    eapply upto_stutter_step_correspondence in NTH; eauto. 
    - destruct NTH as (m & atr_m & AFTERm & Pm & UPTO').
      exists m. rewrite (plus_n_O m) pred_at_sum AFTERm. apply Pm. 
    - intros ?? Po. destruct Po as [?| [? ->]]; eauto.
    - intros. destruct H0; [| done]. eauto.
  Qed.  
    
  Lemma upto_stutter_fairness (auxtr:auxtrace (LM := LM)) (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    (∀ ρ, fair_aux ρ auxtr) ->
    (∀ ρ, fair_model_trace ρ mtr).
  Proof.
    intros Hupto Hfa ρ n Hpmod.
    unfold pred_at in Hpmod.
    destruct (after n mtr) as [mtr'|] eqn:Heq; last done.
    destruct (upto_stutter_after _ _ n Hupto Heq) as (n'&auxtr'&Heq'&Hupto').
    have Hre: role_enabled_model ρ (trfirst mtr') by destruct mtr'.
    specialize (Hfa ρ).
    have Henaux : role_enabled ρ (trfirst auxtr').
    { have HUs: ls_under (trfirst auxtr') = trfirst mtr'.
      - punfold Hupto'. by inversion Hupto'.
      - unfold role_enabled, role_enabled_model in *.
        rewrite HUs //. }
    have Hfa' := (fair_aux_after ρ auxtr n' auxtr' Hfa Heq' 0).
    have Hpredat: pred_at auxtr' 0 (λ δ _, role_enabled ρ δ).
    { rewrite /pred_at /=. destruct auxtr'; done. }
    destruct (upto_stutter_fairness_0 ρ auxtr' mtr' Hupto' (Hfa' Hpredat)) as (m&Hres).
    exists m. rewrite !(pred_at_sum _ n) Heq //.
  Qed.

  Lemma upto_stutter_finiteness auxtr (mtr: mtrace M):
    upto_stutter_aux auxtr mtr ->
    terminating_trace mtr ->
    terminating_trace auxtr.
  Proof.
    intros Hupto [n Hfin].
    have [n' ?] := upto_stutter_after_None _ _ n Hupto Hfin.
    eexists; done.
  Qed.

End upto_stutter_preserves_fairness_and_termination.
