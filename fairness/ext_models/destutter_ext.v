From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness trace_utils.
From trillium.fairness Require Export fuel lm_fair. 
From trillium.fairness.ext_models Require Export ext_models.
(* ext_lm_fair.  *)


(* TODO: move to lm_fair, reorganize?, reduce the scope? *)
Class LMFairPre `{LM: LiveModel G M LSI} := {
  edG :> EqDecision G;
  cntG :> Countable G;
  edM :> EqDecision (fmstate M);
  dTr :> ∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2);
  inhLM :> Inhabited (lm_ls LM);
  inhG :> Inhabited G;
}. 


Section ExtLM.
  (** The differences with Ext(LM_Fair) are:
      - this is not a FairModel, so there is no notion of "roles" and enabledness
      - following from previous, (inl) transitions are made with FairLabel
      This additional construction is needed because the destuttering proof
      would be hard to conduct using LM_Fair-like traces *)

  Context `{LM: LiveModel G M LSI}.
  Context {LMFP: LMFairPre (LM := LM)}.
  Let LMF := LM_Fair (LM := LM).
  
  Context {ELMF: ExtModel LMF}.

  Definition elm_lbl := (lm_lbl LM + (@EI _ ELMF))%type. 

  (* TODO: change name? *)
  Inductive elm_trans: lm_ls LM -> elm_lbl -> lm_ls LM -> Prop :=
  | elm_lm_step s1 ℓ s2 (STEP: lm_ls_trans LM s1 ℓ s2):
    elm_trans s1 (inl ℓ) s2
  | elm_ext_step s1 s2 ι (REL: ETs ι s1 s2):
    elm_trans s1 (inr ι) s2.   

  Definition ELM : Model := {|
    mstate := lm_ls LM;
    mlabel := elm_lbl;
    mtrans := elm_trans
  |}.  

  Definition eauxtrace := trace (mstate ELM) (mlabel ELM). 

  CoInductive eauxtrace_valid: eauxtrace -> Prop :=
  | eauxtrace_valid_singleton δ: eauxtrace_valid ⟨δ⟩
  | eauxtrace_valid_cons δ ℓ tr:
      elm_trans δ ℓ (trfirst tr) ->
      eauxtrace_valid tr →
      eauxtrace_valid (δ -[ℓ]-> tr).

  (* TODO: unify fairness definitions by parametrizing fair_by
     with predicate on "expected step"; use it in fair_aux and fair_eaux  *)
  Definition fair_eaux ρ (eauxtr: eauxtrace): Prop :=
    forall n, pred_at eauxtr n (λ δ _, role_enabled ρ δ) ->
         ∃ m, pred_at eauxtr (n+m) (λ δ _, ¬role_enabled ρ δ) ∨
              pred_at eauxtr (n+m) (λ _ ℓ, ∃ tid, ℓ = Some $ inl (Take_step ρ tid)).

  (* TODO: remove after refactoring of fair_eaux*)
  Lemma fair_eaux_after ρ eauxtr n eauxtr':
    fair_eaux ρ eauxtr ->
    after n eauxtr = Some eauxtr' ->
    fair_eaux ρ eauxtr'.
  Proof.
    rewrite /fair_aux => Hfair Hafter m Hpa.
    specialize (Hfair (n+m)).
    rewrite -> (pred_at_sum _ n) in Hfair. rewrite Hafter in Hfair.
    destruct (Hfair Hpa) as (p&Hp).
    exists (p). by rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n), Hafter in Hp.
  Qed.

End ExtLM.


Section destuttering_auxtr.
  Context `{LM: LiveModel G M LSI}.
  Context {EM: ExtModel M}.
  (* Let EMF := ext_model_FM (EM := EM).  *)
  Context {LMFP: LMFairPre (LM := LM)}.
  Let LMF := LM_Fair (LM := LM).
  Context {ELMF: ExtModel LMF}.

  Context (proj_ext: (@EI _ ELMF) -> (@EI _ EM)). 
  
  Lemma fuel_must_not_incr_fuels oρ'
    (δ1 δ2: LiveState G M LSI)
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
    (δ1 δ2: LiveState G M LSI)
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


  Definition EUl (ℓ: ELM.(mlabel)): option (option (@ext_role _ EM)) :=
    match ℓ with
    | inl (Take_step ρ _) => Some (Some (inl ρ))
    | inr e => Some $ Some $ inr $ env $ proj_ext $ e
    | _ => None
    end.

  Definition Ψ (δ: LiveState G M LSI) :=
    size δ.(ls_fuel) + [^ Nat.add map] ρ ↦ f ∈ δ.(ls_fuel (G := G)), f.

  Lemma fuel_dec_unless_lm_step δ ℓ δ'
    (Htrans : lm_ls_trans LM δ ℓ δ'):
    (∃ ℓ' : fmrole M, EUl (inl ℓ) = Some $ Some $ inl ℓ') ∨
    Ψ δ' < Ψ δ ∧ ls_under δ = ls_under δ'.
  Proof. 
    destruct ℓ as [| tid' |];
      [left; eexists; done| right | inversion Htrans; naive_solver ].

    destruct Htrans as (Hne&Hdec&Hni&Hincl&Heq).
    rewrite -> Heq in *. split; last done.
    
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

  Lemma fuel_dec_unless_step δ ℓ δ'
    (Htrans : elm_trans δ ℓ δ'):
    (∃ ℓ' : option (@ext_role _ EM), EUl ℓ = Some ℓ') ∨
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
          (eauxtr: eauxtrace (LM := LM))
    :
    eauxtrace_valid eauxtr ->
    dec_unless ls_under EUl Ψ eauxtr.
  Proof.
    intros Hval n. revert eauxtr Hval. induction n; intros eauxtr Hval; last first.
    { edestruct (after (S n) eauxtr) as [eauxtrn|] eqn:Heq; rewrite Heq =>//.
      simpl in Heq. simplify_eq. destruct eauxtrn as [|δ ℓ eauxtr']=>//; last first.
      inversion Hval as [|???? Hmatch]; simplify_eq =>//.
      specialize (IHn _ Hmatch). rewrite Heq // in IHn. }
    rewrite after_0_id. destruct eauxtr; [done| ].
    inversion Hval as [|??? Htrans Hmatch]; simplify_eq =>//.
    eapply fuel_dec_unless_step; eauto. 
  Qed.

  Definition upto_stutter_eauxtr :=
    upto_stutter (ls_under (G:=G) (M:=M) (LSI := LSI)) EUl.

  Lemma can_destutter_eauxtr eauxtr:
    eauxtrace_valid eauxtr →
    ∃ mtr, upto_stutter_eauxtr eauxtr mtr.
  Proof.
    intros ?. eapply can_destutter.
    eapply fuel_dec_unless =>//.
  Qed.

End destuttering_auxtr.

(* TODO: move *)
Lemma upto_stutter_mono' {S S' L L': Type} (Us: S -> S') (Ul: L -> option L'):
  monotone2 (upto_stutter_ind Us Ul).
Proof.
  unfold monotone2. intros x0 x1 r r' IN LE.
  induction IN; try (econstructor; eauto; done).
Qed.

Section upto_preserves.
  (* Context `{LM: LiveModel G M LSI}. *)
  (* Context `{Countable G}. *)
  Context `{LM: LiveModel G M LSI}.
  Context {EM: ExtModel M}.
  Context {LMFP: LMFairPre (LM := LM)}.
  Let LMF := LM_Fair (LM := LM).
  Context {ELMF: ExtModel LMF}.
  Context (proj_ext: (@EI _ ELMF) -> (@EI _ EM)). 

  Hypothesis PROJ_KEEP_EXT:
    forall δ1 ι δ2, (@ETs _ ELMF) ι δ1 δ2 -> 
                (@ETs _ EM) (proj_ext ι) (ls_under δ1) (ls_under δ2). 

  Local Hint Resolve upto_stutter_mono' : paco.

  (* TODO: here and for similar lemmas:
     try to unify usual and external versions *)
  Lemma upto_preserves_validity (eauxtr : eauxtrace (LM := LM)) mtr:
    upto_stutter_eauxtr proj_ext eauxtr mtr ->
    eauxtrace_valid eauxtr ->
    emtrace_valid mtr.
  Proof.
    revert eauxtr mtr. pcofix CH. intros eauxtr mtr Hupto Hval.
    punfold Hupto.
    induction Hupto as [| |btr str δ ????? IH].
    - pfold. constructor.
    - apply IHHupto. inversion Hval. assumption.
    - pfold; constructor=>//.
      + subst. inversion Hval as [| A B C Htrans E F ] =>//. subst.

        inversion Htrans.
        * subst.  
          unfold lm_ls_trans, ls_trans in *.
          destruct ℓ0; try done. simpl in *. simplify_eq.
          destruct STEP as [??].
          have <- //: ls_under $ trfirst btr = trfirst str.
          { destruct IH as [IH|]; last done. punfold IH. inversion IH =>//. }
          by constructor. 
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
        subst. by inversion Hval.
  Qed.

End upto_preserves.

Section upto_stutter_preserves_fairness_and_termination.
  (* Context `{LM: LiveModel G M LSI}. *)
  (* Context `{Countable G}. *)
  Context `{LM: LiveModel G M LSI}.
  Context {EM: ExtModel M}.
  Context {LMFP: LMFairPre (LM := LM)}.
  Let LMF := LM_Fair (LM := LM).
  Context {ELMF: ExtModel LMF}.
  Context (proj_ext: (@EI _ ELMF) -> (@EI _ EM)). 

  (* Notation upto_stutter_aux := (upto_stutter (ls_under (LSI := LSI)) (Ul (LM := LM))). *)

  Lemma upto_stutter_step_correspondence (eauxtr: eauxtrace (LM := LM)) (emtr: emtrace (EM := EM))
    (Po: LiveState _ _ LSI -> option (mlabel ELM) -> Prop)
    (Pi: M -> option (option (ext_role (EM := EM))) -> Prop)
    (LIFT: forall δ oℓ, Po δ oℓ -> Pi (ls_under δ) (match oℓ with 
                                              | Some ℓ => EUl proj_ext ℓ (LM := LM)
                                              | None => None
                                              end))
    (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ))
    :
    upto_stutter_eauxtr proj_ext eauxtr emtr (LM := LM) ->
    forall n atr_aux,
      after n eauxtr = Some atr_aux ->
      pred_at atr_aux 0 Po ->
    exists m atr_m,
      after m emtr = Some atr_m /\ pred_at atr_m 0 Pi /\ 
      upto_stutter_eauxtr proj_ext atr_aux atr_m.
  Proof.
    intros Hupto n. generalize dependent eauxtr. generalize dependent emtr. 
    induction n as [|n]; intros eauxtr emtr Hupto atr_aux AFTER A0.
    - rewrite after_0_id in AFTER. assert (atr_aux = emtr) as -> by congruence.
      do 2 eexists. split; [| split]; [..| by eauto].
      { by erewrite after_0_id. }
      punfold Hupto. inversion Hupto; simplify_eq.
      4: { apply upto_stutter_mono'. }
      + rename A0 into Hpa.
        rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
        by apply LIFT in Hpa. 
      + rewrite -> !pred_at_0 in A0.
        rewrite /pred_at /=. destruct eauxtr; simpl in *; try congruence.
        * apply LIFT in A0. congruence.
        * apply LIFT in A0. destruct ℓ; simpl in *; try done.
          destruct l; [done| ..].           
          all: subst; eapply PI0; eauto.
      + rewrite -> !pred_at_0 in A0.
        apply pred_at_0. rewrite <- H0.
        by eapply LIFT in A0. 
    - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
      3: { apply upto_stutter_mono'. }
      + simpl in AFTER. 
        eapply IHn; eauto.
        by pfold.
      + simpl in AFTER.
        assert (upto_stutter_eauxtr proj_ext btr str) as UPTO'.
        { inversion IH; eauto. done. } 
        specialize (IHn str btr UPTO' _ AFTER A0) as (m & ?&?&?).
        exists (S m). eauto. 
  Qed.

  Lemma upto_stutter_fairness_0 ρ eauxtr (mtr: emtrace (EM := EM)):
    upto_stutter_eauxtr proj_ext eauxtr mtr ->
    (∃ n, pred_at eauxtr n (λ δ _, ¬role_enabled (LSI := LSI) ρ δ)
          ∨ pred_at eauxtr n (λ _ ℓ, ∃ ζ, ℓ = Some $ inl (Take_step ρ ζ))) ->
    ∃ m, pred_at mtr m (λ δ _, ¬role_enabled_model ρ δ)
         ∨ pred_at mtr m (λ _ ℓ, ℓ = Some $ Some $ inl ρ).
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
    - intros. destruct H; [| done]. eauto.
  Qed.

  Lemma upto_stutter_fairness (eauxtr: eauxtrace (LM := LM)) (emtr: emtrace (EM := EM)):
    upto_stutter_eauxtr proj_ext eauxtr emtr ->
    (∀ ρ, fair_eaux ρ eauxtr) ->
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
      - punfold Hupto'; [| by apply upto_stutter_mono']. 
        by inversion Hupto'.
      - unfold role_enabled, role_enabled_model in *.
        rewrite HUs //. }
    have Hfa' := (fair_eaux_after ρ eauxtr n' auxtr' Hfa Heq' 0).
    have Hpredat: pred_at auxtr' 0 (λ δ _, role_enabled ρ δ).
    { rewrite /pred_at /=. destruct auxtr'; done. }
    destruct (upto_stutter_fairness_0 ρ auxtr' emtr' Hupto' (Hfa' Hpredat)) as (m&Hres).
    exists m. rewrite !(pred_at_sum _ n) Heq //.
    rewrite /fairness_sat. 
    rewrite -pred_at_or in Hres.
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
