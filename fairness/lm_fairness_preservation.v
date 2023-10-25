From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness fuel traces_match trace_utils lm_fair_traces lm_fair trace_helpers trace_lookup. 


Section fairness_preserved.
  Context `{LM: LiveModel G M LSI}.
  (* Context `{EqDecision G}. *)
  Context {LF: LMFairPre LM}. 

  Lemma mapping_live_role (δ: LiveState G M LSI) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_mapping δ !! ρ).
  Proof. by intros ?%ls_mapping_dom%elem_of_dom. Qed.
  Lemma fuel_live_role (δ: LiveState G M LSI) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_fuel δ !! ρ).
  Proof. 
    intros ?%ls_mapping_dom.
    apply elem_of_dom. by rewrite -ls_same_doms.
  Qed. 

  Local Hint Resolve mapping_live_role: core.
  Local Hint Resolve fuel_live_role: core.

  Local Hint Resolve pred_first_trace: core.

  (* TODO: fix names below *)
  
  (* Definition group_step_or_dis *)
  (*   (τ: G) (δ: LiveState G M LSI) (oℓ: option (lm_lbl LM)) := *)
  (*   (forall ρ, ¬ ls_mapping δ !! ρ = Some τ) \/ (∃ ℓ, oℓ = Some ℓ /\ lm_lbl_matches_group ℓ τ). *)
  Definition group_step_or_dis (τ: G) (δ: LiveState G M LSI) (og: option $ option G) :=
    fairness_sat (λ τ δ, exists ρ, ls_mapping δ !! ρ = Some τ) (fun t og' => og' = Some t) τ δ og.

  Definition fair_by_group: G -> lmftrace (LM := LM) -> Prop := 
    fair_by (λ τ δ, exists ρ, ls_mapping δ !! ρ = Some τ)
      (fun t og' => og' = Some t). 
  
  (* Definition steps_or_unassigned *)
  (*   (ρ: fmrole M) (δ: LiveState G M LSI) (ℓ: option (lm_lbl LM)) := *)
  (*   (∀ τ, ls_mapping δ !! ρ ≠ Some τ) \/ (∃ τ, ℓ = Some $ Take_step ρ τ). *)
  Definition steps_or_unassigned :=
    fairness_sat_gen (λ ρ δ, ρ ∈ dom (ls_mapping δ)) step_by_next_TS.
    
  Definition fair_aux_SoU: fmrole M -> lmftrace (LM := LM) -> Prop := 
    fair_by_gen (λ ρ δ, ρ ∈ dom (ls_mapping δ))
      step_by_next_TS. 

  Definition fairness_induction_stmt ρ fm f m τ (* extr *) (auxtr : lmftrace (LM := LM)) δ
    :=
    infinite_trace auxtr ->
    (forall τ, fair_by_group τ auxtr) ->
    fm = (f, m) ->
    δ = trfirst auxtr ->
    δ.(ls_fuel) !! ρ = Some f ->
    δ.(ls_mapping) !! ρ = Some τ ->
    pred_at auxtr m (fun δ oℓ => group_step_or_dis τ δ oℓ)
    ->
    (* ∃ M, pred_at auxtr M (fun δ ℓ => steps_or_unassigned ρ δ ℓ)).  *)
    exists i δi ostep, auxtr !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep.
  
  Local Lemma case1 ρ f m (auxtr' : lmftrace (LM := LM)) δ ℓ :
    (∀ m0 : nat * nat,
         strict lt_lex m0 (f, m)
         → ∀ (f m: nat) τ (auxtr : lmftrace (LM := LM))
             (δ : LiveState G M LSI),
          mtrace_valid auxtr -> fairness_induction_stmt ρ m0 f m τ (* extr *) auxtr δ ) ->
    (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) ->
    mtrace_valid auxtr' ->
    infinite_trace auxtr' ->
    ls_fuel δ !! ρ = Some f ->
    (forall τ, fair_by_group τ auxtr' ) ->
    ∃ i δi ostep, (δ -[ ℓ ]-> auxtr') !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep.
  Proof.
      intros IH Hdec (* Hmatch *) Hvalid Hinf Hsome Hfair.
      unfold oless in Hdec.
      simpl in *.
      rewrite -> Hsome in *.
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq.
      -
        destruct (decide (exists τ, ls_mapping (trfirst auxtr') !! ρ = Some τ)) as [MAP| ]; last first.
        { exists 1. rewrite trace_lookup_cons.
          pose proof (trace_lookup_0 auxtr') as (?&?).
          do 2 eexists. split; eauto. 
          rewrite /steps_or_unassigned. left.
          intros ?%elem_of_dom. apply n. done. }
        destruct MAP as [τ' Hτ']. 
        pose proof (Hfair τ' 0) as [p Hp]. 
        { rewrite pred_at_state_trfirst. eauto. } 

        assert (∃ i δi ostep, auxtr' !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep) as (i&?&?&?&?). 
        { eapply (IH _ _ _ p _); eauto.
          Unshelve. 
          unfold strict, lt_lex. specialize (Hdec ltac:(by eapply elem_of_dom_2)).
          rewrite Heq in Hdec. lia. } 
        exists (1+i). eauto. 
      - pose proof (trace_lookup_0 auxtr') as (?&?).
        exists 1. do 2 eexists. rewrite trace_lookup_cons. split; eauto. 
        rewrite /steps_or_unassigned. left.
        apply not_elem_of_dom in Heq. by rewrite -ls_same_doms in Heq. 
  Qed.
  
  Lemma fairness_preserved_ind ρ:
    ∀ fm f m τ (auxtr: lmftrace (LM := LM)) δ,
      mtrace_valid auxtr -> 
      fairness_induction_stmt ρ fm f m τ auxtr δ.
  Proof.    
    induction fm as [fm IH] using lex_ind.
    intros f m τ auxtr δ VALID Hexinfin Hfair -> Htm Hfuel Hmapping Hexen.
    destruct auxtr as [|δ_ ℓ auxtr'] eqn:Heq.
    { have [??] := Hexinfin 1. done. }
    have Hfair': (forall τ, fair_by_group τ auxtr'). 
    { intros. eapply fair_by_cons; eauto. apply Hfair. }
    simpl in *. subst δ_. 
    (* destruct (decide (lm_lbl_matches_group ℓ τ)) as [Hζ|Hζ]. *)
    destruct (decide (ℓ = Some τ)) as [Hζ|Hζ]. 
    - subst.
      (* pose proof (mtrace_valid_steps' VALID 0) as Hls.  *)
      pose proof (trace_valid_cons_inv _ _ _ _ VALID) as [_ Hls]. simpl in Hls.
      destruct (next_TS_role δ τ (trfirst auxtr')) eqn:N. 
      + (* Three cases: *)
(*            (1) ρ' = ρ and we are done *)
(*            (2) ρ' ≠ ρ but they share the same ρ -> ρ decreases *)
(*            (3) ρ' ≠ ρ and they don't have the same tid -> *)
(*            impossible because tid and the label must match! *)
        clear Hls. 
        pose proof N as Hls%next_TS_spec_pos. 
        destruct (decide (ρ = f0)) as [->|Hρneq].
        { exists 0. do 2 eexists. rewrite trace_lookup_0_cons. split; eauto. 
          right. red. eauto. }
        destruct Hls as (?&Hsame&Hdec&Hnotinc&_).
        rewrite -Hsame /= in Hmapping.
        have Hmustdec: must_decrease ρ (Some f0) δ (trfirst auxtr') (Some τ).
        { constructor; eauto; congruence. }
        (* Copy and paste begins here *)
        eapply case1 =>//; last by eauto using infinite_cons.
        2: { eapply trace_valid_cons_inv; eauto. }
        intros Hinfuels. apply Hdec =>//. 
        clear -Hfuel. apply elem_of_dom; eauto.
      + eapply next_TS_spec_inv_S in N; eauto. clear Hls. rename N into Hls.  
        destruct Hls as (? & Hlsdec & Hlsincr).
        unfold fuel_decr in Hlsdec.
        have Hmustdec: must_decrease ρ None δ (trfirst auxtr') (Some τ).
        { constructor; eauto. }
        eapply case1 =>//.
        * move=> Hinfuel; apply Hlsdec => //; first set_solver.
        * eapply trace_valid_cons_inv; eauto. 
        * eapply infinite_cons =>//.
    - (* Another thread is taking a step. *)
      destruct (decide (exists τ, ls_mapping (trfirst auxtr') !! ρ = Some τ)) as [MAP| ]; last first.
      { exists 1. pose proof (trace_lookup_0 auxtr') as (?&?). 
        do 2 eexists. rewrite trace_lookup_cons. split; eauto.         
        left. by intros ?%elem_of_dom. }
      destruct m as [| m'].
      { rewrite -> !pred_at_0 in Hexen.
        red in Hexen. destruct Hexen as [Hexen|Hexen].
        - exfalso. set_solver. 
        - destruct Hexen as (?&?&?). set_solver. }
      pose proof (trace_valid_cons_inv _ _ _ _ VALID) as [_ Hls]. simpl in Hls.
      destruct ℓ; [| done]. 
      destruct MAP as [τ'' Hτ'']. 
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'| ] eqn:Hfuel'.
      2: { apply elem_of_dom_2 in Hτ''. apply not_elem_of_dom_2 in Hfuel'.
           rewrite ls_same_doms in Hτ''. done. }
      red in Hls. destruct Hls as (ℓ & STEP & MATCH). 
      destruct (decide (τ = τ'')) as [<-|Hchange].
      + assert (f' <= f) as Hff'.
        { eapply others_step_fuel_decr; eauto.
          destruct ℓ; simpl in *; congruence. }
        unfold fair_by in *.
        assert (exists i δi ostep, auxtr' !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep) as (P&?&?&Hind).
        { eapply (IH _ _ _ m' _); eauto.
          - eapply trace_valid_cons_inv; eauto.
          - by eapply infinite_cons.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). eauto.
      + assert (f' < f) as Hff' by (eapply owner_change_fuel_decr; eauto). 
        unfold fair_by in *.
        pose proof (Hfair' τ'' 0) as [p Hp].
        { rewrite pred_at_state_trfirst. eauto. }        
        assert (exists i δi ostep, auxtr' !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep) as (P&?&?&Hind).
        { eapply (IH _ _ _ p _); eauto.
          - eapply trace_valid_cons_inv; eauto.
          - by eapply infinite_cons.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). eauto.
  Qed.
  
  Lemma group_fairness_implies_step_or_unassign
    (auxtr: lmftrace (LM := LM)):
    infinite_trace auxtr ->
    mtrace_valid auxtr ->
    (forall τ, fair_by_group τ auxtr) ->
    forall ρ, fair_aux_SoU ρ auxtr.
  Proof.
    intros Hinfin Hmatch Hex ρ.
    red. intros n DOMn.
    unfold pred_at in DOMn.
    destruct (after n auxtr) as [tr|] eqn:Heq; rewrite Heq in DOMn.
    2: { done. } 
    (* setoid_rewrite pred_at_sum. rewrite Heq. *)
    setoid_rewrite <- trace_lookup_after; eauto.  

    have [τ Hτ] : is_Some((trfirst tr).(ls_mapping) !! ρ).
    { destruct tr; apply elem_of_dom; eauto. }
    clear DOMn.
    have [f Hfuel] : is_Some((trfirst tr).(ls_fuel) !! ρ).
    { apply elem_of_dom. rewrite -ls_same_doms. eapply elem_of_dom; eauto. }
    have Hex' := Hex τ n.

    setoid_rewrite pred_at_sum in Hex'.
    destruct Hex' as [m Hm].
    { red. rewrite Heq. destruct tr; eauto. }

    rewrite Heq in Hm.
    have ?: infinite_trace tr.
    { have Hinf := infinite_trace_after n auxtr Hinfin. by rewrite Heq in Hinf. }
    eapply (fairness_preserved_ind ρ _ f m τ _); eauto.
    - eapply trace_valid_after; eauto. 
    - intros. eapply fair_by_after; eauto. apply Hex. 
  Qed.

  (* TODO: move*)
  Lemma pred_at_ex {S L T: Type} (P : T -> S → option L → Prop) tr n:
    pred_at tr n (fun s ol => exists t, P t s ol) <-> exists t, pred_at tr n (P t).
  Proof.
    rewrite /pred_at. destruct after.
    2: { intuition. by destruct H. }
    destruct t; eauto.
  Qed.     

  Lemma steps_or_unassigned_implies_aux_fairness (auxtr: lmftrace (LM := LM)):
    (forall ρ, fair_aux_SoU ρ auxtr) -> (forall ρ, fair_by_next_TS ρ auxtr).
  Proof.
    intros FAIR ρ n Hn.
    eapply pred_at_impl in Hn.
    2: { intros ?? EN%mapping_live_role%elem_of_dom. apply EN. }
    specialize (FAIR _ _ Hn).
    destruct FAIR as (m&?&?&NMth&STEP).
    exists m.
    do 2 eexists. split; eauto. 
    destruct STEP. 
    - left. intros ?%mapping_live_role.
      by apply H, elem_of_dom.
    - by right.
  Qed.

  Lemma group_fairness_implies_role_fairness (auxtr: lmftrace (LM := LM)):
    infinite_trace auxtr ->
    mtrace_valid auxtr ->
    (forall τ, fair_by_group τ auxtr) ->
    (forall ρ, fair_by_next_TS ρ auxtr).
  Proof. 
    intros. auto using steps_or_unassigned_implies_aux_fairness, 
      group_fairness_implies_step_or_unassign.
  Qed. 
    
  Section Preservation.
    Context {So Lo: Type}.
    Context `{EqDecision Lo}. 
    
    Let out_trace := trace So (option Lo).
    
    (* counterpart of locale step.
       TODO: any restrictions? *)
    Context (out_step: So -> option Lo -> So -> Prop). 
    
    (* Representation of group labels on outer level *)
    Context (lift_grole: G -> Lo).
    Hypothesis (INJlg: Inj eq eq lift_grole). 
    
    Context (locale_prop: Lo -> So -> Prop).
    
    (* Context (state_rel: cfg Λ → lm_ls LM → Prop). *)
    Context (state_rel: So → lm_ls LM → Prop).
    
    Definition lm_live_lift := forall ζ ρ δ c,
        ls_mapping δ !! ρ = Some ζ ->
        (* ρ ∈ live_roles _ δ ->  *)
        state_rel c δ ->
        (* locale_enabled ζ c *)
        locale_prop (lift_grole ζ) c. 
    
    
    Hypothesis (match_locale_prop_states: lm_live_lift).
    
    (* Definition out_LM_labels_match (oζ : option Lo) (ℓ: lm_lbl LM) := *)
    (*   match oζ with *)
    (*   | Some ζ => *)
    (*       exists τ, ζ = lift_grole τ /\ *)
    (*              match ℓ with *)
    (*              | Take_step _ τ' | Silent_step τ' => τ = τ' *)
    (*              | Config_step => False *)
    (*              end *)
    (*   | None => match ℓ with *)
    (*            | Config_step => True *)
    (*            | _ => False *)
    (*            end *)
    (*   end.  *)
    
    Definition out_LMF_labels_match (oζ : option Lo) (oℓ: option G) :=
      match oζ, oℓ with
      | Some ζ, Some ℓ => lift_grole ℓ = ζ
      | None, None => True
      | _, _ => False
      end. 
    
    (* TODO: rename *)
    Definition lm_exaux_traces_match_gen: out_trace → lmftrace (LM := LM) → Prop :=
      traces_match 
        (* labels_match *) out_LMF_labels_match
        (* live_tids *) state_rel
        (* locale_step  *) out_step
        (fmtrans LM_Fair). 
    
    From trillium.fairness Require Import trace_lookup.
    
    (* TODO: move *)
    Lemma pred_at_impl {St L : Type} (P Q: St -> option L -> Prop)
      (IMPL: forall s ol, P s ol -> Q s ol):
      forall tr i, pred_at tr i P -> pred_at tr i Q.
    Proof.
      rewrite /pred_at. intros. 
      destruct after; intuition; destruct t.
      all: by apply IMPL.
    Qed.
    
    Let lbl_match (ℓ: Lo) oℓ' := oℓ' = Some ℓ. 
    
    Theorem fairness_preserved (extr: out_trace) (auxtr: lmftrace (LM := LM)):
      infinite_trace extr ->
      lm_exaux_traces_match_gen extr auxtr ->
      (forall ζ, fair_by locale_prop lbl_match ζ extr) -> (forall τ, fair_by_group τ auxtr).
    Proof.
      intros INF MATCH FAIR_OUT.
      intros. do 2 red. intros n ASG.
      pose proof ASG as (δ & NTH & [ρ MAP])%pred_at_trace_lookup.
      
      edestruct @traces_match_state_lookup_2 as (c & ENTH & RELn); eauto.
      
      red in FAIR_OUT. edestruct FAIR_OUT as [m STEP].
      { eapply pred_at_trace_lookup; eauto. }
      apply pred_at_or in STEP.
      
      apply pred_at_or in STEP. 
      apply pred_at_trace_lookup in STEP as (c' & ENTH' & STEP).
      edestruct @traces_match_state_lookup_1 as (δ' & NTH' & RELn'); eauto. 
      exists m. apply pred_at_trace_lookup. eexists. split; eauto.
      red. destruct STEP as [EMP | STEP]. 
      - left. intros [??]. apply EMP. eapply match_locale_prop_states; eauto.  
      - right.
        destruct STEP as (?&?&LBLM). 
        edestruct @traces_match_label_lookup_1 as (ℓ & NTH'l & LBL); eauto.
        eexists. split; eauto. red in LBL.
        red in LBLM. subst.
        destruct ℓ; try done.
        apply INJlg in LBL. congruence.
    Qed.      
    
  End Preservation.

End fairness_preserved.


(* TODO: move? *)
Lemma traces_match_LM_preserves_validity `{LM: LiveModel G M LSI} {LF: LMFairPre LM}
  `{C: Type} {L: Type}
  (otr: trace C L) (auxtr : lmftrace (LM := LM))
  state_rel lbl_rel outer_step :
  traces_match lbl_rel state_rel outer_step ((fmtrans LM_Fair)) otr auxtr ->
  mtrace_valid auxtr.
Proof.
  revert otr auxtr. pcofix CH. intros otr auxtr Hmatch.
  pfold. 
  inversion Hmatch; [by econstructor| ].
  constructor =>//.
  specialize (CH _ _ H3).
  eauto.   
Qed.

Section lang_fairness_preserved.
  Context `{LM: LiveModel (locale Λ) M LSI}.
  (* Context `{EqDecision (locale Λ)}. *)
  Context {LF: LMFairPre LM}. 

  Definition lm_exaux_traces_match :=
    lm_exaux_traces_match_gen
      (locale_step (Λ := Λ))
      (id: locale Λ -> locale Λ)
      (live_tids (LM := LM)). 

  Lemma match_locale_enabled_states_livetids: lm_live_lift id locale_enabled live_tids (LM := LM).
  Proof.
    red. intros ζ ρ δ c Hloc Hsr. 
    rewrite /locale_enabled.
    destruct Hsr as [HiS Hneqloc].
    have [e Hein] := (HiS _ _ Hloc). exists e. split; first done.
    destruct (to_val e) eqn:Heqe =>//.
    exfalso. specialize (Hneqloc ζ e Hein). rewrite Heqe in Hneqloc.
    have Hv: Some v ≠ None by []. by specialize (Hneqloc Hv ρ).
  Qed.

  Theorem ex_fairness_preserved (extr: extrace Λ) (auxtr: lmftrace (LM := LM)):
    infinite_trace extr ->
    lm_exaux_traces_match extr auxtr ->
    (forall ζ, fair_ex ζ extr) -> (∀ ρ : fmrole M, fair_by_next_TS ρ auxtr).
  Proof.
    intros. eapply group_fairness_implies_role_fairness; eauto. 
    { eapply traces_match_infinite_trace; eauto. }
    { eapply traces_match_LM_preserves_validity; eauto. }
    eapply fairness_preserved; eauto.
    { apply _. }
    eapply match_locale_enabled_states_livetids; eauto.
  Qed.

End lang_fairness_preserved. 


Section model_fairness_preserved.
  Context `{LM: LiveModel G M LSI}.
  (* Context `{EqDecision G}. *)
  Context {LF: LMFairPre LM}. 

  Context `{Mout: FairModel}. 

  Context (lift_grole: G -> fmrole Mout).
  Hypothesis (INJlg: Inj eq eq lift_grole). 

  Context (state_rel: fmstate Mout → lm_ls LM → Prop).

  Hypothesis (match_labels_prop_states: 
               lm_live_lift lift_grole role_enabled_model state_rel).


  Definition lm_model_traces_match :=
    lm_exaux_traces_match_gen
      (fmtrans Mout)
      lift_grole
      state_rel. 
  
  Theorem model_fairness_preserved (mtr: mtrace Mout) (auxtr: lmftrace (LM := LM)):
    infinite_trace mtr ->
    lm_model_traces_match mtr auxtr ->
    (∀ ρ, fair_model_trace ρ mtr) -> (∀ ρ : fmrole M, fair_by_next_TS ρ auxtr).
  Proof.
    intros. eapply group_fairness_implies_role_fairness; eauto. 
    { eapply traces_match_infinite_trace; eauto. }
    { eapply traces_match_LM_preserves_validity; eauto. }
    eapply fairness_preserved; eauto.
  Qed.

End model_fairness_preserved. 
