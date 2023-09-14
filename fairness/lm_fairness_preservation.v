From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness fuel traces_match trace_utils.


(* TODO: move? *)
Lemma traces_match_LM_preserves_validity `{LM: LiveModel G M}
  `{C: Type} {L: Type}
   (otr: trace C L) (auxtr : auxtrace (LM := LM))
   state_rel lbl_rel outer_step :
  traces_match lbl_rel state_rel outer_step LM.(lm_ls_trans) otr auxtr ->
  auxtrace_valid auxtr (LM := LM).
Proof.
  revert otr auxtr. cofix CH. intros otr auxtr Hmatch.
  inversion Hmatch; first by constructor.
  constructor =>//. by eapply CH.
Qed.


Section fairness_preserved.
  Context `{LM: LiveModel G M}.
  Context `{EqDecision G}.

  (* State and labels of 'outer' model.
     On top level it corresponds to the language. *)
  (* TODO: formulate it in terms of actual model?
     Possible for heap_lang but not clear how to do so for arbitrary language
     (namely, how to uniformly define a state's set of live roles) *)
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

  Definition out_LM_labels_match (oζ : option Lo) (ℓ: lm_lbl LM) :=
  match oζ with
  | Some ζ =>
      exists τ, ζ = lift_grole τ /\
      match ℓ with
      | Take_step _ τ' | Silent_step τ' => τ = τ'
      | Config_step => False
      end
  | None => match ℓ with
           | Config_step => True
           | _ => False
           end
  end. 

  (* TODO: rename *)
  Definition lm_exaux_traces_match_gen: out_trace → auxtrace (LM := LM) → Prop :=
    traces_match 
    (* labels_match *) out_LM_labels_match
    (* live_tids *) state_rel
    (* locale_step  *) out_step
    LM.(lm_ls_trans).

  Lemma traces_match_labels tid ℓ c δ rex (raux : auxtrace (LM := LM)) :
    lm_exaux_traces_match_gen (c -[Some tid]-> rex) (δ -[ℓ]-> raux) ->
    exists τ, tid = lift_grole τ /\ 
    ((∃ ρ, ℓ = Take_step ρ τ) ∨ (ℓ = Silent_step τ)).
  Proof.
    intros Hm. inversion Hm as [|?????? Hlab]; simplify_eq.
    red in Hlab. destruct Hlab as [? [-> Hlab]]. 
    destruct ℓ; eauto; inversion Hlab; simplify_eq; eauto.
  Qed.

  Lemma mapping_live_role (δ: LiveState G M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_mapping δ !! ρ).
  Proof. rewrite -elem_of_dom ls_same_doms. SS. Qed.
  Lemma fuel_live_role (δ: LiveState G M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_fuel δ !! ρ).
  Proof. rewrite -elem_of_dom. SS. Qed.

  Local Hint Resolve mapping_live_role: core.
  Local Hint Resolve fuel_live_role: core.

  Lemma match_locale_prop (extr : out_trace) (auxtr : auxtrace (LM := LM)) ζ ρ:
    lm_exaux_traces_match_gen extr auxtr ->    
    ls_mapping (trfirst auxtr) !! ρ = Some ζ ->
    (* ρ ∈ live_roles _ (trfirst auxtr) -> *)
    locale_prop (lift_grole ζ) (trfirst extr).
  Proof.
    intros Hm Hloc (* Hlive *).
    eapply match_locale_prop_states; eauto.
    eapply traces_match_first; eauto.  
  Qed. 
  
  (* Local Hint Resolve match_locale_prop: core. *)
  Local Hint Resolve pred_first_trace: core.

  
  Definition steps_or_unassigned 
    (ρ: fmrole M) (δ: LiveState G M) (ℓ: option (lm_lbl LM)) :=
    (∀ τ, ls_mapping δ !! ρ ≠ Some τ) \/ (∃ τ, ℓ = Some $ Take_step ρ τ).     
    
  Definition fair_aux_SoU auxtr ρ n := 
    pred_at auxtr n (λ δ _, ρ ∈ dom (ls_mapping δ)) ->
    ∃ m, pred_at auxtr (n + m)
      (λ (δ : lm_ls LM) (ℓ : option (lm_lbl LM)), steps_or_unassigned ρ δ ℓ). 

  (* TODO: ? try to unify with fair_aux_after *)
  (* TODO: add ∀ in fair_aux_SoU definition  *)
  Lemma fair_aux_SoU_after ρ (auxtr: auxtrace (LM := LM))
    n auxtr':
    (forall k, fair_aux_SoU auxtr ρ k) ->
    after n auxtr = Some auxtr' ->
    (forall k, fair_aux_SoU auxtr' ρ k).
  Proof.
    rewrite /fair_aux_SoU => Hfair Hafter m Hpa.
    specialize (Hfair (n+m)).
    rewrite -> (pred_at_sum _ n) in Hfair. rewrite Hafter in Hfair.
    destruct (Hfair Hpa) as (p&Hp).
    exists (p).
    (* by rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n), Hafter in Hp. *)
    rewrite <-Nat.add_assoc, ->!(pred_at_sum _ n) in Hp.
    by rewrite Hafter in Hp. 
  Qed.

  Definition fairness_induction_stmt ρ fm f m τ extr (auxtr : auxtrace (LM := LM)) δ
    :=
      (infinite_trace extr ->
       (forall ζ, fair_by locale_prop ζ extr) ->
       fm = (f, m) ->
       lm_exaux_traces_match_gen extr auxtr ->
       δ = trfirst auxtr ->
       δ.(ls_fuel) !! ρ = Some f ->
       δ.(ls_mapping) !! ρ = Some τ ->
       (pred_at extr m (λ c _, ¬locale_prop (lift_grole τ) c) ∨ 
        pred_at extr m (λ _ oζ, oζ = Some (Some (lift_grole τ)))) ->
      ∃ M, pred_at auxtr M (fun δ ℓ => steps_or_unassigned ρ δ ℓ)). 
  
  Local Lemma case1 ρ f m (extr': out_trace) (auxtr' : auxtrace (LM := LM)) δ ℓ :
    (∀ m0 : nat * nat,
         strict lt_lex m0 (f, m)
         → ∀ (f m: nat) τ (extr : out_trace) (auxtr : auxtrace (LM := LM))
             (δ : LiveState G M), fairness_induction_stmt ρ m0 f m τ extr auxtr δ ) ->
    (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) ->
    lm_exaux_traces_match_gen extr' auxtr' ->
    infinite_trace extr' ->
    ls_fuel δ !! ρ = Some f ->
    (∀ ζ, fair_by locale_prop ζ extr') ->
    ∃ M0 : nat, pred_at (δ -[ ℓ ]-> auxtr') M0 (fun δ ℓ => steps_or_unassigned ρ δ ℓ).
    Proof.
      intros IH Hdec Hmatch Hinf Hsome Hfair.
      unfold oless in Hdec.
      simpl in *.
      rewrite -> Hsome in *.
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq.
      -
        
        (* destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first. *)
        destruct (decide (exists τ, ls_mapping (trfirst auxtr') !! ρ = Some τ)) as [MAP| ]; last first.
        { exists 1. apply pred_at_S.
          rewrite /steps_or_unassigned. apply pred_at_or. left.
          eapply pred_at_state_trfirst. eauto. }
        (* have [τ' Hτ'] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto. *)
        destruct MAP as [τ' Hτ']. 

        have Hloc'en: pred_at extr' 0 (λ (c : So) (_ : option (option Lo)),
                          locale_prop (lift_grole τ') c).
        { rewrite /pred_at /= pred_first_trace.
          eapply match_locale_prop; eauto. }

        have [p Hp] := (Hfair (lift_grole τ') 0 Hloc'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (steps_or_unassigned ρ).
        { eapply (IH _ _ _ p _ extr'); eauto.
          Unshelve. unfold strict, lt_lex. specialize (Hdec ltac:(by eapply elem_of_dom_2)).
          lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
      - exists 1. apply pred_at_S.
        rewrite /steps_or_unassigned. apply pred_at_or. left.
        apply pred_at_state_trfirst.
        rewrite -ls_same_doms in Hdec.
        intros ??. apply Hdec, elem_of_dom. eauto. 
    Qed.

    Local Ltac SS' :=
      (* epose proof ls_fuel_dom; *)
      (* set_solver. *)
      eapply elem_of_dom; eauto. 

    Lemma others_step_fuel_decr ρ f f' τ
      δ ℓ auxtr' 
      c ζ' extr'
      (Htm: lm_exaux_traces_match_gen (c -[ ζ' ]-> extr') (δ -[ ℓ ]-> auxtr'))
      (Hfuel : ls_fuel δ !! ρ = Some f)
      (Hmapping : ls_mapping δ !! ρ = Some τ)
      (Hζ: Some (lift_grole τ) ≠ ζ')
      (FUEL: ls_fuel (trfirst auxtr') !! ρ = Some f'):
      f' ≤ f.
    Proof.
      inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
      destruct ζ' as [ζ'|]; last first; simpl in *.
      - simpl in *. destruct ℓ; try done. destruct Hls as [_ [_ [Hnoninc _]]].
        have HnotNone: Some ρ ≠ None by congruence.
        specialize (Hnoninc ρ ltac:(SS')).
        unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
        rewrite FUEL in Hnoninc. 
        destruct Hnoninc as [?|[?|C]]. 
        3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
        all: set_solver. 
      - destruct Hl as [τ' [-> Hl]]. 
        simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
        + destruct Hls as (?&?&?&Hnoninc&?).
          unfold fuel_must_not_incr in Hnoninc.
          have Hneq: Some ρ ≠ Some ρ0 by congruence.
          specialize (Hnoninc ρ ltac:(SS')).
          unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
          rewrite FUEL in Hnoninc.
          destruct Hnoninc as [?|[?|C]]. 
          3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
          all: set_solver. 
        + destruct Hls as (?&?&Hnoninc&?).
          unfold fuel_must_not_incr in Hnoninc.
          have Hneq: Some ρ ≠ None by congruence.
          specialize (Hnoninc ρ ltac:(SS')).
          unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
          rewrite FUEL in Hnoninc. 
          destruct Hnoninc as [?|[?|C]]. 
          3: { destruct (proj1 C). eapply elem_of_dom; eauto. }
          all: set_solver. 
    Qed.
    
    Lemma owner_change_fuel_decr ρ f f'
      c τ extr'
      δ ℓ auxtr'
      ζ' τ''
      (Htm: lm_exaux_traces_match_gen (c -[ ζ' ]-> extr') (δ -[ ℓ ]-> auxtr'))
      (Hfuel: ls_fuel δ !! ρ = Some f)
      (Hmapping: ls_mapping δ !! ρ = Some τ)
      (* (Hρlive: ρ ∈ live_roles M δ) *)
      (* (Hρlive': ρ ∈ live_roles M (trfirst auxtr')) *)
      (Hζ'' : ls_mapping (trfirst auxtr') !! ρ = Some τ'')
      (Hchange : τ ≠ τ'')
      (FUEL: ls_fuel (trfirst auxtr') !! ρ = Some f'):
      f' < f.
    Proof.
      destruct ζ' as [ζ'|]; last first; simpl in *.
      - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        simpl in *. destruct ℓ; try done. destruct Hls as [_ [Hdec _]].
        unfold fuel_decr in Hdec.
        have Hmd: must_decrease ρ None δ (trfirst auxtr') None.
        { econstructor. congruence. rewrite Hζ''. eauto. }
        specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
        unfold oleq in Hdec. rewrite Hfuel in Hdec.
        by rewrite FUEL in Hdec. 
      - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        simpl in *.
        destruct Hl as [τ' [-> Hl]]. 
        destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
        + destruct Hls as (?&?&Hdec&?&?).
          unfold fuel_decr in Hdec. simplify_eq.
          have Hmd: must_decrease ρ (Some ρ0) δ (trfirst auxtr') (Some ζ0).
          { econstructor 2. congruence. rewrite Hζ''; eauto. }
          specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
          unfold oleq in Hdec. rewrite Hfuel in Hdec.
          by rewrite FUEL in Hdec. 
        + destruct Hls as (?&Hdec&_).
          unfold fuel_decr in Hdec. simplify_eq.
          have Hmd: must_decrease ρ None δ (trfirst auxtr') (Some ζ0).
          { econstructor 2. congruence. rewrite Hζ''; eauto. }
          specialize (Hdec ρ ltac:(SS') ltac:(SS') Hmd).
          unfold oleq in Hdec. rewrite Hfuel in Hdec.
          by rewrite FUEL in Hdec. 
    Qed.


  Lemma fairness_preserved_ind ρ:
    ∀ fm f m τ (extr: out_trace) (auxtr: auxtrace (LM := LM)) δ,
      fairness_induction_stmt ρ fm f m τ extr auxtr δ.
  Proof.
    induction fm as [fm IH] using lex_ind.
    intros f m τ extr auxtr δ Hexinfin Hfair -> Htm -> Hfuel Hmapping Hexen.
    destruct extr as [|c ζ' extr'] eqn:Heq.
    { have [??] := Hexinfin 1. done. }
    have Hfair': (forall τ, fair_by locale_prop τ extr').
    { intros. by eapply fair_by_cons. }
    destruct auxtr as [|δ ℓ auxtr']; first by inversion Htm.
    simpl in *. 
    (* destruct (decide (ρ ∈ live_roles M δ)) as [Hρlive|]; last first. *)
    (* { exists 0. left. unfold pred_at. simpl. intros contra. eauto. } *)
    destruct (decide (Some (lift_grole τ) = ζ')) as [Hζ|Hζ].
    - rewrite <- Hζ in *.
      destruct (traces_match_labels _ _ _ _ _ _ Htm) as [τ' [LIFT_EQ Htm']].
      apply INJlg in LIFT_EQ as <-. 
      destruct Htm' as [[ρ' ->]| ->]; last first.
      + inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        unfold ls_trans in Hls. simpl in Hls. 
        destruct Hls as (? & Hlsdec & Hlsincr).
        unfold fuel_decr in Hlsdec.
        have Hmustdec: must_decrease ρ None δ (trfirst auxtr') (Some τ).
        { constructor; eauto. }
        eapply case1 =>//.
        * move=> Hinfuel; apply Hlsdec => //; first set_solver.
        * eapply infinite_cons =>//.
      + (* Three cases: *)
(*            (1) ρ' = ρ and we are done *)
(*            (2) ρ' ≠ ρ but they share the same ρ -> ρ decreases *)
(*            (3) ρ' ≠ ρ and they don't have the same tid -> *)
(*            impossible because tid and the label must match! *)
        inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        destruct (decide (ρ = ρ')) as [->|Hρneq].
        { exists 0. right. rewrite /pred_at /=. eauto. }
        destruct Hls as (?&Hsame&Hdec&Hnotinc&_).
        rewrite -Hsame /= in Hmapping.
        have Hmustdec: must_decrease ρ (Some ρ') δ (trfirst auxtr') (Some τ).
        { constructor; eauto; congruence. }
        (* Copy and paste begins here *)
        eapply case1 =>//; last by eauto using infinite_cons.
        intros Hinfuels. apply Hdec =>//. 
        clear -Hfuel. apply elem_of_dom; eauto.

    - (* Another thread is taking a step. *)
      (* destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first. *)
      destruct (decide (exists τ, ls_mapping (trfirst auxtr') !! ρ = Some τ)) as [MAP| ]; last first.
      { exists 1. apply pred_at_or. left.
        eapply pred_at_state_trfirst; eauto. }
      destruct m as [| m'].
      { rewrite -> !pred_at_0 in Hexen. destruct Hexen as [Hexen|Hexen].
        - exfalso. apply Hexen. eapply (match_locale_prop _ _ _ _ Htm); eauto. 
        - simplify_eq. }
      (* have [τ'' Hτ''] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto. *)
      destruct MAP as [τ'' Hτ'']. 
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'| ] eqn:Hfuel'.
      2: { apply elem_of_dom_2 in Hτ''. apply not_elem_of_dom_2 in Hfuel'.
           rewrite ls_same_doms in Hτ''. done. }
      destruct (decide (τ = τ'')) as [<-|Hchange].
      +
        (* have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f. *)
        assert (f' <= f) as Hff' by (eapply others_step_fuel_decr; eauto).

        unfold fair_by in *.
        have Hζ'en: pred_at extr' 0 (λ (c : So) _, locale_prop (lift_grole τ) c).
        { rewrite /pred_at /= pred_first_trace.
          eapply match_locale_prop; eauto. 
          by inversion Htm. }

        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (steps_or_unassigned ρ).
        { eapply (IH _ _ _ m' _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.

      +
        assert (f' < f) as Hff' by (eapply owner_change_fuel_decr; eauto). 

        unfold fair_by in *.
        have: pred_at extr' 0 (λ c _, locale_prop (lift_grole τ'') c).
        { rewrite /pred_at /= pred_first_trace.
          eapply match_locale_prop; eauto. 
          by inversion Htm. }
        have Hζ'en: pred_at extr' 0 (λ c _, locale_prop (lift_grole τ'') c).
        { rewrite /pred_at /= pred_first_trace.
          eapply match_locale_prop; eauto. 
          by inversion Htm. }
        have [p Hp] := (Hfair' (lift_grole τ'') 0 Hζ'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (steps_or_unassigned ρ).
        { eapply (IH _ _ _ p _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
  Qed.

  
  Lemma exec_fairness_implies_step_or_unassign (extr: out_trace) (auxtr: auxtrace (LM := LM)):
    infinite_trace extr ->
    lm_exaux_traces_match_gen extr auxtr ->
    (forall ζ, fair_by locale_prop ζ extr) ->
    forall ρ n, fair_aux_SoU auxtr ρ n.
  Proof.
    intros Hinfin Hmatch Hex ρ n.
    red.
    intros DOMn.
    unfold pred_at in DOMn.
    destruct (after n auxtr) as [tr|] eqn:Heq; rewrite Heq in DOMn.
    2: { done. } 
    setoid_rewrite pred_at_sum. rewrite Heq.

    have [τ Hτ] : is_Some((trfirst tr).(ls_mapping) !! ρ).
    { destruct tr; apply elem_of_dom; eauto. }
    clear DOMn.
    have [f Hfuel] : is_Some((trfirst tr).(ls_fuel) !! ρ).
    { apply elem_of_dom. rewrite -ls_same_doms. eapply elem_of_dom; eauto. }
    
    have Hex' := Hex (lift_grole τ) n.
    have [tr1' [Heq' Htr]] : exists tr1', after n extr = Some tr1' ∧ lm_exaux_traces_match_gen tr1' tr
     by eapply traces_match_after.
    have Hte: locale_prop (lift_grole τ) (trfirst tr1').
    { eapply match_locale_prop; eauto. }
    
    setoid_rewrite pred_at_sum in Hex'. rewrite Heq' in Hex'.
    have Hpa: pred_at extr n (λ c _, locale_prop (lift_grole τ) c).
    { unfold pred_at. rewrite Heq'. destruct tr1'; eauto. }
    destruct (Hex' Hpa) as [m Hm].
    have ?: infinite_trace tr1'.
    { have Hinf := infinite_trace_after n extr Hinfin. by rewrite Heq' in Hinf. }
    eapply (fairness_preserved_ind ρ _ f m τ _ tr); eauto.
    intros ?. by eapply fair_by_after.
  Qed.

  Lemma steps_or_unassigned_implies_aux_fairness (auxtr: auxtrace (LM := LM)):
    (forall ρ n, fair_aux_SoU auxtr ρ n) -> (forall ρ, fair_aux ρ auxtr (LM := LM)).
  Proof.
    intros FAIR ρ n Hn.
    eapply pred_at_impl in Hn.
    2: { intros ? ? EN%mapping_live_role%elem_of_dom. apply EN. }
    specialize (FAIR _ _ Hn). destruct FAIR as (m & STEP).
    exists m.
    apply pred_at_or in STEP. destruct STEP; eauto. left.
    eapply pred_at_impl; eauto. intros. simpl in *.
    intros [??]%mapping_live_role. congruence.
  Qed.   
 
    
  Theorem fairness_preserved (extr: out_trace) (auxtr: auxtrace (LM := LM)):
    infinite_trace extr ->
    lm_exaux_traces_match_gen extr auxtr ->
    (forall ζ, fair_by locale_prop ζ extr) -> (forall ρ, fair_aux ρ auxtr (LM := LM)).
  Proof.
    intros.
    apply steps_or_unassigned_implies_aux_fairness.
    eapply exec_fairness_implies_step_or_unassign; eauto.
  Qed. 

End fairness_preserved.


Section lang_fairness_preserved.
  Context `{LM: LiveModel (locale Λ) M}.
  Context `{EqDecision (locale Λ)}.

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

  Theorem ex_fairness_preserved (extr: extrace Λ) (auxtr: auxtrace (LM := LM)):
    infinite_trace extr ->
    lm_exaux_traces_match extr auxtr ->
    (forall ζ, fair_ex ζ extr) -> (forall ρ, fair_aux ρ auxtr (LM := LM)).
  Proof.
    intros. eapply fairness_preserved; eauto.
    { apply _. }
    eapply match_locale_enabled_states_livetids; eauto.
    Unshelve. apply _.
  Qed.

End lang_fairness_preserved. 


Section model_fairness_preserved.
  Context `{LM: LiveModel G M}.
  Context `{EqDecision G}.

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
  
  Theorem model_fairness_preserved (mtr: mtrace Mout) (auxtr: auxtrace (LM := LM)):
    infinite_trace mtr ->
    lm_model_traces_match mtr auxtr ->
    (∀ ρ, fair_model_trace ρ mtr) -> (forall ρ, fair_aux ρ auxtr (LM := LM)).
  Proof.
    intros. eapply fairness_preserved; eauto.
    Unshelve. apply _.
  Qed.

End model_fairness_preserved. 
