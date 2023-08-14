From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness fuel traces_match. 


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
  (* TODO: require injectivity? *)
  Context (lift_grole: G -> Lo).
  Hypothesis (INJlg: Inj eq eq lift_grole). 
  
  (* Context (locale_prop: locale Λ -> cfg Λ -> Prop).  *)
  Context (locale_prop: Lo -> So -> Prop).

  Definition fair_by (ζ: Lo) (otr: out_trace): Prop :=
    forall n, pred_at otr n (λ c _, locale_prop ζ c) ->
         ∃ m, pred_at otr (n+m) (λ c _, ¬ locale_prop ζ c)
              ∨ pred_at otr (n+m) (λ _ otid, otid = Some (Some ζ)).


  (* Context (state_rel: cfg Λ → lm_ls LM → Prop). *)
  Context (state_rel: So → lm_ls LM → Prop).

  Hypothesis (match_locale_prop_states: 
               forall ζ ρ δ c,
                 ls_mapping δ !! ρ = Some ζ ->
                 ρ ∈ live_roles _ δ -> 
                 state_rel c δ ->
                 (* locale_enabled ζ c *)
                 locale_prop (lift_grole ζ) c
             ).

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
    ρ ∈ live_roles _ (trfirst auxtr) ->
    (* locale_prop ζ (trfirst extr). *)
    locale_prop (lift_grole ζ) (trfirst extr).
  Proof.
    intros Hm Hloc Hlive.
    eapply match_locale_prop_states; eauto.
    eapply traces_match_first; eauto.  
  Qed. 
  
  (* Local Hint Resolve match_locale_prop: core. *)
  Local Hint Resolve pred_first_trace: core.

  Definition fairness_induction_stmt ρ fm f m (* ζ *) τ extr (auxtr : auxtrace (LM := LM))
    δ
    (* c *)
    :=
      (infinite_trace extr ->
       (forall ζ, fair_by ζ extr) ->
       fm = (f, m) ->
       lm_exaux_traces_match_gen extr auxtr ->
       (* c = trfirst extr -> *)
       δ = trfirst auxtr ->
       δ.(ls_fuel) !! ρ = Some f ->
       δ.(ls_mapping) !! ρ = Some τ ->
       (pred_at extr m (λ c _, ¬locale_prop (lift_grole τ) c) ∨ pred_at extr m (λ _ oζ, oζ = Some (Some (lift_grole τ)))) ->
      ∃ M, pred_at auxtr M (λ δ _, ¬role_enabled ρ δ)
           ∨ pred_at auxtr M (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0))).

  Local Lemma case1 ρ f m (extr': out_trace) (auxtr' : auxtrace (LM := LM)) δ ℓ :
    (∀ m0 : nat * nat,
         strict lt_lex m0 (f, m)
         → ∀ (f m: nat) (* (ζ: locale Λ) *) τ (extr : out_trace) (auxtr : auxtrace (LM := LM))
             (δ : LiveState G M), fairness_induction_stmt ρ m0 f m (* ζ *) τ extr auxtr δ ) ->
    (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) ->
    lm_exaux_traces_match_gen extr' auxtr' ->
    infinite_trace extr' ->
    ls_fuel δ !! ρ = Some f ->
    (∀ ζ, fair_by ζ extr') ->
    ∃ M0 : nat,
      pred_at (δ -[ ℓ ]-> auxtr') M0
              (λ δ0 _, ¬ role_enabled ρ δ0)
      ∨ pred_at (δ -[ ℓ ]-> auxtr') M0
                (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
    Proof.
      intros IH Hdec Hmatch Hinf Hsome Hfair.
      unfold oless in Hdec.
      simpl in *.
      rewrite -> Hsome in *.
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq.
      - destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
        { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. }
        have [τ' Hτ'] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.

        have Hloc'en: pred_at extr' 0 (λ (c : So) (_ : option (option Lo)),
                          locale_prop (lift_grole τ') c).
        { rewrite /pred_at /= pred_first_trace.
          eapply match_locale_prop; eauto. }

        have [p Hp] := (Hfair (lift_grole τ') 0 Hloc'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ (δ0 : LiveState G M) _, ¬ role_enabled ρ δ0)
                                  ∨ pred_at auxtr' M0 (λ (_ : LiveState G M) ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ p _ extr'); eauto.
          Unshelve. unfold strict, lt_lex. specialize (Hdec ltac:(by eapply elem_of_dom_2)).
          lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
      - exists 1. left. rewrite /pred_at /=. rewrite /role_enabled.
        destruct auxtr' =>/=.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
    Qed.

    Lemma others_step_fuel_decr ρ f τ
      δ ℓ auxtr' 
      c ζ' extr'
      (Htm: lm_exaux_traces_match_gen (c -[ ζ' ]-> extr') (δ -[ ℓ ]-> auxtr'))
      (Hfuel : ls_fuel δ !! ρ = Some f)
      (Hmapping : ls_mapping δ !! ρ = Some τ)
      (Hρlive: ρ ∈ live_roles M δ)
      (Hζ: Some (lift_grole τ) ≠ ζ'):
      ∃ f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f.
    Proof.
      inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
      (* red in Hl. *)
      destruct ζ' as [ζ'|]; last first; simpl in *.
      - simpl in *. destruct ℓ; try done. destruct Hls as [_ [_ [Hnoninc _]]].
        have HnotNone: Some ρ ≠ None by congruence.
        specialize (Hnoninc ρ ltac:(SS)).
        unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
        destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
        eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
        apply elem_of_dom_2 in Heq. set_solver.
      - destruct Hl as [τ' [-> Hl]]. 
        simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
        + destruct Hls as (?&?&?&Hnoninc&?).
          unfold fuel_must_not_incr in Hnoninc.
          have Hneq: Some ρ ≠ Some ρ0 by congruence.
          specialize (Hnoninc ρ ltac:(SS)).
          unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
          destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
          eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
          apply elem_of_dom_2 in Heq. set_solver.
        + destruct Hls as (?&?&Hnoninc&?).
          unfold fuel_must_not_incr in Hnoninc.
          have Hneq: Some ρ ≠ None by congruence.
          specialize (Hnoninc ρ ltac:(SS)).
          unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
          destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
          eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
          apply elem_of_dom_2 in Heq. set_solver.  
    Qed.
    
    Lemma owner_change_fuel_decr ρ f
      c τ extr'
      δ ℓ auxtr'
      ζ' τ''
      (Htm: lm_exaux_traces_match_gen (c -[ ζ' ]-> extr') (δ -[ ℓ ]-> auxtr'))
      (Hfuel: ls_fuel δ !! ρ = Some f)
      (Hmapping: ls_mapping δ !! ρ = Some τ)
      (Hρlive: ρ ∈ live_roles M δ)
      (Hρlive': ρ ∈ live_roles M (trfirst auxtr'))
      (Hζ'' : ls_mapping (trfirst auxtr') !! ρ = Some τ'')
      (Hchange : τ ≠ τ''):
      ∃ f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' < f.
    Proof.
      destruct ζ' as [ζ'|]; last first; simpl in *.
      - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        simpl in *. destruct ℓ; try done. destruct Hls as [_ [Hdec _]].
        unfold fuel_decr in Hdec.
        have Hmd: must_decrease ρ None δ (trfirst auxtr') None.
        { econstructor. congruence. rewrite Hζ''. eauto. }
        specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
        unfold oleq in Hdec. rewrite Hfuel in Hdec.
        destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done].
      - inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        simpl in *.
        destruct Hl as [τ' [-> Hl]]. 
        destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
        + destruct Hls as (?&?&Hdec&?&?).
          unfold fuel_decr in Hdec. simplify_eq.
          have Hmd: must_decrease ρ (Some ρ0) δ (trfirst auxtr') (Some ζ0).
          { econstructor 2. congruence. rewrite Hζ''; eauto. }
          specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
          unfold oleq in Hdec. rewrite Hfuel in Hdec.
          destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done].
        + destruct Hls as (?&Hdec&_).
          unfold fuel_decr in Hdec. simplify_eq.
          have Hmd: must_decrease ρ None δ (trfirst auxtr') (Some ζ0).
          { econstructor 2. congruence. rewrite Hζ''; eauto. }
          specialize (Hdec ρ ltac:(SS) ltac:(SS) Hmd).
          unfold oleq in Hdec. rewrite Hfuel in Hdec.
          destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [by eexists|done]. 
    Qed.

    Lemma fair_by_cons :
∀ (tid : Lo) (c : So) (tid' : option Lo) (r : out_trace),
  fair_by tid (c -[ tid' ]-> r) → fair_by tid r.
    Proof. Admitted. 



  Lemma fairness_preserved_ind ρ:
    ∀ fm f m τ (extr: out_trace) (auxtr: auxtrace (LM := LM)) δ,
      fairness_induction_stmt ρ fm f m τ extr auxtr δ.
  Proof.
    induction fm as [fm IH] using lex_ind.
    intros f m τ extr auxtr δ Hexinfin Hfair -> Htm -> Hfuel Hmapping Hexen.
    destruct extr as [|c ζ' extr'] eqn:Heq.
    { have [??] := Hexinfin 1. done. }
    have Hfair': (forall τ, fair_by τ extr').
    { intros. by eapply fair_by_cons. }
    destruct auxtr as [|δ ℓ auxtr']; first by inversion Htm.
    destruct (decide (ρ ∈ live_roles M δ)) as [Hρlive|]; last first.
    { exists 0. left. unfold pred_at. simpl. intros contra. eauto. }
    destruct (decide (Some (lift_grole τ) = ζ')) as [Hζ|Hζ].
    - rewrite <- Hζ in *.
      (* destruct (traces_match_labels _ _ _ _ _ _ Htm) as [[ρ' ->]| ->]; last first. *)
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
        intros Hinfuels. apply Hdec =>//. SS.

    - (* Another thread is taking a step. *)
      destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
      { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. }
      destruct m as [| m'].
      { rewrite -> !pred_at_0 in Hexen. destruct Hexen as [Hexen|Hexen].
        - exfalso. apply Hexen. eapply (match_locale_prop _ _ _ _ Htm); eauto. 
        - simplify_eq. }
      have [τ'' Hτ''] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.
      destruct (decide (τ = τ'')) as [<-|Hchange].
      + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f.
        { eapply others_step_fuel_decr; eauto. }

        unfold fair_by in *.
        have Hζ'en: pred_at extr' 0 (λ (c : So) _, locale_prop (lift_grole τ) c).
        { rewrite /pred_at /= pred_first_trace.
          eapply match_locale_prop; eauto. 
          by inversion Htm. }

        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0)
                        ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ m' _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.

      + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' < f.
        { eapply owner_change_fuel_decr; eauto. }

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
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0)
                        ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ p _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
  Qed.


  Lemma fair_by_after :
    ∀ (ζ : Lo) (tr tr' : out_trace) 
      (k : nat), after k tr = Some tr' → fair_by ζ tr → fair_by ζ tr'.
  Proof. Admitted.

  Theorem fairness_preserved (extr: out_trace) (auxtr: auxtrace (LM := LM)):
    infinite_trace extr ->
    lm_exaux_traces_match_gen extr auxtr ->
    (forall ζ, fair_by ζ extr) -> (forall ρ, fair_aux ρ auxtr (LM := LM)).
  Proof.
    intros Hinfin Hmatch Hex ρ n Hn.

    (* clear Hmatch.  *)
    
    unfold pred_at in Hn.
    destruct (after n auxtr) as [tr|] eqn:Heq.
    2: { done. } 
    setoid_rewrite pred_at_sum. rewrite Heq.
    have Hen: role_enabled ρ (trfirst tr) by destruct tr.

    have [τ Hτ] : is_Some((trfirst tr).(ls_mapping) !! ρ) by eauto.
    have [f Hfuel] : is_Some((trfirst tr).(ls_fuel) !! ρ) by eauto.
    have Hex' := Hex (lift_grole τ) n.
    have [tr1' [Heq' Htr]] : exists tr1', after n extr = Some tr1' ∧ lm_exaux_traces_match_gen tr1' tr
     by eapply traces_match_after.
    have Hte: locale_prop (lift_grole τ) (trfirst tr1').
    { eapply match_locale_prop.
      1, 2: eauto.
      apply Hen. }
    
    setoid_rewrite pred_at_sum in Hex'. rewrite Heq' in Hex'.
    have Hpa: pred_at extr n (λ c _, locale_prop (lift_grole τ) c).
    { unfold pred_at. rewrite Heq'. destruct tr1'; eauto. }
    destruct (Hex' Hpa) as [m Hm].
    have ?: infinite_trace tr1'.
    { have Hinf := infinite_trace_after n extr Hinfin. by rewrite Heq' in Hinf. }
    eapply (fairness_preserved_ind ρ _ f m τ _ tr); eauto.
    intros ?. by eapply fair_by_after.
  Qed.

End fairness_preserved.


(* TODO: move? *)
Section lang_fairness_preserved.
  Context `{LM: LiveModel (locale Λ) M}.
  Context `{Countable (locale Λ)}.

  Definition lm_exaux_traces_match :=
    lm_exaux_traces_match_gen
      (locale_step (Λ := Λ))
      (id: locale Λ -> locale Λ)
      (live_tids (LM := LM)). 

  Lemma match_locale_enabled_states_livetids
    ζ ρ δ c
    (Hloc: ls_mapping δ !! ρ = Some ζ)    
    (Hsr: live_tids c δ (LM := LM)):
    locale_enabled ζ c. 
  Proof. 
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
    intros.
    (* In case of language we don't require the role to be alive,
       since the notion of thread's "enabledness" is weaker than one of role *)
    clear H4.
    eapply match_locale_enabled_states_livetids; eauto.
    Unshelve. apply _.
  Qed.


End lang_fairness_preserved. 
