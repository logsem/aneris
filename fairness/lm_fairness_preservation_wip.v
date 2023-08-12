From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Export inftraces fairness fuel traces_match. 

(* TODO: some refactorings were made in original file *)
Section fairness_preserved.
  Context `{LM: LiveModel (locale Λ) M}.
  Context `{Countable (locale Λ)}.
  Notation "'Tid'" := (locale Λ).

  Context (state_rel: cfg Λ → lm_ls LM → Prop).
  Hypothesis (match_locale_enabled_states: 
               forall ζ ρ δ c,
                 ls_mapping δ !! ρ = Some ζ ->
                 state_rel c δ ->
                 locale_enabled ζ c). 

  Definition lm_exaux_traces_match: extrace Λ → auxtrace (LM := LM) → Prop :=
    traces_match 
      labels_match
      (* live_tids *) state_rel
      locale_step LM.(lm_ls_trans).

  Lemma exaux_preserves_validity extr (auxtr : auxtrace (LM := LM)):
    lm_exaux_traces_match extr auxtr ->
    auxtrace_valid auxtr (LM := LM).
  Proof.
    revert extr auxtr. cofix CH. intros extr auxtr Hmatch.
    inversion Hmatch; first by constructor.
    constructor =>//. by eapply CH.
  Qed.

  Lemma exaux_preserves_termination extr (auxtr : auxtrace (LM := LM)) :
    lm_exaux_traces_match extr auxtr ->
    terminating_trace auxtr ->
    terminating_trace extr.
  Proof.
    intros Hmatch [n HNone].
    revert extr auxtr Hmatch HNone. induction n as [|n IHn]; first done.
    intros extr auxtr Hmatch HNone.
    replace (S n) with (1 + n) in HNone =>//.
    rewrite (after_sum' _ 1) in HNone.
    destruct auxtr as [s| s ℓ auxtr'];
      first by inversion Hmatch; simplify_eq; exists 1.
    simpl in HNone.
    inversion Hmatch; simplify_eq.
    apply terminating_trace_cons.
    eapply IHn =>//.
  Qed.

  Lemma traces_match_labels tid ℓ c δ rex (raux : auxtrace (LM := LM)) :
    lm_exaux_traces_match (c -[Some tid]-> rex) (δ -[ℓ]-> raux) ->
    ((∃ ρ, ℓ = Take_step ρ tid) ∨ (ℓ = Silent_step tid)).
  Proof.
    intros Hm. inversion Hm as [|?????? Hlab]; simplify_eq.
    destruct ℓ; eauto; inversion Hlab; simplify_eq; eauto.
  Qed.

  Lemma mapping_live_role (δ: LiveState Tid M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_mapping (G := Tid) δ !! ρ).
  Proof. rewrite -elem_of_dom ls_same_doms. SS. Qed.
  Lemma fuel_live_role (δ: LiveState Tid M) ρ:
    ρ ∈ M.(live_roles) δ ->
    is_Some (ls_fuel (G := Tid) δ !! ρ).
  Proof. rewrite -elem_of_dom. SS. Qed.

  Local Hint Resolve mapping_live_role: core.
  Local Hint Resolve fuel_live_role: core.

  Lemma match_locale_enabled (extr : extrace Λ) (auxtr : auxtrace (LM := LM)) ζ ρ:
    lm_exaux_traces_match extr auxtr ->
    ls_mapping (trfirst auxtr) !! ρ = Some ζ ->
    locale_enabled ζ (trfirst extr).
  Proof.
    intros Hm Hloc.
    eapply match_locale_enabled_states; eauto.
    eapply traces_match_first; eauto.  
  Qed. 
  
  Local Hint Resolve match_locale_enabled: core.
  Local Hint Resolve pred_first_trace: core.

  Definition fairness_induction_stmt ρ fm f m ζ extr (auxtr : auxtrace (LM := LM))
    δ
    (* c *)
    :=
      (infinite_trace extr ->
       (forall ζ, fair_ex ζ extr) ->
       fm = (f, m) ->
       lm_exaux_traces_match extr auxtr ->
       (* c = trfirst extr -> *)
       δ = trfirst auxtr ->
       δ.(ls_fuel) !! ρ = Some f ->
       δ.(ls_mapping) !! ρ = Some ζ ->
       (pred_at extr m (λ c _, ¬locale_enabled ζ c) ∨ pred_at extr m (λ _ oζ, oζ = Some (Some ζ))) ->
      ∃ M, pred_at auxtr M (λ δ _, ¬role_enabled ρ δ)
           ∨ pred_at auxtr M (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0))).

  Local Lemma case1 ρ f m (extr' : extrace Λ) (auxtr' : auxtrace (LM := LM)) δ ℓ :
    (∀ m0 : nat * nat,
         strict lt_lex m0 (f, m)
         → ∀ (f m: nat) (ζ: locale Λ) (extr : extrace Λ) (auxtr : auxtrace (LM := LM))
             (δ : LiveState Tid M) (* (c : cfg Λ) *), fairness_induction_stmt ρ m0 f m ζ extr auxtr δ (* c *)) ->
    (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) ->
    lm_exaux_traces_match extr' auxtr' ->
    infinite_trace extr' ->
    ls_fuel δ !! ρ = Some f ->
    (∀ ζ, fair_ex ζ extr') ->
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
        have [ζ' Hζ'] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.

        have Hloc'en: pred_at extr' 0 (λ (c : cfg Λ) (_ : option (olocale Λ)),
                          locale_enabled ζ' c).
        { rewrite /pred_at /= pred_first_trace. eauto. }

        have [p Hp] := (Hfair ζ' 0 Hloc'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ (δ0 : LiveState Tid M) _, ¬ role_enabled ρ δ0)
                                  ∨ pred_at auxtr' M0 (λ (_ : LiveState Tid M) ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ p _ extr'); eauto.
          Unshelve. unfold strict, lt_lex. specialize (Hdec ltac:(by eapply elem_of_dom_2)).
          lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
      - exists 1. left. rewrite /pred_at /=. rewrite /role_enabled.
        destruct auxtr' =>/=.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
        + apply not_elem_of_dom in Heq; eapply not_elem_of_weaken; last (by apply ls_fuel_dom); set_solver.
    Qed.

    Lemma others_step_fuel_decr ρ f ζ
      δ ℓ auxtr' 
      c ζ' extr'
      (Htm: lm_exaux_traces_match (c -[ ζ' ]-> extr') (δ -[ ℓ ]-> auxtr'))
      (Hfuel : ls_fuel δ !! ρ = Some f)
      (Hmapping : ls_mapping δ !! ρ = Some ζ)
      (Hρlive: ρ ∈ live_roles M δ)
      (Hζ: Some ζ ≠ ζ'):
      ∃ f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f.
    Proof.
      inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq. 
      destruct ζ' as [ζ'|]; last first; simpl in *.
      - simpl in *. destruct ℓ; try done. destruct Hls as [_ [_ [Hnoninc _]]].
        have HnotNone: Some ρ ≠ None by congruence.
        specialize (Hnoninc ρ ltac:(SS)).
        unfold oleq in Hnoninc. rewrite Hfuel in Hnoninc.
        destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'|] eqn:Heq; [|set_solver].
        eexists; split =>//. destruct Hnoninc as [Hnoninc|Hnoninc]=>//.
        apply elem_of_dom_2 in Heq. set_solver.
      - simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
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
      c ζ extr'
      δ ℓ auxtr'
      ζ' ζ''
      (Htm: lm_exaux_traces_match (c -[ ζ' ]-> extr') (δ -[ ℓ ]-> auxtr'))
      (Hfuel: ls_fuel δ !! ρ = Some f)
      (Hmapping: ls_mapping δ !! ρ = Some ζ)
      (Hρlive: ρ ∈ live_roles M δ)
      (Hρlive': ρ ∈ live_roles M (trfirst auxtr'))
      (Hζ'' : ls_mapping (trfirst auxtr') !! ρ = Some ζ'')
      (Hchange : ζ ≠ ζ''):
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
        simpl in *. destruct ℓ as [ρ0 ζ0| ζ0|]; try done.
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


  Lemma fairness_preserved_ind ρ:
    ∀ fm f m ζ (extr: extrace Λ) (auxtr: auxtrace (LM := LM)) δ (* c *),
      fairness_induction_stmt ρ fm f m ζ extr auxtr δ (* c *).
  Proof.
    induction fm as [fm IH] using lex_ind.
    intros f m ζ extr auxtr δ (* c *) Hexinfin Hfair -> Htm (* -> *) -> Hfuel Hmapping Hexen.
    destruct extr as [|c ζ' extr'] eqn:Heq.
    { have [??] := Hexinfin 1. done. }
    have Hfair': (forall ζ, fair_ex ζ extr').
    { intros. by eapply fair_ex_cons. }
    destruct auxtr as [|δ ℓ auxtr']; first by inversion Htm.
    destruct (decide (ρ ∈ live_roles M δ)) as [Hρlive|]; last first.
    { exists 0. left. unfold pred_at. simpl. intros contra. eauto. }
    destruct (decide (Some ζ = ζ')) as [Hζ|Hζ].
    - rewrite <- Hζ in *.

      (* clear IH.  *)      
      
      destruct (traces_match_labels _ _ _ _ _ _ Htm) as [[ρ' ->]| ->]; last first.
      + inversion Htm as [|s1 ℓ1 r1 s2 ℓ2 r2 Hl Hs Hts Hls Hmatchrest]; simplify_eq.
        unfold ls_trans in Hls. simpl in Hls. 
        destruct Hls as (? & Hlsdec & Hlsincr).
        unfold fuel_decr in Hlsdec.
        have Hmustdec: must_decrease ρ None δ (trfirst auxtr') (Some ζ).
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
        have Hmustdec: must_decrease ρ (Some ρ') δ (trfirst auxtr') (Some ζ).
        { constructor; eauto; congruence. }
        (* Copy and paste begins here *)
        eapply case1 =>//; last by eauto using infinite_cons.
        intros Hinfuels. apply Hdec =>//. SS.

    - (* Another thread is taking a step. *)
      destruct (decide (ρ ∈ live_roles M (trfirst auxtr'))) as [Hρlive'|]; last first.
      { exists 1. left. unfold pred_at. simpl. destruct auxtr'; eauto. }
      destruct m as [| m'].
      { rewrite -> !pred_at_0 in Hexen. destruct Hexen as [Hexen|Hexen].
        - exfalso. apply Hexen. unfold locale_enabled. by eapply (match_locale_enabled _ _ _ _ Htm).
        - simplify_eq. }
      have [ζ'' Hζ''] : is_Some (ls_mapping (trfirst auxtr') !! ρ) by eauto.
      destruct (decide (ζ = ζ'')) as [<-|Hchange].
      + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' ≤ f.
        { eapply others_step_fuel_decr; eauto. }

        unfold fair_ex in *.
        have Hζ'en: pred_at extr' 0 (λ (c : cfg Λ) _, locale_enabled ζ c).
        { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }

        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0)
                        ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ m' _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.

      + have [f' [Hfuel' Hff']] : exists f', ls_fuel (trfirst auxtr') !! ρ = Some f' ∧ f' < f.
        { eapply owner_change_fuel_decr; eauto. }

        unfold fair_ex in *.
        have: pred_at extr' 0 (λ c _, locale_enabled ζ'' c).
        { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }
        have Hζ'en: pred_at extr' 0 (λ c _, locale_enabled ζ'' c).
        { rewrite /pred_at /= pred_first_trace. inversion Htm; eauto. }
        have [p Hp] := (Hfair' ζ'' 0 Hζ'en).
        have [P Hind] : ∃ M0 : nat, pred_at auxtr' M0 (λ δ0 _, ¬ role_enabled ρ δ0)
                        ∨ pred_at auxtr' M0 (λ _ ℓ, ∃ ζ0, ℓ = Some (Take_step ρ ζ0)).
        { eapply (IH _ _ _ p _ extr'); eauto. by eapply infinite_cons. by inversion Htm.
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). rewrite !pred_at_sum. simpl. done.
  Qed.

  Theorem fairness_preserved (extr: extrace Λ) (auxtr: auxtrace (LM := LM)):
    infinite_trace extr ->
    lm_exaux_traces_match extr auxtr ->
    (forall ζ, fair_ex ζ extr) -> (forall ρ, fair_aux ρ auxtr (LM := LM)).
  Proof.
    intros Hinfin Hmatch Hex ρ n Hn.

    (* clear Hmatch.  *)
    
    unfold pred_at in Hn.
    destruct (after n auxtr) as [tr|] eqn:Heq.
    2: { done. } 
    setoid_rewrite pred_at_sum. rewrite Heq.
    have Hen: role_enabled ρ (trfirst tr) by destruct tr.

    have [ζ Hζ] : is_Some((trfirst tr).(ls_mapping) !! ρ) by eauto.
    have [f Hfuel] : is_Some((trfirst tr).(ls_fuel) !! ρ) by eauto.
    have Hex' := Hex ζ n.
    have [tr1' [Heq' Htr]] : exists tr1', after n extr = Some tr1' ∧ lm_exaux_traces_match tr1' tr
     by eapply traces_match_after.
    have Hte: locale_enabled ζ (trfirst tr1').
    { eapply match_locale_enabled; eauto. }
    
    setoid_rewrite pred_at_sum in Hex'. rewrite Heq' in Hex'.
    have Hpa: pred_at extr n (λ c _, locale_enabled ζ c).
    { unfold pred_at. rewrite Heq'. destruct tr1'; eauto. }
    destruct (Hex' Hpa) as [m Hm].
    have ?: infinite_trace tr1'.
    { have Hinf := infinite_trace_after n extr Hinfin. by rewrite Heq' in Hinf. }
    eapply (fairness_preserved_ind ρ _ f m ζ _ tr); eauto.
    intros ?. by eapply fair_ex_after.
  Qed.

  (* Tactic Notation "inv" open_constr(P) := match goal with *)
  (*               | [H: P |- _] => inversion H; clear H; simplify_eq *)
  (*                                         end. *)

End fairness_preserved.

(* TODO: move? *)
Lemma match_locale_enabled_states_livetids `{Countable (locale Λ)} `{LM: LiveModel (locale Λ) M}
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

