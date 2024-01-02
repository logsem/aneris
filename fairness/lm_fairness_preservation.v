From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.program_logic Require Export adequacy.
From trillium.fairness Require Import inftraces fairness fuel traces_match trace_utils lm_fair_traces lm_fair trace_helpers trace_lookup trace_lookup utils trace_len.


Section fairness_preserved.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {LF: LMFairPre LM}. 

  (* Context `{EqDecision G}. *)
  (* Context {LF: LMFairPre LM}.  *)

  (* Context (GLM: Model). *)
  (* Let St := mstate GLM. *)
  (* Let L := mlabel GLM. *)
  Let LS := lm_ls LM. 
  (* Variable (A: Type). *)
  (* Variable (transA: LS -> A -> LS -> Prop).  *)

  Class AlmostLM {A: Type} (transA: LS -> A -> LS -> Prop) := {
      am_lift_G: G -> A; 
      am_lift_LM_step: forall δ1 δ2 g, transA δ1 (am_lift_G g) δ2 -> 
                                   locale_trans δ1 g δ2 (LM := LM);
      am_transA_keep_asg: forall δ1 a δ2 ρ τ f, 
                 transA δ1 a δ2 -> 
                 (forall g, am_lift_G g ≠ a) ->
                 ls_mapping δ1 !! ρ = Some τ ->
                 ls_fuel δ1 !! ρ = Some f ->
                 ls_mapping δ2 !! ρ = Some τ /\ ls_fuel δ2 !! ρ = Some f;
      am_lift_G_dec': forall a, {g | am_lift_G g = a} + (forall g, am_lift_G g ≠ a);
      am_lift_inj :> Inj eq eq am_lift_G;
  }.

  Global Instance am_lift_G_dec `{ALM: AlmostLM transA}:
    forall a, Decision (exists g, am_lift_G g = a).
  Proof. 
    intros a. destruct (am_lift_G_dec' a) as [[g ?]| ]. 
    - left. eauto.
    - right. set_solver.
  Qed. 

  Context `(AM: AlmostLM). 
  
  Definition atrace := trace LS A.

  Lemma am_transA_keep_fuel: forall δ1 a δ2 ρ f, 
      transA δ1 a δ2 -> 
      (forall g, am_lift_G g ≠ a) ->
      ls_fuel δ1 !! ρ = Some f ->
      ls_fuel δ2 !! ρ = Some f.
  Proof. 
    intros ????? TRANS NOa FUEL.
    pose proof FUEL as [??]%mk_is_Some%ls_same_doms'.
    eapply am_transA_keep_asg; eauto. 
  Qed.

  Lemma am_transA_keep_mapping: forall δ1 a δ2 ρ g, 
      transA δ1 a δ2 -> 
      (forall g, am_lift_G g ≠ a) ->
      ls_mapping δ1 !! ρ = Some g ->
      ls_mapping δ2 !! ρ = Some g.
  Proof. 
    intros ????? TRANS NOa MAP.
    pose proof MAP as [??]%mk_is_Some%ls_same_doms'.
    eapply am_transA_keep_asg; eauto. 
  Qed.

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
  Definition group_step_or_dis (τ: G) (δ: LiveState G M LSI) (ol: option A) :=
    fairness_sat (λ τ δ, exists ρ, ls_mapping δ !! ρ = Some τ) 
      (fun t l' => am_lift_G t = l') τ δ ol.

  Definition fair_by_group: G -> atrace -> Prop := 
    fair_by (λ τ δ, exists ρ, ls_mapping δ !! ρ = Some τ)
      (fun t l' => am_lift_G t = l').

  Definition astep_by_next_TS ρ δ1 ostep :=
    ∃ (l : A) (δ2 : LS) (τ: G),
      ostep = Some (l, δ2) ∧ am_lift_G τ = l /\
      next_TS_role δ1 τ δ2 = Some ρ. 
  
  Definition steps_or_unassigned :=
    fairness_sat_gen (λ ρ δ, ρ ∈ dom (ls_mapping δ))
                     astep_by_next_TS. 

  Definition fair_aux_SoU: fmrole M -> atrace -> Prop := 
    fair_by_gen (λ ρ δ, ρ ∈ dom (ls_mapping δ))
      astep_by_next_TS. 

  Global Instance astep_Dec: forall ρ δ1 ostep, Decision (astep_by_next_TS ρ δ1 ostep).
  Proof. 
    intros ?? ostep. rewrite /astep_by_next_TS.
    destruct ostep as [[??]| ].
    2: { right. set_solver. }    
    eapply Decision_iff_impl.
    { rewrite ex_det_iff; [rewrite ex_det_iff| ].
      - reflexivity. 
      - intros ? (?& [=] & ?). subst. reflexivity.
      - intros ? (?&?& [=] & ?). subst. reflexivity. }
    destruct (am_lift_G_dec' a) as [[g ?]| ]; subst. 
    2: { right. set_solver. }
    destruct (decide (next_TS_role δ1 g l = Some ρ)).
    { left. eauto. }
    right. set_solver. 
  Qed.    

  Definition fairness_induction_stmt ρ fm f m τ (* extr *) (auxtr : atrace) δ
    :=
    (* infinite_trace auxtr -> *)
    (forall τ, fair_by_group τ auxtr) ->
    fm = (f, m) ->
    δ = trfirst auxtr ->
    δ.(ls_fuel) !! ρ = Some f ->
    (ls_mapping δ) !! ρ = Some τ ->
    pred_at auxtr m (fun δ oℓ => group_step_or_dis τ δ oℓ)
    ->
    (* ∃ M, pred_at auxtr M (fun δ ℓ => steps_or_unassigned ρ δ ℓ)).  *)
    exists i δi ostep, auxtr !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep.
  
  Local Lemma case1 ρ f m (auxtr' : atrace) δ ℓ :
    (∀ m0 : nat * nat,
         strict lt_lex m0 (f, m)
         → ∀ (f m: nat) τ (auxtr : atrace)
             (δ : LiveState G M LSI),
          trace_valid transA auxtr -> fairness_induction_stmt ρ m0 f m τ (* extr *) auxtr δ ) ->
    (ρ ∈ dom (ls_fuel (trfirst auxtr')) → oless (ls_fuel (trfirst auxtr') !! ρ) (ls_fuel δ !! ρ)) ->
    trace_valid transA auxtr' ->
    (* infinite_trace auxtr' -> *)
    ls_fuel δ !! ρ = Some f ->
    (forall τ, fair_by_group τ auxtr' ) ->
    ∃ i δi ostep, (δ -[ ℓ ]-> auxtr') !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep.
  Proof.
    intros IH Hdec (* Hmatch *) Hvalid
      (* Hinf *)
      Hsome Hfair.
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
        (* rewrite Heq in Hdec. *)
        lia. } 
      exists (1+i). eauto. 
    - pose proof (trace_lookup_0 auxtr') as (?&?).
      exists 1. do 2 eexists. rewrite trace_lookup_cons. split; eauto. 
      rewrite /steps_or_unassigned. left.
      apply not_elem_of_dom in Heq. by rewrite -ls_same_doms in Heq. 
  Qed.    

  (* TODO: move *)
  Lemma label_lookup_singleton {St L: Type} (s: St) i:
    (⟨ s ⟩: trace St L) L!! i = None.
  Proof.
    (* pose proof trace_len_singleton *)
    simpl. destruct (⟨ s ⟩ L!! i) eqn:ITH; [| done].
    eapply mk_is_Some, label_lookup_dom in ITH.
    2: { apply trace_len_singleton. }
    simpl in ITH. lia.
  Qed. 

  Lemma fairness_preserved_ind ρ:
    ∀ fm f m τ (auxtr: atrace) δ,
      trace_valid transA auxtr -> 
      fairness_induction_stmt ρ fm f m τ auxtr δ.
  Proof.    
    induction fm as [fm IH] using lex_ind.
    intros f m τ auxtr δ VALID
      (* Hexinfin *)
      Hfair -> Htm Hfuel Hmapping Hexen.
    destruct auxtr as [|δ_ ℓ auxtr'] eqn:Heq.
    { apply pred_at_trace_lookup in Hexen as (st & TR0 & EN).
      destruct m; [| done].
      rewrite state_lookup_0 in TR0. inversion TR0. simpl in *. subst.
      rewrite label_lookup_singleton in EN.
      do 2 red in EN. destruct EN as [UNMAP| ]; [| set_solver].
      exists 0. do 2 eexists. split; [apply trace_lookup_0_singleton| ]. 
      left. intros ?%elem_of_dom. edestruct UNMAP; eauto. }
    have Hfair': (forall τ, fair_by_group τ auxtr'). 
    { intros. eapply fair_by_cons; eauto. apply Hfair. }
    simpl in *. subst δ_. 
    (* destruct (decide (lm_lbl_matches_group ℓ τ)) as [Hζ|Hζ]. *)
    pose proof (trace_valid_cons_inv _ _ _ _ VALID) as [_ Hls].
    
    assert (am_lift_G τ ≠ ℓ ->
            (forall f', ls_fuel (trfirst auxtr') !! ρ = Some f' -> f' <= f) ->
            (forall f' τ', ls_fuel (trfirst auxtr') !! ρ = Some f' -> ls_mapping (trfirst auxtr') !! ρ = Some τ' -> τ' ≠ τ -> f' < f) ->
            ∃ (i : nat) (δi : LiveState G M LSI) (ostep : option (A * LiveState G M LSI)),
    (δ -[ ℓ ]-> auxtr') !! i = Some (δi, ostep) ∧ steps_or_unassigned ρ δi ostep)
      as OTHER_HELPER.
    { intros NEQ FUEL_LE FUEL_LT.
      destruct (decide (exists τ, ls_mapping (trfirst auxtr') !! ρ = Some τ)) as [MAP| ]; last first.
      { exists 1. pose proof (trace_lookup_0 auxtr') as (?&?).
        do 2 eexists. rewrite trace_lookup_cons. split; eauto.
        left. by intros ?%elem_of_dom. }
      destruct m as [| m'].
      { rewrite -> !pred_at_0 in Hexen.
        red in Hexen. destruct Hexen as [Hexen|Hexen].
        - exfalso. set_solver.
        - destruct Hexen as (?&?&?). set_solver. }
      destruct MAP as [τ'' Hτ''].
      destruct (ls_fuel (trfirst auxtr') !! ρ) as [f'| ] eqn:Hfuel'.
      2: { apply elem_of_dom_2 in Hτ''. apply not_elem_of_dom_2 in Hfuel'.
           rewrite ls_same_doms in Hτ''. done. }
      destruct (decide (τ = τ'')) as [<-|Hchange].
      - specialize (FUEL_LE _ eq_refl). 
        assert (exists i δi ostep, auxtr' !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep) as (P&?&?&Hind).
        { eapply (IH _ _ _ m' _); eauto.
          eapply trace_valid_cons_inv; eauto.
          (* - by eapply infinite_cons. *)
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). eauto.
      - apply not_eq_sym in Hchange. specialize (FUEL_LT _ _ eq_refl Hτ'' Hchange). 
        unfold fair_by in *.
        pose proof (Hfair' τ'' 0) as [p Hp].
        { rewrite pred_at_state_trfirst. eauto. }        
        assert (exists i δi ostep, auxtr' !! i = Some (δi, ostep) /\ steps_or_unassigned ρ δi ostep) as (P&?&?&Hind).
        { eapply (IH _ _ _ p _); eauto.
          eapply trace_valid_cons_inv; eauto.
          (* - by eapply infinite_cons. *)
          Unshelve. unfold strict, lt_lex. lia. }
        exists (1+P). eauto. } 

    
    (* destruct (proj_G ℓ) as [g| ] eqn:PROJ. *)
    destruct (decide (exists g, am_lift_G g = ℓ)) as [[g LIFTg]| ]. 
    { 

    (* destruct (decide (ℓ = Some τ)) as [Hζ|Hζ].  *)
    destruct (decide (g = τ)) as [Hζ|Hζ]. 
    - subst.
      (* pose proof (mtrace_valid_steps' VALID 0) as Hls.  *)
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
          right. red. do 3 eexists. repeat split; eauto. }
        destruct Hls as (?&Hsame&Hdec&Hnotinc&_).
        rewrite -Hsame /= in Hmapping.
        have Hmustdec: must_decrease ρ (Some f0) δ (trfirst auxtr') (Some τ).
        { constructor; eauto; congruence. }
        (* Copy and paste begins here *)
        eapply case1 =>//. 
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
        (* * eapply infinite_cons =>//. *)
        * eapply am_lift_LM_step; eauto.   
    - subst. eapply am_lift_LM_step in Hls as (?&?&?); eauto.
      eapply OTHER_HELPER.
      + intros ?. apply Hζ. eapply am_lift_inj; eauto.
      + intros. eapply others_step_fuel_decr; eauto.
        destruct x; simpl in *; congruence. 
      + intros. eapply owner_change_fuel_decr; eauto. }

    eapply OTHER_HELPER; eauto.
    - intros. eapply am_transA_keep_asg in Hmapping as (?&?); eauto.
      rewrite H0 in H2. inversion H2. lia.
    - intros. eapply am_transA_keep_asg in Hfuel as (?&?); eauto.
      congruence.     
  Qed.
  
  Lemma group_fairness_implies_step_or_unassign
    (auxtr: atrace):
    (* infinite_trace auxtr -> *)
    trace_valid transA auxtr ->
    (forall τ, fair_by_group τ auxtr) ->
    forall ρ, fair_aux_SoU ρ auxtr.
  Proof.
    intros Hmatch Hex ρ.
    red. intros n DOMn.
    unfold pred_at in DOMn.
    destruct (after n auxtr) as [tr|] eqn:Heq; rewrite Heq in DOMn.
    2: { done. } 
    (* setoid_rewrite pred_at_sum. rewrite Heq. *)
    setoid_rewrite <- trace_lookup_after; eauto.  

    have [τ Hτ] : is_Some((ls_mapping (trfirst tr)) !! ρ).
    { destruct tr; apply elem_of_dom; eauto. }
    clear DOMn.
    have [f Hfuel] : is_Some((trfirst tr).(ls_fuel) !! ρ).
    { apply elem_of_dom. rewrite -ls_same_doms. eapply elem_of_dom; eauto. }
    have Hex' := Hex τ n.

    setoid_rewrite pred_at_sum in Hex'.
    destruct Hex' as [m Hm].
    { red. rewrite Heq. destruct tr; eauto. }

    rewrite Heq in Hm.
    (* have ?: infinite_trace tr. *)
    (* { have Hinf := infinite_trace_after n auxtr Hinfin. by rewrite Heq in Hinf. } *)
    eapply (fairness_preserved_ind ρ _ f m τ _); eauto.
    - eapply trace_valid_after; eauto. 
    - intros. eapply fair_by_after; eauto. apply Hex. 
  Qed.

  Definition afair_by_next_TS: fmrole M -> atrace -> Prop :=
    (* fair_by_gen role_enabled step_by_next_TS.  *)
    fair_by_gen role_enabled astep_by_next_TS. 
 
  Lemma steps_or_unassigned_implies_aux_fairness (auxtr: atrace):
    (forall ρ, fair_aux_SoU ρ auxtr) -> (forall ρ, afair_by_next_TS ρ auxtr).
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
      by apply H0, elem_of_dom.
    - by right.
  Qed.

  Lemma group_fairness_implies_role_fairness (auxtr: atrace):
    (* infinite_trace auxtr -> *)
    trace_valid transA auxtr ->
    (forall τ, fair_by_group τ auxtr) ->
    (forall ρ, afair_by_next_TS ρ auxtr).
  Proof. 
    intros. auto using steps_or_unassigned_implies_aux_fairness, 
      group_fairness_implies_step_or_unassign.
  Qed. 
    
  Section Preservation.
    Context {So Lo: Type}.
    Context `{EqDecision Lo}. 
    
    Let out_trace := trace So (Lo).
    
    (* counterpart of locale step.
       TODO: any restrictions? *)
    (* Context (out_step: So -> option Lo -> So -> Prop).  *)
    Context (out_step: So -> Lo -> So -> Prop).
    
    (* Representation of "almost LM" model labels on outer level *)
    Context (lift_A: A -> Lo).
    Hypothesis (INJlg: Inj eq eq lift_A). 
    
    Context (locale_prop: Lo -> So -> Prop).
    
    (* Context (state_rel: cfg Λ → lm_ls LM → Prop). *)
    Context (state_rel: So → lm_ls LM → Prop).
    
    Definition lm_live_lift δ := forall g (ρ: fmrole M) c,
        ls_mapping δ !! ρ = Some g ->
        (* ρ ∈ live_roles _ δ ->  *)
        state_rel c δ ->
        (* locale_enabled ζ c *)
        locale_prop (lift_A (am_lift_G g)) c.     
    
    (* Hypothesis (match_locale_prop_states: lm_live_lift). *)
    
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
    
    (* Definition out_A_labels_match (oζ : option Lo) (a: A) := *)
    Definition out_A_labels_match (ζ : Lo) (a: A) :=
      (* match oζ with *)
      (* | Some ζ => lift_A a = ζ *)
      (* | None => False *)
      (* end.  *)
      lift_A a = ζ. 
    
    (* TODO: rename *)
    Definition lm_exaux_traces_match_gen: out_trace → atrace → Prop :=
      traces_match 
        (* labels_match *) out_A_labels_match
        (* live_tids *) state_rel
        (* locale_step  *) out_step
        (* (fmtrans LM_Fair).  *) transA. 
        
    Let lbl_match (ℓ: Lo) oℓ' := oℓ' = ℓ. 
    
    Theorem fairness_preserved (extr: out_trace) (auxtr: atrace):
      (* infinite_trace extr -> *)
      lm_exaux_traces_match_gen extr auxtr ->
      (forall δ i, auxtr S!! i = Some δ -> lm_live_lift δ) ->
      (forall ζ, fair_by locale_prop lbl_match ζ extr) -> (forall τ, fair_by_group τ auxtr).
    Proof.
      intros MATCH LIFT FAIR_OUT.
      intros. do 2 red. intros n ASG.
      pose proof ASG as (δ & NTH & [ρ MAP])%pred_at_trace_lookup.
      
      edestruct @traces_match_state_lookup_2 as (c & ENTH & RELn); eauto.
      
      red in FAIR_OUT. edestruct FAIR_OUT as [m STEP].
      { specialize (LIFT _ _ NTH). 
        eapply pred_at_trace_lookup; eauto. }
      apply pred_at_or in STEP.
      
      apply pred_at_or in STEP. 
      apply pred_at_trace_lookup in STEP as (c' & ENTH' & STEP).
      edestruct @traces_match_state_lookup_1 as (δ' & NTH' & RELn'); eauto. 
      exists m. apply pred_at_trace_lookup. eexists. split; eauto.
      red. destruct STEP as [EMP | STEP]. 
      - left. intros [??]. apply EMP.
        eapply LIFT; eauto.  
      - right.
        destruct STEP as (?&?&LBLM). 
        edestruct @traces_match_label_lookup_1 as (ℓ & NTH'l & LBL); eauto.
        eexists. split; eauto. red in LBL.
        red in LBLM. subst.
        eapply INJlg; eauto. 
    Qed.
    
  End Preservation.

End fairness_preserved.


Instance LM_ALM `{Countable G} `(LM: LiveModel G M LSI): AlmostLM olocale_trans (LM := LM).
Proof. 
  refine {| am_lift_G := Some |}; eauto. 
  - intros ?????? STEP NEQ **.
    destruct a; [| done]. 
    by destruct (NEQ g).
  - intros [a| ].
    + left. eauto.
    + right. congruence. 
Defined.

Lemma LM_ALM_afair_by_next `{Countable G} `(LM: LiveModel G M LSI) {LF: LMFairPre LM} auxtr:
  (∀ ρ, afair_by_next_TS (LM_ALM LM) ρ auxtr) <-> ∀ ρ, fair_by_next_TS ρ auxtr.
Proof.
  apply forall_proper. intros.
  apply fair_by_gen_Proper; try reflexivity.
  red. intros ??->. intros ??->. intros ??->.
  rewrite /step_by_next_TS /astep_by_next_TS. simpl.
  split.
  - intros (?&?&?&->&<-&<-). eauto.
  - intros (?&?&->&?). do 3 eexists. eauto. 
Qed. 

(* Lemma traces_match_LM_preserves_validity `{LM: LiveModel G M LSI} {LF: LMFairPre LM} *)
(*   `{C: Type} {L: Type} *)
(*   (otr: trace C L) (auxtr : lmftrace (LM := LM)) *)
(*   state_rel lbl_rel outer_step : *)
(*   traces_match lbl_rel state_rel outer_step ((fmtrans LM_Fair)) otr auxtr -> *)
(*   mtrace_valid auxtr. *)
(* Proof. *)
(*   revert otr auxtr. pcofix CH. intros otr auxtr Hmatch. *)
(*   pfold.  *)
(*   inversion Hmatch; [by econstructor| ]. *)
(*   constructor =>//. *)
(*   specialize (CH _ _ H3). *)
(*   eauto.    *)
(* Qed. *)

Section lang_fairness_preserved.
  Context `{Countable (locale Λ)}.
  Context `{LM: LiveModel (locale Λ) M LSI}.
  Context {LF: LMFairPre LM}.

  Let ALM := LM_ALM LM.

  Definition lm_exaux_traces_match :=
    lm_exaux_traces_match_gen
      (transA := olocale_trans)
      (locale_step (Λ := Λ))
      id
      (live_tids (LM := LM)).  

  Lemma match_locale_enabled_states_livetids: 
    forall δ, lm_live_lift ALM id
      (* locale_enabled *) (from_option locale_enabled (fun _ => False))
      live_tids δ (LM := LM).
  Proof.
    red. intros δ ζ ρ c Hloc Hsr. 
    rewrite /locale_enabled.
    destruct Hsr as [HiS Hneqloc].
    have [e Hein] := (HiS _ _ Hloc). exists e. split; first done.
    destruct (to_val e) eqn:Heqe =>//.
    exfalso. specialize (Hneqloc ζ e Hein). rewrite Heqe in Hneqloc.
    have Hv: Some v ≠ None by []. by specialize (Hneqloc Hv ρ).
  Qed.

  Theorem ex_fairness_preserved (extr: extrace Λ) (auxtr: atrace (LM := LM)):
    (* infinite_trace extr -> *)
    lm_exaux_traces_match extr auxtr ->
    (forall ζ, fair_ex ζ extr) -> (∀ ρ : fmrole M, afair_by_next_TS ALM ρ auxtr).
  Proof.
    intros. eapply group_fairness_implies_role_fairness; eauto. 
    (* { eapply traces_match_infinite_trace; eauto. } *)
    { eapply traces_match_valid2; eauto. }
    eapply fairness_preserved; eauto.
    { apply _. }
    { intros. eapply match_locale_enabled_states_livetids; eauto. }
    simpl. intros. destruct ζ as [ζ| ].
    { apply H1. }
    red. simpl in *. by intros ?(?&?&?)%pred_at_trace_lookup.
  Qed.

End lang_fairness_preserved. 


Section model_fairness_preserved.
  Context `{CNT: Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {A} {transA} {ALM: AlmostLM transA (LM := LM) (A := A)}. 
  Context {LF: LMFairPre LM}. 

  Context `{Mout: FairModel}. 

  Context (lift_A: A -> option $ fmrole Mout).
  Hypothesis (INJlg: Inj eq eq lift_A). 

  Context (state_rel: fmstate Mout → lm_ls LM → Prop).

  Context (fairness_cond: fmrole Mout → fmstate Mout → Prop). 

  (* Hypothesis (match_labels_prop_states:  *)
  (*              lm_live_lift ALM lift_A *)
  (*                (* role_enabled_model *) *)
  (*                (from_option fairness_cond (fun _ => False)) *)
  (*                state_rel). *)
  Definition match_labels_prop_states :=
    lm_live_lift ALM lift_A
      (* role_enabled_model *)
      (from_option fairness_cond (fun _ => False))
      state_rel.
    

  Definition lm_model_traces_match :=
    lm_exaux_traces_match_gen
      (transA := transA)
      (fmtrans Mout)
      (lift_A)
      state_rel. 
  
  Lemma model_fairness_preserved' (mtr: mtrace Mout) (auxtr: atrace (LM := LM))
    (* (INF: infinite_trace mtr) *)
    (MATCH: lm_model_traces_match mtr auxtr)
    (* (FAIR: ∀ ρ : fmrole Mout, fair_model_trace ρ mtr): *)
    (LIFT: forall i δ, auxtr S!! i = Some δ -> match_labels_prop_states δ)
    (FAIR: forall ρ, fair_by fairness_cond role_match ρ mtr):
    ∀ τ : G, fair_by_group ALM τ auxtr.
  Proof. 
    eapply fairness_preserved.
    2: by apply MATCH. 
    all: eauto.
    { intros. eapply LIFT; eauto. } 
    intros [?| ].
    { apply FAIR. }
    red. simpl in *. by intros ?(?&?&?)%pred_at_trace_lookup.
  Qed. 


  Theorem model_fairness_preserved (mtr: mtrace Mout) (auxtr: atrace (LM := LM)):
    (* infinite_trace mtr -> *)
    lm_model_traces_match mtr auxtr ->
    (forall i δ, auxtr S!! i = Some δ -> match_labels_prop_states δ) ->
    (forall ρ, fair_by fairness_cond role_match ρ mtr) -> (∀ ρ : fmrole M, afair_by_next_TS ALM ρ auxtr).
  Proof.
    intros. eapply group_fairness_implies_role_fairness; eauto. 
    (* { eapply traces_match_infinite_trace; eauto. } *)
    { eapply traces_match_valid2; eauto. }
    by eapply model_fairness_preserved'.
  Qed. 

End model_fairness_preserved. 
