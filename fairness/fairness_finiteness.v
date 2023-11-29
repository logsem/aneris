From stdpp Require Import finite.
From trillium.prelude Require Import finitary quantifiers classical_instances.
From trillium.fairness Require Import fairness fuel traces_match lm_fair_traces lm_fair. 

Section gmap.
  Context `{!EqDecision K, !Countable K}.

  Definition max_gmap (m: gmap K nat) : nat :=
    map_fold (λ k v r, v `max` r) 0 m.

  Lemma max_gmap_spec m:
    map_Forall (λ _ v, v <= max_gmap m) m.
  Proof.
    induction m using map_ind; first done.
    apply map_Forall_insert =>//. rewrite /max_gmap map_fold_insert //.
    - split; first lia. intros ?? Hnotin. specialize (IHm _ _ Hnotin). simpl in IHm.
      unfold max_gmap in IHm. lia.
    - intros **. lia.
  Qed.
End gmap.

(* TODO: move? *)
Section LMFinBranching.
  Context `{LM: LiveModel G M LSI}.
  Context {DEC: forall a b c, Decision (LSI a b c)}.

  Definition get_role {M : FairModel} {LSI} {LM: LiveModel G M LSI} (lab: mlabel LM) :=
  match lab with
  | Take_step ρ _ => Some ρ
  | _ => None
  end.

  (* Definition map_underlying_trace {M : FairModel} {LSI} {LM: LiveModel (locale Λ) M LSI} (aux : auxiliary_trace LM) := *)
  (*   (trace_map (λ s, ls_under s) (λ lab, get_role lab) aux). *)

  Program Definition enumerate_next
    (δ1: LM)
    (* (c': cfg Λ) *)
    (inner_exts: list (M * option (fmrole M)))
    (next_threads: list G)
    (convert_lbl: option (fmrole M) -> lm_lbl LM)
    : list (LM * @mlabel LM) := 
    '(s2, ℓ) ← inner_exts;
    d ← enumerate_dom_gsets' (dom δ1.(ls_fuel) ∪ live_roles _ s2);
    fs ← enum_gmap_bounded' (live_roles _ s2 ∪ d) (max_gmap δ1.(ls_fuel) `max` LM.(lm_fl) s2);
    ms ← enum_gmap_range_bounded' (live_roles _ s2 ∪ d) next_threads ;
    let ℓ' := convert_lbl ℓ
    in
    (if
        (* (decide ((s2, ms, fs) = (s2, ms, fs))) *)
        (* (decide (LSI s2 ms fs)) *)        
        (decide (LSI s2 (`ms) (`fs))) (* TODO: what's the difference with above? *)
    then
    [({| ls_under := s2;
             ls_fuel := `fs;
             ls_mapping := `ms ;
          |}, ℓ')]
      else
    []).
  Next Obligation.
    intros ??????????. destruct fs as [? Heq]. rewrite /= Heq //. set_solver.
  Qed.
  Next Obligation.
    intros ??????????. destruct fs as [? Heq]. destruct ms as [? Heq'].
    rewrite /= Heq //.
  Qed.
  Next Obligation. done. Qed. 

  Definition lift_convert_lbl (oζ: option G) (ℓ: option (fmrole M)): lm_lbl LM :=
    match ℓ with
    | None => match oζ with
               Some ζ => Silent_step ζ
             | None => Config_step
             end
    | Some ℓ => match oζ with
               | None => Config_step
               | Some ζ => Take_step ℓ ζ
               end
    end. 

  Lemma enum_next_in
    δ1
    ℓ δ'
    inner_exts
    next_threads
    convert_lbl
    (IN_IE: (ls_under δ', get_role ℓ) ∈ inner_exts)
    (IN_DOMS: dom (ls_fuel δ') ⊆ dom (ls_fuel δ1) ∪ live_roles M δ')
    (FUEL_LIM: forall ρ f (F: ls_fuel δ' !! ρ = Some f),
        f ≤ max_gmap (ls_fuel δ1) `max` lm_fl LM δ')
    (THREADS_IN: forall ρ' tid' (T: ls_mapping δ' !! ρ' = Some tid'),
        tid' ∈ next_threads)    
    (CONVERT: ℓ = convert_lbl (get_role ℓ))
    :
    (δ', ℓ) ∈ enumerate_next δ1 inner_exts next_threads convert_lbl
  .
  Proof. 
    unfold enumerate_next. apply elem_of_list_bind.
    exists (δ'.(ls_under), get_role ℓ).
    split; last first.
    { apply IN_IE. }
    
    apply elem_of_list_bind. eexists (dom $ δ'.(ls_fuel)). split; last first.
    { apply enumerate_dom_gsets'_spec.
      apply IN_DOMS. }
    apply elem_of_list_bind.
    assert (Hfueldom: dom δ'.(ls_fuel) = live_roles M δ' ∪ dom (ls_fuel δ')).
    { rewrite subseteq_union_1_L //. apply ls_fuel_dom. }
    eexists (δ'.(ls_fuel) ↾ Hfueldom); split; last first.
    { eapply enum_gmap_bounded'_spec; split =>//. }
    apply elem_of_list_bind.
    assert (Hmappingdom: dom δ'.(ls_mapping) = live_roles M δ' ∪ dom (ls_fuel δ')).
    { rewrite -Hfueldom ls_same_doms //. }
    exists (δ'.(ls_mapping) ↾ Hmappingdom); split; last first.
    { eapply enum_gmap_range_bounded'_spec; split=>//. }
    destruct decide; [| by destruct δ']. 
    rewrite elem_of_list_singleton; f_equal.
    - destruct δ'; simpl. f_equal; apply ProofIrrelevance.
    - done.
  Qed.

  Lemma next_step_domain
    δ           
    (oζ : option G)
    inner_exts
    next_threads
    (δ' : LM)
    (ℓ : mlabel LM)
    (Hlbl : labels_match oζ ℓ (LM := LM))
    (Htrans : lm_ls_trans LM δ ℓ δ')
    (INNER_DOM: (ls_under δ', get_role ℓ) ∈ inner_exts)
    (THREADS_IN: forall ρ' tid' (T: ls_mapping δ' !! ρ' = Some tid'), tid' ∈ next_threads)
    :
    (δ', ℓ) ∈ enumerate_next δ inner_exts next_threads (lift_convert_lbl oζ).
  Proof.
    eapply enum_next_in. 
    { done. }
    { destruct ℓ as [ρ tid' | |].
      - inversion Htrans as (?&?&?&?&?&?&?). intros ρ' Hin. destruct (decide (ρ' ∈ live_roles _ δ')); first set_solver.
        destruct (decide (ρ' ∈ dom $ ls_fuel δ)); set_solver. 
      - inversion Htrans as (?&?&?&?&?). set_solver.
      - inversion Htrans as (?&?&?&?&?). done. }
    { set (δ1 := δ). 
      intros ρ f Hsome. destruct ℓ as [ρ' tid' | |].
      - destruct (decide (ρ = ρ')) as [-> | Hneq].
        + inversion Htrans as [? Hbig]. destruct Hbig as (Hmap&Hleq&?&Hlim&?&?).
          destruct (decide (ρ' ∈ live_roles _ δ')).
          * rewrite Hsome /= in Hlim.
            assert (Hlive: ρ' ∈ live_roles _ δ') by set_solver.
            specialize (Hlim Hlive). lia.
          * unfold fuel_decr in Hleq.
            apply elem_of_dom_2 in Hmap. rewrite ls_same_doms in Hmap.
            pose proof Hsome as Hsome'. apply elem_of_dom_2 in Hsome'.
            specialize (Hleq ρ' ltac:(done) ltac:(done)).
            assert (oleq (ls_fuel δ' !! ρ') (ls_fuel δ !! ρ')).
            { specialize (H0 ρ' Hmap). destruct H0 as [?|[?|?]]; set_solver. }
            simpl in H3. rewrite Hsome in H3.
            subst δ1.
            apply elem_of_dom in Hmap as [? Heq]. rewrite Heq in H3. 
            pose proof (max_gmap_spec _ _ _ Heq). simpl in *.
            lia. 
        + inversion Htrans as [? Hbig]. destruct Hbig as (Hmap&?&Hleq'&?&Hnew&?).
          destruct (decide (ρ ∈ dom $ ls_fuel δ1)) as [Hin|Hnotin].
          * assert (Hok: oleq (ls_fuel δ' !! ρ) (ls_fuel δ1 !! ρ)).
            { unfold fuel_must_not_incr in *.
              (* assert (ρ ∈ dom $ ls_fuel δ1) by SS. *)              
              specialize (Hleq' ρ ltac:(done) ) as [Hleq'|Hleq'] =>//. apply elem_of_dom_2 in Hsome. set_solver. }
            rewrite Hsome in Hok. destruct (ls_fuel δ1 !! ρ) as [f'|] eqn:Heqn; last done.
            pose proof (max_gmap_spec _ _ _ Heqn). simpl in *.
            etrans; [| apply Nat.le_max_l]. etrans; eauto.
          * assert (Hok: oleq (ls_fuel δ' !! ρ) (Some (LM.(lm_fl) δ'))).
            { apply Hnew. apply elem_of_dom_2 in Hsome. set_solver. }
            rewrite Hsome in Hok. simpl in Hok. lia.
      - inversion Htrans as [? [? [Hleq [Hincl Heq]]]]. specialize (Hleq ρ).
        assert (ρ ∈ dom $ ls_fuel δ1) as Hin.
        { apply elem_of_dom_2 in Hsome. set_solver. }
        specialize (Hleq Hin) as [Hleq|[Hleq|Hleq]].
        + rewrite Hsome in Hleq. destruct (ls_fuel δ1 !! ρ) as [f'|] eqn:Heqn.
          * pose proof (max_gmap_spec _ _ _ Heqn). simpl in *.
            etrans; [| apply Nat.le_max_l].
            rewrite Heqn in Hleq. lia.  
          * simpl in *. rewrite Heqn in Hleq. done.
        + destruct Hleq as [[=] _]. 
        + apply elem_of_dom_2 in Hsome. set_solver.
      - inversion Htrans as [? [? [Hleq [Hnew Hfalse]]]]. done. }
    { done. }
    { destruct ℓ; simpl; destruct oζ =>//; by inversion Hlbl. }
   Qed.

  Lemma role_LM_step_dom
    δ           
    (inner_exts : list (M * option (fmrole M)))
    (next_threads : list G)
    (ℓ : mlabel LM)
    : 
    exists (lδ': list (lm_ls LM)), forall (δ': lm_ls LM),
      lm_ls_trans LM δ ℓ δ' ->
      (ls_under δ', get_role ℓ) ∈ inner_exts ->
      (forall ρ' tid' (T: ls_mapping δ' !! ρ' = Some tid'), tid' ∈ next_threads) ->
      In δ' lδ'.
  Proof.
    assert (exists oζ oρ, lift_convert_lbl oζ oρ = ℓ) as (oζ & oρ & CONV). 
    { rewrite /lift_convert_lbl. destruct ℓ.
      - by exists (Some g), (Some f).
      - by exists (Some g), None.
      - by exists None, None. }
    set (l2 := enumerate_next δ inner_exts next_threads (lift_convert_lbl oζ)).
    exists (map fst l2).
    intros. apply in_map_iff. exists (δ', ℓ). split; auto.
    apply elem_of_list_In. subst l2. apply next_step_domain; auto.
    subst ℓ. by destruct oζ, oρ. 
  Qed. 

End LMFinBranching.

Section finitary.
  Context `{M: FairModel}.
  Context `{Λ: language}.
  Context `{LM: LiveModel (locale Λ) M LSI}.
  Context `{EqDecision M}.
  (* Context `{EqDecision (locale Λ)}. *)
  Context `{DEC: forall a b c, Decision (LSI a b c)}.

  Variable (ξ: execution_trace Λ -> finite_trace M (option M.(fmrole)) -> Prop).

  Variable model_finitary: rel_finitary ξ.

  #[local] Instance eq_dec_next_states ex atr c' oζ:
    EqDecision {'(δ', ℓ) : M * (option (fmrole M)) |
                  ξ (ex :tr[ oζ ]: c') (atr :tr[ ℓ ]: δ')}.
  Proof. intros x y. apply make_decision. Qed.

  Lemma model_finite: ∀ (ex : execution_trace Λ) (atr : finite_trace _ _) c' oζ,
    Finite (sig (λ '(δ', ℓ), ξ (ex :tr[oζ]: c') (atr :tr[ℓ]: δ'))).
  Proof.
    intros ex atr c' oζ.
    pose proof (model_finitary ex atr c' oζ).
    by apply smaller_card_nat_finite in H.
  Qed.

  Definition enum_inner extr fmodtr c' oζ : list (M * option M.(fmrole)) :=
    map proj1_sig (@enum _ _ (model_finite extr fmodtr c' oζ)).

  Lemma enum_inner_spec (δ' : M) ℓ extr atr c' oζ :
    ξ (extr :tr[oζ]: c') (atr :tr[ℓ]: δ') → (δ', ℓ) ∈ enum_inner extr atr c' oζ.
  Proof.
    intros H. unfold enum_inner. rewrite elem_of_list_fmap.
    exists (exist _ (δ', ℓ) H). split =>//. apply elem_of_enum.
  Qed.

  (* Lemma enum_inner_spec extr atr c' oζ : *)
  (*   ξ (extr :tr[oζ]: c') (atr) → (δ', ℓ) ∈ enum_inner extr atr c' oζ. *)
  (* Proof. *)
  (*   intros H. unfold enum_inner. rewrite elem_of_list_fmap. *)
  (*   exists (exist _ (δ', ℓ) H). split =>//. apply elem_of_enum. *)
  (* Qed. *)

  (* (* TODO: move *) *)
  (* Fixpoint trace_map {A A' L L'} (sf: A → A') *)
  (*   (lsf: A -> L -> A -> L') (tr: finite_trace A L): finite_trace A' L' := *)
  (* match tr with *)
  (* | trace_singleton x => trace_singleton $ sf x *)
  (* | trace_extend tr' ℓ x => trace_extend (trace_map sf lsf tr') (lsf x ℓ (trace_first tr')) (sf x) *)
  (* end. *)

  Fixpoint get_underlying_fairness_trace {M : FairModel} {LSI} {LM: LiveModel (locale Λ) M LSI} {LF: LMFairPre LM}
    (ex : auxiliary_trace (fair_model_model LM_Fair)) :=
  match ex with
  | trace_singleton δ => trace_singleton (ls_under δ)
  (* | trace_extend ex' (Take_step ρ _) δ => trace_extend (get_underlying_fairness_trace M LSI LM ex') ρ (ls_under δ) *)
  (* | trace_extend ex' _ _ => get_underlying_fairness_trace M LSI LM ex' *)
  | trace_extend ex' None δ =>
      let u' := get_underlying_fairness_trace ex' in
      trace_extend u' None δ
  | trace_extend ex' (Some g) δ =>
      let u' := get_underlying_fairness_trace ex' in
      match (next_TS_role (trace_last ex') g δ) with
      | Some ρ => trace_extend u' (Some ρ) δ
      (* | None => u' *)
      | None => trace_extend u' None δ
      end
  end.

  Lemma valid_state_evolution_finitary_fairness' {LF: LMFairPre LM}:
    rel_finitary (valid_lift_fairness lm_valid_evolution_step (λ extr auxtr, ξ extr (get_underlying_fairness_trace auxtr)) (M := fair_model_model LM_Fair)).
  Proof.
    rewrite /valid_lift_fairness.
    intros ex atr [e' σ'] oζ.
    eapply finite_smaller_card_nat.
    simpl.
    set (inner_exts := ((trace_last atr).(ls_under), None) :: enum_inner ex (get_underlying_fairness_trace atr) (e', σ') oζ).
    set (next_threads := (locales_of_list e')).
    set (convert_lbl := lift_convert_lbl oζ (LM := LM)).

    (* eapply surjective_finite. Unshelve. *)
    set (get_ol := fun (st_ℓ: lm_ls LM * lm_lbl LM) => 
                        match st_ℓ with
                        | (st, Silent_step τ) | (st, Take_step _ τ) => (st, Some τ)
                        | (st, _) => (st, None)
                        end). 
    
    eapply (in_list_finite (get_ol <$> (enumerate_next (trace_last atr) 
                              inner_exts next_threads convert_lbl))).
    intros [δ' ℓ]. intros [[Hlbl [Htrans Htids]] Hξ].
    apply elem_of_list_fmap.
    subst. simpl in Htrans. destruct ℓ as [τ| ]; [| done].
    red in Htrans. destruct Htrans as (ℓ & Htrans & MATCH).

    (* TODO: get rid of duplication *)
    destruct (next_TS_role (trace_last atr) τ δ') eqn:N; rewrite N in Hξ.
    - clear Htrans.
      apply next_TS_spec_pos in N as Htrans.
      exists (δ', Take_step f τ). split; [done| ].
      eapply next_step_domain; eauto.
      { done. }
      { inversion Htrans as [Htrans'].
        apply elem_of_cons; right.
        by apply enum_inner_spec. }
      { intros ρ' tid' Hsome. unfold tids_smaller in *.
        apply locales_of_list_from_locale_from. eauto. }
    - eapply next_TS_spec_inv_S in N.  
      2: { eexists. split; eauto. }
      clear Htrans. rename N into Htrans. 
      exists (δ', Silent_step τ). split. 
      { simpl. destruct ℓ; simpl in *; congruence || done. }
      eapply next_step_domain; eauto.
      { done. }
      { apply elem_of_cons; left. f_equal. inversion Htrans as (?&?&?&?&?); done. }
      { intros ρ' tid' Hsome. unfold tids_smaller in *.
        apply locales_of_list_from_locale_from. eauto. }
      
    Unshelve.
    + intros. apply make_proof_irrel.
  Qed.

  Lemma valid_state_evolution_finitary_fairness
          {LF: LMFairPre LM}
    (φ: execution_trace Λ -> auxiliary_trace (fair_model_model LM_Fair) -> Prop) :
    rel_finitary (valid_lift_fairness lm_valid_evolution_step (λ extr auxtr, ξ extr (get_underlying_fairness_trace auxtr) ∧ φ extr auxtr) (M := fair_model_model LM_Fair)).
  Proof.
    eapply rel_finitary_impl; [| apply valid_state_evolution_finitary_fairness'].
    { by intros ??[? [? ?]]. }
    Unshelve.
    all: intros ??; apply make_decision.
  Qed.

End finitary.

Section finitary_simple.
  Context `{M: FairModel}.
  Context `{Λ: language}.
  Context `{LM: LiveModel (locale Λ) M LSI}.
  Context `{EqDecision M}.
  Context `{EqDecision (locale Λ)}.
  Context `{DEC: forall a b c, Decision (LSI a b c)}.

  (* Context `{HPI0: forall s x, ProofIrrel ((let '(s', ℓ) := x in M.(fmtrans) s ℓ s'): Prop) }. *)
  Context `{HPI0: forall s x, ProofIrrel ((let '(s', ℓ) := x in
                                      fmtrans M s ℓ s' \/ (s' = s /\ ℓ = None)): Prop)}.

  (* TODO: a stronger version is put here because the same expression is used
           in ProofIrrel hypothesis.
           This stronger version is derivable from finiteness of transitions only *)
  Variable model_finitary': forall s1, Finite { '(s2, ℓ) |
                                           (* M.(fmtrans) s1 ℓ s2 *)
                                           (fmtrans M s1 ℓ s2 \/ (s2 = s1 /\ ℓ = None))
                                    }.

  (* (* TODO: adapted from valid_state_evolution_fairness, unify? *) *)
  Definition mtrace_evolution
             (extr : execution_trace Λ) (mtr : finite_trace M (option (fmrole M))) :=
    match extr, mtr with
    | (extr :tr[oζ]: (es, σ)), mtr :tr[ℓ]: δ =>
        M.(fmtrans) (trace_last mtr) ℓ δ \/ (δ = trace_last mtr /\ ℓ = None) 
    | _, _ => True
    end.

  (* (* TODO: move*) *)
  (* Lemma underlying_trace_last {A A' L L' : Type} (sf : A → A') (lf : L → L') *)
  (*   (tr : finite_trace A L): *)
  (*   trace_last (trace_map sf lf tr) = sf (trace_last tr). *)
  (* Proof. *)
  (*   get_underlying_fairness_trace *)
  (*   by destruct tr. Qed. *)

  Lemma valid_state_evolution_finitary_fairness_simple
          {LF: LMFairPre LM}
    (φ: execution_trace Λ -> auxiliary_trace (fair_model_model LM_Fair) -> Prop)
    (* (VALIDφ: forall extr auxtr, φ extr auxtr -> trace_steps (fmtrans LM_Fair) auxtr): *)
    :
    rel_finitary (valid_lift_fairness lm_valid_evolution_step φ (M := (fair_model_model LM_Fair))).
  Proof.
    eapply rel_finitary_impl. 
    2: eapply valid_state_evolution_finitary_fairness with (ξ := mtrace_evolution).
    2: { red. intros. eapply finite_smaller_card_nat.
         rewrite /mtrace_evolution.
         specialize (model_finitary' (trace_last atr)).
         eapply in_list_finite with (l := map proj1_sig (@enum _ _ model_finitary')).
         intros. apply elem_of_list_fmap.
         destruct x as (δ', ℓ), c'. simpl in *. 
         exists ((δ', ℓ) ↾ H). split; auto.
         apply elem_of_enum. }
    intros ??[??]. repeat split; eauto.
    red. destruct ex as [?| ] eqn:EX; [done| ].
    destruct aux as [?| ] eqn:AUX; [done| ]. 
    destruct a. simpl in *. 
    (* rewrite trace_map_last.  *)
    red in H. destruct H as (?&?&?). red in H1.
    destruct l0; simpl in H1; intuition.
    (* TODO: move *) 
    assert (forall tr, trace_last (get_underlying_fairness_trace tr) = ls_under (trace_last tr)) as UNDER_LAST.
    { clear. destruct tr; try done. simpl.
      (* inversion VALID. *)
      subst. destruct l.
      2: { done. }
      destruct next_TS_role; done. }
      
    (*   destruct next_TS_role eqn:N; [done| ]. *)
    (*   eapply next_TS_spec_inv_S in N. *)
    (*   2: { by rewrite H2. } *)
    (*   simpl in N. repeat apply proj2 in N. rewrite -N. *)
    (*   simpl. done. } *)
     
    destruct (next_TS_role (trace_last f0) l0 a0) eqn:N.
    - apply next_TS_spec_pos in N. left.
      rewrite UNDER_LAST. apply N. 
    - subst. simpl.
      right. split; auto.
      apply next_TS_spec_inv_S in N; auto.
      simpl in N. repeat apply proj2 in N. rewrite -N.
      symmetry. apply UNDER_LAST.
    
    Unshelve.
    + intros. apply make_proof_irrel.
  Qed.

End finitary_simple.


Section RelFinitary.
  (* Context `{Countable (locale Λ)}.  *)
  Context `(LM: LiveModel (locale Λ) M LSI). 
  Context {LF: LMFairPre LM}. 

  (* TODO: Why do we need [LM] explicit here? *)
  Definition live_rel (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) :=
  live_tids (LM:=LM) (trace_last ex) (trace_last aux).

  Definition sim_rel (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) :=
    valid_state_evolution_fairness lm_valid_evolution_step ex aux (M := (fair_model_model LM_Fair)) ∧ live_rel ex aux.

Definition sim_rel_with_user (ξ : execution_trace Λ -> finite_trace M (option (fmrole M)) -> Prop)
  (ex : execution_trace Λ) (aux : auxiliary_trace (fair_model_model LM_Fair)) :=
  sim_rel ex aux ∧ ξ ex (get_underlying_fairness_trace aux).

(* TODO: Maybe redefine [sim_rel_with_user] in terms of [valid_lift_fairness] *)
Lemma valid_lift_fairness_sim_rel_with_user 
      (ξ : execution_trace Λ → finite_trace M (option $ fmrole M) → Prop) extr atr :
  valid_lift_fairness lm_valid_evolution_step
    (λ extr auxtr, ξ extr (get_underlying_fairness_trace (LM:=LM) auxtr) ∧
                   live_rel extr auxtr) (M := fair_model_model LM_Fair) extr atr ↔
  sim_rel_with_user ξ extr atr.
Proof. 
  split; [by intros [Hvalid [Hlive Hξ]]|
          by intros [[Hvalid Hlive] Hξ]].
Qed.

Lemma rel_finitary_sim_rel_with_user_ξ {DEC: forall a b c, Decision (LSI a b c)} ξ :
  rel_finitary ξ → rel_finitary (sim_rel_with_user ξ).
Proof.
  intros Hrel.
  eapply rel_finitary_impl.
  { intros ex aux. by eapply valid_lift_fairness_sim_rel_with_user.
    (* TODO: Figure out if these typeclass subgoals should be resolved locally *) }
  by eapply valid_state_evolution_finitary_fairness.
Qed.

Lemma rel_finitary_sim_rel_with_user_sim_rel 
  `{forall a b c, Decision (LSI a b c)} `{EqDecision (mstate LM)}
ξ :
  rel_finitary (sim_rel ) → rel_finitary (sim_rel_with_user ξ).
Proof.
  intros Hrel. eapply rel_finitary_impl; [|done]. by intros ex aux [Hsim _].
Qed.

End RelFinitary.
