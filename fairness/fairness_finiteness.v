From stdpp Require Import finite.
From trillium.prelude Require Import finitary quantifiers classical_instances.
From trillium.fairness Require Import fairness fuel traces_match.

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

Section finitary.
  Context `{M: FairModel}.
  Context `{Λ: language}.
  Context `{LM: LiveModel (locale Λ) M}.
  Context `{EqDecision M}.
  Context `{EqDecision (locale Λ)}.

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

  (* TODO: move *)
  Fixpoint trace_map {A A' L L'} (sf: A → A') (lf: L -> L') (tr: finite_trace A L): finite_trace A' L' :=
  match tr with
  | trace_singleton x => trace_singleton $ sf x
  | trace_extend tr' ℓ x => trace_extend (trace_map sf lf tr') (lf ℓ) (sf x)
  end.

  Fixpoint get_underlying_fairness_trace (M : FairModel) (LM: LiveModel (locale Λ) M) (ex : auxiliary_trace LM) :=
  match ex with
  | trace_singleton δ => trace_singleton (ls_under δ)
  | trace_extend ex' (Take_step ρ _) δ => trace_extend (get_underlying_fairness_trace M LM ex') ρ (ls_under δ)
  | trace_extend ex' _ _ => get_underlying_fairness_trace M LM ex'
  end.

  Definition get_role {M : FairModel} {LM: LiveModel (locale Λ) M} (lab: mlabel LM) :=
  match lab with
  | Take_step ρ _ => Some ρ
  | _ => None
  end.

  Definition map_underlying_trace {M : FairModel} {LM: LiveModel (locale Λ) M} (aux : auxiliary_trace LM) :=
    (trace_map (λ s, ls_under s) (λ lab, get_role lab) aux).

  Program Definition enumerate_next
    (δ1: LM)
    (* (c': cfg Λ) *)
    (inner_exts: list (M * option (fmrole M)))
    (next_threads: list (locale Λ))
    (convert_lbl: option (fmrole M) -> lm_lbl LM)
    : list (LM * @mlabel LM) := 
    '(s2, ℓ) ← inner_exts;
    d ← enumerate_dom_gsets' (dom δ1.(ls_fuel) ∪ live_roles _ s2);
    fs ← enum_gmap_bounded' (live_roles _ s2 ∪ d) (max_gmap δ1.(ls_fuel) `max` LM.(lm_fl) s2);
    ms ← enum_gmap_range_bounded' (live_roles _ s2 ∪ d) next_threads ;
    let ℓ' := convert_lbl ℓ
    in
    mret ({| ls_under := s2;
             ls_fuel := `fs;
             (* ls_fuel_dom := proj2_sig fs; *) (* TODO: why this does not work?*)
             ls_mapping := `ms ;
          |}, ℓ').
  Next Obligation.
    intros ??????????. destruct fs as [? Heq]. rewrite /= Heq //. set_solver.
  Qed.
  Next Obligation.
    intros ??????????. destruct fs as [? Heq]. destruct ms as [? Heq'].
    rewrite /= Heq //.
  Qed.

  Definition lift_convert_lbl (oζ: olocale Λ) (ℓ: option (fmrole M)): lm_lbl LM :=
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
    rewrite elem_of_list_singleton; f_equal.
    - destruct δ'; simpl. f_equal; apply ProofIrrelevance.
    - done.
  Qed.

  Lemma valid_state_evolution_finitary_fairness':
    rel_finitary (valid_lift_fairness lm_valid_evolution_step (λ extr auxtr, ξ extr (map_underlying_trace auxtr (LM := LM)))).
  Proof.
    rewrite /valid_lift_fairness.
    intros ex atr [e' σ'] oζ.
    eapply finite_smaller_card_nat.
    simpl.
    set (inner_exts := ((trace_last atr).(ls_under), None) :: enum_inner ex (map_underlying_trace atr) (e', σ') oζ).
    set (next_threads := (locales_of_list e')).
    set (convert_lbl := lift_convert_lbl oζ). 
    eapply (in_list_finite (enumerate_next (trace_last atr) 
                              inner_exts next_threads convert_lbl)).
    intros [δ' ℓ]. intros [[Hlbl [Htrans Htids]] Hξ].

    eapply enum_next_in. 
    { destruct ℓ as [ρ tid' | |].
      - inversion Htrans as [Htrans']. apply elem_of_cons; right.
        by apply enum_inner_spec.
      - apply elem_of_cons; left. f_equal. inversion Htrans as (?&?&?&?&?); done.
      - apply elem_of_cons; right. inversion Htrans as (?&?).
        by apply enum_inner_spec. }
    { destruct ℓ as [ρ tid' | |].
      - inversion Htrans as (?&?&?&?&?&?&?). intros ρ' Hin. destruct (decide (ρ' ∈ live_roles _ δ')); first set_solver.
        destruct (decide (ρ' ∈ dom $ ls_fuel (trace_last atr))); set_solver. 
      - inversion Htrans as (?&?&?&?&?). set_solver.
      - inversion Htrans as (?&?&?&?&?). done. }
    { set (δ1 := trace_last atr). 
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
            (* assert (must_decrease ρ' (Some ρ') δ1 δ' (Some tid')) as Hmd; first by constructor 3. *)            
            (* specialize (Hleq Hmd). rewrite Hsome /= in Hleq. *)
            (* apply elem_of_dom in Hmap as [? Heq]. rewrite Heq in Hleq. *)
            (* pose proof (max_gmap_spec _ _ _ Heq). simpl in *. *)
            (* apply Nat.lt_le_incl. eapply Nat.lt_le_trans; [apply Hleq| ]. *)
            (* etrans; [apply H3| ]. *)
            (* apply Nat.le_max_l.             *)
            assert (oleq (ls_fuel δ' !! ρ') (ls_fuel (trace_last atr) !! ρ')).
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
              assert (ρ ∈ dom $ ls_fuel δ1) by SS.
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
    { intros ρ' tid' Hsome. unfold tids_smaller in *.
      apply locales_of_list_from_locale_from. eauto. }
    { destruct ℓ; simpl; destruct oζ =>//; by inversion Hlbl. }
    Unshelve.
    + intros ??. apply make_decision.
    + intros. apply make_proof_irrel.
    + (* done. *) exact (locale Λ).
    + done. 
  Qed. 

  Lemma valid_state_evolution_finitary_fairness (φ: execution_trace Λ -> auxiliary_trace LM -> Prop) :
    rel_finitary (valid_lift_fairness lm_valid_evolution_step (λ extr auxtr, ξ extr (map_underlying_trace auxtr) ∧ φ extr auxtr)).
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
  Context `{LM: LiveModel (locale Λ) M}.
  Context `{EqDecision M}.
  Context `{EqDecision (locale Λ)}.

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

  (* TODO: move*)
  Lemma trace_map_last {A A' L L' : Type} (sf : A → A') (lf : L → L') 
    (tr : finite_trace A L):
    trace_last (trace_map sf lf tr) = sf (trace_last tr).
  Proof. by destruct tr. Qed. 

  Lemma valid_state_evolution_finitary_fairness_simple (φ: execution_trace Λ -> auxiliary_trace LM -> Prop) :
    rel_finitary (valid_lift_fairness lm_valid_evolution_step φ).
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
    rewrite trace_map_last. 
    red in H. destruct H as (?&?&?). red in H1.
    destruct l0; simpl in H1; intuition.
    Unshelve.
    + intros ??. apply make_decision.
    + intros ??. apply make_decision.
    + intros. apply make_proof_irrel.
  Qed.

End finitary_simple.

(* TODO: Why do we need [LM] explicit here? *)
Definition live_rel `(LM: LiveModel (locale Λ) M) `{Countable (locale Λ)}
           (ex : execution_trace Λ) (aux : auxiliary_trace LM) :=
  live_tids (LM:=LM) (trace_last ex) (trace_last aux).

Definition sim_rel `(LM: LiveModel (locale Λ) M) `{Countable (locale Λ)}
           (ex : execution_trace Λ) (aux : auxiliary_trace LM) :=
  valid_state_evolution_fairness lm_valid_evolution_step ex aux ∧ live_rel LM ex aux.

Definition sim_rel_with_user `(LM: LiveModel (locale Λ) M) `{Countable (locale Λ)}
           (ξ : execution_trace Λ -> finite_trace M (option (fmrole M)) -> Prop)
  (ex : execution_trace Λ) (aux : auxiliary_trace LM) :=
  sim_rel LM ex aux ∧ ξ ex (map_underlying_trace aux).

(* TODO: Maybe redefine [sim_rel_with_user] in terms of [valid_lift_fairness] *)
Lemma valid_lift_fairness_sim_rel_with_user `{LM:LiveModel (locale Λ) Mdl}
      `{Countable (locale Λ)}
      (ξ : execution_trace Λ → finite_trace Mdl (option $ fmrole Mdl) →
           Prop) extr atr :
  valid_lift_fairness lm_valid_evolution_step
    (λ extr auxtr, ξ extr (map_underlying_trace (LM:=LM) auxtr) ∧
                   live_rel LM extr auxtr) extr atr ↔
  sim_rel_with_user LM ξ extr atr.
Proof. split; [by intros [Hvalid [Hlive Hξ]]|by intros [[Hvalid Hlive] Hξ]]. Qed.

Lemma rel_finitary_sim_rel_with_user_ξ `{LM:LiveModel (locale Λ) Mdl}
      `{Countable (locale Λ)} ξ :
  rel_finitary ξ → rel_finitary (sim_rel_with_user LM ξ).
Proof.
  intros Hrel.
  eapply rel_finitary_impl.
  { intros ex aux. by eapply valid_lift_fairness_sim_rel_with_user.
    (* TODO: Figure out if these typeclass subgoals should be resolved locally *)
    Unshelve.
    - intros ??. apply make_decision.
    - intros ??. apply make_decision. }
  by eapply valid_state_evolution_finitary_fairness.
  (* TODO: get rid of it *)
  Unshelve. 
  all: intros ??; apply make_decision.
Qed.

Lemma rel_finitary_sim_rel_with_user_sim_rel `{LM:LiveModel (locale Λ) Mdl}
      `{EqDecision (mstate LM)} `{EqDecision (mlabel LM)}
      `{Countable (locale Λ)} ξ :
  rel_finitary (sim_rel LM) → rel_finitary (sim_rel_with_user LM ξ).
Proof.
  intros Hrel. eapply rel_finitary_impl; [|done]. by intros ex aux [Hsim _].
Qed.
