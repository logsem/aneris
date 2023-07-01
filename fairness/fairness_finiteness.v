From stdpp Require Import finite.
From trillium.prelude Require Import finitary quantifiers classical_instances.
From trillium.fairness Require Import fairness fuel.

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
  Context `{LM: LiveModel Λ M}.
  Context `{EqDecision M}.
  Context `{EqDecision (locale Λ)}.

  Context `{HPI0: forall s x, ProofIrrel ((let '(s', ℓ) := x in M.(fmtrans) s ℓ s'): Prop) }.

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

  Fixpoint get_underlying_fairness_trace (M : FairModel) (LM: LiveModel Λ M) (ex : auxiliary_trace LM) :=
  match ex with
  | trace_singleton δ => trace_singleton (ls_under δ)
  | trace_extend ex' (Take_step ρ _) δ => trace_extend (get_underlying_fairness_trace M LM ex') ρ (ls_under δ)
  | trace_extend ex' _ _ => get_underlying_fairness_trace M LM ex'
  end.

  Definition get_role {M : FairModel} {LM: LiveModel Λ M} (lab: mlabel LM) :=
  match lab with
  | Take_step ρ _ => Some ρ
  | _ => None
  end.

  Definition map_underlying_trace {M : FairModel} {LM: LiveModel Λ M} (aux : auxiliary_trace LM) :=
    (trace_map (λ s, ls_under s) (λ lab, get_role lab) aux).

  Program Definition enumerate_next extr (fmodtr: auxiliary_trace LM) c' oζ:
    list (LM * @mlabel LM) :=
    let δ1 := trace_last fmodtr in
    '(s2, ℓ) ← (δ1.(ls_under), None) :: enum_inner extr (map_underlying_trace fmodtr) c' oζ;
    d ← enumerate_dom_gsets' (dom δ1.(ls_fuel) ∪ live_roles _ s2);
    fs ← enum_gmap_bounded' (live_roles _ s2 ∪ d) (max_gmap δ1.(ls_fuel) `max` LM.(lm_fl) s2);
    ms ← enum_gmap_range_bounded' (live_roles _ s2 ∪ d) (locales_of_list c'.1);
    let ℓ' := match ℓ with
              | None => match oζ with
                         Some ζ => Silent_step ζ
                       | None => Config_step
                       end
              | Some ℓ => match oζ with
                         | None => Config_step
                         | Some ζ => Take_step ℓ ζ
                         end
              end in
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

  Lemma valid_state_evolution_finitary_fairness (φ: execution_trace Λ -> auxiliary_trace LM -> Prop) :
    rel_finitary (valid_lift_fairness (λ extr auxtr, ξ extr (map_underlying_trace auxtr) ∧ φ extr auxtr)).
  Proof.
    rewrite /valid_lift_fairness.
    intros ex atr [e' σ'] oζ.
    eapply finite_smaller_card_nat.
    simpl.
    eapply (in_list_finite (enumerate_next ex atr (e',σ') oζ)).
    intros [δ' ℓ] [[Hlbl [Htrans Htids]] [Hξ Hφ]].
    unfold enumerate_next. apply elem_of_list_bind.
    exists (δ'.(ls_under), match ℓ with Take_step l _ => Some l | _ => None end).
    split; last first.
    { destruct ℓ as [ρ tid' | |].
      - inversion Htrans as [Htrans']. apply elem_of_cons; right.
        by apply enum_inner_spec.
      - apply elem_of_cons; left. f_equal. inversion Htrans as (?&?&?&?&?); done.
      - apply elem_of_cons; right. inversion Htrans as (?&?). by apply enum_inner_spec. }
    apply elem_of_list_bind. eexists (dom $ δ'.(ls_fuel)). split; last first.
    { apply enumerate_dom_gsets'_spec. destruct ℓ as [ρ tid' | |].
      - inversion Htrans as (?&?&?&?&?&?&?). intros ρ' Hin. destruct (decide (ρ' ∈ live_roles _ δ')); first set_solver.
        destruct (decide (ρ' ∈ dom $ ls_fuel (trace_last atr))); first set_solver. set_solver.
      - inversion Htrans as (?&?&?&?&?). set_solver.
      - inversion Htrans as (?&?&?&?&?). done. }
    apply elem_of_list_bind.
    assert (Hfueldom: dom δ'.(ls_fuel) = live_roles M δ' ∪ dom (ls_fuel δ')).
    { rewrite subseteq_union_1_L //. apply ls_fuel_dom. }
    eexists (δ'.(ls_fuel) ↾ Hfueldom); split; last first.
    { eapply enum_gmap_bounded'_spec; split =>//.
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
            assert(must_decrease ρ' (Some ρ') (trace_last atr) δ' (Some tid')) as Hmd; first by constructor 3.
            specialize (Hleq Hmd). rewrite Hsome /= in Hleq.
            apply elem_of_dom in Hmap as [? Heq]. rewrite Heq in Hleq.
            pose proof (max_gmap_spec _ _ _ Heq). simpl in *. lia.
        + inversion Htrans as [? Hbig]. destruct Hbig as (Hmap&?&Hleq'&?&Hnew&?).
          destruct (decide (ρ ∈ dom $ ls_fuel (trace_last atr))) as [Hin|Hnotin].
          * assert (Hok: oleq (ls_fuel δ' !! ρ) (ls_fuel (trace_last atr) !! ρ)).
            { unfold fuel_must_not_incr in *.
              assert (ρ ∈ dom $ ls_fuel (trace_last atr)) by SS.
              specialize (Hleq' ρ ltac:(done) ltac:(congruence)) as [Hleq'|Hleq'] =>//. apply elem_of_dom_2 in Hsome. set_solver. }
            rewrite Hsome in Hok. destruct (ls_fuel (trace_last atr) !! ρ) as [f'|] eqn:Heqn; last done.
            pose proof (max_gmap_spec _ _ _ Heqn). simpl in *. lia.
          * assert (Hok: oleq (ls_fuel δ' !! ρ) (Some (LM.(lm_fl) δ'))).
            { apply Hnew. apply elem_of_dom_2 in Hsome. set_solver. }
            rewrite Hsome in Hok. simpl in Hok. lia.
      - inversion Htrans as [? [? [Hleq [Hincl Heq]]]]. specialize (Hleq ρ).
        assert (ρ ∈ dom $ ls_fuel (trace_last atr)) as Hin.
        { apply elem_of_dom_2 in Hsome. set_solver. }
        specialize (Hleq Hin ltac:(done)) as [Hleq|Hleq].
        + rewrite Hsome in Hleq. destruct (ls_fuel (trace_last atr) !! ρ) as [f'|] eqn:Heqn. 
          * pose proof (max_gmap_spec _ _ _ Heqn). simpl in *.
            rewrite Heqn in Hleq.
            lia.
          * simpl in *. rewrite Heqn in Hleq. done.
        + apply elem_of_dom_2 in Hsome. set_solver.
      - inversion Htrans as [? [? [Hleq [Hnew Hfalse]]]]. done. }
    apply elem_of_list_bind.
    assert (Hmappingdom: dom δ'.(ls_mapping) = live_roles M δ' ∪ dom (ls_fuel δ')).
    { rewrite -Hfueldom ls_same_doms //. }
    exists (δ'.(ls_mapping) ↾ Hmappingdom); split; last first.
    { eapply enum_gmap_range_bounded'_spec; split=>//.
      intros ρ' tid' Hsome. unfold tids_smaller in *.
      apply locales_of_list_from_locale_from. eauto. }
    rewrite elem_of_list_singleton; f_equal.
    - destruct δ'; simpl. f_equal; apply ProofIrrelevance.
    - destruct ℓ; simpl; destruct oζ =>//; by inversion Hlbl.
      Unshelve.
      + intros ??. apply make_decision.
      + intros. apply make_proof_irrel.
      + done.
      + done.
  Qed.
End finitary.

Section finitary_simple.
  Context `{M: FairModel}.
  Context `{Λ: language}.
  Context `{LM: LiveModel Λ M}.
  Context `{EqDecision M}.
  Context `{EqDecision (locale Λ)}.

  Context `{HPI0: forall s x, ProofIrrel ((let '(s', ℓ) := x in M.(fmtrans) s ℓ s'): Prop) }.

  Variable model_finitary: forall s1, Finite { '(s2, ℓ) | M.(fmtrans) s1 ℓ s2 }.

  Definition enum_inner_simple (s1: M): list (M * option M.(fmrole)) :=
    map proj1_sig (@enum _ _ (model_finitary s1)).

  Lemma enum_inner_spec_simple (s1 s2: M) ℓ:
    M.(fmtrans) s1 ℓ s2 -> (s2, ℓ) ∈ enum_inner_simple s1.
  Proof.
    intros H. unfold enum_inner. rewrite elem_of_list_fmap.
    exists (exist _ (s2, ℓ) H). split =>//. apply elem_of_enum.
  Qed.

  Program Definition enumerate_next_simple (δ1: LM) (oζ : olocale Λ) (c': cfg Λ):
    list (LM * @mlabel LM) :=
    '(s2, ℓ) ← (δ1.(ls_under), None) :: enum_inner_simple δ1.(ls_under);
    d ← enumerate_dom_gsets' (dom δ1.(ls_fuel) ∪ live_roles _ s2);
    fs ← enum_gmap_bounded' (live_roles _ s2 ∪ d) (max_gmap δ1.(ls_fuel) `max` LM.(lm_fl) s2);
    ms ← enum_gmap_range_bounded' (live_roles _ s2 ∪ d) (locales_of_list c'.1);
    let ℓ' := match ℓ with
              | None => match oζ with
                         Some ζ => Silent_step ζ
                       | None => Config_step
                       end
              | Some ℓ => match oζ with
                         | None => Config_step
                         | Some ζ => Take_step ℓ ζ
                         end
              end in
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

  (* TODO: Derive this from the stronger version *)
  Lemma valid_state_evolution_finitary_fairness_simple (φ: execution_trace Λ -> auxiliary_trace LM -> Prop) :
    rel_finitary (valid_lift_fairness φ).
  Proof.
    intros extr auxtr [e' σ'] oζ.
    eapply finite_smaller_card_nat.
    eapply (in_list_finite (enumerate_next_simple (trace_last auxtr) oζ (e',σ'))).
    intros [δ2 ℓ] [[Hlab [Htrans Hsmall]] ?].
    unfold enumerate_next. apply elem_of_list_bind.
    exists (δ2.(ls_under), match ℓ with Take_step l _ => Some l | _ => None end).
    split; last first.
    { destruct ℓ as [ρ tid' | |].
      - inversion Htrans as [Htrans']. apply elem_of_cons; right. by apply enum_inner_spec_simple.
      - apply elem_of_cons; left. f_equal. inversion Htrans as (?&?&?&?&?); done.
      - apply elem_of_cons; right. inversion Htrans as (?&?). by apply enum_inner_spec_simple. }
    apply elem_of_list_bind. eexists (dom $ δ2.(ls_fuel)). split; last first.
    { apply enumerate_dom_gsets'_spec. destruct ℓ as [ρ tid' | |].
      - inversion Htrans as (?&?&?&?&?&?&?). intros ρ' Hin. destruct (decide (ρ' ∈ live_roles _ δ2)); first set_solver.
        destruct (decide (ρ' ∈ dom $ ls_fuel (trace_last auxtr))); first set_solver. set_solver.
      - inversion Htrans as (?&?&?&?&?). set_solver.
      - inversion Htrans as (?&?&?&?&?). done. }
    apply elem_of_list_bind.
    assert (Hfueldom: dom δ2.(ls_fuel) = live_roles M δ2 ∪ dom (ls_fuel δ2)).
    { rewrite subseteq_union_1_L //. apply ls_fuel_dom. }

    eexists (δ2.(ls_fuel) ↾ Hfueldom); split; last first.
    { eapply enum_gmap_bounded'_spec; split =>//.
      intros ρ f Hsome. destruct ℓ as [ρ' tid' | |].
      - destruct (decide (ρ = ρ')) as [-> | Hneq].
        + inversion Htrans as [? Hbig]. destruct Hbig as (Hmap&Hleq&?&Hlim&?&?).
          destruct (decide (ρ' ∈ live_roles _ δ2)).
          * rewrite Hsome /= in Hlim.
            assert (Hlive: ρ' ∈ live_roles _ δ2) by set_solver.
            specialize (Hlim Hlive). lia.
          * unfold fuel_decr in Hleq.
            apply elem_of_dom_2 in Hmap. rewrite ls_same_doms in Hmap.
            pose proof Hsome as Hsome'. apply elem_of_dom_2 in Hsome'.
            specialize (Hleq ρ' ltac:(done) ltac:(done)).
            assert(must_decrease ρ' (Some ρ') (trace_last auxtr) δ2 (Some tid')) as Hmd; first by constructor 3.
            specialize (Hleq Hmd). rewrite Hsome /= in Hleq.
            apply elem_of_dom in Hmap as [? Heq]. rewrite Heq in Hleq.
            pose proof (max_gmap_spec _ _ _ Heq). simpl in *. lia.
        + inversion Htrans as [? Hbig]. destruct Hbig as (Hmap&?&Hleq'&?&Hnew&?).
          destruct (decide (ρ ∈ dom $ ls_fuel (trace_last auxtr))) as [Hin|Hnotin].
          * assert (Hok: oleq (ls_fuel δ2 !! ρ) (ls_fuel (trace_last auxtr) !! ρ)).
            { unfold fuel_must_not_incr in *.
              assert (ρ ∈ dom $ ls_fuel (trace_last auxtr)) by SS.
              specialize (Hleq' ρ ltac:(done) ltac:(congruence)) as [Hleq'|Hleq'] =>//. apply elem_of_dom_2 in Hsome. set_solver. }
            rewrite Hsome in Hok. destruct (ls_fuel (trace_last auxtr) !! ρ) as [f'|] eqn:Heqn; last done.
            pose proof (max_gmap_spec _ _ _ Heqn). simpl in *. lia.
          * assert (Hok: oleq (ls_fuel δ2 !! ρ) (Some (LM.(lm_fl) δ2))).
            { apply Hnew. apply elem_of_dom_2 in Hsome. set_solver. }
            rewrite Hsome in Hok. simpl in Hok. lia.
      - inversion Htrans as [? [? [Hleq [Hincl Heq]]]]. specialize (Hleq ρ).
        assert (ρ ∈ dom $ ls_fuel (trace_last auxtr)) as Hin.
        { apply elem_of_dom_2 in Hsome. set_solver. }
        specialize (Hleq Hin ltac:(done)) as [Hleq|Hleq].
        + rewrite Hsome in Hleq. destruct (ls_fuel (trace_last auxtr) !! ρ) as [f'|] eqn:Heqn; last done.
          pose proof (max_gmap_spec _ _ _ Heqn). simpl in *. lia.
        + apply elem_of_dom_2 in Hsome. set_solver.
      - inversion Htrans as [? [? [Hleq [Hnew Hfalse]]]]. done. }
    apply elem_of_list_bind.
    assert (Hmappingdom: dom δ2.(ls_mapping) = live_roles M δ2 ∪ dom (ls_fuel δ2)).
    { rewrite -Hfueldom ls_same_doms //. }

    exists (δ2.(ls_mapping) ↾ Hmappingdom); split; last first.
    { eapply enum_gmap_range_bounded'_spec; split=>//.
      intros ρ' tid' Hsome. unfold tids_smaller in *.
      apply locales_of_list_from_locale_from. eauto. }
    rewrite elem_of_list_singleton; f_equal.
    - destruct δ2; simpl. f_equal; apply ProofIrrelevance.
    - destruct ℓ; simpl; destruct oζ =>//; by inversion Hlab.
      Unshelve.
      + intros ??. apply make_decision.
      + intros. apply make_proof_irrel.
      + done.
      + done.
  Qed.
End finitary_simple.

(* TODO: Why do we need [LM] explicit here? *)
Definition live_rel `(LM: LiveModel Λ M) `{Countable (locale Λ)}
           (ex : execution_trace Λ) (aux : auxiliary_trace LM) :=
  live_tids (LM:=LM) (trace_last ex) (trace_last aux).

Definition sim_rel `(LM: LiveModel Λ M) `{Countable (locale Λ)}
           (ex : execution_trace Λ) (aux : auxiliary_trace LM) :=
  valid_state_evolution_fairness ex aux ∧ live_rel LM ex aux.

Definition sim_rel_with_user `(LM: LiveModel Λ M) `{Countable (locale Λ)}
           (ξ : execution_trace Λ -> finite_trace M (option (fmrole M)) -> Prop)
  (ex : execution_trace Λ) (aux : auxiliary_trace LM) :=
  sim_rel LM ex aux ∧ ξ ex (map_underlying_trace aux).

(* TODO: Maybe redefine [sim_rel_with_user] in terms of [valid_lift_fairness] *)
Lemma valid_lift_fairness_sim_rel_with_user `{LM:LiveModel Λ Mdl}
      `{Countable (locale Λ)}
      (ξ : execution_trace Λ → finite_trace Mdl (option $ fmrole Mdl) →
           Prop) extr atr :
  valid_lift_fairness
    (λ extr auxtr, ξ extr (map_underlying_trace (LM:=LM) auxtr) ∧
                   live_rel LM extr auxtr) extr atr ↔
  sim_rel_with_user LM ξ extr atr.
Proof. split; [by intros [Hvalid [Hlive Hξ]]|by intros [[Hvalid Hlive] Hξ]]. Qed.

Lemma rel_finitary_sim_rel_with_user_ξ `{LM:LiveModel Λ Mdl}
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
  Unshelve.
  - intros ??. apply make_proof_irrel.
Qed.

Lemma rel_finitary_sim_rel_with_user_sim_rel `{LM:LiveModel Λ Mdl}
      `{EqDecision (mstate LM)} `{EqDecision (mlabel LM)}
      `{Countable (locale Λ)} ξ :
  rel_finitary (sim_rel LM) → rel_finitary (sim_rel_with_user LM ξ).
Proof.
  intros Hrel. eapply rel_finitary_impl; [|done]. by intros ex aux [Hsim _].
Qed.
