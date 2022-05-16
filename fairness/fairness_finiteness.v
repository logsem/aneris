From trillium.fairness Require Import fairness resources.
From trillium.prelude Require Import finitary quantifiers classical_instances.
From stdpp Require Import finite.

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
  Context `{EqDecision M}.
  Context `{EqDecision (locale Λ)}.

  Context `{HPI0: forall s x, ProofIrrel ((let '(s', ℓ) := x in M.(fmtrans) s ℓ s'): Prop) }.

  Variable model_finitary: forall s1, Finite { '(s2, ℓ) | M.(fmtrans) s1 ℓ s2 }.

  Definition enum_inner (s1: M): list (M * option M.(fmrole)) :=
    map proj1_sig (@enum _ _ (model_finitary s1)).

  Lemma enum_inner_spec (s1 s2: M) ℓ:
    M.(fmtrans) s1 ℓ s2 -> (s2, ℓ) ∈ enum_inner s1.
  Proof.
    intros H. unfold enum_inner. rewrite elem_of_list_fmap.
    exists (exist _ (s2, ℓ) H). split =>//. apply elem_of_enum.
  Qed.

  Program Definition enumerate_next (δ1: (fair_model (Λ := Λ) M)) (oζ : olocale Λ) (c': cfg Λ):
    list (fair_model M * @mlabel (fair_model (Λ := Λ) M)) :=
    '(s2, ℓ) ← (δ1.(ls_under), None) :: enum_inner δ1.(ls_under);
    fs ← enum_gmap_bounded' (live_roles _ s2) (max_gmap δ1.(ls_fuel) `max` fuel_limit s2);
    ms ← enum_gmap_range_bounded' (live_roles _ s2) (locales_of_list c'.1);
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
             ls_mapping_dom := proj2_sig ms
          |}, ℓ').
  Next Obligation.
    intros ??????????. destruct fs as [??]. by simpl.
  Qed.

  Lemma valid_state_evolution_finitary_fairness (φ: execution_trace Λ -> auxiliary_trace (fair_model M) -> Prop) :
    rel_finitary (valid_lift_fairness φ).
  Proof.
    intros extr auxtr [e' σ'] oζ.
    eapply finite_smaller_card_nat.
    eapply (in_list_finite (enumerate_next (trace_last auxtr) oζ (e',σ'))).
    intros [δ2 ℓ] [[Hlab [Htrans Hsmall]] ?].
    unfold enumerate_next. apply elem_of_list_bind.
    exists (δ2.(ls_under), match ℓ with Take_step l _ => Some l | _ => None end).
    split; last first.
    { destruct ℓ as [ρ tid' | |].
      - inversion Htrans as [Htrans']. apply elem_of_cons; right. by apply enum_inner_spec.
      - apply elem_of_cons; left. f_equal. inversion Htrans as (?&?&?&?); done.
      - apply elem_of_cons; right. inversion Htrans as (?&?). by apply enum_inner_spec. }
    apply elem_of_list_bind. eexists (δ2.(ls_fuel) ↾ (ls_fuel_dom _)); split; last first.
    { eapply enum_gmap_bounded'_spec; split; first by apply ls_fuel_dom.
      intros ρ f Hsome. destruct ℓ as [ρ' tid' | |].
      - destruct (decide (ρ = ρ')) as [-> | Hneq].
        + inversion Htrans as [? Hbig]. destruct Hbig as (?&?&?&Hlim&?).
          rewrite Hsome /= in Hlim.
          assert (Hlive: ρ' ∈ live_roles _ δ2).
          { rewrite -ls_fuel_dom elem_of_dom. eauto. }
          specialize (Hlim Hlive). lia.
        + inversion Htrans as [? Hbig]. destruct Hbig as (?&?&Hleq&?&Hnew).
          destruct (decide (ρ ∈ live_roles _ (trace_last auxtr))) as [Hin|Hnotin].
          * assert (Hok: oleq (ls_fuel δ2 !! ρ) (ls_fuel (trace_last auxtr) !! ρ)).
            { apply Hleq =>//. congruence. }
            rewrite Hsome in Hok. destruct (ls_fuel (trace_last auxtr) !! ρ) as [f'|] eqn:Heqn; last done.
            rewrite <-ls_fuel_dom, elem_of_dom in Hin.
            pose proof (max_gmap_spec _ _ _ Heqn). simpl in *. lia.
          * assert (Hok: oleq (ls_fuel δ2 !! ρ) (Some (fuel_limit δ2))).
            { apply Hnew. apply elem_of_dom_2 in Hsome. rewrite -ls_fuel_dom. set_solver. }
            rewrite Hsome in Hok. simpl in *. lia.
      - inversion Htrans as [? [? [Hleq Heq]]]. specialize (Hleq ρ).
        assert (Hok: oleq (ls_fuel δ2 !! ρ) (ls_fuel (trace_last auxtr) !! ρ)).
        { apply Hleq; last done. rewrite Heq -ls_fuel_dom elem_of_dom Hsome. by eauto. }
        rewrite Hsome in Hok. destruct (ls_fuel (trace_last auxtr) !! ρ) as [f'|] eqn:Heqn; last done.
        pose proof (max_gmap_spec _ _ _ Heqn). simpl in *. lia.
      - inversion Htrans as [? [? [Hleq Hnew]]]. specialize (Hleq ρ).
        destruct (decide (ρ ∈ live_roles _ (trace_last auxtr))).
        + assert (Hok: oleq (ls_fuel δ2 !! ρ) (ls_fuel (trace_last auxtr) !! ρ)).
          { apply Hleq; done. }
          rewrite Hsome in Hok. destruct (ls_fuel (trace_last auxtr) !! ρ) as [f'|] eqn:Heqn; last done.
          pose proof (max_gmap_spec _ _ _ Heqn). simpl in *. lia.
        + assert (Hok: oleq (ls_fuel δ2 !! ρ) (Some (fuel_limit δ2))).
          { apply Hnew. apply elem_of_dom_2 in Hsome. rewrite -ls_fuel_dom. set_solver. }
          rewrite Hsome in Hok. simpl in *. lia. }
    apply elem_of_list_bind. exists (δ2.(ls_mapping) ↾ (ls_mapping_dom _)); split; last first.
    { eapply enum_gmap_range_bounded'_spec; split; first by apply ls_mapping_dom.
      intros ρ' tid' Hsome. unfold tids_smaller in *.
      apply locales_of_list_from_locale_from. eauto. }
    rewrite elem_of_list_singleton; f_equal.
    - destruct δ2; simpl. f_equal; apply ProofIrrelevance.
    - destruct ℓ; simpl; destruct oζ =>//; by inversion Hlab.
      Unshelve.
      + intros ??. apply make_decision.
      + intros. apply make_proof_irrel.
  Qed.
End finitary.
