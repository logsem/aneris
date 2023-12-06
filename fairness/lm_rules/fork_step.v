From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel fuel_ext resources partial_ownership.


Section ForkStep.
  Context `{LM: LiveModel G M LSI}.
  Context `{Countable G}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.


  Lemma mim_helper_fork_step tmap1 map1 (R1 R2 : gset (fmrole M))
    (fs: gmap (fmrole M) nat)
    (ζ τ_new : G)
    (Hdisj : R1 ## R2)
    (Hunioneq : R1 ∪ R2 = dom fs)
    (Hnewζ : τ_new ∉ dom tmap1)
    (Hmapping : tmap1 !! ζ = Some (dom fs))
    (Hdomincl : dom fs ⊆ dom map1)
    (Hminv: maps_inverse_match map1 tmap1)
    :
  maps_inverse_match
    (map_imap (λ ρ o, if decide (ρ ∈ R2) then Some τ_new else Some o) map1) 
    (<[τ_new:=R2]> (<[ζ:=R1]> (tmap1))).
  Proof.
    intros ρ ζ'. rewrite map_lookup_imap.
    destruct (decide (ρ ∈ dom (map1))) as [Hin|Hin].
    + apply elem_of_dom in Hin as [ζ'' Hρ]. rewrite Hρ. simpl.
      destruct (decide (ρ ∈ R2)) as [Hin'|Hin'].
      * split.
        -- intros. simplify_eq. rewrite lookup_insert. eauto.
        -- intros (ks & Hlk & H'). destruct (decide (ζ' = τ_new)); first congruence.
           rewrite lookup_insert_ne // in Hlk. exfalso.
           assert (ρ ∈ dom fs).
           { set_unfold. naive_solver. }
           destruct (decide (ζ = ζ')); simplify_eq.
           ** rewrite lookup_insert in Hlk. set_unfold.
              naive_solver.
           ** rewrite lookup_insert_ne // in Hlk.
              assert (ζ = ζ'); last done.
              { eapply (maps_inverse_bij _ _ _ _ ks); by eauto. }
      * split.
        -- intros ?. simplify_eq.
           specialize (Hminv ρ ζ').
           apply Hminv in Hρ as (?&?&?).
           destruct (decide (ζ' = τ_new)).
           { simplify_eq. apply not_elem_of_dom in Hnewζ.
             simpl in Hnewζ. rewrite -> Hnewζ in *. congruence. }
           destruct (decide (ζ' = ζ)).
           { simplify_eq. assert (ρ ∈ R1); first set_solver.
             exists R1. rewrite lookup_insert_ne // lookup_insert //. }
           rewrite lookup_insert_ne // lookup_insert_ne //. eauto.
        -- intros (ks&Hin&?).
           destruct (decide (ζ' = τ_new)).
           { simplify_eq. rewrite lookup_insert in Hin. set_solver. }
           rewrite lookup_insert_ne // in Hin.
           destruct (decide (ζ' = ζ)).
           { simplify_eq. rewrite lookup_insert // in Hin.
             f_equal. simplify_eq.
             assert (map1 !! ρ = Some ζ).
             { eapply Hminv. eexists _. split; eauto. set_unfold; naive_solver. }
             congruence. }
           rewrite lookup_insert_ne // in Hin.
           assert (map1 !! ρ = Some ζ').
           { eapply Hminv. eexists _. split; eauto. }
           congruence.
    + apply not_elem_of_dom in Hin. rewrite Hin /=. split; first done.
      intros (?&Hin'&?).
      apply not_elem_of_dom in Hin.
      destruct (decide (ζ' = τ_new)).
      { simplify_eq. rewrite lookup_insert in Hin'. simplify_eq.
        set_unfold; naive_solver. }
      rewrite lookup_insert_ne // in Hin'.
      destruct (decide (ζ' = ζ)).
      { simplify_eq. rewrite lookup_insert // in Hin'. simplify_eq.
        set_unfold; naive_solver. }
      rewrite lookup_insert_ne // in Hin'.
      assert (map1 !! ρ = Some ζ').
      { eapply Hminv. eauto. }
      apply not_elem_of_dom in Hin. congruence.
  Qed.

  Lemma actual_update_fork_split_gen R1 R2 fs (δ1: LM) ζ τ_new
    (Hdisj: R1 ## R2):
    fs ≠ ∅ ->
    R1 ∪ R2 = dom fs ->
    fuel_reorder_preserves_LSI (LSI := LSI) ->
    τ_new ∉ dom (ls_tmap δ1 (LM := LM)) ->
    has_fuels_S ζ fs -∗ model_state_interp δ1 ==∗
      ∃ δ2, has_fuels τ_new (fs ⇂ R2) ∗ has_fuels ζ (fs ⇂ R1) ∗
            (partial_mapping_is {[ τ_new := ∅ ]} -∗ frag_mapping_is {[ τ_new := ∅ ]}) ∗
            model_state_interp δ2 ∗ 
            ⌜lm_ls_trans LM δ1 (Silent_step ζ) δ2⌝ ∗
            ⌜ ls_tmap δ2 = (<[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1 (LM := LM)))) ⌝. 
  Proof.
    iIntros (Hnemp Hunioneq PRES Hnewζ) "Hf Hmod".
    unfold has_fuels_S.
    simpl in *.
    iDestruct (has_fuel_fuel with "Hf Hmod") as %Hfuels.
    (* iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hts. *)
    iDestruct "Hmod" as (FR) "(Haf&Ham&HFR&Hamod&%HFR)".
    (* pose Hlocincl := locales_of_list_step_incl _ _ _ _ _ Hstep. *)
    iMod (update_has_fuels_no_step_no_change ζ (S <$> fs) fs with "Hf Haf Ham") as "(Haf&Hf&Ham)".
    { intros contra. apply fmap_empty_inv in contra. set_solver. }
    { rewrite dom_fmap_L //. }
    iDestruct "Hf" as "(Hf & Hfuels)".
    iDestruct (frag_mapping_same with "Ham Hf") as %Hmapping.
    iMod (update_mapping_new_locale ζ τ_new _ R1 R2 with "Ham Hf") as "(Ham&HR1&HR2)"; eauto.

    set new_mapping := (map_imap (λ ρ o,
                                 if decide (ρ ∈ R2) then Some $ τ_new else Some o)
                                (ls_mapping δ1)).
    set new_fuels := (map_imap (λ ρ o,
                              if decide (ρ ∈ R1 ∪ R2) then Some (o - 1)%nat else Some o)
                             (ls_fuel δ1)). 
    set new_tmap := <[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1)). 

    assert (Hsamedoms: dom new_mapping = dom new_fuels).
    { rewrite !map_imap_dom_eq; first by rewrite ls_same_doms.
      - by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)).
      - by intros ρ??; destruct (decide (ρ ∈ R2)). }
    assert (Hfueldom: live_roles _ δ1 ⊆ dom new_fuels).
    { rewrite map_imap_dom_eq; first by apply ls_fuel_dom.
      - by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)). }

    assert (∀ ρ: fmrole M, ρ ∈ dom new_fuels
    ↔ (∃ (τ : G) (R : gset (fmrole M)), new_tmap !! τ = Some R ∧ ρ ∈ R)) as TMAP2_DOM.
    { intros.
      rewrite map_imap_dom_eq. 
      2: { intros. by destruct decide. }
      rewrite -ls_same_doms. 
      rewrite /new_tmap. do 2 setoid_rewrite lookup_insert_Some.
      split.
      + intros [g Mρ]%elem_of_dom.
        apply (ls_mapping_tmap_corr (LM := LM)) in Mρ as (R & TMg & INρ). 
        destruct (decide (ρ ∈ R2)).
        { exists τ_new, R2. tauto. }
        destruct (decide (g = τ_new)) as [-> | ?].
        * destruct Hnewζ. eapply elem_of_dom; eauto.
        * destruct (decide (ζ = g)).
          ** subst ζ. assert (R = dom fs) as -> by congruence.
             exists g, R1. set_solver.
          ** exists g, R. set_solver.
      + intros (τ & R & COND & Rρ).
        eapply elem_of_dom. 
        destruct COND as [[-> <-] | [NEQ COND]].
        * exists ζ. eapply ls_mapping_tmap_corr.
          eexists. split; eauto. set_solver.
        * exists τ. destruct COND as [[<- <-] | [NEQ' TMτ]].
          ** eapply ls_mapping_tmap_corr.
             eexists. split; eauto. set_solver.
          ** eapply ls_mapping_tmap_corr; eauto. }
    assert (∀ (τ1 τ2 : G) (S1 S2 : gset (fmrole M)), τ1 ≠ τ2
    → new_tmap !! τ1 = Some S1
      → new_tmap !! τ2 = Some S2 → S1 ## S2) as TMAP2_DISJ.
    { intros. clear -H1 H2 H0 Hmapping Hdisj Hunioneq. 
      Local Ltac solve_disj δ1 τ1 τ2 := 
          eapply disjoint_subseteq;
          [..| eapply (ls_tmap_disj δ1 τ1 τ2 (LM := LM)); eauto];
          [apply _| ..];
          set_solver.

      Local Ltac simpl_hyp Hi := 
        rewrite lookup_insert in Hi || (rewrite lookup_insert_ne in Hi; [| done]).

      Local Ltac simpl_all_hyps H1 H2 :=
        repeat (simpl_hyp H1 || simpl_hyp H2).

      destruct (decide (τ1 = τ_new)), (decide (τ2 = τ_new)), 
        (decide (τ1 = ζ)), (decide (τ2 = ζ)).
      all: subst; try congruence.
      all: simpl_all_hyps H1 H2.
      1-8: (solve_disj δ1 ζ τ2 || solve_disj δ1 τ1 ζ || set_solver). 
      eapply (ls_tmap_disj δ1 τ1 τ2); eauto. }

    assert (Hdomincl: dom fs ⊆ dom (ls_fuel δ1)).
    { intros ρ' Hin'. rewrite elem_of_dom Hfuels; last first.
      { rewrite dom_fmap_L //. }
      rewrite lookup_fmap fmap_is_Some. by apply elem_of_dom. }

    assert (maps_inverse_match new_mapping new_tmap) as MATCH.
    { eapply mim_helper_fork_step; eauto.
      - by rewrite ls_same_doms.
      - by apply ls_mapping_tmap_corr. }

    assert (LSI (ls_under δ1) new_mapping new_fuels) as LSI'.
    { eapply PRES; [| by apply (ls_inv δ1)].
      rewrite /new_mapping. erewrite dom_imap_L; [reflexivity| ].
      intros. rewrite elem_of_dom /is_Some. split.
      - intros [? ?]. eexists. split; eauto. destruct decide; eauto.
      - intros (?&?&?). eauto. }
    erewrite <- maps_inverse_match_uniq1 with (m2 := new_mapping) in LSI'.
    3: { apply MATCH. }
    2: { apply ls_mapping_tmap_corr_impl. apply TMAP2_DISJ. }    

    iExists (build_LS_ext (ls_under δ1) _ Hfueldom _ TMAP2_DOM TMAP2_DISJ LSI' (LM := LM)).

    iModIntro.
    rewrite -Hunioneq big_sepS_union //. iDestruct "Hfuels" as "[Hf1 Hf2]".
    iSplitL "Hf2 HR2".
    { unfold has_fuels.
      rewrite dom_domain_restrict;
        [|set_solver -Hsamedoms Hsamedoms Hfueldom Hdomincl].
      iFrame.
      iApply (big_sepS_impl with "Hf2"). iIntros "!#" (x Hin) "(%f&%&?)".
      iExists _; iFrame. iPureIntro. rewrite map_filter_lookup_Some //. }
    iSplitL "Hf1 HR1".
    { unfold has_fuels.
      rewrite dom_domain_restrict;
        [|set_solver -Hsamedoms Hsamedoms Hfueldom Hdomincl].
      iFrame.
      iApply (big_sepS_impl with "Hf1"). iIntros "!#" (x Hin) "(%f&%&?)".
      iExists _; iFrame. iPureIntro. rewrite map_filter_lookup_Some //. }
    iSplitR; [iIntros; by iFrame | ].

    (* assert (maps_inverse_match _ (<[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1))) *)
    
    iSplitL "Ham Haf Hamod HFR".
    { iExists FR; simpl.
      rewrite build_LS_ext_spec_st build_LS_ext_spec_tmap build_LS_ext_spec_fuel.
      iFrame "Ham Hamod HFR".
      iSplit.
      - iApply (auth_fuel_is_proper with "Haf"). unfold fuel_apply.
        rewrite -leibniz_equiv_iff. intros ρ. rewrite !map_lookup_imap.
        rewrite Hunioneq dom_fmap_L difference_diag_L difference_empty_L.
        rewrite lookup_gset_to_gmap.
        destruct (decide (ρ ∈ dom (ls_fuel δ1) ∪ dom fs)) as [Hin|Hin].
        + rewrite option_guard_True //=.
          assert (Hmap: ρ ∈ dom (ls_fuel δ1)).
          { set_unfold. naive_solver. }
          destruct (decide (ρ ∈ dom fs)) as [Hinfs|Hinfs].
          * apply elem_of_dom in Hmap as [? Hinfuels]. rewrite Hinfuels /=.
            rewrite Hfuels in Hinfuels; last set_solver.
            rewrite lookup_fmap in Hinfuels.
            rewrite leibniz_equiv_iff.
            rewrite -lookup_fmap in Hinfuels.
            rewrite lookup_fmap_Some in Hinfuels.
            destruct Hinfuels as [y [<- Hinfuels]].
            rewrite Hinfuels. f_equiv. lia.
          * apply elem_of_dom in Hmap as [? Hinfuels].
            rewrite Hinfuels //.
        + rewrite option_guard_False //=.
          rewrite -> not_elem_of_union in Hin. destruct Hin as [Hin ?].
          rewrite -> not_elem_of_dom in Hin. rewrite Hin //.
      -  rewrite map_imap_dom_eq // => ρ f Hin. by destruct (decide (ρ ∈ R1 ∪ R2)). 
    }
    iSplitL.
    2: { rewrite build_LS_ext_spec_tmap. done. }
    iSplit.
    { iPureIntro. destruct (map_choose _ Hnemp) as [ρ[??]]. exists ρ.
      eapply ls_mapping_tmap_corr.
      (* apply Hminv. *)
      eexists _. split; eauto. apply elem_of_dom. eauto. }
    iSplit.
    { iPureIntro. intros ρ Hlive Hlive' Hmd. simpl. inversion Hmd; simplify_eq.
      - rewrite build_LS_ext_spec_fuel.
        rewrite map_lookup_imap.
        assert (Hin: ρ ∈ dom (ls_fuel δ1)).
        { rewrite -ls_same_doms elem_of_dom. eauto. }
        apply elem_of_dom in Hin. destruct Hin as [f' Hin'].
        rewrite Hin' /=.
        destruct (decide (ρ ∈ R1 ∪ R2)) as [Hin''|Hin''].
        { rewrite dom_fmap_L -Hunioneq in Hfuels.
          specialize (Hfuels _ Hin''). rewrite lookup_fmap Hin' in Hfuels.
          destruct (fs !! ρ); simplify_eq. simpl in Hfuels. injection Hfuels.
          intros ->. simpl. lia. }
        symmetry in Hsametid. eapply ls_mapping_tmap_corr in Hsametid as (?&?&?).
        set_unfold; naive_solver.
      - rewrite build_LS_ext_spec_fuel.
        rewrite map_lookup_imap. simpl in *. clear Hmd.
        erewrite build_LS_ext_spec_mapping in Hissome, Hneqtid.
        2, 3: by eauto.
        destruct (decide (ρ ∈ dom (ls_mapping δ1))) as [Hin|Hin]; last first.
        { apply not_elem_of_dom in Hin.
          rewrite map_lookup_imap Hin //= in Hissome. by inversion Hissome. }
        apply elem_of_dom in Hin as [ζ' Hin'].
        rewrite map_lookup_imap Hin' /= in Hneqtid.
        destruct (decide (ρ ∈ R2)) as [Hin''|Hin'']; last done.
        rewrite Hfuels; last (set_unfold; naive_solver). rewrite lookup_fmap.
        assert (Hindom: ρ ∈ dom fs); first by set_unfold; naive_solver.
        apply elem_of_dom in Hindom as [f Hindom]. rewrite Hindom /= decide_True /=; [lia|set_unfold; naive_solver]. }
    iSplit.
    { iPureIntro. intros ρ' Hρ'. simpl. left.
      rewrite build_LS_ext_spec_fuel.
      rewrite map_lookup_imap. rewrite elem_of_dom in Hρ'.
      destruct Hρ' as [f Hf]. rewrite Hf /=. destruct (decide ((ρ' ∈ R1 ∪ R2))); simpl; lia. }
    rewrite build_LS_ext_spec_fuel build_LS_ext_spec_st.
    iSplit; [simpl| done]. rewrite map_imap_dom_eq //.
    by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)).
  Qed. 

End ForkStep.


Section ForkStepTrue.
  Context `{LM: LiveModel G M LSI_True}.
  Context `{Countable G}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Lemma actual_update_fork_split R1 R2 fs (δ1: LM) ζ τ_new
    (Hdisj: R1 ## R2):
    fs ≠ ∅ ->
    R1 ∪ R2 = dom fs ->
    τ_new ∉ dom (ls_tmap δ1 (LM := LM)) ->
    has_fuels_S ζ fs -∗ model_state_interp δ1 ==∗
      ∃ δ2, has_fuels τ_new (fs ⇂ R2) ∗ has_fuels ζ (fs ⇂ R1) ∗
            (partial_mapping_is {[ τ_new := ∅ ]} -∗ frag_mapping_is {[ τ_new := ∅ ]}) ∗
            model_state_interp δ2 ∗ 
            ⌜lm_ls_trans LM δ1 (Silent_step ζ) δ2⌝ ∗
            ⌜ ls_tmap δ2 = (<[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1 (LM := LM)))) ⌝. 
  Proof.
    intros. by apply actual_update_fork_split_gen. 
  Qed. 

End ForkStepTrue.
