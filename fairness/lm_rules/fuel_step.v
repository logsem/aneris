From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel resources.
From trillium.fairness.lm_rules Require Import resources_updates.


Section FuelDropStep.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Lemma mim_fuel_helper (fs: gmap (fmrole M) nat) rem ζ
    (tmap1: gmap G (gset (fmrole M)))
    map1
    (Hincl : rem ⊆ dom fs)
    (Hxdom : ∀ ρ : fmrole M, map1 !! ρ = Some ζ ↔ ρ ∈ dom (S <$> fs))
    (Hminv1 : maps_inverse_match map1 tmap1):
  maps_inverse_match
    (filter (λ '(k, _), k ∈ (dom map1 ∪ dom fs) ∖ rem) map1)
    (<[ζ:=dom fs ∖ rem]> tmap1).
  Proof.
    intros ρ ζ'. split.
    + intros [Hlk Hin]%map_filter_lookup_Some. destruct (decide (ζ' = ζ)) as [->|Hneq].
      * rewrite lookup_insert. eexists; split=>//.
        set_solver.
      * rewrite lookup_insert_ne //. by eapply Hminv1.
    + intros Hin. destruct (decide (ζ' = ζ)) as [->|Hneq].
      * rewrite lookup_insert in Hin. apply map_filter_lookup_Some.
        destruct Hin as (?&?&?). simplify_eq. split; last set_solver.
        apply Hxdom. rewrite dom_fmap. set_solver.
      * rewrite lookup_insert_ne // -Hminv1 in Hin. apply map_filter_lookup_Some; split=>//.
        apply elem_of_difference; split.
        ** apply elem_of_dom_2 in Hin. set_solver.
        ** assert (ρ ∉ dom fs); last set_solver.
           rewrite dom_fmap_L in Hxdom.
           intros contra%Hxdom. congruence.
  Qed. 

  Lemma fuel_step_ls_tmap_dom (δ: LiveState G M LSI) ρ rem (fs: gmap (fmrole M) nat) (ζ: G)
    (LOOKUP: ls_tmap δ !! ζ = Some (dom fs))
    (REM_INCL: rem ⊆ dom fs)
    :
    ρ ∈ dom (ls_mapping δ) ∖ rem ↔
    ∃ τ R, <[ζ:=dom fs ∖ rem]> (ls_tmap δ) !! τ = Some R ∧ ρ ∈ R.
  Proof.
    setoid_rewrite lookup_insert_Some.
    rewrite elem_of_difference.
    pose proof (ls_mapping_tmap_corr δ) as Hminv1. 
    assert (dom fs ⊆ dom (ls_mapping δ)) as INCL. 
    { apply elem_of_subseteq. intros ρ' [f IN]%elem_of_dom.              
      red in Hminv1. eapply elem_of_dom.
      red. exists ζ. apply Hminv1. eexists. split; eauto.
      eapply elem_of_dom. set_solver. }
    split.
    - intros [[τ L]%elem_of_dom Nr].
      specialize (proj1 (Hminv1 _ _) L) as (R & TM & IN). 
      exists τ. destruct (decide (τ = ζ)) as [-> | ?].
      + exists (dom fs ∖ rem). split; [| set_solver]. tauto. 
      + exists R. split; auto.
    - intros (τ & R & [[[-> <-] | [? ?]] IN]).
      + set_solver.
      + red in Hminv1.
        split.
        * apply elem_of_dom. exists τ. apply Hminv1. eauto.
        * eapply not_elem_of_weaken; eauto.
          pose proof (ls_tmap_disj _ _ _ _ _ H0 LOOKUP H1).
          set_solver.
  Qed.

  Let tmap_disj (tmap: gmap G (gset (fmrole M))) := 
    forall (τ1 τ2 : G) (S1 S2 : gset (fmrole M)),
      τ1 ≠ τ2 → tmap !! τ1 = Some S1 → tmap !! τ2 = Some S2 → S1 ## S2. 
    
  Lemma tmap_update_subset_disjoint (tmap tmap': gmap G (gset (fmrole M)))
        (DISJ: tmap_disj tmap)
        (SUB: forall τ S', tmap' !! τ = Some S' -> exists S, tmap !! τ = Some S /\ S' ⊆ S):
    tmap_disj tmap'.
  Proof. 
    red. intros ????? L1 L2.
    pose proof (SUB _ _ L1) as (S1'&?&?). pose proof (SUB _ _ L2) as (S2'&?&?).
    eapply disjoint_subseteq; eauto.
    apply _.
  Qed.

  Lemma map_filter_diff_simpl (m: gmap (fmrole M) G) (R: gset (fmrole M)):
    filter (fun '(k, _) => k ∈ dom m ∖ R) m = filter (fun '(k, _) => k ∉ R) m.
  Proof. 
    apply map_filter_ext. intros.
    rewrite elem_of_difference elem_of_dom. set_solver. 
  Qed.

  Lemma TMAP'_ALT: 
    forall (δ1: lm_ls LM) ζ Rζ rem, ls_tmap δ1 !! ζ = Some Rζ -> rem ⊆ Rζ -> <[ζ:=Rζ ∖ rem]> (ls_tmap δ1) = (λ rs, rs ∖ rem) <$> (ls_tmap δ1). 
  Proof. 
    intros * TMζ Hincl. apply map_eq. intros g.
    rewrite lookup_fmap.
    destruct (ls_tmap δ1 !! g) eqn:TMg.
    2: { simpl. apply not_elem_of_dom_1. rewrite dom_insert.
         apply not_elem_of_union. split.
         2: { intros [??]%elem_of_dom. congruence. }
         apply not_elem_of_singleton. intros ->. congruence. }
    simpl. rewrite lookup_insert_Some.
    destruct (decide (ζ = g)).
    - left. subst. split; eauto. congruence.
    - right. split; auto. rewrite TMg. f_equal.
      symmetry. apply difference_disjoint_L.
      eapply disjoint_subseteq; [| reflexivity | apply Hincl| ].
      { apply _. }
      symmetry. eapply (ls_tmap_disj δ1); eauto. 
  Qed. 

  Lemma actual_update_no_step_enough_fuel_drop
  (δ1: LM) rem
  (* c1 c2 *)
  s fs ζ:
    (dom fs ≠ ∅) ->
    (live_roles _ s) ∩ rem = ∅ →
    rem ⊆ dom fs →
    fuel_drop_preserves_LSI s rem (LSI := LSI) ->
    (* locale_step c1 (Some ζ) c2 -> *)
    has_fuels_S ζ fs -∗ 
    partial_model_is s -∗ 
    model_state_interp δ1
    ==∗ ∃ δ2,
        ⌜ lm_ls_trans LM δ1 (Silent_step ζ) δ2 ⌝ ∗
        has_fuels ζ (fs ⇂ (dom fs ∖ rem)) ∗
        partial_model_is s ∗ 
        model_state_interp δ2 ∗
        ⌜ ls_tmap δ2 = <[ζ:=dom fs ∖ rem]> (ls_tmap δ1) ⌝. 
  Proof.
    iIntros "%HnotO %Holdroles %Hincl %PRES Hf ST Hmod".
    (* destruct c2 as [tp2 σ2]. *)
    destruct (set_choose_L _ HnotO) as [??].
    iDestruct (has_fuel_in with "Hf Hmod") as %Hxdom; eauto.
    iDestruct (has_fuel_fuel with "Hf Hmod") as "%Hfuel"; eauto.
    (* iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hζs. *)
    pose proof (ls_inv δ1) as LSI1. 
    iDestruct "Hmod" as "(%FR & Hfuel & Hamapping & HFR & Hmodel & %HFR)".
    iAssert (⌜ ls_tmap δ1 !! ζ = Some (dom fs) ⌝)%I as %TMAP1.
    { iDestruct "Hf" as "[MAP _]". simpl.
      rewrite dom_fmap. 
      iApply (frag_mapping_same with "Hamapping MAP"). }
    unfold has_fuels_S.
    simpl in *.

    set new_dom := ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem).
    set new_mapping := ls_mapping δ1 ⇂ new_dom.

    assert (dom (fuel_apply (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs) (ls_fuel δ1)
                   ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem)) = new_dom) as Hnewdom.
    { rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap //.
      intros ρ0 _ Hindom.
      case_decide as Hninf; [by apply elem_of_dom|].
      apply elem_of_difference in Hindom as [Hin1 ?].
      apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
      exfalso. apply Hninf. apply elem_of_dom in Hin2 as [f ?].
      eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
      apply elem_of_difference; split =>//. by eapply elem_of_dom_2. }

    assert (Hsamedoms: dom new_mapping =
                       dom (fuel_apply (fs ⇂ (dom fs ∖ rem))
                                       (ls_fuel δ1)
                                       ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem))).
    { rewrite /new_mapping /new_dom. unfold fuel_apply.
      assert (dom fs ⊆ dom δ1.(ls_fuel)) as Hdom_le.
      { intros ρ Hin. rewrite elem_of_dom Hfuel; last set_solver.
        apply elem_of_dom in Hin as [? Hin]. rewrite lookup_fmap Hin //=. }
      rewrite map_imap_dom_eq; last first.
      { intros ρ _ Hin. rewrite dom_gset_to_gmap in Hin.
        case_decide; [by apply elem_of_dom|].
        apply elem_of_dom. set_solver +Hin Hdom_le. }
      rewrite dom_domain_restrict ?dom_gset_to_gmap ?ls_same_doms //.
      set_solver +Hdom_le. }

    iAssert (⌜ ls_under δ1 = s ⌝)%I as "%ST_EQ".
    { iApply (model_agree with "Hmodel ST"). }

    assert (Hfueldom: live_roles _ δ1 ⊆
     dom (fuel_apply (fs ⇂ (dom fs ∖ rem))
                     (ls_fuel δ1)
                     ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem))).
    { rewrite /fuel_apply Hnewdom.
      intros ρ Hin. apply elem_of_difference; split;
        [apply ls_fuel_dom in Hin; set_solver +Hin|
          set_solver -Hnewdom Hsamedoms]. }
    iMod (update_has_fuels_no_step ζ (S <$> fs) (fs ⇂ (dom fs ∖ rem)) with "[Hf] [Hfuel] [Hamapping]") as "(Hafuels&Hfuels&Hamapping)" =>//.
    { rewrite -dom_empty_iff_L. set_solver -Hnewdom Hsamedoms Hfueldom. }
    { rewrite dom_domain_restrict; set_solver -Hnewdom Hsamedoms Hfueldom. }
    rewrite dom_domain_restrict; [| set_solver]. 
    iModIntro. 

    pose proof (ls_mapping_tmap_corr δ1) as Hminv1. 
    assert (dom fs ⊆ dom (ls_mapping δ1)) as INCL. 
    { apply elem_of_subseteq. intros ρ' [f IN]%elem_of_dom.              
      red in Hminv1. eapply elem_of_dom.
      red. exists ζ. apply Hminv1. eexists. split; eauto.
      eapply elem_of_dom. set_solver. }
    assert (new_dom = dom (ls_mapping δ1) ∖ rem) as NEW_DOM. 
    { rewrite /new_dom.
      apply set_eq. intros.
      pose proof (ls_same_doms δ1). 
      destruct (decide (x ∈ rem)); [set_solver| ].      
      destruct (decide (x ∈ dom (ls_mapping δ1))); set_solver. }
    assert (maps_inverse_match new_mapping (<[ζ:=dom fs ∖ rem]>
      (ls_tmap δ1)
           )) as MATCH.
    { clear -Hxdom Hminv1 Hincl.
      subst new_mapping new_dom. 
      rewrite -ls_same_doms.
      apply mim_fuel_helper; auto. }

    (* TODO: doing this explicitly to avoid saving explicit proof terms
       (parameters of build_LS_ext)
       which otherwise critically slow down subsequent proofs *)
    assert ( ∀ (τ1 τ2 : G) (S1 S2 : gset (fmrole M)),
               τ1 ≠ τ2
               → <[ζ:=dom fs ∖ rem]> (ls_tmap δ1) !! τ1 = Some S1
               → <[ζ:=dom fs ∖ rem]> (ls_tmap δ1) !! τ2 = Some S2 → S1 ## S2) as DISJ2. 
    { clear -TMAP1 tmap_disj. intros.
      eapply tmap_update_subset_disjoint.
      { red. apply (ls_tmap_disj δ1). }
      2: eauto. 
      2: apply H1. 2: apply H2.
      intros ?? L%lookup_insert_Some.
      destruct L as [[-> <-]| [? ?]].
      all: eexists; split; eauto; set_solver. }

    set (new_fuels := fuel_apply (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs)
           (ls_fuel δ1) ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem)). 
    assert ( ∀ ρ : fmrole M, ρ ∈ dom new_fuels
    ↔ (∃ (τ : G) (R : gset (fmrole M)),
         <[ζ:=dom fs ∖ rem]> (ls_tmap δ1) !! τ = Some R ∧ ρ ∈ R)) as TMAP_DOM2. 
    { intros.
      rewrite -Hsamedoms.
      rewrite /new_mapping. 
      erewrite dom_domain_restrict; [| set_solver]. 
      rewrite NEW_DOM.
      apply fuel_step_ls_tmap_dom; auto. }  

    assert (LSI δ1 (<[ζ:=dom fs ∖ rem]> (ls_tmap δ1)) new_fuels) as LSI2.
    { rewrite TMAP'_ALT; auto. 
      move PRES at bottom. red in PRES. simpl.
      rewrite ST_EQ. eapply PRES.
      rewrite -ST_EQ. apply δ1. }
      
    fold new_fuels in Hfueldom. 
    iExists (build_LS_ext (ls_under δ1) _ Hfueldom (<[ζ:=dom fs ∖ rem]> (ls_tmap δ1)) TMAP_DOM2 DISJ2 LSI2).

    (* remember (build_LS_ext _ _ _ _ _ _) as δ2.  *)
    simpl.
    iSplit; last first.
    { rewrite (dom_fmap_L _ fs). iFrame "Hfuels". 
      (* rewrite /maps_inverse_match //=. *)
      rewrite /model_state_interp. 
      rewrite build_LS_ext_spec_st build_LS_ext_spec_fuel build_LS_ext_spec_tmap.
      iFrame.
      iSplitL; [| done]. 
      assert (dom fs ⊆ dom (ls_fuel $ δ1)).
      { intros ρ Hin. setoid_rewrite dom_fmap in Hxdom.
        specialize (Hxdom ρ). rewrite -ls_same_doms. apply elem_of_dom. exists ζ.
        by apply Hxdom. }
      iExists _. iFrame. 
      iSplit.
      { subst new_fuels. 
        iApply (auth_fuel_is_proper with "Hafuels"). f_equiv.
        (* rewrite dom_domain_restrict; last set_solver -Hnewdom Hsamedoms Hfueldom. *)
        replace (dom fs ∖ (dom fs ∖ rem)) with rem; [set_solver +|].
        rewrite -leibniz_equiv_iff. intros ρ. split; [set_solver -Hnewdom Hsamedoms Hfueldom|].
        intros [? [?|?]%not_elem_of_difference]%elem_of_difference =>//. }
      iPureIntro.
      (* split. *)
      (* - intros. eapply tids_dom_restrict_mapping; eauto.  *)
      - rewrite Hnewdom /new_dom. apply elem_of_equiv_empty_L. intros ρ [Hin1 Hin2]%elem_of_intersection.
        assert (ρ ∈ dom (ls_fuel δ1))
               by set_solver -Hnewdom Hsamedoms Hfueldom.
        set_solver -Hnewdom Hsamedoms Hfueldom. }
        
    iPureIntro.
    (* split; [split; [|split; [|split; [|split]]]|] =>//. *)
    repeat split; try done. 
    - eexists. apply Hxdom. by rewrite dom_fmap.
    - unfold fuel_decr. simpl.
      intros ρ' Hin Hin' Hmustdec.
      rewrite Hnewdom in Hin'.

      inversion Hmustdec; simplify_eq.
      + have Hinfs: ρ' ∈ dom (S <$> fs) by set_solver.
        rewrite map_lookup_imap Hfuel // lookup_fmap. rewrite dom_fmap in Hinfs.
        rewrite lookup_gset_to_gmap option_guard_True //=.

        pose proof Hinfs as Hinfs'. apply elem_of_dom in Hinfs' as [f Heqf].
        assert (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs !! ρ' = Some f) as Heqfilter.
        { rewrite map_filter_lookup Heqf /= option_guard_True //. set_solver -Hnewdom Hsamedoms Hfueldom Hmustdec. }
        rewrite decide_True // ?Heqfilter ?lookup_fmap ?Heqf /=; last by eapply elem_of_dom_2. lia.
      + erewrite build_LS_ext_spec_mapping in Hneqtid; [| by eauto].
        rewrite /= /new_mapping map_filter_lookup in Hneqtid.
        pose proof Hin as Hin2. rewrite -ls_same_doms in Hin2. apply elem_of_dom in Hin2 as [f Hf].
        rewrite Hf /= option_guard_True // in Hneqtid.
    - intros ρ' Hin. simpl. destruct (decide (ρ' ∈ rem)) as [Hin'|Hnin'].
      + right. right. 
        split; last set_solver -Hnewdom Hsamedoms Hfueldom.
        rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap; first set_solver.
        intros ρ0 _ Hin0. 
        case_decide as Hnin; [by apply elem_of_dom|].
        apply elem_of_difference in Hin0 as [Hin1 ?].
        apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
        exfalso. apply Hnin. apply elem_of_dom in Hin2 as [f ?].
        eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
        apply elem_of_difference; split =>//. by eapply elem_of_dom_2.
      + left.
        rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=;
                      last set_solver -Hnewdom Hsamedoms Hfueldom.
        apply elem_of_dom in Hin as [f Hf].
        case_decide as Hin; [|by rewrite !Hf //=].
        apply elem_of_dom in Hin as [f' Hf']. rewrite Hf'.
        apply map_filter_lookup_Some in Hf' as [Hfs Hf'].
        rewrite Hfuel ?lookup_fmap ?Hfs /=; [lia |].
        rewrite dom_fmap; set_solver -Hnewdom Hsamedoms Hfueldom.
    - rewrite Hnewdom. assert (dom fs ⊆ dom $ ls_fuel δ1);
        last set_solver -Hnewdom Hsamedoms Hfueldom.
      intros ρ Hin. apply elem_of_dom.
      rewrite Hfuel ?dom_fmap // -elem_of_dom dom_fmap //.
    - red. rewrite build_LS_ext_spec_tmap. intros g. 
      rewrite dom_insert_L difference_union_distr_l elem_of_union.
      intros [IN| ]; [| set_solver].
      apply elem_of_dom_2 in TMAP1. set_solver.
  Qed. 

End FuelDropStep. 


Section FuelKeepStep.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

    (* model_state_interp δ1 *)
    (* ==∗ ∃ δ2, *)
    (*     ⌜ lm_ls_trans LM δ1 (Silent_step ζ) δ2 ⌝ ∗ *)
    (*     has_fuels ζ (fs ⇂ (dom fs ∖ rem)) ∗ *)
    (*     partial_model_is s ∗  *)
    (*     model_state_interp δ2 ∗ *)
    (*     ⌜ ls_tmap δ2 (LM := LM) = <[ζ:=dom fs ∖ rem]> (ls_tmap δ1 (LM := LM)) ⌝.  *)

  Lemma actual_update_no_step_enough_fuel_keep
  (δ1: LM)
  (* c1 c2 *)
  fs ζ:
    dom fs ≠ ∅ ->
    LSI_fuel_independent (LSI := LSI) ->
    (* locale_step c1 (Some ζ) c2 -> *)
    has_fuels_S ζ fs -∗
    model_state_interp δ1
    ==∗ ∃ δ2,
        ⌜ lm_ls_trans LM δ1 (Silent_step ζ) δ2 ⌝ ∗
        has_fuels ζ fs ∗
        model_state_interp δ2 ∗
        ⌜ ls_tmap δ2 = ls_tmap δ1 ⌝. 
  Proof.
    iIntros "%HnotO %PRES Hf Hmod".
    (* destruct c2 as [tp2 σ2]. *)
    destruct (set_choose_L _ HnotO) as [??].
    iDestruct (has_fuel_in with "Hf Hmod") as %Hxdom; eauto.
    iDestruct (has_fuel_fuel with "Hf Hmod") as "%Hfuel"; eauto.
    (* iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hζs. *)
    pose proof (ls_inv δ1) as LSI1. 
    iDestruct "Hmod" as "(%FR & Hfuel & Hamapping & HFR & Hmodel & %HFR)".
    iAssert (⌜ ls_tmap δ1 !! ζ = Some (dom fs) ⌝)%I as %TMAP1.
    { iDestruct "Hf" as "[MAP _]". simpl.
      rewrite dom_fmap. 
      iApply (frag_mapping_same with "Hamapping MAP"). }
    unfold has_fuels_S.
    simpl in *.

    (* set new_dom := ((dom (ls_fuel δ1) ∪ dom fs)). *)
    (* set new_mapping := ls_mapping δ1 ⇂ new_dom. *)
    (* set new_dom := dom (ls_fuel δ1). *)
    set new_mapping := ls_mapping δ1. 
    set new_fuels := fuel_apply fs (ls_fuel δ1) (dom (ls_fuel δ1) ∪ dom fs). 

    (* assert (dom (fuel_apply (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs) (ls_fuel δ1) *)
    (*                ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem)) = new_dom) as Hnewdom. *)
    (* { rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap //. *)
    (*   intros ρ0 _ Hindom. *)
    (*   case_decide as Hninf; [by apply elem_of_dom|]. *)
    (*   apply elem_of_difference in Hindom as [Hin1 ?]. *)
    (*   apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom. *)
    (*   exfalso. apply Hninf. apply elem_of_dom in Hin2 as [f ?]. *)
    (*   eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//. *)
    (*   apply elem_of_difference; split =>//. by eapply elem_of_dom_2. } *)

    (* assert (new_dom = dom (ls_mapping δ1)) as NEW_DOM.  *)
    (* { by rewrite ls_same_doms. }  *)

    pose proof (ls_mapping_tmap_corr δ1) as Hminv1. 
    assert (dom fs ⊆ dom (ls_mapping δ1)) as INCL. 
    { apply elem_of_subseteq. intros ρ' [f IN]%elem_of_dom.              
      red in Hminv1. eapply elem_of_dom.
      red. exists ζ. apply Hminv1. eexists. split; eauto.
      eapply elem_of_dom. set_solver. }

    assert (Hsamedoms: dom new_mapping = dom new_fuels).
    { rewrite /new_mapping /new_fuels.
      rewrite map_imap_dom_eq; last first.
      { intros ρ _ Hin. rewrite dom_gset_to_gmap in Hin.
        case_decide; [by apply elem_of_dom|].
        apply elem_of_dom. set_solver. }
      rewrite dom_gset_to_gmap.
      rewrite -ls_same_doms. 
      by rewrite union_comm_L subseteq_union_1_L. }

    assert (Hfueldom: live_roles _ δ1 ⊆ dom new_fuels).
    { rewrite -Hsamedoms.
      etrans; [by apply ls_mapping_dom| ].
      set_solver. }

    iMod (update_has_fuels_no_step ζ (S <$> fs) (fs) with "[Hf] [Hfuel] [Hamapping]") as "(Hafuels&Hfuels&Hamapping)" =>//.
    { rewrite -dom_empty_iff_L. set_solver. }
    { set_solver. }
    (* rewrite dom_domain_restrict; [| set_solver].  *)
    rewrite (dom_fmap_L _ fs) difference_diag_L difference_empty_L. fold new_fuels.
    rewrite insert_id; [| done]. 
    iModIntro. 

    assert (maps_inverse_match new_mapping (ls_tmap δ1)) as MATCH.
    { apply ls_mapping_tmap_corr. }

    (* TODO: doing this explicitly to avoid saving explicit proof terms
       (parameters of build_LS_ext)
       which otherwise critically slow down subsequent proofs *)
    assert ( ∀ (τ1 τ2 : G) (S1 S2 : gset (fmrole M)),
               τ1 ≠ τ2
               → (ls_tmap δ1) !! τ1 = Some S1
               → (ls_tmap δ1) !! τ2 = Some S2 → S1 ## S2) as DISJ2. 
    { apply ls_tmap_disj. }

    assert ( ∀ ρ : fmrole M, ρ ∈ dom new_fuels
    ↔ (∃ (τ : G) (R : gset (fmrole M)),
         (ls_tmap δ1) !! τ = Some R ∧ ρ ∈ R)) as TMAP_DOM2. 
    { intros.
      rewrite -ls_tmap_fuel_same_doms.
      by rewrite -Hsamedoms ls_same_doms. }

    (* iAssert (⌜ ls_under δ1 = s ⌝)%I as "%ST_EQ". *)
    (* { iApply (model_agree with "Hmodel ST"). } *)
    assert (LSI δ1 (ls_tmap δ1) new_fuels) as LSI2.
    { eapply PRES; eauto. }

    (* fold new_fuels in Hfueldom.  *)
    iExists (build_LS_ext (ls_under δ1) _ Hfueldom (ls_tmap δ1) TMAP_DOM2 DISJ2 LSI2).

    (* remember (build_LS_ext _ _ _ _ _ _) as δ2.  *)
    simpl.
    iSplit; last first.
    { iFrame "Hfuels". 
      (* rewrite /maps_inverse_match //=. *)
      rewrite /model_state_interp. 
      rewrite build_LS_ext_spec_st build_LS_ext_spec_fuel build_LS_ext_spec_tmap.
      iFrame.
      iSplitL; [| done]. 
      assert (dom fs ⊆ dom (ls_fuel $ δ1)).
      { intros ρ Hin. setoid_rewrite dom_fmap in Hxdom.
        specialize (Hxdom ρ). rewrite -ls_same_doms. apply elem_of_dom. exists ζ.
        by apply Hxdom. }      
      iExists _. iFrame. 
      iPureIntro.
      (* split. *)
      (* - intros. eapply tids_dom_restrict_mapping; eauto.  *)
      - apply elem_of_equiv_empty_L. intros ρ [Hin1 Hin2]%elem_of_intersection.
        rewrite -Hsamedoms in Hin2. rewrite /new_mapping in Hin2.
        rewrite ls_same_doms in Hin2. set_solver. }
        
    iPureIntro.
    (* split; [split; [|split; [|split; [|split]]]|] =>//. *)
    repeat split; try done. 
    - eexists. apply Hxdom. by rewrite dom_fmap.
    - unfold fuel_decr. simpl.
      intros ρ' Hin Hin' Hmustdec.
      (* rewrite Hnewdom in Hin'. *)

      inversion Hmustdec; simplify_eq.
      + have Hinfs: ρ' ∈ dom (S <$> fs) by set_solver.
        rewrite map_lookup_imap Hfuel // lookup_fmap. rewrite dom_fmap in Hinfs.
        rewrite lookup_gset_to_gmap option_guard_True //=.

        pose proof Hinfs as Hinfs'. apply elem_of_dom in Hinfs' as [f Heqf].
        assert (fs !! ρ' = Some f) as Heqfilter.
        { rewrite Heqf /= //.  }
        rewrite decide_True // ?Heqfilter ?lookup_fmap ?Heqf /=.
        { lia. }
        set_solver. 
    - intros ρ' Hin. simpl.
      left. 
      rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=;
        last set_solver -Hsamedoms Hfueldom.
      apply elem_of_dom in Hin as [f Hf].
      case_decide as Hin; [|by rewrite !Hf //=].
      apply elem_of_dom in Hin as [f' Hf'].
      rewrite Hf' Hf. simpl.
      pose proof (Hfuel ρ') as F.
      assert (ρ' ∈ dom (S <$> fs)) as DOM.
      { rewrite dom_fmap. eapply elem_of_dom; eauto. }
      specialize (F DOM).
      rewrite lookup_fmap Hf' in F. rewrite Hf in F. inversion F. lia.  
    - by rewrite -Hsamedoms ls_same_doms.
    - red. rewrite build_LS_ext_spec_tmap. set_solver.
  Qed. 
  
End FuelKeepStep.

(* TODO: remove lots of duplication between three rules *)
Section FuelStep.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI_True}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Lemma actual_update_no_step_enough_fuel
  (δ1: LM) rem
  (* c1 c2 *)
  fs ζ:
    (dom fs ≠ ∅) ->
    (live_roles _ δ1) ∩ rem = ∅ →
    rem ⊆ dom fs →
    (* locale_step c1 (Some ζ) c2 -> *)
    has_fuels_S ζ fs -∗ model_state_interp δ1
    ==∗ ∃ δ2,
        ⌜ lm_ls_trans LM δ1 (Silent_step ζ) δ2 ⌝ ∗
        has_fuels ζ (fs ⇂ (dom fs ∖ rem)) ∗
        model_state_interp δ2 ∗
        ⌜ ls_tmap δ2 = <[ζ:=dom fs ∖ rem]> (ls_tmap δ1) ⌝. 
  Proof.
    iIntros "%HnotO %Holdroles %Hincl Hf Hmod".
    (* destruct c2 as [tp2 σ2]. *)
    destruct (set_choose_L _ HnotO) as [??].
    iDestruct (has_fuel_in with "Hf Hmod") as %Hxdom; eauto.
    iDestruct (has_fuel_fuel with "Hf Hmod") as "%Hfuel"; eauto.
    (* iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hζs. *)
    iDestruct "Hmod" as "(%FR & Hfuel & Hamapping & HFR & Hmodel & %HFR)".
    iAssert (⌜ ls_tmap δ1 !! ζ = Some (dom fs) ⌝)%I as %TMAP1.
    { iDestruct "Hf" as "[MAP _]". simpl.
      rewrite dom_fmap. 
      iApply (frag_mapping_same with "Hamapping MAP"). }
    unfold has_fuels_S.
    simpl in *.

    set new_dom := ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem).
    set new_mapping := ls_mapping δ1 ⇂ new_dom.

    assert (dom (fuel_apply (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs) (ls_fuel δ1)
                   ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem)) = new_dom) as Hnewdom.
    { rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap //.
      intros ρ0 _ Hindom.
      case_decide as Hninf; [by apply elem_of_dom|].
      apply elem_of_difference in Hindom as [Hin1 ?].
      apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
      exfalso. apply Hninf. apply elem_of_dom in Hin2 as [f ?].
      eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
      apply elem_of_difference; split =>//. by eapply elem_of_dom_2. }

    assert (Hsamedoms: dom new_mapping =
                       dom (fuel_apply (fs ⇂ (dom fs ∖ rem))
                                       (ls_fuel δ1)
                                       ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem))).
    { rewrite /new_mapping /new_dom. unfold fuel_apply.
      assert (dom fs ⊆ dom δ1.(ls_fuel)) as Hdom_le.
      { intros ρ Hin. rewrite elem_of_dom Hfuel; last set_solver.
        apply elem_of_dom in Hin as [? Hin]. rewrite lookup_fmap Hin //=. }
      rewrite map_imap_dom_eq; last first.
      { intros ρ _ Hin. rewrite dom_gset_to_gmap in Hin.
        case_decide; [by apply elem_of_dom|].
        apply elem_of_dom. set_solver +Hin Hdom_le. }
      rewrite dom_domain_restrict ?dom_gset_to_gmap ?ls_same_doms //.
      set_solver +Hdom_le. }
    assert (Hfueldom: live_roles _ δ1 ⊆
     dom (fuel_apply (fs ⇂ (dom fs ∖ rem))
                     (ls_fuel δ1)
                     ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem))).
    { rewrite /fuel_apply Hnewdom.
      intros ρ Hin. apply elem_of_difference; split;
        [apply ls_fuel_dom in Hin; set_solver +Hin|
          set_solver -Hnewdom Hsamedoms]. }
    iMod (update_has_fuels_no_step ζ (S <$> fs) (fs ⇂ (dom fs ∖ rem)) with "[Hf] [Hfuel] [Hamapping]") as "(Hafuels&Hfuels&Hamapping)" =>//.
    { rewrite -dom_empty_iff_L. set_solver -Hnewdom Hsamedoms Hfueldom. }
    { rewrite dom_domain_restrict; set_solver -Hnewdom Hsamedoms Hfueldom. }
    rewrite dom_domain_restrict; [| set_solver]. 
    iModIntro. 

    pose proof (ls_mapping_tmap_corr δ1 ) as Hminv1. 
    assert (dom fs ⊆ dom (ls_mapping δ1)) as INCL. 
    { apply elem_of_subseteq. intros ρ' [f IN]%elem_of_dom.              
      red in Hminv1. eapply elem_of_dom.
      red. exists ζ. apply Hminv1. eexists. split; eauto.
      eapply elem_of_dom. set_solver. }
    assert (new_dom = dom (ls_mapping δ1) ∖ rem) as NEW_DOM. 
    { rewrite /new_dom.
      apply set_eq. intros.
      pose proof (ls_same_doms δ1). 
      destruct (decide (x ∈ rem)); [set_solver| ].      
      destruct (decide (x ∈ dom (ls_mapping δ1))); set_solver. }
    assert (maps_inverse_match new_mapping (<[ζ:=dom fs ∖ rem]>
      (ls_tmap δ1)
           )) as MATCH.
    { clear -Hxdom Hminv1 Hincl.
      subst new_mapping new_dom. 
      rewrite -ls_same_doms.
      apply mim_fuel_helper; auto. }

    (* TODO: doing this explicitly to avoid saving explicit proof terms
       (parameters of build_LS_ext)
       which otherwise critically slow down subsequent proofs *)
    assert ( ∀ (τ1 τ2 : G) (S1 S2 : gset (fmrole M)),
               τ1 ≠ τ2
               → <[ζ:=dom fs ∖ rem]> (ls_tmap δ1) !! τ1 = Some S1
               → <[ζ:=dom fs ∖ rem]> (ls_tmap δ1) !! τ2 = Some S2 → S1 ## S2) as DISJ2. 
    { clear -TMAP1. intros.
      eapply tmap_update_subset_disjoint.
      { red. apply (ls_tmap_disj δ1). }
      2: eauto. 
      2: apply H1. 2: apply H2.
      intros ?? L%lookup_insert_Some.
      destruct L as [[-> <-]| [? ?]].
      all: eexists; split; eauto; set_solver. }

    assert ( ∀ ρ : fmrole M, ρ ∈ dom
        (fuel_apply (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs)
           (ls_fuel δ1) ((dom (ls_fuel δ1) ∪ dom fs) ∖ rem))
    ↔ (∃ (τ : G) (R : gset (fmrole M)),
         <[ζ:=dom fs ∖ rem]> (ls_tmap δ1) !! τ = Some R ∧ ρ ∈ R)) as TMAP_DOM2. 
    { intros.
      rewrite -Hsamedoms.
      rewrite /new_mapping. 
      erewrite dom_domain_restrict; [| set_solver]. 
      rewrite NEW_DOM.
      apply fuel_step_ls_tmap_dom; auto. }

    (* assert (forall s m f, LSI_True s m f) as mk_LT. *)
    (* { intros. rewrite /LSI_True.  *)

    iExists (build_LS_ext (ls_under δ1) _ Hfueldom (<[ζ:=dom fs ∖ rem]> (ls_tmap δ1)) TMAP_DOM2 DISJ2 _).
    Unshelve.
    2: { done. }

    (* remember (build_LS_ext _ _ _ _ _ _) as δ2.  *)
    simpl.
    iSplit; last first.
    { rewrite (dom_fmap_L _ fs). iFrame "Hfuels". 
      (* rewrite /maps_inverse_match //=. *)
      rewrite /model_state_interp. 
      rewrite build_LS_ext_spec_st build_LS_ext_spec_fuel build_LS_ext_spec_tmap.
      iFrame.
      iSplitL; [| done]. 
      assert (dom fs ⊆ dom (ls_fuel $ δ1)).
      { intros ρ Hin. setoid_rewrite dom_fmap in Hxdom.
        specialize (Hxdom ρ). rewrite -ls_same_doms. apply elem_of_dom. exists ζ.
        by apply Hxdom. }
      iExists _. iFrame. 
      iSplit.
      { iApply (auth_fuel_is_proper with "Hafuels"). f_equiv.
        (* rewrite dom_domain_restrict; last set_solver -Hnewdom Hsamedoms Hfueldom. *)
        replace (dom fs ∖ (dom fs ∖ rem)) with rem; [set_solver +|].
        rewrite -leibniz_equiv_iff. intros ρ. split; [set_solver -Hnewdom Hsamedoms Hfueldom|].
        intros [? [?|?]%not_elem_of_difference]%elem_of_difference =>//. }
      iPureIntro.
      (* split. *)
      (* - intros. eapply tids_dom_restrict_mapping; eauto.  *)
      - rewrite Hnewdom /new_dom. apply elem_of_equiv_empty_L. intros ρ [Hin1 Hin2]%elem_of_intersection.
        assert (ρ ∈ dom (ls_fuel δ1))
               by set_solver -Hnewdom Hsamedoms Hfueldom.
        set_solver -Hnewdom Hsamedoms Hfueldom. }
        
    iPureIntro.
    (* split; [split; [|split; [|split; [|split]]]|] =>//. *)
    repeat split; try done. 
    - eexists. apply Hxdom. by rewrite dom_fmap.
    - unfold fuel_decr. simpl.
      intros ρ' Hin Hin' Hmustdec.
      rewrite Hnewdom in Hin'.

      inversion Hmustdec; simplify_eq.
      + have Hinfs: ρ' ∈ dom (S <$> fs) by set_solver.
        rewrite map_lookup_imap Hfuel // lookup_fmap. rewrite dom_fmap in Hinfs.
        rewrite lookup_gset_to_gmap option_guard_True //=.

        pose proof Hinfs as Hinfs'. apply elem_of_dom in Hinfs' as [f Heqf].
        assert (filter (λ '(k, _), k ∈ dom fs ∖ rem) fs !! ρ' = Some f) as Heqfilter.
        { rewrite map_filter_lookup Heqf /= option_guard_True //. set_solver -Hnewdom Hsamedoms Hfueldom Hmustdec. }
        rewrite decide_True // ?Heqfilter ?lookup_fmap ?Heqf /=; last by eapply elem_of_dom_2. lia.
      + erewrite build_LS_ext_spec_mapping in Hneqtid; [| by eauto].
        rewrite /= /new_mapping map_filter_lookup in Hneqtid.
        pose proof Hin as Hin2. rewrite -ls_same_doms in Hin2. apply elem_of_dom in Hin2 as [f Hf].
        rewrite Hf /= option_guard_True // in Hneqtid.
    - intros ρ' Hin. simpl. destruct (decide (ρ' ∈ rem)) as [Hin'|Hnin'].
      + right. right. 
        split; last set_solver -Hnewdom Hsamedoms Hfueldom.
        rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap; first set_solver.
        intros ρ0 _ Hin0. 
        case_decide as Hnin; [by apply elem_of_dom|].
        apply elem_of_difference in Hin0 as [Hin1 ?].
        apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
        exfalso. apply Hnin. apply elem_of_dom in Hin2 as [f ?].
        eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
        apply elem_of_difference; split =>//. by eapply elem_of_dom_2.
      + left.
        rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=;
                      last set_solver -Hnewdom Hsamedoms Hfueldom.
        apply elem_of_dom in Hin as [f Hf].
        case_decide as Hin; [|by rewrite !Hf //=].
        apply elem_of_dom in Hin as [f' Hf']. rewrite Hf'.
        apply map_filter_lookup_Some in Hf' as [Hfs Hf'].
        rewrite Hfuel ?lookup_fmap ?Hfs /=; [lia |].
        rewrite dom_fmap; set_solver -Hnewdom Hsamedoms Hfueldom.
    - 
      rewrite Hnewdom. assert (dom fs ⊆ dom $ ls_fuel δ1);
        last set_solver -Hnewdom Hsamedoms Hfueldom.
      intros ρ Hin. apply elem_of_dom.
      rewrite Hfuel ?dom_fmap // -elem_of_dom dom_fmap //.
    - red. rewrite build_LS_ext_spec_tmap. intros g. 
      rewrite dom_insert_L difference_union_distr_l elem_of_union.
      intros [IN| ]; [| set_solver].
      apply elem_of_dom_2 in TMAP1. set_solver.
  Qed. 

End FuelStep. 
