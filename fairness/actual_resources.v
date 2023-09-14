From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel fuel_ext resources partial_ownership.


Section actual_ownership.
  Context `{LM: LiveModel G M}.
  Context `{Countable G}.
  (* Context `{EqDecision (expr Λ)}. *)
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  (* TODO: decide what to do with notations *)
  Notation "tid ↦M R" := (frag_mapping_is {[ tid := R ]}) (at level 33).
  Notation "tid ↦m ρ" := (frag_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
  Notation "ρ ↦F f" := (frag_fuel_is {[ ρ := f ]}) (at level 33).

End actual_ownership. 

Section ActualOwnershipImpl.
  Context `{LM: LiveModel G M}.
  Context `{Countable G}.
  (* Context `{EqDecision (expr Λ)}. *)
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

  (* TODO: move to upstream *)
  Lemma disjoint_subseteq:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C}
    {H2 : Union C} {H3 : Intersection C} {H4 : Difference C},
    `{Set_ A C} → ∀ X1 X2 Y1 Y2: C, X1 ⊆ Y1 -> X2 ⊆ Y2 → Y1 ## Y2 -> X1 ## X2.
  Proof. intros. set_solver. Qed.

  Lemma fuel_step_ls_tmap_dom δ ρ rem (fs: gmap (fmrole M) nat) ζ
    (LOOKUP: ls_tmap δ !! ζ = Some (dom fs))
    (REM_INCL: rem ⊆ dom fs)
    :
    ρ ∈ dom (ls_mapping δ) ∖ rem ↔
    ∃ τ R, <[ζ:=dom fs ∖ rem]> (ls_tmap δ (LM := LM)) !! τ = Some R ∧ ρ ∈ R.
  Proof.
    setoid_rewrite lookup_insert_Some.
    rewrite elem_of_difference.
    pose proof (ls_mapping_tmap_corr δ (LM := LM)) as Hminv1. 
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
        ⌜ ls_tmap δ2 (LM := LM) = <[ζ:=dom fs ∖ rem]> (ls_tmap δ1 (LM := LM)) ⌝. 
Proof.
    iIntros "%HnotO %Holdroles %Hincl Hf Hmod".
    (* destruct c2 as [tp2 σ2]. *)
    destruct (set_choose_L _ HnotO) as [??].
    iDestruct (has_fuel_in with "Hf Hmod") as %Hxdom; eauto.
    iDestruct (has_fuel_fuel with "Hf Hmod") as "%Hfuel"; eauto.
    (* iDestruct (model_state_interp_tids_smaller with "Hmod") as %Hζs. *)
    iDestruct "Hmod" as "(%FR & Hfuel & Hamapping & HFR & Hmodel & %HFR)".
    iAssert (⌜ ls_tmap δ1 (LM := LM) !! ζ = Some (dom fs) ⌝)%I as %TMAP1.
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

    pose proof (ls_mapping_tmap_corr δ1 (LM := LM)) as Hminv1. 
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
      (ls_tmap δ1 (LM := LM))
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

    iExists (build_LS_ext (ls_under δ1) _ Hfueldom (<[ζ:=dom fs ∖ rem]> (ls_tmap δ1 (LM := LM))) TMAP_DOM2 DISJ2 (LM := LM)).

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
      rewrite (build_LS_ext_spec_fuel). 
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
        rewrite build_LS_ext_spec_fuel. 
        rewrite /fuel_apply map_imap_dom_eq ?dom_gset_to_gmap; first set_solver.
        intros ρ0 _ Hin0. 
        case_decide as Hnin; [by apply elem_of_dom|].
        apply elem_of_difference in Hin0 as [Hin1 ?].
        apply elem_of_union in Hin1 as [?|Hin2]; first by apply elem_of_dom.
        exfalso. apply Hnin. apply elem_of_dom in Hin2 as [f ?].
        eapply elem_of_dom_2. rewrite map_filter_lookup_Some. split =>//.
        apply elem_of_difference; split =>//. by eapply elem_of_dom_2.
      + left.
        rewrite build_LS_ext_spec_fuel. 
        rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=;
                      last set_solver -Hnewdom Hsamedoms Hfueldom.
        apply elem_of_dom in Hin as [f Hf].
        case_decide as Hin; [|by rewrite !Hf //=].
        apply elem_of_dom in Hin as [f' Hf']. rewrite Hf'.
        apply map_filter_lookup_Some in Hf' as [Hfs Hf'].
        rewrite Hfuel ?lookup_fmap ?Hfs /=; [lia |].
        rewrite dom_fmap; set_solver -Hnewdom Hsamedoms Hfueldom.
    - rewrite build_LS_ext_spec_fuel. 
      rewrite Hnewdom. assert (dom fs ⊆ dom $ ls_fuel δ1);
        last set_solver -Hnewdom Hsamedoms Hfueldom.
      intros ρ Hin. apply elem_of_dom.
      rewrite Hfuel ?dom_fmap // -elem_of_dom dom_fmap //.
    - by rewrite build_LS_ext_spec_st.   
  Qed. 


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

  Lemma actual_update_fork_split R1 R2 (* tp1 tp2 *) fs (δ1: LM) ζ τ_new
    (* σ1 σ2 *)
    (Hdisj: R1 ## R2):
    fs ≠ ∅ ->
    R1 ∪ R2 = dom fs ->
    (* trace_last extr = (tp1, σ1) -> *)
    (* locale_step (tp1, σ1) (Some ζ) (tp2, σ2) -> *)
    (* (∃ tp1', tp2 = tp1' ++ [efork] ∧ length tp1' = length tp1) -> *)
    τ_new ∉ dom (ls_tmap δ1 (LM := LM)) ->
    has_fuels_S ζ fs -∗ model_state_interp δ1 ==∗
      ∃ δ2, has_fuels τ_new (fs ⇂ R2) ∗ has_fuels ζ (fs ⇂ R1) ∗
            (partial_mapping_is {[ τ_new := ∅ ]} -∗ frag_mapping_is {[ τ_new := ∅ ]}) ∗
            model_state_interp δ2 ∗ 
            ⌜lm_ls_trans LM δ1 (Silent_step ζ) δ2⌝ ∗
            ⌜ ls_tmap δ2 = (<[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1 (LM := LM)))) ⌝. 
  Proof.
    iIntros (Hnemp Hunioneq Hnewζ) "Hf Hmod".
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
    assert (Hsamedoms: dom (map_imap
                                (λ ρ o,
                                 if decide (ρ ∈ R2) then Some $ τ_new else Some o)
                                (ls_mapping δ1)) =
                         dom (map_imap
                             (λ ρ o,
                              if decide (ρ ∈ R1 ∪ R2) then Some (o - 1)%nat else Some o)
                             (ls_fuel δ1))
           ).
    { rewrite !map_imap_dom_eq; first by rewrite ls_same_doms.
      - by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)).
      - by intros ρ??; destruct (decide (ρ ∈ R2)). }
    assert (Hfueldom: live_roles _ δ1 ⊆ dom (map_imap
                             (λ ρ o,
                              if decide (ρ ∈ R1 ∪ R2) then Some (o - 1)%nat else Some o)
                             (ls_fuel δ1))).
    { rewrite map_imap_dom_eq; first by apply ls_fuel_dom.
      - by intros ρ??; destruct (decide (ρ ∈ R1 ∪ R2)). }

    assert (∀ ρ: fmrole M, ρ ∈ dom (map_imap
           (λ (ρ0 : fmrole M) (o : nat),
              if decide (ρ0 ∈ R1 ∪ R2) then Some (o - 1) else Some o)
           (ls_fuel δ1))
    ↔ (∃ (τ : G) (R : gset (fmrole M)),
         <[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1)) !! τ = Some R ∧ ρ ∈ R)) as TMAP2_DOM.
    { intros.
      rewrite map_imap_dom_eq. 
      2: { intros. by destruct decide. }
      rewrite -ls_same_doms. 
      do 2 setoid_rewrite lookup_insert_Some.
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
    assert ( ∀ (τ1 τ2 : G) (S1 S2 : gset (fmrole M)),
    τ1 ≠ τ2
    → <[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1)) !! τ1 = Some S1
      → <[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1)) !! τ2 = Some S2 → S1 ## S2) as TMAP2_DISJ.
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

    iExists (build_LS_ext (ls_under δ1) _ Hfueldom _ TMAP2_DOM TMAP2_DISJ (LM := LM)).

    iModIntro.
    assert (Hdomincl: dom fs ⊆ dom (ls_fuel δ1)).
    { intros ρ' Hin'. rewrite elem_of_dom Hfuels; last first.
      { rewrite dom_fmap_L //. }
      rewrite lookup_fmap fmap_is_Some. by apply elem_of_dom. }
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
    
    assert (maps_inverse_match
    (map_imap
       (λ (ρ : fmrole M) (o : G),
          if decide (ρ ∈ R2) then Some τ_new else Some o)
       (ls_mapping δ1)) (<[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1)))) as MATCH.
    { eapply mim_helper_fork_step; eauto.
      - by rewrite ls_same_doms.
      - by apply ls_mapping_tmap_corr. }

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

  Ltac by_contradiction :=
    match goal with
    | |- ?goal => destruct_decide (decide (goal)); first done; exfalso
    end.

  (* Lemma union_intersection_difference_equiv_L: *)
  (* ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} *)
  (*   {H2 : Union C} {H3 : Intersection C} {H4 : Difference C}, *)
  (*   Set_ A C → LeibnizEquiv C → *)
  (*   ∀ X Y: C, (forall y, Decision (y ∈ Y)) -> *)
  (*   X ≡ X ∩ Y ∪ X ∖ Y. *)
  (* Proof. *)
  (*   intros. apply set_equiv_subseteq. split; [| set_solver]. *)
  (*   apply elem_of_subseteq. intros x ?. *)
  (*   destruct (decide (x ∈ Y)); set_solver. *)
  (* Qed. *)

    
  Lemma actual_update_step_still_alive
        s1 s2 fs1 fs2 ρ (δ1 : LM) ζ fr1 fr_stash:
    (live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1 ->
    fr_stash ⊆ dom fs1 ->
    (live_roles _ s1) ∩ (fr_stash ∖ {[ ρ ]}) = ∅ ->
    dom fs2 ∩ fr_stash = ∅ ->
    (* locale_step (tp1, σ1) (Some ζ) (tp2, σ2) -> *)
    fmtrans _ s1 (Some ρ) s2 -> valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := LM) ->
    has_fuels ζ fs1 -∗ frag_model_is s1 -∗ model_state_interp δ1 -∗
    frag_free_roles_are fr1
    ==∗ ∃ (δ2: LM),
        ⌜lm_ls_trans LM δ1 (Take_step ρ ζ) δ2 ⌝
        ∗ has_fuels ζ fs2 ∗ frag_model_is s2 ∗ model_state_interp δ2 ∗
        frag_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪ fr_stash) ∗
        ⌜ ls_tmap δ2 (LM := LM) = (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := LM))) ⌝. 
  Proof.
    iIntros (Hfr_new Hstash_own Hstash_dis Hstash_rem Htrans Hfuelsval) "Hfuel Hmod Hsi Hfr1".

    assert (Hfsne: fs1 ≠ ∅).
    { destruct Hfuelsval as (_&_&?&_). intros ->. set_solver. }

    iDestruct (has_fuel_in with "Hfuel Hsi") as "%Hxdom"; eauto.
    iDestruct (has_fuel_fuel with "Hfuel Hsi") as %Hfuel; eauto.

    iDestruct "Hsi" as "(%FR&Hafuel&Hamapping&HFR&Hamod&%HFR)".
    iDestruct (model_agree with "Hamod Hmod") as "%Heq".

    iDestruct (free_roles_inclusion with "HFR Hfr1") as %HfrFR.

    set (new_mapping := map_imap
                    (λ ρ' _, if decide (ρ' ∈ dom $ ls_fuel δ1) then ls_mapping δ1 !! ρ' else Some ζ)
                    (gset_to_gmap 333 ((dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)))).
    assert (Hsamedoms: dom new_mapping
              =
               dom (update_fuel_resource δ1 fs1 fs2 s2)).
    { unfold update_fuel_resource, fuel_apply. rewrite -leibniz_equiv_iff.
      intros ρ'; split.
      - intros Hin. destruct (decide (ρ' ∈ dom fs2)) as [[f Hin1]%elem_of_dom|Hin1].
        + apply elem_of_dom. eexists f. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
          rewrite decide_True //. apply elem_of_dom. rewrite Hin1; eauto.
          rewrite map_imap_dom_eq dom_gset_to_gmap in Hin; first set_solver.
          intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
          apply elem_of_dom. rewrite ls_same_doms. SS.
        + rewrite map_imap_dom_eq dom_gset_to_gmap; last first.
          { intros ρ0 ? Hin0. destruct (decide (ρ0 ∈ dom fs2)) as [|Hnotin]; apply elem_of_dom; first done.
            unfold valid_new_fuelmap in Hfuelsval.
            destruct Hfuelsval as (_&_&_&_& Hdomfs2). set_solver. }

          rewrite map_imap_dom_eq dom_gset_to_gmap in Hin; first set_solver.
          intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
          apply elem_of_dom. rewrite ls_same_doms. SS.
      - intros [f Hin]%elem_of_dom. rewrite map_lookup_imap in Hin.
        rewrite map_imap_dom_eq dom_gset_to_gmap.
        + by_contradiction. rewrite lookup_gset_to_gmap option_guard_False // in Hin.
        + intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
          apply elem_of_dom. rewrite ls_same_doms. SS. }

    assert (Hnewdom: dom (update_fuel_resource δ1 fs1 fs2 s2) =
                       (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)).
    { unfold update_fuel_resource, fuel_apply. rewrite map_imap_dom_eq ?dom_gset_to_gmap //.
      intros ρ' _ Hin. destruct (decide (ρ' ∈ dom fs2)); apply elem_of_dom =>//. set_solver. }

    assert (Hfueldom: live_roles _ s2 ⊆ dom $ update_fuel_resource δ1 fs1 fs2 s2).
    { rewrite -Hsamedoms map_imap_dom_eq dom_gset_to_gmap //.
      { epose proof ls_fuel_dom as Hfueldom. intros ρ' Hin.
        destruct Hfuelsval as (?&?&?&?&?&Hdom_le).
        destruct (decide (ρ' ∈ live_roles _ δ1)).
        - apply elem_of_difference.
          split; [set_solver -Hnewdom Hsamedoms Hdom_le|].
          intros [? Habs]%elem_of_difference.
          destruct (decide (ρ' = ρ)).
          + simplify_eq. apply not_elem_of_dom in Habs.
            rewrite -> Habs in *. simpl in *. eauto.
          + apply Habs.
            assert (ρ' ∈ dom fs1 ∖ {[ρ]}); set_solver -Hnewdom Hsamedoms.
        - apply elem_of_difference.
          split; [apply elem_of_union; right; set_unfold; naive_solver|
                   set_unfold; naive_solver]. }
      intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
      apply elem_of_dom. rewrite ls_same_doms. SS. }
    (* iExists {| *)
    (*   ls_under := s2; *)
    (*   ls_fuel :=  _; *)
    (*   ls_fuel_dom := Hfueldom; *)
    (*   ls_mapping := _; *)
    (*   ls_same_doms := Hsamedoms; *)
    (* |}.  *)
    iExists (build_LS_ext s2 _ Hfueldom (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := LM))) _ _ (LM := LM)).
    (* Unshelve. *)
    iMod (update_has_fuels _ fs1 fs2 with "Hfuel Hafuel Hamapping") as "(Hafuel & Hfuel & Hmapping)".
    { set_solver. }
    { unfold valid_new_fuelmap in Hfuelsval.
      destruct Hfuelsval as (_&_&?&?& Hfs2_inf&Hfs2_sup).
      apply elem_of_equiv_empty_L => ρ0 Hin.
      apply elem_of_intersection in Hin as [Hin1 Hin2].
      apply elem_of_difference in Hin1 as [Hin11 Hin12].
      assert (ρ0 ∈ live_roles _ s2 ∖ live_roles _ s1)
             by set_solver -Hsamedoms Hnewdom.
      assert (ρ0 ∈ fr1) by set_solver -Hsamedoms Hnewdom.
      assert (ρ0 ∈ FR) by set_solver -Hsamedoms Hnewdom.
      assert (ρ0 ∉ dom (ls_fuel δ1)) by set_solver -Hsamedoms Hnewdom.
      done. }
    iMod (update_model s2 with "Hamod Hmod") as "[Hamod Hmod]".


    (* iMod (update_free_roles (live_roles M s2 ∖ live_roles M s1) *)
    (*        with "HFR Hfr1") as "[HFR Hfr2]"; [set_solver|]. *)
    pose proof (proj1 (subseteq_disjoint_union_L _ _) HfrFR) as [FR' [FR_EQ DISJ']].
    iMod (update_free_roles_strong fr1 (fr1 ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪ fr_stash) FR' with "[HFR] [Hfr1]") as "[HFR Hfr2]"; auto.
    { apply disjoint_union_l. split; [set_solver| ].
      eapply disjoint_subseteq.
      { apply _. } (* TODO: why is it needed explicitly? *)
      { apply Hstash_own. }
      { eapply subseteq_proper; [reflexivity|..].
        { apply leibniz_equiv_iff, FR_EQ. }
        set_solver. }
      rewrite -ls_same_doms in HFR.
      clear -HFR Hxdom.
      eapply disjoint_subseteq; [apply _| |reflexivity|].
      2: { symmetry. apply disjoint_intersection. apply leibniz_equiv_iff, HFR. }
      apply elem_of_subseteq. intros ? ?%Hxdom.
      eapply elem_of_dom_2; eauto. }
    { by rewrite FR_EQ. }
    
    assert (maps_inverse_match new_mapping (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := LM)))) as MATCH.
    { subst new_mapping s1 FR. 
      clear -Hxdom Hfuelsval fr1 Hfr_new FR' HFR.
      
      intros ρ' ζ'. simpl. rewrite map_lookup_imap.
      rewrite lookup_gset_to_gmap //=.
      destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hnotin].
      - rewrite option_guard_True //=. destruct (decide (ρ' ∈ dom (ls_fuel δ1))).
        + destruct (decide (ζ' = ζ)) as [->|Hneq].
          * rewrite lookup_insert. split.
            { eexists; split =>//. apply elem_of_difference in Hin as [? Hin].
              apply not_elem_of_difference in Hin as [?|?]; [|done].
              set_solver. }
            { intros (?&?&?). simplify_eq. apply Hxdom.
              destruct Hfuelsval as (?&?&?&?&?). by_contradiction.
              assert (ρ' ∈ live_roles M s2 ∖ live_roles M δ1).
              { set_solver. }
               assert (ρ' ∈ fr1).
              { set_solver. }
              assert (ρ' ∈ (fr1 ∪ FR')) by set_solver.
              assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver .
              done. }
          * rewrite lookup_insert_ne //.
            apply ls_mapping_tmap_corr.
        + split.
          * intros Htid. simplify_eq. rewrite lookup_insert. eexists; split=>//.
            set_solver.
          * assert (ρ' ∈ dom fs2) by set_solver. intros Hm. by_contradiction.
            rewrite lookup_insert_ne in Hm; last congruence.
            apply ls_mapping_tmap_corr in Hm.
            apply elem_of_dom_2 in Hm. rewrite ls_same_doms // in Hm.
      - destruct Hfuelsval as (?&?&?&?&Hinf&?). rewrite option_guard_False //=. split; first done.
        destruct (decide (ζ' = ζ)) as [->|Hneq].
        { rewrite lookup_insert //. intros (?&?&?). simplify_eq. set_solver. }
        rewrite lookup_insert_ne //.
        intros Habs%ls_mapping_tmap_corr.

        apply not_elem_of_difference in Hnotin as [Hnin|Hin].
        + apply elem_of_dom_2 in Habs. rewrite ls_same_doms in Habs. set_solver.
        + apply elem_of_difference in Hin as [Hin Hnin].
          apply Hxdom in Hin. congruence. }

    iModIntro.
    iSplit.
    { iPureIntro.
      destruct Hfuelsval as (Hlim&Hzombie&Hinfs1m&Hnewlim&Hdec&Hinf&Hsup).
      (* constructor =>//.  *)
      - constructor; simpl.
        { rewrite build_LS_ext_spec_st. by rewrite Heq //. }
        split; first by apply Hxdom; set_solver.
        split.
        { intros ? ? Hdom Hmd. inversion Hmd; clear Hmd; simplify_eq.
          + symmetry in Hsametid. rewrite -> Hxdom in Hsametid. simpl.
            unfold update_fuel_resource, fuel_apply.
            rewrite build_LS_ext_spec_fuel.
            rewrite map_lookup_imap lookup_gset_to_gmap.
            destruct (decide (ρ' ∈ live_roles M s2 ∪ dom fs2)) as [Hin|Hin].
            * rewrite option_guard_True //=.
              { destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
                ** rewrite Hfuel; last set_solver.
                   apply Hdec; [congruence|set_solver -Hsamedoms Hnewdom Hdom].
                ** exfalso. set_solver -Hsamedoms Hnewdom Hdom. }
              apply elem_of_difference; split;
                [set_solver -Hsamedoms Hnewdom Hdom|].
              apply not_elem_of_difference; right.
              apply elem_of_union in Hin as [|]; [|done].
              destruct (decide (ρ' = ρ)); simplify_eq.
              apply Hinf; set_solver -Hsamedoms Hnewdom Hdom.
            * rewrite option_guard_False //=.
              ** assert (ρ' ∈ dom fs2); set_solver -Hsamedoms Hnewdom Hdom.
              ** apply not_elem_of_difference; right; set_solver -Hsamedoms Hnewdom Hdom.
          + simpl in *. unfold update_fuel_resource, fuel_apply.
            rewrite build_LS_ext_spec_fuel.
            rewrite map_lookup_imap lookup_gset_to_gmap.

            erewrite build_LS_ext_spec_mapping in Hneqtid, Hissome.
            2, 3: by eauto.
            destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hin].
            * rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //= decide_True //= in Hneqtid.
            * apply not_elem_of_difference in Hin as [?|Hin];
                [set_solver -Hsamedoms Hnewdom Hdom|].
              apply elem_of_difference in Hin as [??].
              rewrite map_lookup_imap lookup_gset_to_gmap /= option_guard_False /= in Hissome;
                [inversion Hissome; congruence|set_solver -Hsamedoms Hnewdom Hdom].
          (* + simpl in *. rewrite Hfuel; last set_solver -Hsamedoms Hnewdom Hdom. *)
          (*   unfold update_fuel_resource, fuel_apply. *)
          (*   rewrite build_LS_ext_spec_fuel in Hnotdead, Hdom. *)
          (*   rewrite Hnewdom in Hnotdead. *)
          (*   rewrite build_LS_ext_spec_fuel. *)
          (*   rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=. *)
          (*   assert (ρ' ∈ dom fs2) by (set_solver -Hsamedoms Hnewdom Hdom). *)
          (*   rewrite decide_True; [| done]. *)
          (*   apply Hzombie =>//; [| set_solver]. *)
          (*   rewrite build_LS_ext_spec_st in Hnotalive. *)
          (*   set_solver -Hsamedoms Hnewdom Hdom. *)
    }
        split.
        + intros ? Hin.
          rewrite build_LS_ext_spec_fuel build_LS_ext_spec_st. 
          simplify_eq; simpl.

          unfold update_fuel_resource, fuel_apply.
          rewrite map_lookup_imap lookup_gset_to_gmap.
          destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hlive|Hlive].
          * rewrite option_guard_True //=.
            apply elem_of_difference in Hlive as [Hin1 Hnin].
            apply not_elem_of_difference in Hnin.
            destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
            **
              destruct (decide (ρ' = ρ)).
              { subst ρ'. destruct Hnin; [set_solver| ].
                destruct (decide (ρ ∈ live_roles M s2)).
                - tauto.
                - left. rewrite Hfuel; set_solver. }
              destruct (decide (ρ' ∈ live_roles _ δ1)); left.
               *** destruct (decide (ρ' ∈ dom fs1)).
                   { rewrite Hfuel //.
                     apply oleq_oless, Hdec; [congruence|set_solver -Hsamedoms Hnewdom]. }
                   { exfalso. set_solver -Hsamedoms Hnewdom. }
               *** assert (ρ' ∉ live_roles _ s2).
                   { by_contradiction. assert (ρ' ∈ fr1); [eapply elem_of_subseteq; eauto; set_solver -Hsamedoms Hnewdom|].
                     assert (ρ' ∈ (fr1 ∪ FR')); [eapply elem_of_subseteq; eauto; set_solver -Hsamedoms Hnewdom|set_solver -Hsamedoms Hnewdom]. }
                   assert (ρ' ∈ dom fs1) by set_solver -Hsamedoms Hnewdom.
                   rewrite Hfuel //. apply oleq_oless, Hdec; [congruence|set_solver -Hsamedoms Hnewdom].
            ** left. rewrite elem_of_dom in Hin. destruct Hin as [? ->]. simpl;lia.
          * destruct (decide (ρ' = ρ)).
            { subst. right. left. split; auto. left.               
              eapply not_elem_of_weaken; [|by apply map_imap_dom_inclusion; rewrite dom_gset_to_gmap].
              rewrite dom_gset_to_gmap //. }

            right; right; split.
            ** eapply not_elem_of_weaken; [|by apply map_imap_dom_inclusion; rewrite dom_gset_to_gmap].
               rewrite dom_gset_to_gmap //.
            ** apply not_elem_of_difference in Hlive as [?|Hlive]; [set_solver -Hsamedoms Hnewdom|].
               apply elem_of_difference in Hlive as [? Habs].
               exfalso. apply Habs.
               set_solver -Hsamedoms Hnewdom Hfueldom.
        +
          rewrite build_LS_ext_spec_fuel build_LS_ext_spec_st.
          split.
          { intros Hlive.
            
            unfold update_fuel_resource, fuel_apply.
          destruct (decide (ρ ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hnin].
          - rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
            rewrite decide_True; [by apply Hlim |set_solver -Hsamedoms Hnewdom Hfueldom].
          - exfalso; apply not_elem_of_difference in Hnin as [Hnin|Hnin].
            + assert (ρ ∉ live_roles _ δ1).
              eapply not_elem_of_weaken => //.
              { epose proof ls_fuel_dom. set_solver -Hsamedoms Hnewdom Hfueldom. }
              assert (ρ ∈ dom fs2) by set_solver -Hsamedoms Hnewdom Hfueldom. set_solver -Hsamedoms Hnewdom Hfueldom.
            + apply elem_of_difference in Hnin as [? Hnin].
              apply not_elem_of_dom in Hnin. rewrite Hnin /= in Hlim.
              by apply Hlim. }
          split.
          { intros ρ'. unfold update_fuel_resource, fuel_apply => Hin.
            rewrite map_imap_dom_eq in Hin; last first.
            { intros ρ0 _ Hin'. destruct (decide (ρ0 ∈ dom fs2)); [by apply elem_of_dom|].
              rewrite dom_gset_to_gmap elem_of_difference in Hin'.
              destruct Hin' as [Hin' ?]. apply elem_of_union in Hin' as [?|?]; [by apply elem_of_dom|done]. }
            rewrite dom_gset_to_gmap in Hin. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True /=; last set_solver -Hsamedoms Hnewdom Hfueldom.
            assert (ρ' ∈ dom fs2) by set_solver -Hsamedoms Hnewdom Hfueldom. rewrite decide_True //. apply Hnewlim. apply elem_of_difference; split =>//.
            intros contra%Hxdom%elem_of_dom_2. rewrite ls_same_doms in contra. simplify_eq. set_solver -Hsamedoms Hnewdom Hfueldom. }
          intros ρ0 Hin.
          assert (ρ0 ∉ live_roles _ δ1).
          { eapply not_elem_of_weaken; last apply ls_fuel_dom. set_solver -Hsamedoms Hnewdom Hfueldom. }
          apply elem_of_difference in Hin as [Hin1 Hnin].
          assert (ρ0 ∈ live_roles _ s2).
          { by_contradiction.
            assert (ρ0 ∈ dom fs2).
            { unfold update_fuel_resource, fuel_apply in Hin1.
              eapply elem_of_subseteq in Hin1; last apply map_imap_dom_inclusion.
              rewrite dom_gset_to_gmap in Hin1. set_solver -Hsamedoms Hnewdom Hfueldom. }
            exfalso. assert (Hinabs: ρ0 ∈ dom fs1) by set_solver -Hsamedoms Hnewdom Hfueldom.
            apply not_elem_of_dom in Hnin. rewrite Hfuel // in Hnin.
            apply elem_of_dom in Hinabs. rewrite Hnin in Hinabs. simpl in Hinabs.
            by inversion Hinabs. }
          set_solver -Hsamedoms Hnewdom Hfueldom. }

    iFrame "Hfuel Hmod Hfr2".
    iSplitL; [| rewrite build_LS_ext_spec_tmap; done]. 

    iExists _.
    rewrite build_LS_ext_spec_st build_LS_ext_spec_fuel build_LS_ext_spec_tmap.
    iFrame. all: eauto. (* TODO: find source... *)
        

    { simpl. rewrite /update_fuel_resource /fuel_apply.
      rewrite map_imap_dom_eq ?dom_gset_to_gmap.
      + iPureIntro. 
        apply elem_of_equiv_empty_L. intros ρ' [Hin1 Hin2]%elem_of_intersection.

        (* TODO: problems with elem_of_proper *)
        assert (fr1 ∖ (live_roles M s2 ∖ live_roles M s1) ∪ fr_stash ∪ FR' ≡ FR ∖ (live_roles M s2 ∖ live_roles M s1) ∪ fr_stash ∪ FR' ∩ (live_roles M s2 ∖ live_roles M s1)) as ALT.
        { set_solver. }
        rewrite ALT in Hin1.

        apply elem_of_union in Hin1 as [[Hin1 | Hin1] %elem_of_union | Hin1].
        2, 3: set_solver.
        apply elem_of_difference in Hin1 as [Hin11 Hin12].
        apply not_elem_of_difference in Hin12.
        apply elem_of_difference in Hin2 as [Hin21 Hin22].
        apply not_elem_of_difference in Hin22.
        assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver -Hsamedoms Hnewdom Hfueldom.
        assert (ρ' ∈ dom fs2) by set_solver -Hsamedoms Hnewdom Hfueldom.
        destruct Hin12 as [Hin12|Hin12]; last by (epose proof ls_fuel_dom; set_solver -Hsamedoms Hnewdom Hfueldom).
        destruct Hfuelsval as (?&?&?&?&?&?).
        assert (ρ' ∉ dom fs1); last set_solver -Hsamedoms Hnewdom Hfueldom.
        intros contra. pose proof (Hfuel _ contra) as Habs. apply elem_of_dom in contra as [? contra].
        rewrite contra in Habs. apply elem_of_dom_2 in Habs. done.
    + intros ρ' _ Hin. destruct (decide (ρ' ∈ dom fs2)) as [Hin'|].
      * apply elem_of_dom in Hin' as [? ->]. done.
      * assert (ρ' ∈ dom (ls_fuel δ1)) as Hin' by set_solver -Hsamedoms Hnewdom Hfueldom. apply elem_of_dom in Hin' as [? ->]. done. }

    Unshelve. all: eauto.
    - intros. 
      rewrite Hnewdom. setoid_rewrite lookup_insert_Some.
      rewrite -ls_same_doms. split.
      + intros [IN NIN]%elem_of_difference.
        apply not_elem_of_difference in NIN.        
        apply elem_of_union in IN as [IN | IN].
        2: set_solver. 
        apply elem_of_dom in IN as [τ' MAP].
        destruct (decide (τ' = ζ)) as [-> | NEQ].
        * destruct NIN.
           ** destruct H0. by apply Hxdom.
           ** set_solver.
        * apply (ls_mapping_tmap_corr (LM := LM)) in MAP as (?&?&?).
          set_solver.
      + intros (τ & R & PROP & IN).
        destruct PROP as [[<- <-] | [NEQ MAP]].
        * set_solver.
        * apply elem_of_difference. split.
          ** apply elem_of_union. left.
             eapply elem_of_dom. exists τ. eapply ls_mapping_tmap_corr; eauto.
          ** apply not_elem_of_difference. left.
             intros IN'%Hxdom.
             apply (ls_mapping_tmap_corr (LM := LM)) in IN' as (?&?&?).
             eapply ls_tmap_disj; eauto.
    - intros.
      assert (forall τ' S', τ' ≠ ζ -> ls_tmap δ1 (LM := LM) !! τ' = Some S' -> dom fs2 ## S') as FS2_DISJ. 
      { destruct Hfuelsval as (?&?&?&?&?&?&FS2).
        clear -Hfr_new HfrFR FS2 Hxdom HFR.  
        intros τ' S' NEQ' IN'. 
        
        intros ρ' IN1 IN2.
        move FS2 at bottom. specialize (FS2 _ IN1).
        assert (ρ' ∈ dom fs1 -> False) as NINf1. 
        { intros INf1. apply Hxdom in INf1.
          eapply (ls_mapping_tmap_corr (LM := LM)) in INf1 as (?&?&?).
          eapply ls_tmap_disj; eauto. }
        repeat rewrite elem_of_union in FS2. destruct FS2 as [[[?|?]|?]|?].
        2-4: apply NINf1; set_solver. 
        apply Hfr_new, HfrFR in H0.
        assert (ρ' ∈ dom (ls_fuel δ1)); [| set_solver].
        rewrite -ls_same_doms. eapply elem_of_dom. 
        eexists. eapply ls_mapping_tmap_corr. eauto. }
 
      destruct (decide (τ1 = ζ)), (decide (τ2 = ζ)). 
      all: subst; try congruence.
      all: simpl_all_hyps H0 H1.
      + inversion H0. subst. eapply FS2_DISJ; eauto.
      + inversion H1. subst. symmetry. eapply FS2_DISJ; eauto.
      + assert (τ1 ≠ τ2) by congruence. 
        eapply ls_tmap_disj; eauto. 
  Qed. 


End ActualOwnershipImpl.
