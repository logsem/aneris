From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel fuel_ext resources partial_ownership.


Section ModelStep.
  Context `{LM: LiveModel G M LSI_True}.
  Context `{Countable G}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.

  Ltac by_contradiction :=
    match goal with
    | |- ?goal => destruct_decide (decide (goal)); first done; exfalso
    end.

  (* TODO: remove duplication across lm_rules files *)
  Local Ltac solve_disj δ1 τ1 τ2 := 
    eapply disjoint_subseteq;
    [..| eapply (ls_tmap_disj δ1 τ1 τ2 (LM := LM)); eauto];
    [apply _| ..];
    set_solver.
  
  Local Ltac simpl_hyp Hi := 
    rewrite lookup_insert in Hi || (rewrite lookup_insert_ne in Hi; [| done]).
  
  Local Ltac simpl_all_hyps H1 H2 :=
    repeat (simpl_hyp H1 || simpl_hyp H2).

  Lemma mim_model_step_helper
    (s2 : M)
    (fs1 fs2 : gmap (fmrole M) nat)
    (ρ : fmrole M)
    (δ1 : LM)
    (ζ : G)
    (fr1 : gset (fmrole M))
    (Hfr_new : live_roles M s2 ∖ live_roles M (ls_under δ1) ⊆ fr1 ∪ dom fs1 ∩ dom fs2)
    (Hfuelsval : valid_new_fuelmap fs1 fs2 (ls_under δ1) s2 ρ (LM := LM))
    (Hxdom : ∀ ρ : fmrole M, ls_mapping δ1 !! ρ = Some ζ ↔ ρ ∈ dom fs1)
    (HFR : fr1 ∩ dom (ls_fuel δ1) = ∅)
:
  maps_inverse_match
    (update_mapping (ls_mapping δ1) ζ fs1 fs2)
    (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := LM))). 
  Proof.
    intros ρ' ζ'. simpl. rewrite map_lookup_imap.
    rewrite lookup_gset_to_gmap //=.
    destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hnotin].
    - rewrite option_guard_True //=.
      2: { by rewrite ls_same_doms. }
      destruct (decide (ρ' ∈ dom (ls_fuel δ1))).
      + rewrite decide_True; [| by rewrite ls_same_doms].
        destruct (decide (ζ' = ζ)) as [->|Hneq].
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
            assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver .
            done. }
        * rewrite lookup_insert_ne //.
          apply ls_mapping_tmap_corr.
      + rewrite ls_same_doms decide_False; [| done].  
        split.
        * intros Htid. simplify_eq.
          rewrite lookup_insert. eexists; split=>//.
          set_solver.
        * assert (ρ' ∈ dom fs2) by set_solver. intros Hm. by_contradiction.
          rewrite lookup_insert_ne in Hm; last congruence.
          apply ls_mapping_tmap_corr in Hm.
          apply elem_of_dom_2 in Hm. rewrite ls_same_doms // in Hm.
    - destruct Hfuelsval as (?&?&?&?&Hinf&?). rewrite option_guard_False //=.
      2: { by rewrite ls_same_doms. }
      split; first done.
      destruct (decide (ζ' = ζ)) as [->|Hneq].
      { rewrite lookup_insert //. intros (?&?&?). simplify_eq. set_solver. }
      rewrite lookup_insert_ne //.
      intros Habs%ls_mapping_tmap_corr.
      
      apply not_elem_of_difference in Hnotin as [Hnin|Hin].
      + apply elem_of_dom_2 in Habs. rewrite ls_same_doms in Habs. set_solver.
      + apply elem_of_difference in Hin as [Hin Hnin].
        apply Hxdom in Hin. congruence.
  Qed.

  Lemma model_step_ls_trans
  (s1 s2 : M)
  (fs1 fs2 : gmap (fmrole M) nat)
  (ρ : fmrole M)
  (δ1 : LM)
  (ζ : G)
  (fr1 : gset (fmrole M))
  (Hfr_new : live_roles M s2 ∖ live_roles M s1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2)
  (Htrans : fmtrans M s1 (Some ρ) s2)
  (Hlim : ρ ∈ live_roles M s2 → oleq (fs2 !! ρ) (Some (lm_fl LM s2)))
  (Hzombie : ρ ∉ live_roles M s2
            → ρ ∈ dom fs1 ∩ dom fs2 → oleq (fs2 !! ρ) (fs1 !! ρ))
  (Hinfs1m : ρ ∈ dom fs1)
  (Hnewlim : ∀ ρ' : fmrole M,
              ρ' ∈ dom fs2 ∖ dom fs1 → oleq (fs2 !! ρ') (Some (lm_fl LM s2)))
  (Hdec : ∀ ρ' : fmrole M, ρ ≠ ρ' → ρ' ∈ dom fs1 ∩ dom fs2 → oless (fs2 !! ρ') (fs1 !! ρ'))
  (Hinf : dom fs1 ∖ {[ρ]} ∪ live_roles M s2 ∖ live_roles M s1 ⊆ dom fs2)
  (Hsup : dom fs2
         ⊆ live_roles M s2 ∖ live_roles M s1
           ∪ (live_roles M s2 ∩ live_roles M s1) ∩ dom fs1
           ∪ dom fs1 ∖ live_roles M s1
           ∪ (live_roles M s1 ∖ live_roles M s2) ∩ dom fs1)
  (Hxdom : ∀ ρ : fmrole M, ls_mapping δ1 !! ρ = Some ζ ↔ ρ ∈ dom fs1)
  (Hfuel : ∀ ρ : fmrole M, ρ ∈ dom fs1 → ls_fuel δ1 !! ρ = fs1 !! ρ)
  (FR : gset (fmrole M))
  (HFR : FR ∩ dom (ls_fuel δ1) = ∅)
  (Heq : ls_under δ1 = s1)
  (HfrFR : fr1 ⊆ FR)
  (new_mapping := 
     (* map_imap *)
     (*               (λ (ρ' : fmrole M) (_ : nat), *)
     (*                  if decide (ρ' ∈ dom (ls_fuel δ1)) *)
     (*                  then ls_mapping δ1 !! ρ' *)
     (*                  else Some ζ) *)
     (*               (gset_to_gmap 333 *)
     (*                  ((dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) *)
     update_mapping (ls_mapping δ1) ζ fs1 fs2
  )
  (new_fuels := update_fuel_resource (ls_fuel δ1) fs1 fs2)
  (Hsamedoms : dom new_mapping = dom new_fuels)
  (Hnewdom : dom new_fuels =
            (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))
  (Hfueldom : live_roles M s2 ⊆ dom new_fuels)
  (FR' : gset (fmrole M))
  (FR_EQ : FR = fr1 ∪ FR')
  (DISJ' : fr1 ## FR')
  (MATCH : maps_inverse_match new_mapping (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := LM))))
:
    forall tmap_sd tmap_disj,
  lm_ls_trans LM δ1 (Take_step ρ ζ)
    (build_LS_ext s2 new_fuels Hfueldom
       (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := LM)))
       tmap_sd tmap_disj I (LM := LM)). 
  Proof.
    intros. 
    constructor; simpl.
    { rewrite build_LS_ext_spec_st. by rewrite Heq //. }
    split; first by apply Hxdom; set_solver.
    split.
    { intros ? ? Hdom Hmd. 
      rewrite build_LS_ext_spec_fuel. erewrite build_LS_ext_spec_fuel in *. 
      inversion Hmd; clear Hmd; simplify_eq.
      + symmetry in Hsametid. rewrite -> Hxdom in Hsametid. simpl.
        unfold update_fuel_resource, fuel_apply.
        rewrite map_lookup_imap lookup_gset_to_gmap.
        destruct (decide (ρ' ∈ live_roles M s2 ∪ dom fs2)) as [Hin|Hin].
        * rewrite option_guard_True //=.
          { destruct (decide (ρ' ∈ dom fs2)) as [Hin2|Hin2].
            ** rewrite Hfuel.
               2: { done. }
               apply Hdec; [congruence|].
               clear -Hin2 Hxdom Hsametid. 
               set_solver. 
            ** exfalso.
               clear -Hin2 Hinf Hsametid Hneqρ. set_solver. }
          apply elem_of_difference; split.
          { clear -H0. set_solver. }
          apply not_elem_of_difference; right.
          apply elem_of_union in Hin as [|]; [|done].
          destruct (decide (ρ' = ρ)); simplify_eq.
          apply Hinf.
          clear -n Hinf Hsametid Hneqρ. set_solver.
        *
          assert (ρ' ∈ dom fs2).
          { clear -Hin Hinf Hsametid Hneqρ. set_solver. }
          apply not_elem_of_union in Hin; tauto.
      + simpl in *. unfold update_fuel_resource, fuel_apply.
        rewrite map_lookup_imap lookup_gset_to_gmap.
        
        erewrite build_LS_ext_spec_mapping in Hneqtid, Hissome.
        2, 3: by eauto.
        destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hin].
        * subst new_mapping. 
          rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //= in Hneqtid.
          2: { by rewrite ls_same_doms. }
          rewrite decide_True //= in Hneqtid. 
          by rewrite ls_same_doms. 
        * apply not_elem_of_difference in Hin as [?|Hin].
          { apply not_elem_of_union in H1; tauto. } 
          apply elem_of_difference in Hin as [??].
          rewrite map_lookup_imap lookup_gset_to_gmap /= option_guard_False /= in Hissome;
            [inversion Hissome; congruence|].
          apply not_elem_of_difference. right. clear -H1 H2. set_solver. }
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
          { subst ρ'. destruct Hnin.
            { set_solver. }  
            destruct (decide (ρ ∈ live_roles M s2)).
            - tauto.
            - left. rewrite Hfuel; [| done]. 
              set_solver. }
          destruct (decide (ρ' ∈ live_roles _ δ1)); left.
          *** destruct (decide (ρ' ∈ dom fs1)).
              { rewrite Hfuel //.
                apply oleq_oless, Hdec; [congruence|]. 
                apply elem_of_intersection. split; auto. }
              { exfalso.
                clear -Hsup Hin2 e n0. 
                set_solver. }
          *** destruct (decide (ρ' ∈ live_roles _ s2)).
              { assert (ρ' ∈ fr1 ∪ dom fs1 ∩ dom fs2); [eapply elem_of_subseteq; eauto |].
                { set_solver. }
                apply elem_of_union in H0 as [H0 | H0]. 
                - assert (ρ' ∈ (fr1 ∪ FR')); [eapply elem_of_subseteq; eauto; set_solver -Hsamedoms Hnewdom| ].
                  clear -H1 Hin HFR. set_solver.
                - apply oleq_oless. rewrite Hfuel.
                  eapply Hdec; eauto. clear -H0. set_solver. }
              assert (ρ' ∈ dom fs1).
              { clear Hin1 Hnin Hsamedoms Hnewdom.
                clear tmap_disj tmap_sd. clear Hinf Hfueldom.
                clear dependent MATCH. 
                set_solver. } 
              rewrite Hfuel //. apply oleq_oless, Hdec; [congruence|].
              by apply elem_of_intersection. 
        ** left. rewrite elem_of_dom in Hin. destruct Hin as [? ->]. simpl;lia.
      * destruct (decide (ρ' = ρ)).
        { subst. right. left. split; auto. left.               
          eapply not_elem_of_weaken; [|by apply map_imap_dom_inclusion; rewrite dom_gset_to_gmap].
          rewrite dom_gset_to_gmap //. }
        
        right; right; split.
        ** eapply not_elem_of_weaken; [|by apply map_imap_dom_inclusion; rewrite dom_gset_to_gmap].
           rewrite dom_gset_to_gmap //.
        ** apply not_elem_of_difference in Hlive as [?|Hlive].
           { set_solver -Hsamedoms Hnewdom Hfueldom. }
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
            { rewrite -ls_same_doms. pose proof (ls_mapping_dom δ1) as ->. 
              clear. set_solver. }
            assert (ρ ∈ dom fs2) by set_solver -Hsamedoms Hnewdom Hfueldom. 
            set_solver -Hsamedoms Hnewdom Hfueldom.
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
      set_solver -Hsamedoms Hnewdom Hfueldom.
  Qed. 

  Lemma model_step_new_fr
  (s1 s2 : M)
  (fs1 fs2 : gmap (fmrole M) nat)
  (ρ : fmrole M)
  (δ1 : LM)
  (ζ : G)
  (fr1 fr_stash : gset (fmrole M))
  (Hfr_new : live_roles M s2 ∖ live_roles M s1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2 )
  (Hstash_own : fr_stash ⊆ dom fs1)
  (Hstash_dis : live_roles M s1 ∩ (fr_stash ∖ {[ρ]}) = ∅)
  (Hstash_rem : dom fs2 ∩ fr_stash = ∅)
  (Hfuelsval : valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := LM))
  (* (Hfsne : fs1 ≠ ∅) *)
  (Hxdom : ∀ ρ : fmrole M, ls_mapping δ1 !! ρ = Some ζ ↔ ρ ∈ dom fs1)
  (Hfuel : ∀ ρ : fmrole M, ρ ∈ dom fs1 → ls_fuel δ1 !! ρ = fs1 !! ρ)
  (FR : gset (fmrole M))
  (HFR : FR ∩ dom (ls_fuel δ1) = ∅)
  (Heq : ls_under δ1 = s1)
  (HfrFR : fr1 ⊆ FR)
  (FR' : gset (fmrole M))
  (FR_EQ : FR = fr1 ∪ FR')
  (DISJ' : fr1 ## FR')
  :
  (fr1 ∖ (live_roles M s2 ∖ (live_roles M s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash ∪ FR')
   ∩ dom (update_fuel_resource (ls_fuel δ1) fs1 fs2) = ∅.
  Proof. 
    simpl. rewrite /update_fuel_resource /fuel_apply.
    rewrite map_imap_dom_eq ?dom_gset_to_gmap.
    2: { intros ρ' _ Hin. destruct (decide (ρ' ∈ dom fs2)) as [Hin'|].
         { apply elem_of_dom in Hin' as [? ->]. done. }
         assert (ρ' ∈ dom (ls_fuel δ1)) as Hin' by set_solver. 
         apply elem_of_dom in  Hin' as [? ->]. done. }

    apply elem_of_equiv_empty_L. intros ρ' [Hin1 Hin2]%elem_of_intersection.
      
    (* TODO: problems with elem_of_proper *)
    assert (fr1 ∖ (live_roles M s2 ∖ (live_roles M s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash ∪ FR' ≡ FR ∖ (live_roles M s2 ∖ (live_roles M s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash ∪ FR' ∩ (live_roles M s2 ∖ (live_roles M s1 ∪ dom fs1 ∩ dom fs2))) as ALT.
    { set_solver -Hin1 Hin2. }
    rewrite ALT in Hin1. clear ALT. 
    
    apply elem_of_union in Hin1 as [[Hin1 | Hin1] %elem_of_union | Hin1].
    2, 3: set_solver.
    apply elem_of_difference in Hin1 as [Hin11 Hin12].
    apply not_elem_of_difference in Hin12.
    apply elem_of_difference in Hin2 as [Hin21 Hin22].
    apply not_elem_of_difference in Hin22.
    assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver.
    assert (ρ' ∈ dom fs2) by set_solver.
    destruct Hin12 as [Hin12|Hin12].
    2: { eapply H0. apply elem_of_union in Hin12 as [? | ?].
         - eapply ls_fuel_dom. set_solver.
         - destruct H0. rewrite -ls_same_doms.
           apply elem_of_dom. eexists. apply Hxdom. clear -H2. set_solver. } 
    destruct Hfuelsval as (?&?&?&?&?&?).
    assert (ρ' ∉ dom fs1).
    2: { eapply H0. eapply ls_fuel_dom. set_solver -Hin11 Hin21 Hin22. }
    intros contra. pose proof (Hfuel _ contra) as Habs. apply elem_of_dom in contra as [? contra].
    rewrite contra in Habs. apply elem_of_dom_2 in Habs. done.
  Qed.
    
  (* (* TODO: refactor this definition? *) *)
  (* (* TODO: move *) *)
  (* Definition update_mapping (δ1: lm_ls LM) ζ (fs1 fs2: gmap (fmrole M) nat) :=  *)
  (*   map_imap (λ ρ' _, if decide (ρ' ∈ dom $ ls_fuel δ1) then ls_mapping δ1 !! ρ' else Some ζ) *)
  (*     (gset_to_gmap 333 ((dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))). *)

  Lemma actual_update_step_still_alive
        s1 s2 fs1 fs2 ρ (δ1 : LM) ζ fr1 fr_stash:
    (live_roles _ s2 ∖ live_roles _ s1) ⊆ fr1 ∪ dom fs1 ∩ dom fs2 ->
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
        frag_free_roles_are (fr1 ∖ (live_roles _ s2 ∖ (live_roles _ s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash) ∗
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

    set (new_mapping := update_mapping (ls_mapping δ1) ζ fs1 fs2).
    set (new_fuels := update_fuel_resource (ls_fuel δ1) fs1 fs2). 
    assert (Hsamedoms: dom new_mapping = dom new_fuels).
    { unfold update_fuel_resource, fuel_apply. rewrite -leibniz_equiv_iff.
      intros ρ'; split.
      - intros Hin. destruct (decide (ρ' ∈ dom fs2)) as [[f Hin1]%elem_of_dom|Hin1].
        + apply elem_of_dom. eexists f. rewrite map_lookup_imap lookup_gset_to_gmap option_guard_True //=.
          rewrite decide_True //. apply elem_of_dom. rewrite Hin1; eauto.          
          rewrite map_imap_dom_eq dom_gset_to_gmap in Hin.
          { by rewrite -ls_same_doms. } 
          intros ρ0??. 
          destruct (decide (ρ0 ∈ dom $ ls_mapping δ1)); [| done].
          by apply elem_of_dom.
        + rewrite map_imap_dom_eq dom_gset_to_gmap; last first.
          { intros ρ0 ? Hin0. destruct (decide (ρ0 ∈ dom fs2)) as [|Hnotin]; apply elem_of_dom; first done.
            unfold valid_new_fuelmap in Hfuelsval.
            destruct Hfuelsval as (_&_&_&_& Hdomfs2). set_solver. }

          rewrite map_imap_dom_eq dom_gset_to_gmap in Hin.
          { by rewrite -ls_same_doms. }
          intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_mapping δ1)); [|done].
          by apply elem_of_dom. 
      - intros [f Hin]%elem_of_dom. rewrite map_lookup_imap in Hin.
        rewrite map_imap_dom_eq dom_gset_to_gmap ls_same_doms. 
        + by_contradiction. rewrite lookup_gset_to_gmap option_guard_False // in Hin.
        + intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_fuel δ1)); [|done].
          apply elem_of_dom. by rewrite ls_same_doms. }

    assert (Hnewdom: dom new_fuels = (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)).
    { unfold update_fuel_resource, fuel_apply. rewrite map_imap_dom_eq ?dom_gset_to_gmap //.
      intros ρ' _ Hin. destruct (decide (ρ' ∈ dom fs2)); apply elem_of_dom =>//. set_solver. }

    assert (Hfueldom: live_roles _ s2 ⊆ dom new_fuels).
    { rewrite -Hsamedoms map_imap_dom_eq dom_gset_to_gmap //.
      { pose proof (ls_fuel_dom δ1) as Hfueldom. intros ρ' Hin.
        destruct Hfuelsval as (?&?&?&?&?&Hdom_le).
        destruct (decide (ρ' ∈ live_roles _ δ1)).
        - apply elem_of_difference. split. 
          (* split; [set_solver -Hnewdom Hsamedoms Hdom_le|]. *)
          { apply ls_mapping_dom in e. clear -e. set_solver. } 
          intros [? Habs]%elem_of_difference.
          destruct (decide (ρ' = ρ)).
          + simplify_eq. apply not_elem_of_dom in Habs.
            rewrite -> Habs in *. simpl in *. eauto.
          + apply Habs.
            assert (ρ' ∈ dom fs1 ∖ {[ρ]}); set_solver -Hnewdom Hsamedoms.
        - apply elem_of_difference.
          split; [apply elem_of_union; right; set_unfold; naive_solver|
                   set_unfold; naive_solver]. }
      intros ρ0??. destruct (decide (ρ0 ∈ dom $ ls_mapping δ1)); [|done].
      by apply elem_of_dom.  }
    (* iExists {| *)
    (*   ls_under := s2; *)
    (*   ls_fuel :=  _; *)
    (*   ls_fuel_dom := Hfueldom; *)
    (*   ls_mapping := _; *)
    (*   ls_same_doms := Hsamedoms; *)
    (* |}.  *)
    iExists (build_LS_ext s2 _ Hfueldom (<[ζ:=dom fs2]> (ls_tmap δ1 (LM := LM))) _ _ ltac:(done) (LM := LM)).
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
    iMod (update_free_roles_strong fr1 (fr1 ∖ (live_roles _ s2 ∖ (live_roles _ s1 ∪ dom fs1 ∩ dom fs2)) ∪ fr_stash) FR' with "[HFR] [Hfr1]") as "[HFR Hfr2]"; auto.
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
    { pose proof Hfuelsval as (?&?&?&?&?&?). 
      eapply @mim_model_step_helper; eauto.
      { rewrite Heq. etransitivity.
        { apply Hfr_new. }
        set_solver. }
      rewrite Heq; eauto. }

    iModIntro.
    iSplit.
    { iPureIntro.
      destruct Hfuelsval as (Hlim&Hzombie&Hinfs1m&Hnewlim&Hdec&Hinf&Hsup).
      eapply model_step_ls_trans; eauto. }

    iFrame "Hfuel Hmod Hfr2".
    iSplitL; [| rewrite build_LS_ext_spec_tmap; done]. 

    iExists _.
    rewrite build_LS_ext_spec_st build_LS_ext_spec_fuel build_LS_ext_spec_tmap.
    iFrame. all: eauto. (* TODO: find source... *)        
    { iPureIntro. eapply model_step_new_fr; eauto. }
    
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
        apply Hfr_new, elem_of_union in H0 as [H0 | H0].
        2: { set_solver. }
        apply HfrFR in H0. 
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


End ModelStep.
