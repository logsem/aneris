From iris.algebra Require Import auth gmap gset excl.
From iris.proofmode Require Import tactics.
From trillium.fairness Require Import fairness fuel resources actual_resources heap_lang_defs em_lm em_lm_heap_lang pmp_lifting lm_fair lm_fair_traces.


(* TODO: move? *)
Lemma tids_smaller'_restrict_mapping `{M: FairModel} {LSI}
  (c1 c2: cfg heap_lang) (δ1 δ2: LiveState (locale heap_lang) M LSI) (ζ: locale heap_lang)
  (Hζs : tids_smaller' c1.1 δ1)
  (* (DOM12: ls_mapping δ2 ⊆ ls_mapping δ1 (LSI := LSI)) *)
  (DOM12: dom (ls_tmap δ2) ⊆ dom (ls_tmap δ1))
  (STEP: locale_step c1 (Some ζ) c2)
  :
  tids_smaller' c2.1 δ2 (M := M) (LSI := LSI).
Proof.
  unfold tids_smaller'; simpl.
  intros ζ0 Hin.
  destruct c1, c2.
  eapply from_locale_step =>//.
  rewrite /tids_smaller' /= in Hζs. eapply Hζs.
  intuition. 
Qed.

Lemma tids_smaller'_model_step `{LM: LiveModel (locale heap_lang) M LSI} c1 c2 ζ
  (δ1 δ2: LiveState (locale heap_lang) M LSI)
  (Hstep: locale_step c1 (Some ζ) c2)
  (Hless: tids_smaller' c1.1 δ1)
  (IN: ζ ∈ dom (ls_tmap δ1))
  (* S is a subset of dom (ls_fuel δ1); *)
  (*      missing roles are those that are dropped by ζ; *)
  (*      new roles get assigned here *)
  (* (MAP2: exists f (S: gset (fmrole M)), *)
  (*     ls_mapping δ2 = map_imap *)
  (*                       (λ (ρ' : fmrole M) (_ : nat), *)
  (*                         if decide (ρ' ∈ dom (ls_fuel δ1)) *)
  (*                         then ls_mapping δ1 (LSI := LSI) !! ρ' *)
  (*                         else Some ζ) *)
  (*                       (gset_to_gmap f S) *)
  (* ) *)
  (MAP2: exists (fs2: gmap (fmrole M) nat), ls_tmap δ2 = <[ζ:=dom fs2]> (ls_tmap δ1))
  :
  tids_smaller' c2.1 δ2 (LSI := LSI).
Proof. 
  (* eapply tids_smaller_restrict_mapping; eauto. *)
  (* destruct MAP2 as (?&?&->).   *)
  unfold tids_smaller'; simpl.
  simpl in MAP2. destruct MAP2 as (?&->).
  intros ζ0 [? Hmim]%elem_of_dom.
  (* rewrite map_lookup_imap in Hmim. rewrite lookup_gset_to_gmap in Hmim. *)
  rewrite lookup_insert_Some in Hmim. 
  (* destruct (decide (ρ' ∈ S)); last by rewrite option_guard_False in Hmim. *)
  (* rewrite option_guard_True //= in Hmim. *)

  destruct c1, c2. simpl in *. 
  destruct Hmim.
  + destruct H as [<- <-].
    eapply from_locale_step =>//; eauto.
  + destruct H as [? TM].
    eapply from_locale_step =>//.
    eapply Hless. by apply elem_of_dom.
Qed. 

Lemma tids_smaller'_fork_step
  `{LM: LiveModel (locale heap_lang) M LSI} σ1 σ2
   (δ1 δ2: lm_ls LM) ζ τ_new
  (Hstep: locale_step σ1 (Some ζ) σ2)
  (SM: tids_smaller' σ1.1 δ1)
  (DOM: ζ ∈ dom (ls_tmap δ1))
  (* (MAP2: exists (R2: gset (fmrole M)), ls_mapping δ2 = map_imap
                                                    (λ (ρ : fmrole M) (o : locale heap_lang),
                                                      if decide (ρ ∈ R2) then Some τ_new else Some o)
                                                    (ls_mapping δ1 (LSI := LSI)) *)
  (MAP2: exists R2 R1, ls_tmap δ2 = <[τ_new:=R2]> (<[ζ:=R1]> (ls_tmap δ1)))
  (FORK: ∃ tp1' efork, τ_new = locale_of σ1.1 efork /\ σ2.1 = tp1' ++ [efork] ∧ length tp1' = length σ1.1)
  :
  tids_smaller' σ2.1 δ2 (LSI := LSI).
Proof.
  destruct σ1 as [tp1 σ1], σ2 as [tp2 σ2]. simpl in *.
  red. intros ζ0 [Rζ0 IN2]%elem_of_dom.
  simpl in *.
  destruct MAP2 as (R2 & R1 & MAP2).
  simpl. rewrite MAP2 in IN2.
  repeat rewrite lookup_insert_Some in IN2.
  destruct IN2 as [[<- <-] | ].
  {
    destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
    inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
    assert (efs = [efork]) as ->.
    { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
      rewrite app_length //=; rewrite app_length //= in Hlen.
      clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
    assert (is_Some (from_locale (t1 ++ e1 :: t2 ++ [efork]) (locale_of (t1 ++ e1 :: t2) efork))).
    + unfold from_locale. erewrite from_locale_from_Some; eauto.
      apply prefixes_from_spec. list_simplifier. eexists _, []. split=>//.
      by list_simplifier.
    + eapply from_locale_from_equiv =>//; [constructor |].
      (* rewrite H0. *)
      replace (t1 ++ e1 :: t2 ++ [efork]) with ((t1 ++ e1 :: t2) ++ [efork]);
        last by list_simplifier.
      replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]);
        last by list_simplifier.
      assert (locales_equiv (t1 ++ e1 :: t2) (t1 ++ e2 :: t2)).
      { apply locales_equiv_middle. eapply locale_step_preserve =>//. }
      assert (tp1' = t1 ++ e2 :: t2).
      { rewrite app_comm_cons in YY.
        erewrite app_assoc in YY. eapply app_inj_tail in YY. apply YY. }
      apply locales_equiv_from_app =>//.
      * congruence.
      * eapply locales_equiv_from_refl. by list_simplifier. }
  
  destruct H as [NEQ [[<- <-]| ?]].
  {
    (* intros ?; simplify_eq. *)
    assert (is_Some (from_locale tp1 ζ)).
    2: by eapply from_locale_step =>//.
    by apply SM. }

  destruct H as [? ?].
{
    destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
    inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
    assert (efs = [efork]) as ->.
    { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
      rewrite app_length //=; rewrite app_length //= in Hlen.
      clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }

    pose proof H0 as H0_%mk_is_Some%elem_of_dom.
    pose proof (SM ζ0 H0_) as [l0 LOCζ0].
   
    (* assert (is_Some (from_locale (t1 ++ e1 :: t2 ++ [l0]) (locale_of (t1 ++ e1 :: t2) l0))). *)
    (* + unfold from_locale. erewrite from_locale_from_Some; eauto. *)
    (*   apply prefixes_from_spec. list_simplifier. *)
    (*   do 2 eexists. split. *)
    (*   { reflexivity. } *)
    (*   Unshelve. 2: exact []. *)
    (*   by list_simplifier. *)
    (* + unfold from_locale. *)

    (*   erewrite from_locale_from_Some; eauto.     *)

    (*   eapply from_locale_from_equiv =>//. [constructor |]. *)
    (*   (* rewrite H0. *) *)
    (*   replace (t1 ++ e1 :: t2 ++ [efork]) with ((t1 ++ e1 :: t2) ++ [efork]); *)
    (*     last by list_simplifier. *)
    (*   replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]); *)
    (*     last by list_simplifier. *)
    (*   assert (locales_equiv (t1 ++ e1 :: t2) (t1 ++ e2 :: t2)). *)
    (*   { apply locales_equiv_middle. eapply locale_step_preserve =>//. } *)
    (*   assert (tp1' = t1 ++ e2 :: t2). *)
    (*   { rewrite app_comm_cons in YY. *)
    (*     erewrite app_assoc in YY. eapply app_inj_tail in YY. apply YY. } *)
    (*   apply locales_equiv_from_app =>//. *)
    (*   * congruence. *)
    (*   * eapply locales_equiv_from_refl. by list_simplifier. } *)

    (*----------------------------------*)
  
  (* rewrite map_lookup_imap. *)

  (* ?????? *)

  (* destruct (ls_mapping δ1 !! ρ) eqn:Heq. *)
  (* 2: { intros. simpl in *. discriminate. } *)
  
  (* destruct (decide (ρ ∈ R2)); first  (intros ?; simplify_eq). *)
  (* - destruct FORK as (tp1' & efork & (-> & -> & Hlen)). *)
  (*   inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq. *)
  (*   assert (efs = [efork]) as ->. *)
  (*   { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)). *)
  (*     rewrite app_length //=; rewrite app_length //= in Hlen. *)
  (*     clear Hlen. eapply app_inj_1 =>//. by list_simplifier. } *)
  (*   inversion H. *)
  (*   subst ζ'.  *)
  (*   assert (is_Some (from_locale (t1 ++ e1 :: t2 ++ [efork]) (locale_of (t1 ++ e1 :: t2) efork))). *)
  (*   + unfold from_locale. erewrite from_locale_from_Some; eauto. *)
  (*     apply prefixes_from_spec. list_simplifier. eexists _, []. split=>//. *)
  (*     by list_simplifier. *)
  (*   + eapply from_locale_from_equiv =>//; [constructor |]. *)
  (*     (* rewrite H0. *) *)
  (*     replace (t1 ++ e1 :: t2 ++ [efork]) with ((t1 ++ e1 :: t2) ++ [efork]); *)
  (*       last by list_simplifier. *)
  (*     replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]); *)
  (*       last by list_simplifier. *)
  (*     assert (locales_equiv (t1 ++ e1 :: t2) (t1 ++ e2 :: t2)). *)
  (*     { apply locales_equiv_middle. eapply locale_step_preserve =>//. } *)
  (*     assert (tp1' = t1 ++ e2 :: t2). *)
  (*     { rewrite app_comm_cons in YY.  *)
  (*       erewrite app_assoc in YY. eapply app_inj_tail in YY. apply YY. } *)
  (*     apply locales_equiv_from_app =>//. *)
  (*     * congruence. *)
  (*     * eapply locales_equiv_from_refl. by list_simplifier.  *)
  (* - intros ?; simplify_eq. *)
  (*   assert (is_Some (from_locale tp1 ζ')).  *)
  (*   2: by eapply from_locale_step =>//. *)
  (*   inversion H. subst. eauto.  *)
Admitted. 




Section ActualOwnershipInterface. 
  Context `{LM: LiveModel (locale heap_lang) M LSI_True}.
  Context {Σ : gFunctors}.
  Context {fG: fairnessGS LM Σ}.
  Context {LF': LMFairPre' LM}. 
  Context`{invGS_gen HasNoLc Σ}.

  (* TODO: move *)
  Lemma tids_restrict_smaller' (σ: cfg heap_lang) (δ: lm_ls LM):
    tids_restrict σ (ls_tmap δ) -> tids_smaller' σ.1 δ.
  Proof.
    rewrite /tids_smaller' /tids_restrict. 
    intros. apply locales_of_list_from_locale_from'.
    destruct (decide (ζ ∈ locales_of_list σ.1)); [done| ].
    specialize (H0 _ n).
    apply elem_of_dom in H1 as [? ?]. congruence. 
  Qed.


  Local Instance LF: LMFairPre LM.
  esplit; apply _.
  Defined. 


  (* TODO: get rid of mim_* lemmas inside of actual_resources *)
  (* TODO: get rid of excessive shelved goals
     (could be solved by new implementation of LiveState) *)
  Lemma ActualOwnershipPartial:
    ⊢ PartialModelPredicates ∅ (EM := @LM_EM_HL _ _ _ LF') (iLM := LM) (PMPP := ActualOwnershipPartialPre) (eGS := fG). 
  Proof.
    iIntros. iApply (Build_PartialModelPredicates (EM := @LM_EM_HL _ _ _ LF')). 
    iModIntro. repeat iSplitL.
    - iIntros (???????) "FUELS MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      iMod (actual_update_no_step_enough_fuel with "FUELS LM_MSI") as (?) "(%STEPM & FUELS & LM_MSI' & %TMAP')".
      3: by apply empty_subseteq. 2: set_solver. 1: done. 
      iModIntro. do 2 iExists _. rewrite /em_lm_msi. iFrame.
      iPureIntro. split.
      + remember (trace_last auxtr) as δ1. 
        pose proof (tids_restrict_smaller' _ _ TR) as SM.
        repeat split; eauto.
        * eexists. split; [apply STEPM| ]. done. 
        * eapply tids_smaller'_restrict_mapping; [..| apply STEP]; eauto.
          rewrite TMAP'.
          rewrite dom_insert. rewrite subseteq_union_1; [done| ].
          apply singleton_subseteq_l.
          eapply locale_trans_dom; eauto.
          eexists. split; eauto.
          { apply STEPM. }
          done. 
      + eapply tids_dom_restrict_mapping; eauto.
    - iIntros "* FUELS MSI". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      remember (trace_last auxtr) as δ1.
      pose proof (tids_restrict_smaller' _ _ TR) as SM.
      assert (Hnewζ: (locale_of tp1 efork) ∉ dom (ls_tmap δ1)).
      { subst δ1. rewrite LAST in SM. apply not_elem_of_dom. simpl in *.
        apply TR. 
        unfold tids_smaller in SM. 
        rewrite elem_of_list_fmap. intros ([??]&Hloc&Hin).
        symmetry in Hloc.
        rewrite -> prefixes_from_spec in Hin.
        destruct Hin as (?&t0&?&?).
        simplify_eq. list_simplifier.
        eapply locale_injective=>//.
        apply prefixes_from_spec.
        exists t0, []. split =>//. rewrite LAST in H1. by list_simplifier. }

      (* TODO: make it a lemma *)
      iAssert (⌜ (ls_tmap δ1 !! ζ = Some (dom fs)) ⌝)%I as %TMAPζ.
      { iDestruct "FUELS" as "[FRAG ?]".
        iDestruct "LM_MSI" as (?) "(?&AUTH&?&?)".
        simpl.
        iDestruct (frag_mapping_same with "AUTH FRAG") as "%MM".
        by rewrite dom_fmap_L in MM. }
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      iMod (actual_update_fork_split with "FUELS LM_MSI") as (?) "(FUELS1 & FUELS2 & POST & LM_MSI' & %STEPM & %TMAP')"; eauto.
      do 2 iExists _. iFrame. iModIntro. iPureIntro. split.
      + red. intros. eapply tids_dom_fork_step; eauto.
        * intros. apply TR. congruence.
        * inversion STEPM. destruct H1 as [? MM].
          eapply ls_mapping_tmap_corr in MM as (?&?&?).
          eapply elem_of_dom_2; eauto.
        * simpl.
          destruct POOL as (?&?&?).
          exists x, efork. done.
      + repeat split; eauto.
        { eexists; split; [apply STEPM| ]; done. }
        eapply tids_smaller'_fork_step; [apply STEP| ..]. 
        * by rewrite -LAST.
        * eapply locale_trans_dom; eauto.
          eexists. split; [apply STEPM| ]. done. 
        * eauto. 
        * destruct POOL as (?&?&?).
          exists x, efork. done.
    - iIntros "* FUELS ST MSI FR". simpl in *.
      iDestruct "MSI" as "[LM_MSI %TR]".
      pose proof (tids_restrict_smaller' _ _ TR) as SM.
      iDestruct (model_agree' with "LM_MSI ST") as "%Heq".
      iDestruct (has_fuel_in with "FUELS LM_MSI") as %Hxdom; eauto.
      (* TODO: make it a lemma *)
      iAssert (⌜ fr1 ∩ dom (ls_fuel δ1) = ∅ ⌝)%I as %FR0.
      { iDestruct "LM_MSI" as (?) "(?&?&FR'&?&%)".
        iDestruct (free_roles_inclusion with "FR' FR") as "%".
        iPureIntro. set_solver. }
      iMod (actual_update_step_still_alive with "FUELS ST LM_MSI FR") as (?) "(%STEPM & FUELS & ST & LM_MSI & FR & %TMAP2)"; eauto. 
      iModIntro. do 2 iExists _. iFrame. iPureIntro. split.
      + repeat split; eauto.
        (* 2: by rewrite LAST2; eauto. *)
        { rewrite LAST2. eexists; split; [apply STEPM| ]. done. }  
        eapply tids_smaller'_model_step; eauto.
        eapply locale_trans_dom; eauto.
        eexists. split; [apply STEPM| ]. done. 
      + eapply tids_dom_restrict_mapping; eauto.
        Unshelve. all: eauto. 
  Qed.

End ActualOwnershipInterface.  
