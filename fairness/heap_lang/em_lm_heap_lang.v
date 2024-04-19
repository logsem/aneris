From trillium.fairness.heap_lang Require Import heap_lang_defs em_lm. 
From trillium.fairness Require Import lm_fair lm_fair_traces. 
From trillium.fairness.lm_rules Require Import resources_updates. 


Section LM_EM_HL.
  Context `{LM: LiveModel (locale heap_lang) M LSI}.
  (* Context {LF: LMFairPre LM}. *)
  Context {LF: LMFairPre LM}.

  Definition LM_EM_HL: ExecutionModel heap_lang (fair_model_model LM_Fair) :=
    LM_EM (LM := LM) 0%nat ltac:(done).

  (* TODO: how to avoid specifying instances of EqDec and Cnt? *)
  Global Instance LM_EM_fairPre {Σ} {hGS: @heapGpreS Σ _ LM_EM_HL}:
    (* fairnessGpreS LM Σ. *)
    fairnessGpreS LM Σ. 
  Proof.
    apply hGS.
  Qed.

  (* TODO: get rid of it*)
  Global Instance LM_EM_fair `{hGS: @heapGS Σ _ LM_EM_HL}:
    (* fairnessGS LM Σ. *)
    fairnessGS LM Σ.
  Proof. apply hGS. Defined.

End LM_EM_HL.

Lemma tids_smaller_restrict_mapping `{M: FairModel} {LSI}
  (c1 c2: cfg heap_lang) δ1 δ2 (ζ: locale heap_lang)
  (Hζs : tids_smaller c1.1 δ1)
  (DOM12: ls_mapping δ2 ⊆ ls_mapping δ1 (LSI := LSI))
  (STEP: locale_step c1 (Some ζ) c2)
  :
  tids_smaller c2.1 δ2 (M := M) (LSI := LSI).
Proof.
  unfold tids_smaller; simpl.
  intros ρ ζ0 Hin.
  destruct c1, c2.
  eapply from_locale_step =>//.
  rewrite /tids_smaller /= in Hζs. eapply Hζs.
  eapply lookup_weaken; eauto. 
Qed.

Lemma tids_dom_restrict_mapping `{LM: LiveModel (locale heap_lang) M LSI} 
  (c1 c2: cfg heap_lang)
  (tmap1 tmap2: gmap (locale heap_lang) (gset (fmrole M))) (ζ: locale heap_lang)
  (Hstep : locale_step c1 (Some ζ) c2)
  (Hlocssmall: tids_restrict c1 tmap1)
  (TMAP2: exists S, tmap2 = <[ζ:=S]> (tmap1))
  :
  tids_restrict c2 tmap2.
Proof.
  intros ζ0 Hnotin.
  destruct TMAP2 as [? ->]. 
  destruct c1, c2. simpl in *. 
  apply lookup_insert_None; split.
  + apply Hlocssmall.
    have Hle := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
    clear -Hnotin Hle. set_solver.
  + intros <-. 
    have ? := locales_of_list_step_incl _ _ _ _ _ Hstep. simpl.
    (* clear Hfueldom Hsamedoms. *)
    inversion Hstep. simplify_eq.
    assert (locale_of t1 e1 ∈ locales_of_list (t1 ++ e1 :: t2));
      last by eauto.
    apply locales_of_list_from_locale_from.
    rewrite from_locale_from_Some //. 
    eapply prefixes_from_spec.
    eexists _,_. by list_simplifier.
Qed.
  (* TODO: ?? *)
    (* - rewrite Hnewdom /new_dom. apply elem_of_equiv_empty_L. intros ρ [Hin1 Hin2]%elem_of_intersection. *)
    (*   assert (ρ ∈ dom (ls_fuel δ1)) *)
    (*     by set_solver -Hnewdom Hsamedoms Hfueldom. *)
    (*   set_solver -Hnewdom Hsamedoms Hfueldom. } *) 


Lemma tids_smaller_fork_step `{LM: LiveModel (locale heap_lang) M LSI} σ1 σ2 δ1 δ2 ζ τ_new
  (Hstep: locale_step σ1 (Some ζ) σ2)
  (SM: tids_smaller σ1.1 δ1)
  (MAP2: exists (R2: gset (fmrole M)), ls_mapping δ2 = map_imap
                                                    (λ (ρ : fmrole M) (o : locale heap_lang),
                                                      if decide (ρ ∈ R2) then Some τ_new else Some o)
                                                    (ls_mapping δ1 (LSI := LSI)))
  (FORK: ∃ tp1' efork, τ_new = locale_of σ1.1 efork /\ σ2.1 = tp1' ++ [efork] ∧ length tp1' = length σ1.1)
  :
  tids_smaller σ2.1 δ2 (LSI := LSI).
Proof.
  destruct σ1 as [tp1 σ1], σ2 as [tp2 σ2]. simpl in *.
  intros ρ ζ'.
  simpl in *. destruct MAP2 as [R2 ->].
  simpl. rewrite map_lookup_imap.
  destruct (ls_mapping δ1 !!ρ) eqn:Heq.
  2: { intros. simpl in *. discriminate. }
  
  destruct (decide (ρ ∈ R2)); first  (intros ?; simplify_eq).
  - destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
    inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
    assert (efs = [efork]) as ->.
    { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
      rewrite app_length //=; rewrite app_length //= in Hlen.
      clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
    inversion H.
    subst ζ'. 
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
      * eapply locales_equiv_from_refl. by list_simplifier. 
  - intros ?; simplify_eq.
    assert (is_Some (from_locale tp1 ζ')). 
    2: by eapply from_locale_step =>//.
    inversion H. subst. eauto. 
Qed.

Lemma tids_dom_fork_step `{LM: LiveModel (locale heap_lang) M LSI}
  (c1 c2: cfg heap_lang) (ζ: locale heap_lang)
  (tmap1 tmap2: gmap (locale heap_lang) (gset (fmrole M)))
  τ_new (R1 R2: gset (fmrole M))
  (Hstep: locale_step c1 (Some ζ) c2)
  (Hsmall: ∀ ζ : locale heap_lang,
      ζ ∉ locales_of_list c1.1 → tmap1 !! ζ = None)
  (Hmapping : ζ ∈ dom tmap1)
  (FORK: (∃ tp1' efork, τ_new = locale_of c1.1 efork /\ c2.1 = tp1' ++ [efork] ∧ length tp1' = length c1.1))
  (TMAP2: tmap2 = <[τ_new:=R2]> (<[ζ:=R1]> (tmap1)))
  :
  ∀ ζ0 : locale heap_lang,
    ζ0 ∉ locales_of_list c2.1 → tmap2 !! ζ0 = None.
Proof.
  assert (Hlocincl: locales_of_list c1.1 ⊆ locales_of_list c2.1).
  { destruct c1 as [tp1 σ1], c2 as [tp2 σ2]. simpl in *.
    apply (locales_of_list_step_incl _ _ _ _ _ Hstep). }
  intros ζ' Hζ'.
  rewrite TMAP2.
  destruct c1 as [tp1 σ1], c2 as [tp2 σ2]. simpl in *.
  rewrite lookup_insert_ne.
  { rewrite lookup_insert_ne; last first.
    { intros <-.
      apply elem_of_dom in Hmapping as [? MM]. 
      rewrite Hsmall in MM; [congruence | naive_solver]. }
    apply Hsmall; set_unfold; naive_solver. }
  pose proof (locales_of_list_step_incl _ _ _ _ _ Hstep).
  (* clear Hfueldom Hsamedoms. *)
  assert (ζ' ∉ locales_of_list tp1) by eauto.
  intros contra. simplify_eq.
  destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
  inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |].
  simplify_eq.
  assert (efs = [efork]) as ->.
  { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
    rewrite app_length //=; rewrite app_length //= in Hlen.
    clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
  (* rewrite H0 in Hζ'. *)
  apply Hζ'. apply elem_of_list_fmap.
  eexists (t1 ++ e2 :: t2, _); split =>//.
  - erewrite locale_equiv =>//. apply locales_equiv_middle.
    eapply locale_step_preserve => //.
  - replace (t1 ++ e2 :: t2 ++ [efork]) with ((t1 ++ e2 :: t2) ++ [efork]); last by list_simplifier.
    rewrite prefixes_from_app.
    rewrite app_comm_cons app_assoc in YY. eapply app_inj_tail in YY.
    set_unfold; naive_solver.
Qed.


Lemma tids_smaller_model_step `{LM: LiveModel (locale heap_lang) M LSI} c1 c2 ζ δ1 δ2
  (Hstep: locale_step c1 (Some ζ) c2)
  (Hless: tids_smaller c1.1 δ1)
  (* S is a subset of dom (ls_fuel δ1); *)
  (*      missing roles are those that are dropped by ζ; *)
  (*      new roles get assigned here *)
  (MAP2: exists f (S: gset (fmrole M)),
      ls_mapping δ2 = map_imap
                        (λ (ρ' : fmrole M) (_ : nat),
                          if decide (ρ' ∈ dom (ls_fuel δ1))
                          then ls_mapping δ1 (LSI := LSI) !! ρ'
                          else Some ζ)
                        (gset_to_gmap f S)
  )
  :
  tids_smaller c2.1 δ2 (LSI := LSI).
Proof.  
  (* eapply tids_smaller_restrict_mapping; eauto. *)
  (* destruct MAP2 as (?&?&->).   *)
  unfold tids_smaller; simpl.
  simpl in MAP2. destruct MAP2 as (?&S&->).
  intros ρ' ? Hmim.
  rewrite map_lookup_imap in Hmim. rewrite lookup_gset_to_gmap in Hmim.
  destruct (decide (ρ' ∈ S)); last by rewrite option_guard_False in Hmim.
  rewrite option_guard_True //= in Hmim.
  destruct (decide (ρ' ∈ dom (ls_fuel δ1))). 
  + inversion Hstep; simplify_eq.
    eapply from_locale_step =>//. eapply Hless. rewrite -Hmim decide_True; auto. 
  + simplify_eq.
    inversion Hstep; simplify_eq.
    eapply from_locale_step =>//. unfold from_locale.
    simpl. rewrite decide_False in Hmim; [| done]. inversion Hmim. subst ζ0.  
    rewrite from_locale_from_Some; [done| ]. 
    apply prefixes_from_spec. exists t1, t2. by list_simplifier.
Qed.

Ltac by_contradiction :=
  match goal with
  | |- ?goal => destruct_decide (decide (goal)); first done; exfalso
  end.

Lemma mim_helper_model_step `{LM: LiveModel (locale heap_lang) M LSI}
  (s2 : fmstate M)
  (fs1 fs2 : gmap (fmrole M) nat)
  (ρ : fmrole M)
  (δ1 : LM)
  (ζ : locale heap_lang)
  (fr1 : gset (fmrole M))
  (Hfr_new : live_roles M s2 ∖ live_roles M δ1 ⊆ fr1 ∪ dom fs1 ∩ dom fs2)
  (Hfuelsval : valid_new_fuelmap fs1 fs2 δ1 s2 ρ (LM := LM))
  (Hxdom : ∀ ρ : fmrole M, ls_mapping δ1 !! ρ = Some ζ ↔ ρ ∈ dom fs1)
  (HFR : fr1 ∩ dom (ls_fuel δ1) = (∅: gset (fmrole M))):
  maps_inverse_match
    (map_imap
       (λ (ρ' : fmrole M) (_ : nat),
          if decide (ρ' ∈ dom (ls_fuel δ1)) then ls_mapping δ1 !! ρ' else Some ζ)
       ((gset_to_gmap 333%nat ((dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2)))
         (* : gmap (fmrole M) (locale heap_lang) *)
)
)
    (<[ζ:=dom fs2]> (ls_tmap δ1)).
Proof. 
  intros ρ' ζ'. simpl. rewrite map_lookup_imap.
  rewrite lookup_gset_to_gmap //=.
  destruct (decide (ρ' ∈ (dom (ls_fuel δ1) ∪ dom fs2) ∖ (dom fs1 ∖ dom fs2))) as [Hin|Hnotin].
  - rewrite option_guard_True //=. destruct (decide (ρ' ∈ dom (ls_fuel δ1))).
    + destruct (decide (ζ' = ζ)) as [->|Hneq].
      * rewrite lookup_insert. split.
        { eexists; split =>//. apply elem_of_difference in Hin as [? Hin].
          apply not_elem_of_difference in Hin as [?|?]; [|done].
          rewrite decide_True in H; [set_solver| ]. done. }
        { intros (?&?&?). simplify_eq.
          rewrite decide_True; [| set_solver]. 
          apply Hxdom.
          destruct Hfuelsval as (?&?&?&?&?). by_contradiction.
          assert (ρ' ∈ live_roles M s2 ∖ live_roles M δ1).
          { set_solver. }
          assert (ρ' ∈ fr1).
          { set_solver. }
          assert (ρ' ∉ dom $ ls_fuel δ1) by set_solver.
          done. }
      * rewrite lookup_insert_ne //. rewrite decide_True; [| done]. 
        apply ls_mapping_tmap_corr.
    + split.
      * rewrite decide_False; [| done]. 
        intros Htid. simplify_eq.
        rewrite lookup_insert. eexists; split=>//.
        set_solver.
      * rewrite decide_False; [| done]. 
        assert (ρ' ∈ dom fs2) by set_solver. intros Hm. by_contradiction.
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
      apply Hxdom in Hin. rewrite Hin in Habs. congruence.  
Qed.       


Lemma tids_smaller'_restrict_mapping `{M: FairModel} {LSI}
  (c1 c2: cfg heap_lang) (δ1 δ2: LiveState (locale heap_lang) M LSI) (ζ: locale heap_lang)
  (Hζs : tids_smaller' c1.1 δ1)
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
  (MAP2: exists (fs2: gmap (fmrole M) nat), ls_tmap δ2 = <[ζ:=dom fs2]> (ls_tmap δ1))
  :
  tids_smaller' c2.1 δ2 (LSI := LSI).
Proof. 
  unfold tids_smaller'; simpl.
  simpl in MAP2. destruct MAP2 as (?&->).
  intros ζ0 [? Hmim]%elem_of_dom.
  rewrite lookup_insert_Some in Hmim. 
  destruct c1, c2. simpl in *. 
  destruct Hmim.
  + destruct H as [<- <-].
    eapply from_locale_step =>//; eauto.
  + destruct H as [? TM].
    eapply from_locale_step =>//.
    eapply Hless. by apply elem_of_dom.
Qed. 

(* TODO: refactor proof *)
Lemma tids_smaller'_fork_step
  `{LM: LiveModel (locale heap_lang) M LSI} σ1 σ2
   (δ1 δ2: lm_ls LM) ζ τ_new
  (Hstep: locale_step σ1 (Some ζ) σ2)
  (SM: tids_smaller' σ1.1 δ1)
  (DOM: ζ ∈ dom (ls_tmap δ1))
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
  { assert (is_Some (from_locale tp1 ζ)).
    2: by eapply from_locale_step =>//.
    by apply SM. }

  destruct H as [? ?].
  rename ζ into ζ_step, ζ0 into ζ, τ_new into ζ_new, Rζ0 into Rζ. 
  rename NEQ into NOTNEW. rename H into NOTSTEP. rename H0 into TMζ1. 
  (* can also assume: ls_tmap δ1 !! ζ_step = Some (R1 ∪ R2) *)
  
  assert (ls_tmap δ2 !! ζ = Some Rζ) as TMζ2.
  { rewrite -TMζ1 MAP2. repeat rewrite lookup_insert_ne; auto. }
  
  edestruct (SM ζ) as [eζ FLζ1].
  { eapply elem_of_dom; eauto. }
  destruct FORK as (tp1' & efork & (-> & -> & Hlen)).
  
  inversion Hstep as [? ? e1 ? e2 ? efs t1 t2 Hf1 YY Hprimstep |]. simplify_eq.
  assert (efs = [efork]) as ->.
  { symmetry. assert (length tp1' = length (t1 ++ e2 :: t2)).
    rewrite app_length //=; rewrite app_length //= in Hlen.
    clear Hlen. eapply app_inj_1 =>//. by list_simplifier. }
  assert (tp1' = t1 ++ e2 :: t2).
  { rewrite app_comm_cons in YY.
    erewrite app_assoc in YY. eapply app_inj_tail in YY. apply YY. }
  subst tp1'.
  assert (locales_equiv (t1 ++ e1 :: t2) (t1 ++ e2 :: t2)) as EQUIV. 
  { apply locales_equiv_middle. eapply locale_step_preserve =>//. }
  eapply from_locale_from_equiv.
  { eapply locales_equiv_from_refl. done. }
  { apply locales_equiv_from_app.
    { apply EQUIV. }
    eapply locales_equiv_from_refl. by list_simplifier. }
  exists eζ. apply from_locale_from_Some_app. done. 
Qed.
