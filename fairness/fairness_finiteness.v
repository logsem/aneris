From stdpp Require Import finite.
From trillium.prelude Require Import quantifiers classical_instances finitary.
(* From trillium.prelude Require Import finitary. *)
From trillium.fairness Require Import fairness fuel traces_match lm_fair_traces lm_fair utils. 

Section LMFinBranching.
  Context `{Countable G}.
  Context `{LM: LiveModel G M LSI}.
  Context {DEC: forall a b c, Decision (LSI a b c)}.

  Definition get_role {M : FairModel} {LSI} {LM: LiveModel G M LSI} (lab: mlabel LM) :=
  match lab with
  | Take_step ρ _ => Some ρ
  | _ => None
  end.

  Definition potential_FLs_list (st1: lm_ls LM): list (@FairLabel G (fmrole M)) :=    
    Config_step :: flat_map (fun τ => elements (potential_step_FLs st1 τ)) (elements (dom (ls_tmap st1))). 

  Lemma potential_FLs_list_approx δ1 ℓ δ2
    (TRANS: lm_ls_trans LM δ1 ℓ δ2):
    ℓ ∈ potential_FLs_list δ1.
  Proof.
    destruct (decide (ℓ = Config_step)).
    { subst. set_solver. }
    assert (exists g, fair_lbl_matches_group ℓ g) as [g MATCH]. 
    { destruct ℓ; try congruence; simpl; eauto. }
    rewrite /potential_FLs_list.
    apply elem_of_list_further.
    apply elem_of_list_In, in_flat_map.
    exists g. split.
    { apply elem_of_list_In, elem_of_elements.
      apply elem_of_dom. 
      destruct ℓ; try congruence; simpl in *; subst. 
      - apply proj2, proj1 in TRANS.
        apply (ls_mapping_tmap_corr) in TRANS as (?&?&?). eauto.
      - apply proj1 in TRANS as (?&TRANS).
        apply (ls_mapping_tmap_corr) in TRANS as (?&?&?). eauto. }
    apply elem_of_list_In, elem_of_elements.
    rewrite /potential_step_FLs.
    destruct ℓ; try congruence; simpl in *; subst. 
    2: { set_solver. }
    apply elem_of_union_r. apply elem_of_map. eexists. split; eauto.
    apply elem_of_dom. apply proj2, proj1 in TRANS.
    by apply mk_is_Some, ls_same_doms' in TRANS.
  Qed. 

  Program Definition enumerate_next_st
    (δ1: LM)
    (inner_exts: list M)
    (next_threads: list G)
    : list LM := 
    '(s2) ← inner_exts;
    d ← enumerate_dom_gsets' (dom δ1.(ls_fuel) ∪ live_roles _ s2);
    fs ← enum_gmap_bounded' (live_roles _ s2 ∪ d) (max_gmap δ1.(ls_fuel) `max` LM.(lm_fl) s2);
    dom_tmap ← elements $ powerset $ list_to_set next_threads;
    tm ← enum_gmap_range_bounded' dom_tmap (elements $ powerset (live_roles _ s2 ∪ d));
    (if
        (decide (LSI s2 (`tm) (`fs) /\
                 dom (ls_mapping_impl (`tm)) = dom (`fs) /\
                 tmap_disj (`tm)))
    then
    [{| ls_under := s2;
             ls_fuel := `fs;
             ls_tmap := `tm ;
          |}]
      else
    []).
  Next Obligation.
    intros ??????????. destruct fs as [? Heq]. rewrite /= Heq //. set_solver.
  Qed.
  Next Obligation.
    intros ????????(? & DOM_EQ & TM_DISJ).
    destruct fs as [fs Heq]. destruct tm as [tm [DOM CODOM]].
    rewrite /= Heq //.
    simpl in *. rewrite -Heq -DOM_EQ.
    intros.
    rewrite elem_of_dom.
    apply exist_proper.
    by apply ls_mapping_tmap_corr_impl.
  Qed. 
  Next Obligation. tauto. Qed. 
  Next Obligation. tauto. Qed.
  
  
  Lemma enum_next_st_in
    δ1
    δ'
    inner_exts
    next_threads
    (IN_IE: (ls_under δ') ∈ inner_exts)
    (IN_DOMS: dom (ls_fuel δ') ⊆ dom (ls_fuel δ1) ∪ live_roles M δ')
    (FUEL_LIM: forall ρ f (F: ls_fuel δ' !! ρ = Some f),
        f ≤ max_gmap (ls_fuel δ1) `max` lm_fl LM δ')
    (THREADS_IN: dom (ls_tmap δ') ⊆ list_to_set next_threads)    
    :
    δ' ∈ enumerate_next_st δ1 inner_exts next_threads
  .
  Proof. 
    unfold enumerate_next_st. apply elem_of_list_bind.
    exists (δ'.(ls_under)).
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

    exists (dom (ls_tmap δ')). split.
    2: { apply elem_of_elements. by apply powerset_spec. }
    assert (enum_range_prop (dom (ls_tmap δ'))
              (elements (powerset (live_roles M δ' ∪ dom (ls_fuel δ')))) 
              (ls_tmap δ')) as ERPδ'.
    { split; [done| ].
      apply map_Forall_lookup. intros ?? ITH.
      apply elem_of_elements. apply powerset_spec.
      rewrite -Hfueldom.
      apply elem_of_subseteq.
      intros. eapply ls_tmap_fuel_same_doms; eauto. }

    apply elem_of_list_bind. unshelve eexists; [by eauto| ]. 
    split; [| by apply enum_gmap_range_bounded'_spec].
    
    destruct decide.
    2: { destruct n. simpl. repeat split; try by apply δ'.
         by rewrite ls_same_doms. }
    rewrite elem_of_list_singleton; f_equal.
    destruct δ'; simpl. f_equal; apply ProofIrrelevance.
  Qed.

  Lemma enum_next_in
    δ1
    δ'
    ℓ
    inner_exts
    next_threads
    (IN_IE: (ls_under δ') ∈ inner_exts)
    (IN_DOMS: dom (ls_fuel δ') ⊆ dom (ls_fuel δ1) ∪ live_roles M δ')
    (Htrans : lm_ls_trans LM δ1 ℓ δ')
    (THREADS_IN: dom (ls_tmap δ') ⊆ list_to_set next_threads)    
    :
    δ' ∈ enumerate_next_st δ1 inner_exts next_threads
  .
  Proof. 
    eapply enum_next_st_in; eauto.
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
          assert (oleq (ls_fuel δ' !! ρ') (ls_fuel δ1 !! ρ')).
          { specialize (H1 ρ' Hmap). destruct H1 as [?|[?|?]]; set_solver. }
          simpl in H4. rewrite Hsome in H4.
          apply elem_of_dom in Hmap as [? Heq]. rewrite Heq in H4. 
          pose proof (max_gmap_spec _ _ _ Heq). simpl in *.
          lia. 
      + inversion Htrans as [? Hbig]. destruct Hbig as (Hmap&?&Hleq'&?&Hnew&?).
        destruct (decide (ρ ∈ dom $ ls_fuel δ1)) as [Hin|Hnotin].
        * assert (Hok: oleq (ls_fuel δ' !! ρ) (ls_fuel δ1 !! ρ)).
          { unfold fuel_must_not_incr in *.
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
          lia.  
        * simpl in *. done.
      + destruct Hleq as [[=] _]. 
      + apply elem_of_dom_2 in Hsome. set_solver.
    - inversion Htrans as [? [? [Hleq [Hnew Hfalse]]]]. done. 
  Qed. 

  Definition enumerate_next
    (δ1: LM)
    (inner_exts: list M)
    (next_threads: list G) : list (LM * lm_lbl LM) :=
    δ ← enumerate_next_st δ1 inner_exts next_threads;
    ℓ ← potential_FLs_list δ1;
    mret (δ, ℓ).

  Lemma next_step_domain
    δ ℓ
    inner_exts
    next_threads
    (δ' : LM)
    (Htrans : lm_ls_trans LM δ ℓ δ')
    (INNER_DOM: (ls_under δ') ∈ inner_exts)
    (THREADS_IN: dom (ls_tmap δ') ⊆ list_to_set next_threads)    
    :
    (δ', ℓ) ∈ enumerate_next δ inner_exts next_threads.
  Proof.
    rewrite /enumerate_next. apply elem_of_list_bind. exists δ'.
    split.
    { apply elem_of_list_bind. exists ℓ. split; [set_solver| ].
      eapply potential_FLs_list_approx; eauto. }
    eapply enum_next_in; eauto.  
    destruct ℓ as [ρ tid' | |].
    - inversion Htrans as (?&?&?&?&?&?&?). intros ρ' Hin. destruct (decide (ρ' ∈ live_roles _ δ')); first set_solver.
      destruct (decide (ρ' ∈ dom $ ls_fuel δ)); set_solver. 
    - inversion Htrans as (?&?&?&?&?). set_solver.
    - inversion Htrans as (?&?&?&?&?). done. 
  Qed.


  Lemma role_LM_step_dom_all
    δ           
    (inner_exts : list M)
    (next_threads : list G)
    : 
    forall ℓ (δ': lm_ls LM),
      lm_ls_trans LM δ ℓ δ' ->
      (ls_under δ') ∈ inner_exts ->
      dom (ls_tmap δ') ⊆ list_to_set next_threads ->
      (* In δ' (enumerate_next_st δ inner_exts next_threads). *)
      In δ' (map fst (enumerate_next δ inner_exts next_threads)).
  Proof.
    intros. apply in_map_iff. exists (δ', ℓ). split; auto.
    intros. apply elem_of_list_In. eapply next_step_domain; eauto.
  Qed.

  (* TODO: write more concisely? *)
  Definition roles_rearranged (δ1 δ2: LiveState _ _ LSI) (D: gset G) τ :=
    ls_under δ2 = ls_under δ1 /\ ls_fuel δ2 = ls_fuel δ1 /\
    (* dom (ls_mapping δ2) = dom (ls_mapping δ1) /\ *)
    dom (ls_tmap δ2) ⊆ D ∪ {[ τ ]} /\
    dom (ls_mapping δ2) = dom (ls_mapping δ1) /\    
    (forall ρ, ρ ∈ dom (ls_mapping δ2) ->
          ls_mapping δ2 !! ρ = match (ls_mapping δ1 !! ρ) with
                               | Some τ' => Some (if (decide (τ' ∈ D)) then τ' else τ)
                               | None => Some τ
                               end). 
  
  Lemma ex_norm_step δ1 ℓ δ2
    (STEP: lm_ls_trans LM δ1 ℓ δ2)
    (LSI_STABLE: forall δ1 τ δ2, locale_trans δ1 τ δ2 (LM := LM) ->
                             exists δ2', roles_rearranged δ2 δ2' (dom $ ls_tmap δ1) τ)
    :
    exists (δ2': LiveState _ _ LSI) (g: G),
      fair_lbl_matches_group ℓ g /\
      lm_ls_trans LM δ1 ℓ δ2' /\
      roles_rearranged δ2 δ2' (dom $ ls_tmap δ1) g.
  Proof.
    assert (exists τ, fair_lbl_matches_group ℓ τ) as [τ MATCH]. 
    { destruct ℓ; simpl in STEP; [..| tauto].
      all: simpl; eauto. }
    specialize (LSI_STABLE δ1 τ δ2 ltac:(by red; eauto)).
    destruct LSI_STABLE as [δ2' ARR].
    exists δ2', τ. split; [| split]; [done |.. | by apply ARR].
    destruct ARR as (ST & FUEL & TMAP_DOM & MAP_DOM & MAP_VAL). 
    destruct ℓ; simpl in *; subst; rewrite ST FUEL.
    3: done. 
    - repeat split; try by apply STEP.
      + apply proj2, proj2, proj1 in STEP. red.
        rewrite FUEL. intros.
        inversion H2; subst.  
        { eapply STEP; eauto. left; eauto. }
        specialize (MAP_VAL ρ' ltac:(by eapply elem_of_dom; eauto)).
        apply elem_of_dom in Hissome. rewrite MAP_DOM in Hissome.
        apply elem_of_dom in Hissome as [? Hissome].
        rewrite Hissome in MAP_VAL.
        destruct decide. 
        { rewrite MAP_VAL -Hissome in Hneqtid.
          eapply STEP; eauto. right; eauto. }
        eapply STEP; eauto. right; eauto.
        rewrite Hissome. intros MAP1.
        pose proof (ls_mapping_tmap_corr δ1) as MINV.
        apply n. eapply mim_in_1; eauto. 
      + apply proj2, proj2, proj2, proj1 in STEP. red.
        rewrite FUEL ST. apply STEP.
    - repeat split; try by apply STEP.
      (* TODO: refactor *)
      + apply proj2, proj1 in STEP. red.
        rewrite FUEL. intros.
        inversion H2; subst.  
        { eapply STEP; eauto. left; eauto. }
        specialize (MAP_VAL ρ' ltac:(by eapply elem_of_dom; eauto)).
        apply elem_of_dom in Hissome. rewrite MAP_DOM in Hissome.
        apply elem_of_dom in Hissome as [? Hissome].
        rewrite Hissome in MAP_VAL.
        destruct decide. 
        { rewrite MAP_VAL -Hissome in Hneqtid.
          eapply STEP; eauto. right; eauto. }
        eapply STEP; eauto. right; eauto.
        rewrite Hissome. intros MAP1.
        pose proof (ls_mapping_tmap_corr δ1) as MINV.
        apply n. eapply mim_in_1; eauto. 
      + apply proj2, proj2, proj1 in STEP. red.
        rewrite FUEL ST. apply STEP.
  Qed.

  (* not using Finite type to avoid dealing with ProofIrrel *)
  
  Global Instance locale_trans_ex_dec_fin
    (* {LF: LMFairPre LM} *)
    `{∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2)}
    `{EqDecision (fmstate M)}
    δ1 τ
    steps
    (FIN_STEPS: forall oρ s2, fmtrans M (ls_under δ1) oρ s2 -> In s2 steps)
    (LSI_STABLE: forall δ1 τ δ2, locale_trans δ1 τ δ2 (LM := LM) ->
                             exists δ2', roles_rearranged δ2 δ2' (dom $ ls_tmap δ1) τ):
    Decision (exists δ2, locale_trans δ1 τ δ2 (LM := LM)).
  Proof. 
    pose proof (role_LM_step_dom_all δ1 (ls_under δ1 :: steps) (elements $ dom $ ls_tmap δ1)) as STEPS. 
    set (δ's := map fst (enumerate_next δ1 (ls_under δ1 :: steps) (elements (dom (ls_tmap δ1))))).
    set (τ_ℓs := filter (locale_trans δ1 τ (LM := LM)) δ's).
    destruct τ_ℓs eqn:FLT.
    2: { left. exists m. eauto.
         pose proof (in_eq m l) as IN. rewrite -FLT in IN.
         apply elem_of_list_In, elem_of_list_filter in IN. apply IN. }
    right. intros [δ' TRANS].    
    red in TRANS. destruct TRANS as (ℓ & TRANS & MATCH). 
    pose proof (ex_norm_step _ _ _ TRANS LSI_STABLE) as (δ2' & g & MATCH' & TRANS' & ARR).
    enough (In δ2' τ_ℓs) as IN. 
    { by rewrite FLT in IN. }
    (* specialize (STEPS _ _ TRANS'). forward STEPS; [| forward STEPS].  *)
    forward eapply (STEPS _ _ TRANS') as ?. 
    { apply elem_of_cons. destruct ℓ; simpl in *; try done.
      - right. eapply elem_of_list_In, FIN_STEPS; eauto. apply TRANS'.
      - left. repeat apply proj2 in TRANS'. congruence. }
    { intros. rewrite list_to_set_elements.
      red in ARR. apply proj2, proj2, proj1 in ARR.
      etrans; [apply ARR| ].
      rewrite union_comm subseteq_union_1; [done| ]. apply singleton_subseteq_l.
      eapply locale_trans_dom. eexists. split; eauto. }
      (* destruct ARR as (ST & FUEL & TMAP_DOM & MAP_DOM & MAP_VAL). *)
      (* apply elem_of_subseteq. intros ?. rewrite !elem_of_dom. intros T.   *)
      (* pose proof T as T'. specialize (MAP_VAL _ T'). *)
      (* rewrite T in MAP_VAL. *)
      (* rewrite MAP_DOM in T'. apply elem_of_dom in T' as [? T']. *)
      (* rewrite T' in MAP_VAL. inversion MAP_VAL. subst tid'. *)
      (* destruct decide; [done| ]. *)
      (* pose proof (ls_mapping_tmap_corr δ1 (LM := LM)) as MINV. *)
      (* destruct ℓ; simpl in *; try done. *)
      (* - apply proj2, proj1 in TRANS'. subst.  *)
      (*   eapply mim_in_1; eauto. *)
      (* - apply proj1 in TRANS' as [? TRANS']. subst.  *)
      (*   eapply mim_in_1; eauto. } *)
    subst τ_ℓs. apply elem_of_list_In, elem_of_list_filter. split.
    { eexists. split; eauto. }
    apply elem_of_list_In. done.
  Qed.

  Global Instance locale_trans_fin_ex_dec_fin
    `{∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2)}
    `{EqDecision (fmstate M)}
    δ1 τ
    (nexts: forall s1, {l: list (fmstate M) | forall s2 oρ, fmtrans M s1 oρ s2 -> s2 ∈ l})
    (LSI_STABLE: forall δ1 τ δ2, locale_trans δ1 τ δ2 (LM := LM) ->
                             exists δ2', roles_rearranged δ2 δ2' (dom $ ls_tmap δ1) τ):
    Decision (exists δ2, locale_trans δ1 τ δ2 (LM := LM)).
  Proof. 
    apply locale_trans_ex_dec_fin with (steps := proj1_sig $ nexts (ls_under δ1)); eauto.
    intros. simpl. destruct (nexts δ1) as [? IN]; simpl in *.
    apply elem_of_list_In. eauto.
  Qed.

  Definition rearrange_roles_map (tm: gmap G (gset (fmrole M))) (R: gset G) (r: G):
    gmap G (gset (fmrole M)) :=
    let cleaned := filter (fun '(k, _) => k ∈ R) tm in
    let cur_r := default ∅ (tm !! r) in
    let to_move := flatten_gset (map_img (filter (fun '(k, _) => k ∉ R) tm)) in
    <[ r := cur_r ∪ to_move ]> cleaned.

  Lemma rrm_tmap_fuel_same_doms (δ: LiveState G M LSI) R r:
    ∀ ρ : fmrole M,
    ρ ∈ dom (ls_fuel δ)
    ↔ (∃ (τ : G) (R0 : gset (fmrole M)),
         rearrange_roles_map (ls_tmap δ) R r !! τ = Some R0 ∧ ρ ∈ R0).
  Proof.
    intros ρ. 
    rewrite /rearrange_roles_map.
    setoid_rewrite lookup_insert_Some. setoid_rewrite map_filter_lookup_Some.
    rewrite -ls_same_doms elem_of_dom. 
    split.
    { intros [g MAP].
      pose proof MAP as TM. apply ls_mapping_tmap_corr in TM as (Rg & TM & IN).
      destruct (decide (r = g)).
      - subst.
        do 2 eexists. split.
        + left. split; reflexivity.
        + rewrite TM. simpl. set_solver.
      - destruct (decide (g ∈ R)).
        + do 2 eexists. split; [| apply IN].
          right. eauto.
        + do 2 eexists. split.
          * left. split; reflexivity.
          * apply elem_of_union. right. apply flatten_gset_spec.
            eexists. split; eauto.
            apply elem_of_map_img.
            eexists. apply map_filter_lookup_Some. eauto. }
    intros (τ & R' & PROP & IN).
    destruct PROP as [[<- <-] | (? & tm & IN')].
    + apply elem_of_union in IN as [IN | IN].
      * destruct (ls_tmap δ !! r) eqn:TM; try set_solver. simpl in IN.
        exists r. eapply ls_mapping_tmap_corr; eauto.
      * apply flatten_gset_spec in IN. destruct IN as (s & IN' & IN).
        apply elem_of_map_img in IN'. destruct IN' as (g & IN').
        apply map_filter_lookup_Some in IN' as (TM & IN').  
        exists g. eapply ls_mapping_tmap_corr; eauto.
    + exists τ. eapply ls_mapping_tmap_corr; eauto.
  Qed. 

  Lemma rrm_tmap_disj tm R r
    (DISJ: tmap_disj tm):
    tmap_disj (rearrange_roles_map tm R r).
  Proof.
red. rewrite /rearrange_roles_map.
      setoid_rewrite lookup_insert_Some. setoid_rewrite map_filter_lookup_Some.
      intros * NEQ TM1 TM2.

      assert (forall k2 S2 (NEQ: r ≠ k2) (tm2 : tm !! k2 = Some S2)
                (IN2 : k2 ∈ R),
  default ∅ (tm !! r)
  ∪ flatten_gset (map_img (filter (λ '(k, _), k ∉ R) tm)) ## S2) as HELPER. 
      { intros. apply disjoint_union_l. split.
        * destruct (tm !! r) eqn:TM; [| set_solver].
          simpl. eapply DISJ; [apply NEQ0| ..]; eauto. 
        * apply flatten_gset_disjoint. intros s. 
          rewrite elem_of_map_img.
          setoid_rewrite map_filter_lookup_Some.
          intros (g&?&?).
          destruct (decide (g = k0)); [subst; done| ]. 
          eapply DISJ; eauto. }
      
      destruct TM1 as [[<- <-] | (? & tm1 & IN1)], TM2 as [[<- <-] | (? & tm2 & IN2)]. 
      { congruence. }
      + eapply HELPER; eauto.
      + apply disjoint_sym. eapply HELPER; eauto.
      + eapply DISJ; [apply NEQ| ..]; eauto.
  Qed. 

  Lemma rrm_mapping (tm: gmap G (gset (fmrole M))) (R: gset G) (r: G)
                    (DISJ: tmap_disj tm)
    :
    ls_mapping_impl (rearrange_roles_map tm R r) =
    (fun g => if (decide (g ∈ R)) then g else r) <$> (ls_mapping_impl tm). 
  Proof. 
    simpl. apply map_eq. intros ρ. 
    rewrite /rearrange_roles_map.
    rewrite lookup_fmap.
    (* pose proof (ls_mapping_tmap_corr_impl tm DISJ ρ) as MIM. *)
    destruct (ls_mapping_impl tm !! ρ) eqn:MAP.
    2: { simpl. apply not_elem_of_dom_1. simpl.
         intros [g MAP']%elem_of_dom.
         pose proof MAP as TM. eapply mim_neg with (g := g) in MAP.
         2: { by apply ls_mapping_tmap_corr_impl. }
         pose proof MAP' as TM'. apply ls_mapping_tmap_corr_impl in TM'.
         2: { by apply rrm_tmap_disj. }
         destruct TM' as (Rg & EQRg & IN).
         apply lookup_insert_Some in EQRg. 
         destruct EQRg as [[-> <-] | [NEQ IN']].
         - apply elem_of_union in IN as [? | IN]; [set_solver| ].
           apply flatten_gset_spec in IN as (?&IN'&IN).
           apply elem_of_map_img in IN' as (?&IN').
           apply map_filter_lookup_Some in IN' as [IN' ?].
           eapply mim_neg with (g := x0) in TM.
           2: { by apply ls_mapping_tmap_corr_impl. }
           by rewrite IN' in TM.
         - apply map_filter_lookup_Some in IN' as [IN' ?].
           by rewrite IN' in MAP. }
    simpl.
    apply ls_mapping_tmap_corr_impl.
    { by apply rrm_tmap_disj. }
    pose proof MAP as TM. apply ls_mapping_tmap_corr_impl in TM; [| done].
    destruct TM as (R' & TM & IN).
    setoid_rewrite lookup_insert_Some.
    destruct (decide (g ∈ R)) as [gR | ngR].
    { destruct (decide (r = g)) as [-> | NEQ].
      - eexists. split.
        { left. split; reflexivity. }
        rewrite TM. set_solver.
      - eexists. split; [| eauto].
        right. split; eauto. apply map_filter_lookup_Some. eauto. }
    eexists.  split.
    { left. split; reflexivity. }
    rewrite elem_of_union. right. apply flatten_gset_spec.
    eexists. split; eauto. apply elem_of_map_img.
    eexists. apply map_filter_lookup_Some. eauto.
  Qed. 

    
  Definition rearrange_roles (δ: lm_ls LM) (R: gset G) (r: G)
    (LSI': LSI (ls_under δ) (rearrange_roles_map (ls_tmap δ) R r) (ls_fuel δ)): 
    lm_ls LM.
    refine {| ls_under := ls_under δ;
              ls_fuel := ls_fuel δ;
              (* ls_mapping := rearrange_roles_map (ls_mapping δ) R r *)
              ls_tmap := rearrange_roles_map (ls_tmap δ) R r;
           |}.
    - apply ls_fuel_dom.
    - apply rrm_tmap_fuel_same_doms. 
    - red. rewrite /rearrange_roles_map.
      setoid_rewrite lookup_insert_Some. setoid_rewrite map_filter_lookup_Some.
      intros * NEQ TM1 TM2.

      assert (forall k2 S2 (NEQ: r ≠ k2) (tm2 : ls_tmap δ !! k2 = Some S2)
                (IN2 : k2 ∈ R),
  default ∅ (ls_tmap δ !! r)
  ∪ flatten_gset (map_img (filter (λ '(k, _), k ∉ R) (ls_tmap δ))) ## S2) as HELPER. 
      { intros. apply disjoint_union_l. split.
        * destruct (ls_tmap δ !! r) eqn:TM; [| set_solver].
          simpl. eapply ls_tmap_disj; eauto.
        * apply flatten_gset_disjoint. intros s. 
          rewrite elem_of_map_img.
          setoid_rewrite map_filter_lookup_Some.
          intros (g&?&?).
          destruct (decide (g = k0)); [subst; done| ]. 
          eapply ls_tmap_disj; eauto. }
      
      destruct TM1 as [[<- <-] | (? & tm1 & IN1)], TM2 as [[<- <-] | (? & tm2 & IN2)]. 
      { congruence. }
      + eapply HELPER; eauto.
      + apply disjoint_sym. eapply HELPER; eauto.
      + eapply ls_tmap_disj; [apply NEQ| ..]; eauto.
    - done. 
  Defined.

  Lemma rearrange_roles_spec (δ: lm_ls LM) 
    (R: gset G) (r: G)
    (LSI': LSI (ls_under δ) (rearrange_roles_map (ls_tmap δ) R r) (ls_fuel δ))
    :
    roles_rearranged δ (rearrange_roles δ R r LSI') R r.
  Proof.
    red. repeat split; simpl.
    - rewrite /rearrange_roles_map.
      rewrite dom_insert. 
      rewrite union_comm. apply union_mono; [| done].
      apply dom_filter_sub.
    - rewrite (ls_same_doms δ).
      apply set_eq. intros. rewrite elem_of_dom. 
      rewrite rrm_tmap_fuel_same_doms. 
      apply exist_proper. simpl.
      intros. rewrite ls_mapping_tmap_corr.
      simpl. reflexivity.
    - intros ?. rewrite /ls_mapping. rewrite !rrm_mapping.
      2: { apply δ. }
      simpl. rewrite !elem_of_dom !lookup_fmap. intros [g MAP].
      rewrite MAP.
      destruct (ls_mapping_impl (ls_tmap δ) !! ρ); done. 
  Qed. 

End LMFinBranching.

Section finitary.
  Context `{M: FairModel}.
  Context `{Λ: language}.
  Context `{Countable (locale Λ)}.
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
    by apply smaller_card_nat_finite in H0.
  Qed.

  Definition enum_inner extr fmodtr c' oζ : list (M * option M.(fmrole)) :=
    map proj1_sig (@enum _ _ (model_finite extr fmodtr c' oζ)).

  Lemma enum_inner_spec (δ' : M) ℓ extr atr c' oζ :
    ξ (extr :tr[oζ]: c') (atr :tr[ℓ]: δ') → (δ', ℓ) ∈ enum_inner extr atr c' oζ.
  Proof.
    intros REL. unfold enum_inner. rewrite elem_of_list_fmap.
    exists (exist _ (δ', ℓ) REL). split =>//. apply elem_of_enum.
  Qed.

  Fixpoint get_underlying_fairness_trace {M : FairModel} {LSI} {LM: LiveModel (locale Λ) M LSI} {LF: LMFairPre LM}
    (ex : auxiliary_trace (fair_model_model LM_Fair)) :=
  match ex with
  | trace_singleton δ => trace_singleton (ls_under δ)
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
    set (inner_exts := ((trace_last atr).(ls_under)) :: (map fst (enum_inner ex (get_underlying_fairness_trace atr) (e', σ') oζ))).
    set (next_threads := (locales_of_list e')).
    (* set (convert_lbl := lift_convert_lbl oζ (LM := LM)). *)

    (* eapply surjective_finite. Unshelve. *)
    set (get_ol := fun (st_ℓ: lm_ls LM * lm_lbl LM) => 
                        match st_ℓ with
                        | (st, Silent_step τ) | (st, Take_step _ τ) => (st, Some τ)
                        | (st, _) => (st, None)
                        end). 
    
    eapply (in_list_finite (get_ol <$> (enumerate_next (trace_last atr) 
                              inner_exts next_threads))).
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
      (* { done. } *)
      { inversion Htrans as [Htrans'].
        apply elem_of_cons; right.
        apply elem_of_list_fmap. 
        exists (ls_under δ', Some f). split; [done| ].  
        by apply enum_inner_spec. }
      { 
        (* intros ρ' tid' Hsome. *)
        unfold tids_smaller' in *.
        apply elem_of_subseteq. intros.
        apply Htids in H0. apply locales_of_list_from_locale_from in H0.
        apply elem_of_list_to_set. done. }
    - eapply next_TS_spec_inv_S in N.  
      2: { eexists. split; eauto. }
      clear Htrans. rename N into Htrans. 
      exists (δ', Silent_step τ). split. 
      { simpl. destruct ℓ; simpl in *; congruence || done. }
      eapply next_step_domain; eauto.
      (* { done. } *)
      { apply elem_of_cons.
        left. inversion Htrans as (?&?&?&?&?); done. }
      {
        apply elem_of_subseteq. intros.
        apply elem_of_list_to_set. apply locales_of_list_from_locale_from.
        by apply Htids. }
      
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
  Context `{CNT: Countable (locale Λ)}.
  Context `{LM: LiveModel (locale Λ) M LSI}.
  Context `{EqDecision M}.
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
    (* TODO: extract to a lemma *) 
    assert (forall tr, trace_last (get_underlying_fairness_trace tr) = ls_under (trace_last tr)) as UNDER_LAST.
    { clear. destruct tr; try done. simpl.
      (* inversion VALID. *)
      subst. destruct l.
      2: { done. }
      destruct next_TS_role; done. }
      
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
  Context `{Countable (locale Λ)}. 
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
