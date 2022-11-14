From aneris.aneris_lang Require Import aneris_lang network resources.
From aneris.prelude  Require Import gset_map.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Import traces.
From aneris.aneris_lang Require Import events.
From aneris.aneris_lang.state_interp Require Import state_interp_def.
From aneris.algebra Require Import disj_gsets.
From iris.algebra Require Import auth.

Set Default Proof Using "Type".

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  Lemma aneris_events_state_interp_same_tp ex c oζ c':
    valid_exec (ex :tr[oζ]: c') →
    trace_ends_in ex c →
    c.1 = c'.1 →
    aneris_events_state_interp (ex :tr[oζ]: c') ⊣⊢ aneris_events_state_interp ex.
  Proof.
    rewrite /aneris_events_state_interp.
    iIntros (Hexvalid Hc Heq).
    destruct c as [tp σ]; destruct c' as [tp' σ']; simplify_eq/=.
    iSplit.
    - iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
      iExists _, _, _; iFrame "#".
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
        first iFrame "Hsend"; last first.
      { intros sag; simpl; erewrite events_of_trace_extend_same_tp; [done|done| |done]; done. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
        first iFrame "Hrec"; last first.
      { intros sag; simpl; erewrite events_of_trace_extend_same_tp; [done|done| |done]; done. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (allocEV sag) ex)); first by iFrame.
      intros lbl; simpl; erewrite events_of_trace_extend_same_tp; [done|done| |done]; done.
    - iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
      iExists _, _, _; iFrame "#".
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
        first iFrame "Hsend"; last first.
      { intros sag; simpl; erewrite events_of_trace_extend_same_tp; [done|done| |done]; done. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
        first iFrame "Hrec"; last first.
      { intros sag; simpl; erewrite events_of_trace_extend_same_tp; [done|done| |done]; done. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (allocEV sag) ex)); first by iFrame.
      intros lb; simpl; erewrite events_of_trace_extend_same_tp; [done|done| |done]; done.
  Qed.

  Lemma aneris_events_state_interp_pure ex c oζ c':
    valid_exec (ex :tr[oζ]: c') →
    trace_ends_in ex c →
    c.2 = c'.2 →
    aneris_events_state_interp (ex :tr[oζ]: c') ⊣⊢ aneris_events_state_interp ex.
  Proof.
    rewrite /aneris_events_state_interp.
    iIntros (Hexvalid Hc Heq).
    destruct c as [tp σ]; destruct c' as [tp' σ']; simplify_eq/=.
    iSplit.
    - iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
      iExists _, _, _; iFrame "#".
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
        first iFrame "Hsend"; last first.
      { intros sag; simpl; erewrite events_of_trace_extend_pure;
          [done| apply sendonEV_groups_impure |done| |done]; done. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
        first iFrame "Hrec"; last first.
      { intros sag; simpl; erewrite events_of_trace_extend_pure;
          [done| apply receiveonEV_groups_impure |done| |done]; done. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (allocEV sag) ex)); first by iFrame.
      intros lbl; simpl; erewrite events_of_trace_extend_pure;
        [done| apply allocEV_impure |done| |done]; done.
    - iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
      iExists _, _, _; iFrame "#".
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
        first iFrame "Hsend"; last first.
      { intros sag; simpl; erewrite events_of_trace_extend_pure;
          [done| apply sendonEV_groups_impure |done| |done]; done. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
        first iFrame "Hrec"; last first.
      { intros sag; simpl; erewrite events_of_trace_extend_pure;
          [done| apply receiveonEV_groups_impure |done| |done]; done. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (allocEV sag) ex)); first by iFrame.
      intros lbl; simpl; erewrite events_of_trace_extend_pure;
        [done| apply allocEV_impure |done| |done]; done.
  Qed.

  Lemma aneris_events_state_interp_no_triggered' ex tp1 K e1 tp2 efs σ1 e2 σ2 oζ:
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    (∀ sag, ¬ sendonEV_groups sag e1 σ1 e2 σ2) →
    (∀ sag, ¬ receiveonEV_groups sag e1 σ1 e2 σ2) →
    (∀ lbl, ¬ allocEV lbl e1 σ1 e2 σ2) →
    aneris_events_state_interp (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) ⊣⊢ aneris_events_state_interp ex.
  Proof.
    rewrite /aneris_events_state_interp.
    iIntros (Hexvalid Hei Hstep Hns Hnr Hna).
    iSplit.
    - iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
      iExists _, _, _; iFrame "#".
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
        first iFrame "Hsend"; last first.
      { intros sag; simpl. rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); eauto. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
        first iFrame "Hrec"; last first.
      { intros sag; simpl. rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); eauto. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (allocEV sag) ex)); first by iFrame.
      intros lbl; simpl. rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); eauto.
    - iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
      iExists _, _, _; iFrame "#".
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
        first iFrame "Hsend"; last first.
      { intros sag; simpl. rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); eauto. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
        first iFrame "Hrec"; last first.
      { intros sag; simpl. rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); eauto. }
      erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (allocEV sag) ex)); first by iFrame.
      intros lbl; simpl. rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); eauto.
  Qed.

  Lemma aneris_events_state_interp_no_triggered ex tp1 K e1 tp2 efs σ1 e2 σ2 oζ :
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    (∀ sh mbody to, expr_e e1 ≠ SendTo sh mbody to ) →
    (∀ sh, expr_e e1 ≠ ReceiveFrom sh) →
    (∀ lbl e', expr_e e1 ≠ ref<< lbl >> e')%E →
    aneris_events_state_interp (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) ⊣⊢ aneris_events_state_interp ex.
  Proof.
    intros ??? Hns Hnr Hna.
    eapply aneris_events_state_interp_no_triggered'; [done|done|done| | |].
    - intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      eapply Hns; simplify_eq; done.
    - intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?).
      eapply Hnr; simplify_eq; done.
    - intros ? (?&?&?&?&?&?&?&?&?).
      eapply Hna; simplify_eq; done.
  Qed.

  Lemma aneris_events_state_interp_alloc_triggered lbl evs ex tp1 K e1 tp2 efs
        σ1 e2 σ2 oζ :
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    allocEV lbl e1 σ1 e2 σ2 →
    alloc_evs lbl evs -∗
    aneris_events_state_interp ex ==∗
    aneris_events_state_interp (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) ∗
    alloc_evs lbl (evs ++ [mkEventObservation e1 σ1 e2 σ2]).
  Proof.
    rewrite /aneris_events_state_interp.
    iIntros (Hexvalid Hei Hstep HEV) "Hevs".
    iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
    iDestruct (alloc_evs_lookup with "Halloc Hevs") as %[Hexevs ?]%lookup_fn_to_gmap.
    iMod (alloc_evs_update with "Halloc Hevs") as "[Halloc $]".
    iModIntro.
    iExists _, _, _; iFrame "#".
    erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
      first iFrame "Hsend"; last first.
    { intros sag; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_alloc_groups; eauto. }
    erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
      first iFrame "Hrec"; last first.
    { intros sag; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_alloc_groups; eauto. }
    rewrite -fn_to_gmap_insert //.
    erewrite fn_to_gmap_eq_fns; first iFrame "Halloc"; last first.
    intros lbl'; simpl.
    destruct (decide (lbl' = lbl)) as [->|Hneq].
    - rewrite fn_lookup_insert.
      rewrite -Hexevs.
      rewrite (events_of_trace_extend_triggered _ _ _ _ _ e1 _ _ σ1); eauto.
    - rewrite fn_lookup_insert_ne //.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); [done|done|done|done|].
      intros ?; apply Hneq; eapply allocEV_inj; done.
  Qed.

  Lemma aneris_events_state_interp_send_triggered sag evs ex tp1 K e1 tp2 efs
  σ1 e2 σ2 oζ:
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    sendonEV_groups sag e1 σ1 e2 σ2 →
    sendon_evs_groups sag evs -∗
    aneris_events_state_interp ex ==∗
    aneris_events_state_interp (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) ∗
    sendon_evs_groups sag (evs ++ [mkEventObservation e1 σ1 e2 σ2]).
  Proof.
    rewrite /aneris_events_state_interp.
    iIntros (Hexvalid Hei Hstep HEV) "Hevs".
    iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
    iDestruct (sendon_evs_lookup with "Hsend Hevs") as %[Hexevs ?]%lookup_fn_to_gmap.
    iMod (sendon_evs_update with "Hsend Hevs") as "[Hsend $]".
    iModIntro.
    iDestruct (own_valid with "Hown") as %Hvalid.
    setoid_rewrite auth_frag_valid in Hvalid.
    setoid_rewrite disj_gsets_valid in Hvalid.
    iExists _, _, _; iFrame "#".
    erewrite (fn_to_gmap_eq_fns _ (λ lbl, events_of_trace (allocEV lbl) ex));
      first iFrame "Halloc"; last first.
    { intros lbl; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_sendon_groups; eauto. }
    erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
      first iFrame "Hrec"; last first.
    { intros sag'; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_sendon_groups; eauto. }
    rewrite -fn_to_gmap_insert //.
    erewrite fn_to_gmap_eq_fns; first iFrame "Hsend"; last first.
    intros sag' Hsag'.
    destruct (decide (sag' = sag)) as [->|Hneq].
    - rewrite fn_lookup_insert.
      rewrite -Hexevs.
      rewrite (events_of_trace_extend_triggered _ _ _ _ _ e1 _ _ σ1); eauto.
    - rewrite fn_lookup_insert_ne //.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); [done|done|done|done|].
      intros ?. apply Hneq.
      eapply sendonEV_groups_inj; [ apply Hvalid; set_solver | | ]; done.
  Qed.

  Lemma aneris_events_state_interp_send_untracked sag rtrck R T ex tp1 K e1 tp2
        efs σ1 e2 σ2 oζ:
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    sendonEV_groups sag e1 σ1 e2 σ2 →
    sag ⤳*[false, rtrck] (R, T) -∗
    aneris_events_state_interp ex -∗
    aneris_events_state_interp (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) ∗
    sag ⤳*[false, rtrck] (R, T).
  Proof.
    rewrite /aneris_events_state_interp.
    iIntros (Hexvalid Hei Hstep HEV) "Hsag".
    iDestruct (messages_mapsto_observed with "Hsag") as "[$ Hsag]".
    iDestruct "Hsag" as (As Ar) "(#HAs&#HAr&#Hown&%HAssa&%HArsa)".
    iDestruct 1 as (As' Ar' lbls) "(#Hown'&#HAs'&#HAr'&Hsend&Hrecv&Halloc)".
    iDestruct (observed_send_agree with "HAs HAs'") as %<-.
    iDestruct (observed_receive_agree with "HAr HAr'") as %<-.
    iExists _, _, _; iFrame "#".
    iDestruct (own_op with "[Hown Hown']") as "Hown''".
    { iSplit; [ iApply "Hown" | iApply "Hown'" ]. }
    rewrite -auth_frag_op.
    iDestruct (own_valid with "Hown''") as %Hvalid.
    setoid_rewrite auth_frag_valid in Hvalid.
    setoid_rewrite disj_gsets_valid in Hvalid.
    erewrite (fn_to_gmap_eq_fns _ (λ lbl, events_of_trace (allocEV lbl) ex));
      first iFrame "Halloc"; last first.
    { intros lbl; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_sendon_groups; eauto. }
    erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (receiveonEV_groups sag) ex));
      first iFrame "Hrecv"; last first.
    { intros sag'; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_sendon_groups; eauto. }
    erewrite fn_to_gmap_eq_fns; first iFrame "Hsend"; last first.
    intros sag'.
    destruct (decide (sag' = sag)) as [->|Hneq].
    - rewrite HAssa; done.
    - intros Hsa'.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); [done|done|done|done|].
      intros ?; apply Hneq. eapply sendonEV_groups_inj; eauto.
      apply Hvalid; set_solver.
  Qed.

  Lemma aneris_events_state_interp_receive_triggered sag evs ex tp1 K e1 tp2
        efs σ1 e2 σ2 oζ :
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    receiveonEV_groups sag e1 σ1 e2 σ2 →
    receiveon_evs_groups sag evs -∗
    aneris_events_state_interp ex ==∗
    aneris_events_state_interp (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) ∗
    receiveon_evs_groups sag (evs ++ [mkEventObservation e1 σ1 e2 σ2]).
  Proof.
    rewrite /aneris_events_state_interp.
    iIntros (Hexvalid Hei Hstep HEV) "Hevs".
    iDestruct 1 as (As Ar lbls) "(#Hown&#HAs&#HAr&Hsend&Hrec&Halloc)".
    iDestruct (receiveon_evs_lookup with "Hrec Hevs")
      as %[Hexevs ?]%lookup_fn_to_gmap.
    iMod (receiveon_evs_update with "Hrec Hevs") as "[Hrec $]".
    iDestruct (own_valid with "Hown") as %Hvalid.
    setoid_rewrite auth_frag_valid in Hvalid.
    setoid_rewrite disj_gsets_valid in Hvalid.
    iModIntro.
    iExists _, _, _; iFrame "#".
    erewrite (fn_to_gmap_eq_fns _ (λ lbl, events_of_trace (allocEV lbl) ex));
      first iFrame "Halloc"; last first.
    { intros lbl; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_receiveon_groups; eauto. }
    erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
      first iFrame "Hsend"; last first.
    { intros sag'; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_receiveon_groups; eauto. }
    rewrite -fn_to_gmap_insert //.
    erewrite fn_to_gmap_eq_fns; first iFrame "Hrec"; last first.
    intros sag' Hsag'.
    destruct (decide (sag' = sag)) as [->|Hneq].
    - rewrite fn_lookup_insert.
      rewrite -Hexevs.
      rewrite (events_of_trace_extend_triggered _ _ _ _ _ e1 _ _ σ1); eauto.
    - rewrite fn_lookup_insert_ne //.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); [done|done|done|done|].
      intros ?; apply Hneq.
      eapply receiveonEV_groups_inj; [ apply Hvalid; set_solver | | ]; done.
  Qed.

  Lemma aneris_events_state_interp_receive_untracked sag strck R T ex tp1 K e1
        tp2 efs σ1 e2 σ2 oζ :
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    receiveonEV_groups sag e1 σ1 e2 σ2 →
    sag ⤳*[strck, false] (R, T) -∗
    aneris_events_state_interp ex -∗
    aneris_events_state_interp (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) ∗
    sag ⤳*[strck, false] (R, T).
  Proof.
    rewrite /aneris_events_state_interp.
    iIntros (Hexvalid Hei Hstep HEV) "Hsag".
    iDestruct (messages_mapsto_observed with "Hsag") as "[$ Hsag]".
    iDestruct "Hsag" as (As Ar) "(#HAs&#HAr&#Hown&%HAssa&%HArsa)".
    iDestruct 1 as (As' Ar' lbls) "(#Hown'&HAs'&#HAr'&Hsend&Hrec&Halloc)".
    iDestruct (observed_send_agree with "HAs HAs'") as %<-.
    iDestruct (observed_receive_agree with "HAr HAr'") as %<-.
    iExists _, _, _; iFrame "#".
    iDestruct (own_op with "[Hown Hown']") as "Hown''".
    { iSplit; [ iApply "Hown" | iApply "Hown'" ]. }
    rewrite -auth_frag_op.
    iDestruct (own_valid with "Hown''") as %Hvalid.
    setoid_rewrite auth_frag_valid in Hvalid.
    setoid_rewrite disj_gsets_valid in Hvalid.
    erewrite (fn_to_gmap_eq_fns _ (λ lbl, events_of_trace (allocEV lbl) ex));
      first iFrame "Halloc"; last first.
    { intros lbl; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_receiveon_groups; eauto. }
    erewrite (fn_to_gmap_eq_fns _ (λ sag, events_of_trace (sendonEV_groups sag) ex));
      first iFrame "Hsend"; last first.
    { intros sag'; simpl.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1);
        last eapply ev_not_others_receiveon_groups; eauto. }
    erewrite fn_to_gmap_eq_fns; first iFrame "Hrec"; last first.
    intros sag'.
    destruct (decide (sag' = sag)) as [->|Hneq].
    - rewrite HArsa; done.
    - intros  Hsag'.
      rewrite (events_of_trace_extend_not_triggered _ _ _ _ _ e1 _ _ σ1); [done|done|done|done|].
      intros ?; apply Hneq; eapply receiveonEV_groups_inj; try eauto.
      apply Hvalid; set_solver.
  Qed.

End state_interpretation.
