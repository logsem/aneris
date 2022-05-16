From trillium.prelude Require Import classical.
From trillium.traces Require Import trace.
From trillium.program_logic Require Import
     ectx_language language traces.

(** Ideally, all definitions in this file should be computational.
    But that's is too much work. Hence, since we already assume classical
    axioms in this work we can use those to axiomatize the function that
    given an execution extracts its observations. *)

Record Event (Λ : language) := mkEvent {
  is_triggered :> expr Λ → state Λ → expr Λ → state Λ → Prop;
  (* The following two axioms ensure that events are only triggered
     on head steps. *)
  is_triggered_not_val :
    ∀ e1 σ1 e2 σ2, is_triggered e1 σ1 e2 σ2 → to_val e1 = None;
  is_triggered_ectx_free :
    ∀ e1 σ1 e2 σ2,
      is_triggered e1 σ1 e2 σ2 →
      ∀ K e1', e1 = ectx_fill K e1' → is_Some (to_val e1') ∨ K = ectx_emp;
  is_triggered_not_stuttering :
    ∀ e1 σ1 e2 σ2,
      is_triggered e1 σ1 e2 σ2 → e1 ≠ e2;
}.

Arguments is_triggered {_} _ _ _ _.
Arguments is_triggered_not_val {_} _ _ _ _.
Arguments is_triggered_ectx_free {_} _.
Arguments is_triggered_not_stuttering {_} _.

Record EventObservation (Λ : language) := mkEventObservation {
  pre_expr : expr Λ;
  pre_state : state Λ;
  post_expr : expr Λ;
  post_state : state Λ;
}.

Arguments mkEventObservation {_} _ _ _ _.
Arguments pre_state {_} _.
Arguments pre_expr {_} _.
Arguments post_state {_} _.
Arguments post_expr {_} _.

Definition validEventObservation
           {Λ : language} (EV : Event Λ) (eo : EventObservation Λ) :=
  EV eo.(pre_expr) eo.(pre_state) eo.(post_expr) eo.(post_state).

Definition event_obs (Λ : language) := list (EventObservation Λ).

Definition valid_event_obs
           {Λ : language} (EV : Event Λ) (eo : event_obs Λ)  : Prop :=
  Forall (validEventObservation EV) eo.

Inductive trace_has_events {Λ : language} (EV : Event Λ) :
          execution_trace Λ → event_obs Λ → Prop :=
| singleton_events c : trace_has_events EV {tr[c]} []
| extend_observed ex c c' tp1 tp2 efs K eo eobs oζ:
    trace_ends_in ex c →
    c.2 = eo.(pre_state) →
    c.1 = tp1 ++ ectx_fill K eo.(pre_expr) :: tp2 →
    c'.2 = eo.(post_state) →
    c'.1 = tp1 ++ ectx_fill K eo.(post_expr) :: tp2 ++ efs →
    validEventObservation EV eo →
    trace_has_events EV ex eobs →
    trace_has_events EV (ex :tr[oζ]: c') (eobs ++ [eo])
| extend_not_observed ex c c' eobs oζ:
    trace_ends_in ex c →
    (∀ tp1 tp2 efs K e1 e2,
      c.1 = tp1 ++ ectx_fill K e1 :: tp2 →
      c'.1 = tp1 ++ ectx_fill K e2 :: tp2 ++ efs →
      ¬ EV e1 c.2 e2 c'.2) →
    trace_has_events EV ex eobs →
    trace_has_events EV (ex :tr[oζ]: c') eobs.

Section properties.
  Context {Λ : language} (EV : Event Λ).

  Implicit Types e : expr Λ.
  Implicit Types tp : list (expr Λ).
  Implicit Types σ : state Λ.
  Implicit Types eobs : event_obs Λ.
  Implicit Types obs : EventObservation Λ.
  Implicit Types ex : execution_trace Λ.

  Lemma validEventObservation_exprs_neq obs :
    validEventObservation EV obs → obs.(pre_expr) ≠ obs.(post_expr).
  Proof. intros; eapply is_triggered_not_stuttering; done. Qed.

  Lemma validEventObservation_not_val obs :
    validEventObservation EV obs → to_val obs.(pre_expr) = None.
  Proof. intros; eapply is_triggered_not_val; done. Qed.

  Lemma trace_has_events_valid ex eobs :
    trace_has_events EV ex eobs → valid_event_obs EV eobs.
  Proof.
    induction 1 as [|ex [tp σ] [tp' σ']|]; simplify_eq/=.
    - by constructor.
    - apply Forall_app; split; first done.
      apply Forall_singleton; done.
    - done.
  Qed.

  Lemma event_in_the_middle tp1 tp2 K e1 e2 efs tp1' tp2' K' eo efs' :
    validEventObservation EV eo →
    to_val e1 = None →
    (∀ e1' K'', e1 = ectx_fill K'' e1' → is_Some (to_val e1') ∨ K'' = ectx_emp) →
    tp1 ++ ectx_fill K e1 :: tp2 = tp1' ++ ectx_fill K' (pre_expr eo) :: tp2' →
    tp1 ++ ectx_fill K e2 :: tp2 ++ efs =
    tp1' ++ ectx_fill K' (post_expr eo) :: tp2' ++ efs' →
    pre_expr eo = e1 ∧ post_expr eo = e2.
  Proof.
    intros HEV He1 Hnectx Heq1 Heq2.
    destruct (decide (length tp1' < length tp1)).
    { pose proof (f_equal (λ x, x !! length tp1') Heq1) as Heq1'.
      rewrite /= lookup_app_l // lookup_app_r // Nat.sub_diag /= in Heq1'.
      pose proof (f_equal (λ x, x !! length tp1') Heq2) as Heq2'.
      rewrite /= lookup_app_l // lookup_app_r // Nat.sub_diag /= in Heq2'.
      rewrite Heq1' in Heq2'; simplify_eq.
      apply ectx_fill_inj in Heq2'.
      exfalso; eapply validEventObservation_exprs_neq; done. }
    pose proof (f_equal (λ x, x !! length tp1') Heq1) as Heq1'.
    rewrite /= lookup_app_r in Heq1'; last lia.
    rewrite // lookup_app_r // Nat.sub_diag /= in Heq1'.
    pose proof (f_equal (λ x, x !! length tp1') Heq2) as Heq2'.
    rewrite /= lookup_app_r in Heq2'; last lia.
    rewrite // lookup_app_r // Nat.sub_diag /= in Heq2'.
    rewrite /= app_comm_cons lookup_app_l in Heq2'; last first.
    { simpl.
      assert (length tp1' < length tp1 + S (length tp2)); last lia.
      pose proof (f_equal length Heq1) as Heq'.
      rewrite !app_length //= in Heq'; lia. }
    destruct (length tp1' - length tp1); last first.
    { simpl in *.
      rewrite Heq1' in Heq2'; simplify_eq.
      apply ectx_fill_inj in Heq2'.
      exfalso; eapply validEventObservation_exprs_neq; done. }
    simplify_eq/=.
    pose proof Heq1' as Heq1''.
    apply ectx_fill_positive in Heq1'' as [[K'' ->]|[K'' ->]];
          [| |done|
             by apply validEventObservation_not_val].
    - rewrite ectx_comp_comp in Heq2'.
      apply ectx_fill_inj in Heq2'.
      rewrite ectx_comp_comp in Heq1'.
      apply ectx_fill_inj in Heq1'.
      simplify_eq.
      assert (K'' = ectx_emp) as ->.
      { edestruct Hnectx as [[]|]; [done| |done].
        pose proof (validEventObservation_not_val _ HEV); simplify_eq. }
      rewrite !ectx_fill_emp; done.
    - rewrite ectx_comp_comp in Heq1'.
      apply ectx_fill_inj in Heq1'.
      rewrite ectx_comp_comp in Heq2'.
      apply ectx_fill_inj in Heq2'.
      assert (K'' = ectx_emp) as ->.
      { edestruct @is_triggered_ectx_free as [[]|];
          [done|symmetry; done| |done].
        pose proof (validEventObservation_not_val _ HEV); simplify_eq. }
      rewrite ectx_fill_emp in Heq1'.
      rewrite ectx_fill_emp in Heq2'.
      simplify_eq; done.
  Qed.

  (** This lemma, proven completely constructively, is an evidence why we
      are justified in using classical logic in constructing observations of
      a valid execution trace. *)
  Lemma trace_has_events_functional ex eobs eobs' :
    valid_exec ex →
    trace_has_events EV ex eobs →
    trace_has_events EV ex eobs' →
    eobs = eobs'.
  Proof.
    intros Hex; revert eobs eobs'.
    induction Hex as [|ex [tp σ] oζ [tp' σ'] Hendsin Hstep Hex IHex];
      intros eobs eobs'.
    { do 2 inversion 1; simplify_eq; done. }
    inversion 1 as [|ex' [tpz σz] [tpy σy] tp1z tp2z ? ? obs3 ? eobs3 Hendsin'|
                    ex' [tpz σz] [tpy σy] ? ? Hendsin' Hnobs]; simplify_eq/=.
    - pose proof (trace_ends_in_inj _ _ _ Hendsin Hendsin'); simplify_eq.
      inversion 1 as [|ex' [tpx σx] [tpw σw] tp1x tp2x ? ? obs4 ? eobs4 Hendsin''
                           ??? Htpseq| ex' [tpx σx] [tpw σw] ? ? Hendsin'' Hnobs];
        simplify_eq/=.
      + repeat f_equal; first by apply IHex.
        pose proof (trace_ends_in_inj _ _ _ Hendsin' Hendsin'') as Htpseq'.
        simplify_eq Htpseq'; intros Htpseq'1 Htpseq'2; clear Htpseq'.
        assert (pre_expr obs3 = pre_expr obs4 ∧ post_expr obs3 = post_expr obs4)
          as [? ?].
        eapply event_in_the_middle; [done| | |done|].
        { apply validEventObservation_not_val; done. }
        { intros; eapply is_triggered_ectx_free; eauto. }
        { done. }
        destruct obs3; destruct obs4; simplify_eq/=; done.
      + pose proof (trace_ends_in_inj _ _ _ Hendsin Hendsin''); simplify_eq.
        exfalso; eapply Hnobs; eauto.
    - pose proof (trace_ends_in_inj _ _ _ Hendsin Hendsin'); simplify_eq.
      inversion 1 as [|ex' [tpx σx] [tpw σw] ? ? ? ? obs4 eobs4 ?  Hendsin''|
                    ex' [tpx σx] [tpw σw] ? Hendsin'' Hnobs']; simplify_eq/=.
      + pose proof (trace_ends_in_inj _ _ _ Hendsin Hendsin''); simplify_eq.
        exfalso; eapply Hnobs; eauto.
      + apply IHex; done.
  Qed.

  Lemma trace_has_valid_events ex eobs :
    trace_has_events EV ex eobs → valid_event_obs EV eobs.
  Proof.
    induction 1; [constructor| |done].
    apply Forall_app_2; first done.
    apply Forall_singleton; done.
  Qed.

  Lemma events_for_trace ex : ∃ eobs, trace_has_events EV ex eobs.
  Proof.
    induction ex as [c|ex [eobs Hthe] ? c].
    { eexists; econstructor. }
    destruct (ExcludedMiddle ((∃ tp1 tp2 efs K e1 e2,
      (trace_last ex).1 = tp1 ++ ectx_fill K e1 :: tp2 ∧
      c.1 = tp1 ++ ectx_fill K e2 :: tp2 ++ efs ∧
      EV e1 (trace_last ex).2 e2 c.2))) as
        [(tp1&tp2&efs&K&e1&e2&Heq1&Heq2&HEV)|Hnex].
    - exists (eobs ++ [mkEventObservation e1 (trace_last ex).2 e2 c.2]).
      econstructor; eauto using trace_ends_in_last.
    - exists eobs; econstructor; [done| |done].
      intros ?????????; apply Hnex; eauto 10.
  Qed.

  Definition events_of_trace ex : event_obs Λ := epsilon (events_for_trace ex).

  Lemma trace_has_events_of_trace ex :
    trace_has_events EV ex (events_of_trace ex).
  Proof. apply (epsilon_correct _ (events_for_trace ex)). Qed.

  Lemma events_of_trace_valid ex : valid_event_obs EV (events_of_trace ex).
  Proof. eapply trace_has_valid_events; apply trace_has_events_of_trace. Qed.

  Lemma events_of_trace_extend_same_tp ex c c' oζ:
    valid_exec (ex :tr[oζ]: c') →
    c.1 = c'.1 →
    trace_ends_in ex c →
    events_of_trace (ex :tr[oζ]: c') = events_of_trace ex.
  Proof.
    intros Hex Htps Hc.
    destruct c as [tp σ]; destruct c' as [tp' σ']; simplify_eq/=.
    cut (∀ eobs, trace_has_events EV (ex :tr[oζ]: (tp', σ')) eobs → events_of_trace ex = eobs).
    { intros Help. erewrite Help; first done. apply trace_has_events_of_trace. }
    intros eobs Heobs.
    eapply trace_has_events_functional; [|apply trace_has_events_of_trace|].
    { inversion Hex; done. }
    inversion Heobs as [|?????? K ??? Hei|]; simplify_eq/=; last done.
    pose proof (trace_ends_in_inj _ _ _ Hc Hei); simplify_eq/=.
    exfalso; eapply validEventObservation_exprs_neq; first done.
    eapply ectx_fill_inj; done.
  Qed.

  Lemma events_of_singleton_trace c : events_of_trace {tr[c]} = [].
  Proof.
    eapply trace_has_events_functional;
      [constructor|apply trace_has_events_of_trace|constructor].
  Qed.

  Lemma events_of_trace_extend_pure ex c c' oζ:
    (∀ eo, validEventObservation EV eo → eo.(pre_state) ≠ eo.(post_state)) →
    valid_exec (ex :tr[oζ]: c') →
    c.2 = c'.2 →
    trace_ends_in ex c →
    events_of_trace (ex :tr[oζ]: c') = events_of_trace ex.
  Proof.
    intros Himpure Hex Htps Hc.
    destruct c as [tp σ]; destruct c' as [tp' σ']; simplify_eq/=.
    cut (∀ eobs, trace_has_events EV (ex :tr[oζ]: (tp', σ')) eobs → events_of_trace ex = eobs).
    { intros Help. erewrite Help; first done. apply trace_has_events_of_trace. }
    intros eobs Heobs.
    eapply trace_has_events_functional; [|apply trace_has_events_of_trace|].
    { inversion Hex; done. }
    inversion Heobs as [|?????? K ??? Hei|]; simplify_eq/=; last done.
    pose proof (trace_ends_in_inj _ _ _ Hc Hei); simplify_eq/=.
    exfalso; eapply Himpure; eauto.
  Qed.

    Definition event_is_triggered (ob : EventObservation Λ) (c c' : cfg Λ) :=
    ∃ K tp1 tp2 efs,
      c.2 = ob.(pre_state) ∧
      c.1 = tp1 ++ ectx_fill K ob.(pre_expr) :: tp2 ∧
      c'.2 = ob.(post_state) ∧
      c'.1 = tp1 ++ ectx_fill K ob.(post_expr) :: tp2 ++ efs.

  Lemma events_of_trace_extend_app (ex : execution_trace Λ) (c : cfg Λ) oζ:
    valid_exec (ex :tr[oζ]: c) →
    ∃ evs,
      length evs ≤ 1 ∧
      events_of_trace (ex :tr[oζ]: c) = events_of_trace ex ++ evs ∧
      ∀ ev, ev ∈ evs → event_is_triggered ev (trace_last ex) c.
  Proof.
    intros Hvl.
    pose proof (trace_has_events_of_trace (ex :tr[oζ]: c)) as Hthe.
    inversion Hthe as [|?????????? Hend|]; simplify_eq.
    - eexists [_]; split; first done.
      erewrite (trace_has_events_functional ex (events_of_trace ex));
        [|by eapply valid_exec_exec_extend_inv; eauto|by apply trace_has_events_of_trace|by eauto].
      split; first done.
      intros ev; rewrite elem_of_list_singleton; intros ->.
      apply last_eq_trace_ends_in in Hend; simplify_eq.
      eexists _, _, _, _; eauto.
    - exists []; split; simpl; first lia.
      rewrite app_nil_r.
      split; last set_solver.
      apply (trace_has_events_functional (ex :tr[oζ]: c)); [done|by apply trace_has_events_of_trace|].
      eapply extend_not_observed; [eauto|eauto|by apply trace_has_events_of_trace].
  Qed.

  Lemma events_of_trace_app (ex : execution_trace Λ) (l : list (olocale Λ * cfg Λ)) :
    valid_exec (ex +trl+ l) →
    ∃ evs,
      length evs ≤ length l ∧
      events_of_trace (ex +trl+ l) = events_of_trace ex ++ evs ∧
      ∀ ev  oζ1 oζ2,
        ev ∈ evs →
        ∃ i c1 c2 oζ1' oζ2',
          ((oζ1, trace_last ex) :: l) !! i = Some (oζ1', c1) ∧
          ((oζ2, trace_last ex) :: l) !! S i = Some (oζ2', c2) ∧
          event_is_triggered ev c1 c2.
  Proof.
    induction l as [|[??]  ?] using rev_ind.
    { exists []; rewrite /= app_nil_r; split_and!; [done|done|]. set_solver. }
    rewrite -trace_append_list_assoc /=.
    intros Hvl.
    destruct IHl as (evs & Hevs1 & Hevs2 & Hevs3).
    { eapply valid_exec_exec_extend_inv; eauto. }
    apply events_of_trace_extend_app in Hvl as (evs' & Hevs'1 & Hevs'2 & Hevs'3).
    rewrite Hevs2 in Hevs'2; rewrite Hevs'2.
    rewrite -app_assoc.
    eexists; split_and!; [|done|].
    { rewrite !app_length /=; lia. }
    intros ev oζ1 oζ2 [Hev|Hev]%elem_of_app.
    - destruct (Hevs3 ev oζ1 oζ2 Hev) as (i & c1 & c2 & oζ1' & oζ2' & Hc1 & Hc2 & Htrg).
      exists i, c1, c2, oζ1', oζ2'.
      rewrite (lookup_app_l (_ :: _)); last first.
      { apply lookup_lt_Some in Hc1; simpl in *; lia. }
      rewrite lookup_app_l; last first.
      { apply lookup_lt_Some in Hc2; simpl in *; lia. }
      done.
    - destruct (trace_last_of_append_list ex l oζ1) as [oζ Heq].
      eexists (length l), _, _, oζ, _; split_and!; last by apply Hevs'3.
      + rewrite -Heq.
        rewrite (lookup_app_l (_ :: _)); first done.
        simpl; lia.
      + rewrite lookup_app_r; last done.
        rewrite Nat.sub_diag //.
  Qed.

  Lemma events_of_trace_app_map (ex : execution_trace Λ) (l : list (olocale Λ * cfg Λ)) :
    valid_exec (ex +trl+ l) →
    ∃ evs,
      length evs ≤ length l ∧
      events_of_trace (ex +trl+ l) = events_of_trace ex ++ evs ∧
      ∀ ev,
        ev ∈ evs →
        ∃ i c1 c2,
          (trace_last ex :: map snd l) !! i = Some c1 ∧
          (trace_last ex ::  map snd l) !! S i = Some c2 ∧
          event_is_triggered ev c1 c2.
  Proof.
    intros Hval. destruct (events_of_trace_app ex l Hval) as (evs & Hlen & Hevs & H).
    exists evs; repeat (split =>//). intros ev Hin.
    destruct (H ev inhabitant inhabitant Hin) as (i & c1 & c2 & oζ1 & oζ2 & Hi & HSi & Htrig).
    exists i, c1, c2. change (trace_last ex :: map snd l) with (map snd $ (inhabitant, trace_last ex) :: l).
    rewrite ->!list_lookup_fmap, Hi, HSi. done.
  Qed.
End properties.

Section properties.
  Context {Λ : ectxLanguage} (EV : Event Λ).

  Implicit Types e : expr Λ.
  Implicit Types tp : list (expr Λ).
  Implicit Types K : ectx Λ.
  Implicit Types σ : state Λ.
  Implicit Types eobs : event_obs Λ.
  Implicit Types obs : EventObservation Λ.
  Implicit Types ex : execution_trace Λ.

  Lemma events_of_trace_extend_triggered ex tp1 tp2 K e1 e2 efs σ1 σ2 oζ :
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    EV e1 σ1 e2 σ2 →
    events_of_trace EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) =
    events_of_trace EV ex ++ [mkEventObservation e1 σ1 e2 σ2].
  Proof.
    intros HexV Hex Hhstep HEV.
    pose proof (trace_has_events_of_trace
                  EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2))) as Hhasevs.
    inversion Hhasevs as
        [|??? tp1' tp2' efs' K' eo eobs ? Hei ? Heq1 ? Heq2 HEV' ? Heq3 Heq4|
         ????? Hei HnEV]; simplify_eq.
    - pose proof (trace_ends_in_inj _ _ _ Hex Hei); simplify_eq.
      rewrite -Heq4.
      assert (eobs = events_of_trace EV ex) as ->.
      { eapply trace_has_events_functional;
          [done|done| apply trace_has_events_of_trace]. }
      repeat f_equal. simpl in *.
      assert (pre_expr eo = e1 ∧ post_expr eo = e2) as [? ?].
      eapply event_in_the_middle; [done| | |done|].
      { eapply val_head_stuck; done. }
      { intros ?? ->; eapply head_ctx_step_val; done. }
      { done. }
      destruct eo; simplify_eq/=; done.
    - pose proof (trace_ends_in_inj _ _ _ Hex Hei); simplify_eq.
      exfalso; eapply HnEV; eauto.
  Qed.

  Lemma events_of_trace_extend_not_triggered ex tp1 tp2 K e1 e2 efs σ1 σ2 oζ:
    valid_exec ex →
    trace_ends_in ex (tp1 ++ fill K e1 :: tp2, σ1) →
    head_step e1 σ1 e2 σ2 efs →
    ¬ EV e1 σ1 e2 σ2 →
    events_of_trace EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2)) =
    events_of_trace EV ex.
  Proof.
    intros HexV Hex Hhstep HEV.
    pose proof (trace_has_events_of_trace
                  EV (ex :tr[oζ]: (tp1 ++ fill K e2 :: tp2 ++ efs, σ2))) as Hhasevs.
    inversion Hhasevs as
        [|??? tp1' tp2' efs' K' eo eobs ? Hei ? Heq1 ? Heq2 HEV' ? Heq3 Heq4|
         ????? Hei HnEV Hhasevs']; simplify_eq/=.
    - pose proof (trace_ends_in_inj _ _ _ Hex Hei); simplify_eq/=.
      exfalso.
      assert (pre_expr eo = e1 ∧ post_expr eo = e2) as [? ?].
      eapply event_in_the_middle; [done| | |done|].
      { eapply val_head_stuck; done. }
      { intros ?? ->; eapply head_ctx_step_val; done. }
      { done. }
      destruct eo; simplify_eq/=; done.
    - pose proof (trace_ends_in_inj _ _ _ Hex Hei); simplify_eq.
      eapply trace_has_events_functional;
        [done|done| apply trace_has_events_of_trace].
  Qed.

End properties.
