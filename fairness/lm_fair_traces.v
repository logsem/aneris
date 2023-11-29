From trillium.fairness Require Import fuel lm_fair trace_helpers inftraces trace_lookup.
From Paco Require Import paco1 paco2 pacotac.

Section aux_trace.  
  Context `{LM: LiveModel G M LSI}.
  Context {LF: LMFairPre LM}. 

  (* Definition auxtrace := trace LM.(lm_ls) LM.(lm_lbl). *)
  Definition lmftrace := mtrace LM_Fair.
  (* Definition foo := trace (mstate LM) (option G).  *)
  (* Goal forall (t1: lmftrace) (t2: foo), t1 = t2.  *)  

  Definition role_enabled ρ (δ: LiveState G M LSI) := ρ ∈ M.(live_roles) δ.

  Definition lbl_with_role (ρ: fmrole M) (ℓ: lm_lbl LM) := 
    ∃ tid, ℓ = Take_step ρ tid.

  Definition is_TS (l: lm_lbl LM) :=
    match l with | Take_step _ _ => true | _ => false end.
 
  Definition next_TS_role δ1 (τ: G) δ2: option (fmrole M) :=
    let lbls := allowed_step_FLs δ1 τ δ2 (LM := LM) in
    let lbls_TS := filter is_TS lbls in
    match (elements lbls_TS) with
    | Take_step ρ _ ::_ => Some ρ
    | _ => None
    end. 

  Lemma next_TS_spec_pos δ1 τ δ2 ρ:
    next_TS_role δ1 τ δ2 = Some ρ ->
    lm_ls_trans LM δ1 (Take_step ρ τ) δ2.
  Proof. 
    (* rewrite /next_TS_role.  *)
  Admitted.

  Lemma next_TS_spec_inv_TS δ1 τ δ2 ρ:
    lm_ls_trans LM δ1 (Take_step ρ τ) δ2 ->
    exists ρ', next_TS_role δ1 τ δ2 = Some ρ'. 
  Proof. 
    intros TRANS.
    rewrite /next_TS_role.
    (* /allowed_step_FLs. *)
    destruct (decide (filter is_TS (allowed_step_FLs δ1 τ δ2) = ∅)).
    { exfalso. eapply filter_empty_not_elem_of_L; [| apply e|..].
      3: { rewrite /allowed_step_FLs. apply elem_of_filter. split.
           { apply bool_decide_eq_true. eauto. }
           rewrite /potential_step_FLs. apply elem_of_union_r.
           apply elem_of_map. eexists. split; eauto.
           rewrite -ls_same_doms. simpl in TRANS. apply elem_of_dom. set_solver. }
      Unshelve. all: by apply _ || done. }
    destruct elements eqn:ELTS.
    { apply elements_empty_iff in ELTS. set_solver. }
    pose proof (in_eq f l) as IN%elem_of_list_In. rewrite -ELTS in IN.
    apply elem_of_elements, elem_of_filter in IN as [TS _].
    destruct f; eauto; by destruct TS. 
  Qed.

  Lemma next_TS_spec_inv_S δ1 τ δ2:
    locale_trans δ1 τ δ2 (LM := LM) ->
    next_TS_role δ1 τ δ2 = None ->
    lm_ls_trans LM δ1 (Silent_step τ) δ2.
  Proof.
    intros TRANS NO_TS.
    destruct TRANS as (ℓ&TRANS&MATCH). destruct ℓ as [| |]. 
    2: { by inversion MATCH. } 
    2: { naive_solver. }
    edestruct next_TS_spec_inv_TS as [? ?]; eauto.
    inversion MATCH. congruence.
  Qed.

  Definition step_by_next_TS (ρ: fmrole M) (δ1: lm_ls LM) (ostep: option (option G * lm_ls LM)) := 
    exists τ δ2, ostep = Some (Some τ, δ2) /\ next_TS_role δ1 τ δ2 = Some ρ. 
                         
  Definition fair_by_next_TS: fmrole M -> lmftrace -> Prop :=
    fair_by_gen role_enabled step_by_next_TS. 
  
  (* CoInductive auxtrace_valid: auxtrace -> Prop := *)
  (* | auxtrace_valid_singleton δ: auxtrace_valid ⟨δ⟩ *)
  (* | auxtrace_valid_cons δ ℓ tr: *)
  (*     LM.(lm_ls_trans) δ ℓ (trfirst tr) -> *)
  (*     auxtrace_valid tr → *)
  (*     auxtrace_valid (δ -[ℓ]-> tr). *)

  (* Lemma auxtrace_valid_forall (tr: auxtrace) : *)
  (*   auxtrace_valid tr -> *)
  (*   ∀ n, match after n tr with *)
  (*        | Some ⟨ _ ⟩ | None => True *)
  (*        | Some (δ -[ℓ]-> tr') => LM.(lm_ls_trans) δ ℓ (trfirst tr') *)
  (*        end. *)
  (* Proof. *)
  (*   intros Hval n. revert tr Hval. induction n as [|n]; intros tr Hval; *)
  (*     destruct (after _ tr) as [trn|] eqn: Heq =>//; simpl in Heq; *)
  (*     simplify_eq; destruct trn =>//; inversion Hval; simplify_eq; try done. *)
  (*   specialize (IHn _ H1) (* TODO *). rewrite Heq in IHn. done. *)
  (* Qed. *)

  (* Lemma auxtrace_valid_after (tr: auxtrace): *)
  (*   auxtrace_valid tr -> *)
  (*   forall n atr, after n tr = Some atr -> auxtrace_valid atr. *)
  (* Proof.  *)
  (*   intros VALID n. generalize dependent tr. induction n. *)
  (*   { intros. rewrite after_0_id in H0. congruence. }   *)
  (*   intros. inversion VALID; subst.  *)
  (*   { done. } *)
  (*   simpl in H0. eauto. *)
  (* Qed.  *)
    
End aux_trace.


Definition labels_match `{LM: LiveModel G M LSI} (oζ : option G) (ℓ : LM.(lm_lbl)) : Prop :=
  match oζ, ℓ with
  | None, Config_step => True
  | Some ζ, lbl => fair_lbl_matches_group lbl ζ
  | _, _ => False
  end.

Section aux_trace_lang.
  Context `{LM: LiveModel (locale Λ) M LSI}.
  Context `{Countable (locale Λ)}.

  Notation "'Tid'" := (locale Λ). 

  Definition tids_smaller (c : list (expr Λ)) (δ: LiveState Tid M LSI) :=
    ∀ ρ ζ, δ.(ls_mapping) !! ρ = Some ζ -> is_Some (from_locale c ζ).

End aux_trace_lang.

Ltac SS :=
  epose proof ls_fuel_dom;
  (* epose proof ls_mapping_dom; *)
  set_solver.

Definition live_tids `{LM:LiveModel (locale Λ) M LSI} `{EqDecision (locale Λ)}
           (c : cfg Λ) (δ : LM.(lm_ls)) : Prop :=
  (∀ ρ ζ, δ.(ls_mapping (G := locale Λ)) !! ρ = Some ζ -> is_Some (from_locale c.1 ζ)) ∧
  ∀ ζ e, from_locale c.1 ζ = Some e -> (to_val e ≠ None) ->
         ∀ ρ, δ.(ls_mapping) !! ρ ≠ Some ζ.

(* TODO: replace original definition with this *)
Lemma live_tids_alt `{LM:LiveModel (locale Λ) M LSI} `{EqDecision (locale Λ)} c δ:
  live_tids c δ (LM := LM) (Λ := Λ) <->
    (forall ζ, (exists ρ, ls_mapping δ !! ρ = Some ζ) ->
          locale_enabled ζ c).
Proof.
  rewrite /live_tids /locale_enabled. split.
  - intros. destruct H0 as [ρ MAP].
    destruct H as [EXPR NVAL].
    specialize (EXPR _ _ MAP) as [e ?].
    eexists. split; eauto.
    specialize (NVAL _ _ H). 
    destruct (to_val e); [| done].
    specialize (NVAL ltac:(eauto)).
    edestruct NVAL; eauto.
  - intros. split.
    + intros. specialize (H ζ (@ex_intro _ _ _ H0)) as [e [MAP ?]].
      eauto.
    + intros. intros MAP.
      specialize (H ζ (@ex_intro _ _ _ MAP)) as [? [? NVAL]].
      congruence.
Qed.


Section fuel_dec_unless.
  Context `{LM: LiveModel G Mdl LSI}.
  (* Context `{Countable G}. *)
  Context {LF: LMFairPre LM}. 
  
  (* Definition Ul (ℓ: LM.(mlabel)) := *)
  (*   match ℓ with *)
  (*   | Take_step ρ _ => Some (Some ρ) *)
  (*   | _ => None *)
  (*   end. *)

  Definition Usls (δ1: lm_ls LM) (* (ℓ: mlabel LM) *) (oτ: option G) (δ2: lm_ls LM):
    option $ option $ fmrole Mdl :=
    match oτ with 
    | Some τ => match (next_TS_role δ1 τ δ2) with 
               | Some ρ => Some $ Some ρ
               | None => None
               end
    | None => None
    end. 
    
  Definition Ψ (δ: LiveState G Mdl LSI) :=
    size δ.(ls_fuel) + [^ Nat.add map] ρ ↦ f ∈ δ.(ls_fuel (G := G)), f.

  Lemma fuel_dec_unless (auxtr: lmftrace (LM := LM)) :
    (* auxtrace_valid auxtr -> *)
    mtrace_valid auxtr -> 
    dec_unless ls_under Usls Ψ auxtr.
  Proof.
    intros Hval n. revert auxtr Hval. induction n; intros auxtr Hval; last first.
    { edestruct (after (S n) auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
      simpl in Heq;
      simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.
      destruct auxtr; [done| ].
      apply trace_valid_cons_inv in Hval as [Hval _]. 
      specialize (IHn _ Hval). rewrite Heq // in IHn. }
    edestruct (after 0 auxtr) as [auxtrn|] eqn:Heq; rewrite Heq =>//.
    simpl in Heq; simplify_eq. destruct auxtrn as [|δ ℓ auxtr']=>//; last first.

    (* inversion Hval as [|??? Htrans Hmatch]; simplify_eq =>//. *)
    apply trace_valid_cons_inv in Hval as [Hval Htrans].     
    (* destruct ℓ as [| tid' |]; *)
    (*   [left; eexists; done| right | inversion Htrans; naive_solver ]. *)
    simpl in Htrans. destruct ℓ as [τ| ]; [| done].
    simpl. destruct (next_TS_role δ τ (trfirst auxtr')) eqn:N; rewrite N; eauto. 
    apply next_TS_spec_inv_S in Htrans; auto.
    right. 
    
    destruct Htrans as (Hne&Hdec&Hni&Hincl&Heq). rewrite -> Heq in *. split; last done.

    destruct (decide (dom $ ls_fuel δ = dom $ ls_fuel (trfirst auxtr'))) as [Hdomeq|Hdomneq].
    - destruct Hne as [ρ Hρtid].

      assert (ρ ∈ dom $ ls_fuel δ) as Hin by rewrite -ls_same_doms elem_of_dom //.
      pose proof Hin as Hin'. pose proof Hin as Hin''.
      apply elem_of_dom in Hin as [f Hf].
      rewrite Hdomeq in Hin'. apply elem_of_dom in Hin' as [f' Hf'].
      rewrite /Ψ -!size_dom Hdomeq.
      apply Nat.add_lt_mono_l.

      rewrite /Ψ (big_opM_delete (λ _ f, f) (ls_fuel (trfirst _)) ρ) //.
      rewrite (big_opM_delete (λ _ f, f) (ls_fuel  δ) ρ) //.
      apply Nat.add_lt_le_mono.
      { rewrite /fuel_decr in Hdec. specialize (Hdec ρ). rewrite Hf Hf' /= in Hdec.
        apply Hdec; [set_solver | set_solver | by econstructor]. }

      apply big_addM_leq_forall => ρ' Hρ'.
      rewrite dom_delete_L in Hρ'.
      have Hρneqρ' : ρ ≠ ρ' by set_solver.
      rewrite !lookup_delete_ne //.
      destruct (decide (ρ' ∈ dom δ.(ls_fuel))) as [Hin|Hnotin]; last set_solver.
      rewrite /fuel_must_not_incr in Hni.
      (* destruct (Hni ρ' ltac:(done) ltac:(done)); [done|set_solver]. *)
      destruct (Hni ρ' ltac:(done)); [done|set_solver].
    - assert (size $ ls_fuel (trfirst auxtr') < size $ ls_fuel δ).
      { rewrite -!size_dom. apply subset_size. set_solver. }
      apply Nat.add_lt_le_mono =>//.
      apply big_addM_leq_forall => ρ' Hρ'.
      (* destruct (Hni ρ' ltac:(set_solver) ltac:(done)); [done|set_solver]. *)
      destruct (Hni ρ' ltac:(set_solver)); [done|set_solver].
  Qed.

End fuel_dec_unless.

Section destuttering_auxtr.
  Context `{LM: LiveModel G M LSI}.
  Context {LF: LMFairPre LM}. 
  (* Context `{Countable G}. *)

  (* Why is [LM] needed here? *)
  Definition upto_stutter_auxtr :=
    upto_stutter (ls_under (G:=G) (M:=M) (LSI := LSI)) (Usls (LM := LM)).

  Lemma can_destutter_auxtr (auxtr: lmftrace (LM := LM)):
    mtrace_valid auxtr →
    ∃ mtr, upto_stutter_auxtr auxtr mtr.
  Proof.
    intros ?. eapply can_destutter.
    eapply fuel_dec_unless =>//.
  Qed.

End destuttering_auxtr.

Section upto_preserves.
  Context `{LM: LiveModel G M LSI}.
  (* Context `{Countable G}. *)
  Context {LF: LMFairPre LM}. 

  Hint Resolve upto_stutter_mono : paco.

  Lemma upto_preserves_validity (auxtr : lmftrace (LM := LM)) mtr:
    upto_stutter_auxtr auxtr mtr ->
    mtrace_valid auxtr ->
    mtrace_valid mtr.
  Proof.
    revert auxtr mtr. pcofix CH. intros auxtr mtr Hupto Hval.
    punfold Hupto.
    induction Hupto as [| |btr str δ ????? IH].
    - pfold. constructor.
    - apply IHHupto.
      eapply trace_valid_cons_inv; eauto. 
    - pfold; constructor=>//.
      + subst.
        eapply @trace_valid_cons_inv in Hval as [Hval Htrans]. 
        (* inversion Hval as [| A B C Htrans E F ] =>//. *)
        subst. unfold ls_trans in *.
        destruct ℓ; try done. simpl in *. simplify_eq.
        pose proof Htrans as [??].
        have <- //: ls_under $ trfirst btr = trfirst str.
        { destruct IH as [IH|]; last done. punfold IH. inversion IH =>//. }
        Set Printing Coercions.
        destruct next_TS_role eqn:N; [| done].
        inversion H0. subst.
        apply next_TS_spec_pos in N. apply N. 
      + right. eapply CH.
        { destruct IH =>//. }
        subst. eapply trace_valid_cons_inv; eauto.  
  Qed.

End upto_preserves.

Section upto_stutter_preserves_fairness_and_termination.
  Context `{LM: LiveModel G M LSI}.
  (* Context `{Countable G}. *)
  Context {LF: LMFairPre LM}. 

  (* Notation upto_stutter_aux := (upto_stutter (ls_under (LSI := LSI)) (Usls (LM := LM))). *)

  (* Lemma upto_stutter_mono'' : (* TODO fix this proliferation *) *)
  (*   monotone2 (upto_stutter_ind (ls_under (LSI := LSI)) (Usls (LM:=LM))). *)
  (* Proof. *)
  (*   unfold monotone2. intros x0 x1 r r' IN LE. *)
  (*   induction IN; try (econstructor; eauto; done). *)
  (* Qed. *)
  (* Hint Resolve upto_stutter_mono' : paco. *)

  Lemma upto_stutter_step_correspondence (auxtr: lmftrace (LM := LM)) (mtr: mtrace M)
    (Po: lm_ls LM -> option (option G * lm_ls LM) -> Prop)
    (Pi: M -> option (option (fmrole M) * M) -> Prop)
    (LIFT: forall δ ostep, Po δ ostep -> Pi (ls_under δ) (match ostep with 
                                              | Some (ℓ, δ') => match (Usls δ ℓ δ') with | Some r => Some (r, ls_under δ') | None => None end
                                              | None => None
                                              end))
    (PI0: forall st, Pi st None -> forall ℓ, Pi st (Some ℓ))
    :
    upto_stutter_auxtr auxtr mtr (LM := LM) ->
    forall n atr_aux so stepo,
      after n auxtr = Some atr_aux ->
      (* pred_at atr_aux 0 Po -> *)
      atr_aux !! 0 = Some (so, stepo) ->
      Po so stepo ->
    exists m atr_m si stepi,
      after m mtr = Some atr_m /\ 
      (* pred_at atr_m 0 Pi /\  *)
      atr_m !! 0 = Some (si, stepi) /\
      Pi si stepi /\
      upto_stutter_auxtr atr_aux atr_m.
  Proof.
    intros Hupto n. generalize dependent auxtr. generalize dependent mtr. 
    induction n as [|n]; intros auxtr mtr Hupto atr_aux os ostep AFTER O0 A0.
    - rewrite after_0_id in AFTER. assert (atr_aux = mtr) as -> by congruence.
      (* do 4 eexists. *)
      exists 0, auxtr.
      pose proof (trace_lookup_0 auxtr) as [stepi STEPI].
      exists (trfirst auxtr), stepi.
      do 3 (split; eauto). 
      punfold Hupto. inversion Hupto; simplify_eq.
      4: { apply upto_stutter_mono. } 
      + rename A0 into Hpa.
        rewrite /pred_at /=. rewrite /pred_at //= in Hpa.
        destruct ostep; [done| ].
        specialize (LIFT _ _ Hpa). simpl in LIFT.
        rewrite trace_lookup_0_singleton in O0, STEPI. 
        rewrite trace_lookup_0_singleton in O0.
        inversion O0. congruence. 
      +
        (* rewrite -> !pred_at_0 in A0. *)
        rewrite /pred_at /=.
        destruct auxtr; try congruence.
        * apply LIFT in A0. 
          simpl.
          rewrite trace_lookup_0_singleton in STEPI. inversion STEPI.
          subst.           
          rewrite trace_lookup_0_cons in O0. inversion O0. subst.
          rewrite H in A0. congruence. 
        * apply LIFT in A0.
          simpl in H1. subst.
          rewrite trace_lookup_0_cons in O0.
          inversion O0. subst. simpl. 
          rewrite H in A0.
          destruct stepi; eauto. 
      + 
        (* rewrite -> !pred_at_0 in A0. *)
        simpl. 
        (* apply pred_at_0. rewrite <- H1. *)
        eapply LIFT in A0.
        rewrite trace_lookup_0_cons in O0. inversion O0. subst.
        rewrite H0 in A0.
        simpl in STEPI.
        pose proof (trace_lookup_0_cons (ls_under os) ℓ' str).
        simpl in H. rewrite STEPI in H. inversion H. subst.
        red in H1. try pclearbot.
        apply upto_stutter_trfirst in H1. by rewrite H1.
    - punfold Hupto. inversion Hupto as [| |?????? ?? IH ]; simplify_eq.
      3: { apply upto_stutter_mono. }
      + simpl in AFTER. 
        eapply IHn; eauto.
        by pfold.
      + simpl in AFTER.
        assert (upto_stutter_auxtr btr str) as UPTO'.
        { inversion IH; eauto. done. } 
        specialize (IHn str btr UPTO').
        specialize (IHn _ os ostep AFTER O0 A0). 
        destruct IHn as (m&?&?&?&?&?&?&?). 
        exists (S m). do 3 eexists. eauto. 
  Qed.

  (* TODO: move, rename *)
  Lemma trace_lookup_after_weak {St L: Type} (tr: trace St L) s n:
    (exists atr, after n tr = Some atr /\ trfirst atr = s) <-> exists ostep, tr !! n = Some (s, ostep). 
  Proof. 
    rewrite /lookup /trace_lookup.
    destruct after.
    2: { by split; [intros (?&?&?)| intros (?&?)]. }
    transitivity (trfirst t = s).
    { split; eauto. by intros (?&[=->]&?). }
    destruct t; simpl; eauto.
    all: split; [intros ->| intros (?&[=])]; eauto.
  Qed.

  Lemma upto_stutter_fairness_0 ρ (auxtr: lmftrace (LM := LM)) (mtr: mtrace M):
    upto_stutter_auxtr auxtr mtr ->
    (∃ n s ostep, auxtr !! n = Some (s, ostep ) /\ 
                  (¬role_enabled (LSI := LSI) ρ s ∨
                     (* pred_at auxtr n (λ _ ℓ, ∃ ζ, ℓ = Some (Take_step ρ ζ)) *)
                    step_by_next_TS ρ s ostep)
    ) ->
    ∃ m, pred_at mtr m (λ δ _, ¬role_enabled_model ρ δ)
         ∨ pred_at mtr m (λ _ ℓ, ℓ = Some $ Some ρ).
  Proof.
    repeat setoid_rewrite <- pred_at_or. 
    intros UPTO (n & so & stepo & NTH & PROP).
    (* pose proof NTH as [atr AFTER]%trace_lookup_after_weak. *)
    pose proof (proj2 (trace_lookup_after_weak auxtr so n)) as (atr & AFTER & A0); [by eauto| ].
    rewrite (plus_n_O n) in NTH. 
    (* rewrite pred_at_sum AFTER in NTH. *)
    erewrite <- @trace_lookup_after in NTH; eauto.  
    (* apply pred_at_trace_lookup' in NTH as (so & stepo & A0 & PROP). *)
    pattern so, stepo in PROP. 
    
    eapply upto_stutter_step_correspondence in PROP; eauto. 
    - destruct PROP as (m & atr_m & si & stepi & AFTERm & B0 & Pi & UPTO').
      exists m. rewrite pred_at_or. rewrite (plus_n_O m) pred_at_sum AFTERm.
      eapply pred_at_trace_lookup'.
      do 2 eexists. split; [eauto| ].
      pattern si. pattern stepi. apply Pi. 
    - intros ?? Po. simpl. destruct Po as [?| ?]; eauto.
      red in H. destruct H as (?&?&->&H).
      right. simpl. by rewrite H.
    - intros. destruct H; [| done]. eauto.
  Qed.  
    
  Lemma upto_stutter_fairness (auxtr: lmftrace (LM := LM)) (mtr: mtrace M):
    upto_stutter_auxtr auxtr mtr ->
    (∀ ρ, fair_by_next_TS ρ auxtr) ->
    (∀ ρ, fair_model_trace ρ mtr).
  Proof.
    intros Hupto Hfa ρ n Hpmod.
    unfold pred_at in Hpmod.
    destruct (after n mtr) as [mtr'|] eqn:Heq; last done.
    destruct (upto_stutter_after _ _ n Hupto Heq) as (n'&auxtr'&Heq'&Hupto').
    have Hre: role_enabled_model ρ (trfirst mtr') by destruct mtr'.
    specialize (Hfa ρ).
    have Henaux : role_enabled ρ (trfirst auxtr').
    { have HUs: ls_under (trfirst auxtr') = trfirst mtr'.
      - punfold Hupto'; [| apply upto_stutter_mono]. by inversion Hupto'.
      - unfold role_enabled, role_enabled_model in *.
        rewrite HUs //. }
    (* have Hfa' := (fair_by_after ρ auxtr n' auxtr' Hfa Heq' 0). *)
    have Hfa' := (fair_by_gen_after _ _ ρ auxtr auxtr' n' Heq' Hfa 0).
    (* have Hfa' := (fair_by_after _ _ ρ auxtr auxtr' n' Heq'). *)
    
    have Hpredat: pred_at auxtr' 0 (λ δ _, role_enabled ρ δ).
    { rewrite /pred_at /=. destruct auxtr'; done. }

    specialize (Hfa' Hpredat). clear Hpredat.
    destruct Hfa' as (m&Hres). simpl in Hres.
    (* rewrite /fairness_sat.  *)
    repeat setoid_rewrite pred_at_sum. rewrite !Heq. rewrite /role_match. 
    setoid_rewrite pred_at_iff.
    2: { intros. apply Morphisms_Prop.or_iff_morphism; [reflexivity| ].
         Unshelve. 2: exact (ol = Some (Some ρ)).
         split; [intros (?&->&->)| intros ->]; eauto. }
    setoid_rewrite <- pred_at_or.
    eapply upto_stutter_fairness_0; eauto.
  Qed.

  Lemma upto_stutter_finiteness auxtr (mtr: mtrace M):
    upto_stutter_auxtr auxtr mtr ->
    terminating_trace mtr ->
    terminating_trace auxtr.
  Proof.
    intros Hupto [n Hfin].
    have [n' ?] := upto_stutter_after_None _ _ n Hupto Hfin.
    eexists; done.
  Qed.

End upto_stutter_preserves_fairness_and_termination.


Definition valid_evolution_step `{LM:LiveModel (locale Λ) M LSI} 
  (* `{EqDecision (locale Λ)} *)
                                {LF: LMFairPre LM}
  oζ (σ2: cfg Λ) δ1 (oℓ: option (locale Λ)) δ2 :=
    (* labels_match (LM:=LM) oζ ℓ ∧  *)
    eq oζ oℓ /\
    (* LM.(lm_ls_trans) δ1 ℓ δ2 ∧ *)
    (fmtrans LM_Fair δ1 oℓ δ2) /\
    tids_smaller (σ2.1) δ2.

(* TODO: get rid of previous version *)
Definition lm_valid_evolution_step `{LM:LiveModel (locale Λ) M LSI} 
  (* `{EqDecision (locale Λ)} *)
  {LF: LMFairPre LM}
  :
    cfg Λ → olocale Λ → cfg Λ → 
    mstate LM → olocale Λ → mstate LM -> Prop := 
    (fun (_: cfg Λ) => valid_evolution_step).
