From iris.proofmode Require Import tactics.
From trillium.fairness Require Import trace_len trace_lookup.
From trillium.fairness Require Import inftraces fairness trace_utils utils_tactics.

Close Scope Z_scope.
 

Section FMTraceHelpers.
  Context {M: FairModel}.
  Let St := fmstate M.
  Let L := fmrole M.
  
  Definition set_fair_model_trace (T: L -> Prop) tr :=
    forall ρ (Tρ: T ρ), fair_model_trace ρ tr. 

  Definition strong_fair_model_trace (tr: mtrace M) (ρ: fmrole M) :=
    forall n (EN: pred_at tr n (λ δ _, role_enabled_model ρ δ)),
    exists m, ClassicalFacts.Minimal 
                (fun x => pred_at tr (n+x) (λ δ ℓ, ¬ role_enabled_model ρ δ \/ 
                                                     ℓ = Some (Some ρ))) m.


  Lemma fair_model_trace_defs_equiv (tr: mtrace M) (ρ: fmrole M):
    fair_model_trace ρ tr <-> strong_fair_model_trace tr ρ.
  Proof using. 

    split.
    2: { intros FAIR. do 2 red. intros.
         red in FAIR. specialize (FAIR n H) as [m [FAIR MIN]].
         exists m. eapply pred_at_iff; [| apply FAIR]. 
         intros. rewrite /role_match.
         apply Morphisms_Prop.or_iff_morphism; [done| ].
         split; [intros (?&->&->)|intros ->]; eauto. }

    intros FAIR. red. intros.
    red in FAIR.
    specialize (@FAIR n). destruct FAIR; auto.

    pattern x in H. eapply min_prop_dec in H as [d MIN].
    { clear x. exists d. 
      eapply Minimal_proper; eauto. 
      red. intros. symmetry. 
      apply pred_at_iff.
      intros. rewrite /role_match.
      apply Morphisms_Prop.or_iff_morphism; [done| ].
      split; [intros (?&->&->)|intros ->]; eauto. }

    intros.
    eapply pred_at_dec. intros.
    apply or_dec.
    2: { destruct ro; [destruct o| ]. 
         - destruct (decide (f = ρ)).
           + subst. left. eexists. split; eauto. done.
           + right. by intros (?&[=<-]&[=]).
         - right. by intros (?&[=<-]&[=]).
         - right. by intros (?&[=<-]&[=]). }
    apply not_dec.
    rewrite /role_enabled_model. solve_decision.
  Qed. 
  
  Definition strong_fair_model_trace_alt (tr: mtrace M) (ρ: fmrole M) :=
    forall n st (NTH: tr S!! n = Some st) (EN: role_enabled_model ρ st),
    exists m, ClassicalFacts.Minimal (
             fun x => (exists st', tr S!! (n + x) = Some st' /\ 
                             ¬ role_enabled_model ρ st') \/
                     (tr L!! (n + x) = Some (Some ρ))
           ) m. 

  Lemma strong_fair_model_trace_alt_defs_equiv (tr: mtrace M) (ρ: fmrole M):
    strong_fair_model_trace tr ρ <-> strong_fair_model_trace_alt tr ρ.
  Proof using. 
    rewrite /strong_fair_model_trace /strong_fair_model_trace_alt. 
    pose proof trace_has_len tr as [len LEN]. 
    split; intros. 
    - specialize (H n).
      specialize (H ltac:(by apply pred_at_trace_lookup; eauto)). 
      destruct H as [m [PROP MIN]]. exists m. split.
      { apply pred_at_or in PROP as [PROP | PROP];
          [left | right]; apply pred_at_trace_lookup in PROP as [? [??]]; eauto. }
      intros. apply MIN. apply pred_at_trace_lookup.
      destruct H as [(?&?&?) | STEP]; [by eauto|]. 
      forward eapply (proj1 (label_lookup_states tr (n + k))) as [[st' ST'] _]; eauto.
    - apply pred_at_trace_lookup in EN as [? [Tn EN]]. 
      specialize (H _ _ Tn EN). destruct H as [m [PROP MIN]].  
      exists m. split.
      + apply pred_at_trace_lookup. destruct PROP as [(?&?&?) | STEP]; eauto.
        forward eapply (proj1 (label_lookup_states tr (n + m))) as [[st' ST'] _]; eauto.
      + intros. apply MIN. apply pred_at_or in H. destruct H as [DIS | STEP].
        * left. apply pred_at_trace_lookup in DIS. eauto. 
        * right. apply pred_at_trace_lookup in STEP as [?[??]]. eauto. 
  Qed.        

  
  Section ValidTracesProperties.
    Context {tr: mtrace M} (VALID: mtrace_valid tr). 

    Local Ltac gd t := generalize dependent t.

    Definition label_kept_state_gen (Ps: St -> Prop) (Pstep: St -> option L -> St -> Prop) :=
      forall st oℓ' st' (P1: Ps st) (PSTEP: Pstep st oℓ' st') (STEP: fmtrans _ st oℓ' st'), 
        Ps st'.
    
    Lemma steps_keep_state_gen i (P: St -> Prop) Pstep j
      (Pi: exists st, tr S!! i = Some st /\ P st)    
      (* (P_KEPT: label_kept_state P Pl) *)
      (P_KEPT: label_kept_state_gen P Pstep)
      (NOρ: forall (k: nat) st1 oℓ' st2 (IKJ: i <= k < j), tr !! k = Some (st1, Some (oℓ', st2)) -> Pstep st1 oℓ' st2):
      forall k st' (IKJ: i <= k <= j) (KTH: tr S!! k = Some st'), P st'.
    Proof using VALID.
      intros k st' [IK KJ]. apply Nat.le_sum in IK as [d ->]. gd st'. induction d.
      { rewrite Nat.add_0_r. destruct Pi as (? & ? & ?). intros. congruence. }
      intros st'' KTH. rewrite Nat.add_succ_r -Nat.add_1_r in KTH. 
      pose proof (trace_has_len tr) as [len LEN]. 
      forward eapply (proj2 (trace_lookup_dom_strong  _ _ LEN (i + d))) as [st' CUR].
      { eapply state_lookup_dom; eauto. }
      
      destruct CUR as (oℓ' & st''_ & CUR).
      pose proof CUR as (PREV & CUR' & STEP)%state_label_lookup. 
      assert (st''_ = st'') as -> by congruence.
      red in P_KEPT. eapply P_KEPT.
      - apply IHd; [lia| eauto].
      - eapply NOρ; eauto. lia. 
      - eapply trace_valid_steps'; eauto. 
    Qed.
    

    (* TODO: unify with general case *)
    Definition label_kept_state (Ps: St -> Prop) (Pl: option L -> Prop) :=
      forall st oℓ' st' (Pst: Ps st) (Poℓ: Pl oℓ') (STEP: fmtrans _ st oℓ' st'), 
        Ps st'.
    
    Definition other_step ρ: option (fmrole M) -> Prop :=
      fun oρ' => oρ' ≠ Some ρ. 

    Lemma steps_keep_state i (P: St -> Prop) Pl j
      (Pi: exists st, tr S!! i = Some st /\ P st)    
      (P_KEPT: label_kept_state P Pl)
      (NOρ: forall (k: nat) oℓ' (IKJ: i <= k < j), tr L!! k = Some oℓ' -> Pl oℓ'):
      forall k st' (IKJ: i <= k <= j) (KTH: tr S!! k = Some st'), P st'.
    Proof using VALID.
      intros k st' [IK KJ]. apply Nat.le_sum in IK as [d ->]. gd st'. induction d.
      { rewrite Nat.add_0_r. destruct Pi as (? & ? & ?). intros. congruence. }
      intros st'' KTH. rewrite Nat.add_succ_r -Nat.add_1_r in KTH. 
      pose proof (trace_has_len tr) as [len LEN]. 
      forward eapply (proj2 (trace_lookup_dom_strong  _ _ LEN (i + d))) as [st' CUR].
      { eapply state_lookup_dom; eauto. }
      destruct CUR as (oℓ' & st''_ & (PREV & CUR & STEP)%state_label_lookup).
      assert (st''_ = st'') as -> by congruence.
      red in P_KEPT. eapply P_KEPT.
      - apply IHd; [lia| eauto].
      - eapply NOρ; eauto. lia.
      - eapply trace_valid_steps'; eauto. 
        apply state_label_lookup. eauto. 
    Qed.
    
    Lemma steps_keep_state_inf i (P: St -> Prop) Pl
      (Pi: exists st, tr S!! i = Some st /\ P st)    
      (P_KEPT: label_kept_state P Pl)
      (NOρ: forall (k: nat) oℓ', i <= k -> tr L!! k = Some oℓ' -> Pl oℓ'):
      forall k st' (IK: i <= k) (KTH: tr S!! k = Some st'), P st'.
    Proof using VALID.
      intros. eapply steps_keep_state; eauto.
      intros p **. eapply (NOρ p); eauto. lia.  
    Qed.

    (* (* TODO: rename *) *)
    (* Lemma kept_state_fair_step' (ρ: L) (P: St -> Prop) *)
    (*   (KEPT: label_kept_state P (other_step ρ)) *)
    (*   (* (P_EN: forall st (Pst: P st), @role_enabled_model M ρ st) *) *)
    (*   (FAIRρ: fair_model_trace ρ tr): *)
    (*   forall i st (ITH: tr S!! i = Some st) (Pst: P st), *)
    (*   exists j st', ClassicalFacts.Minimal (fun j => i <= j /\ tr L!! j = Some $ Some ρ \/ ¬ role_enabled_model ρ st') j /\ *)
    (*              tr S!! j = Some st' /\ P st'. *)
    (* Proof using VALID. *)
    (*   intros.  *)
    (*   apply fair_model_trace_defs_equiv, strong_fair_model_trace_alt_defs_equiv in FAIRρ.          *)
    (*   red in FAIRρ. edestruct FAIRρ as [d [STEP MIN]]; [eauto| ..]. *)
    (*   { apply P_EN. eauto. } *)
    (*   clear FAIRρ.  *)

    (*   pose proof (trace_has_len tr) as [len LEN]. *)
    (*   assert (my_omega.NOmega.lt_nat_l (i + d) len) as DOMid. *)
    (*   { destruct STEP as [(?&?&?) | STEP].  *)
    (*     - eapply state_lookup_dom; eauto. *)
    (*     - apply my_omega.NOmega.lt_lt_nat with (m := i + d + 1); [lia| ]. *)
    (*       eapply label_lookup_dom; eauto. } *)
    (*   pose proof (proj2 (state_lookup_dom _ _ LEN (i + d)) DOMid) as [st' IDTH]. *)
      
    (*   forward eapply steps_keep_state with (i := i) (j := i + d) (k := i + d) as NEXT_EN; eauto.  *)
    (*   { intros. destruct IKJ as [[v ->]%Nat.le_sum KJ].  *)
    (*     intros ->. enough (d <= v); [lia| ]. apply MIN. eauto. } *)
    (*   { lia. } *)
      
    (*   destruct STEP as [(st'_ & ST' & DIS') | STEP]. *)
    (*   { assert (st'_ = st') as -> by congruence.  *)
    (*     destruct DIS'. apply P_EN. eauto. } *)
    (*   exists (i + d), st'. split; eauto. *)
    (*   red. split; [split; [lia| eauto]| ]. *)
    (*   intros k [LE' STEP']. apply Nat.le_sum in LE' as [d' ->]. *)
    (*   enough (d <= d'); [lia| ]. apply MIN. eauto. *)
    (* Qed. *)

    (* TODO: rename *)
    Lemma kept_state_fair_step (ρ: L) (P: St -> Prop)
      (KEPT: label_kept_state P (other_step ρ))
      (P_EN: forall st (Pst: P st), @role_enabled_model M ρ st)
      (FAIRρ: fair_model_trace ρ tr):
      forall i st (ITH: tr S!! i = Some st) (Pst: P st),
      exists j st', ClassicalFacts.Minimal (fun j => i <= j /\ tr L!! j = Some $ Some ρ) j /\
                 tr S!! j = Some st' /\ P st'.
    Proof using VALID.
      intros. 
      apply fair_model_trace_defs_equiv, strong_fair_model_trace_alt_defs_equiv in FAIRρ.         
      red in FAIRρ. edestruct FAIRρ as [d [STEP MIN]]; [eauto| ..].
      { apply P_EN. eauto. }
      clear FAIRρ. 

      pose proof (trace_has_len tr) as [len LEN].
      assert (my_omega.NOmega.lt_nat_l (i + d) len) as DOMid.
      { destruct STEP as [(?&?&?) | STEP]. 
        - eapply state_lookup_dom; eauto.
        - apply my_omega.NOmega.lt_lt_nat with (m := i + d + 1); [lia| ].
          eapply label_lookup_dom; eauto. }
      pose proof (proj2 (state_lookup_dom _ _ LEN (i + d)) DOMid) as [st' IDTH].
      
      forward eapply steps_keep_state with (i := i) (j := i + d) (k := i + d) as NEXT_EN; eauto. 
      { intros. destruct IKJ as [[v ->]%Nat.le_sum KJ]. 
        intros ->. enough (d <= v); [lia| ]. apply MIN. eauto. }
      { lia. }
      
      destruct STEP as [(st'_ & ST' & DIS') | STEP].
      { assert (st'_ = st') as -> by congruence. 
        destruct DIS'. apply P_EN. eauto. }
      exists (i + d), st'. split; eauto.
      red. split; [split; [lia| eauto]| ].
      intros k [LE' STEP']. apply Nat.le_sum in LE' as [d' ->].
      enough (d <= d'); [lia| ]. apply MIN. eauto.
    Qed.

  End ValidTracesProperties.

End FMTraceHelpers.
