From iris.proofmode Require Import tactics.
From trillium.fairness Require Import lemmas trace_len trace_lookup.
From trillium.fairness Require Import inftraces fairness trace_utils.

Close Scope Z_scope.
 
Section TraceHelpers.
  Context {St L: Type}.

  Lemma pred_at_dec (P: St → option L → Prop)
    (DEC: forall st ro, Decision (P st ro)):
    forall tr i, Decision (pred_at tr i P).
  Proof using.
    intros tr i. unfold pred_at.
    destruct (after i tr); [destruct t| ]; auto.
    solve_decision.
  Qed.

  Lemma pred_at_or
    P1 P2 (tr: trace St L) i: 
    pred_at tr i P1 \/ pred_at tr i P2 <-> pred_at tr i (fun x y => P1 x y \/ P2 x y).
  Proof using.
    unfold pred_at. destruct (after i tr); [destruct t| ]; tauto.
  Qed.

  Lemma pred_at_ex {T: Type} (P : T -> St → option L → Prop) tr n:
    pred_at tr n (fun s ol => exists t, P t s ol) <-> exists t, pred_at tr n (P t).
  Proof.
    rewrite /pred_at. destruct after.
    2: { intuition. by destruct H. }
    destruct t; eauto.
  Qed.

  Lemma pred_at_impl (P Q: St -> option L -> Prop)
    (IMPL: forall s ol, P s ol -> Q s ol):
    forall tr i, pred_at tr i P -> pred_at tr i Q.
  Proof.
    rewrite /pred_at. intros. 
    destruct after; intuition; destruct t.
    all: by apply IMPL.
  Qed.

End TraceHelpers. 

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

    From Paco Require Import pacotac.
    Local Ltac gd t := generalize dependent t.

    Lemma mtrace_valid_steps' i st ℓ st'
      (ITH: tr !! i = Some (st, Some (ℓ, st'))):
      fmtrans _ st ℓ st'. 
    Proof using VALID.
      gd st. gd ℓ. gd st'. gd tr. clear dependent tr. 
      induction i. 
      { simpl. intros. punfold VALID. inversion VALID.
        - subst. done.
        - subst. inversion ITH. by subst. }
      intros. simpl in ITH.
      destruct tr.
      { inversion ITH. }
      punfold VALID. inversion_clear VALID; pclearbot; auto.
      eapply IHi; eauto. 
    Qed.

    Lemma mtrace_valid_steps'' i st ℓ st'
      (ST1: tr S!! i = Some st)
      (ST2: tr S!! (i + 1) = Some st')
      (LBL: tr L!! i = Some ℓ):
      fmtrans _ st ℓ st'. 
    Proof using VALID.
      eapply mtrace_valid_steps'.
      apply state_label_lookup. eauto.
    Qed. 
    
    Definition label_kept_state (P: St -> Prop) (ℓ: L) :=
      forall st oℓ' st' (Ps: P st) (OTHER: oℓ' ≠ Some ℓ) (STEP: fmtrans _ st oℓ' st'), 
        P st'.
    
    Lemma steps_keep_state i (P: St -> Prop) ℓ j
      (Pi: exists st, tr S!! i = Some st /\ P st)    
      (P_KEPT: label_kept_state P ℓ)
      (NOρ: forall (k: nat) oℓ' (IKJ: i <= k < j), tr L!! k = Some oℓ' -> oℓ' ≠ Some ℓ):
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
      - eapply mtrace_valid_steps'; eauto. 
        apply state_label_lookup. eauto. 
    Qed.
    
    (* TODO: rename *)
    Lemma kept_state_fair_step (ρ: L) (P: St -> Prop)
      (KEPT: label_kept_state P ρ)
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

  (* use trace_valid_cons_inv instead *)
  (* Lemma mtrace_valid_cons (tr: mtrace M) (s: fmstate M) (oρ: option (fmrole M)) *)
  (*   (VALID: mtrace_valid (s -[oρ]-> tr)): *)
  (*   mtrace_valid tr /\ fmtrans M s oρ (trfirst tr).  *)
  (* Proof using. *)
  (*   punfold VALID. inversion VALID. subst. *)
  (*   pclearbot. done.  *)
  (* Qed. *)

End FMTraceHelpers.


