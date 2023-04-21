From iris.proofmode Require Import tactics.
From hahn Require Import HahnBase.
From trillium.fairness.examples.ticketlock Require Import lemmas trace_len set_map_properties.


(* TODO: inherited from hahn? *)
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

End TraceHelpers. 

Section FMTraceHelpers.
  Context {M: FairModel}.
  Let St := fmstate M.
  Let L := fmrole M.
  
  Definition set_fair_model_trace (T: L -> Prop) tr :=
    forall ρ (Tρ: T ρ), fair_model_trace ρ tr. 

  (* TODO: already exists somewhere? *)
  Lemma Decision_iff_impl (P Q: Prop) (PQ: P <-> Q) (DEC_P: Decision P):
    Decision Q. 
  Proof using. 
    destruct DEC_P; [left | right]; tauto. 
  Qed.

  Lemma pred_at_or P1 P2 (tr: mtrace M) i: 
    pred_at tr i P1 \/ pred_at tr i P2 <-> pred_at tr i (fun x y => P1 x y \/ P2 x y).
  Proof using.
    unfold pred_at. destruct (after i tr); [destruct t| ]; tauto.
  Qed.
  

  Definition strong_fair_model_trace (tr: mtrace M) (ρ: fmrole M) :=
    forall n (EN: pred_at tr n (λ δ _, role_enabled_model ρ δ)),
    exists m, ClassicalFacts.Minimal 
                (fun x => pred_at tr (n+x) (λ δ ℓ, ¬ role_enabled_model ρ δ \/ 
                                                     ℓ = Some (Some ρ))) m.


  Lemma fair_model_trace_defs_equiv (tr: mtrace M) (ρ: fmrole M):
    fair_model_trace ρ tr <-> strong_fair_model_trace tr ρ.
  Proof using. 
    split.
    2: { intros FAIR. red. intros.
         red in FAIR. specialize (FAIR n H) as [m [FAIR MIN]].
         exists m. by apply pred_at_or. }

    intros FAIR. red. intros.
    red in FAIR.
    specialize (@FAIR n). destruct FAIR; auto.

    pattern x in H. eapply min_prop_dec in H as [d MIN].
    { clear x. exists d. 
      eapply Minimal_proper; eauto. 
      red. intros. symmetry. apply pred_at_or. }

    intros. eapply Decision_iff_impl. 
    { symmetry. apply pred_at_or. }
    eapply pred_at_dec. intros.
    apply or_dec.
    2: { solve_decision. }
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
    - specialize (H n). specialize_full H. 
      { apply pred_at_trace_lookup. eauto. }
      destruct H as [m [PROP MIN]]. exists m. split.
      { apply pred_at_or in PROP as [PROP | PROP];
          [left | right]; apply pred_at_trace_lookup in PROP; desc; eauto. }
      intros. apply MIN. apply pred_at_trace_lookup.
      destruct H as [DIS | STEP].
      { desc. exists st'. eauto. }
      forward eapply (proj1 (label_lookup_states tr (n + k))) as [[st' ST'] _]; eauto.
    - apply pred_at_trace_lookup in EN. desc. 
      specialize (H _ _ EN EN0). desc. destruct H as [PROP MIN].  
      exists m. split.
      + apply pred_at_trace_lookup. destruct PROP as [DIS | STEP]; desc; eauto.
        forward eapply (proj1 (label_lookup_states tr (n + m))) as [[st' ST'] _]; eauto.
      + intros. apply MIN. apply pred_at_or in H. destruct H as [DIS | STEP].
        * left. apply pred_at_trace_lookup in DIS. eauto. 
        * right. apply pred_at_trace_lookup in STEP. desc. eauto. 
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
      { destruct STEP; desc.
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
