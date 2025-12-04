From iris.proofmode Require Import tactics.
(* From trillium.fairness Require Import lemmas trace_len trace_lookup. *)
From trillium.traces Require Import inftraces trace_utils trace_lookup trace_len.


Close Scope Z.
 

Section ValidTracesProperties.
  Context {St L: Type}.
  Context (R: St -> L -> St -> Prop). 
  Context {tr: trace St L} (VALID: trace_valid R tr). 

  Local Ltac gd t := generalize dependent t.

  Definition label_kept_state_gen (Ps: St -> Prop) (Pstep: St -> L -> St -> Prop) :=
    forall st oℓ' st' (P1: Ps st) (PSTEP: Pstep st oℓ' st') (STEP: R st oℓ' st'), 
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
    opose proof * (proj2 (trace_lookup_dom_strong  _ _ LEN (i + d))) as [st' CUR].
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
  Definition label_kept_state (Ps: St -> Prop) (Pl: L -> Prop) :=
    forall st oℓ' st' (Pst: Ps st) (Poℓ: Pl oℓ') (STEP: R st oℓ' st'), 
      Ps st'.
  
  Definition other_step ρ: L -> Prop :=
    fun oρ' => oρ' ≠ ρ. 

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
    opose proof * (proj2 (trace_lookup_dom_strong  _ _ LEN (i + d))) as [st' CUR].
    { eapply state_lookup_dom; eauto. }
    destruct CUR as (oℓ' & st''_ & (PREV & CUR & STEP)%state_label_lookup).
    assert (st''_ = st'') as -> by congruence.
    red in P_KEPT. eapply P_KEPT.
    - apply IHd; [lia| eauto].
    - eapply NOρ; eauto. lia.
    - eapply trace_valid_steps'; eauto. 
      apply state_label_lookup. eauto. 
  Qed.

  Require Import Coq.Logic.Classical.

  Lemma steps_not_kept_step_between i (P: St -> Prop) Pl j ci cj
  (ITH: tr S!! i = Some ci)
  (JTH: tr S!! j = Some cj)
  (P_KEPT: label_kept_state P Pl)
  (LE: i <= j)
  (ENi: P ci)
  (DISj: ¬ P cj):
  exists k τ, i <= k < j /\ tr L!! k = Some τ /\ ¬ Pl τ.
  Proof using VALID.
    odestruct (classic _) as [YES | NO]; [by apply YES| ].
    destruct DISj.
    eapply steps_keep_state; eauto.
    intros. 
    odestruct (classic _) as [YES | NO']; [by apply YES| ].
    destruct NO; eauto.
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

    (* (* TODO: rename *) *)
    (* Lemma kept_state_fair_step (ρ: L) (P: St -> Prop) *)
    (*   (KEPT: label_kept_state P (other_step ρ)) *)
    (*   (P_EN: forall st (Pst: P st), @role_enabled_model M ρ st) *)
    (*   (FAIRρ: fair_model_trace ρ tr): *)
    (*   forall i st (ITH: tr S!! i = Some st) (Pst: P st), *)
    (*   exists j st', ClassicalFacts.Minimal (fun j => i <= j /\ tr L!! j = Some $ Some ρ) j /\ *)
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

End ValidTracesProperties.
