From trillium.fairness Require Import inftraces fairness.
From trillium.fairness.examples.comp Require Import lm_fair my_omega lemmas trace_len trace_helpers trace_lookup.

Local Ltac gd t := generalize dependent t.

(* TODO: move*)
Section Subtrace.
  Context {St L: Type}.
  

  CoFixpoint trace_prefix_inf (tr: trace St L) (max_len: nat_omega): trace St L :=
    match tr, max_len with
    | tr, NOnum 0 => ⟨ trfirst tr ⟩ (* shouldn't be reached if max_len > 0*)
    | tr, NOnum 1 => ⟨ trfirst tr ⟩ (* actual base case *)
    | ⟨ s ⟩, _ => ⟨ s ⟩
    | s -[ l ]-> tr', ml => s -[l]-> (trace_prefix_inf tr' (NOmega.pred ml))
    end. 

  Definition subtrace (tr: trace St L) (start: nat) (fin: nat_omega): option (trace St L) :=
    match (after start tr) with
    | None => None
    | Some tr => let max_len := NOmega.sub fin (NOnum start) in
                if (decide (max_len = NOnum 0))
                then None
                else Some (trace_prefix_inf tr max_len)
    end.

  Lemma trace_prefix_len1 (tr: trace St L):
    trace_prefix_inf tr (NOnum 1) = ⟨ trfirst tr ⟩.
  Proof. 
    rewrite (trace_unfold_fold (trace_prefix_inf tr (NOnum 1))).
    destruct tr; done. 
  Qed. 

  Lemma trace_prefix_inf_len (tr: trace St L) (len max_len: nat_omega)
    (GT0: max_len ≠ NOnum 0)
    (LEN: trace_len_is tr len)
    (LE: NOmega.le max_len len)
    :
    trace_len_is (trace_prefix_inf tr max_len) max_len.
  Proof. 
    destruct max_len.
    { lia_NO' len.
      red. simpl. clear -LEN.
      intros i. gd tr. induction i.
      { simpl. done. }
      intros.
      rewrite (trace_unfold_fold (trace_prefix_inf tr NOinfinity)).
      destruct tr.
      { done. }
      specialize (IHi tr). specialize_full IHi.
      { apply trace_len_tail in LEN. eauto. }
      done. }      
    gd tr. gd len. induction n.
    { intros. done. }
    intros. 
    destruct n. 
    { rewrite trace_prefix_len1. apply trace_len_singleton. }
    rewrite (trace_unfold_fold (trace_prefix_inf tr (NOnum (S (S n))))). 
    destruct tr. 
    { pose proof (trace_len_singleton s (L := L)) as LEN'.
      pose proof (trace_len_uniq _ _ _ LEN LEN').
      subst. simpl in *. lia. }
    specialize (IHn ltac:(done) (NOmega.pred len)).
    specialize (IHn ltac:(lia_NO len)). specialize_full IHn.
    { eapply trace_len_tail; eauto. }
    apply (trace_len_cons s ℓ) in IHn. done.
  Qed. 

  (* Lemma trace_prefix_inf_over tr len max_len *)
  (*   (LEN: trace_len_is tr len) *)
  (*   (GE: NOmega.le len max_len): *)
  (*   trace_prefix_inf tr max_len = trace_prefix_inf tr len. *)
  (* Proof.  *)

  (* Lemma subtrace_over tr start fin len *)
  (*   (LEN: trace_len_is tr len) *)
  (*   (GE: NOmega.le len fin): *)
  (*   subtrace tr start fin = subtrace tr start len. *)
  (* Proof.  *)


  Lemma subtrace_len (tr: trace St L) (len: nat_omega)
    (start: nat) (fin: nat_omega)
    (LEN: trace_len_is tr len)
    (LE: NOmega.lt_nat_l start fin)
    (BOUND: NOmega.le fin len)
    :
    exists str, subtrace tr start fin = Some str /\
           trace_len_is str (NOmega.sub fin (NOnum start)).
  Proof. 
    rewrite /subtrace.
    forward eapply (proj2 (LEN start)) as [atr SUF]. 
    { lia_NO' len; lia_NO' fin. }
    rewrite SUF.
    destruct decide. 
    { lia_NO' fin. inversion e. lia. }
    eexists. split; eauto.
    eapply trace_prefix_inf_len; eauto.
    - eapply trace_len_after; eauto.
    - lia_NO' fin; lia_NO len.
  Qed.    
    
  Lemma trace_prefix_inf_head (tr: trace St L) d:
    trfirst (trace_prefix_inf tr d) = trfirst tr.
  Proof.
    (* rewrite (trace_unfold_fold (trace_prefix_inf tr d)).  *)
    rewrite (trace_unfold_fold tr).
    destruct tr, d; simpl; try done.
    all: by destruct n; [| destruct n]. 
  Qed. 

  Definition trace_prefix_inf_step_alt tr d :=
    if (decide (NOmega.le d (NOnum 1)))
    then ⟨ trfirst tr ⟩
    else match tr with 
         | ⟨ s ⟩ => ⟨ s ⟩
         | s -[ℓ]-> tr' => s -[ℓ]-> trace_prefix_inf tr' (NOmega.pred d)
         end.

  Definition trace_prefix_inf_step_equiv tr d:
    trace_prefix_inf tr d = trace_prefix_inf_step_alt tr d.
  Proof. 
    rewrite (trace_unfold_fold (trace_prefix_inf tr d)).
    rewrite /trace_prefix_inf_step_alt. 
    destruct tr; simpl.
    - destruct d.
      + simpl. rewrite decide_False; tauto.
      + destruct n; [| destruct n].
        1, 2: rewrite decide_True; [done| ]. 
        3: rewrite decide_False; [done| ].
        all: simpl; lia.
    - destruct d.
      + rewrite decide_False; [done| ]. tauto.
      + destruct n; [| destruct n].
        1, 2: rewrite decide_True; [done| ]. 
        3: rewrite decide_False; [done| ].
        all: simpl; lia.
  Qed.

  Lemma trace_prefix_inf_lookup_bounded
    (tr : trace St L)
    (  lim k : nat)
    (  H : k < lim)
    (  len : nat_omega)
    (  LEN : trace_len_is tr len)
    (  BOUND : NOmega.lt_nat_l lim len):
    trace_prefix_inf tr (NOnum lim) S!! k = tr S!! k /\
      (k < lim - 1 -> trace_prefix_inf tr (NOnum lim) !! k = tr !! k). 
  Proof.
    gd lim. gd tr. gd len. induction k.  
    { intros.
      rewrite trace_prefix_inf_step_equiv. 
      rewrite /trace_prefix_inf_step_alt. simpl.  
      destruct decide.
      - assert (lim = 1) as -> by lia.
        destruct tr; try done. simpl.
        split; [| lia].
        done.
      - split; [by destruct tr| ].
        intros. destruct tr; [done| ].
        rewrite trace_lookup_0_cons.
        by rewrite trace_prefix_inf_head. } 
    intros.
    rewrite trace_prefix_inf_step_equiv.
    rewrite /trace_prefix_inf_step_alt.
    destruct decide.
    - simpl in l. assert (lim = 1) as -> by lia.
      lia.
    - simpl in *. destruct tr.
      + pose proof (trace_len_singleton s (L := L)) as LEN'. 
        forward eapply (trace_len_uniq _ _ _ LEN LEN') as ->.
        simpl in *. lia.
      + rewrite !trace_lookup_cons !state_lookup_cons.
        destruct lim; [lia| ].
        rewrite PeanoNat.Nat.sub_succ_l; [| lia].
        setoid_rewrite <- Nat.succ_lt_mono. 
        eapply IHk; eauto.
        { apply trace_len_tail in LEN. eauto. }
        { lia. }
        lia_NO' len. 
  Qed. 

  Lemma trace_prefix_inf_lookup_unbounded
(  tr : trace St L)
(  d : nat_omega)
(  k : nat)
(  H : NOmega.lt_nat_l k d)
(  len : nat_omega)
(  LEN : trace_len_is tr len)
(  LE : NOmega.le len d):
  trace_prefix_inf tr d !! k = tr !! k.
  Proof. 
    gd d. gd tr. gd len. induction k.  
    { intros.
      rewrite trace_prefix_inf_step_equiv.
      rewrite /trace_prefix_inf_step_alt. 
      destruct decide.
      - lia_NO' d. assert (n = 1) as -> by lia.
        lia_NO' len. assert (n = 0 \/ n = 1) as [-> | ->] by lia.
        + by apply trace_len_0_inv in LEN.
        + apply trace_len_1_inv in LEN as [? ->]. done.
      - destruct tr; try done.
        rewrite !trace_lookup_0_cons.
        by rewrite trace_prefix_inf_head. }
    intros.
    rewrite trace_prefix_inf_step_equiv.
    rewrite /trace_prefix_inf_step_alt.
    destruct decide.
    - lia_NO' d.
    - destruct tr.
      { lia_NO' d. }
      rewrite !trace_lookup_cons. eapply IHk; eauto.
      { apply trace_len_tail in LEN. apply LEN. }
      { lia_NO d. }
      lia_NO' len; lia_NO' d.
  Qed. 
  
  Lemma trace_prefix_inf_lookup tr d:
    forall k, NOmega.lt_nat_l k d ->
         trace_prefix_inf tr d S!! k = tr S!! k /\
         (NOmega.lt_nat_l (k + 1) d -> trace_prefix_inf tr d !! k = tr !! k). 
  Proof.
    intros.
    pose proof (trace_has_len tr) as [len LEN].
    destruct (decide (NOmega.le len d)) as [LE | LT].
    { forward eapply trace_prefix_inf_lookup_unbounded as KTH; eauto.
      split; eauto.
      rewrite /state_lookup.
      rewrite /lookup /trace_lookup in KTH.
      by rewrite KTH. }      
    
    assert (exists lim, d = NOnum lim /\ NOmega.lt_nat_l lim len)
             as (lim & -> & BOUND). 
    { lia_NO' len; lia_NO' d; eauto.
      exists n0. split; eauto. lia. }
    simpl in *.
    setoid_rewrite Nat.lt_add_lt_sub_r. 
    eapply trace_prefix_inf_lookup_bounded; eauto.
  Qed. 
    
  (* Lemma subtrace_lookup_after (tr: trace St L) str atr *)
  (*   (start: nat) (fin: nat_omega) *)
  (*   (SUB: subtrace tr start fin = Some str) *)
  (*   (AFTER: after start tr = Some atr): *)
  (*   forall k, str !! k = atr !! k.  *)
  (* Proof.  *)

  Lemma subtrace_lookup (tr: trace St L) str
    (start: nat) (fin: nat_omega)
    (SUB: subtrace tr start fin = Some str):
    forall k, NOmega.lt_nat_l k (NOmega.sub fin (NOnum start)) ->
         str S!! k = tr S!! (start + k) /\
         (NOmega.lt_nat_l (k + 1) (NOmega.sub fin (NOnum start)) -> 
          str !! k = tr !! (start + k)). 
  Proof. 
    intros.
    rewrite /subtrace in SUB.
    destruct (after start tr) eqn:AFTER; [| done].
    destruct decide; [done| ].
    inversion SUB. subst. clear SUB. 
    erewrite <- trace_lookup_after; [| apply AFTER].
    erewrite <- state_lookup_after; [| apply AFTER].
    eapply trace_prefix_inf_lookup.
    lia_NO fin. 
  Qed.

  (* TODO: move *)
  Require Import Coq.Logic.Classical.

  Lemma trace_prop_split (tr: trace St L) (P: (St * option (L * St)) -> Prop) len 
    (DECP: forall res, Decision (P res))
    (LEN: trace_len_is tr len)
    : 
    exists (l: nat_omega), 
    (forall i res (LT: NOmega.lt (NOnum i) l) (RES: tr !! i = Some res), P res) /\
    (forall j res (NEXT: l = NOnum j) (RES: tr !! j = Some res), ¬ P res) /\
    NOmega.le l len. 
  Proof using.
    destruct (classic (exists j res, tr !! j = Some res /\ ¬ P res)) as [STOP | EV]. 
    - destruct STOP as [j' STOP'].
      pattern j' in STOP'. apply min_prop_dec in STOP' as [j [NPROP MIN]]. 
      2: { intros. admit. }
      exists (NOnum j). simpl in *. repeat split.      
      + intros. destruct (decide (P res)); [done| ]. 
        enough (j <= i); [lia| ].
        apply MIN. eexists. split; eauto.
      + intros. inversion NEXT. subst.
        destruct NPROP as [? [RES' NP]].
        congruence.
      + lia_NO' len.
        destruct NPROP as [? [RES' NP]].
        pose proof (proj1 (trace_lookup_dom _ _ LEN j) (ex_intro _ x RES')).
        simpl in H. lia. 
    - exists len. repeat split.
      + intros.
        apply not_exists_forall_not with (x := i) in EV. 
        apply not_exists_forall_not with (x := res) in EV.
        apply not_and_or in EV. destruct EV; [done| ].
        eapply NNP_P; eauto.
      + intros.
        apply not_exists_forall_not with (x := j) in EV.        
        pose proof (proj1 (trace_lookup_dom _ _ LEN j)).
        specialize (H ltac:(eauto)).
        lia_NO' len. inversion NEXT. lia.
      + lia_NO len. 
  Admitted. 

  Lemma trace_prop_split' (tr: trace St L) (P: (St * option (L * St)) -> Prop) 
    len
    (start: nat)
    (DECP: forall res, Decision (P res))
    (LEN: trace_len_is tr len)
    (BOUND: NOmega.le (NOnum start) len)
    : 
    exists (l: nat_omega),      
    (forall i res (GE: start <= i) (LT: NOmega.lt (NOnum i) l) (RES: tr !! i = Some res), P res) /\
    (forall j res (NEXT: l = NOnum j) (RES: tr !! j = Some res), ¬ P res) /\
    NOmega.le (NOnum start) l /\
    NOmega.le l len.
  Proof using.
    destruct (after start tr) eqn:AFTER.
    2: { eapply trace_len_neg in AFTER; eauto.
         assert (len = NOnum start) as ->.
         { lia_NO' len. f_equal. lia. }
         exists (NOnum start). repeat split.
         3, 4: done. 
         - intros. eapply mk_is_Some in RES.
           apply (trace_lookup_dom _ _ LEN) in RES.
           simpl in *. lia.
         - intros. inversion NEXT. subst j.
           eapply mk_is_Some in RES.
           apply (trace_lookup_dom _ _ LEN) in RES.
           simpl in *. lia. }
    forward eapply (trace_prop_split t).
    { eauto. }
    { eapply trace_len_after in AFTER; eauto. }
    intros (l&L1&L2&LE).
    exists (NOmega.add l (NOnum start)). repeat split.
    - intros. apply Nat.le_sum in GE as [d ->].
      apply (L1 d); eauto.
      + lia_NO l.
      + erewrite trace_lookup_after; eauto.
    - intros.
      lia_NO' l. inversion NEXT. subst j. clear NEXT.
      eapply L2; eauto.
      rewrite Nat.add_comm in RES. 
      erewrite trace_lookup_after; eauto.
    - lia_NO l. 
    - lia_NO' l; lia_NO' len.
  Qed.     


  Lemma subtrace_inv tr len str start max_len
    (SUB: subtrace tr start max_len = Some str)
    (LEN: trace_len_is tr len):
    NOmega.lt_nat_l start max_len /\ NOmega.lt_nat_l start len.
  Proof. 
    rewrite /subtrace in SUB.
    destruct (after start tr) eqn:AFTER.
    2: { done. } 
    destruct decide; [done| ].
    inversion SUB. subst. clear SUB.
    eapply mk_is_Some, LEN in AFTER.
    split; auto.
    lia_NO' max_len. 
    destruct (decide (start < n0)); [done| ].
    destruct n. f_equal. lia.
  Qed. 

  (* TODO: is it possible to show their equality? *)
  (* also possible to generalize to any max_len >= len(tr) *)
  Lemma inf_subtrace_after_lookup (tr str atr: trace St L) k
    (SUB: subtrace tr k NOinfinity = Some str)
    (AFTER: after k tr = Some atr):
    forall k, str !! k = atr !! k.
  Proof. 
    intros.
    erewrite (trace_lookup_after tr atr); eauto.
    eapply subtrace_lookup; done. 
  Qed. 

End Subtrace.


Section ModelSubtrace.
  Context {St L: Type}. 

  Lemma fair_by_subtrace
    (tr str: trace St (option L)) k P
    (SUB: subtrace tr k NOinfinity = Some str)
    (FAIR: ∀ ρ, fair_by P ρ tr):
    ∀ ρ, fair_by P ρ str.
  Proof. 
    intros.
    pose proof (trace_has_len tr) as [len LEN]. 
    forward eapply subtrace_inv as [_ BOUND]; eauto.
    apply LEN in BOUND as [atr AFTER]. 
    eapply (fair_by_after P ρ tr atr) in FAIR; eauto.
    red. intros.
    apply pred_at_trace_lookup' in H as (s & step & NTH & Ps).
    red in FAIR. specialize (FAIR n). specialize_full FAIR.
    { apply pred_at_trace_lookup'.
      erewrite <- inf_subtrace_after_lookup; eauto. }
    destruct FAIR as [m FAIR]. exists m.
    apply pred_at_or. apply pred_at_trace_lookup'. 
    apply pred_at_or in FAIR.
    apply pred_at_trace_lookup' in FAIR as (s'&step'&MNth&PROP).
    erewrite inf_subtrace_after_lookup; eauto.
  Qed.
  
  
  From Paco Require Import paco1 paco2 pacotac.
  (* TODO: merge with mtrace_valid_steps'*)
  Lemma trace_valid_equiv `{M: FairModel} (tr: mtrace M)
    (VALID': forall i s1 ℓ s2, tr !! i = Some (s1, Some (ℓ, s2)) ->
                          fmtrans _ s1 ℓ s2):
    mtrace_valid tr. 
  Proof. 
    pcofix V.
    intros; pfold.
    rewrite (trace_unfold_fold tr); simpl.
    destruct tr.
    { constructor. }
  Admitted.
  
  
  (* TODO: move *)
  Lemma subtrace_valid `{M: FairModel} (tr: mtrace M) len
    str start max_len
    (LEN: trace_len_is tr len)
    (VALID: mtrace_valid tr)
    (BOUND: NOmega.le max_len len) (* TODO: relax? *)
    (SUB2: subtrace tr start max_len = Some str):
    mtrace_valid str.
  Proof.
    forward eapply subtrace_inv as [LT1 LT2]; eauto.
    apply trace_valid_equiv. intros.
    eapply mtrace_valid_steps' in VALID; eauto.
    rewrite -H. symmetry.
    forward eapply (subtrace_len tr _ _ max_len); eauto.
    intros (str' & SUB' & LEN').
    assert (str' = str) as -> by congruence.
    assert (NOmega.lt_nat_l (i + 1) (NOmega.sub max_len (NOnum start))) as LT'.
    { eapply trace_lookup_dom_strong; eauto. }
    eapply subtrace_lookup; eauto.
    lia_NO max_len. 
  Qed. 

End ModelSubtrace.
