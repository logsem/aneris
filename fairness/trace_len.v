From trillium.fairness Require Import my_omega lemmas. 
From trillium.fairness Require Import inftraces trace_utils.

Section TraceLen.
  Context {St L: Type}. 

  Instance NOmega_lt_le (x y: nat_omega):
    Decision (NOmega.lt x y). 
  Proof using. 
    destruct x, y; simpl; solve_decision.
  Qed. 

  Definition trace_len_is (tr: trace St L) (len: nat_omega) :=
    forall (i: nat), is_Some (after i tr) <-> NOmega.lt_nat_l i len. 
      
  Lemma trace_has_len (tr: trace St L):
    exists len, trace_len_is tr len.
  Proof using. 
    destruct (infinite_or_finite tr) as [INF | FIN_].
    { exists NOinfinity. red. intros. red in INF.
      simpl. split; auto using INF. }
    red in FIN_. 
    assert (exists n, ClassicalFacts.Minimal (fun n => after n tr = None) n) as FIN.
    { destruct FIN_. eapply min_prop_dec; eauto. solve_decision. }
    clear FIN_. destruct FIN as [n [SIZE MIN]]. 
    exists (NOnum n). red. intros i. simpl. split.
    - intros SOME. destruct (le_lt_dec n i) as [LE| ]; auto.
      apply Nat.le_sum in LE as [d ->].
      rewrite after_sum' in SOME. rewrite SIZE in SOME. by destruct SOME.
    - intros LT. destruct (is_Some_dec (after i tr)); auto.
      specialize (MIN i). destruct (after i tr); try done.
      specialize (MIN eq_refl). lia. 
  Qed. 

  Lemma trace_len_cons s l (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    trace_len_is (s -[l]-> tr) (NOmega.succ len).
  Proof. 
    unfold trace_len_is in *. intros.
    destruct i.
    { simpl. lia_NO' len. simpl. intuition. lia. }
    simpl. rewrite LEN. lia_NO len.
  Qed.
  
  Lemma trace_len_uniq (tr: trace St L) (len1 len2: nat_omega)
    (LEN1: trace_len_is tr len1) (LEN2: trace_len_is tr len2):
    len1 = len2. 
  Proof. 
    unfold trace_len_is in *.
    destruct (NOmega.lt_trichotomy len1 len2) as [?|[?|?]]; auto.
    - destruct len1; [done| ].
      pose proof (proj2 (LEN2 n)) as L2. specialize (L2 ltac:(lia_NO len2)).
      specialize (proj1 (LEN1 _) L2). simpl. lia.
    - destruct len2; [done| ].
      pose proof (proj2 (LEN1 n)) as L1. specialize (L1 ltac:(lia_NO len1)).
      specialize (proj1 (LEN2 _) L1). simpl. lia.
  Qed. 
  
  Lemma trace_len_tail s l (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is (s -[l]-> tr) len):
    trace_len_is tr (NOmega.pred len).
  Proof.
    pose proof (trace_has_len tr) as [len' LEN'].
    pose proof (trace_len_cons s l _ _ LEN').
    forward eapply (trace_len_uniq _ _ _ LEN H) as ->; eauto.
    lia_NO' len'. 
  Qed.

  Lemma trace_len_singleton (s: St):
    trace_len_is ⟨ s ⟩ (NOnum 1).
  Proof. 
    red. intros. destruct i; simpl.
    - rewrite is_Some_Some_True. lia.
    - rewrite is_Some_None_False. lia.
  Qed. 

  Local Ltac gd t := generalize dependent t.

  Lemma trace_len_after (tr tr': trace St L) i
    (len: nat_omega)
    (LEN: trace_len_is tr len)
    (AFTER: after i tr = Some tr'):
    trace_len_is tr' (NOmega.sub len (NOnum i)).
  Proof.
    gd tr. gd tr'. gd len. induction i.
    { intros. simpl in AFTER. 
      rewrite NOmega.sub_0_r. inversion AFTER. by subst. }
    intros. destruct tr; [done| ].
    simpl in AFTER.
    pose proof (trace_len_tail _ _ _ _ LEN).
    specialize (IHi _ _ _ H AFTER).
    lia_NO' len. simpl in *.
    by replace (n - S i) with (Nat.pred n - i) by lia.
  Qed. 

  Lemma trace_len_0_inv (tr: trace St L)
    (LEN1: trace_len_is tr (NOnum 0)):
    False. 
  Proof.
    pose proof (proj1 (LEN1 0)). specialize_full H; eauto.
    red in H. lia. 
  Qed. 

  Lemma trace_len_gt_0 (tr: trace St L):
    forall len, trace_len_is tr len -> NOmega.lt_nat_l 0 len.
  Proof. 
    intros. lia_NO' len. destruct n; [| lia].
    by apply trace_len_0_inv in H. 
  Qed. 

  Lemma trace_len_1_inv (tr: trace St L)
    (LEN1: trace_len_is tr (NOnum 1)):
    exists s, tr = ⟨ s ⟩.
  Proof. 
    destruct tr; eauto.
    pose proof (proj1 (LEN1 1)). specialize_full H; eauto.
    red in H. lia. 
  Qed.    

  Lemma trace_len_neg (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall (i: nat), after i tr = None <-> NOmega.le len (NOnum i).
  Proof. 
    intros. specialize (LEN i).
    destruct (after i tr).
    - apply proj1 in LEN. specialize_full LEN; eauto. 
      split; try done. lia_NO len.
    - split; try done. intros _.
      lia_NO' len.
      + by destruct (proj2 LEN I).
      + destruct (decide (n <= i)); [done| ].
        by destruct (proj2 LEN ltac:(lia)).
  Qed.

  Lemma terminating_trace_equiv (tr: trace St L) len
    (LEN: trace_len_is tr len):
    terminating_trace tr <-> exists n, len = NOnum n.
  Proof.
    rewrite /terminating_trace. split.
    - intros [? N]. eapply trace_len_neg in N; eauto.
      lia_NO' len. eauto.
    - intros [? ->]. exists x.
      eapply trace_len_neg; eauto. simpl. lia.
  Qed. 

  Lemma infinite_trace_equiv (tr : trace St L) (len : nat_omega)
    (LEN: trace_len_is tr len):
    infinite_trace tr ↔ len = NOinfinity. 
  Proof.
    rewrite /infinite_trace. split.
    - intros A. destruct len; [done| ].
      eapply trace_len_neg with (i := n), proj2 in LEN. 
      specialize (A n) as [? T]. rewrite LEN in T; [done| ]. simpl. lia. 
    - intros -> ?. by apply LEN.
  Qed.     

End TraceLen.


Section TracesMatch.
  (* Context {L1 L2 S1 S2 : Type}. *)

  Lemma traces_match_same_length_impl {L1 L2 S1 S2 : Type}
    R1 R2 step1 step2 tr1 tr2 len1 len2
    (LEN1: trace_len_is tr1 len1)
    (LEN2: trace_len_is tr2 len2)
    (MATCH: @traces_match L1 L2 S1 S2 R1 R2 step1 step2 tr1 tr2)
    (LT: NOmega.lt len1 len2):
    False. 
  Proof.
    destruct len1; [done| ].
    pose proof (proj2 (LEN2 n)) as LL2. specialize (LL2 ltac:(lia_NO len2)) as [atr2 AFTER2].
    pose proof (traces_match_after _ _ _ _ _ _ _ _ MATCH AFTER2) as (atr1 & AFTER1 & _).
    specialize (proj1 (LEN1 _) (mk_is_Some _ _ AFTER1)). simpl. lia.
  Qed.
    
  Lemma traces_match_same_length {L1 L2 S1 S2 : Type}
    R1 R2 step1 step2 tr1 tr2 len1 len2
    (LEN1: trace_len_is tr1 len1)
    (LEN2: trace_len_is tr2 len2)
    (MATCH: @traces_match L1 L2 S1 S2 R1 R2 step1 step2 tr1 tr2):
    len1 = len2.
  Proof. 
    unfold trace_len_is in *.
    destruct (NOmega.lt_trichotomy len1 len2) as [?|[?|?]]; auto; exfalso. 
    - eapply traces_match_same_length_impl with (tr1 := tr1) (tr2 := tr2); eauto. 
    - apply traces_match_flip in MATCH. 
      eapply @traces_match_same_length_impl with (tr1 := tr2) (tr2 := tr1); eauto.
  Qed. 

End TracesMatch.
