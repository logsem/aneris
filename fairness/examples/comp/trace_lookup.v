From trillium.fairness.examples.comp Require Import my_omega lemmas trace_len.
From trillium.fairness Require Import inftraces.

Section TraceLookup.
  Context {St L: Type}. 

  (* Postpone instantiation of Lookup to make the notations work properly after *)
  Let trace_lookup_impl (tr: trace St L) i :=
        match (after i tr) with
        | None => None
        | Some (tr_singl s) => Some (s, None)
        | Some (tr_cons s l tr') => Some (s, Some (l, trfirst tr'))
        end.


  Definition state_lookup (tr: trace St L) (i: nat): option St := 
    match trace_lookup_impl tr i with
    | Some (st, _) => Some st
    | None => None
    end. 
    
  Definition label_lookup (tr: trace St L) (i: nat): option L := 
    match trace_lookup_impl tr i with
    | Some (_, Some (ℓ, _)) => Some ℓ
    | _ => None
    end.

  Global Instance state_lookup_Lookup: Lookup nat St (trace St L) :=
    fun i tr => state_lookup tr i. 

  Global Instance label_lookup_Lookup: Lookup nat L (trace St L) :=
    fun i tr => label_lookup tr i. 

  Notation "tr S!! i" := (state_lookup tr i) (at level 20). 
  Notation "tr L!! i" := (label_lookup tr i) (at level 20). 
  
  Global Instance trace_lookup: Lookup nat (St * option (L * St)) (trace St L) :=
    fun i tr => trace_lookup_impl tr i.

  Local Ltac unfold_lookups :=
    rewrite /lookup /state_lookup /label_lookup /trace_lookup /trace_lookup_impl.

  Lemma trace_lookup_trichotomy (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, (exists st ℓ st', tr !! i = Some (st, Some (ℓ, st')) /\ NOmega.lt_nat_l (i + 1) len) \/
         (exists st, tr !! i = Some (st, None) /\ len = NOnum (i + 1)) \/
         (tr !! i = None /\ NOmega.le len (NOnum i)). 
  Proof using. 
    intros.
    pose proof (LEN i) as Ai. pose proof (LEN (i + 1)) as Ai'.
    rewrite after_sum' in Ai'. 
    destruct (NOmega_lt_le (NOnum i) len).
    2: { right. right. apply not_iff_compat, proj2 in Ai, Ai'.
         destruct len; simpl in *; try done.
         specialize (Ai ltac:(lia)). specialize (Ai' ltac:(lia)). 
         split; [| lia].
         apply eq_None_not_Some in Ai. rewrite Ai in Ai'.
         unfold_lookups. by rewrite Ai. }
    apply proj2 in Ai.
    specialize (Ai ltac:(lia_NO len)) as [ti Ai]. 
    rewrite Ai in Ai'. 
    destruct (decide (NOnum (i + 1) = len)) eqn:EQ'.
    { right. left. subst. simpl in *. clear EQ'.
      apply not_iff_compat, proj2 in Ai'. specialize (Ai' ltac:(lia)). 
      apply eq_None_not_Some in Ai'.
      unfold_lookups. rewrite Ai. destruct ti; eauto. congruence. }
    assert (NOmega.lt_nat_l (i + 1) len) as LT'.
    { destruct len; try done; simpl in *.
      destruct (decide (i + 1 < n0)); auto. destruct n. f_equal. lia. }
    left.
    apply proj2 in Ai'. specialize (Ai' LT'). destruct Ai' as [ti' Ai'].
    unfold_lookups. rewrite Ai. 
    destruct ti; simpl in *; eauto. congruence. 
  Qed. 

  Lemma trace_lookup_dom (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, is_Some (tr !! i) <-> NOmega.lt_nat_l i len.
  Proof using. 
    intros i. destruct (trace_lookup_trichotomy _ _ LEN i) as [LT | [EQ | GT]].
    - destruct LT as (?&?&?&LT&?). rewrite LT.
      split; intros; auto.
      destruct len; simpl in *; try lia. 
    - destruct EQ as (?&EQ&?). subst.
      rewrite EQ. split; simpl in *; intros; auto. lia. 
    - destruct GT as [GT ?]. split; intros.
      + rewrite GT in H0. by destruct H0. 
      + lia_NO len. 
  Qed. 

  Lemma trace_lookup_dom_strong (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, (exists st ℓ st', tr !! i = Some (st, Some (ℓ, st'))) <-> NOmega.lt_nat_l (i + 1) len.
  Proof using. 
    intros i. destruct (trace_lookup_trichotomy _ _ LEN i) as [LT | [EQ | GT]].
    - destruct LT as (?&?&?&LT&?). rewrite LT. 
      split; intros; eauto. 
    - destruct EQ as (?&->&?).
      subst. split; intros. 
      + destruct H as (?&?&?&?). congruence. 
      + simpl in *; lia.
    - destruct len; try done; simpl in *.
      + tauto. 
      + destruct GT as [-> ?]. split.
        * by intros (?&?&?&?).
        * lia. 
  Qed.

  Lemma trace_lookup_dom_eq (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, (exists st, tr !! i = Some (st, None)) <-> len = NOnum (i + 1). 
  Proof using.
    intros i. destruct (trace_lookup_trichotomy _ _ LEN i) as [LT | [EQ | GT]].
    - destruct LT as (?&?&?&LT&?). rewrite LT. split; intros. 
      + by destruct H0. 
      + subst. simpl in *; lia.
    - destruct EQ as (?&->&?). split; intros; eauto.
    - destruct len; try done; simpl in *.
      + tauto. 
      + destruct GT as [-> ?]. split.
        * by intros (?&?).
        * intros [=]. lia. 
  Qed.

  Lemma state_label_lookup (tr: trace St L):
    forall i st st' ℓ, 
      tr !! i = Some (st, Some (ℓ, st')) <->
      (tr S!! i = Some st /\ tr S!! (i + 1) = Some st' /\ tr L!! i = Some ℓ).
  Proof using. 
    intros. unfold_lookups. rewrite after_sum'.
    destruct (after i tr); simpl. 
    2: { split; [intros [=] | intros [[=] _]]. }
    destruct t; auto.
    { split; [intros [=] | intros [_ [[=] _]]]. }
    simpl. split; intros.
    - inversion H. subst. split; auto. destruct t; auto. 
    - destruct t; destruct H as ([=] & [=] & [=]); subst; auto. 
  Qed. 

  Lemma state_lookup_dom (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, is_Some (tr S!! i) <-> NOmega.lt_nat_l i len.
  Proof using. 
    intros. etransitivity; [| apply trace_lookup_dom]; eauto.
    unfold_lookups. destruct (after i tr); try done.
    2: { split; by intros []. }
    by destruct t. 
  Qed. 
  
  Lemma label_lookup_dom (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, is_Some (tr L!! i) <-> NOmega.lt_nat_l (i + 1) len.
  Proof using. 
    intros. rewrite /label_lookup.
    pose proof (trace_lookup_trichotomy _ _ LEN i) as X. rewrite /lookup /trace_lookup in X.
    destruct X as [LT | [EQ | GT]].  
    - destruct LT as (?&?&?&LT&?). rewrite LT. done.
    - destruct EQ as (?&->&->). simpl. split; [by intros []| lia]. 
    - destruct GT as [-> ?].
      lia_NO' len. split; [by intros []| lia]. 
  Qed. 

  Lemma state_lookup_prev (tr: trace St L) i (DOM: is_Some (tr S!! i)):
    forall j (LE: j <= i), is_Some (tr S!! j). 
  Proof using. 
    intros. pose proof (trace_has_len tr) as [len ?].
    eapply state_lookup_dom in DOM; eauto.
    eapply state_lookup_dom; eauto. destruct len; eauto. simpl in *. lia. 
  Qed.  
    
  Lemma label_lookup_states (tr: trace St L):
    forall i, is_Some (tr L!! i) <-> is_Some (tr S!! i) /\ is_Some (tr S!! (i + 1)). 
  Proof using. 
    pose proof (trace_has_len tr) as [len ?].
    intros. etransitivity; [apply label_lookup_dom| ]; eauto.
    etransitivity; [symmetry; eapply state_lookup_dom| ]; eauto.
    split; try tauto. intros. split; auto. 
    eapply state_lookup_prev; eauto. lia.    
  Qed.     

  Lemma pred_at_trace_lookup (tr: trace St L) (i: nat) P:
      pred_at tr i P <-> exists st, tr S!! i = Some st /\ P st (tr L!! i). 
  Proof using.
    destruct (trace_has_len tr) as [len LEN].
    rewrite /state_lookup /label_lookup /trace_lookup_impl.
    rewrite /pred_at. destruct (after i tr) eqn:Ai.
    2: { split; intros; try done. by destruct H as [? [[=] ?]]. }
    destruct t; split; intros; eauto; destruct H as [? [[=] ?]]; congruence.
  Qed. 

  Lemma pred_at_trace_lookup' (tr : trace St L) (i : nat) (P : St → option L → Prop):
    pred_at tr i P ↔ exists s step, tr !! i = Some (s, step) /\ 
                                 P s (from_option (Some ∘ fst) None step). 
  Proof.
    rewrite pred_at_trace_lookup.
    pose proof (trace_has_len tr) as [len LEN]. 
    destruct (trace_lookup_trichotomy _ _ LEN i) as [T|[T|T]].
    - destruct T as (?&?&?&ITH&?).
      rewrite ITH. 
      rewrite /lookup /trace_lookup in ITH.
      rewrite /lookup /state_lookup /label_lookup. 
      rewrite ITH. split. 
      + intros (?&[=->]&?). eauto.
      + intros (?&?&[=->]&?). subst. eauto.
    - destruct T as (?&ITH&->).
      rewrite ITH.
      rewrite /lookup /trace_lookup in ITH.
      rewrite /lookup /state_lookup /label_lookup. 
      rewrite ITH. split.
      + intros (?&[=->]&?). eauto.
      + intros (?&?&[=]&?). subst. eauto.
    - destruct T as [ITH ?]. rewrite ITH.
      rewrite /lookup /trace_lookup in ITH.
      rewrite /lookup /state_lookup /label_lookup. 
      rewrite ITH. split.
      + by intros (?&[=]&?).
      + by intros (?&?&[=]&?).
  Qed. 

  Lemma inf_trace_lookup (tr: trace St L)
    (INF: trace_len_is tr NOinfinity):
    forall i, exists c1 ℓ c2, tr !! i = Some (c1, Some (ℓ, c2)).
  Proof. 
    intros. eapply trace_lookup_dom_strong; done.
  Qed. 

  Lemma trace_lookup_cons s l (tr: trace St L) i:
    (s -[ l ]-> tr) !! S i = tr !! i.
  Proof. done. Qed. 
    
  Lemma trace_state_lookup_simpl (tr: trace St L) i s' step s
    (TLi: tr !! i = Some (s', step))
    (SLi: tr S!! i = Some s):
    s' = s.
  Proof.
    rewrite /state_lookup in SLi. rewrite /lookup /trace_lookup in TLi.
    destruct (trace_lookup_impl tr i) as [[??]|]; congruence. 
  Qed. 

  Lemma trace_lookup_0_cons s ℓ (tr: trace St L):
    (s -[ℓ]-> tr) !! 0 = Some (s, Some (ℓ, trfirst tr)).
  Proof. done. Qed.

  Lemma state_lookup_cons s l (tr: trace St L) i:
    (s -[ l ]-> tr) S!! S i = tr S!! i.
  Proof. done. Qed.
    
  Lemma label_lookup_cons s l (tr: trace St L) i:
    (s -[ l ]-> tr) S!! S i = tr S!! i.
  Proof. done. Qed.
    
  Lemma trace_lookup_after (tr atr: trace St L) (a: nat)
    (AFTER: after a tr = Some atr):
    forall k, atr !! k = tr !! (a + k).
  Proof. 
    intros. rewrite /lookup /trace_lookup /trace_lookup_impl. 
    rewrite after_sum'. by rewrite AFTER.
  Qed. 
    
  Lemma state_lookup_after (tr atr: trace St L) (a: nat)
    (AFTER: after a tr = Some atr):
    forall k, atr S!! k = tr S!! (a + k).
  Proof. 
    intros. rewrite /state_lookup /trace_lookup_impl. 
    rewrite after_sum'. by rewrite AFTER.
  Qed. 
    
End TraceLookup.

Notation "tr S!! i" := (state_lookup tr i) (at level 20). 
Notation "tr L!! i" := (label_lookup tr i) (at level 20). 
