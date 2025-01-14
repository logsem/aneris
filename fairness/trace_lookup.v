From trillium.fairness Require Import my_omega lemmas trace_len.
From trillium.fairness Require Import inftraces trace_utils utils.

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

  Lemma trace_lookup_dom_neg (tr : trace St L) (len : nat_omega)
    (LEN: trace_len_is tr len):
    ∀ i, tr !! i = None ↔ NOmega.le len (NOnum i).
  Proof. 
    intros. erewrite <- trace_len_neg; eauto.
    unfold_lookups. destruct after; [destruct t| ]; done.
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

  Lemma state_lookup_dom_neg (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, tr S!! i = None <-> NOmega.le len (NOnum i).
  Proof using.
    intros i.
    pose proof (state_lookup_dom _ _ LEN i) as EQUIV.
    apply not_iff_compat in EQUIV. 
    by rewrite -eq_None_not_Some -NOmega.le_iff_not_lt_nat in EQUIV.
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
    
  Lemma label_lookup_prev (tr : trace St L) i (DOM: is_Some (tr L!! i)):
    ∀ j (LE: j ≤ i), is_Some (tr L!! j).
  Proof using.
    intros. pose proof (trace_has_len tr) as [len ?].
    eapply label_lookup_dom in DOM; eauto.
    eapply label_lookup_dom; eauto. destruct len; eauto. simpl in *. lia.
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

  Lemma label_lookup_states' (tr: trace St L):
    forall i, is_Some (tr L!! i) <-> is_Some (tr S!! (S i)). 
  Proof using.
    intros. rewrite label_lookup_states.
    rewrite Nat.add_1_r. rewrite and_comm iff_and_impl_helper; [done| ].
    intros. eapply state_lookup_prev; eauto. 
  Qed.

  Lemma next_state_lookup (tr: trace St L):
    forall i, is_Some (tr S!! (S i)) <-> is_Some (tr S!! i) /\ is_Some (tr L!! i).
  Proof using.
    intros. rewrite label_lookup_states. rewrite Nat.add_1_r.
    split; [| tauto]. intros. apply and_assoc. split; eauto.
    rewrite and_idemp. eapply state_lookup_prev; eauto.
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
    
  Lemma trace_label_lookup_simpl (tr: trace St L) i step ℓ
    (TLi: tr !! i = Some step)
    (SLi: tr L!! i = Some ℓ):
    exists s1 s2, step = (s1, Some (ℓ, s2)). 
  Proof.
    rewrite /label_lookup /trace_lookup_impl in SLi. rewrite /lookup /trace_lookup /trace_lookup_impl in TLi.
    destruct (after i tr); try done.
    destruct t; try done. inversion SLi. inversion TLi. subst. eauto.  
  Qed. 

  Lemma state_lookup_0 (tr: trace St L):
    tr S!! 0 = Some (trfirst tr). 
  Proof. by destruct tr. Qed.

  Lemma label_lookup_0 st ℓ (tr: trace St L):
    (st -[ℓ]-> tr) L!! 0 = Some ℓ. 
  Proof. done. Qed.

  Lemma trace_state_lookup_simpl' (tr: trace St L) i st:
    (exists step, tr !! i = Some step /\ fst step = st) <-> tr S!! i = Some st. 
  Proof.
    unfold_lookups. 
    destruct after.
    2: { split; [intros (?&?&?) | intros ?]; done. }
    destruct t.
    all: split; [intros  ([??]&?&?) | intros [=]]; simpl in *; subst.
    all: congruence || eauto. 
  Qed. 

  Lemma trace_state_lookup (tr: trace St L) i st ostep
    (ITH: tr !! i = Some (st, ostep)):
    tr S!! i = Some st.
  Proof. 
    eapply trace_state_lookup_simpl'; eauto. 
  Qed. 

  Lemma trace_label_lookup_simpl' (tr: trace St L) i ℓ:
    (exists s1 s2, tr !! i = Some (s1, Some (ℓ, s2))) <-> tr L!! i = Some ℓ. 
  Proof.
    split.
    { intros (?&?&?%state_label_lookup). tauto. }
    unfold_lookups. 
    destruct after; [| done].
    destruct t; [done| ]. intros [=->]. eauto.
  Qed. 

  Lemma trace_lookup_0_singleton (s: St):    
     (⟨ s ⟩: trace St L) !! 0 = Some (s, None).
  Proof. done. Qed. 

  Lemma trace_lookup_0 (tr: trace St L):    
    exists ostep, tr !! 0 = Some (trfirst tr, ostep).
  Proof.
    destruct tr; eauto. 
  Qed.

  Lemma trace_lookup_0_Some (tr: trace St L):
    is_Some (tr !! 0). 
  Proof.
    pose proof (trace_has_len tr) as [len LEN]. 
    eapply trace_lookup_dom; eauto.
    eapply trace_len_gt_0; eauto. 
  Qed.

End TraceLookup.

Notation "tr S!! i" := (state_lookup tr i) (at level 20). 
Notation "tr L!! i" := (label_lookup tr i) (at level 20). 


Section After.
  Context {St L: Type}. 

  Local Ltac unfold_lookups :=
    rewrite /lookup /state_lookup /label_lookup /trace_lookup.

  Lemma trace_lookup_after (tr atr: trace St L) (a: nat)
    (AFTER: after a tr = Some atr):
    forall k, atr !! k = tr !! (a + k).
  Proof. 
    intros. unfold_lookups. 
    rewrite after_sum'. by rewrite AFTER.
  Qed. 

  Lemma state_lookup_after (tr atr: trace St L) (a: nat)
    (AFTER: after a tr = Some atr):
    forall k, atr S!! k = tr S!! (a + k).
  Proof. 
    intros. unfold_lookups. 
    rewrite after_sum'. by rewrite AFTER.
  Qed. 

  Lemma label_lookup_after (tr atr: trace St L) (a: nat)
    (AFTER: after a tr = Some atr):
    forall k, atr L!! k = tr L!! (a + k).
  Proof. 
    intros. unfold_lookups. 
    rewrite after_sum'. by rewrite AFTER.
  Qed.

  Lemma state_lookup_after_0 (tr atr : trace St L) n
    (AFTER: after n tr = Some atr):
    tr S!! n = Some (trfirst atr).
  Proof. 
    rewrite -(Nat.add_0_r n).
    erewrite <- state_lookup_after; eauto.
    apply state_lookup_0.
  Qed.

  Lemma state_lookup_after' (tr: trace St L) n st:
    (exists atr, after n tr = Some atr /\ trfirst atr = st) <-> tr S!! n = Some st. 
  Proof. 
    destruct (after n tr) as [atr| ] eqn:AFTER.
    2: { split; [by intros (?&?&?)| ].
         pose proof (trace_has_len tr) as [len ?]. 
         eintros ?%mk_is_Some%state_lookup_dom; eauto.
         eapply trace_len_neg in AFTER; eauto. lia_NO len. }
    erewrite state_lookup_after_0; eauto.
    split. 
    - intros (?&[=->]&?). congruence.
    - intros [=]. eauto.
  Qed. 

  Lemma trace_lookup_after_strong (tr: trace St L) s1 ℓ s2 n:
    (exists atr', after n tr = Some (s1 -[ℓ]-> atr') /\ trfirst atr' = s2) <-> tr !! n = Some (s1, Some (ℓ, s2)). 
  Proof. 
    destruct (after n tr) as [atr| ] eqn:AFTER.
    2: { split; [by intros (?&?&?)| ].
         pose proof (trace_has_len tr) as [len LEN].
         intros NTH.
         forward eapply (proj1 (trace_lookup_dom_strong _ _ LEN n)); eauto.
         eapply trace_len_neg in AFTER; eauto. lia_NO len. }

    rewrite /lookup /trace_lookup AFTER. 
    split.
    - intros (?&[=->]&?). congruence.
    - intros EQ. destruct atr; [congruence| ].
      inversion EQ. subst. eauto. 
  Qed.

  Lemma trace_lookup_after_weak (tr: trace St L) s n:
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

  Lemma trace_lookup_prev (tr: trace St L) i st2 ostep
    (ITH': tr !! S i = Some (st2, ostep)):
    exists st1 l, tr !! i = Some (st1, Some (l, st2)).
  Proof.
    pose proof (trace_has_len tr) as [len LEN]. 
    forward eapply (proj2 (trace_lookup_dom_strong _ _ LEN i)).
    { eapply trace_lookup_dom; eauto.
      by rewrite Nat.add_1_r. }
    intros (?&?&st'&ITH).
    enough (st' = st2).
    { subst. eauto. }    
    apply state_label_lookup in ITH as (?&ITH'_&?).
    rewrite Nat.add_1_r in ITH'_.
    symmetry. 
    eapply trace_state_lookup_simpl; eauto.
  Qed.

End After.


Section TracesMatch.
  Context {L1 L2 S1 S2: Type}.
  Context {Rℓ : L1 → L2 → Prop}.
  Context {Rs : S1 → S2 → Prop}.
  Context {trans1 : S1 → L1 → S1 → Prop}.
  Context {trans2 : S2 → L2 → S2 → Prop}.  
  

  Lemma traces_match_trace_lookup_general 
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat)
    (MATCH: traces_match Rℓ Rs trans1 trans2 tr1 tr2):
    match tr1 !! n, tr2 !! n with
    | Some step1, Some step2 => 
        Rs (fst step1) (fst step2) /\
          match snd step1, snd step2 with 
          | Some (ℓ1, s1'), Some (ℓ2, s2') => Rℓ ℓ1 ℓ2 /\ Rs s1' s2'
          | None, None => True
          | _, _ => False
          end
    | None, None => True
    | _ , _ => False
    end. 
  Proof. 
    pose proof (trace_has_len tr1) as [len LEN1]. pose proof (trace_has_len tr2) as [? LEN2].
    forward eapply (traces_match_same_length _ _ _ _ tr1 tr2) as X; eauto. subst x.
    destruct (tr1 !! n) as [[s1 step1]| ] eqn:STEP1, (tr2 !! n) as [[s2 step2]| ] eqn:STEP2. 
    4: done. 
    3: { eapply mk_is_Some, trace_lookup_dom in STEP2; eauto. 
         eapply trace_lookup_dom_neg in STEP1; eauto.
         lia_NO len. }
    2: { eapply mk_is_Some, trace_lookup_dom in STEP1; eauto. 
         eapply trace_lookup_dom_neg in STEP2; eauto.
         lia_NO len. }

    forward eapply (proj1 (trace_state_lookup_simpl' tr1 n s1)) as ST1; eauto.  
    forward eapply (proj1 (trace_state_lookup_simpl' tr2 n s2)) as ST2; eauto.  
    simpl in *.
    pose proof (proj2 (state_lookup_after' _ _ _) ST1) as (atr1 & AFTER1 & A1).
    forward eapply traces_match_after' with (tr1 := tr1) (tr2 := tr2); eauto.
    intros (atr2 & AFTER2 & A2). 
    split.
    { apply traces_match_first in A2.
      erewrite state_lookup_after_0 in ST1; eauto. 
      erewrite state_lookup_after_0 in ST2; eauto.
      congruence. }
    destruct step1 as [[ℓ1 s1']| ], step2 as [[ℓ2 s2']| ].
    4: done.
    3: { forward eapply (proj1 (trace_lookup_dom_strong _ _ LEN2 n)); eauto.
         forward eapply (proj1 (trace_lookup_dom_eq _ _ LEN1 n)); eauto.
         lia_NO' len. intros [=]. lia. }
    2: { forward eapply (proj1 (trace_lookup_dom_strong _ _ LEN1 n)); eauto.
         forward eapply (proj1 (trace_lookup_dom_eq _ _ LEN2 n)); eauto.
         lia_NO' len. intros [=]. lia. }
    
    apply trace_lookup_after_strong in STEP1 as (?&AFTER1'&?), STEP2 as (?&AFTER2'&?).
    erewrite AFTER1' in AFTER1. rewrite AFTER2' in AFTER2.
    inversion AFTER1. inversion AFTER2. subst atr1 atr2.
    inversion A2. subst. split; eauto.
    eapply traces_match_first; eauto.
  Qed.

  Lemma traces_match_state_lookup_1
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat) st1
    (MATCH: traces_match Rℓ Rs trans1 trans2 tr1 tr2)
    (ST1: tr1 S!! n = Some st1):
    exists st2, tr2 S!! n = Some st2 /\ Rs st1 st2.
  Proof. 
    apply trace_state_lookup_simpl' in ST1 as ([s1 ostep1] & NTH1 & <-).
    pose proof (traces_match_trace_lookup_general _ _ n MATCH) as STEPS.
    rewrite NTH1 in STEPS.
    destruct (tr2 !! n) as [[s2 ostep2]|] eqn:NTH2; [| done]. simpl in *.
    destruct STEPS. eexists. split; eauto.
    eapply trace_state_lookup_simpl'; eauto.
  Qed. 

  Lemma traces_match_state_lookup_2
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat) st2
    (MATCH: traces_match Rℓ Rs trans1 trans2 tr1 tr2)
    (ST2: tr2 S!! n = Some st2):
    exists st1, tr1 S!! n = Some st1 /\ Rs st1 st2.
  Proof. 
    apply trace_state_lookup_simpl' in ST2 as ([s2 ostep2] & NTH2 & <-).
    pose proof (traces_match_trace_lookup_general _ _ n MATCH) as STEPS.
    rewrite NTH2 in STEPS.
    destruct (tr1 !! n) as [[s1 ostep1]|] eqn:NTH1; [| done]. simpl in *.
    destruct STEPS. eexists. split; eauto.
    eapply trace_state_lookup_simpl'; eauto.
  Qed.

  Lemma traces_match_label_lookup_1
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat) ℓ1
    (MATCH: traces_match Rℓ Rs trans1 trans2 tr1 tr2)
    (LBL1: tr1 L!! n = Some ℓ1):
    exists ℓ2, tr2 L!! n = Some ℓ2 /\ Rℓ ℓ1 ℓ2. 
  Proof. 
    apply trace_label_lookup_simpl' in LBL1 as (s & s' & NTH1).
    pose proof (traces_match_trace_lookup_general _ _ n MATCH) as STEPS.
    rewrite NTH1 in STEPS.
    destruct (tr2 !! n) as [[s2 ostep2]|] eqn:NTH2; [| done]. simpl in *.
    destruct ostep2 as [[??]|]; [| tauto]. destruct STEPS as (?&?&?). 
    eexists. split; eauto.
    eapply trace_label_lookup_simpl'; eauto.
  Qed.

  Lemma traces_match_label_lookup_2
    (tr1 : trace S1 L1) (tr2 : trace S2 L2) (n : nat) ℓ2
    (MATCH: traces_match Rℓ Rs trans1 trans2 tr1 tr2)
    (LBL2: tr2 L!! n = Some ℓ2):
    exists ℓ1, tr1 L!! n = Some ℓ1 /\ Rℓ ℓ1 ℓ2. 
  Proof. 
    apply trace_label_lookup_simpl' in LBL2 as (s & s' & NTH2).
    pose proof (traces_match_trace_lookup_general _ _ n MATCH) as STEPS.
    rewrite NTH2 in STEPS.
    destruct (tr1 !! n) as [[s1 ostep1]|] eqn:NTH1; [| done]. simpl in *.
    destruct ostep1 as [[??]|]; [| tauto]. destruct STEPS as (?&?&?). 
    eexists. split; eauto.
    eapply trace_label_lookup_simpl'; eauto.
  Qed.

End TracesMatch. 


Section UptoStutter.
  Context {St S' L L' : Type}.
  Context {Us : St → S'}.
  Context {Usls: St -> L -> St -> option L'}.

  From Paco Require Import paco1 paco2 pacotac.

  Lemma upto_stutter_trace_label_lookup {btr : trace St L} {str : trace S' L'} 
    (n : nat) st ℓ st' l:
    upto_stutter Us Usls btr str →
    btr !! n = Some (st, Some (ℓ, st')) ->
    Usls st ℓ st' = Some l ->
      ∃ (n' : nat), str L!! n' = Some l.
  Proof.
    intros UPTO NTH MATCH.
    pose proof (trace_has_len btr) as [? LEN].
    apply trace_lookup_after_strong in NTH as (atr' & AFTER & A0). 
    forward eapply (upto_stutter_after' _ _ n UPTO); eauto.
    intros (n' & str' & AFTER' & UPTOn).
    exists n'.
    rewrite -(Nat.add_0_r n'). erewrite <- label_lookup_after; eauto.
    punfold UPTOn; [| by apply upto_stutter_mono].
    inversion UPTOn; subst; try congruence.
    rewrite label_lookup_0. congruence.  
  Qed.

  (* Lemma upto_stutter_trace_lookup' {btr : trace St L} {str : trace S' L'}  *)
  (*   (n : nat) st st' l: *)
  (*   upto_stutter Us Usls btr str → *)
  (*   str !! n = Some (st, Some (l, st')) -> *)
  (*   (* Usls st ℓ st' = Some l -> *) *)
  (*     ∃ (n' : nat) δ1 ℓ δ2 , btr !! n' = Some (δ1, Some (ℓ, δ2)) /\ *)
  (*                          Us δ1 = st /\ Us δ2 = st' /\ Usls δ1 ℓ δ2 = Some l. *)
  (* Proof. *)
  (*   intros UPTO NTH. *)
  (*   pose proof (trace_has_len btr) as [? LEN]. *)
  (*   apply trace_lookup_after_strong in NTH as (atr' & AFTER & A0).  *)
  (*   forward eapply (upto_stutter_after _ _ n UPTO); eauto. *)
  (*   intros (n' & str' & AFTER' & UPTOn). *)
  (*   exists n'. *)
  (*   rewrite -(Nat.add_0_r n'). erewrite <- trace_lookup_after; eauto. *)
  (*   punfold UPTOn; [| by apply upto_stutter_mono]. *)
  (*   inversion UPTOn; subst; try congruence. *)
  (*   2: { rewrite trace_lookup_0_cons. simpl in *. *)
  (*        do 3 eexists. split; [reflexivity| ..]. *)
  (*        repeat split; eauto. *)
  (*        pclearbot.  *)
  (*        by eapply upto_stutter_trfirst in H5. }  *)
  (*   rewrite trace_lookup_0_cons. *)
  (*   simpl in *. subst. *)
  (*   (* assume that dec_unless holds for btr, *)
  (*      prove that eventually there will be a step. *)
  (*      Try to reuse similar argument from inftraces.destutter_spec_ind ? *) *)
  (* Abort.  *)

  Lemma upto_stutter_state_lookup {btr : trace St L} {str : trace S' L'} n' st':
    upto_stutter Us Usls btr str
    → str S!! n' = Some st' ->
      ∃ n st, btr S!! n = Some st /\ Us st = st'.
  Proof.
    intros UPTO NTH.
    pose proof (trace_has_len str) as [? LEN]. 
    pose proof (proj1 (state_lookup_dom _ _ LEN n') (mk_is_Some _ _ NTH)) as BOUND.
    pose proof (proj2 (LEN _) BOUND) as [str_n AFTER].
    forward eapply (upto_stutter_after _ _ n' UPTO); eauto.
    intros (n & btr' & AFTER' & UPTOn).
    exists n.
    rewrite -(Nat.add_0_r n). erewrite <- state_lookup_after; eauto.
    rewrite state_lookup_0. f_equal.
    eexists. split; [reflexivity| ].
    etransitivity.
    { symmetry. eapply upto_stutter_trfirst; eauto. }
    apply Some_inj. rewrite -state_lookup_0.
    erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r.
  Qed. 

  Lemma upto_stutter_state_lookup' {btr : trace St L} {str : trace S' L'} (n : nat) bst:
    upto_stutter Us Usls btr str
    → btr S!! n = Some bst ->
      ∃ (n' : nat),
        str S!! n' = Some (Us bst).
  Proof.
    intros UPTO NTH.
    pose proof (trace_has_len btr) as [? LEN]. 
    pose proof (proj1 (state_lookup_dom _ _ LEN n) (mk_is_Some _ _ NTH)) as BOUND.
    pose proof (proj2 (LEN _) BOUND) as [btr_n AFTER].
    forward eapply (upto_stutter_after' _ _ n UPTO); eauto.
    intros (n' & str' & AFTER' & UPTOn).
    exists n'.
    rewrite -(Nat.add_0_r n'). erewrite <- state_lookup_after; eauto.
    rewrite state_lookup_0. f_equal.     
    erewrite upto_stutter_trfirst; [..| apply UPTOn]; eauto.
    f_equal. apply Some_inj.
    rewrite -state_lookup_0.
    erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r.
  Qed. 

  (* Lemma upto_stutter_state_lookup {btr : trace St L} {str : trace S' L'} n ℓ: *)
  (*   upto_stutter Us Usls btr str *)
  (*   → btr L!! n = Some ℓ -> *)
  (*     ∃ n' l, str L!! n' = Some l /\ Ul ℓ = l. *)
  (* Proof. *)
  (*   intros UPTO NTH. *)
  (*   pose proof (trace_has_len str) as [? LEN].  *)
  (*   pose proof (proj1 (state_lookup_dom _ _ LEN n') (mk_is_Some _ _ NTH)) as BOUND. *)
  (*   pose proof (proj2 (LEN _) BOUND) as [str_n AFTER]. *)
  (*   forward eapply (upto_stutter_after _ _ n' UPTO); eauto. *)
  (*   intros (n & btr' & AFTER' & UPTOn). *)
  (*   exists n. *)
  (*   rewrite -(Nat.add_0_r n). erewrite <- state_lookup_after; eauto. *)
  (*   rewrite state_lookup_0. f_equal. *)
  (*   eexists. split; [reflexivity| ]. *)
  (*   etransitivity. *)
  (*   { symmetry. eapply upto_stutter_trfirst; eauto. } *)
  (*   apply Some_inj. rewrite -state_lookup_0. *)
  (*   erewrite state_lookup_after; eauto. by rewrite Nat.add_0_r. *)
  (* Qed.  *)

End UptoStutter.


Section ValidTracesProperties.
  Context {St L: Type}.
  Context (trans: St -> L -> St -> Prop). 

  Context (tr: trace St L).
  Hypothesis VALID: trace_valid trans tr. 

  From Paco Require Import pacotac.
  Local Ltac gd t := generalize dependent t.
  
  Lemma trace_valid_steps' i st ℓ st'
    (ITH: tr !! i = Some (st, Some (ℓ, st'))):
    trans st ℓ st'. 
  Proof using VALID.
    gd st. gd ℓ. gd st'. gd tr. clear dependent tr. 
    induction i. 
    { simpl. intros. punfold VALID. inversion VALID.
      3: { by apply trace_valid_mono. } 
      - subst. done.
      - subst. inversion ITH. by subst. }
    intros. simpl in ITH.
    destruct tr.
    { inversion ITH. }
    punfold VALID; [| by apply trace_valid_mono]. 
    inversion_clear VALID; pclearbot; auto.
    eapply IHi; eauto. 
  Qed.
  
  Lemma trace_valid_steps'' i st ℓ st'
    (ST1: tr S!! i = Some st)
    (ST2: tr S!! (i + 1) = Some st')
    (LBL: tr L!! i = Some ℓ):
    trans st ℓ st'. 
  Proof using VALID.
    eapply trace_valid_steps'.
    apply state_label_lookup. eauto.
  Qed.      
  
End ValidTracesProperties. 
