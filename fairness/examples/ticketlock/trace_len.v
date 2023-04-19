From iris.proofmode Require Import tactics.
Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
Import derived_laws_later.bi.
Require Import Coq.Logic.Classical.
From trillium.fairness.examples.ticketlock Require Import lemmas.

Section TraceLen.
  From hahn Require Import HahnBase.
  From trillium.fairness.examples.ticketlock Require Import my_omega. 

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
      specialize (MIN i). specialize_full MIN; [| lia]. 
      destruct (after i tr); done.
  Qed. 
      
  (* Lookup nat (mstate M) utrace. *)
  Global Instance trace_lookup: 
    Lookup nat (St * option (L * St)) (trace St L).
  intros i tr.
  destruct (after i tr) eqn:AFTER.
  2: { exact None. }
  destruct t.
  - exact (Some (s, None)).
  - exact (Some (s, Some (ℓ, trfirst t))).
  Defined. 

  Lemma NOmega_trichotomy (x y: nat_omega):
    NOmega.lt x y \/ x = y \/ NOmega.lt y x. 
  Proof using. 
    destruct x, y; simpl; try lia; eauto.
    pose proof (PeanoNat.Nat.lt_trichotomy n n0).
    destruct H as [? | [? | ?]]; auto. 
  Qed. 

  Instance nat_omega_eq_dec: EqDecision nat_omega.
  Proof using. solve_decision. Qed.     

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
         specialize_full Ai; [lia| ]. specialize_full Ai'; [lia| ].
         split; [| lia].
         apply eq_None_not_Some in Ai. 
         rewrite /lookup /trace_lookup. by rewrite Ai. }
    apply proj2 in Ai. specialize_full Ai; [destruct len; try done; lia| ].
    destruct Ai as [ti Ai]. rewrite Ai in Ai'.   
    destruct (decide (NOnum (i + 1) = len)) eqn:EQ'.
    { right. left. subst. simpl in *. clear EQ'.
      apply not_iff_compat, proj2 in Ai'. specialize_full Ai'; [lia| ].
      apply eq_None_not_Some in Ai'. 
      rewrite /lookup /trace_lookup. rewrite Ai. destruct ti; eauto. congruence. }
    assert (NOmega.lt_nat_l (i + 1) len) as LT'.
    { destruct len; try done; simpl in *.
      destruct (decide (i + 1 < n0)); auto. destruct n. f_equal. lia. }
    left.
    apply proj2 in Ai'. specialize_full Ai'; auto. destruct Ai' as [ti' Ai']. 
    rewrite /lookup /trace_lookup. rewrite Ai. 
    destruct ti; simpl in *; eauto. congruence. 
  Qed. 

  Lemma trace_lookup_dom (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, is_Some (tr !! i) <-> NOmega.lt_nat_l i len.
  Proof using. 
    intros i. destruct (trace_lookup_trichotomy _ _ LEN i) as [LT | [EQ | GT]].
    - desc. rewrite LT. split; intros; auto.
      destruct len; simpl in *; try lia. 
    - desc. subst. rewrite EQ. split; simpl in *; intros; auto. lia. 
    - desc. split; intros.
      + rewrite GT in H. by destruct H.
      + destruct len; simpl in *; try lia. 
  Qed. 

  Lemma trace_lookup_dom_strong (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, (exists st ℓ st', tr !! i = Some (st, Some (ℓ, st'))) <-> NOmega.lt_nat_l (i + 1) len.
  Proof using. 
    intros i. destruct (trace_lookup_trichotomy _ _ LEN i) as [LT | [EQ | GT]].
    - desc. rewrite LT. split; intros; eauto. 
    - desc. subst. split; intros; desc.
      + congruence. 
      + simpl in *; lia.
    - desc. destruct len; try done; simpl in *. split; intros.
      + desc. congruence. 
      + lia. 
  Qed.

  Lemma trace_lookup_dom_eq (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, (exists st, tr !! i = Some (st, None)) <-> len = NOnum (i + 1). 
  Proof using.
    intros i. destruct (trace_lookup_trichotomy _ _ LEN i) as [LT | [EQ | GT]].
    - desc. subst. split; intros; desc.
      + congruence. 
      + subst. simpl in *; lia.
    - desc. split; intros; eauto.
    - desc. destruct len; try done; simpl in *. split; intros.
      + desc. congruence. 
      + inversion H. lia.
  Qed.

  Definition state_lookup (tr: trace St L) (i: nat): option St := 
    match tr !! i with
    | Some (st, _) => Some st
    | None => None
    end. 
    
  Definition label_lookup (tr: trace St L) (i: nat): option L := 
    match tr !! i with
    | Some (_, Some (ℓ, _)) => Some ℓ
    | _ => None
    end.

  Global Instance state_lookup_Lookup: 
    Lookup nat St (trace St L).
  intros i tr. exact (state_lookup tr i). 
  Defined. 

  Global Instance label_lookup_Lookup: 
    Lookup nat L (trace St L).
  intros i tr. exact (label_lookup tr i). 
  Defined.

  Notation "tr S!! i" := (state_lookup tr i) (at level 20). 
  Notation "tr L!! i" := (label_lookup tr i) (at level 20). 

  Lemma state_label_lookup (tr: trace St L):
    forall i st st' ℓ, 
      tr !! i = Some (st, Some (ℓ, st')) <->
      (tr S!! i = Some st /\ tr S!! (i + 1) = Some st' /\ tr L!! i = Some ℓ).
  Proof using. 
    intros. rewrite /state_lookup /label_lookup.
    rewrite /lookup /trace_lookup. rewrite after_sum'.
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
    rewrite /state_lookup. destruct (tr !! i) as [[x y] | ?]; try done.
    (* TODO: why it's not solved automatically? *)
    split; intros X; by destruct X. 
  Qed. 
  
  Lemma label_lookup_dom (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, is_Some (tr L!! i) <-> NOmega.lt_nat_l (i + 1) len.
  Proof using. 
    intros. rewrite /label_lookup.
    destruct (trace_lookup_trichotomy _ _ LEN i) as [LT | [EQ | GT]]; desc. 
    - rewrite LT. done.
    - subst. rewrite EQ. simpl. split; intros; [by inversion H|lia].
    - rewrite GT. split; intros; [by inversion H| ]. 
      destruct len; simpl in *; try done. lia. 
  Qed. 

  Lemma state_lookup_prev (tr: trace St L) i (DOM: is_Some (tr S!! i)):
    forall j (LE: j <= i), is_Some (tr S!! j). 
  Proof using. 
    intros. pose proof trace_has_len as [len ?].
    eapply state_lookup_dom in DOM; eauto.
    eapply state_lookup_dom; eauto. destruct len; eauto. simpl in *. lia. 
  Qed.  
    
  Lemma label_lookup_states (tr: trace St L):
    forall i, is_Some (tr L!! i) <-> is_Some (tr S!! i) /\ is_Some (tr S!! (i + 1)). 
  Proof using. 
    pose proof trace_has_len as [len ?].
    intros. etransitivity; [apply label_lookup_dom| ]; eauto.
    etransitivity; [symmetry; eapply state_lookup_dom| ]; eauto.
    split; try tauto. intros. split; auto. 
    eapply state_lookup_prev; eauto. lia.    
  Qed.     

  Lemma pred_at_trace_lookup (tr: trace St L) (i: nat) P:
      pred_at tr i P <-> exists st, tr S!! i = Some st /\ P st (tr L!! i). 
  Proof using.
    destruct (trace_has_len tr) as [len LEN].
    rewrite /state_lookup /label_lookup /lookup /trace_lookup.
    rewrite /pred_at. destruct (after i tr) eqn:Ai.
    2: { split; intros; try done. by destruct H as [? [[=] ?]]. }
    destruct t; split; intros; eauto; destruct H as [? [[=] ?]]; congruence.
  Qed. 


End TraceLen.

Notation "tr S!! i" := (state_lookup tr i) (at level 20). 
Notation "tr L!! i" := (label_lookup tr i) (at level 20). 
