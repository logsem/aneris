From iris.proofmode Require Import tactics.
Require Import stdpp.decidable.
From trillium.fairness Require Import inftraces fairness. 
Require Import ClassicalFacts.
From Paco Require Import pacotac.


(* Taken from coq-hahn *)
Tactic Notation "specialize_full" ident(H) :=
  let foo := fresh in
  evar (foo : Prop); cut (foo); subst foo; cycle 1; [eapply H|try clear H; intro H].


Section NatOmega.
  (* Inspired by nat_omega type from coq-hahn library. *)
  (* Using hahn as is somewhy breaks the automation in our project,
     so we use a minimally sufficient part of it. *)
  Inductive nat_omega := NOinfinity | NOnum (n: nat).

  Definition nat_omega_lt_nat n m :=
    match m with
    | NOnum m => n < m
    | NOinfinity => True
    end.
  
  Definition nat_omega_lt n m :=
    match n, m with
    | NOinfinity, _ => False
    | NOnum n, NOnum m => n < m
    | NOnum n, NOinfinity => True
    end.

  Definition nat_omega_le n m :=
    match n, m with
    | NOinfinity, _ => False
    | NOnum n, NOnum m => n <= m
    | NOnum n, NOinfinity => True
    end.

  Global Instance NOmega_lt_le (x y: nat_omega):
    Decision (nat_omega_lt x y). 
  Proof using. 
    destruct x, y; simpl; solve_decision.
  Qed. 

  Global Instance nat_omega_eq_dec: EqDecision nat_omega.
  Proof using. solve_decision. Qed.

End NatOmega. 

Section TraceLength.
  Context {St L: Type}. 

  Definition trace_len_is (tr: trace St L) (len: nat_omega) :=
    forall (i: nat), is_Some (after i tr) <-> nat_omega_lt_nat i len.

  (* TODO: move somewhere else? *)
  Lemma min_prop_dec (P: nat -> Prop) (DEC: forall n, Decision (P n)):
    ClassicalFacts.Minimization_Property P.
  Proof using. 
    red. intros n Pn.    
    assert (forall p, p <= n + 1 -> ((∃ m, Minimal P m) \/ forall k, k < p -> ¬ P k)) as MIN'.
    2: { destruct (MIN' (n + 1)); eauto. edestruct H; eauto. lia. }    
    induction p.
    { intros. right. lia. }
    intros. destruct IHp; [lia| auto| ].
    rewrite Nat.add_1_r in H. apply le_S_n in H. 
    destruct (DEC p).
    - left. exists p. split; auto. intros.
      destruct (decide (p <= k)); auto.
      destruct (H0 k); auto. lia.
    - right. intros. destruct (decide (k = p)); [congruence| ].
      apply H0. lia.
  Qed.

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
      apply eq_None_not_Some in n0. specialize (MIN _ n0). lia.  
  Qed.  
  
End TraceLength. 


Section TraceLookup.
  Context {St L: Type}. 

  Global Instance trace_lookup:
    Lookup nat (St * option (L * St)) (trace St L) :=
    fun i tr => match after i tr with
             | None => None
             | Some ⟨ s ⟩ => Some (s, None)
             | Some (s -[ ℓ ]-> tr') => Some (s, Some (ℓ, trfirst tr'))
             end. 

  Global Instance state_lookup: Lookup nat St (trace St L) := 
    fun i tr => match tr !! i with
             | Some (st, _) => Some st
             | None => None
             end. 
    
  Global Instance label_lookup: Lookup nat L (trace St L) := 
    fun i tr => match tr !! i with
             | Some (_, Some (ℓ, _)) => Some ℓ
             | _ => None
             end.

  Notation "tr S!! i" := (state_lookup i tr) (at level 20). 
  Notation "tr L!! i" := (label_lookup i tr) (at level 20).

  Local Ltac unfold_lookups :=
    rewrite /state_lookup /label_lookup /lookup /trace_lookup.

  Lemma state_label_lookup (tr: trace St L):
    forall i st st' ℓ, 
      tr !! i = Some (st, Some (ℓ, st')) <->
      (tr S!! i = Some st /\ tr S!! (i + 1) = Some st' /\ tr L!! i = Some ℓ).
  Proof using. 
    intros. unfold_lookups.
    rewrite after_sum'.
    destruct (after i tr); simpl. 
    2: { split; [intros [=] | intros [[=] ?]]. }
    destruct t; auto.
    { split; [intros [=] | intros [_ [[=] _]]]. }
    simpl. split; intros.
    - inversion H. subst. split; auto. destruct t; auto. 
    - destruct t; destruct H as ([=] & [=] & [=]); subst; auto. 
  Qed.

  Section LookupWithLen.
    Context (tr: trace St L).
    Context {len: nat_omega} (LEN: trace_len_is tr len). 

    Lemma trace_lookup_trichotomy:
      forall i, 
        (exists st ℓ st', tr !! i = Some (st, Some (ℓ, st')) /\
                       nat_omega_lt_nat (i + 1) len) \/
          (exists st, tr !! i = Some (st, None) /\ len = NOnum (i + 1)) \/
          (tr !! i = (None: option (_ * _)) /\
           nat_omega_le len (NOnum i)). 
    Proof using LEN.
      intros.
      pose proof (LEN i) as Ai. pose proof (LEN (i + 1)) as Ai'.
      rewrite after_sum' in Ai'. 
      destruct (NOmega_lt_le (NOnum i) len).
      2: { right. right. apply not_iff_compat, proj2 in Ai, Ai'.
           destruct len; simpl in *; try done.  
           specialize_full Ai; [lia| ]. specialize_full Ai'; [lia| ].
           split; [| lia].
           apply eq_None_not_Some in Ai.
           unfold_lookups. by rewrite Ai. }
      apply proj2 in Ai. specialize_full Ai; [destruct len; try done; lia| ].
      destruct Ai as [ti Ai]. rewrite Ai in Ai'.   
      destruct (decide (NOnum (i + 1) = len)) eqn:EQ'.
      { right. left. subst. simpl in *. clear EQ'.
        apply not_iff_compat, proj2 in Ai'. specialize_full Ai'; [lia| ].
        apply eq_None_not_Some in Ai'. 
        unfold_lookups. rewrite Ai. destruct ti; eauto. congruence. }
      assert (nat_omega_lt_nat (i + 1) len) as LT'.
      { destruct len; try done; simpl in *.
        destruct (decide (i + 1 < n1)); auto. destruct n0. f_equal. lia. }
      left.
      apply proj2 in Ai'. specialize_full Ai'; auto. destruct Ai' as [ti' Ai'].
      unfold_lookups. rewrite Ai. 
      destruct ti; simpl in *; eauto. congruence. 
    Qed.

    Local Ltac lia_no no := destruct no; simpl in *; lia.  

    Lemma trace_lookup_dom:
      forall i, is_Some (tr !! i: option (_ * _)) <-> nat_omega_lt_nat i len.
    Proof using LEN. 
      intros i. 
      destruct (trace_lookup_trichotomy i) as [CMP | [CMP | CMP]]. 
      - repeat destruct CMP as [? CMP].
        split; [lia_no len| eauto].
      - destruct CMP as [? [? ->]]. simpl. 
        split; [lia | eauto]. 
      - destruct CMP as [-> ?].
        split; try lia_no len. by intros ?%is_Some_None. 
    Qed.

    Lemma trace_lookup_dom_full:
      forall i, (exists st ℓ st', tr !! i = Some (st, Some (ℓ, st'))) <-> nat_omega_lt_nat (i + 1) len.
    Proof using LEN. 
      intros i. destruct (trace_lookup_trichotomy i) as [LT | [EQ | GT]].
      - repeat destruct LT as [? LT]. split; eauto. 
      - destruct EQ as [? [-> ->]]. simpl. split; [intros (?&?&?&[=]) | lia]. 
      - destruct GT as [-> ?].
        split; [intros (?&?&?&[=]) | lia_no len]. 
    Qed.

    Lemma trace_lookup_dom_eq:
      forall i, (exists st, tr !! i = Some (st, None)) <-> len = NOnum (i + 1). 
    Proof using LEN. 
      intros i. destruct (trace_lookup_trichotomy i) as [LT | [EQ | GT]].
      - repeat destruct LT as [? LT].
        split; [intros [? ?]; congruence| ].
        intros ->. simpl in LT. lia. 
      - destruct EQ as [? [-> ->]]. simpl. split; eauto.
      - destruct GT as [-> LE].
        split; [by intros [? ?]| ].
        intros ->. simpl in LE. lia.  
    Qed.
    
    Lemma state_lookup_dom:
      forall i, is_Some (tr S!! i) <-> nat_omega_lt_nat i len.
    Proof using LEN. 
      intros. etransitivity; [| apply trace_lookup_dom]; eauto.
      rewrite /state_lookup.
      destruct (tr !! i: option (_ * _)) as [[? ?] | ]; try (done || eauto).
      (* TODO: why it's not solved automatically? *)
      split; intros X; by destruct X. 
    Qed. 
  
    Lemma label_lookup_dom:
      forall i, is_Some (tr L!! i) <-> nat_omega_lt_nat (i + 1) len.
    Proof using LEN. 
      intros. rewrite /label_lookup.
      destruct (trace_lookup_trichotomy i) as [LT | [EQ | GT]].
      - repeat destruct LT as [? LT].
        by rewrite H. 
      - subst. destruct EQ as [? [-> ->]]. simpl. 
        split; intros; [by inversion H | lia].
      - destruct GT as [-> LE]. split; intros; [by inversion H| ]. 
        destruct len; simpl in *; try done. lia. 
    Qed.

  End LookupWithLen.


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
    unfold_lookups. 
    rewrite /pred_at. destruct (after i tr) eqn:Ai.
    2: { split; intros; try done. by destruct H as [? [[=] ?]]. }
    destruct t; split; intros; eauto; destruct H as [? [[=] ?]]; congruence.
  Qed. 

End TraceLookup. 


Notation "tr S!! i" := (state_lookup i tr) (at level 20). 
Notation "tr L!! i" := (label_lookup i tr) (at level 20).


Section MtraceLookup.
  Context {M} (tr: mtrace M).

  Section ValidMtraceLookup.
    Context (VALID: mtrace_valid tr).

    Local Ltac gd t := generalize dependent t.

    Lemma mtrace_valid_step i st ℓ st'
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
    
    Lemma mtrace_valid_step' i st ℓ st'
      (ST1: tr S!! i = Some st)
      (ST2: tr S!! (i + 1) = Some st')
      (LBL: tr L!! i = Some ℓ):
      fmtrans _ st ℓ st'. 
    Proof using VALID.
      eapply mtrace_valid_step.
      apply state_label_lookup. eauto.
    Qed. 

  End ValidMtraceLookup.

End MtraceLookup.

