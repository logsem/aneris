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
From trillium.fairness.examples.ticketlock Require Export lemmas.

Section TraceLen.
  From hahn Require Import HahnBase.
  From hahn Require Import HahnOmega.

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

  Lemma trace_lookup_len_strong (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, (exists st ℓ st', tr !! i = Some (st, Some (ℓ, st'))) <-> NOmega.lt_nat_l (i + 1) len.
  Proof using. 
    intros. etransitivity.
    2: { apply LEN. }
    rewrite /lookup /trace_lookup. 
    rewrite after_sum'. destruct (after i tr).
    2: { split; intros; desc; try done. by destruct H. }
    destruct t.
    { split; intros; desc; try done. by destruct H. }
    split; intros; desc; eauto. 
  Qed. 

  (* TODO: impossible to reuse previous proof? *)
  Lemma trace_lookup_len (tr: trace St L) (len: nat_omega)
    (LEN: trace_len_is tr len):
    forall i, is_Some (tr !! i) <-> NOmega.lt_nat_l i len.
  Proof using. 
    intros. etransitivity.
    2: { apply LEN. }
    rewrite /lookup /trace_lookup. 
    destruct (after i tr).
    2: { split; intros; desc; by destruct H. }
    destruct t.
    { split; intros; desc; done. }
    split; intros; desc; eauto.
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

  Notation "tr S!! i" := (state_lookup tr i) (at level 20). 
  Notation "tr L!! i" := (label_lookup tr i) (at level 20). 

  Lemma state_label_lookup (tr: trace St L) (len: nat_omega):
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
    
  (* Definition len_of_tr: nat_omega. *)
  (*   destruct (excluded_middle_informative (terminating_trace tr)). *)
  (*   2: { exact NOinfinity. } *)
  (*   red in t. apply constructive_indefinite_description in t as [n N]. *)
  (*   exact (NOnum n). *)
  (* Defined. *)

  (* CoFixpoint trace_length (tr: trace St L): nat_omega := *)
  (*   match tr with *)
  (*   | tr_singl _ => NOnum 1 *)
  (*   | tr_cons _ _ tr' => NOmega.add (NOnum 1) (trace_length tr') *)
  (*   end.  *)

End TraceLen.
