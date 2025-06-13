Require Import ClassicalFacts.
Require Import Lia.
From stdpp Require Import base option.

(* TODO: find existing? *)
Section LogicHelpers.

  Lemma ex2_comm {A B: Type} (P: A -> B -> Prop):
    (exists (a: A) (b: B), P a b) <-> (exists (b: B) (a: A), P a b).
  Proof. 
    split; intros (?&?&?); eauto. 
  Qed. 

  Lemma iff_and_impl_helper {A B: Prop} (AB: A -> B):
    A /\ B <-> A.
  Proof. tauto. Qed.     

  Lemma iff_True_helper {A: Prop}:
    (A <-> True) <-> A.
  Proof. tauto. Qed.     

  Lemma iff_False_helper {A: Prop}:
    (A <-> False) <-> not A.
  Proof. tauto. Qed.

  Lemma ex_and_comm {T: Type} (A: Prop) (B: T -> Prop):
    (exists t, A /\ B t) <-> A /\ exists t, B t.
  Proof. split; intros (?&?&?); eauto. Qed.

  Lemma ex_prod {A B: Type} (P: A * B -> Prop):
    (exists ab, P ab) <-> (exists a b, P (a, b)).
  Proof.
    split.
    - intros [[??] ?]. eauto.
    - intros (?&?&?). eauto.
  Qed. 

  Lemma ex_prod' {A B: Type} (P: A -> B -> Prop):
    (exists a b, P a b) <-> (exists ab, P (fst ab) (snd ab)).
  Proof.
    split.
    - intros (?&?&?). eexists (_, _). eauto.
    - intros [[??] ?]. eauto.
  Qed.

  Lemma ex_proper3 {A B C: Prop} (P Q: A -> B -> C -> Prop)
    (EQUIV: forall a b c, P a b c <-> Q a b c):
    (exists a b c, P a b c) <-> (exists a b c, Q a b c).
  Proof.
    split; intros (?&?&?&?); do 3 eexists; apply EQUIV; eauto. 
  Qed. 

  Lemma ex_det_iff {A: Type} (P: A -> Prop) a
    (DET: forall a', P a' -> a' = a):
    (exists a', P a') <-> P a.
  Proof. 
    split; [| eauto].
    intros [? ?]. erewrite <- DET; eauto.
  Qed. 

  Lemma iff_and_pre {A B C: Prop}
    (BC: A -> (B <-> C)):
    A /\ B <-> A /\ C.
  Proof using. tauto. Qed.

  Lemma curry_uncurry_prop {A B C: Prop}:
    (A -> B -> C) <-> (A /\ B -> C).
  Proof. tauto. Qed. 

  Lemma forall_eq_gen {A: Type} (P: A -> Prop):
    forall a, P a <-> (forall a', a' = a -> P a').
  Proof.
    split; eauto.
    intros ?? ->. eauto.
  Qed.

  Lemma exist_impl_forall {A: Type} {P: A -> Prop} {Q: Prop}:
    ((exists x, P x) -> Q) <-> (forall x, P x -> Q).
  Proof using.
    split.
    - intros PQ x Px. eauto.
    - intros PQ [x Px]. eauto.
  Qed. 

  Lemma forall_prod_helper {A B: Type} (P: A -> B -> Prop):
    (forall a b, P a b) <-> (forall ab: A * B, P (fst ab) (snd ab)).
  Proof.
    split; eauto. intros PP ??.
    apply (PP (a, b)).
  Qed.    
  
  Lemma impl_iff_intro {A B C: Prop}
    (PRE: A -> B <-> C):
    (A -> B) <-> (A -> C).
  Proof using. tauto. Qed.

End LogicHelpers.


Lemma min_prop_dec_impl (P: nat -> Prop) (DEC: forall n, Decision (P n)):
  forall n, P n -> {m | Minimal P m}.
Proof.
  intros n Pn.

  assert (forall p, p <= n + 1 -> ({m | Minimal P m} + {forall k, k < p -> ¬ P k})) as MIN'.
  2: { destruct (MIN' (n + 1)); eauto. edestruct n0; eauto. lia. }

  induction p.
  { intros. right. lia. }
  intros. destruct IHp; [lia| auto| ].
  rewrite PeanoNat.Nat.add_1_r in H. apply le_S_n in H. 
  destruct (DEC p).
  - left. exists p. split; auto. intros.
    destruct (PeanoNat.Nat.le_decidable p k); auto.
    destruct (n0 k); auto. lia.
  - right. intros. destruct (PeanoNat.Nat.eq_decidable k p); [congruence| ].
    apply n0. lia.
Qed. 

Lemma min_prop_dec (P: nat -> Prop) (DEC: forall n, Decision (P n)):
  ClassicalFacts.Minimization_Property P.
Proof using.
  red. intros ? Pn.
  edestruct (min_prop_dec_impl _ _ _ Pn). eauto.  
Qed.

Global Instance Minimal_proper: 
  Proper (pointwise_relation nat iff ==> eq ==> iff) ClassicalFacts.Minimal.
Proof using.
  red. red. intros. red. intros. subst. red in H. 
  split; intros [P MIN].
  all: split; [| intros; apply MIN]; apply H; auto.
Qed. 

Definition Minimal_pos (P: BinNums.positive → Prop) (n : BinNums.positive) :=
  P n ∧ (∀ k, P k → BinPos.Pos.le n k). 

Lemma min_prop_dec_impl_pos (P: BinNums.positive -> Prop) (DEC: forall n, Decision (P n)):
  ∀ n, P n → {m: BinNums.positive | Minimal_pos P m }.
Proof.
  intros n Pn.
  epose proof (min_prop_dec_impl (P ∘ BinPos.Pos.of_nat) _ (BinPos.Pos.to_nat n)) as [m [Pm MINm]].
  { red. rewrite Pnat.Pos2Nat.id. auto. }
  exists (BinPos.Pos.of_nat m). split; auto.
  intros.
  specialize (MINm (BinPos.Pos.to_nat k) ltac:(red; rewrite Pnat.Pos2Nat.id; eauto)).
  lia. 
Qed.


(* TODO: already exists somewhere? *)
Lemma Decision_iff_impl (P Q: Prop) (PQ: P <-> Q) (DEC_P: Decision P):
  Decision Q. 
Proof using. 
  destruct DEC_P; [left | right]; tauto. 
Qed.  

Instance ex_fin_dec {T: Type} (P: T -> Prop) (l: list T)
  (DEC: forall a, Decision (P a))
  (IN: forall a, P a -> In a l):
  Decision (exists a, P a).
Proof.
  destruct (Exists_dec P l) as [EX|NEX].
  { eauto. }
  - left. apply List.Exists_exists in EX as (?&?&?). eauto.
  - right. intros [a Pa]. apply NEX.
    apply List.Exists_exists. eexists. split; eauto.
Qed. 

(** useful for rewriting in equivalences *)
Lemma is_Some_Some_True {A: Type} (a: A):
  is_Some (Some a) <-> True.
Proof. done. Qed. 

(** useful for rewriting in equivalences *)
Lemma is_Some_None_False {A: Type}:
  is_Some (None: option A) <-> False.
Proof.
  split; [| done]. by intros []. 
Qed. 
