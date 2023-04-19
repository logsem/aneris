(******************************************************************************)
(** * Natural numbers with infinity *)
(** An version of HahnOmega without HahnList import which somewhy breaks set_solver in subsequent proofs  *)
(** TODO: figure out the reason why *)
(******************************************************************************)

From hahn Require Import HahnBase. 
Require Import Arith micromega.Lia.

Set Implicit Arguments.

Inductive nat_omega := NOinfinity | NOnum (n: nat).

Module NOmega.

  Definition t := nat_omega.

  Definition zero := NOnum 0.

  Definition one := NOnum 1.

  Definition two := NOnum 2.

  Definition succ n :=
    match n with
    | NOinfinity => NOinfinity
    | NOnum n => NOnum (S n)
    end.

  Definition pred n :=
    match n with
    | NOinfinity => NOinfinity
    | NOnum n => NOnum (Nat.pred n)
    end.

  Definition add n m :=
    match n, m with
    | NOnum n, NOnum m => NOnum (n + m)
    | _, _ => NOinfinity
    end.

  Definition double n :=
    match n with
    | NOnum n => NOnum (Nat.double n)
    | _ => NOinfinity
    end.

  Definition sub n m :=
    match n, m with
    | NOnum n, NOnum m => NOnum (n - m)
    | NOnum n, NOinfinity => NOnum 0
    | NOinfinity, _ => NOinfinity
    end.

  Definition eqb n m :=
    match n, m with
    | NOnum n, NOnum m => Nat.eqb n m
    | NOinfinity, NOinfinity => true
    | _, _ => false
    end.

  Definition leb n m :=
    match n, m with
    | NOnum n, NOnum m => Nat.leb n m
    | NOnum n, NOinfinity => true
    | NOinfinity, _ => false
    end.

  Definition ltb n m :=
    match n, m with
    | NOnum n, NOnum m => Nat.ltb n m
    | NOnum n, NOinfinity => true
    | NOinfinity, _ => false
    end.

  Definition max n m :=
    match n, m with
    | NOnum n, NOnum m => NOnum (Nat.max n m)
    | _, _ => NOinfinity
    end.

  Definition min n m :=
    match n, m with
    | NOnum n, NOnum m => NOnum (Nat.min n m)
    | NOnum n, NOinfinity => NOnum n
    | NOinfinity, _ => m
    end.

  Definition le n m :=
    match n, m with
    | NOinfinity, _ => False
    | NOnum n, NOnum m => n <= m
    | NOnum n, NOinfinity => True
    end.

  Definition lt n m :=
    match n, m with
    | NOinfinity, _ => False
    | NOnum n, NOnum m => n < m
    | NOnum n, NOinfinity => True
    end.

  Definition lt_nat_l n m :=
    match m with
    | NOnum m => n < m
    | NOinfinity => True
    end.
  
  Definition sub_nat_l n m :=
    match m with
    | NOnum m => (n - m)
    | NOinfinity => 0
    end.

  Lemma pred_succ n : pred (succ n) = n.
  Proof. destruct n; ins. Qed.
  
  Lemma pred_0 : pred zero = zero.
  Proof. ins. Qed.


  Lemma add_0_l n : add zero n = n.
  Proof. destruct n; ins. Qed.

  Lemma add_0_r n : add n zero = n.
  Proof. destruct n; ins; auto using Nat.add_0_r. Qed.
  
  Lemma sub_0_r n : sub n zero = n.
  Proof. destruct n; ins; auto using Nat.sub_0_r. Qed.

  Definition lt_succ_r n m : lt n (succ m) <-> le n m.
  Proof.
    destruct n, m; ins; apply Nat.lt_succ_r.
  Qed.

  Lemma eqb_eq n m : eqb n m <-> n = m.
  Proof.
    destruct n, m; ins.
    split; ins; desf; f_equal; apply Nat.eqb_eq; ins.
  Qed.

  Lemma leb_le n m : leb n m <-> le n m.
  Proof.
    destruct n, m; ins; apply Nat.leb_le.
  Qed.

  Lemma ltb_lt n m : ltb n m <-> lt n m.
  Proof.
    destruct n, m; ins; apply Nat.ltb_lt.
  Qed.

  Lemma max_l n m : le m n -> max n m = n.
  Proof.
    destruct n, m; ins; f_equal; auto using Nat.max_l.
  Qed.
  
  Lemma max_r n m : le n m -> max n m = m.
  Proof.
    destruct n, m; ins; f_equal; auto using Nat.max_r.
  Qed.

  Lemma min_l n m : le n m -> min n m = n.
  Proof.
    destruct n, m; ins; f_equal; auto using Nat.min_l.
  Qed.
  
  Lemma min_r n m : le m n -> min n m = m.
  Proof.
    destruct n, m; ins; f_equal; auto using Nat.min_r.
  Qed.

  Lemma lt_irrefl x : ~ lt x x.
  Proof.
    destruct x; ins; lia.
  Qed.

(*  Lemma lt_eq_cases : forall n m : nat, n <= m <-> n < m \/ n = m. *)

  Lemma leb_spec x y : Bool.reflect (le x y) (leb x  y).
  Proof.
    generalize (leb_le x y); destruct leb; intuition.
  Qed.

  Lemma ltb_spec x y : Bool.reflect (lt x y) (ltb x  y).
  Proof.
    generalize (ltb_lt x y); destruct ltb; intuition.
  Qed.

  Lemma succ_inj n m : succ n = succ m -> n = m.
  Proof. destruct n, m; ins; desf. Qed.

  Lemma succ_inj_wd n m : succ n = succ m <-> n = m.
  Proof. split; destruct n, m; ins; desf. Qed.
    
  Lemma succ_inj_wd_neg n m : succ n <> succ m <-> n <> m.
  Proof. intuition; desf; rewrite succ_inj_wd in *; desf. Qed.

  Lemma add_succ_l n m : add (succ n) m = succ (add n m).
  Proof. destruct n, m; ins. Qed.

  Lemma add_succ_r n m : add n (succ m) = succ (add n m).
  Proof. destruct n, m; ins; rewrite Nat.add_succ_r; ins. Qed.

  Lemma add_succ_comm n m : add (succ n) m = add n (succ m).
  Proof. destruct n, m; ins; rewrite Nat.add_succ_r; ins. Qed.

  Lemma add_comm n m : add n m = add m n.
  Proof. destruct n, m; ins; rewrite Nat.add_comm; ins. Qed.

  Lemma add_1_l n : add one n = succ n.
  Proof. destruct n; ins. Qed.

  Lemma add_1_r n : add n one = succ n.
  Proof. rewrite add_comm, add_1_l; ins. Qed.

  Lemma add_assoc n m p : add n (add m p) = add (add n m) p.
  Proof. destruct n, m; ins; desf; auto using Nat.add_assoc. Qed.

  Lemma add_shuffle0 n m p : add (add n m) p = add (add n p) m.
  Proof. destruct n, m; ins; desf; ins; auto using Nat.add_shuffle0. Qed.

  Lemma add_shuffle1 n m p q :
    add (add n m) (add p q) = add (add n p) (add m q).
  Proof. destruct n, m, p; ins; desf; auto using Nat.add_shuffle1. Qed.

  Lemma add_shuffle2 n m p q :
    add (add n m) (add p q) = add (add n q) (add m p).
  Proof. destruct n, m, p; ins; desf; ins; auto using Nat.add_shuffle2. Qed.

  Lemma add_shuffle3 n m p : add n (add m p) = add m (add n p).
  Proof. destruct n, m; ins; desf; ins; auto using Nat.add_shuffle3. Qed.
    
  Lemma sub_1_r n : sub n one = pred n.
  Proof. destruct n; ins; auto using Nat.sub_1_r. Qed.

  Lemma le_wd :
    Morphisms.Proper
      (Morphisms.respectful Logic.eq (Morphisms.respectful Logic.eq iff))
      le.
  Proof.
    split; ins; desf.
  Qed.
    
  Lemma lt_le_incl n m : lt n m -> le n m.
  Proof. destruct n, m; ins; auto with arith. Qed.

  Lemma lt_trans n m p : lt n m -> lt m p -> lt n p.
  Proof. destruct n, m; ins; desf; eauto with arith. Qed.

  Lemma le_trans n m p : le n m -> le m p -> le n p.
  Proof. destruct n, m; ins; desf; eauto with arith. Qed.
  
  Lemma lt_strorder : RelationClasses.StrictOrder lt.
  Proof. constructor; repeat red; [apply lt_irrefl | apply lt_trans]. Qed.

  Definition lt_compat :
    Morphisms.Proper
      (Morphisms.respectful Logic.eq (Morphisms.respectful Logic.eq iff))
      lt.
  Proof. split; ins; desf. Qed.

  Lemma lt_lt_nat n m k :
    n < m -> NOmega.lt_nat_l m k -> NOmega.lt_nat_l n k.
  Proof.
    destruct k; ins; lia.
  Qed.

  Lemma le_lt_nat n m k :
    n <= m -> NOmega.lt_nat_l m k -> NOmega.lt_nat_l n k.
  Proof.
    destruct k; ins; lia.
  Qed.

End NOmega.

Global Hint Immediate NOmega.lt_lt_nat : hahn.
Global Hint Immediate NOmega.le_lt_nat : hahn.

