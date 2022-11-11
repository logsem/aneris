From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.

Import derived_laws_later.bi.

(** Initial simple Fiarneris example *)

(** The simple model states *)
Inductive simple_state :=
| Start
| Sent (sent : nat)
| Delivered (sent : nat) (delivered : nat)
| Received (sent : nat) (delivered : nat).
#[global] Instance simple_state_eqdec : EqDecision simple_state.
Proof. solve_decision. Qed.
#[global] Instance simple_state_inhabited : Inhabited simple_state.
Proof. exact (populate Start). Qed.

Inductive simple_role := A | B | Ndup | Ndrop | Ndeliver.
#[global] Instance simple_role_eqdec : EqDecision simple_role.
Proof. solve_decision. Qed.
#[global] Instance simple_role_inhabited : Inhabited simple_role.
Proof. exact (populate A). Qed.
#[global] Instance simple_role_countable : Countable simple_role.
Proof.
  refine ({|
             encode s := match s with
                         | A => 1
                         | B => 2
                         | Ndup => 3
                         | Ndrop => 4
                         | Ndeliver => 5
                         end;
             decode n := match n with
                         | 1 => Some A
                         | 2 => Some B
                         | 3 => Some Ndup
                         | 4 => Some Ndrop
                         | 5 => Some Ndeliver
                         | _ => None
                         end;
         |})%positive.
  by intros [].
Qed.

Inductive simple_trans
  : simple_state → option simple_role → simple_state -> Prop :=
(* Transitions from Start *)
| Start_B_recv_fail_simple_trans : simple_trans Start (Some B) Start
| Start_A_send_simple_trans : simple_trans Start (Some A) (Sent 1)
(* Transitions from Sent *)
| Sent_B_recv_fail_simple_trans n : simple_trans (Sent n) (Some B) (Sent n)
| Sent_N_duplicate_simple_trans n : simple_trans (Sent $ S n) (Some Ndup) (Sent $ S $ S n)
| Sent_N_drop_simple_trans n : simple_trans (Sent $ S n) (Some Ndrop) (Sent n)
| Sent_N_deliver_simple_trans n : simple_trans (Sent $ S n) (Some Ndeliver) (Delivered n 1)
(* Transitions from Delivered *)
| Delivered_N_duplicate_simple_trans n m : simple_trans (Delivered (S n) m) (Some Ndup) (Delivered (S $ S n) m)
| Delivered_N_drop_simple_trans n m : simple_trans (Delivered (S n) m) (Some Ndrop) (Delivered n m)
| Delivered_N_deliver_simple_trans n m : simple_trans (Delivered (S n) m) (Some Ndeliver) (Delivered n (S m))
| Delivered_B_recv_succ_simple_trans n m : simple_trans (Delivered n m) (Some B) (Received n m)
(* Transitions from Received - Are these needed? *)
(* | Received_N_duplicate_simple_trans n m : simple_trans (Received n m) (Some Ndup) (Received (S n) m) *)
(* | Received_N_drop_simple_trans n m : simple_trans (Received (S n) m) (Some Ndrop) (Received n m) *)
(* | Received_N_deliver_simple_trans n m : simple_trans (Received (S n) m) (Some Ndeliver) (Received n (S m)) *)
.

Definition simple_live_roles (s : simple_state) : gset simple_role :=
  match s with
  | Start => {[A;B]}
  | Sent n => {[B;Ndup;Ndrop;Ndeliver]}
  (* Should Ndeliver etc. be live in Sent 0? *)
  | Delivered n m => {[B;Ndup;Ndrop;Ndeliver]}
  (* Is the network live in the last state? *)
  (* | Received n m => {[Ndup;Ndrop;Ndeliver]} *)
  | Received n m => ∅
  end.

Lemma simple_live_spec_holds s ρ s' :
  simple_trans s (Some ρ) s' -> ρ ∈ simple_live_roles s.
Proof. destruct s; inversion 1; set_solver. Qed.

Definition simple_fair_model : FairModel.
Proof.
  refine({|
            fmstate := simple_state;
            fmrole := simple_role;
            fmtrans := simple_trans;
            live_roles := simple_live_roles;
            fm_live_spec := simple_live_spec_holds;
          |}).
Defined.

Definition state_to_nat (s : simple_state) : nat :=
  match s with
  | Start => 3
  | Sent _ => 2
  | Delivered _ _ => 1
  | Received _ _ => 0
  end.

Definition simple_state_order (s1 s2 : simple_state) : Prop :=
  state_to_nat s1 ≤ state_to_nat s2.

Local Instance simple_state_order_preorder : PreOrder simple_state_order.
Proof.
  split.
  - by intros []; constructor.
  - intros [] [] []; rewrite /simple_state_order.
    all: intros Hc12 Hc23; try by inversion Hc12.
    all: rewrite /simple_state_order; try lia.
Qed.

Definition simple_decreasing_role (s : fmstate simple_fair_model) :
  fmrole simple_fair_model :=
  match s with
  | Start => A
  | Sent _ => Ndeliver
  | Delivered _ _ => B
  | Received _ _ => Ndeliver    (* Why is this needed? *)
  end.

#[local] Program Instance simple_model_terminates :
  FairTerminatingModel simple_fair_model :=
  {|
    ftm_leq := simple_state_order;
    ftm_decreasing_role := simple_decreasing_role;
  |}.
Next Obligation.
  rewrite /simple_state_order.
  intros []; repeat (constructor; intros [] []; simpl in *; try lia).
Qed.
Next Obligation.
  rewrite /simple_state_order.
  intros s [ρ' [s' Htrans]]=> /=.
  split.
  - destruct s; try set_solver. inversion Htrans.
  - intros s'' Htrans'. simpl in *.
    destruct s.
    + inversion Htrans'. split; simpl; lia.
    + inversion Htrans'. split; simpl; lia.
    + inversion Htrans'. split; simpl; lia.
    + inversion Htrans'.
Qed.
Next Obligation.
  intros s s' ρ Htrans Hρ. by destruct s; inversion Htrans.
Qed.
Next Obligation.
  rewrite /simple_state_order.
  intros s1 ρ s2 Htrans. destruct s1; inversion Htrans; simpl; lia.
Qed.
