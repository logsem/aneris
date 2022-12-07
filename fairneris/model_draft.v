From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness Require Import fair_termination.

Import derived_laws_later.bi.

(** Initial simple Fairneris example *)

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

Inductive simple_role := A_role | B_role | Ndup | Ndrop | Ndeliver.
#[global] Instance simple_role_eqdec : EqDecision simple_role.
Proof. solve_decision. Qed.
#[global] Instance simple_role_inhabited : Inhabited simple_role.
Proof. exact (populate A_role). Qed.
#[global] Instance simple_role_countable : Countable simple_role.
Proof.
  refine ({|
             encode s := match s with
                         | A_role => 1
                         | B_role => 2
                         | Ndup => 3
                         | Ndrop => 4
                         | Ndeliver => 5
                         end;
             decode n := match n with
                         | 1 => Some A_role
                         | 2 => Some B_role
                         | 3 => Some Ndup
                         | 4 => Some Ndrop
                         | 5 => Some Ndeliver
                         | _ => None
                         end;
         |})%positive.
  by intros [].
Qed.

Inductive simple_trans
  : simple_state → simple_role → simple_state → Prop :=
(* Transitions from Start *)
| Start_B_recv_fail_simple_trans : simple_trans Start B_role Start
| Start_A_send_simple_trans : simple_trans Start A_role (Sent 1)
(* Transitions from Sent *)
| Sent_B_recv_fail_simple_trans n : simple_trans (Sent n) B_role (Sent n)
| Sent_N_duplicate_simple_trans n : simple_trans (Sent $ S n) Ndup (Sent $ S $ S n)
| Sent_N_drop_simple_trans n : simple_trans (Sent $ S n) Ndrop (Sent n)
| Sent_N_deliver_simple_trans n : simple_trans (Sent $ S n) Ndeliver (Delivered n 0)
(* Transitions from Delivered *)
| Delivered_N_duplicate_simple_trans n m : simple_trans (Delivered (S n) m) Ndup (Delivered (S $ S n) m)
| Delivered_N_drop_simple_trans n m : simple_trans (Delivered (S n) m) Ndrop (Delivered n m)
| Delivered_N_deliver_simple_trans n m : simple_trans (Delivered (S n) m) Ndeliver (Delivered n (S m))
| Delivered_B_recv_succ_simple_trans n m : simple_trans (Delivered n m) B_role (Received n m)
(* Transitions from Received - Are these needed? *)
| Received_N_duplicate_simple_trans n m : simple_trans (Received (S n) m) Ndup (Received (S $ S n) m)
| Received_N_drop_simple_trans n m : simple_trans (Received (S n) m) Ndrop (Received n m)
| Received_N_deliver_simple_trans n m : simple_trans (Received (S n) m) Ndeliver (Received n (S m))
.

Definition simple_live_roles (s : simple_state) : gset simple_role :=
  match s with
  | Start => {[A_role;B_role]}
  | Sent 0 => {[B_role]}
  | Sent n => {[B_role;Ndup;Ndrop;Ndeliver]}
  (* Should Ndeliver etc. be live in Sent 0? *)
  | Delivered 0 m => {[B_role]}
  | Delivered n m => {[B_role;Ndup;Ndrop;Ndeliver]}
  (* Is the network live in the last state? *)
  | Received 0 m => ∅
  | Received n m => {[Ndup;Ndrop;Ndeliver]}
  end.

Lemma simple_live_spec_holds s ρ s' :
  simple_trans s ρ s' -> ρ ∈ simple_live_roles s.
Proof. destruct s; inversion 1; try set_solver; destruct sent; set_solver. Qed.

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

(* (** Fair Model construction (currently does not work, as the config roles
do not terminate) *) *)

(* Definition state_to_nat (s : simple_state) : nat := *)
(*   match s with *)
(*   | Start => 3 *)
(*   | Sent _ => 2 *)
(*   | Delivered _ _ => 1 *)
(*   | Received _ _ => 0 *)
(*   end. *)

(* Definition simple_state_order (s1 s2 : simple_state) : Prop := *)
(*   state_to_nat s1 ≤ state_to_nat s2. *)

(* Local Instance simple_state_order_preorder : PreOrder simple_state_order. *)
(* Proof. *)
(*   split. *)
(*   - by intros []; constructor. *)
(*   - intros [] [] []; rewrite /simple_state_order. *)
(*     all: intros Hc12 Hc23; try by inversion Hc12. *)
(*     all: rewrite /simple_state_order; try lia. *)
(* Qed. *)

(* Definition simple_decreasing_role (s : fmstate simple_fair_model) : *)
(*   fmrole simple_fair_model := *)
(*   match s with *)
(*   | Start => A_role *)
(*   | Sent _ => Ndeliver *)
(*   | Delivered _ _ => B_role *)
(*   | Received _ _ => Ndeliver    (* Why is this needed? *) *)
(*   end. *)

(* #[local] Program Instance simple_model_terminates : *)
(*   FairTerminatingModel simple_fair_model := *)
(*   {| *)
(*     ftm_leq := simple_state_order; *)
(*     ftm_decreasing_role := simple_decreasing_role; *)
(*   |}. *)
(* Next Obligation. *)
(*   rewrite /simple_state_order. *)
(*   intros []; repeat (constructor; intros [] []; simpl in *; try lia). *)
(* Qed. *)
(* Next Obligation. *)
(*   rewrite /simple_state_order. *)
(*   intros s [ρ' [s' Htrans]]=> /=. *)
(*   split. *)
(*   - destruct s; try set_solver. *)
(*   - intros s'' Htrans'. simpl in *. *)
(*     destruct s. *)
(*     + inversion Htrans'. split; simpl; lia. *)
(*     + inversion Htrans'. split; simpl; lia. *)
(*     + inversion Htrans'. split; simpl; lia. *)
(*     + inversion Htrans'. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros s s' ρ Htrans Hρ. by destruct s; inversion Htrans. *)
(* Qed. *)
(* Next Obligation. *)
(*   rewrite /simple_state_order. *)
(*   intros s1 ρ s2 Htrans. destruct s1; inversion Htrans; simpl; lia. *)
(* Qed. *)
