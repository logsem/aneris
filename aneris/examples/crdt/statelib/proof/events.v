From stdpp Require Import base countable.
From aneris.aneris_lang Require Import lang.
From aneris.prelude Require Import time.
From aneris.examples.crdt.spec Require Import crdt_time crdt_events.
From aneris.examples.crdt.statelib.proof Require Import time.

(** * Instantiation of Statelib events *)
(* Section Events. *)

(*   Context `{!Log_Op LogOp}. *)

(*   Record StLibEvent := { *)
(*     ev_op : LogOp; *)
(*     ev_orig : RepId; *)
(*     ev_seqid : SeqNum; *)
(*     (* valid events should include themselves as dependencies *) *)
(*     ev_deps : Timestamp; *)
(*   }. *)

(*   Global Instance oplib_event_eqdec : EqDecision StLibEvent. *)
(*   Proof. solve_decision. Defined. *)

(*   Global Instance oplib_event_countable : Countable StLibEvent. *)
(*   Proof. *)
(*     (* *)
(*     refine {| *)
(*       encode ev := encode (ev.(ev_op), ev.(ev_orig), ev.(ev_vc)); *)
(*       decode n := (λ tr, match tr with *)
(*                          | (op, orig, vc) => Build_OpLibEvent op orig vc *)
(*                          end)  <$> *)
(*                    @decode (LogOp * nat * vector_clock) _ _ n; *)
(*       |}. *)
(*     intros []. rewrite /= decode_encode /=. done. *)
(*   Qed. *) *)
(*   Admitted. *)

(*   Global Instance oplib_event_timed : Timed StLibEvent := { time := ev_deps }. *)

(*   Global Instance OpLibEvent_LogEvents : Log_Events LogOp := { *)
(*     Event := OpLibEvent; *)
(*     EV_Op := ev_op; *)
(*     EV_Orig := ev_orig; *)
(*   }. *)

(* End Events. *)

(* Arguments OpLibEvent : clear implicits. *)

(* Section ComputeMaximals. *)

(*   Context `{!Log_Op LogOp}. *)

(*   (* *)
(*   Global Instance maximals_computing : Maximals_Computing (OpLibEvent LogOp). *)
(*   Proof. *)
(*     refine {| Maximals := compute_maximals ev_vc; *)
(*               Maximum := compute_maximum ev_vc; |}. *)
(*     - apply (compute_maximals_correct (@ev_vc LogOp)). *)
(*     - apply compute_maximum_correct. *)
(*   Qed. *)
(*   *) *)

(* End ComputeMaximals. *)
