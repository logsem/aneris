From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From fairneris Require Import fairness.
From Paco Require Import pacotac.

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

Definition fair_network_mtr (mtr : trace simple_state simple_role) :=
  ∀ n, pred_at mtr n (λ _ ℓ, ℓ ≠ Some Ndup ∧ ℓ ≠ Some Ndrop).

Lemma fair_network_mtr_after mtr mtr' k :
  after k mtr = Some mtr' →
  fair_network_mtr mtr →
  fair_network_mtr mtr'.
Proof.
  rewrite /fair_network_mtr.
  intros Hafter Hfair.
  intros n.
  specialize (Hfair (k+n)).
  rewrite pred_at_sum in Hfair.
  rewrite Hafter in Hfair.
  done.
Qed.

Definition simple_fair_model : FairModel.
Proof.
  refine({|
            fmstate := simple_state;
            fmrole := simple_role;
            fmtrans := simple_trans;
            fmfairness := fair_network_mtr;
            fmfairness_preserved := fair_network_mtr_after;
            live_roles := simple_live_roles;
            fm_live_spec := simple_live_spec_holds;
          |}).
Defined.

(** Fair Model construction (currently does not work, as the config roles
do not terminate) *)

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
  | Start => A_role
  | Sent _ => Ndeliver
  | Delivered _ _ => B_role
  | Received _ _ => Ndup    (* Why is this needed? *)
  end.

(** Included redefinition of FairTerminatingModel here for now *)
Class FairTerminatingModel (Mdl: FairModel) := {
  ftm_leq: relation (Mdl.(fmstate));
  ftm_order: PreOrder ftm_leq;
  ftm_wf: wf (strict ftm_leq);

  ftm_decreasing_role: fmstate Mdl → fmrole Mdl;
  ftm_reachable_state: fmstate Mdl → Prop;

  ftm_reachable: ∀ mtr, pred_at mtr 0 (λ ρ _, ftm_reachable_state ρ) →
                        mtrace_valid mtr → mtrace_fair mtr →
                        ∀ n, pred_at mtr n (λ _ _, True) →
                             pred_at mtr n (λ δ _, ftm_reachable_state δ);
  ftm_decr:
    ∀ (s: fmstate Mdl), ftm_reachable_state s →
                (∃ ρ' s', fmtrans _ s ρ' s') →
                ftm_decreasing_role s ∈ live_roles _ s ∧
                ∀ s', (fmtrans _ s (ftm_decreasing_role s) s' →
                       (strict ftm_leq) s' s);
  ftm_decreasing_role_preserved:
    ∀ (s s': fmstate Mdl) ρ',
      ftm_reachable_state s →
      fmtrans _ s ρ' s' → ρ' ≠ ftm_decreasing_role s →
      ftm_decreasing_role s = ftm_decreasing_role s';
  ftm_notinc:
    ∀ (s: fmstate Mdl) ρ s', ftm_reachable_state s → fmtrans _ s ρ s' → ftm_leq s' s;
}.

Arguments ftm_leq {_ _}.
Arguments ftm_wf {_ _}.
Arguments ftm_reachable_state {_ _}.
Arguments ftm_reachable {_ _}.
Arguments ftm_decr {_ _}.
Arguments ftm_decreasing_role {_ _}.

#[global] Existing Instance ftm_order.

Notation ftm_lt := (strict ftm_leq).
Local Infix "<" := ftm_lt.
Local Infix "≤" := ftm_leq.

Lemma ftm_trans' `{FairTerminatingModel Mdl} a b c:
  a < b → b ≤ c → a < c.
Proof.
  intros [H1 H1'] H2.
  (* TODO: Why do we need to extract this manually? *)
  (* assert (EqDecision Mdl) by apply Mdl.(fmstate_eqdec). *)
  destruct (decide (b = c)) as [->|Heq]; [done|].
  split; [by etransitivity|].
  intros H'. apply H1'.
  by etransitivity.
Qed.

Definition initial_reachable `{FairTerminatingModel M} (mtr : mtrace M) :=
  pred_at mtr 0 (λ ρ _, ftm_reachable_state ρ).

Lemma fair_terminating_traces_terminate_rec `{FairTerminatingModel Mdl}
      (s0: fmstate Mdl) (mtr: mtrace Mdl):
  (trfirst mtr) ≤ s0 →
  initial_reachable mtr →
  mtrace_valid mtr →
  mtrace_fair mtr →
  terminating_trace mtr.
Proof.
  revert mtr. induction s0 as [s0 IH] using (well_founded_ind ftm_wf).
  intros mtr Hleq Hinit Hval Hfair.
  pose proof (ftm_reachable mtr Hinit Hval Hfair) as Hexcl.
  destruct mtr as [|s ℓ mtr'] eqn:Heq; first by eexists 1.
  destruct (ftm_decr (trfirst mtr)) as (Hlive & Htrdec).
  { pose proof (Hexcl 0) as Hexcl0%pred_at_0; [|done]. by simplify_eq. }
  { exists ℓ, (trfirst mtr'). punfold Hval. inversion Hval; subst; done. }
  rewrite <- Heq in *. clear s ℓ Heq.
  pose proof Hfair as [Hfair_scheduling _].
  destruct (Hfair_scheduling (ftm_decreasing_role (trfirst mtr)) 0) as [n Hev];
    first by rewrite /pred_at /=; destruct mtr.
  clear Hfair_scheduling.
  revert mtr Hexcl Hinit Hval Hleq Hfair Hlive IH Hev Htrdec. induction n as [| n IHn];
    intros mtr Hexcl Hinit Hval Hleq Hfair Hlive IH Hev Htrdec.
  - simpl in *. rewrite pred_at_or in Hev. rewrite /pred_at /= in Hev.
    destruct Hev as [Hev|Hev]; first by destruct mtr; done.
    destruct mtr; first done. injection Hev => ->.
    apply terminating_trace_cons.
    eapply IH =>//; eauto.
    + eapply ftm_trans' =>//. apply Htrdec.
      punfold Hval. inversion Hval; simplify_eq; simpl in *; simplify_eq; done.
    + apply (Hexcl 1). apply pred_at_S. by destruct mtr.
    + punfold Hval. inversion Hval; simplify_eq.
      destruct H4; done.
    + destruct Hfair as [Hscheduling Hfair].
      split.
      * intros ρ. by eapply fair_scheduling_mtr_cons.
      * eapply (fmfairness_preserved _ _ _ 1); [|apply Hfair]. done.
  - simpl in *. destruct mtr; first (exists 1; done).
    rewrite -> !pred_at_S in Hev.
    punfold Hval; inversion Hval as [|??? Htrans Hval']; simplify_eq.
    destruct Hval' as [Hval'|]; last done.
    destruct (decide (ℓ = ftm_decreasing_role s)) as [-> | Hnoteq].
    + apply terminating_trace_cons. eapply IH=>//; eauto.
      eapply ftm_trans' =>//; apply Htrdec. simpl. destruct Hval; done.
      * apply (Hexcl 1). apply pred_at_S. by destruct mtr.
      * destruct Hfair as [Hscheduling Hfair].
        split.
        -- intros ρ. by eapply fair_scheduling_mtr_cons.
        -- eapply (fmfairness_preserved _ _ _ 1); [|apply Hfair]. done.
    + destruct mtr as [|s' ℓ' mtr''] eqn:Heq; first by eexists 2.
      destruct (ftm_decr (trfirst mtr)) as (Hlive' & Htrdec').
      { pose proof (Hexcl 1) as Hexcl0%pred_at_0; [|done]. by simplify_eq. }
      { exists ℓ', (trfirst mtr''). punfold Hval'; inversion Hval'; subst; done. }
      apply terminating_trace_cons. eapply IHn=>//; eauto.
      * apply ftm_reachable; [|apply Hval'|].
        -- apply (Hexcl 1). apply pred_at_S, pred_at_0. done.
        -- split.
           ++ intros ρ. eapply (fair_scheduling_mtr_after _ _ _ 1); [|apply Hfair]. done.
           ++ eapply (fmfairness_preserved _ _ _ 1); [|apply Hfair]. done.
      * apply (Hexcl 1). apply pred_at_S, pred_at_0. done.
      * etransitivity; eauto. eapply ftm_notinc =>//.
      * destruct Hfair as [Hscheduling Hfair].
        split.
       -- intros ρ. by eapply fair_scheduling_mtr_cons.
       -- eapply (fmfairness_preserved _ _ _ 1); [|apply Hfair]. done.
      * simplify_eq. eapply Hlive'.
      * erewrite <- ftm_decreasing_role_preserved =>//.
      * intros s'' Htrans''. eapply ftm_decr; eauto.
        by pose proof (Hexcl 1) as Hexcl0%pred_at_0.
Qed.

Definition mtrace_fairly_terminating (mtr : mtrace simple_fair_model) :=
  mtrace_valid mtr →
  mtrace_fair mtr →
  (* This needs to be strengthened to consider config steps *)
  terminating_trace mtr.

Theorem fair_terminating_traces_terminate `{FairTerminatingModel simple_fair_model} :
  ∀ (mtrace : @mtrace simple_fair_model),
  initial_reachable mtrace →
  mtrace_fairly_terminating mtrace.
Proof. intros ???[??]. eapply fair_terminating_traces_terminate_rec=>//. Qed.

Definition simple_reachable_state s :=
  match s with
  | Sent 1 => True
  | Sent _ => False
  | Delivered 0 0 => True
  | Delivered _ _ => False
  | Received 0 0 => True
  | Received _ _ => False
  | _ => True
  end.

Lemma mtrace_valid_after `{M : FairModel} (mtr mtr' : mtrace M) k :
  after k mtr = Some mtr' → mtrace_valid mtr → mtrace_valid mtr'.
Proof.
  revert mtr mtr'.
  induction k; intros mtr mtr' Hafter Hvalid.
  { destruct mtr'; simpl in *; by simplify_eq. }
  punfold Hvalid.
  inversion Hvalid as [|??? Htrans Hval']; simplify_eq.
  eapply IHk; [done|].
  by inversion Hval'.
Qed.

Program Instance simple_model_terminates :
  FairTerminatingModel simple_fair_model :=
  {|
    ftm_leq := simple_state_order;
    ftm_decreasing_role := simple_decreasing_role;
    ftm_reachable_state := simple_reachable_state;
  |}.
Next Obligation.
  rewrite /simple_state_order.
  intros []; repeat (constructor; intros [] []; simpl in *; try lia).
Qed.
Next Obligation.
  intros mtr Hinit Hvalid [Hscheduling Hfair] n Hlen.
  rewrite /pred_at in Hlen. rewrite /pred_at.
  induction n; [done|].
  destruct mtr; [done|].
  assert (match after n (s -[ ℓ ]-> mtr) with
        | None => False
        | _ => True
        end) as Hn.
  { clear IHn. clear Hinit Hvalid Hscheduling Hfair. revert s mtr ℓ Hlen.
    induction n; [done|]; intros s mtr ℓ Hlen.
    simpl in *. destruct mtr; [done|].
    simpl in *. apply IHn. done. }
  assert (match after n (s -[ ℓ ]-> mtr) with
          | Some ⟨ s ⟩ | Some (s -[ _ ]-> _) => simple_reachable_state s
          | None => False
          end) as IHn'.
  { apply IHn. destruct (after n (s -[ ℓ ]-> mtr)); [|done]. destruct t; done. }
  clear Hn IHn.
  replace (S n) with (1 + n) by lia.
  replace (S n) with (1 + n) in Hlen by lia.
  rewrite after_sum.
  rewrite after_sum in Hlen.
  destruct (after n (s -[ ℓ ]-> mtr)) as [mtr'|] eqn:Heq; [|done].
  destruct mtr' as [mtr''|mtr'' ℓ' mtr''']; [done|].
  simpl in *.
  assert (simple_trans mtr'' ℓ' (trfirst mtr''')).
  { assert (mtrace_valid ((mtr'' -[ℓ']-> mtr'''):mtrace simple_fair_model)) as Hvalid'.
    { by eapply mtrace_valid_after. }
    punfold Hvalid'.
    inversion Hvalid'.
    simplify_eq.
    apply H1. }
  assert (fair_network_mtr ((mtr'' -[ℓ']-> mtr'''):mtrace simple_fair_model)) as
    Hfair'.
  { by eapply fair_network_mtr_after. }
  inversion H; simplify_eq; try by inversion Hinit.
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /fair_network_mtr in Hfair.
    specialize (Hfair' 0). by destruct Hfair' as [Hfair' ?].
  - rewrite /fair_network_mtr in Hfair.
    specialize (Hfair' 0). by destruct Hfair' as [Hfair' ?].
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /fair_network_mtr in Hfair.
    specialize (Hfair' 0). by destruct Hfair' as [Hfair' ?].
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
  - rewrite /trfirst in H3. destruct mtr'''; by rewrite -H3.
Qed.
Next Obligation.
  rewrite /simple_state_order.
  intros s Hexcl [ρ' [s' Htrans]]=> /=.
  split.
  - destruct s; try set_solver; destruct sent; try set_solver.
    simpl in *. destruct delivered; try set_solver. inversion Htrans.
  - intros s'' Htrans'. simpl in *.
    destruct s.
    + inversion Htrans'. split; simpl; lia.
    + inversion Htrans'. split; simpl; lia.
    + inversion Htrans'. split; simpl; lia.
    + inversion Htrans'. simplify_eq. simpl in *. done.
Qed.
Next Obligation.
  intros s s' ρ Hreachable Htrans Hρ. by destruct s; inversion Htrans.
Qed.
Next Obligation.
  rewrite /simple_state_order.
  intros s1 ρ s2 Hreachable Htrans. destruct s1; inversion Htrans; simpl; lia.
Qed.
