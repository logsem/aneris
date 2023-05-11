From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From Paco Require Import paco1 paco2 pacotac.
From fairneris Require Export trace_utils ltl_lite.
From fairneris.aneris_lang Require Import ast network.

Import derived_laws_later.bi.

Lemma prefix_trans {A} (l1 l2 l3 : list A) :
  l1 `prefix_of` l2 → l2 `prefix_of` l3 → l1 `prefix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply prefix_app_r. Qed.

Lemma suffix_trans {A} (l1 l2 l3 : list A) :
  l1 `suffix_of` l2 → l2 `suffix_of` l3 → l1 `suffix_of` l3.
Proof. intros [l1' ->] [l2' ->]. by do 2 apply suffix_app_r. Qed.

(** The retransmit model states *)
Inductive retransmit_base_state :=
| Start
| Received.

Definition retransmit_state : Set :=
  retransmit_base_state * message_multi_soup * gmap socket_address (list message).

#[global] Instance simple_state_eqdec : EqDecision retransmit_state.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance simple_state_inhabited : Inhabited retransmit_state.
Proof. exact (populate (Start,∅,∅)). Qed.

Inductive retransmit_node_role := Arole | Brole.
Inductive retransmit_network_role :=
| Ndup
| Ndrop
| Ndeliver.
Definition retransmit_role : Set :=
  retransmit_node_role + retransmit_network_role.

Definition retransmit_node_action : Set := option message.
Definition retransmit_network_action : Set := message.
Definition retransmit_action : Set :=
  retransmit_node_action + retransmit_network_action.

Definition retransmit_node_label : Set :=
  retransmit_node_role * retransmit_node_action.
Definition retransmit_network_label : Set :=
  retransmit_network_role * retransmit_network_action.
Definition retransmit_label : Set :=
  retransmit_node_label + retransmit_network_label.

Definition label_role (l : retransmit_label) : retransmit_role :=
  sum_map fst fst l.

Definition label_action (l : retransmit_label) : retransmit_action :=
  sum_map snd snd l.

#[global] Instance retransmit_role_eqdec : EqDecision retransmit_role.
Proof. intros ??. apply make_decision. Qed.
#[global] Instance retransmit_role_inhabited : Inhabited retransmit_role.
Proof. exact (populate (inl Arole)). Qed.
#[global] Instance retransmit_role_countable : Countable retransmit_role.
Proof.
  refine ({|
             encode s := match s with
                         | inl Arole => 1
                         | inl Brole => 2
                         | inr Ndup => 3
                         | inr Ndrop => 4
                         | inr Ndeliver => 5
                         end;
             decode n := match n with
                         | 1 => Some $ inl Arole
                         | 2 => Some $ inl Brole
                         | 3 => Some $ inr Ndup
                         | 4 => Some $ inr Ndrop
                         | 5 => Some $ inr Ndeliver
                         | _ => None
                         end;
         |})%positive.
  by intros [[]|[]].
Qed.

Definition saA : socket_address := SocketAddressInet "0.0.0.0" 80.
Definition saB : socket_address := SocketAddressInet "0.0.0.1" 80.
Definition mAB : message := mkMessage saA saB "Hello".

Inductive retransmit_trans : retransmit_state → retransmit_label → retransmit_state → Prop :=
| A_Send st ms bs :
  retransmit_trans (st, ms, bs)
                   (inl $ (Arole, Some mAB))
                   (st, ms ⊎ {[+ mAB +]}, bs)
| N_Duplicate st ms bs msg :
  msg ∈ ms →
  retransmit_trans (st, ms, bs)
                   (inr (Ndup, msg))
                   (st, ms ⊎ {[+ msg +]}, bs)
| N_Drop st ms bs msg :
  msg ∈ ms →
  retransmit_trans (st, ms, bs)
                   (inr (Ndrop, msg))
                   (st, ms ∖ {[+ msg +]}, bs)
| N_Deliver st ms ms' bs msg :
  msg ∈ ms →
  bs !!! m_destination msg = ms' →
  retransmit_trans (st, ms, bs)
                   (inr (Ndeliver, msg))
                   (st, ms ∖ {[+ msg +]}, <[m_destination msg := msg::ms']>bs)
| B_RecvFail ms bs :
  bs !!! saB = [] →
  retransmit_trans (Start, ms, bs)
                   (inl $ (Brole, None))
                   (Start, ms, bs)
| B_RecvSucc ms bs msg ms' :
  bs !!! saB = ms'++[msg] →
  retransmit_trans (Start, ms, bs)
                   (inl $ (Brole, None))
                   (Received, ms, <[saB := ms']>bs).

Definition send_filter msg : retransmit_state → option retransmit_label → Prop :=
  λ _ l, option_map label_action l = Some $ inl $ Some msg.
Instance send_filter_decision msg st l : Decision (send_filter msg st l).
Proof. apply make_decision. Qed.

Definition deliver_filter msg : retransmit_state → option retransmit_label → Prop :=
  λ _ l, l = Some $ inr (Ndeliver,msg).
Instance deliver_filter_decision msg st l : Decision (deliver_filter msg st l).
Proof. apply make_decision. Qed.

Notation mtrace := (trace retransmit_state retransmit_label).

(* Definition retransmit_fair_network_delivery msg : mtrace → Prop := *)
(*   □ (□◊↓send_filter msg → ◊↓deliver_filter msg). *)
Definition retransmit_fair_network_delivery msg : mtrace → Prop :=
  □ (□◊↓send_filter msg → ◊↓deliver_filter msg).

Definition retransmit_fair_network (mtr : mtrace) : Prop :=
  ∀ msg, retransmit_fair_network_delivery msg mtr.

(* TODO: This computation is a bit odd *)
Definition retransmit_live_roles (s : retransmit_state) : gset retransmit_role :=
  {[inl Arole]} ∪
  (if decide (s.1.2 = (∅:gmultiset _)) then ∅
   else {[inr Ndup;inr Ndrop;inr Ndeliver]}) ∪

  (match s.1.1 with Start => {[inl Brole]} | _ => ∅ end).

(* TODO: This should be generalised, and lifted to multiple roles *)
Definition retransmit_terminating_role (ρ : retransmit_role) (tr : mtrace) : Prop :=
  (◊ ↓ (λ st _, ρ ∉ retransmit_live_roles st)) tr.

Definition retransmit_role_enabled_model (ρ : retransmit_role) (s : retransmit_state) : Prop :=
  ρ ∈ retransmit_live_roles s.

Definition retransmit_fair_scheduling_mtr (ρ : retransmit_role) : mtrace → Prop :=
  trace_always_eventually_implies_now
    (λ δ _, retransmit_role_enabled_model ρ δ)
    (λ δ ℓ, ¬ retransmit_role_enabled_model ρ δ ∨
              option_map label_role ℓ = Some ρ).

(* Lemma retransmit_fair_scheduling_mtr_after ℓ tr tr' k : *)
(*   after k tr = Some tr' → *)
(*   retransmit_fair_scheduling_mtr ℓ tr → retransmit_fair_scheduling_mtr ℓ tr'. *)
(* Proof. Admitted. *)

Definition retransmit_fair_scheduling (mtr : mtrace) : Prop :=
  ∀ ρ, retransmit_fair_scheduling_mtr ρ mtr.

(* Lemma retransmit_fair_scheduling_after tr tr' k : *)
(*   after k tr = Some tr' → *)
(*   retransmit_fair_scheduling tr → retransmit_fair_scheduling tr'. *)
(* Proof. *)
(*   intros Hafter Hfair ℓ. specialize (Hfair ℓ). *)
(*   by eapply retransmit_fair_scheduling_mtr_after. *)
(* Qed. *)

Definition mtrace_fair (mtr : mtrace) : Prop :=
  retransmit_fair_scheduling mtr ∧ retransmit_fair_network mtr.

(* Good definition? *)
Definition trans_valid (mtr : mtrace) :=
   match mtr with
   | ⟨s⟩ => True
   | (s -[l]-> tr) => retransmit_trans s l (trfirst tr)
   end.

(* Good definition? *)
Definition mtrace_valid (mtr : mtrace) :=
  trace_always trans_valid mtr.

Definition option_lift {S L} (P : S → L → Prop) : S → option L → Prop :=
  λ s ol, ∃ l, ol = Some l ∧ P s l.

Lemma option_lift_Some {S L} (P : S → L → Prop) s l :
  option_lift P s (Some l) → P s l.
Proof. intros (l'&Hl'&HP). by simplify_eq. Qed.

Lemma A_always_live (mtr : mtrace) :
  trace_always (trace_now (λ s _, retransmit_role_enabled_model (inl Arole) s)) mtr.
Proof. apply trace_always_universal.
  rewrite /pred_at /retransmit_role_enabled_model. intros mtr'.
  by destruct mtr'; set_solver.
Qed.

Lemma retransmit_fair_traces_eventually_A mtr :
  retransmit_fair_scheduling_mtr (inl Arole) mtr →
  trace_eventually (trace_now (λ _ ℓ, option_map label_role ℓ = Some $ inl Arole)) mtr.
Proof.
  intros Hfair.
  pose proof (A_always_live mtr) as HA.
  eapply trace_always_eventually_always_implies; [|done].
  eapply trace_always_eventually_always_mono; [| |apply Hfair].
  - intros Htr. apply trace_implies_refl.
  - intros tr.
    apply trace_implies_implies.
    apply trace_now_mono.
    intros s l. intros [Htr|Htr]; [|done].
    rewrite /retransmit_role_enabled_model in Htr. set_solver.
Qed.

Lemma retransmit_fair_traces_eventually_mAB mtr :
  mtrace_valid mtr → retransmit_fair_scheduling_mtr (inl Arole) mtr →
  (◊ ↓ send_filter mAB) mtr.
Proof.
  intros Hvalid Hfair.
  pose proof (retransmit_fair_traces_eventually_A mtr Hfair) as Htr.
  eapply trace_eventually_mono_strong; [|done].
  intros tr' Htr'.
  eapply trace_always_suffix_of in Hvalid; [|done].
  apply trace_always_elim in Hvalid.
  destruct tr' as [s|s l tr']; [done|].
  apply trace_now_mono_strong.
  intros ???? HP; simplify_eq.
  destruct l; [|done]. destruct r. simpl in *.
  simplify_eq. inversion Hvalid. inversion H1. by simplify_eq.
Qed.

(* Proof by the fact that A is always live, and will eventually be scheduled.
   Needs fairness assumptions *)
Lemma retransmit_fair_traces_always_eventually_mAB mtr :
  mtrace_valid mtr → retransmit_fair_scheduling_mtr (inl $ Arole) mtr →
  (□ ◊ ↓ send_filter mAB) mtr.
Proof.
  intros Hvalid Hfair. eapply trace_always_implies_always;
    [|apply trace_always_and; split; [apply Hvalid|apply Hfair]].
  intros tr' [Hvalid' Hfair']%trace_always_and.
  by apply retransmit_fair_traces_eventually_mAB.
Qed.

Lemma eventually_send_eventually_deliver mtr :
  retransmit_fair_network mtr →
  (□ ◊ ↓ send_filter mAB) mtr →
  (◊ ↓ deliver_filter mAB) mtr.
Proof.
  intros Hfair_network Hsend.
  pose proof (Hfair_network mAB). apply trace_always_elim in H.
  rewrite trace_implies_implies in H. apply H. done.
Qed.

(* If a message is delivered, the next state has a message in the buffer *)
(* Proof by validity relation of the model *)
Lemma deliver_next_buffer msg mtr :
  mtrace_valid mtr →
  (↓ deliver_filter msg) mtr →
  (○ ↓ λ s _, ∃ bs, s.2 !!! (m_destination msg) = msg :: bs) mtr.
Proof.
  intros Hvalid%trace_always_elim Hdeliver.
  destruct mtr; [done|].
  exists mtr. split; [done|].
  rewrite /trace_now /deliver_filter /pred_at in Hdeliver.
  simpl in *. simplify_eq.
  inversion Hvalid. simplify_eq.
  destruct mtr.
  - rewrite /trace_now /pred_at. simpl in *. simplify_eq.
    exists (bs !!! m_destination msg).
    simpl. by rewrite lookup_total_insert.
  - rewrite /trace_now /pred_at. simpl in *. simplify_eq.
    exists (bs !!! m_destination msg).
    simpl. by rewrite lookup_total_insert.
Qed.

(* The buffers will only grow until B is scheduled *)
(* Proof by validity relation of the model *)
Lemma retransmit_fair_trace_buffer_grows mtr bs P :
  mtrace_valid mtr →
  (↓ λ s _, s.2 !!! (m_destination mAB) = bs) mtr →
  (trace_until (trace_not (↓ λ _ l, option_map label_role l = Some $ inl Brole)) P) mtr →
  (◊ trace_and (↓ λ s _, suffix bs (s.2 !!! (m_destination mAB))) P) mtr.
Proof. Admitted.

(* A scheduled B will succeed if there is something in the buffer *)
(* Proof by validity relation of the model *)
(* Lemma successful_receive msg mtr : *)
(*   mtrace_valid mtr → *)
(*   (↓ λ s _, ∃ bs, s.2 !!! (m_destination msg) = msg :: bs) mtr → *)
(*   (↓ λ _ l, option_map label_role l = Some $ inl Brole) mtr → *)
(*   (○ ↓ λ s _, s.1.1 = Received) mtr. *)
(* Proof. Admitted. *)

(* A scheduled B will succeed if there is something in the buffer *)
(* Proof by validity relation of the model *)
Lemma successful_deliver_received bs (mtr : mtrace) :
  mtrace_valid mtr →
  (↓ (λ s _, mAB :: bs `suffix_of` s.2 !!! (m_destination mAB))) mtr →
  (↓ (λ _ l, option_map label_role l = Some (inl Brole))) mtr →
  (○ ↓ (λ s _, s.1.1 = Received)) mtr.
Proof.
  intros Hvalid%trace_always_elim Hbs HB.
  destruct mtr as [?|s l mtr]; [done|].
  simpl in *. destruct l as [|]; [|done].
  exists mtr. split; [done|].
  rewrite /trace_now /pred_at in HB.
  simpl in *. simplify_eq.
  destruct r. simpl in *. simplify_eq.
  inversion Hvalid; simplify_eq; [|]; last first.
  { destruct mtr as [[]|[]]; simpl in *; simplify_eq; done. }
    rewrite /trace_now /pred_at in Hbs. simpl in *.
  rewrite H2 in Hbs. by apply suffix_cons_nil_inv in Hbs.
Qed.

(* OBS: Will need scheduling fairness *)
(* Proof by EM on whether B is live.
   - If it is not, we are in Received
   - if It is, B will eventually be scheduled, by fairness *)
Lemma received_or_eventually_B (mtr : mtrace) :
  (↓ λ s _, s.1.1 = Received) mtr ∨
  (◊↓ λ _ l, option_map label_role l = Some $ inl Brole) mtr.
Proof.
  (* TODO: you are here. Time to do fairness stuff. Can we avoid this with LTL? *)
  (* assert ((◊ ↓ λ _ l, option_map label_role l = Some $ inl Brole) mtr' ∨ *)
  (*        ¬ (◊ ↓ λ _ l, option_map label_role l = Some $ inl Brole) mtr'). *)
  (* { apply ExcludedMiddle. } *)
  (* destruct H as [H|H]; last first. *)
  (* { apply trace_not_not in H. *)
  (*   apply trace_not_eventually_always_not in H. *)
  (*   apply trace_always_eventually in H. *)
  (*   revert H. apply trace_eventually_mono_strong. *)
  (*   intros mtr'' Hsuffix' Htr'. *)
  (*   apply trace_not_now in Htr'. *)
  (*   revert Htr'. *)
  (*   apply trace_now_mono_strong. *)
  (*   intros s l Hs Hl H. *)
  (*   simplify_eq. *)
  (*   assert (mtrace_valid mtr''). *)
  (*   { eapply trace_always_suffix_of; [done|]. by eapply trace_always_suffix_of. } *)
  (*   apply trace_always_elim in H0. *)
  (*   rewrite /trans_valid in H0. *)
  (*   destruct mtr''. *)
  (*   - admit.                    (* Need infinite trace property *) *)
  (*   - simpl in *. destruct s. destruct p. simpl in *. simplify_eq. *)
  (*     admit. }                  (* Derp need EM on whether B is live. *) *)
Admitted.

Lemma eventually_deliver_eventually_received mtr :
  mtrace_valid mtr → mtrace_fair mtr →
  (◊ ↓ deliver_filter mAB) mtr →
  (◊ ↓ λ s _, s.1.1 = Received) mtr.
Proof.
  intros Hvalid Hfair Hdeliver.
  eapply trace_eventually_mono_strong in Hdeliver; last first.
  { intros tr' Hsuffix. apply deliver_next_buffer. by eapply trace_always_suffix_of. }
  apply trace_eventually_next in Hdeliver.
  revert Hdeliver.
  apply trace_eventually_thing_strong.
  intros mtr' Hsuffix Hdeliver.
  apply trace_now_exists in Hdeliver as [bs Hdeliver].
  assert (mtrace_valid mtr') as Hvalid'.
  { by eapply trace_always_suffix_of. }
  pose proof (received_or_eventually_B) as [H|H].
  { by apply trace_eventually_now. }
  apply trace_eventually_next.
  apply trace_eventually_until in H.
  pose proof (retransmit_fair_trace_buffer_grows _ (mAB :: bs) _ Hvalid' Hdeliver H) as H'.
  revert H'.
  apply trace_eventually_mono_strong.
  intros mtr'' Hsuffix' [Hmtr1'' Hmtr2'']%trace_andI.
  assert (mtrace_valid mtr'') by by eapply trace_always_suffix_of.
  by eapply successful_deliver_received.
Qed.

(* Any fair trace terminates on role B *)
Lemma retransmit_fair_traces_terminate mtr :
  mtrace_valid mtr → mtrace_fair mtr →
  retransmit_terminating_role (inl Brole) mtr.
Proof.
  intros Hvalid [Hfair1 Hfair2].
  pose proof (retransmit_fair_traces_always_eventually_mAB mtr Hvalid (Hfair1 _)).
  apply (eventually_send_eventually_deliver _ Hfair2) in H.
  apply (eventually_deliver_eventually_received) in H; [|done..].
  revert H. apply trace_eventually_mono.
  intros tr. apply trace_now_mono. intros [[]] _ Hreceived.
  rewrite /retransmit_live_roles. simpl in *. simplify_eq. case_decide; set_solver.
Qed.
