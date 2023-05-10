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

Declare Scope trace_scope.
Delimit Scope trace_scope with trace.
Bind Scope trace_scope with trace.

Notation "□ P" := (trace_always P) (at level 20, right associativity) : trace_scope.
Notation "◊ P" := (trace_eventually P) (at level 20, right associativity) : trace_scope.
Notation "↓ P" := (trace_now P) (at level 20, right associativity) : trace_scope.
Notation "P → Q" := (trace_implies P Q)
                      (at level 99, Q at level 200,
                         format "'[' P  →  '/' '[' Q ']' ']'") : trace_scope.

(* Definition retransmit_fair_network_delivery msg : mtrace → Prop := *)
(*   □ (□◊↓send_filter msg → ◊↓deliver_filter msg). *)
Definition trace_weak_until {S L} (P Q : trace S L → Prop) : trace S L → Prop :=
  trace_or (trace_until P Q) (□ P).
Definition retransmit_fair_network_delivery msg : mtrace → Prop :=
  □ ((trace_weak_until (□◊↓send_filter msg) (↓deliver_filter msg)) → ◊↓deliver_filter msg).

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

Lemma retransmit_fair_scheduling_mtr_after ℓ tr tr' k :
  after k tr = Some tr' →
  retransmit_fair_scheduling_mtr ℓ tr → retransmit_fair_scheduling_mtr ℓ tr'.
Proof. Admitted.

Definition retransmit_fair_scheduling (mtr : mtrace) : Prop :=
  ∀ ρ, retransmit_fair_scheduling_mtr ρ mtr.

Lemma retransmit_fair_scheduling_after tr tr' k :
  after k tr = Some tr' →
  retransmit_fair_scheduling tr → retransmit_fair_scheduling tr'.
Proof.
  intros Hafter Hfair ℓ. specialize (Hfair ℓ).
  by eapply retransmit_fair_scheduling_mtr_after.
Qed.

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

Lemma trace_eventually_cons {S L} (P : trace S L → Prop) s l (tr : trace S L) :
  trace_eventually P tr → trace_eventually P (s -[l]-> tr).
Proof.
  intros [n [Htr1 Htr2]].
  exists (Datatypes.S n).
  split; [done|]. clear Htr1.
  intros m Hm.
  destruct m; [by eexists _|].
  apply Htr2. lia.
Qed.

Lemma trace_always_cons {S L} (P : trace S L → Prop) s l (tr : trace S L) :
  trace_always P (s -[l]-> tr) → trace_always P tr.
Proof.
  rewrite /trace_always.
  intros Htr Htr'. apply Htr. clear Htr.
  by apply trace_eventually_cons.
Qed.

Lemma trace_always_now_cons {S L} (P : S → option L → Prop) s l (tr : trace S L) :
  trace_always (trace_now P) (s -[l]-> tr) → P s (Some l).
Proof. Admitted.

Definition option_lift {S L} (P : S → L → Prop) : S → option L → Prop :=
  λ s ol, ∃ l, ol = Some l ∧ P s l.

Lemma option_lift_Some {S L} (P : S → L → Prop) s l :
  option_lift P s (Some l) → P s l.
Proof. intros (l'&Hl'&HP). by simplify_eq. Qed.

Lemma trace_eventually_mono {S L} (P Q : trace S L → Prop) tr :
  (∀ tr, P tr → Q tr) → trace_eventually P tr → trace_eventually Q tr.
Proof.
  intros HPQ (n&(tr'&Htr1&Htr2)&H2).
  exists n. split; [|done]. exists tr'. split; [done|]. by apply HPQ.
Qed.

Definition trace_suffix_of {S L} (tr1 tr2 : trace S L) : Prop :=
  ∃ n, after n tr2 = Some tr1.

Lemma trace_suffix_of_refl {S L} (tr : trace S L) :
  trace_suffix_of tr tr.
Proof. by exists 0. Qed.

Lemma trace_eventually_mono_strong {S L} (P Q : trace S L → Prop) tr :
  (∀ tr', trace_suffix_of tr' tr → P tr' → Q tr') →
  trace_eventually P tr → trace_eventually Q tr.
Proof.
  intros HPQ (n&(tr'&Htr1&Htr2)&H2).
  exists n. split; [|done]. exists tr'. split; [done|]. apply HPQ; [|done].
  exists n. done.
Qed.

Lemma trace_implies_implies {S L} (P Q : trace S L → Prop) tr :
  trace_implies P Q tr ↔ (P tr → Q tr).
Proof.
  split.
  - by intros [|].
  - intros HPQ.
    assert (P tr ∨ ¬ P tr) as [HP|HP] by apply ExcludedMiddle.
    + by right; apply HPQ.
    + by left.
Qed.

Lemma trace_always_mono {S L} (P Q : trace S L → Prop) tr :
  (∀ tr, trace_implies P Q tr) → trace_always P tr → trace_always Q tr.
Proof.
  intros HPQ HP HQ. apply HP. eapply trace_eventually_mono; [|done].
  clear HP HQ. intros tr' HP HQ. apply HP.
  specialize (HPQ tr'). rewrite trace_implies_implies in HPQ. by apply HPQ.
Qed.

Lemma trace_always_mono_strong {S L} (P Q : trace S L → Prop) tr :
  (∀ tr', trace_suffix_of tr' tr → trace_implies P Q tr') → trace_always P tr → trace_always Q tr.
Proof.
  intros HPQ HP HQ. apply HP. eapply trace_eventually_mono_strong; [|done].
  clear HP HQ. intros tr' Htr' HP HQ. apply HP.
  specialize (HPQ tr'). rewrite trace_implies_implies in HPQ. by apply HPQ.  
Qed.

Lemma after_is_Some_lt {S L} (tr : trace S L) n m :
  m < n → is_Some $ after n tr → is_Some $ after m tr.
Proof.
  revert tr m.
  induction n; intros tr m Hle.
  { intros. assert (m = 0) as -> by lia. done. }
  intros.
  destruct m; [done|].
  simpl in *.
  destruct tr; [done|].
  apply IHn. lia. done.
Qed.

(* TODO: Improve this proof *)
Lemma trace_alwaysI {S L} (P : trace S L → Prop) tr :
  trace_always P tr ↔ (∀ tr', trace_suffix_of tr' tr → trace_always P tr').
Proof.
  split.
  - rewrite /trace_always. 
    intros Halways tr' [n Hafter] HP. apply Halways.
    destruct HP as [m [HP HP']].
    destruct HP as [tr'' [Htr'' Hnot]].
    exists (n + m).
    split.
    + exists tr''. rewrite after_sum'. rewrite Hafter. done.
    + intros m' Hlt.
      assert (after (n+m) tr = Some tr'').
      { rewrite after_sum'. rewrite Hafter. done. } 
      assert (is_Some $ after m' tr) as [tr''' Htr'''].
      { by eapply after_is_Some_lt. }
      exists tr'''. split; [done|].
      by destruct tr'''.
  - intros Halways. eapply (Halways). apply trace_suffix_of_refl.
Qed.

Lemma trace_always_suffix_of {S L} (P : trace S L → Prop) tr1 tr2 :
  trace_suffix_of tr2 tr1 → trace_always P tr1 → trace_always P tr2.
Proof. rewrite (trace_alwaysI _ tr1). intros Hsuffix HP. by eapply HP. Qed.

Lemma trace_always_universal {S L} (P : trace S L → Prop) (tr : trace S L) :
  (∀ tr, P tr) → trace_always P tr.
Proof. by intros ?(?&(?&_&?)&_); eauto. Qed.

Lemma A_always_live (mtr : mtrace) :
  trace_always (trace_now (λ s _, retransmit_role_enabled_model (inl Arole) s)) mtr.
Proof. apply trace_always_universal. 
  rewrite /pred_at /retransmit_role_enabled_model. intros mtr'.
  by destruct mtr'; set_solver.
Qed.

Lemma trace_not_idemp {S L} (P : trace S L → Prop) (tr : trace S L) :
  trace_not (trace_not P) tr ↔ P tr.
Proof. rewrite /trace_not. split; [apply NNP_P|apply P_NNP]. Qed.

(* TODO: Replace existing lemma with this *)
Lemma not_exists_forall_not_alt {A} (P : A → Prop) x : ¬ (∃ x, P x) → ¬ P x.
Proof. intros Hnex HP; apply Hnex; eauto. Qed.

Lemma trace_always_elim {S L} (P : trace S L → Prop) (tr : trace S L) :
  trace_always P tr → P tr.
Proof.
  intros Htr.
  eapply (not_exists_forall_not_alt _ 0) in Htr.
  apply Classical_Prop.not_and_or in Htr as [Htr|Htr].
  { eapply (not_exists_forall_not_alt _ tr) in Htr.
    apply Classical_Prop.not_and_or in Htr as [Htr|Htr]; [done|].
    apply trace_not_not in Htr. by rewrite trace_not_idemp in Htr. }
  eapply not_forall_exists_not in Htr as [x Htr].
  eapply Classical_Prop.imply_to_and in Htr as [Hx Htr].
  lia.
Qed.

(* TODO: This is a bit of a weird statement *)
Lemma trace_always_implies {S L} (P Q : trace S L → Prop) tr :
  trace_always (trace_implies P Q) tr → trace_always P tr → trace_always Q tr.
Proof.
  intros HPQ HP.
  eapply trace_always_mono_strong; [|done].
  intros tr' Hsuffix.
  apply trace_always_elim.
  by eapply trace_always_suffix_of.
Qed.

Lemma trace_always_eventually_always_implies {S L} (P Q : trace S L → Prop) tr :
  trace_always_eventually_implies P Q tr → trace_always P tr → trace_eventually Q tr.
Proof.
  intros HPQ HP.
  eapply trace_always_implies in HP; [|done].
  by apply trace_always_elim.
Qed.  

Lemma trace_always_eventually_always_mono {S L} (P1 P2 Q1 Q2 : trace S L → Prop) tr :
  (∀ tr, trace_implies P2 P1 tr) → (∀ tr, trace_implies Q1 Q2 tr) →
  trace_always_eventually_implies P1 Q1 tr → trace_always_eventually_implies P2 Q2 tr.
Proof.
  setoid_rewrite trace_implies_implies.
  intros HP HQ Htr.
  eapply trace_always_mono; [|done].
  intros Htr'.
  apply trace_implies_implies.
  rewrite !trace_implies_implies.
  intros HPQ HP2.
  eapply trace_eventually_mono; [apply HQ|by apply HPQ; apply HP].
Qed.

Lemma trace_implies_refl {S L} (P : trace S L → Prop) tr :
  trace_implies P P tr.
Proof. by apply trace_implies_implies. Qed.

(* This seems a bit too specific *)

Definition trfirst_label {S L} (tr: trace S L) : option L :=
  match tr with
  | ⟨_⟩ => None
  | _ -[ℓ]-> _ => Some ℓ
  end.

(* This seems a bit too specific *)
Lemma trace_now_mono_strong {S L} (P Q : S → option L → Prop) tr :
  (∀ s l, trfirst tr = s → trfirst_label tr = l → P s l → Q s l) →
  trace_now P tr → trace_now Q tr.
Proof.
  destruct tr as [s|s l tr].
  - rewrite /trace_now /pred_at /=. intros HPQ Htr. by apply HPQ.
  - rewrite /trace_now /pred_at /=. intros HPQ Htr. by apply HPQ.
Qed.

Lemma trace_now_mono {S L} (P Q : S → option L → Prop) tr :
  (∀ s l, P s l → Q s l) → trace_now P tr → trace_now Q tr.
Proof. intros. eapply trace_now_mono_strong; [|done]. by eauto. Qed.

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

Lemma trace_always_idemp {S L} P (tr : trace S L) :
  (□ P) tr → (□ □ P) tr. 
Proof. Admitted.

Lemma trace_always_and {S L} P Q (tr : trace S L) :
  ((□ P) tr ∧ (□ Q) tr) ↔ (□ trace_and P Q) tr. 
Proof. Admitted.

Lemma retransmit_fair_traces_always_eventually_mAB mtr :
  mtrace_valid mtr → retransmit_fair_scheduling_mtr (inl $ Arole) mtr →
  (□ ◊ ↓ send_filter mAB) mtr.
Proof. Admitted.

Lemma trace_or_l {S L} (P Q : trace S L → Prop) (tr : trace S L) :
  P tr → trace_or P Q tr.
Proof. intros HP. by left. Qed.

Lemma trace_or_r {S L} (P Q : trace S L → Prop) (tr : trace S L) :
  Q tr → trace_or P Q tr.
Proof. intros HP. by right. Qed.

Lemma trace_weak_until_always {S L} P Q (tr : trace S L) :
  trace_always P tr → trace_weak_until P Q tr.
Proof. intros HP. by apply trace_or_r. Qed.


(* Any fair trace eventually delivers a message *)
Lemma eventually_send_eventually_deliver mtr :
  retransmit_fair_network mtr →
  (□ ◊ ↓ send_filter mAB) mtr →
  (◊ ↓ deliver_filter mAB) mtr.
Proof.
  intros Hfair_network Hsend.
  pose proof (Hfair_network mAB). apply trace_always_elim in H.
  rewrite trace_implies_implies in H. apply H.
  apply trace_weak_until_always. apply trace_always_idemp. done.
Qed.

(* (* Any fair trace eventually delivers a message *) *)
(* Lemma retransmit_fair_trace_eventually_Ndeliver mtr : *)
(*   mtrace_valid mtr → mtrace_fair mtr → *)
(*   (◊ ↓ deliver_filter mAB) mtr. *)
(* Proof. *)
(*   intros Hvalid Hfair. *)
(*   destruct Hfair as [Hfair_sched Hfair_network]. *)
(*   pose proof (Hfair_network mAB). apply trace_always_elim in H. *)
(*   rewrite trace_implies_implies in H. *)
(*   apply H. apply trace_weak_until_always. apply trace_always_idemp. *)
(*   by apply retransmit_fair_traces_always_eventually_mAB. *)
(* Qed. *)

Definition trace_next {S L} (P : trace S L → Prop) (tr : trace S L) : Prop :=
  ∀ tr', after 1 tr  = Some tr' → P tr'.

Notation "○ P" := (trace_next P) (at level 20, right associativity) : trace_scope.

Lemma trace_eventually_next {S L} (P : trace S L → Prop) (tr : trace S L) :
  (◊ ○ P) tr → (◊ P) tr.
Proof.
  (* destruct 1 as [n [HP HP']]. *)
  (* destruct HP as [tr' [HP1 HP2]]. *)
  (* destruct tr. *)
  (* - admit. *)
  (* - simpl in *. *)
  (*   destruct n; simpl in *. *)
  (*   + simplify_eq. exists 0.  split. *)
  (*   + exists tr'. simpl in *. done. *)
Admitted.

Lemma trace_trueI {S L} (tr : trace S L) :
  trace_true tr.
Proof. destruct tr; done. Qed.

Lemma trace_eventually_suffix_of {S L} (P : trace S L → Prop) tr1 tr2 :
  trace_suffix_of tr1 tr2 → trace_eventually P tr1 → trace_eventually P tr2.
Proof.
  intros [n Hsuffix] [m [[tr' [Hafter HP]] Htrue]].
  exists (n + m).
  rewrite after_sum'. rewrite Hsuffix Hafter.
  split.
  - exists tr'. done.
  - intros m' Hm.
    assert (after (n + m) tr2 = Some tr').
    { rewrite after_sum'. rewrite Hsuffix Hafter. done. }
    assert (is_Some (after m' tr2)) as [tr'' Htr'].
    { by eapply after_is_Some_lt. }
    exists tr''. split; [done| apply trace_trueI].
Qed.

Lemma trace_eventually_thing_strong {S L} (P Q : trace S L → Prop) (tr : trace S L) :
  (∀ tr', trace_suffix_of tr' tr → P tr' → (◊ Q) tr') → (◊ P) tr → (◊ Q) tr.
Proof.
  intros HPQ HP.
  destruct HP as [n [[tr' [Hafter HP]] Htrue]].
  apply HPQ in HP; [|by exists n].
  eapply trace_eventually_suffix_of; [|done].
  by exists n.
Qed.

Lemma trace_not_eventually_always_not {S L} P (tr : trace S L) :
  trace_not (◊ P) tr ↔ (□ (trace_not P)) tr.
Proof. Admitted.

Lemma trace_always_eventually {S L} P (tr : trace S L) :
  (□ P) tr → (◊ P) tr.
Proof. Admitted.

Lemma trace_not_now {S L} P (tr : trace S L) :
  trace_not (↓ P) tr ↔ (↓ (λ s l, ¬ P s l)) tr.
Proof. Admitted.

Lemma trace_eventually_now {S L} P (tr : trace S L) :
  (↓ P) tr → (◊ ↓ P) tr.
Proof. Admitted.

Lemma trace_now_exists {A} {S L} (P : A → S → option L → Prop) (tr : trace S L) :
  (↓ (λ s l, ∃ (x:A), P x s l)) tr → ∃ (x:A), (↓ P x) tr.
Proof. rewrite /trace_now /pred_at. intros H. by destruct tr. Qed.

Lemma trace_andI {S L} (P Q : trace S L → Prop) (tr : trace S L) :
  trace_and P Q tr ↔ P tr ∧ Q tr.
Proof. Admitted.

Lemma trace_nextI {S L} (P : trace S L → Prop) s l (tr : trace S L) :
  P tr → (○ P) (s -[l]-> tr).
Proof. intros ???. simpl in *. by simplify_eq. Qed.

Lemma deliver_next_buffer msg mtr :
  mtrace_valid mtr →
  (↓ deliver_filter msg) mtr →
  (○ ↓ λ s _, ∃ bs, s.2 !!! (m_destination msg) = msg :: bs) mtr.
Proof. Admitted.

Lemma successful_receive msg mtr :
  mtrace_valid mtr →
  (↓ λ s _, ∃ bs, s.2 !!! (m_destination msg) = msg :: bs) mtr →
  (↓ λ _ l, option_map label_role l = Some $ inl Brole) mtr →
  (○ ↓ λ s _, s.1.1 = Received) mtr.
Proof. Admitted.

Lemma retransmit_fair_trace_buffer_grows mtr bs P :
  mtrace_valid mtr →
  (↓ λ s _, s.2 !!! (m_destination mAB) = bs) mtr →
  (trace_until (trace_not (↓ λ _ l, option_map label_role l = Some $ inl Brole)) P) mtr →
  (◊ trace_and (↓ λ s _, suffix bs (s.2 !!! (m_destination mAB))) P) mtr.
Proof. Admitted.

Lemma successful_deliver_received bs (mtr : mtrace) :
  (↓ (λ s _, mAB :: bs `suffix_of` s.2 !!! (m_destination mAB))) mtr →
  (↓ (λ _ l, option_map label_role l = Some (inl Brole))) mtr →
  (○ ↓ (λ s _, s.1.1 = Received)) mtr.
Proof. Admitted.

(* OBS: Will need scheduling fairness *)
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
  apply trace_eventually_mono.
  intros mtr'' [Hmtr1'' Hmtr2'']%trace_andI.
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
