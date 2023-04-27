From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From Paco Require Import paco1 paco2 pacotac.
From fairneris Require Export trace_utils.
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

Definition send_filter msg : retransmit_state → retransmit_label → Prop :=
  λ _ l, label_action l = inl $ Some msg.
Instance send_filter_decision msg st l : Decision (send_filter msg st l).
Proof. apply make_decision. Qed.

Definition deliver_filter msg : retransmit_state → retransmit_label → Prop :=
  λ _ l, l = inr (Ndeliver,msg).
Instance deliver_filter_decision msg st l : Decision (deliver_filter msg st l).
Proof. apply make_decision. Qed.

Class Monotone (f : nat → nat) :=
  { mono_incr : ∀ n m, n ≤ m → f n ≤ f m; }.

Definition count_sends (msg : message) tr : nat :=
  count_labels (trace_filter (send_filter msg) tr).

Definition count_delivers (msg : message) tr : nat :=
  count_labels (trace_filter (deliver_filter msg) tr).

Notation mtrace := (trace retransmit_state retransmit_label).

Definition retransmit_network_fair_delivery (tr : mtrace) : Prop :=
  ∃ (f1 f2 : nat → nat) `(Monotone f1) `(Monotone f2),
    ∀ msg n,
      let sends := count_sends msg (trace_take n tr) in
      let delivers := count_delivers msg (trace_take n tr) in
      f1 delivers ≤ sends ≤ f2 delivers.

(* TODO: This computation is a bit odd *)
Definition retransmit_live_roles (s : retransmit_state) : gset retransmit_role :=
  {[inl Arole]} ∪
  (if decide (s.1.2 = (∅:gmultiset _)) then ∅
   else {[inr Ndup;inr Ndrop;inr Ndeliver]}) ∪
  (match s.1.1 with Start => {[inl Brole]} | _ => ∅ end).

(* TODO: This should be generalised, and lifted to multiple roles *)
Definition retransmit_terminating_role (ρ : retransmit_role) (tr : mtrace) : Prop :=
  ∃ n, after n tr = None ∨ pred_at tr n (λ st _, ρ ∉ retransmit_live_roles st).

Definition retransmit_role_enabled_model (ρ : retransmit_role) (s : retransmit_state) : Prop :=
  ρ ∈ retransmit_live_roles s.

Definition retransmit_fair_scheduling_mtr (ρ : retransmit_role) : mtrace → Prop :=
  trace_implies (λ δ _, retransmit_role_enabled_model ρ δ)
                (λ δ ℓ, ¬ retransmit_role_enabled_model ρ δ ∨
                          option_map label_role ℓ = Some ρ).

Lemma retransmit_fair_scheduling_mtr_after ℓ tr tr' k :
  after k tr = Some tr' →
  retransmit_fair_scheduling_mtr ℓ tr → retransmit_fair_scheduling_mtr ℓ tr'.
Proof. apply trace_implies_after. Qed.

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
  retransmit_fair_scheduling mtr ∧ retransmit_network_fair_delivery mtr.

Inductive mtrace_valid_ind (mtrace_valid_coind: mtrace → Prop) :
  mtrace → Prop :=
| mtrace_valid_singleton δ: mtrace_valid_ind _ ⟨δ⟩
| mtrace_valid_cons δ ℓ tr:
  retransmit_trans δ ℓ (trfirst tr) →
  mtrace_valid_coind tr →
  mtrace_valid_ind _ (δ -[ℓ]-> tr).
Definition mtrace_valid := paco1 mtrace_valid_ind bot1.

Lemma mtrace_valid_mono :
  monotone1 mtrace_valid_ind.
Proof.
  unfold monotone1. intros x0 r r' IN LE.
  induction IN; try (econstructor; eauto; done).
Qed.
Hint Resolve mtrace_valid_mono : paco.

Lemma mtrace_valid_after (mtr mtr' : mtrace) k :
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

Lemma retransmit_trace_delivers_0 (mtr : mtrace) n :
  (∀ n : nat, pred_at mtr n (λ _ l, l ≠ Some (inr (Ndeliver, mAB)))) →
  count_delivers mAB (trace_take n mtr) = 0.
Proof.
  revert mtr.
  induction n; intros mtr Hpred.
  { simpl. specialize (Hpred 0).
    destruct mtr; simpl in *.
    - rewrite /pred_at in Hpred. simpl in *.
      rewrite /count_delivers. done.
    - rewrite /pred_at in Hpred. simpl in *.
      rewrite /count_delivers. done.
  }
  simpl in *.
  destruct mtr; [done|].
  rewrite /count_delivers. simpl.
  case_bool_decide.
  - specialize (Hpred 0). rewrite pred_at_0 in Hpred. rewrite /deliver_filter in H.
    simplify_eq. 
  - apply IHn.
    intros n'. specialize (Hpred (S n')). rewrite pred_at_S in Hpred. done.
Qed.

Lemma A_always_live (mtr : mtrace) n :
  infinite_trace mtr →
  pred_at mtr n (λ s _, retransmit_role_enabled_model (inl Arole) s).
Proof.
  intros Hinf.
  rewrite /pred_at. rewrite /infinite_trace in Hinf.
  destruct (Hinf n) as [mtr' ->].
  destruct mtr'.
  - rewrite /retransmit_role_enabled_model. destruct s as [[[]?]?]; set_solver.
  - rewrite /retransmit_role_enabled_model. destruct s as [[[]?]?]; set_solver.
Qed.

Lemma retransmit_fair_traces_eventually_A (mtr : mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr → retransmit_fair_scheduling mtr →
  ∃ n, pred_at mtr n (λ _ ℓ, option_map label_role ℓ = Some $ inl Arole).
Proof.
  intros Hinf Hvalid Hfair.
  pose proof A_always_live as HA.
  pose proof A_always_live as HA'.
  specialize (HA mtr 0 Hinf).
  apply Hfair in HA as [m HA].
  apply pred_at_or in HA as [HA|HA].
  - specialize (HA' mtr m Hinf). simpl in *.
    apply pred_at_neg in HA; done.
  - exists m. done.
Qed.

Lemma retransmit_fair_traces_eventually_mAB (mtr : mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr → retransmit_fair_scheduling mtr →
  ∃ n, pred_at mtr n (λ st l, option_map label_action l = Some $ inl $ Some mAB).
Proof. 
  intros Hinf Hvalid Hfair.
  pose proof A_always_live as HA.
  pose proof A_always_live as HA'.
  specialize (HA mtr 0 Hinf).
  apply Hfair in HA as [m HA].
  apply pred_at_or in HA as [HA|HA].
  - specialize (HA' mtr m Hinf). simpl in *.
    apply pred_at_neg in HA; done.
  - exists m.
    specialize (Hinf m) as [mtr' Hafter].
    eapply mtrace_valid_after in Hvalid; [|done].
    simpl in *.
    rewrite /pred_at in HA. rewrite Hafter in HA.
    rewrite /pred_at. rewrite Hafter.
    destruct mtr'; [done|].
    destruct ℓ; [|done].
    simpl in *. simplify_eq.
    destruct r=> /=. simpl in *. simplify_eq.
    pinversion Hvalid. simplify_eq.
    inversion H1. simplify_eq. done.
Qed.

(* TODO: This can possibly be generalised *)
Lemma count_sends_pred_at n tr :
  pred_at tr n (λ _ l, option_map label_action l = Some $ inl $ Some mAB) →
  0 < count_sends mAB (trace_take (S n) tr).
Proof.
  revert tr.
  induction n=> /=; intros tr Hpred_at.
  { rewrite /pred_at in Hpred_at.    
    destruct tr; simpl in *.
    - done.
    - rewrite /count_sends=> /=.
      case_bool_decide.
      + simpl. lia.
      + destruct ℓ; [|done]. simplify_eq. rewrite /send_filter in H.
        destruct r. simpl in *. simplify_eq. }
  simpl in *.
  destruct tr; [done|].
  simpl in *. rewrite /count_sends=> /=.
  case_bool_decide.
  - simpl. lia.
  - apply IHn. done.
Qed.

(* Any fair infinite trace grow the number of sends indefinitely *)
Lemma retransmit_trace_sends_grows (mtr : mtrace) x :
  infinite_trace mtr →
  mtrace_valid mtr → retransmit_fair_scheduling mtr →
  ∃ n, x < count_sends mAB (trace_take n mtr).
Proof.
  intros Hafter Hvalid Hfair.
  induction x.
  { assert (∃ n, pred_at mtr n (λ st l, option_map label_action l = Some $ inl $ Some mAB))
      as [n Hn].
    { by apply retransmit_fair_traces_eventually_mAB. }
    exists (S n).
    by eapply count_sends_pred_at. }
  destruct IHx as [n IHn].
  apply (infinite_trace_after' n) in Hafter as (mtr' & Hmtr' & Hafter).
  assert (∃ n, pred_at mtr' n (λ st l, option_map label_action l = Some $ inl $ Some mAB))
    as [m Hm].
  { apply retransmit_fair_traces_eventually_mAB;
      [done|by eapply mtrace_valid_after|
        by eapply retransmit_fair_scheduling_after]. }
  assert (0 < count_sends mAB (trace_take (S m) mtr')).
  { eapply count_sends_pred_at. done. }
  exists (n+(S m)).
  rewrite /count_sends. rewrite /count_sends in H. rewrite /count_sends in IHn.
  rewrite (count_labels_sum _ _ _ _ mtr'); [|done].  
  lia.
Qed.

(* Any fair trace eventually delivers a message *)
Lemma retransmit_fair_trace_eventually_Ndeliver (mtr : mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr → mtrace_fair mtr →
  ∃ n, pred_at mtr n (λ st l, l = Some $ inr (Ndeliver,mAB)).
Proof.
  intros Hafter Hvalid Hfair.
  assert (
      (∃ n, pred_at mtr n
                       (λ (_ : retransmit_state) (l : option retransmit_label),
                          l = Some (inr (Ndeliver, mAB)))) ∨
      ¬ ∃ n, pred_at mtr n
                     (λ (_ : retransmit_state) (l : option retransmit_label),
                        l = Some (inr (Ndeliver, mAB)))).
  { apply ExcludedMiddle. }
  destruct H; [eauto|].
  assert (∀ n : nat,
           pred_at mtr n
             (λ (_ : retransmit_state) (l : option retransmit_label),
                l ≠ Some (inr (Ndeliver, mAB)))) as Hneq.
  { intros n. apply pred_at_neg; [done|].
    by eapply not_exists_forall_not in H. }
  clear H.
  assert (∀ n, count_delivers mAB (trace_take n mtr) = 0) as Hdelivers.
  { intros ?. by apply retransmit_trace_delivers_0. }
  assert (∀ x, ∃ n, x < count_sends mAB (trace_take n mtr)) as Hsends.
  { intros ?. destruct Hfair as [Hfair _]. by apply retransmit_trace_sends_grows. }
  destruct Hfair as [Hfair_sched Hfair_network].
  destruct Hfair_network as (f1 & f2 & ? & ? & Hfair_network).
  assert (∃ n : nat, True) as [n _].
  { exists 0. done. }
  specialize (Hsends (f2 $ count_delivers mAB (trace_take n mtr))) as [m H].
  specialize (Hfair_network mAB m).
  destruct Hfair_network as [Hfair_network1 Hfair_network2].
  rewrite Hdelivers in H.
  rewrite Hdelivers in Hfair_network2.
  lia.
Qed.

Lemma Ndeliver_adds_to_buffer msg s bs (tr:mtrace) :
  mtrace_valid (s -[inr (Ndeliver,msg)]-> tr) →
  (trfirst (s -[inr (Ndeliver,msg)]-> tr)).2 !!! (m_destination msg) = bs →
  (trfirst tr).2 !!! (m_destination msg) = (msg :: bs).
Proof.
  intros Hvalid <-.
  simpl.
  pinversion Hvalid; simplify_eq.
  inversion H1; simplify_eq.
  simpl in *.
  rewrite lookup_total_insert.
  done.
Qed.

Lemma retransmit_fair_trace_buffer_grows (mtr : mtrace) n mtr' :
  mtrace_valid mtr →
  (∀ m, m < n → pred_at mtr m (λ _ l, ¬ option_map label_role l = Some $ inl Brole)) →
  after n mtr = Some mtr' →
  suffix ((trfirst mtr).2 !!! saB) ((trfirst mtr').2 !!! saB).
Proof. 
  revert mtr mtr'. 
  induction n as [|n IHn];
    intros mtr mtr' Hvalid Halways Hafter.
  { simpl in *. by simplify_eq. }
  simpl in *.
  destruct mtr as [|s l mtr]; [done|].
  eapply suffix_trans; last first.
  { apply IHn; [| |done]. 
    - eapply (mtrace_valid_after _ mtr 1); [|done]. done.
    - intros. specialize (Halways (S m)). rewrite pred_at_S in Halways.
      apply Halways. lia. }
  punfold Hvalid. inversion Hvalid. simplify_eq.
  inversion H1; simplify_eq; try set_solver.
  - destruct (decide (m_destination msg = saB)) as [->|Hneq].
    + rewrite lookup_total_insert. apply suffix_cons_r. set_solver.
    + by rewrite lookup_total_insert_ne.
  - simpl in *.
    assert (0 < S n) as H0 by lia.
    specialize (Halways 0 H0). rewrite pred_at_0 in Halways. simplify_eq.
Qed.

(* Any fair trace eventually ends in the receive state *)
Lemma retransmit_fair_trace_eventually_Received (mtr : mtrace) :
  infinite_trace mtr →
  (trfirst mtr).1.1 = Start → mtrace_valid mtr → mtrace_fair mtr →
  ∃ n, pred_at mtr n (λ st _, st.1.1 = Received).
Proof.
  intros Hafter Htrfirst Hvalid Hfair.
  assert (∃ n, pred_at mtr n (λ st l, l = Some $ inr (Ndeliver,mAB))) as [n Hn].
  { by apply retransmit_fair_trace_eventually_Ndeliver. }
  rewrite /pred_at in Hn.
  apply (infinite_trace_after' n) in Hafter as [mtr' [Hmtr' Hafter]].
  destruct Hfair as [Hfair1 Hfair2].
  assert (retransmit_fair_scheduling mtr') as Hfair1'.
  { by eapply retransmit_fair_scheduling_after. }
  rewrite Hmtr' in Hn.
  destruct mtr' as [mtr'|]; [done|].
  simplify_eq.
  rewrite /retransmit_fair_scheduling in Hfair1'.
  assert ((pred_at (s -[ inr (Ndeliver, mAB) ]-> mtr') 0
                   (λ δ _, retransmit_role_enabled_model (inl Brole) δ)) ∨
            ¬ pred_at (s -[ inr (Ndeliver, mAB) ]-> mtr') 0
              (λ δ _, retransmit_role_enabled_model (inl Brole) δ)) as Hrole.
  { eapply ExcludedMiddle. }
  destruct Hrole as [Hrole|Hrole]; last first.
  { apply pred_at_neg in Hrole; [|done].
    rewrite /pred_at in Hrole. simpl in *.
    exists n. rewrite /pred_at. rewrite Hmtr'.
    rewrite /retransmit_role_enabled_model in Hrole.
    rewrite /retransmit_live_roles in Hrole.
    rewrite /label_role in Hrole.
    simpl in *.
    destruct s as [[[] s2] s3]; [|done].
    set_solver. }
  apply Hfair1' in Hrole as [m Hm]. simpl in *.
  apply pred_at_or in Hm as [Hm|Hm].
  - exists (n+m).
    rewrite pred_at_sum. rewrite Hmtr'.
    eapply pred_at_impl; eauto.
    intros ?? Hsl. destruct s0; eauto. destruct p; eauto. destruct r; eauto.
    rewrite /retransmit_role_enabled_model in Hsl.
    rewrite /label_role in Hsl. simpl in *.
    rewrite /retransmit_live_roles in Hsl. simpl in *.
    set_solver.
  - assert (∃ bs, (trfirst (s -[ inr (Ndeliver, mAB) ]-> mtr')).2 !!!
                          (m_destination mAB) = bs) as [bs Hbs].
    { by eexists _. }
    assert (after (S n) mtr = Some mtr') as Hmtr'2.
    { replace (S n) with (n + 1) by lia. rewrite after_sum'.
      rewrite Hmtr'. simpl. done. }
    apply Ndeliver_adds_to_buffer in Hbs; last first.
    { by eapply mtrace_valid_after. }
    destruct m as [|m]; [done|].
    rewrite pred_at_S in Hm.
    assert (∃ n', pred_at mtr' n' (λ _ ℓ,
                                     option_map label_role ℓ = Some $ inl Brole)).
    { exists m. done. }
    apply trace_eventually_until in H as [n' [Hn' Hn'']].
    exists (n+(S $ S n')).
    rewrite pred_at_sum. rewrite Hmtr'.
    rewrite pred_at_S.
    assert (pred_at mtr' n' (λ (s : retransmit_state) (_ : option retransmit_label),
             suffix ((trfirst mtr').2 !!! saB) (s.2 !!! saB))).
    { assert (∃ mtr'', after n' mtr' = Some mtr'').
      { apply (infinite_trace_after' (S n')) in Hafter as [mtr'' [Hmtr'' _]].
        simpl in Hmtr''. eauto. }
      destruct H as [mtr'' Hmtr''].
      eapply (retransmit_fair_trace_buffer_grows _ _ mtr'') in Hn'' as Hbs';
        try done; last first.
      { by eapply mtrace_valid_after. }
      rewrite /pred_at.
      rewrite Hmtr''.
      destruct mtr''; done. }
    replace (S n') with (n' + 1) by lia.
    rewrite pred_at_sum.
    rewrite /pred_at in H. rewrite /pred_at in Hn'.
    destruct (after n' mtr') eqn:Heqn; [|done].
    assert (mtrace_valid t) as Hvalid'.
    { eapply mtrace_valid_after; [done|]. by eapply mtrace_valid_after. }
    destruct t; [naive_solver|].
    rewrite pred_at_S. rewrite /pred_at. simpl.
    simplify_eq.
    rewrite Hbs in H.
    inversion Hn'.
    assert (∃ a, ℓ = inl (Brole,a)) as [a ->].
    { destruct ℓ; try naive_solver. destruct r; try naive_solver. }
    punfold Hvalid'. inversion Hvalid'. simplify_eq.
    inversion H3.
    + destruct s0 as [[]]. simplify_eq. simpl in *.
      destruct H as [? H].
      rewrite H in H6. apply app_eq_nil in H6. set_solver.
    + simpl in *. simplify_eq. destruct t=> /=; simpl in *; simplify_eq; set_solver.
Qed.

(* A trace starting in the receive role has partially terminated for the Brole *)
Lemma retransmit_fair_traces_terminate_aux (mtr: mtrace) :
  (trfirst mtr).1.1 = Received → retransmit_terminating_role (inl Brole) mtr.
Proof.
  intros Htrfirst.
  exists 0. rewrite /pred_at=> /=. simpl in *.
  destruct mtr as [s|s mtr].
  - rewrite /pred_at=> /=. simpl in *. destruct s as [[??]?]. simpl in *.
    simplify_eq. rewrite /retransmit_live_roles. simpl in *.
    case_decide; set_solver.
  - rewrite /pred_at=> /=. simpl in *. destruct s as [[??]?]. simpl in *.
    simplify_eq. rewrite /retransmit_live_roles. simpl in *.
    case_decide; set_solver.
Qed.

(* Any fair trace terminates on role B *)
Lemma retransmit_fair_traces_terminate (mtr : mtrace) :
  (trfirst mtr).1.1 = Start → mtrace_valid mtr → mtrace_fair mtr →
  retransmit_terminating_role (inl Brole) mtr.
Proof.
  intros ???.
  assert (infinite_trace mtr ∨ ¬ infinite_trace mtr) as Hafter.
  { by apply ExcludedMiddle. }
  destruct Hafter as [Hafter|Hafter]; last first.
  { apply not_forall_exists_not in Hafter as [n Hafter].
    destruct (after n mtr) eqn:Heqn; [by naive_solver|].
    rewrite /retransmit_terminating_role. exists n.
    left. done. }
  assert (∃ n, pred_at mtr n (λ st _, st.1.1 = Received)) as [n Hn].
  { by apply retransmit_fair_trace_eventually_Received. }
  rewrite /pred_at in Hn.
  assert (∃ mtr', after n mtr = Some mtr') as [mtr' Hmtr'].
  { destruct (after n mtr) as [mtr'|]; [|done]. by exists mtr'. }
  rewrite Hmtr' in Hn.
  assert ((trfirst mtr').1.1 = Received).
  { by destruct mtr'. }
  assert (retransmit_terminating_role (inl Brole) mtr') as [m Hterminates].
  { by apply retransmit_fair_traces_terminate_aux. }
  exists (m+n). rewrite pred_at_sum'. rewrite after_sum. by rewrite Hmtr'.
Qed.
