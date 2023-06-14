From trillium.prelude Require Import finitary classical_instances.
From aneris.prelude Require Import gset_map misc sig_gset.
From aneris.aneris_lang Require Import state_interp adequacy.
From aneris.examples.consensus Require Import
     paxos_model paxos_prelude paxos_client paxos_runner.
From aneris.aneris_lang Require Import tactics proofmode.

Definition init_state := {|
  state_heaps :=  {["system" := ∅ ]};
  state_sockets := {["system" := ∅ ]};
  state_ms := ∅; |}.

Definition socket_interp `{!paxosG Σ params} sa : socket_interp Σ :=
  match sa with
  | SocketAddressInet "p1" 80
  | SocketAddressInet "p2" 80 => proposer_si
  | SocketAddressInet "a1" 80
  | SocketAddressInet "a2" 80
  | SocketAddressInet "a3" 80 => acceptor_si
  | SocketAddressInet "l1" 80
  | SocketAddressInet "l2" 80 => learner_si
  | SocketAddressInet "c" 80 => client_si
  | _ => λ msg, ⌜True⌝
  end%I.

Definition runner_expr := mkExpr "system" (runner 41 42).

Program Definition a1 : Acceptor := a1_addr ↾ _.
Next Obligation. set_solver. Qed.
Program Definition a2 : Acceptor := a2_addr ↾ _.
Next Obligation. set_solver. Qed.
Program Definition a3 : Acceptor := a3_addr ↾ _.
Next Obligation. set_solver. Qed.
Open Scope nat_scope.

Lemma paxos_res_alloc `{anerisPreG Σ (Paxos_model runner_topo), !paxosPreG Σ runner_topo} :
  ⊢ |==> ∃ (γM γP γmv γmb : gname),
   own γM (● (∅ : gset Message)) ∗
   own γM (◯ (∅ : gset Message)) ∗
   own γP (ballot.pending_class 0 2 0) ∗
   own γP (ballot.pending_class 1 2 0) ∗
   gen_heap_light_ctx γmv (fn_to_gmap Acceptors' (λ _, (None : option (Ballot * Value)))) ∗
   gen_heap_light_ctx γmb (fn_to_gmap Acceptors' (λ _, (None : option Ballot))) ∗
   [∗ set] a ∈ acceptors, ∃ prf, lmapsto γmb (a ↾ prf : Acceptor) 1 (None : option Ballot) ∗
                              lmapsto γmv (a ↾ prf : Acceptor) 1 (None : option (Ballot * Value)).
Proof.
  iMod (own_alloc (● (∅ : gset Message) ⋅ ◯ (∅ : gset Message))) as (γM) "HM".
  { by apply auth_both_valid. }
  iDestruct (own_op with "HM") as "[HM HM']".
  iMod (own_alloc (pending_all)) as (γP) "Hpend"; [done|].
  rewrite (pending_all_split_classes 2) /=; [|lia].
  rewrite union_empty_r_L.
  iPoseProof (big_opS_own with "Hpend") as "Hpend"; [set_solver|].
  iDestruct (big_sepS_union with "Hpend") as "[Hpend0 Hpend1]"; [set_solver|].
  iPoseProof (big_sepS_singleton (λ y, own _ _)%I with "Hpend0") as "Hpend0".
  iPoseProof (big_sepS_singleton (λ y, own _ _)%I with "Hpend1") as "Hpend1".
  iMod (gen_heap_light_init (L := Acceptor) (V := option Ballot) ∅) as (γmb) "Hmb_ctx".
  iMod (gen_heap_light_init (L := Acceptor) (V := option (Ballot * Value)) ∅) as (γmv) "Hmv_ctx".
  iMod (gen_heap_light_alloc_gen _ (fn_to_gmap Acceptors' (λ _, None))
          with "Hmv_ctx") as "[Hmv_ctx Hmvs]".
  { apply map_disjoint_empty_r. }
  iMod (gen_heap_light_alloc_gen _ (fn_to_gmap Acceptors' (λ _, None))
          with "Hmb_ctx") as "[Hmb_ctx Hmbs]".
  { apply map_disjoint_empty_r. }
  iEval (rewrite right_id) in "Hmv_ctx Hmb_ctx".
  assert (fn_to_gmap Acceptors' (λ _, None) =
         ({[ a1 := None; a2 := None; a3 := None]} : _ _ (option (Ballot * Value)))) as HmvE.
  { apply map_eq. by set_unfold. }
  assert (fn_to_gmap Acceptors' (λ _, None) =
         ({[ a1 := None; a2 := None; a3 := None]} : gmap Acceptor (option Ballot))) as HmbE.
  { apply map_eq. by set_unfold. }
  rewrite {2}HmvE {2}HmbE.
  iModIntro. iExists _, _, _, _. iFrame.
  iEval (rewrite !big_sepM_insert //) in "Hmvs Hmbs".
  iDestruct "Hmvs" as "(Hv1 & Hv2 & Hv3 & _)".
  iDestruct "Hmbs" as "(Hb1 & Hb2 & Hb3 & _)".
  iApply (big_sepS_delete _ _ a1_addr); [set_solver|].
  iSplitL "Hv1 Hb1"; [iExists _; iFrame|].
  iApply (big_sepS_delete _ _ a2_addr); [set_solver|].
  iSplitL "Hv2 Hb2"; [iExists _; iFrame|].
  iApply (big_sepS_delete _ _ a3_addr); [set_solver|].
  iSplitL "Hv3 Hb3"; [iExists _; iFrame|].
  clear HmvE HmbE.
  assert (acceptors ∖ {[a1_addr]} ∖ {[a2_addr]} ∖ {[a3_addr]} = (∅ : gset _))
    as -> by set_solver.
  done.
Qed.

(** * Safety theorem for Paxos  *)
Notation messages_sent_from := state_interp.messages_sent_from.

Definition messages_sent_from_parties ms : message_soup :=
  filter (λ m, m.(m_sender) ∈ acceptors ∪ proposers) ms.

Definition simulates
           (ex  : execution_trace aneris_lang)
           (atr : auxiliary_trace (aneris_to_trace_model (Paxos_model runner_topo)))
  : Prop :=
  trace_steps (λ δ _ δ', δ = δ' ∨ PNext δ δ') atr ∧
  (* sent message history [smh] of [trace_last atr] *)
  let '(_, smh) := trace_messages_history ex in
  (* Paxos model state [s] of [trace_last atr] *)
  let δ := trace_last atr in
  messages_model_agree δ.(msgs) (messages_sent_from_parties smh).

Definition aux_init := PInit : Paxos_model runner_topo.

Import RecordSetNotations.

(* TODO: move *)
Definition int_deser : string → option Z := ZOfString.
Definition nat_deser : string → option nat := λ s, Z.to_nat <$> int_deser s.
Definition inl_deser {A} (f : string → option A) (s : string) :=
  let tag := substring 0 2 s in
  let rest := substring 2 (String.length s - 2) s in
  if bool_decide (tag = "L_") then f rest else None.
Definition inr_deser {B} (f : string → option B) (s : string) : option B :=
  let tag := substring 0 2 s in
  let rest := substring 2 (String.length s - 2) s in
  if bool_decide (tag = "R_") then f rest else None.
Definition prod_deser {A B} (f : string → option A) (g : string → option B)
           (s : string) : option (A * B) :=
  i ← index 0 "_" s;
  len ← nat_deser (substring 0 i s);
  let s1 := substring (i + 1) len s in
  let s2 := substring (i + 1 + len)
                      (String.length s - (i + 1 + len)) s in
  a ← f s1;
  b ← g s2;
  mret (a, b).
Definition option_deser {A} (f : string → option A) (s : string) : option (option A) :=
  let tag := substring 0 2 s in
  let rest := substring 2 (String.length s - 2) s in
  if bool_decide (tag = "L_") then Some None
  else (if bool_decide (tag = "R_") then Some (f rest)
        else None).

Definition msg1a_deser (s : string) : option nat := inl_deser nat_deser s.
Definition msg2a_deser (s : string) : option (nat * Z) :=
  inr_deser (prod_deser nat_deser int_deser) s.

Lemma msg1a_serdeser bal :
  msg1a_deser (msg1a_ser bal) = Some bal.
Proof.
  rewrite /msg1a_ser /msg1a_deser.
  rewrite /inl_deser /nat_deser /int_ser_str /inl_ser_str /int_deser.
  replace 2 with (String.length "L_") by done.
  rewrite substring_0_length_append /=.
  rewrite Nat.sub_0_r substring_0_length.
  rewrite ZOfString_inv /=.
  f_equal. lia.
Qed.

Lemma msg2a_serdeser bal val :
  msg2a_deser (msg2a_ser bal val) = Some (bal, `val).
Proof.
  rewrite /msg2a_deser /msg2a_ser.
  rewrite /inr_deser /inr_ser_str.
  replace 2 with (String.length "R_") by done.
  rewrite substring_0_length_append /=.
  rewrite Nat.sub_0_r substring_0_length.
  rewrite /prod_deser /prod_ser_str.
  erewrite (index_0_append_char); [|done|]; last first.
  { apply valid_tag_stringOfZ. }
  simpl.
  rewrite substring_0_length_append.
  rewrite /nat_deser /int_deser.
  rewrite ZOfString_inv /=.
  rewrite substring_add_length_app /=.
  rewrite Nat2Z.id.
  rewrite substring_0_length_append.
  rewrite /int_ser_str.
  rewrite ZOfString_inv /=.
  rewrite -Nat.add_assoc substring_add_length_app /=.
  rewrite !length_app /=.
  match goal with
    | |- context [substring _ ?X _] =>
      replace X with (String.length (StringOfZ (`val))); last first
  end.
  { simpl. lia. }
  rewrite substring_length_append.
  rewrite ZOfString_inv /=.
  rewrite Nat2Z.id //.
Qed.

Definition phase1a_states (c : state) extr (s : PaxosState) : list PaxosState :=
  msg ← elements c.(state_ms) ++ elements (trace_messages_history extr).2;
  bal ← if msg1a_deser msg.(m_body) is Some n then [n] else [];
  mret (s <| msgs ::= (.∪ {[msg1a bal]}) |>).

Definition phase1b_states s : list PaxosState :=
  m ← elements s.(msgs);
  if m is msg1a bal then
    a ← elements Acceptors';
    mret
      (s <| maxBal ::= λ mb, <[a := Some bal]>mb |>
         <| msgs   ::= λ ms, ms ∪ {[msg1b a bal (s.(maxVal) a)]} |>)
  else [].

Definition Values' := sig_gset_gset Values.
Definition phase2a_states (c : state) extr (s : PaxosState): list PaxosState :=
  msg ← elements c.(state_ms) ++ elements (trace_messages_history extr).2;
  m ← if msg2a_deser msg.(m_body) is Some (bal, v) then [(bal, v)] else [];
  val ← elements Values';
  mret (s <| msgs ::= λ ms, ms ∪ {[msg2a m.1 val]} |>).

Definition phase2b_states (c : state) (s : PaxosState) : list PaxosState :=
  m ← elements s.(msgs);
  if m is msg2a bal val then
    a ← elements Acceptors';
    mret
      (s <| maxBal ::= λ mb, <[a := Some bal]>mb |>
         <| maxVal ::= λ mb, <[a := Some (bal, val)]>mb |>
         <| msgs   ::= λ ms, ms ∪ {[msg2b a bal val]} |>)
  else [].

Definition steppable c extr s :=
  map (λ s, (s, tt)) (s :: phase1a_states c extr s ++ phase1b_states s ++
   phase2a_states c extr s ++ phase2b_states c s).

Local Hint Extern 4 => unfold Acceptors' : core.
Local Hint Extern 4 => unfold Values' : core.

#[local] Instance model_eqdec topo:
  EqDecision (Paxos_model topo).
Proof. intros ??. apply make_decision. Qed.

Local Lemma incl_messages_sent M (c' : cfg _) extr:
  M ∈ messages_sent_from_parties
    (gset_of_gmultiset (state_ms c'.2)
             ∖ gset_of_gmultiset (state_ms (trace_last extr).2)
             ∪ (trace_messages_history extr).2) ->
  M ∈ elements (state_ms c'.2) ++ elements (trace_messages_history extr).2.
Proof.
  rewrite /messages_sent_from_parties /gset_of_gmultiset elem_of_filter.
  intros [_ [Hin|Hin]%elem_of_union]; apply elem_of_app; [left|right; set_solver].
  apply gmultiset_elem_of_elements.
  apply gmultiset_elem_of_dom.
  eapply elem_of_weaken; [apply Hin|].
  multiset_solver.
Qed.

Lemma simulates_finitary `{anerisPreG Σ (Paxos_model runner_topo) } :
  rel_finitary (sim_rel simulates).
Proof.
  intros extr auxtr c' oζ.
  assert (∀ x : PaxosState * (),
   ProofIrrel
     ((λ '(δ', ℓ),
         valid_state_evolution (extr :tr[oζ]: c') (auxtr :tr[ℓ]: δ')
         ∧ simulates (extr :tr[ oζ ]: c') (auxtr :tr[ ℓ ]: δ')) x)).
  { intros ?. apply make_proof_irrel. }
  apply finite_smaller_card_nat.
  Unshelve.
  eapply (in_list_finite (steppable c'.2 extr (trace_last auxtr))).
  rewrite /simulates /messages_model_agree /=.
  intros [s []] (Hse & Hsteps & Hsim1 & Hsim2).
  eapply elem_of_list_fmap. exists s; split =>//.
  simpl in Hse.
  destruct Hse as [-> | Hse]; first set_solver.
  inversion Hse as [ | | | ????? Hneg Hnext ];
    simplify_eq; apply elem_of_cons; right; rewrite !elem_of_app.
  - left.
    apply elem_of_list_bind.
    destruct (Hsim1 (msg1a bal) ltac:(set_solver)) as (M & Him & Hin).
    exists M. split; last first.
    { rewrite /messages_sent_from_parties in Hin. by apply incl_messages_sent. }
    destruct Him as (?&?& ->). simpl. rewrite msg1a_serdeser /=. set_solver.
  - right. left.
    apply elem_of_list_bind. eexists. split; last first.
    { apply elem_of_elements. eassumption. }
    simpl. apply elem_of_list_bind. exists a. split=>//; first by apply elem_of_list_ret.
    apply elem_of_elements. apply elem_of_sig_gset_gset. by destruct a.
  - do 2 right. left.
    apply elem_of_list_bind.
    destruct (Hsim1 (msg2a bal val) ltac:(set_solver)) as (M & Him & Hin).
    exists M. split; last first.
    { rewrite /messages_sent_from_parties in Hin. by apply incl_messages_sent. }
    destruct Him as (?&?& ->). simpl. rewrite msg2a_serdeser /=.
    list_simplifier. apply elem_of_list_bind. exists val. split; first set_solver.
    apply elem_of_elements. apply elem_of_sig_gset_gset. by destruct val.
  - do 3 right. apply elem_of_list_bind. eexists. split; last first.
    { apply elem_of_elements. eassumption. }
    simpl. apply elem_of_list_bind. exists a. split; first set_solver.
    apply elem_of_elements. apply elem_of_sig_gset_gset. by destruct a.
Qed.

(** * Simulation theorem for Paxos *)
Theorem paxos_simulation :
  continued_simulation
    simulates
    {tr[([runner_expr], init_state)]} {tr[aux_init]} ∧
    safe runner_expr init_state.
Proof.
  set (Σ := #[anerisΣ (Paxos_model runner_topo); (paxosΣ runner_topo)]).
  assert (anerisPreG Σ (Paxos_model runner_topo)) as HPreG by apply _.
  unfold safe, runner_expr.
  apply (simulation_adequacy Σ (Paxos_model runner_topo) NotStuck ips ∅ addrs ∅ ∅).
  { set_solver. }
  { set_solver. }
  { apply simulates_finitary. }
  { set_solver. }
  { set_solver. }
  { set_solver. }
  { set_solver. }
  iIntros (anG).
  iMod paxos_res_alloc as
      (γM γP γmv γmb) "(HM & HM' & Hpend0 & Hpend1 & Hmv_ctx & Hmb_ctx & Has)".
  set (paxosGI := Build_paxosG Σ runner_topo _ γM _ γP _ γmb _ γmv).
  iIntros "!#".
  iExists (λ v, ∃ w, ⌜v = mkVal "system" w⌝ ∗ (λ _, True) w)%I.
  iIntros "Hf Hhist ? #Hnode _ _ _ _ _ Hfrag".
  iDestruct (big_sepS_union with "Hhist") as "[Hhist Hclient]"; [set_solver|].
  iPoseProof (big_sepS_singleton with "Hclient") as "Hclient".
  iDestruct (big_sepS_union with "Hhist") as "[Hhist Hlearners]"; [set_solver|].
  iDestruct (big_sepS_union with "Hhist") as "[Hacceptors Hproposers]"; [set_solver|].
  iMod (paxos_inv_alloc with "[$Hfrag $Hmb_ctx $Hmv_ctx $Hacceptors
                               $Hproposers $HM $HM']") as "#Hinv".
  iModIntro.
  iSplit; [done|].
  iSplitL.
  { 
    iApply (aneris_wp_lift with "Hnode").
    rewrite /addrs.
    iDestruct (unallocated_split with "Hf") as "[Hf Hf_caddr]"; [set_solver|].
    iDestruct (unallocated_split with "Hf") as "[Hf Hf_learners]"; [set_solver|].
    iDestruct (unallocated_split with "Hf") as "[Hf_acceptors Hf_proposers]";
      [set_solver|].
    iApply (aneris_wp_socket_interp_alloc_singleton client_si with "Hf_caddr").
    iIntros "#Hcaddr_si".
    iApply (aneris_wp_socket_interp_alloc learner_si with "Hf_learners").
    iIntros "#Hleaners_si".
    iApply (aneris_wp_socket_interp_alloc acceptor_si with "Hf_acceptors").
    iIntros "#Hacceptors_si".
    iApply (aneris_wp_socket_interp_alloc proposer_si with "Hf_proposers").
    iIntros "#Hproposers_si".
    iPoseProof (runner_spec with "[-]") as "Hspec".
    { iFrame "#∗".
      rewrite !big_sepS_union ?big_sepS_singleton //; try set_solver.
      rewrite /pending_class -length_elements.
      by iFrame. }
    iApply ("Hspec" with "[]"); auto. }
  iIntros (ex atr c' Hval Hexst Hauxst Hexend Hsim Hnotstuck) "Hsi _".
  iInv (paxosN) as ([c δ]) ">(Hfrag & Hmauth & HmaxBal & HmaxVal & Hmcoh & HbI)" "_".
  iMod (fupd_mask_subseteq ∅) as "_"; [set_solver|].
  iModIntro.
  rewrite /simulates /=.
  iSplit.
  { iDestruct "Hsi" as "(?&?&?&%Hevol&?)". iPureIntro.
    destruct atr as [|atr]; [econstructor|].
    econstructor; [done|done|].
    inversion Hval; simplify_eq.
    eapply Hsim; by econstructor. }
  iDestruct "Hmcoh" as (F Ts) "(Has & Hps & % & [%Hmsgs %HTs])".
  iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as "%Hmdl".
  destruct (trace_messages_history ex) eqn:Heq,
           (trace_last atr) eqn:Heq'.
  rewrite Heq'. simplify_eq. iSplit.
  - iIntros (M HM).
    destruct (Hmsgs M HM) as (m' &?& (a & Hin%elem_of_union & Hm')%elem_of_gset_flat_map_2).
    iExists _. iSplit; [done|].
    rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def.
    destruct Hin.
    + iDestruct (big_sepS_elem_of _ _ a with "Has") as (R) "(% & Ha & ?)"; [done|].
      iDestruct (aneris_state_interp_sent_mapsto_agree with "Ha [Hsi]")
        as %Hsent.
      { rewrite -Heq -Heq' //. }
      iPureIntro.
      rewrite -Hsent in Hm'.
      apply elem_of_filter.
      apply elem_of_filter in Hm' as [<-%elem_of_singleton Hm'].
      rewrite Heq in Hm'.
      split; [|done]. by apply elem_of_union_l.
    + iDestruct (big_sepS_elem_of _ _ a with "Hps") as (R) "(% & Hp & ?)"; [done|].
      iDestruct (aneris_state_interp_sent_mapsto_agree with "Hp [Hsi]")
        as %Hsent.
      { rewrite -Heq -Heq' //. }
      iPureIntro.
      rewrite -Hsent in Hm'.
      apply elem_of_filter.
      apply elem_of_filter in Hm' as [<-%elem_of_singleton Hm'].
      rewrite Heq in Hm'.
      split; [|done]. by apply elem_of_union_r.
  - rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def.
    iIntros (msg [[? | ?]%elem_of_union Hin]%elem_of_filter).
    + iDestruct (big_sepS_elem_of _ _ (m_sender msg) with "Has")
        as (R) "(% & Hsndr & ?)"; [done|].
      iDestruct (aneris_state_interp_sent_mapsto_agree with "Hsndr [Hsi]")
        as %Hsent.
      { rewrite -Heq -Heq' //. }
      iPureIntro. apply HTs.
      eapply elem_of_gset_flat_map_1.
      { by apply elem_of_union_l. }
      rewrite -Hsent. apply elem_of_filter.
      split; [by apply elem_of_singleton|]. rewrite Heq //.
    + iDestruct (big_sepS_elem_of _ _ (m_sender msg) with "Hps")
        as (R) "(% & Hsndr & ?)"; [done|].
      iDestruct (aneris_state_interp_sent_mapsto_agree with "Hsndr [Hsi]")
        as %Hsent.
      { rewrite -Heq -Heq' //. }
      iPureIntro. apply HTs.
      eapply elem_of_gset_flat_map_1.
      { by apply elem_of_union_r. }
      rewrite -Hsent. apply elem_of_filter.
      split; [by apply elem_of_singleton|]. rewrite Heq //.
Qed.

Implicit Types δ : (aneris_to_trace_model (Paxos_model runner_topo)).

Definition ChosenImpl (s : state) (v : Value) :=
  ∃ b Q,
    QuorumA Q ∧
    ∀ a, a ∈ Q →
         ∃ (l : Learner),
           mkMessage (`a) (`l) (msg2b_ser b v) ∈ s.(state_ms).

Corollary paxos_correct_impl v1 v2 tp σ ex:
  trace_starts_in ex ([runner_expr], init_state) →
  trace_ends_in ex (tp, σ) →
  valid_exec ex →
  ChosenImpl σ v1 → ChosenImpl σ v2 → v1 = v2.
Proof.
  intros Hstart Hends Hval (b1 & Q1 & HQ1 & Ha1) (b2 & Q2 & HQ2 & Ha2).
  pose proof paxos_simulation as [Hsim _].
  move: Hsim=> /simulation_does_continue Hexec.
  destruct (Hexec ex) as [atr [Hδ Hcsim]]; [done|done|].
  pose proof (continued_simulation_rel _ _ _ Hcsim) as (Hsteps & Hsim).
  unfold simulates in Hsim.
  destruct (trace_messages_history ex) eqn:HeqH, (trace_last atr) eqn:HeqM.
  destruct Hsim as [? Hsent].
  apply trace_steps_rtc_2 in Hsteps.
  rewrite Hδ in Hsteps.
  eapply paxos_correct.
  - eapply rtc_destutter; eauto. eapply rtc_subrel =>//.
    by intros x y [??].
  - exists b1, Q1. split; [done|].
    intros a' Ha'. rewrite /VotedFor.
    destruct (Ha1 a' Ha') as (l1 & Hm1).
    replace σ with ((trace_last ex).2) in Hm1; last by erewrite last_eq_trace_ends_in; eauto.
    apply trace_messages_history_includes_last in Hm1.
    edestruct (Hsent (mkMessage (`a') (`l1) (msg2b_ser b1 v1)))
      as (M & HinM & <-%is_mdl_message_2b_inv).
    { apply elem_of_filter. simpl. split; [apply elem_of_union_l; auto|].
      by rewrite HeqH in Hm1. }
    rewrite HeqM //.
  - exists b2, Q2. split; [done|].
    intros a' Ha'. rewrite /VotedFor.
    destruct (Ha2 a' Ha') as (l2 & Hm2).
    replace σ with ((trace_last ex).2) in Hm2; last by erewrite last_eq_trace_ends_in; eauto.
    apply trace_messages_history_includes_last in Hm2.
    edestruct (Hsent (mkMessage (`a') (`l2) (msg2b_ser b2 v2)))
      as (M & HinM & <-%is_mdl_message_2b_inv).
    { apply elem_of_filter. simpl.
      split; [apply elem_of_union_l; auto|].
      by rewrite HeqH in Hm2. }
    rewrite HeqM //.
Qed.
