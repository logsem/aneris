From trillium.prelude Require Import finitary classical_instances.
From aneris.prelude Require Import gset_map misc.
From aneris.aneris_lang Require Import state_interp adequacy.
From aneris.examples.transaction_commit Require Import
     two_phase_prelude two_phase_runner_proof.

Definition init_state := {|
  state_heaps :=  {["system" := ∅ ]};
  state_sockets := {["system" := ∅ ]};
  state_ports_in_use :=
    <["tm" := ∅ ]> $ <["rm.01" := ∅ ]> $
    <["rm.02" := ∅ ]> $ <["rm.03" := ∅ ]> $ ∅;
  state_ms := ∅; |}.

Definition socket_interp `{!tcG Σ} sa : socket_interp Σ :=
  match sa with
  | SocketAddressInet "tm" 80 => @tm_si my_topo _ _
  | SocketAddressInet "rm.01" 80
  | SocketAddressInet "rm.02" 80
  | SocketAddressInet "rm.03" 80 => @rm_si my_topo _ _
  | _ => λ msg, ⌜True⌝
  end%I.

Definition runner_expr := mkExpr "system" runner.

Local Instance: ∀ x y z, ProofIrrel (TC_model x y z).
Proof. intros; apply make_proof_irrel. Qed.

Lemma tc_model_finitary rms :
  aneris_model_rel_finitary (TC_model rms).
Proof.
  intros st; simpl in *.
  apply finite_smaller_card_nat.
  eapply (in_gset_finite
            (gset_flat_map (λ rm,
                            {[ <[ rm := PREPARED ]>st;
                               <[ rm := COMMITTED ]>st;
                               <[ rm := ABORTED ]>st]}) (dom st))).
  intros st'; inversion 1 as [| |? ? Hsome].
  - eapply (elem_of_gset_flat_map_1 _ _ rm); [|set_solver].
    rewrite elem_of_dom; eauto.
  - eapply (elem_of_gset_flat_map_1 _ _ rm); [|set_solver].
    rewrite elem_of_dom; eauto.
  - eapply (elem_of_gset_flat_map_1 _ _ rm); [|set_solver].
    rewrite elem_of_dom. destruct Hsome; eauto.
Qed.

(** * Safety theorem for Two-Phase Commit  *)
Theorem tpc_safe :
  safe runner_expr init_state.
Proof.
  set (Σ := #[anerisΣ (TC_model rms); tcΣ]).
  eapply (@adequacy_safe Σ (TC_model rms) _ _ ips addrs addrs ∅ ∅ ∅);
    [| |done|set_solver|set_solver|set_solver|done|done|done].
  { apply tc_model_finitary. }
  iIntros (anG).
  iMod pending_alloc as (γ) "Hpend".
  iMod (gen_mono_heap_init rms (WORKING : rm_stateO)) as (?) "He".
  rewrite big_sepS_sep. iDestruct "He" as "[He _]".
  iDestruct (big_sepS_impl _
    (λ rm, rm ↦●{1/2} (WORKING : rm_stateO) ∗
           rm ↦●{1/2} (WORKING : rm_stateO))%I with "He []") as "He".
  { iIntros "!#" (??) "[? ?]". iFrame. }
  rewrite big_sepS_sep. iDestruct "He" as "[Hwork1 Hwork2]".
  set (tcGI := MkTcG Σ _ _ γ).
  iIntros "!#". iExists socket_interp.
  iIntros "? Hsi Hhist Hfrag ? #? _ _ _ _ _".
  rewrite (big_sepS_delete _ addrs tm_addr); [|set_solver].
  rewrite (big_sepS_delete _ addrs tm_addr); [|set_solver].
  iDestruct "Hsi" as "[? Hrms_si]". iDestruct "Hhist" as "[? Hhist]".
  assert (addrs ∖ {[tm_addr]} = rms) as -> by set_solver.
  iApply fupd_wp.
  iMod (@tc_inv_alloc my_topo _ anG tcGI with "[$Hfrag $Hhist $Hwork2]")
    as "#Hinv".
  iModIntro.
  (* TODO: lift the adeaucy theorems to aneris_wp *)
  iPoseProof (runner_spec with "[-]") as "Hspec".
  { iFrame "∗#". rewrite !big_sepS_union ?big_sepS_singleton //; set_solver. }
  rewrite aneris_wp_unfold /aneris_wp_def /=.
  iModIntro.
  iApply wp_wand_l.
  iSplitR; last first.
  { iApply ("Hspec" with "[]"); auto. }
  auto.
Qed.

Notation state_message_coh := (@state_message_coh my_topo).
Notation state_to_msg := (@state_to_msg my_topo).
(* TODO: fix name clash (network.v and state_interp.v) *)
Notation messages_sent_from := state_interp.messages_sent_from.

Definition M := aneris_to_trace_model (TC_model rms).

Definition simulates
           (ex  : execution_trace aneris_lang)
           (atr : auxiliary_trace M) : Prop :=
  trace_steps (λ δ _ δ', δ = δ' ∨ TCNext rms δ δ') atr ∧
  (* message history [mh] of [ex] *)
  let mh       := trace_messages_history ex in
  (* TPC model state [rmState] of [trace_last atr] *)
  let rmState : TC_model rms := trace_last atr in
  ∀ rm st,
    rm ∈ rms →
    (* if resource manager [rm] is in state [st] in the model, [rm] must have
       sent a message signifying this transition *)
    (rmState !! rm = Some st →
       state_message_coh rm st (messages_sent_from ({[rm]}) mh)) ∧
    (* if the resource manager [rm] has sent a message signifying transitioning
       to [st], the model must be at least in state [st] *)
    (state_message_coh rm st (messages_sent_from {[rm]} mh) →
       ∃ st', rm_step_rtc st st' ∧ rmState !! rm = Some st').

Definition aux_init : M := TCInit rms.

(** * Simulation theorem for Two-Phase Commit *)
Theorem tpc_simulation :
  continued_simulation
    simulates
    {tr[([runner_expr], init_state)]} {tr[aux_init]}.
Proof.
  set (Σ := #[anerisΣ (TC_model rms); tcΣ]).
  assert (anerisPreG Σ (TC_model rms)) as HPreG by apply _.
  eapply (simulation_adequacy Σ (TC_model rms) NotStuck ips ∅ addrs addrs ∅ ∅ (λ _, True));
    [|done|set_solver..|].
  { apply aneris_sim_rel_finitary, tc_model_finitary. }
  iIntros (anG).
  iMod pending_alloc as (γ) "Hpend".
  iMod (gen_mono_heap_init rms (WORKING : rm_stateO)) as (?) "He".
  rewrite big_sepS_sep. iDestruct "He" as "[He _]".
  iDestruct (big_sepS_impl _
    (λ rm, rm ↦●{1/2} (WORKING : rm_stateO) ∗
           rm ↦●{1/2} (WORKING : rm_stateO))%I with "He []") as "He".
  { iIntros "!#" (??) "[? ?]". iFrame. }
  rewrite big_sepS_sep. iDestruct "He" as "[Hwork1 Hwork2]".
  set (tcGI := MkTcG Σ _ _ γ).
  iIntros "!#".
  iExists (* (λ _ atr, ⌜trace_steps (λ δ _ δ', δ = δ' ∨ TCNext rms δ δ') atr⌝%I) *)
    (λ v, ∃ w, ⌜v = mkVal "system" w⌝ ∗ (λ _, True) w)%I, socket_interp.
  iIntros "? Hsi Hhist ? #? _ _ _ _ _ Hfrag".
  rewrite (big_sepS_delete _ addrs tm_addr); [|set_solver].
  rewrite (big_sepS_delete _ addrs tm_addr); [|set_solver].
  iDestruct "Hsi" as "[? Hrms]". iDestruct "Hhist" as "[? Hhist]".
  assert (addrs ∖ {[tm_addr]} = rms) as -> by set_solver.
  iMod (@tc_inv_alloc my_topo _ anG tcGI with "[$Hfrag $Hhist $Hwork2]")
    as "#Hinv".
  iModIntro.
  iSplit; [done|].
  iSplitL.
  { (* TODO: lift the adeaucy theorems to aneris_wp *)
    iPoseProof (runner_spec with "[-]") as "Hspec".
    { iFrame "∗#". rewrite !big_sepS_union ?big_sepS_singleton //; set_solver. }
    rewrite aneris_wp_unfold /aneris_wp_def /=.
    iApply wp_wand_l.
    iSplitR; auto.
    iApply ("Hspec" with "[]"); auto. }
  iIntros (ex atr c Hval Hexst Hauxst Hexend Hauxend Hstuck) "Hsi _".
  iInv tcN as (mdl) ">[Hfrag HrmI]" "_".
  iMod (fupd_mask_subseteq ∅) as "_"; [set_solver|].
  iModIntro.
  iSplit.
  { iDestruct "Hsi" as "(?&?&?&%Hevol&?)". iPureIntro.
    unfold valid_state_evolution in Hevol.
    destruct atr as [|atr]; [econstructor|].
    econstructor; [done|done|].
    inversion Hval; simplify_eq.
    eapply (Hauxend _ _ _ l); by econstructor. }
  rewrite /simulates /rm_inv /=.
  iIntros (rm st Hin).
  rewrite (big_sepS_delete _ _ rm); [|set_solver].
  iDestruct "HrmI" as "[(% & % & %st'' & %Hmdlrm & Hst' & Htok & Hrm & [% %]) _]".
  rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def.
  iDestruct "Hrm" as "(_ & Hrm & _) /=".
  iDestruct (aneris_state_interp_sent_mapsto_agree with "Hrm Hsi")
    as "%Hsent".
  iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as "%Hmdl".
  rewrite Hsent Hmdl.
  iSplit.
  { iIntros (?). by simplify_map_eq. }
  iIntros (Hmcoh). iExists _. iSplit; [|done].
  auto.
Qed.

Implicit Types δ : M.

(* A corollary of the simulation theorem [tpc_simulation] and the model
   correctness theoerem [TCConsistent], transfering the consistency property to
   the implementation *)
Corollary tpc_consistent rm1 rm2 tp σ st1 st2 m1 m2 ex :
  rm1 ∈ rms →
  rm2 ∈ rms →
  state_to_msg rm1 st1 = Some m1 →
  state_to_msg rm2 st2 = Some m2 →
  trace_starts_in ex ([runner_expr], init_state) →
  trace_ends_in ex (tp, σ) →
  valid_exec ex →
  m1 ∈ σ.(state_ms) →
  m2 ∈ σ.(state_ms) →
  ¬ (st1 = ABORTED ∧ st2 = COMMITTED).
Proof.
  intros ?? Hmst1 Hmst2 Hstart Hend Hval Hm1 Hm2 [? ?]; simplify_eq.
  inversion Hmst1; inversion Hmst2; simplify_eq.
  clear Hmst1 Hmst2.
  pose proof tpc_simulation as Hsim.
  move: Hsim=> /simulation_does_continue Hexec.
  destruct (Hexec ex) as [atr [Hδ Hcsim]]; [done|done|].
  pose proof (continued_simulation_rel _ _ _ Hcsim) as (Hsteps & Hsim).
  replace σ with ((trace_last ex).2) in Hm1, Hm2; last by erewrite last_eq_trace_ends_in; eauto.
  eapply trace_messages_history_includes_last in Hm1.
  eapply trace_messages_history_includes_last in Hm2.
  apply trace_steps_rtc_2 in Hsteps.
  rewrite Hδ in Hsteps.
  eapply (TCConsistent rms (trace_last atr) rm1 rm2); [done| | |done].
  { eapply rtc_destutter.
    eapply (rtc_congruence (λ δ, δ)) in Hsteps; [done|].
    intros ?? [?[?|?]]; eauto. }
  destruct (Hsim rm1 ABORTED) as [_ (? & ?%rm_step_rtc_aborted & Heq1)];
    [done|by apply elem_of_filter;set_solver|].
  destruct (Hsim rm2 COMMITTED) as [_ (? & ?%rm_step_rtc_committed & Heq2)];
    [done|by apply elem_of_filter;set_solver|].
  simplify_eq; done.
Qed.
