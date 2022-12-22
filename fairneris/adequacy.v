From stdpp Require Import finite.
From trillium Require Import adequacy.
From fairneris Require Import fairness model_draft.
From fairneris.aneris_lang Require Import aneris_lang resources.
From fairneris.aneris_lang.state_interp Require Import state_interp_def.
From fairneris.aneris_lang.state_interp Require Import state_interp_config_wp.
From fairneris.aneris_lang.state_interp Require Import state_interp.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From iris.proofmode Require Import proofmode.

Definition always_holds {Σ}
           `{!anerisG (fair_model_to_model simple_fair_model) Σ}
           (s : stuckness) (ξ : execution_trace aneris_lang →
                              finite_trace simple_state simple_role → Prop)
           (c1 : cfg aneris_lang)
           (c2 : (fair_model_to_model simple_fair_model).(mstate)) : iProp Σ :=
  ∀ ex atr c,
    ⌜valid_system_trace ex atr⌝ -∗
    ⌜trace_starts_in ex c1⌝ -∗
    ⌜trace_starts_in atr c2⌝ -∗
    ⌜trace_ends_in ex c⌝ -∗
    ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' →
                      trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
    ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
    state_interp ex atr -∗
    |={⊤, ∅}=> ⌜ξ ex atr⌝.

Definition valid_state_evolution_fairness
           (extr : execution_trace aneris_lang)
           (auxtr : auxiliary_trace (fair_model_to_model simple_fair_model)) :=
  labels_match extr auxtr ∧ trace_steps simple_trans auxtr.

Lemma rel_finitary_valid_state_evolution_fairness :
  rel_finitary valid_state_evolution_fairness.
Proof. Admitted.

(* TODO: Move to stdpp *)
Lemma gset_union_difference_intersection_L `{Countable A} (X Y : gset A) :
  X = (X ∖ Y) ∪ (X ∩ Y).
Proof. rewrite union_intersection_l_L difference_union_L. set_solver. Qed.

Theorem strong_simulation_adequacy Σ
    `{!anerisPreG (fair_model_to_model simple_fair_model) Σ}
    (s : stuckness) (e : aneris_expr) (σ : state) (st : simple_state)
    A obs_send_sas obs_rec_sas IPs ip lbls :
  state_ms σ = mABn (state_get_n st) →
  (∃ shA shB : socket_handle,
      state_sockets σ =
      {[ipA := {[shA := (sA, [])]};
        ipB := {[shB := (sB, mABm (state_get_m st))]}]}) →
  (∀ (Hinv : anerisG (fair_model_to_model simple_fair_model) Σ),
     ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas),
                         bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) -∗
     live_roles_frag_own (simple_live_roles st ∖ config_roles) -∗
     dead_roles_frag_own ((all_roles ∖ simple_live_roles st) ∖ config_roles) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas ={⊤}=∗
     WP e @ s; locale_of [] e; ⊤ {{ v, dead_role_frag_own A_role ∗
                                       dead_role_frag_own B_role }} ∗
     always_holds s valid_state_evolution_fairness ([e], σ) st) ->
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  dom (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  continued_simulation valid_state_evolution_fairness
                       (trace_singleton ([e], σ))
                       (trace_singleton st).
Proof.
  intros HmABn HmABm Hwp Hsendle Hrecvle Hipdom Hpiiu Hip Hfixdom Hste Hsce Hmse.
  apply (wp_strong_adequacy aneris_lang (fair_model_to_model simple_fair_model) Σ s).
  { apply rel_finitary_valid_state_evolution_fairness. }
  iIntros (?) "".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (unallocated_init (to_singletons A)) as (γsif)
    "[Hunallocated_auth Hunallocated]".
  iMod (free_ips_init IPs) as (γips) "[HIPsCtx HIPs]".
  iMod free_ports_auth_init as (γpiu) "HPiu".
  iMod (allocated_address_groups_init (to_singletons obs_send_sas)) as
      (γobserved_send) "#Hobserved_send".
  iMod (allocated_address_groups_init (to_singletons obs_rec_sas)) as
      (γobserved_receive) "#Hobserved_receive".
  iMod (socket_address_group_ctx_init (to_singletons A)) as (γC) "Hauth";
    [apply to_singletons_all_disjoint|].
  iMod (socket_address_group_own_alloc_subseteq_pre _ (to_singletons A)
                                                      (to_singletons A)
         with "Hauth") as
      "[Hauth HownA]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "HownA") as "#HownAS".
  iMod (messages_ctx_init (to_singletons A) _ _ _ _ with "HownAS Hobserved_send Hobserved_receive" ) as (γms) "[Hms HB]".
  iMod (steps_init 1) as (γsteps) "[Hsteps _]".
  iMod (roles_init (simple_live_roles st)) as (γlive) "[Hlivefull Hlivefrag]".
  iMod (roles_init (all_roles ∖ simple_live_roles st))
    as (γdead) "[Hdeadfull Hdeadfrag]".
  iMod (alloc_evs_init lbls) as (γalevs) "[Halobctx Halobs]".
  iMod (sendreceive_evs_init (to_singletons obs_send_sas)) as
      (γsendevs) "[Hsendevsctx Hsendevs]".
  iMod (sendreceive_evs_init (to_singletons obs_rec_sas)) as
    (γreceiveevs) "[Hreceiveevsctx Hreceiveevs]".
  (* NB: The model state is not used in the current state interpretation
         and can be removed. *)
  iMod (model_init (model_draft.Start:(fair_model_to_model simple_fair_model).(mstate))) as (γm) "[Hmfull Hmfrag]".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_socket_address_group_name := γC;
           aneris_unallocated_socket_address_groups_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           aneris_model_name := γm;
           aneris_live_roles_name := γlive;
           aneris_dead_roles_name := γdead;
           aneris_steps_name := γsteps;
           aneris_allocEVS_name := γalevs;
           aneris_sendonEVS_name := γsendevs;
           aneris_receiveonEVS_name := γreceiveevs;
           aneris_observed_send_name := γobserved_send;
           aneris_observed_recv_name := γobserved_receive;
         |}).
  iMod (Hwp dg) as "Hwp".
  iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
  iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp #Hγn]"; [done|].
  iAssert (is_node ip) as "Hn".
  { iExists _. eauto. }
  iExists (λ ex atr,
      (⌜simple_valid_state_evolution ex atr⌝ ∗
       aneris_events_state_interp ex ∗
       aneris_state_interp
         (trace_last ex).2
         (trace_messages_history ex) ∗
       thread_live_roles_interp (trace_last ex).1 (trace_last atr) ∗
       steps_auth (trace_length ex)))%I.
  iExists (λ _, dead_role_frag_own A_role ∗
                dead_role_frag_own B_role)%I, (λ _ _, True)%I.
  iSplitR; [by iApply config_wp_correct|].
   iMod (socket_address_group_own_alloc_subseteq_pre _ (to_singletons A) (to_singletons obs_send_sas) with "Hauth")
    as "[Hauth Hown_send]".
   { intros x Hin. eapply elem_of_to_singletons. set_solver. }
  iDestruct (socket_address_group_own_big_sepS with "Hown_send") as "Hown_send".
  iMod (socket_address_group_own_alloc_subseteq_pre _ (to_singletons A) (to_singletons obs_rec_sas) with "Hauth")
    as "[Hauth Hown_recv]".
  { intros x Hin. eapply elem_of_to_singletons. set_solver. }
  iAssert (live_roles_frag_own ((simple_live_roles st) ∖ config_roles) ∗
           live_roles_frag_own ((simple_live_roles st) ∩ config_roles))%I with
            "[Hlivefrag]" as "[Hlivefrag Hlivefrag_cfg]".
  { iApply live_roles_own_split; [set_solver|]. 
    by rewrite -gset_union_difference_intersection_L. }
  iAssert (dead_roles_frag_own ((all_roles ∖ simple_live_roles st) ∖ config_roles) ∗
           dead_roles_frag_own ((all_roles ∖ simple_live_roles st) ∩ config_roles))%I with
            "[Hdeadfrag]" as "[Hdeadfrag Hdeadfrag_cfg]".
  { iApply dead_roles_own_split; [set_solver|].
    by rewrite -gset_union_difference_intersection_L. }  
  iDestruct (socket_address_group_own_big_sepS with "Hown_recv") as "Hown_recv".
  iDestruct ("Hwp" with "Hunallocated [HB] Hlivefrag Hdeadfrag HIPs Hn Halobs
            [Hsendevs Hown_send] [Hreceiveevs Hown_recv]
            Hobserved_send Hobserved_receive") as ">[Hwp H]".
  { iApply (big_sepS_to_singletons with "[] HB").
    iIntros "!>" (x) "Hx".
    iDestruct "Hx" as (As Ar) "(?&?&[%%]&?&?)".
    iFrame. simpl. iSplitL; [|done].
    iExists _, _. iFrame.
    iPureIntro.
    rewrite H H0. rewrite !bool_decide_eq_true. set_solver. }
  { iApply big_sepS_sep.
    iSplitL "Hown_send".
    - iApply (big_sepS_to_singletons with "[] Hown_send"); by eauto.
    - iApply (big_sepS_to_singletons with "[] Hsendevs"); by eauto. }
  { iApply big_sepS_sep.
    iSplitL "Hown_recv".
    - iApply (big_sepS_to_singletons with "[] Hown_recv"); by eauto.
    - iApply (big_sepS_to_singletons with "[] Hreceiveevs"); by eauto. }
  iMod (socket_address_group_own_alloc_subseteq_pre _ (to_singletons A)
                                                    (to_singletons (obs_send_sas ∪ obs_rec_sas)) with "Hauth")
    as "[Hauth Hown_send_recv]"; [by set_solver|].
  rewrite to_singletons_union.
  iPoseProof (aneris_events_state_interp_init with "[$] [$] [$] [$] [$] [$]") as "$".
  iMod (socket_address_group_own_alloc_subseteq_pre _ (to_singletons A)
                                                    (to_singletons A) with "Hauth")
    as "[Hauth Hown]"; [by set_solver|].
  iPoseProof (@aneris_state_interp_init _ _ dg IPs
               with "Hmp [//] Hh Hs Hms [$Hauth $Hown] Hunallocated_auth Hsi HIPsCtx HPiu") as "Hinterp"; eauto.
  { intros sag sa Hsag Hsa. 
    apply Hfixdom.
    assert (is_singleton sag) as [sa' ->]; [by eapply elem_of_to_singletons_inv|].
    apply elem_of_to_singletons in Hsag.
    set_solver. }
  { iPureIntro. apply to_singletons_fmap. intros x.
    rewrite /is_ne. set_solver. }
  iModIntro.  
  iFrame "Hwp".
  iSplitR "H".
  { iSplitR.
    { iPureIntro. split; [constructor|done]. }
    iFrame "Hsteps".
    (* TODO: Change definition in state interp *)
    replace ((all_roles ∖ simple_live_roles st) ∩ config_roles) with
      (config_roles ∖ simple_live_roles st) by set_solver.
    rewrite /= Hmse /= dom_empty_L. by iFrame. }
  iIntros (ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr Hstuck) "Hsi Hposts".
  iDestruct "Hsi" as "(%Hvalid&_)".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_".
  iPureIntro.
  by destruct Hvalid as (Htrace&Hlabels&_).
Qed.

(** Existing approach
- Prove [WP] for program
- Obtain [continued_simulation valid_sim extr auxtr] from [adequacy]
- Obtain [exaux_traces_match extr auxtr] from [continued_simulation valid_sim extr auxtr]
  + NB: [exaux_traces_match] works on infinite traces ([extrace / mtrace]), while
        [continued_simulation] works on finite traces ([execution_trace / auxillary_trace])
- Assume [fair_ex extr], and derive [fair_model_trace mtr] from [exaux_traces_match extr mtr]
- Derive [terminating_trace mtr] from [fair_model_trace mtr] (and FairTerminatingModel])
- Derive [terminating_trace extr] from [terminating_trace mtr] and [exaux_traces_match extr auxtr]

OBS: Translation between [finite_trace] and (infinite) [trace] happens via
     taking the head element and the continued simulation.
*)

(* TODO: Should generalise this for more languages *)
Definition fair_network_ex (extr : extrace aneris_lang) :=
  ∀ n, pred_at extr n (λ _ ζ, ζ ≠ Some (inr DuplicateLabel) ∧
                              ζ ≠ Some (inr DropLabel)).

Definition fair_ex (extr : extrace aneris_lang) :=
  (∀ ζ, fair_scheduling_ex ζ extr) ∧ fair_network_ex extr.

Definition traces_match (extr : extrace aneris_lang)
           (mtr : mtrace simple_fair_model) := True.

Lemma continued_simulation_traces_match extr mtr :
  continued_simulation valid_state_evolution_fairness
                       {tr[trfirst extr]} {tr[trfirst mtr]} →
  traces_match extr mtr.
Proof. Admitted.

Lemma traces_match_valid_preserved extr mtr :
  traces_match extr mtr → mtrace_valid mtr.
Proof. Admitted.

Lemma continued_simulation_valid_preserved
        (extr : extrace aneris_lang) (mtr : mtrace simple_fair_model) :
  continued_simulation valid_state_evolution_fairness
    ({tr[trfirst extr]}) ({tr[trfirst mtr]}) →
  mtrace_valid mtr.
Proof. Admitted.

Lemma traces_match_fairness_preserved extr mtr :
  traces_match extr mtr →
  fair_ex extr → mtrace_fair mtr.
Proof. Admitted.

Theorem continued_simulation_fairness_preserved
        (extr : extrace aneris_lang) (mtr : mtrace simple_fair_model) :
  continued_simulation valid_state_evolution_fairness
    ({tr[trfirst extr]}) ({tr[trfirst mtr]}) →
  fair_ex extr → mtrace_fair mtr.
Proof.
  intros ?%continued_simulation_traces_match.
  by eapply traces_match_fairness_preserved.
Qed.

Lemma traces_match_termination_preserved extr mtr :
  traces_match extr mtr →
  terminating_trace mtr →
  terminating_trace extr.
Proof. Admitted.

Theorem continued_simulation_termination_preserved
        (extr : extrace aneris_lang) (mtr : mtrace simple_fair_model) :
  continued_simulation valid_state_evolution_fairness
    ({tr[trfirst extr]}) ({tr[trfirst mtr]}) →
  terminating_trace mtr → terminating_trace extr.
Proof.
  intros ?%continued_simulation_traces_match.
  by eapply traces_match_termination_preserved.
Qed.

Definition extrace_fairly_terminating extr :=
  fair_ex extr → terminating_trace extr.

Theorem continued_simulation_fair_termination_preserved
        (extr : extrace aneris_lang) (mtr : mtrace simple_fair_model) :
  initial_reachable mtr →
  continued_simulation valid_state_evolution_fairness
    ({tr[trfirst extr]}) ({tr[trfirst mtr]}) →
  extrace_fairly_terminating extr.
Proof.
  intros Hinitial Hsim Hfair.
  eapply continued_simulation_termination_preserved; [done|].
  eapply fair_terminating_traces_terminate;
    [done|by eapply continued_simulation_valid_preserved|
      by eapply continued_simulation_fairness_preserved].
Qed.
