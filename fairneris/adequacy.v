From Paco Require Import pacotac.
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
  labels_match_trace extr auxtr ∧ trace_steps simple_trans auxtr ∧
  live_tids (trace_last extr) (trace_last auxtr).

Lemma rel_finitary_valid_state_evolution_fairness :
  rel_finitary valid_state_evolution_fairness.
Proof. Admitted.

(* TODO: Move to stdpp *)
Lemma gset_union_difference_intersection_L `{Countable A} (X Y : gset A) :
  X = (X ∖ Y) ∪ (X ∩ Y).
Proof. rewrite union_intersection_l_L difference_union_L. set_solver. Qed.


Lemma valid_state_live_tids ex atr :
  simple_valid_state_evolution ex atr →
  live_tids (trace_last ex) (trace_last atr).
Proof.
  intros (Hsteps&Hmatch&Hlive&Hn&Hm).
  intros ζ ℓ Hlabels.
  destruct ζ as [ζ|ζ]; [by apply Hlive|].
  split.
  - assert (ℓ ≠ A_role ∧ ℓ ≠ B_role) as [HAneq HBneq].
    { rewrite /labels_match /locale_simple_label in Hlabels.
      repeat case_match; simplify_eq; eauto. }
    intros Henabled.
    rewrite /role_enabled_model in Henabled.
    destruct (trace_last atr) eqn:Heq; simpl in *.
    + set_solver.
    + destruct ℓ.
      * by destruct sent; set_solver.
      * by destruct sent; set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DuplicateLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DropLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DeliverLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
    + destruct ℓ.
      * by destruct sent; set_solver.
      * by destruct sent; set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DuplicateLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DropLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DeliverLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
    + destruct ℓ.
      * by destruct sent; set_solver.
      * by destruct sent; set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DuplicateLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DropLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
      * destruct sent; [by set_solver|].
        assert (ζ = DeliverLabel) as ->.
        { rewrite /labels_match /locale_simple_label in Hlabels.
          by repeat case_match; simplify_eq. }
        simpl. rewrite /config_enabled. rewrite Hn.
        simpl.
        rewrite gmultiset_disj_union_comm.
        intros Hneq.
        assert (mAB ∈ {[+ mAB +]} ⊎ mABn sent) by multiset_solver.
        rewrite Hneq in H.
        set_solver.
  - intros Hζ.
    + destruct ζ; simpl in Hζ.
      * assert (Some ℓ = Some Ndeliver) as Heq by done.
        assert (ℓ = Ndeliver) as -> by naive_solver.
        rewrite /config_enabled in Hζ.
        destruct (trace_last atr); try by set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
      * assert (Some ℓ = Some Ndup) as Heq by done.
        assert (ℓ = Ndup) as -> by naive_solver.
        rewrite /config_enabled in Hζ.
        destruct (trace_last atr); try by set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
      * assert (Some ℓ = Some Ndrop) as Heq by done.
        assert (ℓ = Ndrop) as -> by naive_solver.
        rewrite /config_enabled in Hζ.
        destruct (trace_last atr); try by set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
        -- rewrite /role_enabled_model. simpl.
           destruct sent; set_solver.
Qed.

Theorem strong_simulation_adequacy_multiple Σ
    `{!anerisPreG (fair_model_to_model simple_fair_model) Σ}
    (s : stuckness) (es : list aneris_expr) (σ : state) (st : simple_state)
    A obs_send_sas obs_rec_sas IPs ip lbls :
  length es ≥ 1 →
  live_threads (es, σ) st →
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
     wptp s es (map (λ _ _, True) es)
     (* OBS: Can add [always_holds ξ] here *)) →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  dom (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  continued_simulation valid_state_evolution_fairness
                       (trace_singleton (es, σ))
                       (trace_singleton st).
Proof.
  intros Hlen Hlive HmABn HmABm Hwp Hsendle Hrecvle Hipdom Hpiiu Hip Hfixdom Hste Hsce Hmse.
  apply (wp_strong_adequacy_multiple aneris_lang (fair_model_to_model simple_fair_model) Σ s);
    [done| |].
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
  iExists (map (λ _ _, True)%I es), (λ _ _, True)%I.
  (* iExists (λ _, dead_role_frag_own A_role ∗ *)
  (*               dead_role_frag_own B_role)%I, (λ _ _, True)%I. *)
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
            Hobserved_send Hobserved_receive") as ">Hwp".
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
  iSplitL.
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
  pose proof Hvalid as Hvalid'.
  destruct Hvalid as (Htrace&Hlabels&Hstate).
  split; [done|].
  split; [done|].
  by apply valid_state_live_tids.
Qed.

Theorem strong_simulation_adequacy Σ
    `{!anerisPreG (fair_model_to_model simple_fair_model) Σ}
    (s : stuckness) (e : aneris_expr) (σ : state) (st : simple_state)
    A obs_send_sas obs_rec_sas IPs ip lbls :
  live_threads ([e], σ) st →
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
                                       dead_role_frag_own B_role }}(*  ∗ *)
     (* always_holds s valid_state_evolution_fairness ([e], σ) st *)) ->
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
  intros Hlive HmABn HmABm Hwp Hsendle Hrecvle Hipdom Hpiiu Hip Hfixdom Hste Hsce Hmse.
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
            Hobserved_send Hobserved_receive") as ">Hwp".
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
  iSplitL.
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
  pose proof Hvalid as Hvalid'.
  destruct Hvalid as (Htrace&Hlabels&Hstate).
  split; [done|].
  split; [done|].
  by apply valid_state_live_tids.
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

Definition exmtr_traces_match : extrace aneris_lang → mtrace simple_fair_model → Prop :=
  traces_match labels_match live_tids language.locale_step simple_trans.

(* TODO: Clean this up - Currently just ported directly from Fairness *)
Lemma valid_inf_system_trace_implies_traces_match
      ex atr iex iatr progtr (auxtr : mtrace simple_fair_model) :
  exec_trace_match ex iex progtr ->
  exec_trace_match atr iatr auxtr ->
  valid_inf_system_trace (continued_simulation valid_state_evolution_fairness) ex atr iex iatr ->
  exmtr_traces_match progtr auxtr.
Proof.
  revert ex atr iex iatr auxtr progtr. cofix IH.
  intros ex atr iex iatr auxtr progtr Hem Ham Hval.
  inversion Hval as [?? Hphi |ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf]; simplify_eq.
  - inversion Hem; inversion Ham. econstructor; eauto.
    apply continued_simulation_rel in Hphi.
    destruct Hphi as (Hmatch&Hsteps&Hlive).
    by simplify_eq.
  - inversion Hem; inversion Ham. subst.
    pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
    apply continued_simulation_rel in Hphi.
    destruct Hphi as (Hmatch&Hsteps&Hlive).
    apply continued_simulation_rel in Hphi'.
    destruct Hphi' as (Hmatch'&Hsteps'&Hlive').
    econstructor.
    + eauto.
    + eauto.
    + match goal with
      | [H: exec_trace_match _ iex' _ |- _] => inversion H; clear H; simplify_eq
      end; done.
    + match goal with
      | [H: exec_trace_match _ iatr' _ |- _] => inversion H; clear H; simplify_eq
      end.
      * inversion Hsteps'; simplify_eq.
        rewrite /trace_ends_in in H3. rewrite H3. done.
      * simpl. inversion Hsteps'; simplify_eq.
        rewrite /trace_ends_in in H4. rewrite H4. done.
    + eapply IH; eauto.
Qed.

Lemma continued_simulation_traces_match extr st :
  extrace_valid extr →
  continued_simulation valid_state_evolution_fairness
                       {tr[trfirst extr]} {tr[st]} →
  ∃ (mtr : mtrace simple_fair_model),
    trfirst mtr = st ∧ exmtr_traces_match extr mtr.
Proof.
  intros Hvalid Hsim.
  assert (∃ iatr,
             valid_inf_system_trace
               (continued_simulation valid_state_evolution_fairness)
               (trace_singleton (trfirst extr))
               (trace_singleton (st))
               (from_trace extr)
               iatr) as [iatr Hiatr].
  { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
    Unshelve.
    - done.
    - eapply from_trace_preserves_validity; eauto; first econstructor. }
  eexists _.
  split; last first.
  { eapply (valid_inf_system_trace_implies_traces_match); eauto.
    - by apply from_trace_spec.
    - by apply to_trace_spec. }
  (* TODO: Clean this up *)
  rewrite /trace_last.
  destruct iatr; simpl. done.
  destruct x. done.
Qed.

Lemma traces_match_valid_preserved extr mtr :
  exmtr_traces_match extr mtr → mtrace_valid mtr.
Proof.
  revert extr mtr. pcofix CH. intros extr mtr Hmatch.
  inversion Hmatch; first by (pfold; constructor).
  pfold.
  constructor =>//.
  specialize (CH _ _ H3).
  right. done.
Qed.

(* TODO: Move the lemmas relalted to general `traces_match` *)
Definition flip_impl {A B} (R : A → B → Prop) : Prop :=
  ∀ a b, R a b ↔ flip R b a.

Lemma traces_match_flip {S1 S2 L1 L2}
      (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop)
      (trans2: S2 -> L2 -> S2 -> Prop)
      tr1 tr2 :
  flip_impl Rℓ → flip_impl Rs →
  traces_match Rℓ Rs trans1 trans2 tr1 tr2 ↔
  traces_match (flip Rℓ) (flip Rs) trans2 trans1 tr2 tr1.
Proof.
  split.
  - revert tr1 tr2. cofix CH.
    intros tr1 tr2 Hmatch. inversion Hmatch; simplify_eq.
    { by constructor. }
    constructor; [done..|].
    by apply CH.
  - revert tr1 tr2. cofix CH.
    intros tr1 tr2 Hmatch. inversion Hmatch; simplify_eq.
    { by constructor. }
    constructor; [done..|].
    by apply CH.
Qed.

Lemma traces_match_traces_implies {S1 S2 L1 L2}
      (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop)
      (trans2: S2 -> L2 -> S2 -> Prop)
      (P1 Q1 : S1 → option L1 → Prop)
      (P2 Q2 : S2 → option L2 → Prop)
      tr1 tr2 :
  flip_impl Rℓ → flip_impl Rs →
  traces_match Rℓ Rs trans1 trans2 tr1 tr2 →
  (∀ s1 s2 oℓ1 oℓ2, Rs s1 s2 →
                    match oℓ1, oℓ2 with
                    | Some ℓ1, Some ℓ2 => Rℓ ℓ1 ℓ2
                    | None, None => True
                    | _, _ => False
                    end →
                    P2 s2 oℓ2 → P1 s1 oℓ1) →
  (∀ s1 s2 oℓ1 oℓ2, Rs s1 s2 →
                    match oℓ1, oℓ2 with
                    | Some ℓ1, Some ℓ2 => Rℓ ℓ1 ℓ2
                    | None, None => True
                    | _, _ => False
                    end → Q1 s1 oℓ1 → Q2 s2 oℓ2) →
  trace_implies P1 Q1 tr1 → trace_implies P2 Q2 tr2.
Proof.
  intros HRℓ HRs Hmatch HP HQ Htr1.
  intros n Hpred_at.
  rewrite /pred_at in Hpred_at.
  assert (traces_match (flip Rℓ)
                       (flip Rs)
                       trans2 trans1
                       tr2 tr1) as Hmatch'.
  { by rewrite -traces_match_flip. }
  destruct (after n tr2) as [tr2'|] eqn:Htr2eq; [|done].
  eapply (traces_match_after) in Hmatch as (tr1' & Htr1eq & Hmatch); [|done].
  specialize (Htr1 n).
  rewrite {1}/pred_at in Htr1.
  rewrite Htr1eq in Htr1.
  destruct tr1' as [|s ℓ tr']; inversion Hmatch; simplify_eq; try by done.
  - assert (P1 s None) as HP1 by by eapply (HP _ _ _ None).
    destruct (Htr1 HP1) as [m Htr1'].
    exists m. rewrite pred_at_sum. rewrite pred_at_sum in Htr1'.
    destruct (after n tr1) as [tr1'|] eqn:Htr1eq'; [|done].
    eapply (traces_match_after) in Hmatch' as (tr2' & Htr2eq' & Hmatch'); [|done].
    rewrite Htr2eq'.
    rewrite /pred_at.
    rewrite /pred_at in Htr1'.
    destruct (after m tr1') as [tr1''|] eqn:Htr1eq''; [|done].
    eapply (traces_match_after) in Hmatch' as (tr2'' & Htr2eq'' & Hmatch''); [|done].
    rewrite Htr2eq''.
    destruct tr1''; inversion Hmatch''; simplify_eq; try by done.
    + by eapply (HQ _ _ None None).
    + by (eapply (HQ _ _ (Some _) _)).
  - assert (P1 s (Some ℓ)) as HP1 by by (eapply (HP _ _ _ (Some _))).
    destruct (Htr1 HP1) as [m Htr1'].
    exists m. rewrite pred_at_sum. rewrite pred_at_sum in Htr1'.
    destruct (after n tr1) as [tr1'|] eqn:Htr1eq'; [|done].
    eapply (traces_match_after) in Hmatch' as (tr2' & Htr2eq' & Hmatch'); [|done].
    rewrite Htr2eq'.
    rewrite /pred_at.
    rewrite /pred_at in Htr1'.
    destruct (after m tr1') as [tr1''|] eqn:Htr1eq''; [|done].
    eapply (traces_match_after) in Hmatch' as (tr2'' & Htr2eq'' & Hmatch''); [|done].
    rewrite Htr2eq''.
    destruct tr1''; inversion Hmatch''; simplify_eq; try by done.
    + by eapply (HQ _ _ None None).
    + by (eapply (HQ _ _ (Some _) _)).
Qed.

(* TODO: Move this *)
Definition simple_label_locale (ℓ : simple_role) : ex_label aneris_lang :=
  match ℓ with
  | A_role => inl ("0.0.0.0",0)
  | B_role => inl ("0.0.0.1",0)
  | Ndeliver => inr DeliverLabel
  | Ndrop => inr DropLabel
  | Ndup => inr DuplicateLabel
  end.

Lemma traces_match_fairness_preserved extr mtr :
  exmtr_traces_match extr mtr →
  fair_ex extr → mtrace_fair mtr.
Proof.
  rewrite /fair_ex /mtrace_fair.
  intros Hmatch [Hfairex_scheduling Hfairex_network].
  assert (mtrace_valid mtr) as Hvalid.
  { by eapply traces_match_valid_preserved. }
  split.
  - intros ℓ.
    assert (∃ ζ, labels_match ζ ℓ) as [ζ Hlabel].
    { exists (simple_label_locale ℓ). destruct ℓ; done. }
    specialize (Hfairex_scheduling ζ).
    eapply traces_match_traces_implies; [by split|by split|done| | |done].
    + intros s1 s2 oℓ1 oℓ2 Hlive HRℓ Henabled.
      simpl in *. simplify_eq.
      apply Hlive in Hlabel.
      by apply Hlabel.
    + intros s1 s2 oℓ1 oℓ2 Hlive HRℓ [Henabled|Henabled]; simpl in *.
      * left. intros Henabled'. apply Henabled.
        apply Hlive in Hlabel.
        by apply Hlabel.
      * right.
        rewrite Henabled in HRℓ. destruct oℓ2; [|done].
        simplify_eq. rewrite Hlabel. rewrite HRℓ. done.
  - intros n. rewrite /pred_at.
    specialize (Hfairex_network n). rewrite /pred_at in Hfairex_network.
    destruct (after n extr) eqn:Heqn; [|done].
    apply traces_match_flip in Hmatch; [|done..].
    eapply (traces_match_after) in Hmatch as (mtr' & Hmtreq & Hmatch); [|done].
    rewrite Hmtreq.
    destruct t; inversion Hmatch; simplify_eq; [done|].
    destruct Hfairex_network as [Hdup Hdrop].
    split.
    + rewrite H2.
      intros Heq. apply Hdup. simplify_eq.
      rewrite /locale_simple_label in Heq.
      repeat case_match; simplify_eq.
    + rewrite H2. intros Heq.
      apply Hdrop.
      simplify_eq.
      rewrite /locale_simple_label in Heq.
      repeat case_match; simplify_eq.
Qed.

(* TODO: Move this *)
Lemma traces_match_after_None {S1 S2 L1 L2}
      (Rℓ: L1 -> L2 -> Prop) (Rs: S1 -> S2 -> Prop)
      (trans1: S1 -> L1 -> S1 -> Prop)
      (trans2: S2 -> L2 -> S2 -> Prop)
      tr1 tr2 n :
  traces_match Rℓ Rs trans1 trans2 tr1 tr2 ->
  after n tr2 = None ->
  after n tr1 = None.
Proof.
  revert tr1 tr2.
  induction n; intros tr1 tr2; [done|].
  move=> /= Hm Ha.
  destruct tr1; first by inversion Hm.
  inversion Hm; simplify_eq. by eapply IHn.
Qed.

Lemma traces_match_termination_preserved extr mtr :
  exmtr_traces_match extr mtr →
  terminating_trace mtr →
  terminating_trace extr.
Proof.
  intros Hmatch [n Hmtr]. exists n.
  by eapply traces_match_after_None.
Qed.

Definition extrace_fairly_terminating extr :=
  extrace_valid extr → fair_ex extr → terminating_trace extr.

Lemma traces_match_fair_termination_preserved
      extr (mtr : mtrace simple_fair_model) :
  initial_reachable mtr →
  exmtr_traces_match extr mtr →
  extrace_fairly_terminating extr.
Proof.
  intros Hinitial Hsim Hvalid Hfair.
  eapply traces_match_termination_preserved; [done|].
  eapply fair_terminating_traces_terminate;
    [done|by eapply traces_match_valid_preserved|
      by eapply traces_match_fairness_preserved].
Qed.

Theorem continued_simulation_fair_termination_preserved
        (extr : extrace aneris_lang) (mtr : mtrace simple_fair_model) :
  initial_reachable mtr →
  continued_simulation valid_state_evolution_fairness
    ({tr[trfirst extr]}) ({tr[trfirst mtr]}) →
  extrace_fairly_terminating extr.
Proof.
  intros Hinitial Hsim Hvalid Hfair.
  apply continued_simulation_traces_match in Hsim as [mtr' [Hfst Hmatch]];
    [|done].
  eapply traces_match_fair_termination_preserved; [|done..].
  (* TODO: Clean this up! *)
  rewrite /initial_reachable. rewrite /initial_reachable in Hinitial.
  destruct mtr, mtr'; rewrite /pred_at; rewrite /pred_at in Hinitial; simpl in *;
                by simplify_eq.
Qed.
