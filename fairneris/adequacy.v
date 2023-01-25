From Paco Require Import pacotac.
From stdpp Require Import finite.
From iris.proofmode Require Import proofmode.
From trillium Require Import adequacy.
From fairneris Require Import fairness model_draft.
From fairneris.aneris_lang Require Import aneris_lang resources.
From fairneris.aneris_lang.state_interp Require Import state_interp_def.
From fairneris.aneris_lang.state_interp Require Import state_interp_config_wp.
From fairneris.aneris_lang.state_interp Require Import state_interp.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris Require Import from_locale_utils.

(* TODO: Move to stdpp *)
Lemma gset_union_difference_intersection_L `{Countable A} (X Y : gset A) :
  X = (X ∖ Y) ∪ (X ∩ Y).
Proof. rewrite union_intersection_l_L difference_union_L. set_solver. Qed.

(* TODO: Move *)
Definition tr_starts_in {S L} (tr : trace S L) (s : S) := trfirst tr = s.

Definition extrace_property {Λ} (c : cfg Λ) (Φ : extrace Λ → Prop) :=
  ∀ extr, tr_starts_in extr c → extrace_valid extr → Φ extr.

Lemma extrace_property_impl {Λ} c (Φ Ψ : extrace Λ → Prop) :
  extrace_property c Φ →
  (∀ extr, tr_starts_in extr c → extrace_valid extr → Φ extr → Ψ extr) →
  extrace_property c Ψ.
Proof. intros HΦ Himpl extr Hstarts Hvalid. by apply Himpl, HΦ. Qed.

(* TODO: This is not used right now - Remove/Reintroduce? *)
(* Definition always_holds {Σ} *)
(*            `{!anerisG (fair_model_to_model simple_fair_model) Σ} *)
(*            (s : stuckness) (ξ : execution_trace aneris_lang → *)
(*                               finite_trace simple_state simple_role → Prop) *)
(*            (c1 : cfg aneris_lang) *)
(*            (c2 : (fair_model_to_model simple_fair_model).(mstate)) : iProp Σ := *)
(*   ∀ ex atr c, *)
(*     ⌜valid_system_trace ex atr⌝ -∗ *)
(*     ⌜trace_starts_in ex c1⌝ -∗ *)
(*     ⌜trace_starts_in atr c2⌝ -∗ *)
(*     ⌜trace_ends_in ex c⌝ -∗ *)
(*     ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → *)
(*                       trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗ *)
(*     ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗ *)
(*     state_interp ex atr -∗ *)
(*     |={⊤, ∅}=> ⌜ξ ex atr⌝. *)

(* TODO: Clean up this definition (annoying to state lemmas about,
         due to separate labels) *)
Definition live_tid (c : cfg aneris_lang) (δ : simple_state)
  (ℓ:fmrole simple_fair_model) (ζ:ex_label aneris_lang) : Prop :=
  labels_match ζ ℓ → role_enabled_model ℓ δ → live_ex_label ζ c.

Definition live_tids (c : cfg aneris_lang) (δ : simple_state) : Prop :=
  ∀ ℓ ζ, live_tid c δ ℓ ζ.

Definition valid_state_evolution_fairness
           (extr : execution_trace aneris_lang)
           (auxtr : auxiliary_trace (fair_model_to_model simple_fair_model)) :=
  auxtr_valid auxtr ∧
  labels_match_trace extr auxtr ∧
  live_tids (trace_last extr) (trace_last auxtr).

Lemma rel_finitary_valid_state_evolution_fairness :
  rel_finitary valid_state_evolution_fairness.
Proof. Admitted.

Definition locale_dead_role_disabled (c : cfg aneris_lang)
           (δ : simple_state) :=
  ∀ (ℓ:fmrole simple_fair_model) ζ,
  labels_match (inl ζ) ℓ →
  ∀ e, from_locale c.1 ζ = Some e → is_Some (language.to_val e) →
       ¬ role_enabled_model ℓ δ.

Lemma derive_live_tid_inl c δ (ℓ : fmrole simple_fair_model) ζ :
  role_enabled_locale_exists c δ →
  locale_dead_role_disabled c δ →
  live_tid c δ ℓ (inl ζ).
Proof.
  intros Himpl1 Himpl2 Hmatch Hrole.
  specialize (Himpl1 _ _ Hmatch Hrole) as [e He].
  exists e.
  split; [done|].
  destruct (language.to_val e) eqn:Heqn; [|done].
  specialize (Himpl2 _ _ Hmatch e He).
  assert (is_Some $ language.to_val e) as Hsome by done.
  by specialize (Himpl2 Hsome).
Qed.

Lemma derive_live_tid_inr (c : cfg aneris_lang) δ
      (ℓ : fmrole simple_fair_model) ζ :
  config_state_valid c δ → live_tid c δ ℓ (inr ζ).
Proof.
  intros (Hn&Hm) Hlabels.
  assert (ℓ ≠ A_role ∧ ℓ ≠ B_role) as [HAneq HBneq].
  { rewrite /labels_match /locale_simple_label in Hlabels.
    repeat case_match; simplify_eq; eauto. }
  intros Henabled.
  rewrite /role_enabled_model in Henabled.
  destruct δ eqn:Heq; simpl in *.
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
Qed.

Lemma valid_state_live_tids ex atr :
  simple_valid_state_evolution ex atr →
  locale_dead_role_disabled (trace_last ex) (trace_last atr) →
  live_tids (trace_last ex) (trace_last atr).
Proof.
  intros (_&_&Hlive1&Hnm) Hlive2.
  intros ℓ ζ Hlabels.
  destruct ζ as [ζ|ζ].
  - by apply derive_live_tid_inl.
  - by apply derive_live_tid_inr.
Qed.

Definition continued_simulation_init {Λ M}
           (ξ : execution_trace Λ → auxiliary_trace M → Prop)
           (c : cfg Λ) (s : mstate M) :=
  continued_simulation ξ {tr[c]} {tr[s]}.

Definition wp_proto `{anerisPreG (fair_model_to_model simple_fair_model) Σ} IPs A
           lbls obs_send_sas obs_rec_sas s es ip st :=
  (∀ (aG : anerisG (fair_model_to_model simple_fair_model) Σ), ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) -∗
     live_roles_frag_own (simple_live_roles st ∖ config_roles) -∗
     dead_roles_frag_own ((all_roles ∖ simple_live_roles st) ∖ config_roles) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas ={⊤}=∗
     wptp s es (map (λ '(tnew,e), λ v, fork_post (locale_of tnew e) v)
                    (prefixes es))
     (* OBS: Can add [always_holds ξ] here *)).

Theorem strong_simulation_adequacy_multiple Σ
    `{!anerisPreG (fair_model_to_model simple_fair_model) Σ}
    (s : stuckness) (es : list aneris_expr) (σ : state) (st : simple_state)
    A obs_send_sas obs_rec_sas IPs ip lbls :
  length es ≥ 1 →
  role_enabled_locale_exists (es, σ) st →
  state_ms σ = mABn (state_get_n st) →
  (∃ shA shB : socket_handle,
      state_sockets σ =
      {[ipA := {[shA := (sA, [])]};
        ipB := {[shB := (sB, mABm (state_get_m st))]}]}) →
  wp_proto IPs A lbls obs_send_sas obs_rec_sas s es ip st →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  dom (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  continued_simulation_init valid_state_evolution_fairness (es, σ) st.
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
  iExists (map (λ '(tnew,e) v, fork_post (locale_of tnew e) v) (prefixes es))%I,
            (fork_post)%I.
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
  { iPureIntro. apply to_singletons_fmap. intros x. rewrite /is_ne. set_solver. }
  iModIntro.
  iSplitR "Hwp".
  { iSplitR.
    { iPureIntro. split; [constructor|done]. }
    iFrame "Hsteps".
    (* TODO: Change definition in state interp *)
    replace ((all_roles ∖ simple_live_roles st) ∩ config_roles) with
      (config_roles ∖ simple_live_roles st) by set_solver.
    rewrite /= Hmse /= dom_empty_L. by iFrame. }
  iFrame "Hwp".
  iIntros (ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr Hstuck Htake)
          "Hsi Hposts".
  iDestruct "Hsi" as "(%Hvalid&_&_&Hlive&_)".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "_".
  iAssert (⌜locale_dead_role_disabled c (trace_last atr)⌝)%I as "%Hrole".
  { iIntros (ℓ ζ Hmatch e Hlocale Hval).
    iAssert (dead_role_frag_own ℓ)%I with "[Hposts]" as "H".
    { rewrite -map_app -prefixes_from_app.
      iDestruct (posts_of_length_drop with "Hposts") as "Hposts"; [done|].
      destruct Hval as [v Hv].
      iDestruct (posts_of_idx with "Hposts") as (ℓ' Hmatch') "H"; [done|done|].
      rewrite /labels_match in Hmatch.
      rewrite /labels_match in Hmatch'.
      rewrite -Hmatch in Hmatch'. simplify_eq. done. }
    simpl in *.
    iDestruct "Hlive" as "(_&_&Hdead&Hdead')".
    iDestruct (dead_role_auth_elem_of with "Hdead H") as %Hin.
    iPureIntro.
    intros Hneq. set_solver. }
  iPureIntro.
  pose proof Hvalid as Hvalid'.
  destruct Hvalid as (Htrace&Hlabels&Hstate).
  split; [done|].
  split; [done|].
  apply valid_state_live_tids; [done|].
  by rewrite Hendex.
Qed.

Theorem strong_simulation_adequacy Σ
    `{!anerisPreG (fair_model_to_model simple_fair_model) Σ}
    (s : stuckness) (e : aneris_expr) (σ : state) (st : simple_state)
    A obs_send_sas obs_rec_sas IPs ip lbls :
  role_enabled_locale_exists ([e], σ) st →
  state_ms σ = mABn (state_get_n st) →
  (∃ shA shB : socket_handle,
      state_sockets σ =
      {[ipA := {[shA := (sA, [])]};
        ipB := {[shB := (sB, mABm (state_get_m st))]}]}) →
  wp_proto IPs A lbls obs_send_sas obs_rec_sas s [e] ip st →  
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  dom (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  continued_simulation_init valid_state_evolution_fairness ([e], σ) st.
Proof.
  intros ??? Hwp. by eapply strong_simulation_adequacy_multiple; [simpl;lia|..].
Qed.

(* TODO: Should generalise this for more languages *)
Definition fair_network_ex (extr : extrace aneris_lang) :=
  ∀ n, pred_at extr n (λ _ ζ, ζ ≠ Some (inr DuplicateLabel) ∧
                              ζ ≠ Some (inr DropLabel)).

Definition fair_ex (extr : extrace aneris_lang) :=
  (∀ ζ, fair_scheduling_ex ζ extr) ∧ fair_network_ex extr.

Definition live_traces_match : extrace aneris_lang → mtrace simple_fair_model → Prop :=
  traces_match labels_match live_tids language.locale_step simple_trans.

(* TODO: Clean this up - Currently just ported directly from Fairness *)
Lemma valid_inf_system_trace_implies_traces_match
      ex atr iex iatr progtr (auxtr : mtrace simple_fair_model) :
  exec_trace_match ex iex progtr ->
  exec_trace_match atr iatr auxtr ->
  valid_inf_system_trace (continued_simulation valid_state_evolution_fairness) ex atr iex iatr ->
  live_traces_match progtr auxtr.
Proof.
  revert ex atr iex iatr auxtr progtr. cofix IH.
  intros ex atr iex iatr auxtr progtr Hem Ham Hval.
  inversion Hval as [?? Hphi |
                      ex' atr' c [? σ'] δ' iex' iatr' oζ ℓ Hphi [=] ? Hinf];
    simplify_eq.
  - inversion Hem; inversion Ham. econstructor.
    apply continued_simulation_rel in Hphi as (Hsteps&Hmatch&Hlive).
    by simplify_eq.
  - inversion Hem; inversion Ham. subst.
    pose proof (valid_inf_system_trace_inv _ _ _ _ _ Hinf) as Hphi'.
    apply continued_simulation_rel in Hphi as (Hmatch&Hsteps&Hlive).
    apply continued_simulation_rel in Hphi' as (Hsteps'&Hmatch'&Hlive').
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

Definition extrace_matching_mtrace_exists st extr :=
   ∃ mtr, trfirst mtr = st ∧ live_traces_match extr mtr.

Lemma continued_simulation_traces_match extr st :
  extrace_valid extr →
  continued_simulation valid_state_evolution_fairness
                       {tr[trfirst extr]} {tr[st]} →
  extrace_matching_mtrace_exists st extr.
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
  destruct iatr; [done|by destruct x].
Qed.

Definition matching_mtrace_exists c st :=
  extrace_property c (extrace_matching_mtrace_exists st).

(** A continued simulation exists between some initial configuration [c]
    and the initial state [init_state] of a fair model. *)
Definition live_simulation (c : cfg aneris_lang) (st : simple_state) :=
  continued_simulation_init valid_state_evolution_fairness c st.

Lemma continued_simulation_traces_match_init c st :
  live_simulation c st → matching_mtrace_exists c st.
Proof.
  intros Hsim extr <- Hvalid.
  apply (continued_simulation_traces_match) in Hsim
      as (mtr & Hmtr & Hmatch); [by eexists _|done].
Qed.

Lemma traces_match_valid_preserved extr mtr :
  live_traces_match extr mtr → mtrace_valid mtr.
Proof.
  revert extr mtr. pcofix CH. intros extr mtr Hmatch.
  inversion Hmatch; first by (pfold; constructor).
  pfold. constructor =>//.
  specialize (CH _ _ H3). by right.
Qed.

Lemma traces_match_fairness_preserved extr mtr :
  live_traces_match extr mtr → fair_ex extr → mtrace_fair mtr.
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
    eapply traces_match_traces_implies; [done| | |done].
    + intros s1 s2 oℓ1 oℓ2 Hlive HRℓ Henabled.
      simpl in *. simplify_eq.
      apply Hlive in Hlabel.
      by apply Hlabel.
    + intros s1 s2 oℓ1 oℓ2 Hlive HRℓ [Henabled|Henabled]; simpl in *.
      * left. intros Henabled'. apply Henabled.
        apply Hlive in Hlabel. by apply Hlabel.
      * right. rewrite Henabled in HRℓ. destruct oℓ2; [|done].
        simplify_eq. rewrite Hlabel. by rewrite HRℓ.
  - intros n. rewrite /pred_at.
    specialize (Hfairex_network n). rewrite /pred_at in Hfairex_network.
    destruct (after n extr) eqn:Heqn; [|done].
    apply traces_match_flip in Hmatch; [|done..].
    eapply (traces_match_after) in Hmatch as (mtr' & Hmtreq & Hmatch); [|done].
    rewrite Hmtreq.
    destruct t; inversion Hmatch; simplify_eq; [done|].
    destruct Hfairex_network as [Hdup Hdrop].
    split.
    + rewrite H2. intros Heq. apply Hdup. simplify_eq.
      rewrite /locale_simple_label in Heq.
      repeat case_match; simplify_eq.
    + rewrite H2. intros Heq. apply Hdrop. simplify_eq.
      rewrite /locale_simple_label in Heq.
      repeat case_match; simplify_eq.
Qed.

Lemma traces_match_termination_preserved extr mtr :
  live_traces_match extr mtr → terminating_trace mtr → terminating_trace extr.
Proof. intros Hmatch [n Hmtr]. exists n. by eapply traces_match_after_None. Qed.

Definition extrace_fairly_terminating (extr : extrace aneris_lang) :=
  fair_ex extr → terminating_trace extr.

Lemma traces_match_fair_termination_preserved extr mtr :
  initial_reachable mtr →
  live_traces_match extr mtr →
  extrace_fairly_terminating extr.
Proof.
  intros Hinitial Hsim Hfair.
  eapply traces_match_termination_preserved; [done|].
  eapply fair_terminating_traces_terminate;
    [done|by eapply traces_match_valid_preserved|
      by eapply traces_match_fairness_preserved].
Qed.

Definition init_state := model_draft.Start.

Lemma initial_reachable_start mtr :
  tr_starts_in mtr init_state → initial_reachable mtr.
Proof.
  rewrite /tr_starts_in. intros Hstart.
  (* TODO: Clean this up *)
  rewrite /initial_reachable. rewrite /initial_reachable in Hstart.
  destruct mtr; rewrite /pred_at; rewrite /pred_at in Hstart; simpl in *;
                by simplify_eq.
Qed.

Definition fairly_terminating (c : cfg aneris_lang) :=
  extrace_property c extrace_fairly_terminating.

Lemma traces_match_fair_termination_preserved_init c :
  matching_mtrace_exists c init_state → fairly_terminating c.
Proof.
  intros Hmatches.
  eapply extrace_property_impl; [done|].
  intros extr Hstart Hvalid (mtr & Hstart' & Hmtr) Hfair.
  eapply traces_match_fair_termination_preserved; [|done..].
  by apply initial_reachable_start.
Qed.

Theorem continued_simulation_fair_termination c :
  live_simulation c init_state → fairly_terminating c.
Proof.
  intros ?.
  by apply traces_match_fair_termination_preserved_init,
    continued_simulation_traces_match_init.
Qed.

Theorem simulation_adequacy_fair_termination_multiple Σ
    `{!anerisPreG (fair_model_to_model simple_fair_model) Σ}
    (s : stuckness) (es : list aneris_expr) (σ : state)
    A obs_send_sas obs_rec_sas IPs ip lbls :
  length es ≥ 1 →
  role_enabled_locale_exists (es, σ) init_state →
  state_ms σ = mABn (state_get_n init_state) →
  (∃ shA shB : socket_handle,
      state_sockets σ =
      {[ipA := {[shA := (sA, [])]};
        ipB := {[shB := (sB, mABm (state_get_m init_state))]}]}) →
  wp_proto IPs A lbls obs_send_sas obs_rec_sas s es ip init_state →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  dom (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  fairly_terminating (es,σ).
Proof.
  intros. by eapply continued_simulation_fair_termination,
            strong_simulation_adequacy_multiple.
Qed.
