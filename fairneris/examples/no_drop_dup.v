From stdpp Require Import list fin_maps.
From iris.proofmode Require Import proofmode.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import fairness.
From fairneris Require Import model_draft.
From fairneris.aneris_lang Require Import aneris_lang.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From fairneris Require Import adequacy.

Definition Aprog shA : expr := SendTo #(LitSocket shA) #"Hello" #saB.
Definition Bprog shB : expr := ReceiveFrom #(LitSocket shB).

Section with_Σ.
  Context `{anerisG (fair_model_to_model simple_fair_model) Σ}.

  Lemma wp_A s E shA :
    {{{ shA ↪[ip_of_address saA] sA ∗ saA ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) ∗
        live_role_frag_own A_role }}}
      (mkExpr (ip_of_address saA) (Aprog shA)) @ s; (ip_of_address saA,tidA); E
    {{{ v, RET v; dead_role_frag_own A_role }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & Hmsg & HA) HΦ".
    iApply wp_lift_atomic_head_step_no_fork; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale)
            "(%Hvalid & Hevs & Hσ & Hlive & Hauth) /=".
    iDestruct "Hlive" as "(Hlive_auth & Hlive_owns & Hdead_auth & Hdead_owns)".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iSplitR.
    { iPureIntro; do 3 eexists. eapply SocketStepS; eauto.
        by econstructor; naive_solver. }
    iModIntro.
    iIntros (v2' ? ? Hstep).
    pose proof (λ b c d f g h i j k,
                aneris_events_state_interp_send_untracked {[saA]}
                  b c d f g h _ i _ _ _ _
                  (inl (ip_of_address saA,tidA)) j k Hstep)
      as Huntracked.
    inv_head_step; iNext.
    rewrite (insert_id (state_sockets σ)); last done.
    rewrite (insert_id (state_sockets σ)) in Huntracked; last done.
    iAssert (socket_address_group_own {[saA]})%I as "#HsaA".
    { iDestruct "Hrt" as "[(%send & %recv & _ & _ & _ & $ & _) _]". }
    iAssert (socket_address_group_own {[saB]})%I as "#HsaB".
    { by iDestruct "Hmsg" as (γ) "[H _]". }
    iMod (aneris_state_interp_send shA saA {[saA]} saB {[saB]} _ _ sA _ _ _ _ _
                                   "Hello"
           with "[] [] [$Hsh] [Hrt] [$Hmsg] [] [$Hσ]")
        as "(%Hmhe & Hσ & Hsh & Hrt)";
      [try set_solver..|].
    { apply message_group_equiv_refl; set_solver. }
    { iFrame "#". iPureIntro; set_solver. }
    { iFrame "#". iPureIntro; set_solver. }
    { iDestruct "Hrt" as "[$ Hrt]". }
    { simpl. rewrite /from_singleton. eauto. }
    iDestruct (live_role_auth_elem_of with "Hlive_auth HA") as %Hrole.
    assert ((trace_last atr) = model_draft.Start) as Heq.
    { destruct (trace_last atr); simpl in Hrole; try set_solver;
        destruct sent; set_solver. }
    iMod (live_role_auth_delete with "Hlive_auth HA") as "Hlive_auth".
    rewrite Heq.
    iMod (live_roles_auth_extend _ {[Ndup;Ndrop;Ndeliver]} with "Hlive_auth")
      as "[Hlive_auth Hlive_owns']"; [set_solver|].
    replace (config_roles ∖ simple_live_roles model_draft.Start) with
      config_roles by set_solver.
    iMod (dead_roles_auth_delete _ {[Ndup;Ndrop;Ndeliver]} with
           "Hdead_auth Hdead_owns") as "Hdead_auth".
    iMod (dead_roles_auth_extend _ {[A_role]} with "Hdead_auth")
      as "[Hdead_auth Hdead_owns]"; [set_solver|].
    iMod (dead_roles_auth_extend _ ∅ with "Hdead_auth")
      as "[Hdead_auth Hdead_owns_∅]"; [set_solver|].
    iExists (Sent 1), A_role.
    iDestruct (Huntracked with "Hrt Hevs") as "[$ Hrt]";
          [done..|set_solver|].
    iModIntro.
    rewrite -Hmhe.
    iFrame.
    iSplitR; [done|].
    simpl.
    iSpecialize ("HΦ" with "Hdead_owns").
    iSplitR "HΦ"; [|done].
    iSplitR "Hlive_auth Hlive_owns' Hdead_auth Hdead_owns_∅"; last first.
    { replace ({[A_role; B_role]} ∖ {[A_role]}) with
              ({[B_role]}:gset simple_role) by set_solver.
      rewrite /thread_live_roles_interp. simpl.
      replace ({[B_role; Ndup; Ndrop; Ndeliver]} ∩ config_roles) with
        config_roles by set_solver.
      replace (config_roles ∖ {[B_role; Ndup; Ndrop; Ndeliver]}) with
        (∅:gset simple_role) by set_solver.
      replace ({[Ndup; Ndrop; Ndeliver; B_role]}) with
        ({[B_role; Ndup; Ndrop; Ndeliver]}:gset simple_role) by set_solver.
      iFrame.
      rewrite union_empty_l_L.
      replace (all_roles ∖ {[A_role; B_role]}) with
        config_roles by set_solver. rewrite difference_diag_L union_empty_r_L.
      replace (all_roles ∖ {[B_role; Ndup; Ndrop; Ndeliver]}) with
        ({[A_role]}:gset simple_role) by set_solver.
      by iFrame. }
    iPureIntro.
    rewrite /simple_valid_state_evolution in Hvalid.
    rewrite /simple_valid_state_evolution.
    rewrite Heq in Hvalid. simpl in Hvalid.
    simpl.
    destruct Hvalid as (Hsteps & Hmatch & Hlive & Hms & Hskt).
    rewrite /trace_ends_in in Hex.
    rewrite Hex in Hms. simpl in Hms. rewrite Hms.
    split; [econstructor; [apply Heq|econstructor|done]|].
    split; [done|].
    split.
    { intros ℓ ζ Hlabels Henabled.
      assert (ℓ = A_role ∨ ℓ = B_role) as [Hℓ|Hℓ].
      { rewrite /labels_match /locale_simple_label in Hlabels.
        repeat case_match; simplify_eq; eauto. }
      - simplify_eq.
        eapply from_locale_step.
        eapply locale_step_atomic; eauto.
        2: { rewrite Hex in Hlive.
             eapply Hlive; [done|].
             rewrite /labels_match /role_enabled_model. set_solver. }
        by repeat econstructor.
      - simplify_eq.
        eapply from_locale_step.
        eapply locale_step_atomic; eauto.
        2: { rewrite Hex in Hlive.
             eapply Hlive; [done|].
             rewrite /labels_match /role_enabled_model. set_solver. }
        by repeat econstructor. }
    split.
    { rewrite (comm _ ∅). set_solver. }
    rewrite Hex in Hskt.
    simpl in Hskt.
    done.
  Qed.

  Lemma snoc_eq {A} (xs ys : list A) x y :
    xs ++ [x] = ys ++ [y] → xs = ys ∧ x = y.
  Proof.
    revert ys.
    induction xs.
    - intros ys Heq. simpl in *.
      rewrite comm in Heq.
      apply app_singleton in Heq. set_solver.
    - intros ys Heq.
      simpl in *.
      assert (∃ z zs, ys = z :: zs) as (z & zs & ->).
      { rewrite app_comm_cons in Heq.
        destruct ys.
        { simpl in *. inversion Heq.
          apply app_nil in H2.
          set_solver. }
        set_solver. }
      set_solver.
  Qed.

  Lemma wp_B s E shB :
    {{{ shB ↪[ip_of_address saB] sB ∗ saB ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) ∗
        live_role_frag_own B_role }}}
      (mkExpr (ip_of_address saB) (Bprog shB)) @ s; (ip_of_address saB, tidB); E
    {{{ v, RET v; dead_role_frag_own B_role }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & #HΨ & HB) HΦ".
    iLöb as "IH".
    iApply wp_lift_head_step; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(%Hvalid & Hevs & Hσ & Hlive & Hauth) /=".
    iDestruct "Hlive" as "(Hlive_auth & Hlive_owns & Hdead_auth & Hdead_owns)".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    destruct (decide (r = [])) as [-> | Hneq].
    - iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { by iPureIntro; do 3 eexists; eapply SocketStepS; eauto; econstructor. }
      iIntros (v2' ? ? Hstep).
      pose proof (λ b c d f g h, aneris_events_state_interp_no_triggered' b c d
                                 _ f _ _ _ _ (inl (ip_of_address saB,tidB)) g h
                                 Hstep)
        as Hnotriggered.
      inv_head_step; [|].
      + assert (length (r ++ [m]) = length ([] : list message))
          as Hdone; [by f_equal|].
        rewrite app_length /= in Hdone. lia.
      + rewrite (insert_id (state_sockets σ)); last done.
        rewrite (insert_id (state_sockets σ)) in Hnotriggered; last done.
        iNext.
        iMod "Hmk".
        iDestruct (live_role_auth_elem_of with "Hlive_auth HB") as %Hrole.
        iModIntro.
        destruct (trace_last atr) eqn:Hs; [..|by destruct sent; set_solver].
        * iExists (trace_last atr), B_role.
          rewrite -message_history_evolution_id; iFrame.
          rewrite Hnotriggered;
            [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?)].
          iSpecialize ("IH" with "[$] [$] [$] [$]").
          rewrite Hs.
          iFrame.
          iPureIntro.
          rewrite /trace_ends_in in Hex.
          rewrite /simple_valid_state_evolution.
          rewrite /simple_valid_state_evolution in Hvalid.

          destruct Hvalid as (Hsteps & Hmatch & Hlive & Hm).
          rewrite /trace_ends_in in Hex.
          rewrite Hex in Hm=> /=.
          rewrite Hs in Hm.
          split; [econstructor;[done|econstructor|done]|].
          split; [done|].
          split; [|done].
          intros ℓ ζ Hlabels Henabled.
          assert (ℓ = A_role ∨ ℓ = B_role) as [Hℓ|Hℓ].
          { rewrite /labels_match /locale_simple_label in Hlabels.
            repeat case_match; simplify_eq; eauto. }
          -- simplify_eq.
             eapply from_locale_step.
             eapply locale_step_atomic; eauto.
             2: { rewrite Hex in Hlive.
                  eapply Hlive; [done|].
                  rewrite /labels_match /role_enabled_model.
                  rewrite Hs.
                  set_solver. }
             by repeat econstructor.
          -- simplify_eq.
             eapply from_locale_step.
             eapply locale_step_atomic; eauto.
             2: { rewrite Hex in Hlive.
                  eapply Hlive; [done|].
                  rewrite /labels_match /role_enabled_model.
                  rewrite Hs.
                  set_solver. }
             by repeat econstructor.
        * iExists (trace_last atr), B_role.
          rewrite -message_history_evolution_id; iFrame.
          rewrite Hnotriggered;
            [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?)].
          iSpecialize ("IH" with "[$] [$] [$] [$]").
          rewrite Hs.
          iFrame.
          iPureIntro.
          rewrite /trace_ends_in in Hex.
          rewrite /simple_valid_state_evolution.
          rewrite /simple_valid_state_evolution in Hvalid.
          destruct Hvalid as (Hsteps & Hmatch & Hlive & Hm).
          rewrite Hex in Hm=> /=.
          rewrite Hs in Hm.
          split; [econstructor;[done|econstructor|done]|].
          split; [done|].
          split; [|done].
          intros ℓ ζ Hlabels Henabled.
          assert (ℓ = A_role ∨ ℓ = B_role) as [Hℓ|Hℓ].
          { rewrite /labels_match /locale_simple_label in Hlabels.
            repeat case_match; simplify_eq; eauto. }
          -- simplify_eq.
             eapply from_locale_step.
             eapply locale_step_atomic; eauto.
             2: { rewrite Hex in Hlive.
                  eapply Hlive; [done|].
                  rewrite /labels_match /role_enabled_model.
                  rewrite Hs.
                  set_solver. }
             by repeat econstructor.
          -- simplify_eq.
             eapply from_locale_step.
             eapply locale_step_atomic; eauto.
             2: { rewrite Hex in Hlive.
                  eapply Hlive; [done|].
                  rewrite /labels_match /role_enabled_model.
                  rewrite Hs.
                  set_solver. }
             by repeat econstructor.
        * clear Hnotriggered.
          destruct Hvalid as (Hvalid&Hmatch&Hlive&Hσ&Hskts).
          destruct Hskts as (shA&shB'&Hskts).
          rewrite Hex in Hskts. simpl in Hskts.
          rewrite Hskts in HSn.
          rewrite insert_commute in HSn; [|done].
          rewrite lookup_insert in HSn.
          simplify_eq.
          rewrite lookup_insert_Some in Hr.
          destruct Hr as [[-> Hr]|]; [|set_solver].
          simplify_eq.
          rewrite /state_get_m in Hr.
          rewrite Hs in Hr. simpl in Hr.
          rewrite /mABm in Hr.
          replace (S delivered) with (delivered + 1)%nat in Hr by lia.
          rewrite repeat_app in Hr. simpl in Hr.
          simplify_eq.
          rewrite /mABm.
          apply app_nil in Hr.
          naive_solver.
    - iClear "IH".
      iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
        first set_solver; auto.
      iModIntro. iSplitR.
      { iPureIntro. apply last_is_Some in Hneq as [m Hneq].
        apply last_Some in Hneq as [? ->].
        do 3 eexists; eapply SocketStepS; eauto; econstructor; eauto 2. }
      iIntros (v2' ? ? Hstep).
      pose proof (λ a b c d f g h i j k,
                  aneris_events_state_interp_receive_untracked a b c d f g h _ i _ _ _ _ (inl (ip_of_address saB,tidB)) j k Hstep)
        as Huntracked.
      iAssert (socket_address_group_own {[saB]})%I as "#HsaB".
      { iDestruct "Hrt" as "[(%send & %recv & _ & _ & _ & $ & _) _]". }
      inv_head_step.
      iPoseProof (aneris_state_interp_receive_some saB {[saB]} _ _ _ _ (Some _)
                      with "[] [$HΨ] [$Hσ] [$Hsh] [Hrt]")
        as (R' sagT) "(%HinT & #HownT & %Hhist & %HR & Hrt & Hrest)";
        [by set_solver..| | |].
      { iFrame "#". iPureIntro. set_solver. }
      { iDestruct "Hrt" as "[$ Hrt]". }
      simpl.
      iClear "Hrt".
      iNext.
      iMod "Hmk".
      iMod "Hrest" as "(Hσ & Hsh & Ha)".
      iDestruct (Huntracked with "Ha Hevs") as "[Hevs Ha]";
            [try done..| |].
      { eexists saB, _, _, _, _, _.
        repeat split; set_solver. }
      clear Huntracked.
      iDestruct (live_role_auth_elem_of with "Hlive_auth HB") as %Hrole.
      iAssert (⌜∃ x y, trace_last atr = Delivered x y⌝)%I as %(x&y&Hs).
      { rewrite /simple_valid_state_evolution in Hvalid.
        destruct (trace_last atr) eqn:Heq;
          [| |by eauto|by destruct sent;set_solver].
        - rewrite Heq in Hvalid.
          destruct Hvalid as (_&_&_&_&Hvalid).
          rewrite Hex in Hvalid.
          simpl in *.
          destruct Hvalid as (shA&shB'&Hvalid).
          rewrite Hvalid in HSn.
          rewrite insert_commute in HSn; [|set_solver].
          rewrite lookup_insert in HSn.
          simplify_eq.
          rewrite lookup_insert_Some in Hr.
          destruct Hr as [Hr|Hr]; set_solver.
        - rewrite Heq in Hvalid.
          destruct Hvalid as (_&_&_&_&Hvalid).
          rewrite Hex in Hvalid.
          simpl in *.
          destruct Hvalid as (shA&shB'&Hvalid).
          rewrite Hvalid in HSn.
          rewrite insert_commute in HSn; [|set_solver].
          rewrite lookup_insert in HSn.
          simplify_eq.
          rewrite lookup_insert_Some in Hr.
          destruct Hr as [Hr|Hr]; set_solver. }
      iMod (live_roles_auth_delete with "Hlive_auth HB") as "Hlive_auth".
      rewrite Hs.
      iMod (dead_role_auth_extend _ B_role with "Hdead_auth")
        as "[Hdead_auth Hdead_own]"; [destruct x; set_solver|].
      iModIntro.
      iExists (Received x y), B_role.
      rewrite Hhist.
      rewrite /thread_live_roles_interp=> /=.
      replace (match x with
               | 0%nat => {[B_role]}
               | S _ => {[B_role; Ndup; Ndrop; Ndeliver]}
               end ∖ {[B_role]}) with
              ((match x with
               | 0%nat => ∅
               | S _ => {[Ndup; Ndrop; Ndeliver]}
               end):gset simple_role); last first.
      { destruct x; set_solver. }
      replace (match x with
              | 0%nat => {[B_role]}
              | S _ => {[B_role; Ndup; Ndrop; Ndeliver]}
              end ∩ config_roles) with
        (match x with
         | 0%nat => ∅
         | S _ => {[Ndup; Ndrop; Ndeliver]}
         end ∩ config_roles:gset simple_role); last first.
      { destruct x; set_solver. }
      replace ({[B_role]}
                    ∪ all_roles
                      ∖ match x with
                        | 0%nat => {[B_role]}
                        | S _ => {[B_role; Ndup; Ndrop; Ndeliver]}
                        end) with
        (all_roles
       ∖ match x with
         | 0%nat => ∅
         | S _ => {[Ndup; Ndrop; Ndeliver]}
         end); last first.
      { destruct x; set_solver. }
      replace (config_roles
                    ∖ match x with
                      | 0%nat => {[B_role]}
                      | S _ => {[B_role; Ndup; Ndrop; Ndeliver]}
                      end) with
        (config_roles
       ∖ match x with
         | 0%nat => ∅
         | S _ => {[Ndup; Ndrop; Ndeliver]}
         end); last first.
      { destruct x; set_solver. }
      iFrame.
      iSplit.
      { iPureIntro.
        destruct Hvalid as (Hvalid&Hsteps&Hlive&Hσ&Hskts).
        rewrite /simple_valid_state_evolution. simpl.
        rewrite Hex in Hskts. simpl in Hskts.
        rewrite /trace_ends_in in Hex.
        rewrite Hex in Hσ.
        simpl in Hσ.
        split; [econstructor; [apply Hs|econstructor|done]|].
        rewrite Hs in Hσ.
        split; [done|].
        simplify_eq.
        simpl in *.
        destruct Hskts as (shA & shB' & Hskts).
        rewrite Hskts in HSn.
        simpl in *. rewrite insert_commute in HSn; [|done].
        rewrite lookup_insert in HSn.
        simplify_eq.
        assert (shB = shB') as <-.
        { rewrite lookup_insert_Some in Hr. set_solver. }
        split.
        { intros ℓ ζ Hlabels Henabled.
          assert (ℓ = A_role ∨ ℓ = B_role) as [Hℓ|Hℓ].
          { rewrite /labels_match /locale_simple_label in Hlabels.
            repeat case_match; simplify_eq; eauto. }
          - simplify_eq.
            rewrite /role_enabled_model in Henabled.
            destruct x; set_solver.
          - simplify_eq.
            eapply from_locale_step.
            eapply locale_step_atomic; eauto.
            2: { rewrite Hex in Hlive.
                 eapply Hlive; [done|].
                 rewrite /labels_match /role_enabled_model.
                 rewrite Hs.
                 destruct x; set_solver. }
            (* TODO: Clean this up. *)
            repeat econstructor.
            set_solver. done.
            instantiate (1:= σ).
            rewrite Hskts.
            set_solver. }
        split; [done|].
        exists shA, shB.
        rewrite Hskts.
        rewrite insert_commute; [|done].
        rewrite insert_insert.
        simpl.
        f_equiv.
        rewrite insert_insert.
        assert (r0 = mABm y) as ->.
        { rewrite lookup_insert_Some in Hr.
          destruct Hr as [[_ Hr]|[Hr _]]; [|done].
          rewrite /mABm in Hr.
          rewrite Hs in Hr.
          rewrite /state_get_m in Hr=> /=.
          replace (S y) with (y + 1)%nat in Hr by lia.
          rewrite repeat_app in Hr. simpl in Hr.
          simplify_eq.
          rewrite /mABm.
          apply snoc_eq in Hr.
          set_solver. }
        done. }
      iApply wp_value.
      by iApply "HΦ".
  Qed.

End with_Σ.

Definition initial_state shA shB :=
  ([mkExpr ipA (Aprog shA); mkExpr ipB (Bprog shB)],
     {| state_heaps := {[ipA:=∅; ipB:=∅]};
       state_sockets := {[ipA := {[shA := (sA, [])]}; ipB := {[shB := (sB, mABm 0)]}]};
       (* NB: Needs to be filled *)
       state_ports_in_use := ∅; (* NB: Needs to be filled *)
       state_ms := ∅; |}).

Lemma no_drop_dup_continued_simulation shA shB :
  ∃ (mtr : mtrace simple_fair_model),
    trfirst mtr = model_draft.Start ∧
    continued_simulation
      valid_state_evolution_fairness
      (trace_singleton $ initial_state shA shB)
      (trace_singleton (trfirst mtr)).
Proof.
  eexists (tr_singl model_draft.Start).
  split; [done|].

  assert (anerisPreG (fair_model_to_model simple_fair_model)
                     (anerisΣ (fair_model_to_model simple_fair_model))) as HPreG.
  { apply _. }
  eapply (strong_simulation_adequacy_multiple _ _ _ _ _ {[saA;saB]});
    [simpl; lia| |set_solver|set_solver| |set_solver|set_solver|..| |]=> /=.
  { intros ℓ ζ Hmatch Henabled. rewrite /role_enabled_model in Henabled. simpl.
    
    assert (ℓ = A_role ∨ ℓ = B_role) as [Heq|Heq] by set_solver; simplify_eq.
    - assert (ζ = ("0.0.0.0", 0%nat)) as ->.
      { rewrite /labels_match /locale_simple_label in Hmatch.
        by repeat case_match; simplify_eq. }
      eexists _. simpl. done.
    - assert (ζ = ("0.0.0.1", 0%nat)) as ->.
      { rewrite /labels_match /locale_simple_label in Hmatch.
        by repeat case_match; simplify_eq. }
      eexists _. simpl. done. }
  {
    iIntros (Hinv) "!> Hunallocated Hrt Hlive Hdead Hfree Hnode Hlbl Hsendevs Hrecvevs".
    iIntros "Hsend_obs Hrecv_obs".
    iIntros "!>".
    iDestruct (unallocated_split with "Hunallocated") as "[HA HB]"; [set_solver|].
    rewrite big_sepS_union; [|set_solver].
    iDestruct "Hrt" as "[HrtA HrtB]".
    rewrite !big_sepS_singleton.
    replace ({[A_role; B_role]} ∖ config_roles) with (({[A_role; B_role]}):gset _)
                                                     by set_solver.
    iDestruct (live_roles_own_split with "Hlive") as "[HliveA HliveB]";
      [set_solver|].
    (* TODO: Aneris WP discrepancies are acting up.. *)
    (*   iSplitL "HrtA HliveA HA". *)
    (*   { *)
    (*     iApply wp_mono; [|iApply aneris_wp_lift]; [by eauto|admit|]. *)
    (*     (* TODO: is_node ipA needs to be obtained from adequacy *) *)
    (*     iApply (aneris_wp_socket_interp_alloc_singleton with "HA"). *)
    (*     iIntros "HsaA". *)
    (*     iApply aneris_wp_unfold. *)
    (*     iIntros (tidA) "His_node". *)
    (*     iApply wp_mono; [|iApply (wp_A)]. with "[$HsaA]"). *)
    (* } *)
    admit.
Admitted.

Theorem choose_nat_terminates shA shB extr :
  trfirst extr = initial_state shA shB →
  extrace_fairly_terminating extr.
Proof.
  intros Hexfirst.
  destruct (no_drop_dup_continued_simulation shA shB) as (mtr & Hmtr & Hsim).
  eapply continued_simulation_fair_termination_preserved; [|by rewrite Hexfirst].
  rewrite /initial_reachable.
  destruct mtr; simpl in *; rewrite Hmtr; done.
Qed.
