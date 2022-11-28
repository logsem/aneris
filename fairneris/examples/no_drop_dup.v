From stdpp Require Import list fin_maps.
From iris.proofmode Require Import proofmode.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import model_draft.
From fairneris.aneris_lang Require Import aneris_lang.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.

Definition Aprog shA : expr := SendTo #(LitSocket shA) #"Hello" #saB.
Definition Bprog shB : expr := ReceiveFrom #(LitSocket shB).

Section with_Σ.
  Context `{anerisG (fair_model_to_model simple_fair_model) Σ}.

  Lemma wp_A shA :
    {{{ shA ↪[ip_of_address saA] sA ∗ saA ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) ∗
        live_roles_frag_own A_role }}}
      Aprog shA @[ip_of_address saA]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & Hmsg & HA) HΦ".
    rewrite aneris_wp_eq /aneris_wp_def.
    iIntros (tid) "Hnode".
    iApply wp_lift_atomic_head_step_no_fork; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(%Hvalid & Hevs & Hσ & Hlive & Hauth) /=".
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
                  (inl (ip_of_address saA,tid)) j k Hstep)
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
    (* Derive this using ghost state tracking current live roles *)
    iDestruct (live_roles_auth_elem_of with "Hlive HA") as %Hrole.
    (* assert (A_role ∈ simple_live_roles (trace_last atr)) as Hrole by admit. *)
    assert ((trace_last atr) = model_draft.Start) as Heq.
    { destruct (trace_last atr); simpl in Hrole; set_solver. }
    (* iDestruct "Hlive" as (M HM) "Hlive". *)
    iMod (live_roles_auth_delete with "Hlive HA") as "Hlive".
    rewrite Heq.
    iMod (live_roles_auth_extend _ Ndup with "Hlive") as "[Hlive HNdup]";
      [set_solver|].
    iMod (live_roles_auth_extend _ Ndrop with "Hlive") as "[Hlive HNdrop]";
      [set_solver|].
    iMod (live_roles_auth_extend _ Ndeliver with "Hlive") as "[Hlive HNdeliver]";
      [set_solver|].
    iExists (Sent 1), (Some A_role).
    iDestruct (Huntracked with "Hrt Hevs") as "[$ Hrt]";
          [done..|set_solver|].
    iModIntro.
    rewrite -Hmhe.
    iFrame.
    iSplitR; [done|].
    simpl.
    iSpecialize ("HΦ" with "[//]").
    iSplitR "HΦ"; [|by iExists _; iFrame].
    iSplitR "Hlive"; last first.
    { replace ({[A_role; B_role]} ∖ {[A_role]}) with
              ({[B_role]}:gset simple_role) by set_solver.
      rewrite (union_comm_L {[Ndup]}).
      rewrite (union_comm_L {[Ndrop]}).
      rewrite (union_comm_L {[Ndeliver]}).
      done. }
    iPureIntro.
    rewrite /simple_valid_state_evolution in Hvalid.
    rewrite /simple_valid_state_evolution.
    rewrite Heq in Hvalid. simpl in Hvalid.
    simpl.
    destruct Hvalid as (Hvalid&Hms&Hskt).
    rewrite /trace_ends_in in Hex.
    rewrite Hex in Hms. simpl in Hms. rewrite Hms.
    split; [econstructor; [apply Heq|econstructor|done]|].
    split.
    { rewrite (comm _ ∅). f_equiv. f_equiv. eauto. }
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

  Lemma wp_B shB :
    {{{ shB ↪[ip_of_address saB] sB ∗ saB ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) ∗
        live_roles_frag_own B_role }}}
      Bprog shB @[ip_of_address saB]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & #HΨ & HB) HΦ".
    rewrite aneris_wp_eq /aneris_wp_def.
    iIntros (tid) "Hnode".
    iLöb as "IH".
    iApply wp_lift_head_step; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(%Hvalid & Hevs & Hσ & Hlive & Hauth) /=".
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
                                 _ f _ _ _ _ (inl (ip_of_address saB,tid)) g h
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
        iDestruct (live_roles_auth_elem_of with "Hlive HB") as %Hrole.
        iModIntro.
        destruct (trace_last atr) eqn:Hs; [..|by set_solver].
        * iExists (trace_last atr), (Some B_role).
          rewrite -message_history_evolution_id; iFrame.
          rewrite Hnotriggered;
            [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?)].
          iSpecialize ("IH" with "[$] [$] [$] [$] [$]").
          rewrite Hs.
          iFrame.
          iPureIntro.
          rewrite /trace_ends_in in Hex.
          rewrite /simple_valid_state_evolution.
          rewrite /simple_valid_state_evolution in Hvalid.
          destruct Hvalid as [Hvalid Hm].
          rewrite Hex in Hm=> /=.
          rewrite Hs in Hm.
          split; [|done].
          econstructor; [apply Hs|econstructor|done].
        * iExists (trace_last atr), (Some B_role).
          rewrite -message_history_evolution_id; iFrame.
          rewrite Hnotriggered;
            [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?)].
          iSpecialize ("IH" with "[$] [$] [$] [$] [$]").
          rewrite Hs.
          iFrame.
          iPureIntro.
          rewrite /trace_ends_in in Hex.
          rewrite /simple_valid_state_evolution.
          rewrite /simple_valid_state_evolution in Hvalid.
          destruct Hvalid as [Hvalid Hm].
          rewrite Hex in Hm=> /=.
          rewrite Hs in Hm.
          split; [|done].
          econstructor; [apply Hs|econstructor|done].
        * clear Hnotriggered.
          destruct Hvalid as (Hvalid&Hσ&Hskts).
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
                  aneris_events_state_interp_receive_untracked a b c d f g h _ i _ _ _ _ (inl (ip_of_address saB,tid)) j k Hstep)
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
      iDestruct (live_roles_auth_elem_of with "Hlive HB") as %Hrole.
      iAssert (⌜∃ x y, trace_last atr = Delivered x y⌝)%I as %(x&y&Hs).
      { rewrite /simple_valid_state_evolution in Hvalid.
        destruct (trace_last atr) eqn:Heq; [| |by eauto|set_solver].
        - rewrite Heq in Hvalid.
          destruct Hvalid as (_&_&Hvalid).
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
          destruct Hvalid as (_&_&Hvalid).
          rewrite Hex in Hvalid.
          simpl in *.
          destruct Hvalid as (shA&shB'&Hvalid).
          rewrite Hvalid in HSn.
          rewrite insert_commute in HSn; [|set_solver].
          rewrite lookup_insert in HSn.
          simplify_eq.
          rewrite lookup_insert_Some in Hr.
          destruct Hr as [Hr|Hr]; set_solver. }
      iMod (live_roles_auth_delete with "Hlive HB") as "Hlive".
      iModIntro.
      iExists (Received x y), (Some B_role).
      rewrite Hhist.
      rewrite Hs.
      rewrite /thread_live_roles_interp=> /=.
      replace ({[B_role; Ndup; Ndrop; Ndeliver]} ∖ {[B_role]}) with
              ({[Ndup; Ndrop; Ndeliver]}:gset simple_role) by set_solver.
      iFrame.
      iSplit.
      { iPureIntro.
        destruct Hvalid as (Hvalid&Hσ&Hskts).
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
        exists shA, shB.
        rewrite Hskts.
        rewrite insert_commute; [|done].
        rewrite insert_insert.
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
      iExists _. iSplit; [done|].
      by iApply "HΦ".
  Qed.

End with_Σ.
