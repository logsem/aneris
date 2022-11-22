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
    {{{ shA ↪[ip_of_address saA] sA ∗ saA ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) }}}
      Aprog shA @[ip_of_address saA]
    {{{ v, RET #v; True }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & Hmsg) HΦ".
    rewrite aneris_wp_eq /aneris_wp_def.
    iIntros (tid) "Hnode".
    iApply wp_lift_atomic_head_step_no_fork; [done|].
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex Hlocale) "(Hevs & Hσ & %Hvalid & Hauth) /=".
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
    assert (A ∈ simple_live_roles (trace_last atr)) as Hrole by admit.
    assert ((trace_last atr) = model_draft.Start) as Heq.
    { destruct (trace_last atr); simpl in Hrole; set_solver. }
    iExists (Sent 1), (Some A).
    iDestruct (Huntracked with "Hrt Hevs") as "[$ Hrt]";
          [done..|set_solver|].
    iModIntro.
    rewrite -Hmhe.
    iFrame.
    iSplitR; [done|].
    simpl.
    iSpecialize ("HΦ" with "[//]").
    iSplitR "HΦ"; [|by iExists _; iFrame].
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
  Admitted.

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
    {{{ shB ↪[ip_of_address saB] sB ∗ saB ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) }}}
      Bprog shB @[ip_of_address saB]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & #HΨ) HΦ".
    rewrite aneris_wp_eq /aneris_wp_def.
    iIntros (tid) "Hnode".
    iLöb as "IH".
    iApply wp_lift_head_step; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(Hevs & Hσ & %Hvalid & Hauth) /=".
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
        iModIntro.
        (* Derive this using ghost state tracking current live roles *)
        assert (B ∈ simple_live_roles (trace_last atr)) as Hrole by admit.
        destruct (trace_last atr) eqn:Hs; [..|by set_solver].
        * iExists (trace_last atr), (Some B).
          rewrite -message_history_evolution_id; iFrame.
          rewrite Hnotriggered;
            [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?)].
          iFrame.
          iSplit.
          { iPureIntro.
            rewrite /trace_ends_in in Hex.
            rewrite /simple_valid_state_evolution.
            rewrite /simple_valid_state_evolution in Hvalid.
            destruct Hvalid as [Hvalid Hm].
            rewrite Hex in Hm=> /=.
            split; [|done].
            rewrite Hs.
            econstructor; [apply Hs|econstructor|done].
          }
          iApply ("IH" with "[$] [$] [$] [$]").
        * iExists (trace_last atr), (Some B).
          rewrite -message_history_evolution_id; iFrame.
          rewrite Hnotriggered;
            [|done|done| by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?&?&?&?&?) |
              by intros ? (?&?&?&?&?&?&?&?&?)].
          iFrame.
          iSplit.
          { iPureIntro.
            rewrite /trace_ends_in in Hex.
            rewrite /simple_valid_state_evolution.
            rewrite /simple_valid_state_evolution in Hvalid.
            destruct Hvalid as [Hvalid Hm].
            rewrite Hex in Hm=> /=.
            split; [|done].
            rewrite Hs.
            econstructor; [apply Hs|econstructor|done].
          }
          iApply ("IH" with "[$] [$] [$] [$]").
        * (* Derive this from trace property, or change model. *)
          assert (∃ delivered', delivered = S delivered') as [delivered' ->]
                                                               by admit.
          simpl in *.
          destruct Hvalid as (Hvalid&Hσ&Hskts).
          rewrite Hs in Hskts.
          simpl in *.
          clear Hnotriggered.
          admit.                (* Assert contradiction from state determining
                                   buffer is non-empty, while it is empty. *)
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
      iModIntro.
      (* TODO: Deduce that we are in [Delivered n m] from buffer state,
               and liveness of [B] *)
      assert (∃ x y, trace_last atr = Delivered x (S y)) as (x&y&Hs).
      { admit. }
      iExists (Received x y), (Some B).
      rewrite Hhist.
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
  Admitted.

End with_Σ.
