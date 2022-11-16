From iris.proofmode Require Import proofmode.
From trillium.program_logic Require Import ectx_lifting.
From fairneris Require Import model_draft.
From fairneris.aneris_lang Require Import aneris_lang.
From fairneris.aneris_lang.state_interp Require Import state_interp state_interp_events.
From fairneris.aneris_lang.program_logic Require Import aneris_weakestpre.

Definition Aprog shA : expr :=
  SendTo #(LitSocket shA) #"Hello" #saB.

Definition Bprog shB : expr :=
  ReceiveFrom #(LitSocket shB).

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
                aneris_events_state_interp_send_untracked {[saA]} b c d f g h _ i _ _ _ _ (inl (ip_of_address saA,tid)) j k Hstep)
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
    destruct Hvalid as [Hms Hskt].
    rewrite /trace_ends_in in Hex.
    rewrite Hex in Hms. simpl in Hms. rewrite Hms.
    split.
    { rewrite (comm _ ∅). f_equiv. f_equiv. eauto. }
    rewrite Hex in Hskt.
    simpl in Hskt.
    done.
  Admitted.

  Lemma wp_B shB :
    {{{ shB ↪[ip_of_address saB] sB ∗ saB ⤳ (∅,∅) ∗ saB ⤇ (λ _, True) }}}
      Bprog shB @[ip_of_address saA]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(Hsh & Hrt & #HΨ) HΦ".
    rewrite aneris_wp_eq /aneris_wp_def.
    iIntros (tid) "Hnode".
    iLöb as "IH".
    iApply wp_lift_head_step; auto.
    iIntros (ex atr K tp1 tp2 σ Hexvalid Hex) "(Hevs & Hσ & Hm & Hauth) /=".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    rewrite (last_eq_trace_ends_in _ _ Hex).
    iDestruct (aneris_state_interp_socket_valid with "Hσ Hsh")
      as (Sn r) "[%HSn (%Hr & %Hreset)]".
    iMod (fupd_mask_intro_subseteq _ ∅ True%I with "[]") as "Hmk";
      first set_solver; auto.
    iModIntro. iSplitR.
    { iPureIntro. admit. }
    iIntros (v2' ? ? Hstep).
    admit.
  Admitted.

End with_Σ.
