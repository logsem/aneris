From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export adequacy.
From aneris.aneris_lang Require Import
     aneris_lang network resources.
From aneris.prelude Require Import gmultiset.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def
     state_interp_local_coh
     state_interp_gnames_coh
     state_interp_free_ips_coh
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_resource_coh
     state_interp_messages_history_coh
     state_interp_events
     state_interp_messages_history.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  (* TODO: Move this elsehwere and use it where we now use ad hoc induction *)
  Lemma fupd_elim_laterN E1 E2 n (P:iProp Σ) :
    E2 ⊆ E1 → P -∗ |={E1,E2}=> |={E2}▷=>^n |={E2,E1}=> P.
  Proof.
    iIntros (Hle) "HP".
    iApply fupd_mask_intro; [done|].
    iIntros "Hclose".
    iInduction n as [|n] "IHn"; [by iMod "Hclose"|]=> /=.
    iIntros "!>!>!>".
    iApply ("IHn" with "HP Hclose").
  Qed.

  Lemma config_wp_correct : ⊢ config_wp.
  Proof.
    rewrite /config_wp. iModIntro.
    iIntros (ex atr c σ2 Hexvalid Hex Hstep) "(Hevs & Hsi & Hm & % & Hauth)".
    rewrite (last_eq_trace_ends_in ex c); [|done].
    iDestruct "Hsi" as (γm mh)
                         "(%Hhist & %Hgcoh & %Hnscoh & %Hmhcoh &
                           Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iApply fupd_elim_laterN; [solve_ndisj|].
    destruct c as [tp1 σ1]=> /=.
    iExists (trace_last atr), ().
    rewrite (aneris_events_state_interp_same_tp _ (tp1, _));
      [| |done|done]; last first.
    { econstructor; [done| |done]. econstructor 2; eauto. }
    iFrame "Hm Hevs Hauth Hsi".
    iSplit; [|by iPureIntro; left].
    iExists γm, mh. iFrame.
    inversion Hstep as [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr|σ|σ];
      simplify_eq/=.
    - iSplit.
      { apply (last_eq_trace_ends_in) in Hex as ->.
        erewrite <- message_history_evolution_deliver_message;
          eauto with set_solver. }
      iSplitR; [eauto using gnames_coh_update_sockets|].
      iSplitR; [eauto using network_sockets_coh_deliver_message|].
      iSplitR; [iPureIntro; apply messages_history_coh_drop_message;
                eauto using messages_history_coh_deliver_message|].
      iSplitL "Hlcoh";
        [by iApply (local_state_coh_deliver_message with "Hlcoh")|].
      iApply free_ips_coh_ms. by iApply free_ips_coh_deliver_message.
    - iFrame.
      iSplit.
      { iPureIntro.
        simplify_eq /=.
        apply (last_eq_trace_ends_in) in Hex as ->.
        rewrite -message_history_evolution_duplicate_message; [done|].
        by apply gmultiset_singleton_subseteq_l. }
      iSplitR; [done|]. iSplitR; [done|].
      iPureIntro. by apply messages_history_coh_duplicate_message.
    - iFrame.
      iSplit.
      { iPureIntro.
        simplify_eq /=.
        apply (last_eq_trace_ends_in) in Hex as ->.
        rewrite -message_history_evolution_drop_message; first done.
        apply gmultiset_difference_subseteq. }
      iSplitR; [done|]. iSplitR; [done|].
      by iPureIntro; eapply messages_history_coh_drop_message.
  Qed.

End state_interpretation.
