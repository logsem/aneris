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
     state_interp_messages_history
     state_interp_adversary_firewall_coh.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  Lemma config_wp_correct : ⊢ config_wp.
  Proof.
    rewrite /config_wp. iIntros. iModIntro.
    iIntros (ex atr c σ2 Hexvalid Hex Hstep) "(Hevs & Hsi & Hm & % & Hauth)". simpl.
    rewrite /state_interp; simplify_eq /=.
    rewrite (last_eq_trace_ends_in ex c) /=; last done.
    iDestruct "Hsi" as (γm mh sags)
                         "(%Hhist & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    assert (∃ n, n = trace_length ex) as [n Heqn] by eauto.
    rewrite -{2}Heqn.
    assert (∃ n', n' = trace_length ex) as [n' Heqn'] by eauto.
    rewrite -!Heqn'.
    clear Heqn Heqn'.
    iInduction (n) as [|n] "IHlen" forall (n'); last first.
    { by iMod ("IHlen" with
                "Hevs Hnauth Hsi Hlcoh Hfreeips Hmctx Hmres Hm Hauth") as "H". }
    iAssert (|={⊤,∅}=>|={∅,⊤}=> True)%I as "Hshift".
    { by iApply fupd_mask_intro_subseteq. }
    iMod (steps_auth_update_S with "Hauth") as "Hauth".
    iMod "Hshift". iModIntro.
    iModIntro. iNext. iModIntro.
    iMod "Hshift". iModIntro.
    destruct c as [tp1 σ1]; simpl in *.
    iExists (trace_last atr), ().
    rewrite (aneris_events_state_interp_same_tp _ (tp1, _)); [| |done|done]; last first.
    { econstructor; [done| |done]. econstructor 2; eauto. }
    pose proof Hstep as Hstep'.
    inversion Hstep as [ip σ Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr | σ];
      simplify_eq/=.
    - iFrame "Hm Hevs Hauth".
      iSplit; last by iPureIntro; left.
      iExists γm, mh, sags. iFrame "Hsi".
      iSplit.
      { erewrite  <- message_history_evolution_deliver_message; eauto with set_solver. }
      iSplitR; [eauto using gnames_coh_update_sockets|].
      iSplitR; [eauto using network_sockets_coh_deliver_message|].
      iSplitR; [eauto using messages_history_coh_deliver_message|].
      iFrame. iSplitL "Hlcoh".
      { by iApply (local_state_coh_deliver_message with "[Hlcoh]"). }
      iSplitL "Hfreeips". by iApply free_ips_coh_deliver_message.
      iSplitL "Hmctx".
      { iApply adversary_firewall_coh_config_step; [eapply Hstep| done]. }
      rewrite /messages_resource_coh.
      iDestruct "Hmres" as "[$ [$ Hmres]]".
      iDestruct "Hmres" as (ms Hle) "[HmresT Hmres]".
      iExists ms. iSplit; [done|]. iFrame "HmresT".
      iApply (big_sepS_mono with "Hmres").
      iIntros (??) "Hmr".
      iDestruct "Hmr" as (sagT sagR Φ Hsag) "[HΦ [HsagT Hmr]]".
      iExists sagT, sagR, Φ.  iSplit; [done|]. iFrame "HΦ HsagT".
      iDestruct "Hmr" as "[Hmr | Hmr]".
      + iDestruct "Hmr" as (m' Hmeq) "Hmr".
        iLeft. iExists m'. iSplit; done.
      + iDestruct "Hmr" as %(m' & Hmeq & Hrecv).
        iRight. iExists m'. done.
    - iFrame "Hevs Hm Hauth".
      iSplitL; last by iPureIntro; left.
      iExists γm, mh, sags. iFrame; simpl.
      iSplit.
      { iPureIntro.
        rewrite -message_history_evolution_drop_message; first done.
        apply gmultiset_difference_subseteq. }
      iSplitR; first done.
      iSplitR; first done.
      iSplitR; first by iPureIntro; eapply messages_history_drop_message.
      rewrite /messages_resource_coh.
      iDestruct "Hmres" as "[$ [$ Hmres]]".
      iDestruct "Hmres" as (ms Hle) "[HmresT Hmres]".
      iExists ms. iSplit; [done|]. iFrame "HmresT".
      iApply (big_sepS_mono with "Hmres").
      iIntros (??) "Hmres".
      iDestruct "Hmres" as (sagT sagR Φ Hsag) "[HΦ [HsagT Hmres]]".
      iExists sagT, sagR, Φ.  iSplit; [done|]. iFrame "HΦ HsagT".
      iDestruct "Hmres" as "[Hmres | Hmres]".
      + iDestruct "Hmres" as (m' Hmeq) "Hmres".
        iLeft. iExists m'. iSplit; done.
      + iDestruct "Hmres" as %(m' & Hmeq & Hrecv).
        iRight. iExists m'. done.
  Qed.

End state_interpretation.
