From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import
     aneris_lang notation network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def
     state_interp_local_coh
     state_interp_gnames_coh
     state_interp_free_ips_coh
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_resource_coh
     state_interp_messages_history_coh
     auxiliary_state.

From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  Lemma config_wp_correct : ⊢ config_wp.
  Proof.
    rewrite /config_wp. iIntros. iModIntro. iIntros (σ1 δ k σ2 ks nt Hstep) "[Hσ Hm]".
    rewrite /state_interp; simplify_eq /=.
    iDestruct "Hσ" as (γm mh)
           "(%Hhist & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iApply step_fupd_fupd; iApply step_fupd_intro; first done.
    destruct Hstep as
        [ ip σ k Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr | σ]; simpl.
    { iExists δ. iIntros "!> !>". iSplit.
      - iPureIntro. split_and!; last by left. simplify_eq.
        eapply message_history_evolution_deliver_message; set_solver.
      - iFrame "Hm". iExists γm, mh. iFrame "Hsi".
        iSplitR; first done.
        iSplitR; [eauto using gnames_coh_update_sockets|].
        iSplitR; [eauto using network_sockets_coh_deliver_message|].
        iSplitR; [eauto using messages_history_coh_deliver_message|].
        iFrame. iSplitL "Hlcoh".
        + by iApply (local_state_coh_deliver_message with "[Hlcoh]").
        + iSplitL "Hfreeips". by iApply free_ips_coh_deliver_message.
          rewrite /messages_resource_coh. iApply (big_sepS_mono with "Hmres").
          iIntros (??) "[Hmr|%Hmr]"; last eauto with iFrame. iLeft.
          iDestruct "Hmr" as (phi) "(Hphi & Hphi2)". eauto with iFrame. }
    iExists δ. iIntros "!> !>". iSplit. iPureIntro.
    split_and!; last by left.
    eapply message_history_evolution_drop_message; set_solver.
    (* by eapply message_history_evolution_drop_message. *)
    iFrame "Hm". iExists γm, mh. iFrame. iSplitR; first done. iSplitR; first done.
    iSplitR. iPureIntro. simpl. eauto.
    iSplitR. iPureIntro. simpl. by eapply messages_history_drop_message.
    rewrite /messages_resource_coh. iApply (big_sepS_mono with "Hmres").
    iIntros (??) "[Hmr|%Hmr]"; last eauto with iFrame. iLeft.
    iDestruct "Hmr" as (phi) "(Hphi & Hphi2)". eauto with iFrame.
  Qed.

End state_interpretation.
