From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.program_logic Require Export gen_heap_light.
From aneris.aneris_lang Require Export
     aneris_lang notation network resources
     state_interp_def
     state_interp_local_coh
     state_interp_gnames_coh
     state_interp_free_ips_coh
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_resource_coh
     state_interp_messages_history_coh.

From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Σ}.

  Lemma config_wp_correct : ⊢ config_wp.
  Proof.
    rewrite /config_wp.
    iIntros.
    iModIntro.
    iIntros (σ1 k σ2 ks nt Hstep) "Hst".
    rewrite /state_interp; simplify_eq /=.
    iDestruct "Hst"
      as (γm mhγ)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iApply step_fupd_fupd; iApply step_fupd_intro; first done.
    iExists γm, mhγ.
    iFrame.
    iIntros "!> !>".
    destruct Hstep as
        [ ip σ k Sn Sn' sh a skt R m Hm HSn Hsh HSn' Hsaddr | σ]; simpl.
    { iFrame "Hsi".
      iSplitR; [eauto using gnames_coh_deliver_message|].
      iSplitR; [eauto using network_sockets_coh_deliver_message|].
      iSplitR; [eauto using messages_history_coh_deliver_message|].
      iSplitL "Hlcoh".
      - by iApply (local_state_coh_deliver_message with "[Hlcoh]").
      - by iApply free_ips_coh_deliver_message. }
    iFrame.
    iSplitR; first done.
    iSplitR; first done.
    iPureIntro. by eapply messages_history_drop_message.
  Qed.
  (* TODO: The only subtle point will be to show that receive_buffers_coh is
     preserved for delivery config step. *)


End state_interpretation.
