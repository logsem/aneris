From aneris.examples.reliable_communication.lib.sharding Require Import sharding_code.
From aneris.examples.reliable_communication.lib.sharding.spec
    Require Import resources.
From aneris.examples.reliable_communication.lib.sharding.proof
    Require Import proof_of_server_handler.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.reliable_communication.lib.mt_server Require Import
                    mt_server_code user_params.
From aneris.aneris_lang.lib Require Import lock_proof map_proof.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.mt_server.proof Require Import
                    mt_server_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.

Section proof.

  Context `{!anerisG Mdl Σ, !DBG Σ, !DB_params}.

  Lemma init_shard_spec_holds ShardInit shard_si sa γ :
    {{{
      ShardInit ∗ shard_mem γ (gset_to_gmap None DB_keys) ∗
      sa ⤇ shard_si ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      (@run_server_spec _ _ _ _ (user_params_at_shard γ sa) ShardInit shard_si)
    }}}
      init_shard (s_serializer DB_serialization) #sa @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(ShardInit & ●_γ & #shard_si & ∅ & free & #run_shard) HΦ".
    rewrite/init_shard.
    wp_pures.
    wp_apply (wp_map_empty with "[//]").
    iIntros (db db_empty).
    wp_alloc l as "Hl".
    wp_pures.
    wp_apply (newlock_spec DB_inv_name _ (shard_lock l (ip_of_address sa) γ)
                with "[●_γ Hl]").
    {
      iExists db, ∅, (gset_to_gmap None DB_keys).
      iFrame.
      iSplit; first done.
      iSplit.
      { iApply big_sepS_intro. by iIntros "!>% % % %". }
      iApply big_sepS_intro.
      iIntros "!>%k %k_key".
      iPureIntro.
      by apply lookup_gset_to_gmap_Some.
    }
    iIntros (lk lock) "#lock".
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL "HΦ"; iNext; first by iApply "HΦ".
    rewrite/start_shard.
    wp_pures.
    wp_apply ("run_shard" with "[] [$ShardInit $∅ $free $shard_si]"); last done.
    iIntros (reqv reqd Ψ) "!>pre HΨ".
    wp_pures.
    wp_apply (server_request_handler_at_shard_spec with "[$pre $lock]").
    iIntros (res).
    iApply "HΨ".
  Qed.

End proof.