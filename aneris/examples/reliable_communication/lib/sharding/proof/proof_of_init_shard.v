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

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Lemma init_shard_spec_holds ShardInit shard_si sa γ :
    let user_params := user_params_at_shard γ sa in
    run_server_spec ShardInit shard_si -∗
    sa ⤇ shard_si -∗
    {{{
      ShardInit ∗
      shard_mem γ (gset_to_gmap None DB_keys) ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]}
    }}}
      init_shard (s_serializer DB_key_ser) (s_serializer DB_val_ser)
        #sa @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    simpl.
    iIntros "#run_shard #shard_si !>%Φ (ShardInit & ●_γ & ∅ & free) HΦ".
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
    simpl.
    wp_apply ("run_shard" with "[] [$ShardInit $∅ $free $shard_si]"); last done.
    iIntros (reqv reqd Ψ) "!>pre HΨ".
    wp_pures.
    wp_apply (server_request_handler_at_shard_spec with "[pre $lock]").
    { iDestruct "pre" as "[(%x&%y&%z&%t&H1&H2&H3&H4&H5&H6)
                          |(%x&%y&%z&H1&H2&H3&H4&H5&H6)]".
      - iLeft.
        iExists x, y, z, t.
        iFrame "H1 H2 H3 H4 H5 H6".
      - iRight.
        iExists x, y, z.
        iFrame "H1 H2 H3 H4 H5 H6". }
    iIntros (res).
    iApply "HΨ".
  Qed.

End proof.
