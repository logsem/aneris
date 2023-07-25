From aneris.examples.reliable_communication.lib.sharding Require Import sharding_code.
From aneris.examples.reliable_communication.lib.sharding.spec
    Require Import resources.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.aneris_lang.lib Require Import map_proof lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
Import inject.

Section proof.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ, !MTS_resources, lock : gname,
                     γ : gname, sa : socket_address, N : namespace}.

  Definition MTshard := (user_params_at_shard γ sa).

  Lemma server_request_handler_at_shard_spec :
    ∀ l reqv reqd lk,
    {{{
      MTshard.(MTS_handler_pre) reqv reqd ∗
      is_lock N (ip_of_address sa) lock lk (shard_lock l (ip_of_address sa) γ)
    }}}
    server_request_handler_at_shard #l lk reqv @[ip_of_address sa]
    {{{ res, RET res;
      ⌜Serializable rep_ser res⌝ ∗
      MTshard.(MTS_handler_post) res reqd I
    }}}.
  Proof.
    iIntros (l reqv data lk Φ)
        "([(%E & %Q & %k & %v & % & % & -> & -> & %shards_k & HQ)|
         (%E & %Q & %k & % & %k_keys & -> & -> & %shards_k & HQ)] & #lock) HΦ".
    {
      rewrite/server_request_handler_at_shard.
      wp_pures.
      wp_apply (acquire_spec with "lock").
      iIntros "% (-> & locked & (%db & %M & %shard &
                    %db_M & ●_γ & l_db & %M_shard))".
      wp_pures.
      wp_load.
      wp_apply (wp_map_insert $! db_M).
      iIntros "%db' %db'_M".
      wp_bind (Store _ _).
      iApply aneris_wp_atomic.
      iMod "HQ" as "(%old & k_old & HQ)".
      iModIntro.
      wp_store.
      iMod (shard_update _ _ _ _ (Some v) with "[//] ●_γ k_old")
            as "(●_γ & k_v)".
      iMod ("HQ" with "k_v") as "Q".
      iModIntro.
      wp_pures.
      wp_apply (release_spec with "[$locked $lock l_db ●_γ]").
      {
        iExists db', (<[k:=v]> M), (<[k:=Some v]> shard).
        iFrame.
        iSplit; first done.
        iPureIntro=>k' k'_key.
        move: (M_shard k' k'_key).
        case: (DB_key_eq_dec k k')=>[->|diff];
        [by rewrite 2!lookup_insert|by rewrite 2!(lookup_insert_ne _ _ _ _ diff)].
      }
      iIntros "% ->".
      wp_pures.
      iApply "HΦ".
      iSplit.
      {
        iPureIntro=>/=.
        exists #().
        by left.
      }
      iLeft.
      iExists E, Q, k, v.
      by do 2 (iSplit; first done).
    }
    rewrite/server_request_handler_at_shard.
    wp_pures.
    wp_apply (acquire_spec with "lock").
    iIntros "% (-> & locked & (%db & %M & %shard &
                  %db_M & ●_γ & l_db & %M_shard))".
    wp_pures.
    wp_bind (Load _).
    iApply aneris_wp_atomic.
    iMod "HQ" as "(%v & k_v & HQ)".
    iModIntro.
    wp_load.
    iPoseProof (shard_valid with "[//] ●_γ k_v") as "%M_k".
    move: M_k (M_shard k k_keys)=>->[->] {v}.
    iMod ("HQ" with "k_v") as "Q".
    iModIntro.
    wp_apply (wp_map_lookup $! db_M).
    case eq' : (M !! k) =>[a|]; iIntros "% ->".
    {
      wp_pures.
      wp_apply (release_spec with "[$lock $locked ●_γ l_db]").
      {
        iExists db, M, shard.
        iFrame.
        by iSplit.
      }
      iIntros "% ->".
      wp_pures.
      iApply "HΦ".
      iSplit.
      {
        iPureIntro=>/=.
        exists (InjRV $a).
        right.
        split=>//=.
        left.
        exists $a.
        split; [done|apply DB_vals_serializable].
      }
      iRight.
      iExists E, Q, k.
      iSplit; first done.
      iExists (Some a).
      by iFrame.
    }
    wp_pures.
    wp_apply (release_spec with "[$lock $locked ●_γ l_db]").
    {
      iExists db, M, shard.
      iFrame.
      by iSplit.
    }
    iIntros "% ->".
    wp_pures.
    iApply "HΦ".
    iSplit.
    {
      iPureIntro=>/=.
      exists (InjLV #()).
      right.
      split=>//=.
      by right.
    }
    iRight.
    iExists E, Q, k.
    iSplit; first done.
    iExists None.
    by iFrame.
  Qed.

End proof.