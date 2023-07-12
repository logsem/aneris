From aneris.examples.reliable_communication.lib.sharding Require Import sharding_code.
From aneris.examples.reliable_communication.lib.sharding.spec
    Require Import resources.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import list_proof.
Import inject.

Section proof.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Lemma request_answer_ser k sa res (reqd : ReqData) :
    (user_params_at_shard (DBG_hash k) sa).(MTS_handler_post) res reqd I -∗
      ⌜Serializable rep_ser res⌝ ∗
      user_params_at_server.(MTS_handler_post) res reqd I.
  Proof.
    iIntros "[(%E & %Q & %k' & %v' & Q & -> & ->)|
              (%E & %Q & %k' & -> & (%v' & -> & Q))]".
    { iSplit. { iPureIntro=>/=. exists #(). by left. }
      iLeft. iExists E, Q, k', v'. iFrame. by iSplit. }
    iSplit.
    { iPureIntro=>/=. exists $v'. right. split=>//=.
        case: v'=>[v'|]; [left|by right]. exists $v'. split=>//=.
        apply DB_vals_serializable. }
    iRight.
    iExists E, Q, k'.
    iSplit; first done.
    iExists v'.
    by iFrame.
  Qed.

  Definition shards_data_spec (shardsv : val) data : iProp Σ :=
    ∀ k, ⌜k ∈ DB_keys⌝ -∗
    {{{ True }}}
      shardsv $k @[ip_of_address DB_addr]
    {{{ RET #(DB_hash k);
      ∃ rpc sa N γ MTR lk (l : list (val*val)), ⌜is_list l data⌝ ∗
      is_lock N (ip_of_address DB_addr) γ lk
          (MTR.(MTSCanRequest) (ip_of_address DB_addr) rpc) ∗
    (@make_request_spec _ _ _ _ (user_params_at_shard (DBG_hash k) sa) MTR) ∗
    ⌜l !! (DB_hash k) = Some (rpc, lk)⌝ }}}.

  Lemma client_request_handler_at_server_spec :
    ∀ data shardsv reqv reqd,
    {{{
      user_params_at_server.(MTS_handler_pre) reqv reqd ∗
      shards_data_spec shardsv data
    }}}
      client_request_handler_at_server data shardsv reqv @[ip_of_address DB_addr]
    {{{ res, RET res;
      ⌜Serializable rep_ser res⌝ ∗
      user_params_at_server.(MTS_handler_post) res reqd I
    }}}.
  Proof.
    iIntros (data shardsv reqv reqd Φ)
          "([(%E & %Q & %k & %v & % & % & -> & -> & HQ)|
        (%E & %Q & %k & % & % & -> & -> & HQ)] & #shards_data_spec) HΦ".
    {
      rewrite/client_request_handler_at_server.
      wp_pures.
      wp_apply "shards_data_spec"; [done..|].
      iIntros "(%rpc & %sa & %N & %γ & %MTR & %lk & %l &
                  %l_data & #lock & #make_request & %l_k)".
      wp_pures.
      wp_apply wp_list_nth; first done.
      iIntros "% [(-> & %abs) | (%r & -> & %l_k_r)]".
      {
        apply Nat2Z.inj_le in abs.
        apply lookup_ge_None_2 in abs.
        by rewrite abs in l_k.
      }
      apply misc.nth_error_lookup in l_k_r.
      rewrite l_k in l_k_r.
      case: l_k_r=><-/=.
      wp_pures.
      wp_apply (acquire_spec with "lock").
      iIntros "% (-> & locked & CanRequest)".
      wp_pures.
      wp_apply ("make_request" with "[$CanRequest HQ]").
      {
        iSplit.
        {
          iPureIntro=>/=.
          exists ($k, $v)%V. left. split=>//=. exists $k, $v. split=>//=.
          split; [apply DB_keys_serializable|apply DB_vals_serializable].
        }
        iLeft.
        iExists E, Q, k, v.
        by do 5 (iSplit; first done).
      }
      iIntros "% %repv (CanRequest & post)".
      wp_pures.
      wp_apply (release_spec with "[$lock $locked $CanRequest]").
      iIntros "% ->".
      wp_pures.
      iApply "HΦ".
      by iApply (request_answer_ser k sa with "post").
    }
    rewrite/client_request_handler_at_server.
    wp_pures.
    wp_apply "shards_data_spec"; [done..|].
    iIntros "(%rpc & %sa & %N & %γ & %MTR & %lk & %l &
                  %l_data & #lock & #make_request & %l_k)".
    wp_pures.
    wp_apply wp_list_nth; first done.
    iIntros "% [(-> & %abs) | (%r & -> & %l_k_r)]".
    {
      apply Nat2Z.inj_le in abs.
      apply lookup_ge_None_2 in abs.
      by rewrite abs in l_k.
    }
    apply misc.nth_error_lookup in l_k_r.
    rewrite l_k in l_k_r.
    case: l_k_r=><-/=.
    wp_pures.
    wp_apply (acquire_spec with "lock").
    iIntros "% (-> & locked & CanRequest)".
    wp_pures.
    wp_apply ("make_request" with "[$CanRequest HQ]").
    {
      iSplit.
      {
        iPureIntro. exists $k. right. split=>//=. apply DB_keys_serializable.
      }
      iRight.
      iExists E, Q, k.
      by do 5 (iSplit; first done).
    }
    iIntros "% %repv (CanRequest & post)".
    wp_pures.
    wp_apply (release_spec with "[$lock $locked $CanRequest]").
    iIntros "% ->".
    wp_pures.
    iApply "HΦ".
    iApply (request_answer_ser k sa with "post").
  Qed.

End proof.