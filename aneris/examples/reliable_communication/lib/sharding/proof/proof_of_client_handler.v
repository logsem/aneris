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

Section proof.

  Context `{!anerisG Mdl Σ, !DBG Σ, !DB_params}.

  Lemma request_answer_ser k sa res (reqd : ReqData) :
    (user_params_at_shard (DBG_shards k) sa).(MTS_handler_post) res reqd I -∗
      ⌜Serializable rep_ser res⌝ ∗
      user_params_at_server.(MTS_handler_post) res reqd I.
  Proof.
    iIntros "[(%E & %P & %Q & %k' & %v' & Q & -> & ->)|
              (%E & %P & %Q & %k' & -> & [(%v' & -> & Q)|(-> & Q)])]".
    { iSplit. { iPureIntro=>/=. exists #(). by left. }
      iLeft. iExists E, P, Q, k', v'. iFrame. by iSplit. }
    { iSplit.
      { iPureIntro=>/=. exists (InjRV v'). right. split=>//=.
        left. exists v'. split=>//=. apply SV_ser. }
      iRight. iExists E, P, Q, k'. iSplit; first done. iLeft.
        iExists v'. by iFrame. }
    iSplit. { iPureIntro=>/=. exists (InjLV #()). right. split=>//=. by right. }
    iRight. iExists E, P, Q, k'. iSplit; first done. iRight. by iFrame.
  Qed.

  Definition shards_data_spec (shardsv : val) shards data : iProp Σ :=
    ∀ k, ⌜k ∈ DB_keys⌝ -∗
    {{{ True }}}
      shardsv #k @[ip_of_address DB_addr]
    {{{ RET #(shards k); ⌜shards k < length DB_addrs⌝ ∗
      ∃ rpc sa N γ MTR lk (l : list (val*val)), ⌜is_list l data⌝ ∗
      is_lock N (ip_of_address DB_addr) γ lk
          (MTR.(MTSCanRequest) (ip_of_address DB_addr) rpc) ∗
    (@make_request_spec _ _ _ _ (user_params_at_shard (DBG_shards k) sa) MTR) ∗
    ⌜l !! (shards k) = Some (rpc, lk)⌝ }}}.

  Lemma client_request_handler_at_server_spec :
    ∀ data shardsv shards reqv reqd,
    {{{
      user_params_at_server.(MTS_handler_pre) reqv reqd ∗
      shards_data_spec shardsv shards data
    }}}
      client_request_handler_at_server data shardsv reqv @[ip_of_address DB_addr]
    {{{ res, RET res;
      ⌜Serializable rep_ser res⌝ ∗
      user_params_at_server.(MTS_handler_post) res reqd I
    }}}.
  Proof.
    iIntros (data shardsv shards reqv reqd Φ)
          "([(%E & %P & %Q & %k & %v & % & % & -> & -> & P & #HQ)|
        (%E & %P & %Q & %k & % & % & -> & -> & P & #HQ)] & #shards_data_spec) HΦ".
    {
      rewrite/client_request_handler_at_server.
      wp_pures.
      wp_apply "shards_data_spec"; [done..|].
      iIntros "(%shards_k_valid & %rpc & %sa & %N & %γ & %MTR & %lk & %l &
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
      wp_apply ("make_request" with "[$CanRequest P]").
      {
        iSplit.
        {
          iPureIntro=>/=.
          exists (#k, v)%V. left. split=>//=. exists #k, v. split=>//=.
          split; [by exists k|apply v.(SV_ser)].
        }
        iLeft.
        iExists E, P, Q, k, v.
        by do 6 (iSplit; first done).
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
    iIntros "(%shards_k_valid & %rpc & %sa & %N & %γ & %MTR & %lk & %l &
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
    wp_apply ("make_request" with "[$CanRequest P]").
    {
      iSplit.
      {
        iPureIntro. exists #k. right. split=>//=. by exists k.
      }
      iRight.
      iExists E, P, Q, k.
      by do 6 (iSplit; first done).
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