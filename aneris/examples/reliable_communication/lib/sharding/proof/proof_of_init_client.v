From aneris.examples.reliable_communication.lib.sharding Require Import sharding_code.
From aneris.examples.reliable_communication.lib.sharding.spec
    Require Import resources api_spec.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.reliable_communication.lib.mt_server Require Import
                    mt_server_code user_params.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.mt_server.proof Require Import
                    mt_server_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
Import sharding_code.
Import inject.

Section proof.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ, !MTS_resources}.

  Lemma init_client_spec_holds srv_si:
    ∀ sa,
    {{{
      unallocated {[sa]} ∗
      sa ⤳ (∅, ∅) ∗
      DB_addr ⤇ srv_si ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      (@make_request_spec _ _ _ _ user_params_at_server _) ∗
      (@init_client_proxy_spec _ _ _ _ user_params_at_server _ srv_si)
    }}}
      init_client (s_serializer DB_key_ser) (s_serializer DB_val_ser)
          #sa #DB_addr @[ip_of_address sa]
    {{{ wr rd, RET (wr, rd); read_spec rd sa ∗ write_spec wr sa }}}.
  Proof.
    iIntros (sa Φ) "(unalloc & ∅ & #srv_si & free & #request_srv & #init_srv_clt)
                        HΦ".
    rewrite/init_client.
    wp_pures.
    wp_apply ("init_srv_clt" with "[$unalloc $∅ $srv_si $free]").
    iIntros (rpc) "CanRequest".
    wp_pures.
    wp_apply (newlock_spec DB_inv_name with "CanRequest").
    iIntros (lk lock) "#lock".
    wp_pures.
    iApply "HΦ".
    iSplit.
    {
      iIntros (E k inv_name k_keys Ψ) "!>HΨ".
      wp_pures.
      wp_apply (acquire_spec with "lock").
      iIntros "% (-> & locked & CanRequest)".
      wp_pures.
      wp_apply ("request_srv" $! _ _ _ (inr (E, (λ vo, Ψ $vo)%I, k))
          with "[$CanRequest HΨ]").
      {
        iSplit.
        { iPureIntro=>/=. exists $k. right. split=>//=.
            apply DB_keys_serializable. }
        iRight.
        iExists E, _, k.
        iFrame.
        by do 3 (iSplit; first done).
      }
      iIntros (repd repv) "(CanRequest & [(% & % & % & % & _ & _ & %)|
          (% & % & % & %eq & % & -> & HΨ)])"; first done.
      move: eq=>[_ <- _].
      wp_pures.
      wp_apply (release_spec with "[$lock $locked $CanRequest]").
      iIntros (? ->).
      wp_pures.
      iApply "HΨ".
    }
    iIntros (E k v inv_name k_keys Ψ) "!>HΨ".
    wp_pures.
    wp_apply (acquire_spec with "lock").
    iIntros "% (-> & locked & CanRequest)".
    wp_pures.
    wp_apply ("request_srv" $! _ _ _ (inl (E, Ψ #(), k, v))
            with "[$CanRequest HΨ]").
    {
      iSplitR.
      { iPureIntro=>/=. exists ($k, $v)%V. left. split=>//=. exists $k, $v.
        split=>//=. split;
          [apply DB_keys_serializable|apply DB_vals_serializable]. }
      iLeft.
      iExists E, (Ψ #()), k, v.
      iFrame.
      by do 3 (iSplit; first done).
    }
    iIntros (repd repv) "(CanRequest & [(% & % & % & % & HΨ & -> & %eq)|
        (% & % & % & % & _)])"; last done.
    move: eq => [_ <- _ _].
    wp_pures.
    wp_apply (release_spec with "[$lock $locked $CanRequest]").
    iIntros (? ->).
    wp_pures.
    iApply "HΨ".
  Qed.

End proof.