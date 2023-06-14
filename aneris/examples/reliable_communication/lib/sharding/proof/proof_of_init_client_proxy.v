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

Section proof.

  Context `{!anerisG Mdl Σ, !DBG Σ, !DB_params, !MTS_resources}.

  Lemma init_client_proxy_spec_holds srv_si:
    ∀ sa,
    {{{
      unallocated {[sa]} ∗
      sa ⤳ (∅, ∅) ∗
      DB_addr ⤇ srv_si ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      (@make_request_spec _ _ _ _ user_params_at_server _) ∗
      (@init_client_proxy_spec _ _ _ _ user_params_at_server _ srv_si)
    }}}
      init_client_proxy (s_serializer DB_serialization) #sa #DB_addr
          @[ip_of_address sa]
    {{{ wr rd, RET (wr, rd); read_spec rd sa ∗ write_spec wr sa }}}.
  Proof.
    iIntros (sa Φ) "(unalloc & ∅ & #srv_si & free & #request_srv & #init_srv_clt)
                        HΦ".
    rewrite/init_client_proxy.
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
      iIntros (E k P Q) "!>%inv_name %k_keys !>%Ψ (P & #HQ) HΨ".
      wp_pures.
      wp_apply (acquire_spec with "lock").
      iIntros "% (-> & locked & CanRequest)".
      wp_pures.
      wp_apply ("request_srv" $! _ _ _ (inr (E, P, Q, k)) with "[$CanRequest P]").
      {
        iSplitR.
        { iPureIntro=>/=. exists #k. right. split=>//=. by exists k. }
        iRight.
        iExists E, P, Q, k.
        iFrame.
        do 4 (iSplit; first done).
        by iModIntro.
      }
      by iIntros (repd repv) "(CanRequest & [(% & % & % & % & % & _ & % & %)|
                        (% & % & % & % & %eq & [(%v & -> & Q)|
                      (-> & Q)])])";
        [done|move:eq=>[_ _ <-_]..] ; wp_pures; 
      wp_apply (release_spec with "[$lock $locked $CanRequest]");
      iIntros (? ->); wp_pures; iApply "HΨ"; [iLeft; iExists v|iRight]; iSplit.
    }
    iIntros (E k v P Q inv_name k_keys Ψ) "!>!>(P & #HQ) HΨ".
    wp_pures.
    wp_apply (acquire_spec with "lock").
    iIntros "% (-> & locked & CanRequest)".
    wp_pures.
    wp_apply ("request_srv" $! _ _ _ (inl (E, P, Q, k, v)) with "[$CanRequest P]").
    {
      iSplitR.
      { iPureIntro=>/=. exists (#k, v)%V. left. split=>//=. exists #k, v.
        split=>//=. split; by [exists k|apply SV_ser]. }
      iLeft.
      iExists E, P, Q, k, v.
      iFrame.
      do 4 (iSplit; first done).
      by iModIntro.
    }
    iIntros (repd repv) "(CanRequest & [(% & % & % & % & % & Q & -> & %eq)|
                    (% & % & % & % & % & _)])"; [move:eq=>[_ _ <- _ _]|done].
    wp_pures.
    wp_apply (release_spec with "[$lock $locked $CanRequest]").
    iIntros (? ->).
    wp_pures.
    by iApply "HΨ".
  Qed.

End proof.