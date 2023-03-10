(** Proof the causal memory implementation w.r.t. modular specification. *)
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.
From aneris.prelude Require Import misc time.
From aneris.aneris_lang Require Import lang tactics proofmode lifting.
From aneris.aneris_lang.lib Require Import list_proof queue_proof map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.rcb Require Import rcb_code.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import
     model_lst model_gst model_update_system.
From aneris.examples.rcb.resources Require Import
     base resources_global resources_lhst resources_local_inv resources_global_inv.
From aneris.examples.rcb.util Require Import list_proof_alt.
From aneris.examples.rcb.proof Require Import
     proof_of_deliver proof_of_broadcast proof_of_network.
From aneris.aneris_lang Require Import network.

Import ast.

Section proof.
  Context `{!anerisG Mdl Σ, !RCB_params, !internal_RCBG Σ}.
  Context (γGauth γGsnap : gname) (γLs : list gname).


  Lemma single_queue_inv_replicate_nil n (lq : val) :
    emp ⊢ [∗ list] i ↦ lq ∈ replicate n [], single_queue_inv γGsnap i lq.
  Proof.
    iInduction n as [ | n'] "IH".
    - simpl; done.
    - simpl.
      iIntros "Hemp".
      iDestruct ("IH" with "Hemp") as "#IH'".
      iSplit.
      + rewrite /single_queue_inv; done.
      + iApply (big_sepL_impl).
        { iFrame "IH'". }
        iModIntro.
        iIntros (k l) "%Hlook #Hinv".
        assert (l = []) as ->.
        { apply lookup_replicate_1 in Hlook as [-> _].
          reflexivity. }
        done.
  Qed.

  Lemma internal_init_spec_holds :
    Global_Inv γGauth γGsnap γLs ⊢
    □ ∀ (i: nat) (z : socket_address) (v : val),
      ⌜is_list RCB_addresses v⌝ →
      ⌜RCB_addresses !! i = Some z⌝ →
      {{{ ([∗ list] i ↦ z ∈ RCB_addresses, z ⤇ socket_proto γGsnap i) ∗
          z ⤳ (∅, ∅) ∗
          unbound (ip_of_address z) {[port_of_address z]} ∗
          lhst_lock γLs i ∅ ∗
          lhst_user γLs i ∅
      }}}
       rcb_init RCB_serialization.(s_serializer).(s_ser) RCB_serialization.(s_serializer).(s_deser) v #i
        @[ip_of_address z]
      {{{ del bct, RET (del, bct);
          lhst_user γLs i ∅ ∗
          internal_deliver_spec γGsnap γLs del i z ∗
          internal_broadcast_spec γGauth γGsnap γLs bct i z}}}.
  Proof.
    iIntros "#Hinv !#" (i z v Hv Hiz Φ)
            "!# (#Hz & Hrs & Hfp & Hliv & Hluser) HΦ".
    remember (ip_of_address z) as ip.
    rewrite /rcb_init.
    wp_pures.
    wp_apply wp_list_length; [done |].
    iIntros (n) "->".
    wp_pures.
    replace (Val #0) with ($ 0 : expr); last first; [done | ].
    wp_apply (wp_vect_make ip (length RCB_addresses) 0); [done |].
    iIntros (vc_vect) "%Hisvc".
    wp_alloc ℓT as "HT".
    do 2 wp_pure _.
    replace (Val #0) with ($ 0 : expr); last first; [done | ].
    wp_apply (wp_vect_make ip (length RCB_addresses) 0); [done |].
    iIntros (seenv) "%Hisvc_seen".
    wp_alloc ℓSeen as "Hseen".
    do 2 wp_pure _.
    wp_bind (InjL _).
    wp_apply (wp_list_nil global_event); first done.
    iIntros (iq Hiq).
    wp_alloc ℓIQ as "HIQ".
    do 2 wp_pure _.
    wp_bind (queue_empty _).
    wp_apply (@wp_queue_empty _ _ _ global_event); [done | ].
    iIntros (qv) "%Hiq_qv".
    wp_apply (wp_list_makeP _ _ ([] : list global_event) qv is_queue); [eauto |].
    iIntros (oq) "%Hil_oq".
    wp_alloc ℓOQs as "HOQ".
    wp_pures.
    wp_apply (newlock_spec
                (nroot.@"lk") _ (local_inv_def γGsnap γLs i ℓT ℓSeen ℓIQ ℓOQs)
                with "[Hliv Hseen HT HIQ HOQ]").
    { rewrite /local_inv_def.
      iExists _, _, _, oq, _, _, [], (replicate (length RCB_addresses) ([] : list global_event)).
      iExists ∅, _; simpl; iFrame.
      repeat iSplit; eauto.
      - by rewrite Hiz /=  Heqip.
      - by (iPureIntro; rewrite replicate_length).
      - iApply single_queue_inv_replicate_nil; done.
      - iPureIntro.
        replace (replicate (length RCB_addresses) 0%nat) with initial_time.
        { eapply RCBM_Lst_valid_empty.
          eapply lookup_lt_Some; eauto. }
        rewrite /initial_time.
        eapply const_fmap; eauto. }
    iIntros (lk γ) "#Hilock".
    wp_pures.
    wp_socket h as "Hh".
    wp_pures.
    wp_apply wp_list_nth_some.
    { iPureIntro; split; eauto with lia.
      assert ( is_Some (RCB_addresses !! i)) as Hsm by eauto.
      simpl. specialize ( lookup_lt_is_Some_1 _ _ Hsm). lia. }
    iIntros (ithSome ( ith & -> & Hh)). simpl.
    wp_apply wp_unSOME; eauto; iIntros (_).
    wp_let.
    assert (ith = z) as ->.
    { pose proof nth_error_lookup _ _ _ Hh as Ha.
      rewrite Hiz in Ha.
      by inversion Ha. }
    rewrite Heqip.
    wp_socketbind.
    iApply fupd_aneris_wp.
    iAssert (|={⊤}=> socket_inv γGsnap z h _ i)%I with "[Hh Hrs]" as ">#Hsocketinv".
    { rewrite Heqip.
      iApply inv_alloc. iNext. iExists _, _; iFrame.
      rewrite big_sepS_empty; done. }
    iModIntro.
    wp_apply aneris_wp_fork.
    iSplitL; last first.
    { iNext.
      wp_apply send_thread_spec; last done.
      iDestruct (big_sepL_lookup _ _ _ _ Hiz with "Hz") as "Hz'".
      iFrame "#"; done. }
    iNext.
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL; last first.
    { iNext.
      wp_apply (recv_thread_spec _ _ _ _ _ i _ _ _ _ _ _ _ z); last done.
      rewrite Hiz /=.
      iDestruct (big_sepL_lookup _ _ _ _ Hiz with "Hz") as "Hz'".
      iFrame "#"; done. }
    iModIntro.
    wp_pures.
    wp_apply internal_broadcast_spec_holds; first by iFrame "#".
    iIntros (br) "Hbr"; simpl.
    wp_apply internal_deliver_spec_holds.
    { repeat iSplit; eauto with iFrame.
      rewrite Hiz; simpl; done. }
    iIntros (rd) "Hdl"; simpl.
    wp_pures.
    iApply "HΦ".
    iFrame; done.
  Qed.

End proof.
