(** Proof the causal memory implementation w.r.t. modular specification. *)
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.
From aneris.prelude Require Import misc time.
From aneris.aneris_lang Require Import lang tactics proofmode lifting.
From aneris.aneris_lang.lib Require Import list_proof map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb Require Import ccddb_code.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import
     model_lst model_gst model_update_system.
From aneris.examples.ccddb.resources Require Import
     base resources_gmem resources_lhst resources_local_inv resources_global_inv.
From aneris.examples.ccddb.proof Require Import
     proof_of_read proof_of_write proof_of_apply proof_of_network.
From aneris.aneris_lang Require Import network.

Import ast.

Section proof.
  Context `{!anerisG Mdl Σ, !DB_params, !internal_DBG Σ}.
  Context (γGauth γGsnap γGkeep : gname) (γLs : list (gname * gname)).

  Lemma internal_init_spec_holds :
    Global_Inv γGauth γGsnap γGkeep γLs ⊢
    □ ∀ (i: nat) (z : socket_address) (v : val),
      ⌜is_list DB_addresses v⌝ →
      ⌜DB_addresses !! i = Some z⌝ →
      {{{ ([∗ list] i ↦ z ∈ DB_addresses, z ⤇ socket_proto γGsnap) ∗
          z ⤳ (∅, ∅) ∗
          free_ports (ip_of_address z) {[port_of_address z]} ∗
          local_history_Local_inv γLs i ∅ }}}
        ccddb_init
        DB_serialization.(s_serializer).(s_ser) DB_serialization.(s_serializer).(s_deser) v #i
        @[ip_of_address z]
      {{{ rd wr, RET (rd, wr);
          local_history_seen γLs i ∅ ∗
          internal_read_spec γGsnap γLs rd i z ∗
          internal_write_spec γGauth γGsnap γGkeep γLs wr i z}}}.
  Proof.
    iIntros "#Hinv !#" (i z v Hv Hiz Φ)
            "!# (#Hz & Hrs & Hfp & Hliv) HΦ".
    remember (ip_of_address z) as ip.
    rewrite /ccddb_init.
    wp_pures.
    wp_apply wp_map_empty; first done.
    iIntros (db Hdb); simpl.
    wp_alloc ℓDB as "HDB".
    wp_pures.
    wp_apply wp_list_length; first done.
    iIntros (? ->).
    wp_pures.
    replace #0 with #0%nat; last done.
    wp_apply wp_vect_make; first done.
    iIntros (t Ht).
    wp_alloc ℓT as "HT".
    do 2 wp_pure _.
    wp_apply wp_list_nil; first done.
    iIntros (iq Hiq).
    wp_alloc ℓIQ as "HIQ".
    do 2 wp_pure _.
    wp_apply wp_list_nil; first done.
    iIntros (oq Hoq).
    wp_alloc ℓOQ as "HOQ".
    wp_pures.
    iApply fupd_aneris_wp.
    iMod (observe_local_history with "Hinv Hliv") as "[Hliv #Hseen]";
      first done.
    iModIntro.
    wp_apply (newlock_spec _ (local_inv_def γGsnap γLs i ℓDB ℓT ℓIQ ℓOQ)
                with "[Hliv HDB HT HIQ HOQ]").
    {iExists _, _, _, _, ∅, _, [], []. iExists ∅, _; simpl; iFrame.
      repeat iSplit; [|done|done|done|done|done|done|]; iPureIntro.
      - by rewrite Hiz /= Heqip.
      - replace (replicate (length DB_addresses) 0%nat) with initial_time.
        + apply DBM_Lst_valid_empty; apply lookup_lt_is_Some_1; eauto.
        + symmetry; apply replicate_as_elem_of.
          rewrite /initial_time fmap_length.
          set_solver. }
    iIntros (lk γlk) "#Hlk".
    wp_pures.
    wp_socket h as "Hh".
    wp_pures.
    wp_apply wp_list_nth_some.
    { iPureIntro; split; eauto with lia.
      assert ( is_Some (DB_addresses !! i)) as Hsm by eauto.
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
    rewrite -Heqip.
    wp_apply aneris_wp_fork.
    iSplitL; last first.
    { iNext.
      rewrite Heqip.
      wp_apply apply_spec_holds; last done.
      rewrite Hiz.
      repeat iSplit; done. }
    iNext.
    wp_pures.
    iApply fupd_aneris_wp.
    iAssert (|={⊤}=> socket_inv γGsnap z h _)%I with "[Hh Hrs]" as ">#Hsocketinv".
    { rewrite Heqip.
      iApply inv_alloc. iNext. iExists _, _; iFrame.
      rewrite big_sepS_empty; done. }
    iModIntro.
    wp_apply aneris_wp_fork.
    iSplitL; last first.
    { iNext.
      rewrite Heqip.
      wp_apply send_thread_spec; last done.
      iDestruct (big_sepL_lookup _ _ _ _ Hiz with "Hz") as "Hz'".
      iFrame "#"; done. }
    iNext.
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL; last first.
    { iNext.
      rewrite Heqip.
      wp_apply (recv_thread_spec _ _ _ _ i _ _ _ _ _ _ z); last done.
      rewrite Hiz /=.
      iDestruct (big_sepL_lookup _ _ _ _ Hiz with "Hz") as "Hz'".
      iFrame "#"; done. }
    iNext.
    wp_pures.
    rewrite Heqip.
    wp_apply internal_write_spec_holds; first by iFrame "#".
    iIntros (wr) "Hwr"; simpl.
    wp_apply internal_read_spec_holds; first by iFrame "#".
    iIntros (rd) "Hrd"; simpl.
    wp_pures.
    iApply "HΦ".
    iFrame; done.
  Qed.

End proof.
