(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting.
From aneris.aneris_lang.lib Require Import map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb Require Import ccddb_code.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import
     model_lst model_gst model_update_system.
From aneris.examples.ccddb.resources Require Import
     base resources_gmem resources_lhst resources_global_inv resources_local_inv.

Import ast.

Section proof.
  Context `{!anerisG Mdl Σ, !DB_params, !internal_DBG Σ}.
  Context (γGauth γGsnap γGkeep : gname) (γLs : list (gname * gname)).

  Definition internal_read_spec
             (rd : val) (i: nat) (z : socket_address) : iProp Σ :=
    □ (∀ (k : Key) (s : gset apply_event),
        ⌜DB_addresses !! i = Some z⌝ -∗
          {{{ local_history_seen γLs i s }}}
          rd #k @[ip_of_address z]
          {{{ vo, RET vo;
              ∃ (s': gset apply_event), ⌜s ⊆ s'⌝ ∗
                local_history_seen γLs i s' ∗
                ((⌜vo = NONEV⌝ ∗ ⌜restrict_key k s' = ∅⌝) ∨
                 (∃ (v: val) (e: apply_event),
                     ⌜vo = SOMEV v⌝ ∗ ⌜e.(ae_val) = v⌝ ∗
                     ⌜e ∈ compute_maximals ae_time (restrict_key k s')⌝ ∗
                     own_mem_snapshot γGsnap k {[erase e]} ∗
                     ⌜e = Observe_lhst (restrict_key k s')⌝))
          }}})%I.

  Lemma internal_read_spec_holds
        (i : nat) (z : socket_address) (DB T IQ OQ : loc) (lk : val)
        (γlk : gname) :
    {{{ Global_Inv γGauth γGsnap γGkeep γLs ∗
        local_invariant γGsnap γLs  i DB T IQ OQ lk γlk z }}}
      store_read #DB lk @[ip_of_address z]
    {{{ rd, RET rd; internal_read_spec rd i z }}}.
  Proof.
    rewrite /store_read /local_invariant.
    remember (ip_of_address z) as ip.
    iIntros (Φ) "(#Ginv & #Linv) HΦ".
    wp_pures. iApply "HΦ". rewrite /internal_read_spec.
    rewrite -Heqip.
    iModIntro.
    iIntros (k s Hiz).
    clear Φ.
    iIntros (Φ) "!# #HS HΦ".
    wp_pures.
    wp_apply acquire_spec; first iExact "Linv".
    iIntros (?) "(-> & Hlk & Hli)".
    simpl.
    wp_pures.
    wp_bind (! _)%E.
    iDestruct "Hli" as (vd vt viq voq d t liq loq s' ip')
    "(Hip' & HDB & HT & HIQ & HOQ &
      #Hdict & #Hvc &Hliv &#Hlstv)".
    iDestruct "Hip'" as %Hip'.
    iDestruct "Hlstv" as %Hlstv.
    iDestruct "Hvc" as %Hvc.
    iDestruct "Hdict" as %Hdict.
    rewrite Hiz in Hip'; simpl in Hip'.
    simplify_eq Hip'; intros <-; rewrite -!Heqip.
    wp_load; simpl.
    wp_bind (map_lookup _ _).
    replace #k with $k; last done.
    iApply wp_map_lookup; first eauto.
    iNext.
    iIntros (w Hw).
    wp_pures.
    iApply fupd_aneris_wp.
    iDestruct (local_history_seen_included with "Hliv HS") as %Hss'.
    iMod (observe_local_history with "Ginv Hliv") as "[Hliv #HS']";
      first done.
    destruct (d !! k) as [p|] eqn:Hpeq.
    - set (e := Observe_lhst (restrict_key k s')).
      pose proof (DBM_LSTV_vals_Some Hlstv k p Hpeq) as [Hp He].
      simpl in Hp, He.
      iInv DB_InvName as
          (M Ss) "(>% & >Hkm & >Ha & >Hs & >Hk1 & >Hk2 & >Hl & >Hvl)".
      iDestruct "Hkm" as %Hkm.
      iDestruct "Hvl" as %Hvl.
      pose proof (elem_of_dom_2 (D := gset Key) _ _ _ Hpeq) as Hk.
      apply (DBM_LSTV_dom_keys Hlstv) in Hk; rewrite Hkm in Hk.
      apply elem_of_dom in Hk as [h Hkh].
      iDestruct (local_history_invs_agree with "Hl Hliv") as %His'.
      assert (e ∈ s' ∧ e.(ae_key) = k) as (Hes' & Hek).
      { apply elem_of_list_to_set,
        elem_of_compute_maximals_as_list1 in He as (He & _).
        by apply elem_of_filter in He as (?&?). }
      assert (erase e ∈ h).
      { pose proof
             (DBM_GstValid_ae_provenance _ i s' e Hvl His' Hes')
          as (h' & Hh' & Heh'); simpl in Hh'.
        rewrite Hek Hkh in Hh'; simplify_eq; done. }
      iMod (get_snapshot with "Hs") as "[Hs Hsnap]"; first done.
      iModIntro.
      iSplitL "Ha Hs Hk1 Hk2 Hl".
      { iNext.
        iExists M, Ss; iFrame; eauto. }
      iModIntro.
      wp_bind (release _).
      iApply (release_spec
                with "[$Hlk HDB HT HOQ HIQ Hliv]").
      { iSplitL "Linv"; first by iFrame "Linv".
        iExists _, _, _, _, _, _, _, _. iExists _,_.
        iSplit; first by rewrite Hiz /= -Heqip.
        iFrame; repeat iSplit; eauto. }
      iNext.
      iIntros (? ->).
      wp_pures.
      iApply "HΦ".
      iDestruct (own_mem_snapshot_weaken _ _ {[erase e]} with "Hsnap")
        as "Hsnap"; first set_solver.
      iExists s'; eauto 10.
    - iModIntro.
      wp_bind (release _).
      iApply (release_spec with "[$Hlk HDB HT HOQ HIQ Hliv]").
      { iFrame "Linv".
        iExists _, _, _, _, _, _, _, _; iFrame; iFrame "#".
        rewrite Hiz /= -Heqip.
        iExists _, _.
        repeat iSplit; eauto with iFrame. }
      iNext; simpl.
      iIntros (? ->).
      assert (restrict_key k s' = ∅).
      { destruct (decide (k ∈ DB_keys)).
        - eapply (DBM_LSTV_vals_None Hlstv); eauto.
        - pose proof (DBM_LSTV_hst_valid Hlstv).
          eapply valid_lhst_restrict_key_out; done. }
      iApply fupd_aneris_wp.
      iInv DB_InvName as
          (M Ss) "(>% & >Hkm & >Ha & >Hs & >Hk1 & >Hk2 & Hl & Hvl)".
      iDestruct "Hkm" as %Hkm.
      iModIntro.
      iSplitR "HΦ".
      { iNext.
        iExists M, Ss; iFrame; eauto. }
      iModIntro.
      wp_pures.
      iApply "HΦ".
      iExists s'; eauto 10.
  Qed.

End proof.
