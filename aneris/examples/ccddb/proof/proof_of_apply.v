(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.

From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     lang network tactics proofmode lifting.
From aneris.prelude Require Import misc.
From aneris.aneris_lang.lib Require Import list_proof map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb Require Import ccddb_code.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import
     model_lst model_gst model_update_system model_update_lst model_update_gst.
From aneris.examples.ccddb.resources Require Import
     base resources_gmem resources_lhst resources_local_inv resources_global_inv.


Section proof.
  Context `{!anerisG Mdl Σ, !DB_params, !internal_DBG Σ}.
  Context (γGauth γGsnap γGkeep : gname) (γLs : list (gname * gname)).


Lemma store_test_wp n (vt : val) (t : vector_clock) (i : nat) :
    {{{ ⌜is_vc vt t⌝ ∗ ⌜length t = length DB_addresses⌝ }}}
      store_test vt #i @[n]
    {{{(f : val), RET f;
       ∀ (w : write_event),
         {{{ True }}}
           f ($ w) @[n]
         {{{(b : bool), RET #b;
            if b then
              ⌜w.(we_orig) ≠ i ∧
              length w.(we_time) = length t ∧
              w.(we_time) !! w.(we_orig) =
              Some (S (default 0 (t !! w.(we_orig)))) ∧
              (∀ j, j < length DB_addresses → j ≠ w.(we_orig) →
                    default 0 (w.(we_time) !! j) <= default 0 (t !! j))⌝
            else True
         }}}
    }}}.
  Proof.
    iIntros (Φ) "[Ht Htlen] HΦ".
    iDestruct "Ht" as %Ht.
    iDestruct "Htlen" as %Htlen.
    rewrite /store_test.
    wp_pures.
    wp_apply wp_list_length; first done.
    iIntros (k Hk).
    wp_pures.
    iApply "HΦ".
    clear Φ.
    iIntros (w vw Φ) "!# HΦ".
    wp_pures.
    destruct (decide (i = w.(we_orig))) as [->|Hioe].
    { rewrite bool_decide_eq_true_2; last lia.
      wp_pures.
      iApply "HΦ"; done. }
    rewrite bool_decide_eq_false_2; last lia.
    wp_pures.
    destruct (decide (w.(we_orig) < length DB_addresses)) as [Hlt|]; last first.
    { rewrite bool_decide_eq_false_2; last lia.
      wp_pures.
      iApply "HΦ"; done. }
    rewrite bool_decide_eq_true_2; last lia.
    wp_pures.
    wp_apply (wp_vect_applicable _ _ _ w.(we_time) t with "[]");
      [by iSplit; iPureIntro; first apply vector_clock_to_val_is_vc|].
    iIntros (b) "Hb".
    iApply ("HΦ" with "[Hb]").
    destruct b; last done.
    iDestruct "Hb" as %(Hb1 & Hb2 & Hb3).
    iPureIntro.
    split_and!; [lia|lia| |].
    - destruct (lookup_lt_is_Some_2 w.(we_time) w.(we_orig))
        as [wto Hwto]; first lia.
      destruct (lookup_lt_is_Some_2 t w.(we_orig))
        as [two Htwo]; first lia.
      rewrite Hwto Htwo in Hb2.
      inversion Hb2 as [? ? ->|]; simplify_eq; simpl.
      rewrite Htwo Hwto /=.
      f_equal; lia.
    - intros j Hj1 Hj2.
      destruct (lookup_lt_is_Some_2 w.(we_time) j) as [wj Hwj]; first lia.
      destruct (lookup_lt_is_Some_2 t j) as [tj Htj]; first lia.
      rewrite Htj Hwj /=.
      assert (we_orig w ≠ j) as Hj2' by done.
      specialize (Hb3 j wj tj Hj2' Hwj Htj).
      eauto with lia.
  Qed.

  Lemma apply_spec_holds
        (i : nat) (z : socket_address) (DB T IQ OQ : loc) (lk : val)
        (γlk : gname) :
    {{{ Global_Inv γGauth γGsnap γGkeep γLs ∗
        local_invariant γGsnap γLs i DB T IQ OQ lk γlk z ∗
        ⌜ip_of_address <$> DB_addresses !! i = Some (ip_of_address z)⌝}}}
      store_apply #DB #T lk #IQ #i @[ip_of_address z]
    {{{ RET #(); False }}}.
  Proof.
    rewrite /store_apply /local_invariant.
    remember (ip_of_address z) as ip.
    iIntros (Φ) "(#Ginv & #Linv & Hip) _".
    iDestruct "Hip" as %Hip.
    wp_lam.
    do 4 wp_let. wp_pure _.
    wp_closure.
    wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_apply acquire_spec; first iExact "Linv".
    iIntros (?) "(-> & Hlk & Hli)".
   iDestruct "Hli" as (vd vt viq voq d t liq loq s' ip')
     "(Hip'& HDB & HT & HIQ & HOQ & #Hdict & #Hvc &Hliv &#Hlstv)".
   rewrite /= Hip /=.
    iDestruct "Hip'" as %Hip'.
    simplify_eq Hip'; intros <-; clear Hip'.
    iDestruct "Hlstv" as %Hlstv.
    iDestruct "Hvc" as %Hvc.
    iDestruct "Hdict" as %Hdict.
    iDestruct "HIQ" as "(HIQ & Hviq & Hliq)".
    iDestruct "Hviq" as %Hviq.
    wp_pures.
    wp_load.
    wp_load.
    wp_apply store_test_wp.
    { iSplit; first done.
      rewrite (DBM_LSTV_time_length Hlstv); done. }
    iIntros (f) "#Hf /=".
    wp_apply (wp_find_remove); [|done|].
    { iIntros (? ? ?) "!# HΦ".
      iApply "Hf"; first done.
      iNext. iIntros (b) "Hb".
      iApply "HΦ".
      destruct b; first iExact "Hb"; done. }
    iIntros (v) "[->|Hv]".
    { wp_pures.
      wp_apply (release_spec with "[$Hlk HDB HT HOQ HIQ Hliq Hliv]").
      { iFrame "Linv".
        iExists _, _, _, _, _, _, _, _. iExists _, _.
        iFrame; iFrame "#".
        repeat iSplit; eauto; done. }
      iIntros (v ->).
      wp_seq.
      iApply "IH". }
    iDestruct "Hv" as (a lv' l1 l2) "((->&->&Hlv')&Honi&Hwtlen&Hwtoa&Hwtnoa)".
    iDestruct "Hlv'" as %Hlv'.
    iDestruct "Honi" as %Honi.
    iDestruct "Hwtlen" as %Hwtlen.
    iDestruct "Hwtoa" as %Hwtoa.
    iDestruct "Hwtnoa" as %Hwtnoa.
    wp_pures.
    wp_store.
    wp_pures.
    rewrite {3}/store_update.
    wp_pures.
    wp_load.
    assert (a.(we_orig) < length t).
    { apply lookup_lt_Some in Hwtoa; lia. }
    destruct (lookup_lt_is_Some_2 t a.(we_orig)); first done.
    wp_apply wp_vect_inc; [|done|done|]; first lia.
    iIntros (vt' Hvt'); simpl.
    wp_store.
    wp_pures.
    wp_load.
    replace #(we_key a) with $(we_key a); [ | done].
    replace (we_val a) with $(we_val a); [ | done].
    wp_apply wp_map_insert; first done.
    iIntros (d' Hd'); simpl.
    wp_store.
    (* wp_seq. *)
    rewrite big_sepL_app big_sepL_cons.
    iDestruct "Hliq" as "(Hliq1 & Ha & Hliq2)".
    iCombine "Hliq1" "Hliq2" as "Hliq".
    rewrite -big_sepL_app.
    set (e := ApplyEvent a.(we_key) a.(we_val)
                  a.(we_time) a.(we_orig) (S (length (elements s')))).
    pose proof (DBM_LSTV_at Hlstv).
    pose proof (DBM_LSTV_time_length Hlstv) as Htlen;
      rewrite /= /DBM_lst_time_length in Htlen.
    assert (e ∉ s') as Hes'.
    { apply (DBM_system_apply_event_fresh_lhst e i d t); eauto with lia. }
    iApply fupd_aneris_wp.
    iInv DB_InvName as
        (M Ss) "(>% & >Hkm & >Hauth & >Hs & >Hk1 & >Hk2 & >Hl & >Hvl)".
    iDestruct "Hkm" as %Hkm.
    iDestruct "Hvl" as %Hvl.
    iDestruct (snapshot_lookup with "Hs Ha") as %(h & Hh1 & Hh2).
    iDestruct (local_history_invs_agree with "Hl Hliv") as %His'.
    assert (we_key a ∈ DB_keys).
    { rewrite Hkm; apply elem_of_dom; eauto. }
    assert (DBM_Lst_valid i
                 {| Lst_mem := <[we_key a:=we_val a]> d;
                    Lst_time := incr_time t (we_orig a);
                    Lst_hst := s' ∪ {[e]} |}).
    { rewrite /e.
      apply (DBM_lst_update_apply i {| Lst_mem := d |}); eauto.
      split_and!; simpl; auto with lia. }
    assert (DBM_Gst_valid {| Gst_mem := M; Gst_hst := <[i := s' ∪ {[e]} ]>Ss |}).
    { rewrite /e.
      eapply (DBM_system_apply_update_gst
                i {| Gst_mem := M |} {| Lst_mem := d |} a);
        simpl; eauto with set_solver.
      split_and!; simpl; auto with lia. }
     iMod (local_history_update _ _ _ _ e with "Hliv Hl") as "[Hl Hliv]".
    { intros e' He' Hlt.
      apply vector_clock_lt_le in Hlt.
      eapply (Forall2_lookup_l _ _ _ a.(we_orig)) in Hlt
        as (e'oa & He'oa & Hle); last done.
      pose proof (DBM_Lst_valid_time_le _ _ e' Hlstv He') as Hle'; simpl in *.
      eapply (Forall2_lookup_l _ _ _ a.(we_orig)) in Hle'
        as (toe & Htoe1 & Htoe2); last done.
      rewrite Htoe1 /= in Hle; lia. }
    iModIntro.
    iSplitL "Hauth Hs Hk1 Hk2 Hl".
    { iNext. iExists _, _; iFrame.
      repeat iSplit; try done. }
    iModIntro.
    wp_apply (release_spec with "[$Hlk HDB HT HOQ HIQ Hliq Hliv]").
    { iFrame "Linv".
      iExists _, _, _, _, _, _, _, _; iExists _, _.
      iFrame; iFrame "#".
      repeat iSplit; eauto. }
    iIntros (? ->).
    wp_seq.
    iApply "IH".
  Qed.

End proof.
