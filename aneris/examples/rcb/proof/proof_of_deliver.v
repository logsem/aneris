(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.

From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     lang network tactics proofmode lifting.
From aneris.prelude Require Import misc.
From aneris.aneris_lang.lib Require Import list_proof map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.rcb Require Import rcb_code.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import
     model_lst model_gst model_update_system model_update_lst model_update_gst.
From aneris.examples.rcb.resources Require Import
     base resources_global resources_lhst resources_local_inv resources_global_inv.


Section proof.
  Context `{!anerisG Mdl Σ, !RCB_params, !internal_RCBG Σ}.
  Context (γGauth γGsnap : gname) (γLs : list gname).

  Lemma wp_is_causally_next n (vt : val) (t : vector_clock) (i : nat) :
    {{{ ⌜is_vc vt t⌝ ∗ ⌜length t = length RCB_addresses⌝ }}}
      is_causally_next vt #i @[n]
    {{{(f : val), RET f;
       ∀ (w : global_event),
         {{{ True }}}
           f ($ w) @[n]
         {{{(b : bool), RET #b;
            if b then
              ⌜w.(ge_orig) ≠ i ∧
              length w.(ge_time) = length t ∧
              w.(ge_time) !! w.(ge_orig) =
              Some (S (default 0 (t !! w.(ge_orig)))) ∧
              (∀ j, j < length RCB_addresses → j ≠ w.(ge_orig) →
                    default 0 (w.(ge_time) !! j) <= default 0 (t !! j))⌝
            else True
         }}}
    }}}.
  Proof.
    iIntros (Φ) "[Ht Htlen] HΦ".
    iDestruct "Ht" as %Ht.
    iDestruct "Htlen" as %Htlen.
    rewrite /is_causally_next.
    wp_pures.
    wp_apply wp_list_length; first done.
    iIntros (k Hk).
    wp_pures.
    iApply "HΦ".
    clear Φ.
    iIntros (w vw Φ) "!# HΦ".
    wp_pures.
    destruct (decide (i = w.(ge_orig))) as [->|Hioe].
    { rewrite bool_decide_eq_true_2; last lia.
      wp_pures.
      iApply "HΦ"; done. }
    rewrite bool_decide_eq_false_2; last lia.
    wp_pures.
    destruct (decide (w.(ge_orig) < length RCB_addresses)) as [Hlt|]; last first.
    { rewrite bool_decide_eq_false_2; last lia.
      wp_pures.
      iApply "HΦ"; done. }
    rewrite bool_decide_eq_true_2; last lia.
    wp_pures.
    wp_apply (wp_vect_applicable _ _ _ w.(ge_time) t with "[]");
      [by iSplit; iPureIntro; first apply vector_clock_to_val_is_vc|].
    iIntros (b) "Hb".
    iApply ("HΦ" with "[Hb]").
    destruct b; last done.
    iDestruct "Hb" as %(Hb1 & Hb2 & Hb3).
    iPureIntro.
    split_and!; [lia|lia| |].
    - destruct (lookup_lt_is_Some_2 w.(ge_time) w.(ge_orig))
        as [wto Hwto]; first lia.
      destruct (lookup_lt_is_Some_2 t w.(ge_orig))
        as [two Htwo]; first lia.
      rewrite Hwto Htwo in Hb2.
      inversion Hb2 as [? ? ->|]; simplify_eq; simpl.
      rewrite Htwo Hwto /=.
      f_equal; lia.
    - intros j Hj1 Hj2.
      destruct (lookup_lt_is_Some_2 w.(ge_time) j) as [wj Hwj]; first lia.
      destruct (lookup_lt_is_Some_2 t j) as [tj Htj]; first lia.
      rewrite Htj Hwj /=.
      assert (ge_orig w ≠ j) as Hj2' by done.
      specialize (Hb3 j wj tj Hj2' Hwj Htj).
      eauto with lia.
  Qed.

  Definition internal_deliver_spec (deliver_fn : val) (i : nat) (z : socket_address) : iProp Σ :=
         ⌜RCB_addresses !! i = Some z⌝ -∗
         <<< ∀∀ (s : gset local_event), lhst_user γLs i s >>>
           deliver_fn #() @[ip_of_address z] ↑RCB_InvName
           <<<▷ ∃∃ s' vo, RET vo;
                         lhst_user γLs i s' ∗
                         ((⌜s' = s⌝ ∗ ⌜vo = NONEV⌝) ∨
                          (∃ a ,
                           ⌜s' = s ∪ {[ a ]}⌝ ∗
                           ⌜a ∉ s⌝ ∗
                           ⌜a ∈ compute_maximals le_time s'⌝ ∗
                           ⌜not (a.(le_orig) = i)⌝ ∗
                           own_global_snap γGsnap {[ erase a ]} ∗
                           ∃ v, ⌜vo = SOMEV v⌝ ∗ ⌜is_lev v a⌝)) >>>.

  Lemma internal_deliver_spec_holds
        (i : nat) (z : socket_address) (T SeenLoc IQ OQ : loc) (lk : val)
        (γlk : gname) :
    {{{ Global_Inv γGauth γGsnap γLs ∗
        local_invariant γGsnap γLs i T SeenLoc IQ OQ lk γlk z ∗
        ⌜ip_of_address <$> RCB_addresses !! i = Some (ip_of_address z)⌝ }}}
      deliver #T lk #IQ #i @[ip_of_address z]
    {{{ (fv : val), RET fv;
        internal_deliver_spec fv i z
    }}}.
  Proof.
    rewrite /deliver /local_invariant.
    remember (ip_of_address z) as ip.
    iIntros (Φ) "(#Ginv & #Linv & %Hip) HΦ".
    wp_pures.
    iApply "HΦ"; clear Φ.
    iIntros "#Haddr". iIntros "!>" (Φ E HE) "Hvs".
    wp_pures.
    rewrite Heqip.
    wp_apply acquire_spec; first iExact "Linv".
    iIntros (?) "(-> & Hlk & Hli)".
    rewrite /local_inv_def.
    iDestruct "Hli" as (vt vseen viq voq t seenv liq loq s' ip')
     "(%Hip'& HT & %Hvc & Hseen & %Hseen_vc & %Hseen_len & HIQ & HOQ & Hlhst & %Hlstv)".
    assert (ip = ip') as ->.
    { rewrite Hip in Hip'. inversion Hip'; done. }
    clear Hip'.
    subst.
    iDestruct "HIQ" as "(HIQ & %Hviq & Hliq)".
    wp_pures.
    wp_load.
    wp_load.
    wp_apply wp_is_causally_next.
    { iSplit; first done.
      rewrite (RCBM_LSTV_time_length Hlstv); done. }
    iIntros (f) "#Hf /=".
    wp_apply (wp_find_remove); [|done|].
    { iIntros (? ? _) "!> HΦ".
      iApply "Hf"; first done.
      iNext. iIntros (b) "Hb".
      iApply "HΦ".
      destruct b; first iExact "Hb"; done. }
    iIntros (v) "[->|Hv]".
    { wp_pures.
      wp_apply (release_spec with "[$Hlk HT Hseen HOQ HIQ Hliq Hlhst]").
      { eauto 20 with iFrame. }
      iIntros (v ->).
      wp_bind (Rec _ _ _).
      iMod "Hvs".
      wp_pure _.
      iDestruct "Hvs" as (x) "[Hu Hupd]".
      iMod ("Hupd" with "[$Hu]") as "HΦ".
      { iLeft. eauto. }
      iModIntro. wp_pures.
      iApply "HΦ". }
    iDestruct "Hv" as (a lv' l1 l2) "((->&->&%Hlv')&%Honi&%Hwtlen&%Hwtoa&%Hwtnoa)".
    wp_pures.
    wp_store.
    wp_load.
    assert (a.(ge_orig) < length t).
    { apply lookup_lt_Some in Hwtoa; lia. }
    destruct (lookup_lt_is_Some_2 t a.(ge_orig)); first done.
    wp_apply wp_vect_inc; [|done|done|]; first lia.
    iIntros (vt' Hvt'); simpl.
    wp_store.
    iDestruct "Hliq" as "(Hliq1 & (%Hne & #Ha) & Hliq2)".
    iCombine "Hliq1" "Hliq2" as "Hliq".
    rewrite -big_sepL_app.
    set (e := LocalEvent a.(ge_payload)
                         a.(ge_time)
                         a.(ge_orig)
                             (S (length (elements s')))).
    assert (a = erase e) as Herase.
    { destruct a; done. }
    pose proof (RCBM_LSTV_at Hlstv).
    pose proof (RCBM_LSTV_time_length Hlstv) as Htlen;
      rewrite /= /RCBM_lst_time_length in Htlen.
    assert (e ∉ s') as Hes'.
    { apply (RCBM_system_local_event_fresh_lhst e i t); eauto with lia. }
    wp_bind (InjR _).
    do 2 wp_pure _.
    iApply (aneris_wp_atomic _ _ E).
    iMod "Hvs". iModIntro. wp_pures.
    iDestruct "Hvs" as (s) "[Hu Himpl]".
    iDestruct (lhst_user_lock_agree with "Hu Hlhst") as %->.
    iInv RCB_InvName as
        (G Ss) "(>% & >Hgsys & >Hl & >%Hvl)" "Hclos_inv".
    iDestruct (own_global_snap_lookup with "Hgsys Ha") as "%Hina".
    iDestruct (lhst_user_lookup with "Hl Hu") as %His'.
    iDestruct (lhst_lock_lookup with "Hl Hlhst") as %His''.
    assert (e ∈ compute_maximals le_time (s' ∪ {[ e ]})) as Hemax.
    { remember {| Lst_time := t; Lst_hst := s' |} as lst.
      replace s' with lst.(Lst_hst); [ | by rewrite Heqlst ].
      eapply RCBM_Lst_valid_compute_maximals; [done |].
      rewrite /e; simpl.
      replace (Lst_time lst) with t; [eauto | ].
      rewrite Heqlst; done. }
    assert (RCBM_Lst_valid i
                 {| Lst_time := incr_time t (ge_orig a);
                    Lst_hst := s' ∪ {[e]} |}).
    { apply (RCBM_lst_update_apply i {| Lst_time := t; Lst_hst := s' |} (erase e));
        rewrite /e; [done | done |].
      split_and!; simpl; auto with lia. }
    assert (RCBM_Gst_valid {| Gst_ghst := G; Gst_hst := <[i := s' ∪ {[e]} ]>Ss |}).
    { rewrite /e.
      apply (RCBM_system_apply_update_gst
               i {| Gst_ghst := G |} {| Lst_time := t; Lst_hst := s' |} a );
        simpl; eauto with set_solver.
      split_and!; simpl; eauto with lia. }
    iMod (lhst_update _ _ _ _ e with "Hu Hlhst Hl") as "(Hu & Hlhst & Hl)".
    iMod ("Hclos_inv" with "[Hgsys Hl]") as "_".
    { eauto 15 with iFrame. }
    rewrite Herase.
    iMod ("Himpl" with "[$Hu]") as "HΦ".
    { iRight. iExists e.
      iFrame "#".
      repeat iSplit; eauto.
      iExists $(erase e).
      iSplit; eauto.
      iPureIntro.
      simpl.
      eexists _, _, _.
      eauto using vector_clock_to_val_is_vc. }
    iModIntro. wp_pures.
    wp_apply (release_spec with "[$Hlk HT Hseen HOQ HIQ Hliq Hlhst]").
    { iFrame "Linv".
      iExists _, _, _, _, _, _, _, _.
      iExists _, _.
      iSplitL ""; [by iPureIntro |].
      iSplitL "HT"; [iFrame |].
      iSplitL ""; [by iPureIntro|].
      iFrame; iFrame "#".
      repeat iSplit; eauto.
      iPureIntro.
      rewrite Hseen_len.
      symmetry.
      apply incr_time_length. }
    iIntros (? ->).
    wp_seq.
    iApply "HΦ".
  Qed.

End proof.
