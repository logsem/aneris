(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import auth gmap excl.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang resources.
From aneris.examples.rcb Require Import rcb_code.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import list_proof map_proof lock_proof network_util_proof.
From aneris.examples.rcb.spec Require Import spec.
From aneris.examples.rcb.model Require Import
     model_lst model_gst model_update_system.
From aneris.examples.rcb.resources Require Import
     base resources_global resources_lhst resources_local_inv resources_global_inv.
From aneris.examples.rcb.proof Require Import proof_of_network proof_of_init.
From aneris.examples.rcb.instantiation Require Import events.


Section proof.
  Context `{!anerisG Mdl Σ, !RCB_params, !RCBG Σ}.

  Local Instance: internal_RCBG Σ :=
    InternalRCBG
      Σ
      (@RCBG_global_history_excl _ _ _)
      (@RCBG_global_history_pers _ _ _)
      (@RCBG_local_history_excl _ _ _)
      (@RCBG_lockG _ _ _).

  Definition rcb_resources γGauth γGsnap γLs : RCB_resources Mdl Σ :=
    {| GlobalInv := Global_Inv γGauth γGsnap γLs;
       OwnGlobal := own_global_user γGauth γGsnap;
       OwnGlobalSnapshot := own_global_snap γGsnap;
       OwnGlobal_Exclusive := own_global_user_excl γGauth γGsnap;
       OwnGlobalSnapshot_union := own_global_snap_union γGsnap;
       OwnGlobalSnapshot_included :=
        own_global_snap_included γGauth γGsnap γLs;
       User_Snapshot := own_global_user_snap γGauth γGsnap;
       Snapshot_ext := own_global_snap_ext γGauth γGsnap γLs;
       OwnLocal := lhst_user γLs;
       OwnLocal_Exclusive := lhst_user_excl γLs;
       init_token := λ i, (lhst_user γLs i ∅ ∗ lhst_lock γLs i ∅)%I;
       OwnLocal_ext := lhst_user_ext γGauth γGsnap γLs;
       OwnLocal_local_ext :=
         lhst_user_strong_ext γGauth γGsnap γLs;
       OwnLocal_provenance :=
         lhst_user_provenance γGauth γGsnap γLs;
       OwnGlobalSnapshot_provenance :=
        global_snap_provenance γGauth γGsnap γLs;
       OwnGlobalSnapshot_origin :=
         own_global_snap_origin γGsnap; 
       Causality := causality γGauth γGsnap γLs;
      RCB_socket_proto := socket_proto γGsnap |}.

  Lemma replicate_init_lhst (l : list socket_address) :
    replicate (length l) ∅ = (λ _ : socket_address, (∅ : (gset le))) <$> l.
  Proof.
    induction l as [ | h t IH]; [done | simpl].
    f_equal; apply IH.
  Qed.

  Lemma length_S_cons {A} (l : list A) n :
    length l = S n -> exists h t, l = h :: t.
  Proof.
    intros Hl.
    destruct l as [ | h t].
    - inversion Hl.
    - eauto.
  Qed.

  Lemma own_lhst_glob_lhst_glob_aux (l : list socket_address) (γLs : list gname) :
     length l = length γLs ->
     ([∗ list] i↦_ ∈ l, lhst_glob γLs i ∅) ⊢
     ([∗ list] γs;S ∈ γLs;replicate (length l) ∅, lhst_glob_aux γs S)%I.
  Proof.
    intros Hlen.
    iInduction l as [| h t IH] "IH" forall (γLs Hlen).
    - simpl.
      iIntros "_".
      assert (γLs = []) as ->.
      { simpl in Hlen.
        destruct γLs; [eauto | inversion Hlen]. }
      iApply big_sepL2_nil; done.
    - iIntros "[Hhead Ht]".
      simpl in *.
      assert (length γLs = S (length t)) as Hl by eauto.
      apply length_S_cons in Hl.
      destruct Hl as [h' [t' Hl]]; subst.
      iApply big_sepL2_cons.
      iSplitL "Hhead".
      { rewrite /lhst_glob.
        iDestruct "Hhead" as (γ) "[%Hlookup ?]".
        assert (γ = h') as ->; [by inversion Hlookup | iFrame]. }
      iApply "IH".
      { eauto with lia. }
      rewrite /lhst_glob.
      iApply (big_sepL_impl with "Ht").
      iModIntro.
      iIntros (k x) "Hsome Hdest".
      iDestruct "Hdest" as (γ) "[%Hlookup ?]".
      iExists γ.
      iFrame. iPureIntro.
      simpl in *; done.
  Qed.

  Lemma own_lhst_user_lock_init_token (l : list socket_address) (γLs : list gname) :
    length l = length γLs ->
    ([∗ list] i↦_ ∈ l, lhst_lock γLs i ∅) ⊢
    ([∗ list] i↦_ ∈ l, lhst_user γLs i ∅) -∗
    ([∗ list] i↦_ ∈ l, (lhst_user γLs i ∅ ∗ lhst_lock γLs i ∅)).
  Proof.
    iInduction l as [| h t] "IH" forall (γLs); iIntros (hl) "Hlock Huser"; [done | simpl].
    iDestruct "Hlock" as "[? Hlock]".
    iDestruct "Huser" as "[? Huser]".
    iFrame.
    simpl in hl.
    symmetry in hl.
    pose proof hl as hl'.
    apply length_S_cons in hl as [h' [γLs' ->]].
    simpl in hl'.
    inversion hl' as [Hlen].
    iPoseProof ("IH" $! γLs' eq_refl with "Hlock Huser") as "Hown".
    iApply (big_sepL_impl with "Hown").
    iModIntro.
    iIntros (k x) "Hsome [Huser Hlock]".
    rewrite /lhst_user /lhst_lock.
    eauto with iFrame.
  Qed.

  Lemma init_setup E :
    True ⊢ |={E}=> ∃ (DBRS : RCB_resources Mdl Σ),
    GlobalInv ∗
    ([∗ list] i ↦ _ ∈ RCB_addresses, init_token i) ∗
    OwnGlobal ∅ ∗
    init_spec
    (rcb_init RCB_serialization.(s_serializer).(s_ser)RCB_serialization.(s_serializer).(s_deser)).
  Proof.
    iIntros (_).
    iMod (alloc_global with "[]") as
        (γGauth γGsnap) "(HGsys & HGuser)"; first done.
    iMod (alloc_lhst with "[]") as (γLs Hlen) "(HLglob & HLlock & HLuser)"; first done.
    iMod (inv_alloc
            RCB_InvName _
            (∃ G Ss,
              ⌜length γLs = length RCB_addresses⌝ ∗
              own_global_sys γGauth γGsnap G ∗
              ([∗ list] γs; S ∈ γLs; Ss, lhst_glob_aux γs S) ∗
              ⌜RCBM_GstValid {| Gst_ghst := G; Gst_hst := Ss|}⌝)%I
            with  "[HGsys HLglob]") as "#Hinv".
    { iModIntro.
      iExists ∅, (replicate (length RCB_addresses) ∅). iFrame.
      iSplitL ""; eauto.
      iSplitL "HLglob".
      - by iApply own_lhst_glob_lhst_glob_aux.
      - iPureIntro.
        assert ({| Gst_ghst := ∅; Gst_hst := replicate (length RCB_addresses) ∅ |} = empty_Gst) as ->.
        { rewrite /empty_Gst /empty_ghst /empty_lhsts.
          rewrite replicate_init_lhst.
          done. }
        apply RCBM_GstValid_empty. }
    iExists (rcb_resources γGauth γGsnap γLs).
    iFrame; iFrame "#".
    iSplitL.
    { iModIntro.
      iApply (own_lhst_user_lock_init_token with "HLlock HLuser"); done. }
    iIntros "!> !#" (i z v Hv Hiz Φ) "!# (Hz & Hrs & Hfp & [Htk1 Htk2]) HΦ".
    iApply (internal_init_spec_holds
              with "[] [] [] [$Hz $Hrs $Hfp $Htk1 $Htk2]");
      [done| done|done|].
    iNext.
    iIntros (del bct) "(Hluser & #Hdel & #Hbct)".
    iApply "HΦ".
    eauto with iFrame.
  Qed.

  Global Instance init_function : RCB_init_function :=
    {|
      init := rcb_init
                RCB_serialization.(s_serializer).(s_ser)
                RCB_serialization.(s_serializer).(s_deser);
      |}.

  Global Program Instance rcb_init : @RCB_init _ _ _  _ init_function :=
    {|
      RCB_init_events := rcb_events;
      RCB_init_setup := init_setup;
    |}.

End proof.
