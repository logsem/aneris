From aneris.aneris_lang Require Import resources proofmode.
From iris.algebra Require Import auth csum excl agree.
From aneris.algebra Require Import monotone.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_resources.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.STS Require Import lst gst utils.
From iris.base_logic.lib Require Import invariants.

From aneris.examples.crdt.statelib.resources
  Require Import utils resources_inv resources_local resources_global.



Section AboutInv.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.
  Notation princ_ev := (@principal (gset (Event CRDT_Op)) cc_subseteq).

  Lemma StLib_OwnLocalSnap_GlobSnap_Provenance E i s1 s2 e :
    ↑CRDT_InvName ⊆ E →
    e ∈ s1 ∪ s2 →
    StLib_GlobalInv ⊢
    StLib_OwnLocalSnap i s1 s2 ={E}=∗ ∃ h, StLib_OwnGlobalSnap h ∗ ⌜e ∈ h⌝.
  Proof.
    iIntros (Hincl He_in) "#Hinv (%f & %Hf & %Hlocal & %Hforeign' & #Hsnap)".
    iInv "Hinv" as ">(%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iExists g.1.
    iMod (own_update _ (●g.1) (●g.1 ⋅ ◯g.1) with "Hsnap_g") as "[Hsnap_g Hsnap']".
    { by apply auth_update_alloc, gset_local_update. }
    iFrame "Hsnap'".
    iDestruct ((forall_fin f) with "Hloc") as "[Hloc Hlocf]".
    iDestruct "Hlocf"
      as "(%h__local & %h__foreign & %h__sub & %Hproj' & %Hislocal' &
        %Hislocal & %Hisforeign & [%Hsub %Hcc] &
        Hown_local & Hown_for & Hown_sub & Hown_cc)".
    iDestruct (princ_ev__subset_cc with "Hsnap Hown_cc") as "[%Hsub_ %Hcc_]".
    iDestruct ((forall_fin' _ (λ f, StLib_GlibInv_local_part f g)) with "[Hloc Hown_local Hown_for Hown_sub Hown_cc]") as "Hloc";
      first iFrame "Hloc".
    { iExists h__local, h__foreign, h__sub. iFrame. by iPureIntro. }
    iMod ("Hclose" with "[Hloc Hglobal Hsnap Hsnap_g]") as "_".
    { iNext. iExists g. iFrame. iFrame "#". by iPureIntro. }
    iPureIntro.

    rewrite (VGst_incl_local _ Hv e). exists f.
    rewrite Hproj'. by apply Hsub, Hsub_.
  Qed.


  Lemma StLib_OwnLocalState_GlobSnap_Provenance E i s1 s2 h :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
    StLib_OwnLocalState i s1 s2 -∗
    StLib_OwnGlobalSnap h ={E}=∗
      StLib_OwnLocalState i s1 s2 ∗ ⌜∀ e, e ∈ h -> e.(EV_Orig) = i -> e ∈ s1⌝.
  Proof.
    iIntros (Hincl) "#Hinv
      (%f & %Hf & %Hlocal & %Hforeign &
        Hown_local & Hown_foreign &
        Hsnap)
      #Hsnap_global".
    iInv "Hinv" as ">(%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iDestruct ((forall_fin f) with "Hloc")
      as "[Hloc
        (%h__local' & %h__foreign' & %h__sub' &
          %Hproj' & %Hlocal' & %Hforeign' & %Hsub' & %Hcc &
          Hown_local' & Hown_foreign' & Hown_sub' & Hown_cc')]".
    iApply fupd_frame_r.
    iSplit; last first.
    - iIntros (e He_in He_orig).
      iCombine "Hsnap_g" "Hsnap_global" as "Hboth".
      iDestruct (own_valid with "Hboth") as "%Hvalid".
      apply auth_both_valid_discrete in Hvalid as [Hsub%gset_included _].
      iDestruct "Hboth" as "[Hsnap_g _]".
      iCombine "Hown_local" "Hown_local'" as "Hcomb".
      iDestruct (own_valid with "Hcomb") as "%Hvalid".
      iDestruct "Hcomb" as "[Hown_local Hown_local']".
      apply pair_valid in Hvalid as [_ ->%to_agree_op_inv_L].
      iPureIntro.
      destruct (VGst_incl_orig _ Hv e) as (f' & Hf' & He_in');
        first apply Hsub, He_in.
      assert (f = f') as ->. { apply fin_to_nat_inj. by rewrite Hf Hf'. }
      rewrite Hproj' in He_in'.
      apply elem_of_union in He_in' as [He_in' | Himp%Hforeign' ]; first exact He_in'.
      by destruct Himp.
    - iExists f. iFrame "%". iFrame.
      iMod ("Hclose" with "[Hglobal Hsnap_g Hloc Hown_local' Hown_foreign' Hown_sub' Hown_cc']") as "_"; last done.
      iNext. iExists g.
      iFrame. iFrame "%".
      iApply (forall_fin' _ (λ f, StLib_GlibInv_local_part f g)  with "[Hloc Hown_local' Hown_foreign' Hown_sub' Hown_cc']");
        first iFrame "Hloc".
      iExists h__local', h__foreign', h__sub'.
      iFrame. iFrame "%".
  Qed.

    (* Events are received locally in causal order *)
  Lemma StLib_OwnLocalState_GlobSnap_Causality E i s1 s2 h :
    ↑CRDT_InvName ⊆ E →
    StLib_GlobalInv ⊢
    StLib_OwnLocalState i s1 s2 -∗ StLib_OwnGlobalSnap h ={E}=∗
      StLib_OwnLocalState i s1 s2 ∗
      ⌜∀ a e, a ∈ h → e ∈ s1 ∪ s2 → a <_t e → a ∈ s1 ∪ s2⌝.
  Proof.
    iIntros (Hincl) "#Hinv
      (%f & %Hf & %Hlocal & %Hforeign &
        Hown_local & Hown_sub &
        #Hsnap)
      #Hsnap_global".
    iInv "Hinv" as ">(%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iDestruct ((forall_fin f) with "Hloc")
      as "[Hloc
        (%h__local & %h__foreign & %h__sub &
          %Hproj' & %Hlocal' & %Hforeign' & %Hsub' & %Hcc &
          Hown_local' & Hown_foreign' & Hown_sub' & Hown_cc')]".
    iApply fupd_frame_r.
    iSplit.
    - iExists f. iFrame "%". iFrame.
      iMod ("Hclose"
        with "[Hglobal Hsnap_g Hloc
          Hown_local' Hown_foreign' Hown_sub' Hown_cc']")
        as "_"; last done.
      iNext. iExists g.
      iFrame. iFrame "%".
      iApply ((forall_fin' f (λ f, StLib_GlibInv_local_part f g)) with "[Hloc Hown_local' Hown_foreign' Hown_sub' Hown_cc']").
      iSplitL "Hloc"; first iFrame "Hloc".
      iExists h__local, h__foreign, h__sub.
      iFrame. iFrame "%".
    - iIntros (e e' He_in He'_in Hlt_t).
      iDestruct (both_agree_agree with "Hown_local Hown_local'")
        as "(Hown_local & Hown_local' & %Heq)"; rewrite<- Heq.
      iDestruct (both_agree_agree with "Hown_sub Hown_sub'")
        as "(Hown_sub & Hown_sub' & %Heq')"; rewrite<- Heq'.

      iDestruct (auth_frag_subset with "Hsnap_g Hsnap_global") as "(Hsnap_g & _ & %Hh)".

      assert (g.2 !!! f ⊆_cc g.1) as Hsubcc.
      { split.
        - intros x Hx_in.
          apply(VGst_incl_local _ Hv x). by exists f.
        - intros x y Hx_in Hy_in Hle_t Hy_in'.
          pose proof (iffLR (elem_of_subseteq (time x) (time y)) Hle_t (get_evid x)
            (VLst_evid_incl_event _ (VGst_hst_valid _ Hv) x Hx_in)) as p.
          destruct (VLst_dep_closed _ (VGst_lhst_valid _ Hv f) y (get_evid x) Hy_in' p) as (z & Hzin & Hzevid).
          rewrite (VLst_ext_eqid _ (VGst_hst_valid _ Hv) x z Hx_in); try done.
          apply (VGst_incl_local _ Hv). by exists f. }

      assert ( h__local ∪ h__sub ⊆_cc g.1 ) as Hsubsetcc.
      { destruct Hcc as [Hsub Hcc].
        split.
        - intros x Hx_in%Hsub.
          rewrite<- Hproj' in Hx_in.
          apply (VGst_incl_local _ Hv).
          by exists f.
        - intros x y Hx_in Hy_in Hle_t Hy_in'.
          pose proof (iffLR (elem_of_subseteq (time x) (time y)) Hle_t (get_evid x)
            (VLst_evid_incl_event _ (VGst_hst_valid _ Hv) x Hx_in)) as p.
          apply (Hcc x y); try done;
            last by apply Hsub.
          rewrite<- Hproj'.
          destruct Hsubcc as [_ Hcc'].
          apply (Hcc' x y); try done.
          rewrite Hproj'. by apply Hsub. }
      iPureIntro.
      rewrite Heq Heq'.
      rewrite Heq Heq' in He'_in.

      destruct Hsubsetcc as [Hsubseteq Hcc'].
      apply (Hcc' e e').
      + by apply Hh.
      + by apply Hsubseteq.
      + by apply strict_include.
      + assumption.
  Qed.

End AboutInv.



Section Resources.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.

  Global Instance StLib_CRDT_Res_Mixin: CRDT_Res_Mixin _ _ CRDT_Op :=
  {|
    GlobState           := StLib_OwnGlobalState;
    GlobState_Exclusive := StLib_OwnGlobalState_exclusive;
    GlobState_Timeless  := StLib_OwnGlobalState_timeless;
    GlobSnap            := StLib_OwnGlobalSnap;
    GlobSnap_Timeless   := StLib_OwnGlobalSnap_Timeless;
    GlobSnap_Persistent := StLib_OwnGlobalSnap_Persistent;
    LocState            := StLib_OwnLocalState;
    LocState_Timeless   := StLib_OwnLocalState_timeless;
    LocState_Exclusive  := StLib_OwnLocalState_exclusive;
    LocSnap             := StLib_OwnLocalSnap;
    LocSnap_Timeless    := StLib_OwnLocalSnap_timeless;
    LocSnap_Persistent  := StLib_OwnLocalSnap_persistent;

    LocState_OwnOrig    := StLib_OwnLocalState_OwnOrig;
    LocState_ForeignOrig:= StLib_OwnLocalState_ForeignOrig;
    LocSnap_OwnOrig     := StLib_OwnLocalSnap_OwnOrig;
    LocSnap_ForeignOrig := StLib_OwnLocalSnap_ForeignOrig;
    LocState_TakeSnap   := StLib_OwnLocalState_TakeSnap;
    GlobSnap_Union      := StLib_OwnGlobalSnap_Union;

    GlobState_TakeSnap  := StLib_OwnGlobalState_TakeSnap;
    GlobSnap_GlobState_Included
                        := StLib_GlobalSnap_GlobState_Included;
    GlobSnap_Ext        := StLib_OwnGlobalSnap_Ext;
    GlobSnap_TotalOrder := StLib_OwnGlobalSnap_TotalOrder;

    LocSnap_Union       := StLib_OwnLocalSnap_Union;
    LocSnap_LocState_Included_CC
                        := StLib_OwnLocalSnap_LocState_Included_CC;
    LocSnap_Ext         := StLib_OwnLocalSnap_Ext;
    LocState_GlobSnap_Provenance
                        := StLib_OwnLocalState_GlobSnap_Provenance;
    LocSnap_GlobSnap_Provenance
                        := StLib_OwnLocalSnap_GlobSnap_Provenance;
    LocState_GlobSnap_Causality
                        := StLib_OwnLocalState_GlobSnap_Causality;
  |}.

End Resources.
Arguments StLib_CRDT_Res_Mixin (CRDT_Op) {_ _ _ _ _ _ _ _}.

