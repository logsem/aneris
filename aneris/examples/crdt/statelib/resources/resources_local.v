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
  Require Import utils resources_inv.



Instance timetouse: Log_Time := timestamp_time.

Section AboutLocal.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.
  Notation princ_ev := (@principal (gset (Event CRDT_Op)) cc_subseteq).

  Definition StLib_OwnLocalSnap
    (repId': RepId) (h__local h__foreign : event_set CRDT_Op): iProp Σ :=
    ∃ (repId: fRepId),
      ⌜ fin_to_nat repId = repId' ⌝
    ∗ ⌜ local_events repId h__local ⌝
    ∗ ⌜ foreign_events repId h__foreign ⌝
    ∗ own (γ_loc_cc !!! repId) (◯ (princ_ev (h__local ∪ h__foreign))).

  Global Instance StLib_OwnLocalSnap_timeless i s s':
    Timeless (StLib_OwnLocalSnap i s s') := _.
  Global Instance StLib_OwnLocalSnap_persistent i s1 s2:
    Persistent (StLib_OwnLocalSnap i s1 s2) := _.

  Definition StLib_OwnLocalState
    (repId' : RepId) (h__local h__foreign : event_set CRDT_Op) : iProp Σ :=
    ∃ (repId: fRepId),
      ⌜ fin_to_nat repId = repId' ⌝
    ∗ ⌜ local_events repId h__local ⌝
    ∗ ⌜ foreign_events repId h__foreign ⌝
    ∗ own (γ_loc_own !!! repId) ((1/3)%Qp, to_agree h__local)
    ∗ own (γ_loc_sub !!! repId) ((2/3)%Qp, to_agree h__foreign)
    ∗ StLib_OwnLocalSnap repId' h__local h__foreign.
  Global Instance StLib_OwnLocalState_timeless i s s' :
    Timeless (StLib_OwnLocalState i s s') := _.
  Lemma StLib_OwnLocalState_exclusive i s1 s2 s1' s2' :
    StLib_OwnLocalState i s1 s2 ⊢ StLib_OwnLocalState i s1' s2' -∗ False.
  Proof.
    iIntros
      "(%f & %Hf & _ & _& _ & Hown & _)
      (%f' & %Hf' & _ & _ & _ & Hown' & _)".
    assert (f = f') as ->. { apply fin_to_nat_inj. by rewrite Hf Hf'. }
    iCombine "Hown" "Hown'" as "HH".
    iDestruct (own_valid with "HH") as "%HH".
    iPureIntro. by apply pair_valid in HH as [].
  Qed.



  Lemma StLib_OwnLocalState_OwnOrig i s1 s2 :
    StLib_OwnLocalState i s1 s2 ⊢ ⌜∀ e, e ∈ s1 -> e.(EV_Orig) = i⌝.
  Proof.
    iIntros "(%f & %Hf & %Hlocal & _)".
    iPureIntro. intros e He_in.
    rewrite -Hf. by apply Hlocal.
  Qed.
  Lemma StLib_OwnLocalState_ForeignOrig i s1 s2 :
    StLib_OwnLocalState i s1 s2 ⊢ ⌜∀ e, e ∈ s2 -> ¬ (e.(EV_Orig) = i)⌝.
  Proof.
    iIntros "(%f & %Hf & _ & %Hforeign & _)".
    iPureIntro. intros e He_in.
    rewrite -Hf. by apply Hforeign.
  Qed.

  Lemma StLib_OwnLocalSnap_OwnOrig i s1 s2 :
    StLib_OwnLocalSnap i s1 s2 ⊢ ⌜∀ e, e ∈ s1 -> e.(EV_Orig) = i⌝.
  Proof.
    iIntros "(%f & %Hf & %Hlocal & _)".
    iPureIntro. intros e He_in.
    rewrite -Hf. by apply Hlocal.
  Qed.
  Lemma StLib_OwnLocalSnap_ForeignOrig i s1 s2 :
    StLib_OwnLocalSnap i s1 s2 ⊢ ⌜∀ e, e ∈ s2 -> ¬ (e.(EV_Orig) = i)⌝.
  Proof.
    iIntros "(%f & %Hf & _ & %Hforeign & _)".
    iPureIntro. intros e He_in.
    rewrite -Hf. by apply Hforeign.
  Qed.

  Lemma StLib_OwnLocalState_TakeSnap i s s' :
    StLib_OwnLocalState i s s' ⊢ StLib_OwnLocalState i s s' ∗ StLib_OwnLocalSnap i s s'.
  Proof.
    iIntros "(%f & %Hf & %Hloc & %Hfor & Hown & Hown' & Hsnap)".
    iSplit; last iAssumption.
    iExists f.
    iFrame "%". iFrame.
  Qed.

  Lemma StLib_OwnLocalSnap_Union E i s1 s2 s1' s2' :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
    StLib_OwnLocalSnap i s1 s2
    -∗ StLib_OwnLocalSnap i s1' s2'
    ={E}=∗ StLib_OwnLocalSnap i (s1 ∪ s1') (s2 ∪ s2').
  Proof.
    iIntros (Hincl) "#Hinv
      (%f & %Hf & %Hlocal & %Hforeign & #Hown)
      (%f' & %Hf' & %Hlocal' & %Hforeign' & #Hown')".
    assert( f = f' ) as <-. { apply fin_to_nat_inj. by rewrite Hf Hf'. }
    iExists f.
    iFrame "%".
    repeat (iApply fupd_frame_l; iSplit).
    - iPureIntro. intros e [He_in | He_in]%elem_of_union;
      [by apply Hlocal | by apply Hlocal'].
    - iPureIntro. intros e [He_in | He_in]%elem_of_union;
      [by apply Hforeign | by apply Hforeign'].
    - iInv "Hinv" as "> (%g & Hagree & Hsnap & %Hv'' & Hloc)" "Hclose".
      iMod ((Sn_one
               f _
               ⌜True⌝
               (own (γ_loc_cc !!! f) (◯ princ_ev ((s1∪s1') ∪ (s2∪s2')))))
             with "[] Hloc [//]")
        as "[#Hown'' Hloc]"; last first.
      { iMod ("Hclose" with "[Hagree Hsnap Hloc]") as "_"; last done.
        iNext. iExists g. by iFrame. }
      iIntros "(%h__local & %h__foreign & %h__sub & %Hproj &
              %Hislocal & %Hisforeign & %Hisforeign' & %Hsubcc &
              Hown_local & Hown_for & Hown_sub & Hown_cc & Hown_cc') _".
      iMod (princ_ev__union_frag_auth (h__local ∪ h__sub) (s1 ∪ s2) (s1' ∪ s2')
        with "Hown Hown' Hown_cc")
        as "[Hown_cc #H2]".
      replace (s1 ∪ s2 ∪ (s1' ∪ s2')) with (s1 ∪ s1' ∪ (s2 ∪ s2'));
        last set_solver.
      iFrame "H2".
      iExists h__local, h__foreign, h__sub. by iFrame.
  Qed.

  Lemma StLib_OwnLocalSnap_LocState_Included_CC E i s1 s2 s1' s2' :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
      StLib_OwnLocalSnap i s1 s2 -∗ StLib_OwnLocalState i s1' s2' ={E}=∗
      ⌜s1 ∪ s2 ⊆_cc s1' ∪ s2'⌝ ∗ StLib_OwnLocalState i s1' s2'.
  Proof.
    iIntros (Hincl)
      "#Hinv
        (%f & %Hf & %Hlocal & %Hforeign & #Hlsnap)
        (%f' & %Hf' & %Hlocal' & %Hforeign' &
          Hlocal & Hforeign & #Hsnap)".
    assert (f' = f) as ->. { apply fin_to_nat_inj. by rewrite Hf Hf'. }
    iInv "Hinv" as "> (%g' & Hagree & Hsnap' & %Hv'' & Hloc)" "Hclose".
    iMod ((Sn_one
            f _
            ⌜True⌝
            (⌜s1 ∪ s2 ⊆_cc s1' ∪ s2'⌝ ∗ StLib_OwnLocalState i s1' s2'))
            with "[Hlocal Hforeign] Hloc [//]")
    as "[[%Hsubset Hlocstate] Hloc]"; last first.
    { iMod ("Hclose" with "[Hagree Hsnap' Hloc]") as "_";
        last by (iFrame "%"; iFrame).
      iNext. iExists g'. iFrame "%". iFrame. }
    iIntros "(%h__local & %h__foreign & %h__sub & %Hislocal' & %Hproj' &
            %Hislocal & %Hisforeign & %Hsubbcc &
            Hown_local & Hown_for & Hown_sub & Hown_cc & Hown_cc') _".
    iPoseProof (princ_ev__subset_cc with "Hlsnap Hown_cc") as "%Hsubset'".
    iDestruct (both_agree_agree with "Hlocal Hown_local")
      as "(Hlocal &  Hown_local & %Heq)".
    iDestruct (both_agree_agree with "Hforeign Hown_sub")
      as "(Hforeign &  Hown_sub & %Heq')".
    rewrite Heq Heq'.
    iApply fupd_frame_l.
    iSplitL "Hown_sub Hown_for Hown_cc Hown_cc' Hlocal";
      last (iApply fupd_frame_l; iSplit).
    + iExists h__local, h__foreign, h__sub.
      by iFrame "Hown_sub Hown_for Hown_cc Hown_cc' Hlocal".
    + iPureIntro.
      by apply (cc_subseteq_preorder.(PreOrder_Transitive))
               with (h__local ∪ h__sub).
    + iExists f. iFrame "%". iFrame "#". by iFrame.
  Qed.

  Lemma StLib_OwnLocalSnap_Ext E i i' s1 s2 s1' s2' :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
    StLib_OwnLocalSnap i s1 s2 -∗ StLib_OwnLocalSnap i' s1' s2' ={E}=∗
    ⌜∀ e e', e ∈ s1 ∪ s2 -> e' ∈ s1' ∪ s2' -> e =_t e' -> e = e'⌝.
  Proof.
    iIntros (Hincl) "Hinv
      (%f & %Hf & %Hlocal & %Hforeign & #Hown)
      (%f' & %Hf' & %Hlocal' & %Hforeign' & #Hown')".
    iIntros (e e' He_in He'_in Heq_t).
    iInv "Hinv" as "> (%g & Hglobal & Hsnap & %Hv'' & Hloc)" "Hclose".

    iMod ((Sn_one f _
             ⌜True⌝
             ⌜e ∈ g.1⌝)
            with "[] Hloc [//]") as "[%He_in_global Hloc]".
    {
      iIntros "(%h__local & %h__foreign & %h__sub & %Hproj' & %Hislocal' &
                %Hislocal & %Hisforeign & [%Hsub %Hcc] &
                Hown_local & Hown_for & Hown_sub & Hown_cc & Hown_cc') _".
      iDestruct (princ_ev__subset_cc with "Hown Hown_cc") as "[%Hsub_ %Hcc_]".
      iSplitL.
      - iExists h__local, h__foreign, h__sub. iFrame. iFrame "%". by iPureIntro.
      - iPureIntro.
        rewrite (VGst_incl_local _ Hv'' e). exists f.
        rewrite Hproj'. by apply Hsub, Hsub_. }

    iMod ((Sn_one f' _
             ⌜True⌝
             ⌜e' ∈ g.1⌝)
            with "[] Hloc [//]") as "[%He'_in_global Hloc]".
    {
      iIntros "(%h__local & %h__foreign & %h__sub & %Hproj' & %Hislocal' &
                %Hislocal & %Hisforeign & [%Hsub %Hcc] &
                Hown_local & Hown_for & Hown_sub & Hown_cc & Hown_cc') _".
      iDestruct (princ_ev__subset_cc with "Hown' Hown_cc") as "[%Hsub_ %Hcc_]".
      iSplitL.
      - iExists h__local, h__foreign, h__sub. iFrame. by iPureIntro.
      - iPureIntro.
        rewrite (VGst_incl_local _ Hv'' e'). exists f'.
        rewrite Hproj'. by apply Hsub, Hsub_. }

    iMod ("Hclose" with "[Hloc Hglobal Hsnap]") as "_".
    { iNext. iExists g. iFrame. iFrame "#". by iPureIntro. }
    iPureIntro.
    apply (VLst_ext_time _ (VGst_hst_valid _ Hv'')); assumption.
  Qed.

  Lemma StLib_OwnLocalSnap_EV_Orig E i s1 s2 :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
    StLib_OwnLocalSnap i s1 s2 ={E}=∗
    ⌜∀ e, e ∈ s1 ∪ s2 → (EV_Orig e < length CRDT_Addresses)%Z⌝.
  Proof.
  Admitted.

End AboutLocal.
