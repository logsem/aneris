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
  Require Import utils resources_inv resources_local.

Section AboutGlobal.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.
  Notation princ_ev := (@principal (gset (Event CRDT_Op)) cc_subseteq).

  Definition StLib_OwnGlobalSnap (h: event_set CRDT_Op) : iProp Σ :=
    own γ_global_snap (◯ h).
  Global Instance StLib_OwnGlobalSnap_Timeless s :
    Timeless (StLib_OwnGlobalSnap s) := _.
  Global Instance StLib_OwnGlobalSnap_Persistent s :
    Persistent (StLib_OwnGlobalSnap s) := _.


  Definition StLib_OwnGlobalState (h : event_set CRDT_Op) : iProp Σ :=
    own γ_global ((2/3)%Qp, to_agree h).
  Lemma StLib_OwnGlobalState_exclusive s s' :
    StLib_OwnGlobalState s ⊢ StLib_OwnGlobalState s' -∗ False.
  Proof.
    iIntros "Hown Hown'".
    iCombine "Hown" "Hown'" as "HH".
    iDestruct (own_valid with "HH") as "%HH".
    iPureIntro. by apply pair_valid in HH as [].
  Qed.
  Global Instance StLib_OwnGlobalState_timeless s :
    Timeless (StLib_OwnGlobalState s) := _.



  Lemma StLib_OwnGlobalSnap_Union s s' :
    StLib_OwnGlobalSnap s ⊢ StLib_OwnGlobalSnap s' -∗ StLib_OwnGlobalSnap (s ∪ s').
  Proof.
    iIntros "Hs Hs'".
    iCombine "Hs" "Hs'" as "?".
    iFrame.
  Qed.

  Lemma auth_frag_subset (γ: gname) (g s : event_set CRDT_Op):
    own γ (● g) -∗ own γ (◯ s) -∗ own γ (● g) ∗ own γ (◯ s) ∗ ⌜s ⊆ g⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iCombine "Hauth" "Hfrag" as "Hboth".
    iDestruct (own_valid with "Hboth") as "%Hvalid".
    apply auth_both_valid_discrete in Hvalid as [Hsub%gset_included _].
    iDestruct "Hboth" as "[Hauth Hfrag]".
    by iFrame.
  Qed.

  Lemma global__elem_of_snap_in_global
    {e: Event CRDT_Op} {s: event_set CRDT_Op} (p: e ∈ s) (g: event_set CRDT_Op) :
    StLib_OwnGlobalSnap s -∗ own γ_global_snap (● g) -∗
      StLib_OwnGlobalSnap s ∗ own γ_global_snap (● g) ∗ ⌜ e ∈ g ⌝.
  Proof.
    iIntros "Hsnap Hsnap_g".
    iDestruct (auth_frag_subset with "Hsnap_g Hsnap")
      as "(Hsnap_g & Hsnap & %Hsub)".
    iFrame.
    iPureIntro.
    by apply elem_of_subseteq with s.
  Qed.

  Lemma StLib_OwnGlobalSnap_Ext E s s' :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
      StLib_OwnGlobalSnap s
      -∗ StLib_OwnGlobalSnap s'
      ={E}=∗ ⌜∀ e e', e ∈ s -> e' ∈ s' -> e =_t e' -> e = e'⌝.
  Proof.
    iIntros (Hincl) "#Hinv #Hsnap #Hsnap' %e %e' %He_in' %He'_in' %Heq_t".
    iInv "Hinv" as "> (%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iDestruct ((global__elem_of_snap_in_global He_in') with "Hsnap Hsnap_g")
      as "(_ & Hsnap_g & %He_in)".
    iDestruct ((global__elem_of_snap_in_global He'_in') with "Hsnap' Hsnap_g")
      as "(_ & Hsnap_g & %He'_in)".
    iMod ("Hclose" with "[Hsnap Hsnap' Hglobal Hsnap_g Hloc]") as "_".
    { iNext. iExists g. by iFrame. }
    iPureIntro.
    by apply (VLst_ext_time _ (VGst_hst_valid _ Hv)).
  Qed.

  Lemma StLib_OwnGlobalSnap_TotalOrder E s :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢ StLib_OwnGlobalSnap s ={E}=∗ ⌜events_total_order s⌝.
  Proof.
    iIntros (Hincl) "#Hinv #Hsnap %e %e' %He_in' %He'_in' %Hneq_t %Horig".
    iInv "Hinv" as "> (%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iDestruct ((global__elem_of_snap_in_global He_in') with "Hsnap Hsnap_g")
      as "(_ & Hsnap_g & %He_in)".
    iDestruct ((global__elem_of_snap_in_global He'_in') with "Hsnap Hsnap_g")
      as "(_ & Hsnap_g & %He'_in)".
    iMod ("Hclose" with "[Hsnap Hglobal Hsnap_g Hloc]") as "_".
    { iNext. iExists g. by iFrame. }
    iPureIntro.
    destruct (VLst_same_orig_comp _ (VGst_hst_valid _ Hv) e e') as [|[|]];
      try done;
      [by left | | by right].
    exfalso; destruct Hneq_t.
    by apply (VLst_ext_time _ (VGst_hst_valid _ Hv)).
  Qed.

  Lemma StLib_OwnGlobalState_TakeSnap E s :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
    StLib_OwnGlobalState s ={E}=∗ StLib_OwnGlobalState s ∗ StLib_OwnGlobalSnap s.
  Proof.
    iIntros (HEincl) "#Hinv Hown_glob".
    iInv "Hinv" as "> (%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iDestruct (both_agree_agree with "Hown_glob Hglobal")
      as "(Hown_glob & Hglobal & ->)".
    iMod (own_update _ (●g.1) (●g.1 ⋅ ◯g.1) with "Hsnap_g") as "[Hsnap_g Hsnap]".
    { by apply auth_update_alloc, gset_local_update. }
    iMod ("Hclose" with "[Hloc Hsnap_g Hglobal]") as "_".
    { iNext. iExists g. by iFrame. }
    by iFrame.
  Qed.

  Lemma StLib_GlobalSnap_GlobState_Included E s s' :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
      StLib_OwnGlobalSnap s
      -∗ StLib_OwnGlobalState s'
      ={E}=∗ ⌜s ⊆ s'⌝ ∗ StLib_OwnGlobalState s'.
  Proof.
    iIntros (Hincl) "#Hinv #Hsnap HglobState".
    iInv "Hinv" as "> (%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iCombine "Hsnap_g" "Hsnap" as "Hboth".
    iDestruct (own_valid with "Hboth") as "%Hvalid".
    apply auth_both_valid_discrete in Hvalid as [Hsub%gset_included _].
    iDestruct "Hboth" as "[Hsnap_g _]".
    iDestruct (both_agree_agree with "HglobState Hglobal")
      as "(HglobState & Hglobal & ->)".
    iMod ("Hclose" with "[Hloc Hglobal Hsnap_g]") as "_".
    { iNext. iExists g. by iFrame. }
    by iFrame.
  Qed.
End AboutGlobal.

