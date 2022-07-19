From aneris.aneris_lang Require Import resources proofmode.
From iris.algebra Require Import auth csum excl agree.
From aneris.algebra Require Import monotone.
From aneris.prelude Require Import time.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_resources.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.STS Require Import lst gst utils.
From iris.base_logic.lib Require Import invariants.

Instance timetouse: Log_Time := timestamp_time.



(** TODO: move to the */utils/v files. *)
Section TODOMove.
  Context `{CRDT_Op: Type, !EqDecision CRDT_Op, !Countable CRDT_Op}.

  Definition frac_gt_half : Qp := 2/3.
  Definition frac_gt_half_diff : Qp := 1/3.

  Definition local_events (i: RepId) (s: event_set CRDT_Op) : Prop :=
    ∀ e, e ∈ s → e.(EV_Orig) = i.
  Definition foreign_events (i: RepId) (s: event_set CRDT_Op) : Prop :=
    ∀ e, e ∈ s → e.(EV_Orig) ≠ i.

End TODOMove.



Section RequiredRAs.
  Context `{!anerisG Mdl Σ, !CRDT_Params}.
  Context `{CRDT_Op: Type, !EqDecision CRDT_Op, !Countable CRDT_Op}.

  Class Internal_StLibG Σ := mkInternalG {
      (* Global state, global snap and local state *)
      Int_StLibG_auth_gset_ev :> inG Σ (authUR (gsetUR (Event CRDT_Op)));
      (* Local state *)
      Int_StLibG_frac_agree :> inG Σ (prodR fracR (agreeR (gsetO (Event CRDT_Op))));
      (* Local state *)
      Int_StLibG_frac_agreeaeee :> inG Σ (agreeR (gsetO (Event CRDT_Op)));
      (* Local and global snapshots *)
      Int_StLibG_mono :> inG Σ (authUR (monotoneUR (@cc_subseteq CRDT_Op _ _)));
    }.

  Class StLib_GhostNames := {
    γ_global: gname;
    γ_global_snap: gname;
    (** local gnames *)
    γ_loc_own: vec gname (length CRDT_Addresses);
    γ_loc_for: vec gname (length CRDT_Addresses);
    γ_loc_sub: vec gname (length CRDT_Addresses);
    γ_loc_cc : vec gname (length CRDT_Addresses);
    StLib_InvName : namespace;
  }.
End RequiredRAs.
Arguments Internal_StLibG (CRDT_Op) {_ _} (Σ).



Section AboutGlobalInvariant.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.
  Notation princ_ev := (@principal (gset (Event CRDT_Op)) cc_subseteq).

  Definition StLib_GlobalInv : iProp Σ :=
    inv (CRDT_InvName .@ "stlib")
      (∃ (g: Gst CRDT_Op), own γ_global ((1/3)%Qp, to_agree g.1)
      ∗ own γ_global_snap (● g.1)
      ∗ ⌜ Gst_Validity g ⌝
      ∗ ∀ (k: fRepId),
          ∃ h__local h__foreign h__sub,
            ⌜ g.2 !!! k = (h__local ∪ h__sub) ⌝
            ∗ ⌜ local_events k h__local ⌝
            ∗ ⌜ foreign_events k h__foreign ⌝
            ∗ ⌜ foreign_events k h__sub ⌝
            ∗ ⌜ (h__local ∪ h__sub) ⊆_cc (h__local ∪ h__foreign) ⌝
            ∗ own (γ_loc_own !!! k) ((1/3)%Qp, to_agree h__local)
            ∗ own (γ_loc_for !!! k) ((1/3)%Qp, to_agree h__foreign)
            ∗ own (γ_loc_sub !!! k) ((1/3)%Qp, to_agree h__sub)
            ∗ own (γ_loc_cc !!! k) (● (princ_ev (h__local ∪ h__sub)))).
  Global Instance StLib_GlobalInv_persistent : Persistent StLib_GlobalInv := _.
End AboutGlobalInvariant.



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
    ∗ own (γ_loc_for !!! repId) ((2/3)%Qp, to_agree h__foreign)
    ∗ StLib_OwnLocalSnap repId' h__local h__foreign.
  Global Instance StLib_OwnLocalState_timeless i s s' :
    Timeless (StLib_OwnLocalState i s s') := _.
  Lemma StLib_OwnLocalState_exclusive i s1 s2 s1' s2' :
    StLib_OwnLocalState i s1 s2 ⊢ StLib_OwnLocalState i s1' s2' -∗ False.
  Proof.
    iIntros
      "(%f & %Hf & _ & _& _ & Hown & _)
      (%f' & %Hf' & _ & _ & _ & Hown' & _)".
    assert (f = f') as ->.
    { apply fin_to_nat_inj. by rewrite Hf Hf'. }
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



  Lemma princ_ev__subset_cc h s γ :
    own γ (◯ princ_ev s) -∗
    own γ (● princ_ev h) -∗
    ⌜ s ⊆_cc h ⌝.
  Proof.
    iIntros "#Hfrag Hauth".
    iCombine "Hauth" "Hfrag" as "Hboth".
    iDestruct (own_valid with "Hboth") as "%Hvalid".
    apply auth_both_valid_discrete in Hvalid as [Hsub Hvalid].
    iPureIntro. by apply principal_included.
  Qed.

  Lemma princ_ev__union_frag_auth h s s' γ :
    own γ (◯ princ_ev s) -∗
    own γ (◯ princ_ev s') -∗
    own γ (● princ_ev h) ==∗
    own γ (● princ_ev h) ∗ own γ (◯ princ_ev (s ∪ s')).
  Proof.
    iIntros "#Hfrag #Hfrag' Hauth".
    iPoseProof (princ_ev__subset_cc with "Hfrag Hauth") as "%Hsubset".
    iPoseProof (princ_ev__subset_cc with "Hfrag' Hauth") as "%Hsubset'".
    assert (cc_subseteq (s ∪ s') h) as Hunion.
    { apply cc_subseteq_union; done. }
    iMod (own_update _ _ (● (princ_ev h) ⋅ ◯ (princ_ev (s ∪ s'))) with "Hauth") as "Hres".
    { eapply monotone_update; done. }
    iModIntro.
    by iApply own_op.
  Qed.

  Lemma forall_fin (r: fRepId) (P: fRepId → iProp Σ) :
    (∀ (f: fRepId), P f) -∗ ((∀ f, ⌜ f ≠ r ⌝ -∗ P f) ∗ P r)%I.
  Proof.
  Admitted.

  Lemma forall_fin' (r: fRepId) (P: fRepId → iProp Σ) :
    (∀ f, ⌜ f ≠ r ⌝ -∗ P f) -∗ P r -∗ (∀ (f: fRepId), P f).
  Proof.
  Admitted.

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
      iDestruct (forall_fin with "Hloc") as "[Hloc Hlocf]".
      iDestruct "Hlocf"
        as "(%h__local & %h__foreign & %h__sub & %Hproj &
          %Hislocal & %Hisforeign & %Hisforeign' & %Hsubcc &
          Hown_local & Hown_for & Hown_sub & Hown_cc)".
      iMod (princ_ev__union_frag_auth (h__local ∪ h__sub) (s1 ∪ s2) (s1' ∪ s2')
        with "Hown Hown' Hown_cc")
        as "[Hown_cc #H2]".
      replace (s1 ∪ s2 ∪ (s1' ∪ s2')) with (s1 ∪ s1' ∪ (s2 ∪ s2')); last set_solver.
      iFrame "H2".
      iMod ("Hclose" with "[Hloc Hagree Hsnap Hown_local Hown_for Hown_sub Hown_cc]"); last done.
      { iNext. iExists g.
        iFrame. iFrame "#". iFrame "%".
        iApply (forall_fin' with "Hloc").
        iExists h__local, h__foreign, h__sub.
        iFrame. iFrame "%". }
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
          Hlocal & Hforeign & Hsnap)".
    assert (f = f') as ->. { apply fin_to_nat_inj. by rewrite Hf Hf'. }
    iInv "Hinv" as "> (%g' & Hagree & Hsnap' & %Hv'' & Hloc)" "Hclose".
    iDestruct (forall_fin with "Hloc") as "[Hloc Hlocf]".
    iDestruct "Hlocf"
      as "(%h__local & %h__foreign & %h__sub & %Hislocal' & %Hproj' &
        %Hislocal & %Hisforeign & %Hsubbcc &
        Hown_local & Hown_for & Hown_sub & Hown_cc)".
    rewrite /StLib_OwnLocalState.
    iPoseProof (princ_ev__subset_cc with "Hlsnap Hown_cc") as "%Hsubset'".
    iAssert (⌜ s1' = h__local ⌝)%I as "%Heq";
      last rewrite Heq.
    { iCombine "Hlocal" "Hown_local" as "Hcombined".
      iDestruct (own_valid_l with "Hcombined") as "[%Hvalid [Hlocal Hown_local]]".
      iPureIntro.
      by apply pair_valid in Hvalid as[_ Hvalid%to_agree_op_inv_L]. }
    iAssert (⌜ s2' = h__foreign ⌝)%I as "%Heq'"; last rewrite Heq'.
    { iCombine "Hforeign" "Hown_for" as "Hcombined".
      iDestruct (own_valid_l with "Hcombined") as "[%Hvalid' [Hforeign Hown_for]]".
      iPureIntro.
      by apply pair_valid in Hvalid' as[_ Hvalid'%to_agree_op_inv_L]. }
    iApply fupd_frame_l.
    iSplit.
    - iPureIntro.
      by apply (cc_subseteq_preorder.(PreOrder_Transitive))
        with (h__local ∪ h__sub).
    - iExists f'. iFrame "%".
      rewrite -Heq -Heq'. iFrame "%".
      iFrame.
      iMod ("Hclose" with "[Hlocal Hagree Hloc Hown_for Hown_sub Hsnap' Hown_cc]")
        as "_"; last done.
      iNext. iExists g'.
      iFrame. iFrame "#". iFrame "%".
      iApply (forall_fin' with "Hloc").
      iExists h__local, h__foreign, h__sub.
      rewrite Heq Heq'.
      iFrame "%". iFrame.
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
    iDestruct ((forall_fin f') with "Hloc") as "[Hloc Hlocf]".
    iDestruct "Hlocf"
      as "(%h__local & %h__foreign & %h__sub & %Hislocal' & %Hproj' &
        %Hislocal & %Hisforeign & %Hsubbcc &
        Hown_local & Hown_for & Hown_sub & Hown_cc)".
    iDestruct (princ_ev__subset_cc with "Hown' Hown_cc") as "[%Hsub %Hcc]".
    rewrite <-Hislocal' in Hsub.
    iDestruct (forall_fin' with "Hloc [Hown_local Hown_for Hown_sub Hown_cc]") as "Hloc".
    { iExists h__local, h__foreign, h__sub. iFrame "%". iFrame "#". iFrame. }
    clear h__local Hislocal' Hproj' Hsubbcc Hcc h__foreign Hislocal h__sub Hisforeign Hislocal.
    iDestruct ((forall_fin f) with "Hloc") as "[Hloc Hlocf]".
    iDestruct "Hlocf"
      as "(%h__local & %h__foreign & %h__sub & %Hislocal' & %Hproj &
        %Hislocal & %Hisforeign & %Hsubbcc &
        Hown_local & Hown_for & Hown_sub & Hown_cc)".
    iDestruct (princ_ev__subset_cc with "Hown Hown_cc") as "[%Hsub' %Hcc']".
    rewrite <-Hislocal' in Hsub'.
    iDestruct (forall_fin' with "Hloc [Hown_local Hown_for Hown_sub Hown_cc]") as "Hloc".
    { iExists h__local, h__foreign, h__sub. iFrame "%". iFrame "#". iFrame. }
    clear h__local Hislocal' Hproj Hsubbcc Hcc' h__foreign Hislocal h__sub Hisforeign Hislocal.
    iMod ("Hclose" with "[Hloc Hglobal Hsnap]") as "_".
    { iNext. iExists g. iFrame. iFrame "#". by iPureIntro. }
    iPureIntro.
    apply (VLst_ext_time _ (VGst_hst_valid _ Hv'')); last assumption.
    - apply (VGst_incl_local _ Hv''). exists f.
      by apply elem_of_subseteq with (s1 ∪ s2).
    - apply (VGst_incl_local _ Hv''). exists f'.
      by apply elem_of_subseteq with (s1' ∪ s2').
  Qed.
End AboutLocal.



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

  Lemma StLib_OwnGlobalSnap_Ext E s s' :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢
      StLib_OwnGlobalSnap s
      -∗ StLib_OwnGlobalSnap s'
      ={E}=∗ ⌜∀ e e', e ∈ s -> e' ∈ s' -> e =_t e' -> e = e'⌝.
  Proof.
    iIntros (Hincl) "#Hinv Hsnap Hsnap' %e %e' %He_in' %He'_in' %Heq_t".
    iDestruct (StLib_OwnGlobalSnap_Union with "Hsnap Hsnap'")
      as "#Hsnap''".
    iInv "Hinv" as "> (%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iAssert (⌜ e ∈ g.1 ⌝)%I as "%He_in".
    { unfold StLib_OwnGlobalSnap.
      iCombine "Hsnap_g" "Hsnap''" as "Hboth".
      iDestruct (own_valid with "Hboth") as "%Hvalid".
      apply auth_both_valid_discrete in Hvalid as [Hsub%gset_included _].
      iDestruct "Hboth" as "[Hsnap_g _]".
      iPureIntro.
      by apply elem_of_subseteq with (s ∪ s'); last apply elem_of_union_l. }
    iAssert (⌜ e' ∈ g.1 ⌝)%I as "%He'_in".
    { unfold StLib_OwnGlobalSnap.
      iCombine "Hsnap_g" "Hsnap''" as "Hboth".
      iDestruct (own_valid with "Hboth") as "%Hvalid".
      apply auth_both_valid_discrete in Hvalid as [Hsub%gset_included _].
      iDestruct "Hboth" as "[Hsnap_g _]".
      iPureIntro.
      by apply elem_of_subseteq with (s ∪ s'); last apply elem_of_union_r. }
    iMod ("Hclose" with "[Hsnap Hsnap' Hglobal Hsnap_g Hloc]") as "_".
    { iNext. iExists g. by iFrame. }
    iPureIntro.
    by apply (VLst_ext_time _ (VGst_hst_valid _ Hv)).
  Qed.

  Lemma StLib_OwnGlobalSnap_TotalOrder E s :
    ↑CRDT_InvName ⊆ E ->
    StLib_GlobalInv ⊢ StLib_OwnGlobalSnap s ={E}=∗ ⌜events_total_order s⌝.
  Proof.
    iIntros (Hincl) "#Hinv Hsnap %e %e' %He_in' %He'_in' %Hneq_t %Horig".
    iInv "Hinv" as "> (%g & Hglobal & Hsnap_g & %Hv & Hloc)" "Hclose".
    iAssert (⌜ e ∈ g.1 ⌝)%I as "%He_in".
    { unfold StLib_OwnGlobalSnap.
      iCombine "Hsnap_g" "Hsnap" as "Hboth".
      iDestruct (own_valid with "Hboth") as "%Hvalid".
      apply auth_both_valid_discrete in Hvalid as [Hsub%gset_included _].
      iDestruct "Hboth" as "[Hsnap_g _]".
      iPureIntro.
      by apply elem_of_subseteq with s. }
    iAssert (⌜ e' ∈ g.1 ⌝)%I as "%He'_in".
    { unfold StLib_OwnGlobalSnap.
      iCombine "Hsnap_g" "Hsnap" as "Hboth".
      iDestruct (own_valid with "Hboth") as "%Hvalid".
      apply auth_both_valid_discrete in Hvalid as [Hsub%gset_included _].
      iDestruct "Hboth" as "[Hsnap_g _]".
      iPureIntro.
      by apply elem_of_subseteq with s. }
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
    iCombine "Hown_glob Hglobal" as "Hcombined".
    iDestruct (own_valid_l with "Hcombined") as "[%Hvalid [Hown_glob Hglobal]]".
    assert (s = g.1) as ->.
    { apply pair_valid in Hvalid as [_ HH%to_agree_op_inv]. set_solver. }
    clear Hvalid.
    iMod (own_update _ (●g.1) (●g.1 ⋅ ◯g.1) with "Hsnap_g") as "[Hsnap_g Hsnap]".
    { by apply auth_update_alloc, gset_local_update. }
    rewrite agree_idemp.
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
  
    iCombine "HglobState Hglobal" as "Hboth".
    iDestruct (own_valid_l with "Hboth") as "[%Hvalid [HglobState Hglobal]]".
    assert (s' = g.1) as ->.
    { apply pair_valid in Hvalid as [_ HH%to_agree_op_inv]. set_solver. }
    clear Hvalid.
    rewrite agree_idemp.
    iMod ("Hclose" with "[Hloc Hglobal Hsnap_g]") as "_".
    { iNext. iExists g. by iFrame. }
    by iFrame.
  Qed.
End AboutGlobal.



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
    iDestruct ((forall_fin f) with "Hloc")
      as "[Hloc (%h__local & %h__foreign & %h__sub & 
        %Hproj & %Hislocal & %Hforeign & %Hsub & %Hsubcc &
        Hown_local & Hown_foreign & Hown_sub & Hown_cc)]".
    iAssert (⌜ s1 ∪ s2 ⊆ g.1 ⌝)%I as "%Hsub'".
    { iAssert (⌜ s1 ∪ s2 ⊆ h__local ∪ h__sub ⌝)%I as "%Hsub'";
        first by iDestruct (princ_ev__subset_cc with "Hsnap Hown_cc")
          as "[%Hsub' _]".
      iPureIntro.
      apply elem_of_subseteq. intros x Hx_in.
      apply (VGst_incl_local _ Hv).
      exists f. rewrite Hproj.
      by apply Hsub'. }
    iMod ("Hclose" with "[Hloc Hown_local Hown_foreign Hown_sub Hown_cc Hsnap_g Hglobal]") as "_".
    { iNext. iExists g. iFrame. iFrame "%".
      iApply (forall_fin' with "Hloc").
      iExists h__local, h__foreign, h__sub.
      iFrame "%". iFrame. }
    iPureIntro.
    by apply elem_of_subseteq with (s1 ∪ s2).
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
      assert (f = f') as ->.
      { apply fin_to_nat_inj. by rewrite Hf Hf'. }
      rewrite Hproj' in He_in'.
      apply elem_of_union in He_in' as [He_in' | Himp%Hsub' ]; first exact He_in'.
      by destruct Himp.
    - iExists f. iFrame "%". iFrame.
      iMod ("Hclose" with "[Hglobal Hsnap_g Hloc Hown_local' Hown_foreign' Hown_sub' Hown_cc']") as "_"; last done.
      iNext. iExists g.
      iFrame. iFrame "%".
      iApply (forall_fin' with "Hloc").
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
    - iIntros (e e' He_in He'_in Hlt_t).

      iCombine "Hown_local" "Hown_local'" as "Hcomb".
      iDestruct (own_valid with "Hcomb") as "%Hvalid".
      apply pair_valid in Hvalid as [_ <-%to_agree_op_inv_L].
      iDestruct "Hcomb" as "[Hown_local Hown_local']".
      iCombine "Hown_foreign" "Hown_foreign'" as "Hcomb".
      iDestruct (own_valid with "Hcomb") as "%Hvalid".
      apply pair_valid in Hvalid as [_ <-%to_agree_op_inv_L].
      iDestruct "Hcomb" as "[Hown_foreign Hown_foreign']".
      rewrite agree_idemp.

      iDestruct "Hsnap" as "(%f' & %Hf' & %Hlocal_ & %Hforeign_ & #Hsnap)".
      assert (f = f') as <-. { apply fin_to_nat_inj. by rewrite Hf Hf'. }
      iDestruct (princ_ev__subset_cc with "Hsnap Hown_cc'") as "[%Hsub'' _]".
      assert (s1 ∪ s2 = s1 ∪ h__sub') as Heqs.
      { destruct  Hcc as [? _].
        by apply set_eq, set_subseteq_antisymm. }
      rewrite -Heqs in Hproj'.
      rewrite -Hproj'.

      iCombine "Hsnap_g" "Hsnap_global" as "Hs".
      iDestruct (own_valid with "Hs") as "%Hvalid".
      apply auth_both_valid_discrete in Hvalid as [Hsub%gset_included _].
      iPureIntro.
      
      destruct (VLst_dep_closed _ (VGst_lhst_valid _ Hv f) e' (get_evid e))
        as (e'' & He''_in & Hevid); first by rewrite -Hproj' in He'_in.
      { apply evidin; first assumption.
        by apply (VLst_evid_incl_event _ (VGst_hst_valid _ Hv)), Hsub. }
      assert (e = e'') as ->; last assumption.
      apply (VLst_ext_eqid _ (VGst_hst_valid _ Hv) e e''); last eauto.
      + by apply Hsub.
      + apply ( (VGst_incl_local _ Hv) e'').
        by exists f.

    - iExists f. iFrame "%". iFrame.
      iMod ("Hclose" with "[Hglobal Hsnap_g Hloc Hown_local' Hown_foreign' Hown_sub' Hown_cc']") as "_"; last done.
      iNext. iExists g.
      iFrame. iFrame "%".
      iApply (forall_fin' with "Hloc").
      iExists h__local', h__foreign', h__sub'.
      iFrame. iFrame "%".
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


