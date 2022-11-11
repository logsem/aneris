From stdpp Require Import gmap.

From iris.base_logic Require Import invariants bi.
From iris.algebra Require Import agree auth excl gmap.

From aneris.algebra Require Import monotone.
From aneris.aneris_lang
  Require Import lang network tactics proofmode lifting resources.
From aneris.aneris_lang.lib
  Require Import list_proof lock_proof vector_clock_proof serialization_proof
    map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.prelude Require Import misc time.

From aneris.examples.crdt.spec
  Require Import crdt_events crdt_resources crdt_denot crdt_time crdt_base.
From aneris.examples.crdt.statelib.resources
  Require Import resources utils resources_inv resources_local resources_global resources_lock.

From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.user_model
  Require Import params model semi_join_lattices.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS
  Require Import utils gst lst mutation merge.
From aneris.examples.crdt.statelib.proof
  Require Import spec events utils
    stlib_proof_utils internal_specs.

Instance timeinst : Log_Time := timestamp_time.

Section Resources_utils.

  Context `{LogOp: Type, LogSt : Type,
            !anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt,
            !Internal_StLibG LogOp Σ, !StLib_GhostNames}.

  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).


  Lemma own_foreign_subset_local i (ho hf ho' hf': event_set LogOp):
    local_events i ho → foreign_events i hf
    → local_events i ho' → foreign_events i hf'
    → ho ∪ hf ⊆ ho' ∪ hf' → ho ⊆ ho'.
  Proof.
    intros Hloc Hfor Hloc' Hfor' Hsubset.
    intros x Hx_in.
    assert (x ∈ ho) as Hx_in'%Hloc; first assumption.
    apply (elem_of_union_l x ho hf), Hsubset, elem_of_union in Hx_in
      as [?|Hx_in%Hfor'];
      first assumption.
    by exfalso.
  Qed.

  Lemma own_foreign_subset_foreign i (ho hf ho' hf': event_set LogOp):
    local_events i ho → foreign_events i hf
    → local_events i ho' → foreign_events i hf'
    → ho ∪ hf ⊆ ho' ∪ hf' → hf ⊆ hf'.
  Proof.
    intros Hloc Hfor Hloc' Hfor' Hsubset.
    intros x Hx_in.
    assert (x ∈ hf) as Hx_in'%Hfor; first assumption.
    apply (elem_of_union_r x ho hf), Hsubset, elem_of_union in Hx_in
      as [Hx_in%Hloc' | ?];
      last assumption.
    by exfalso. 
  Qed.

  Lemma Lock_RemoteLockSnap__incl
    E (f f': fRepId) (st_h__local st_h__foreign h: event_set LogOp):
    ⌜ ↑CRDT_InvName ⊆ E ⌝ -∗
    StLib_GlobalInv -∗
    StLib_OwnLockInv f st_h__local st_h__foreign -∗
    StLib_OwnLockSnap f' h
    ={E}=∗
      StLib_OwnLockInv f st_h__local st_h__foreign
      ∗ ⌜ filter (λ e, EV_Orig e = f) h ⊆ st_h__local ⌝.
  Proof.
    iIntros (Hincl) "#Hinv Hown__lockinv #Hown__snap".

    iInv "Hinv" as ">(%g & Hg_ag & Hg_auth & %Hv & HS)" "Hclose".
    iDestruct ((forall_fin f') with "HS")
      as "[Hothers (%st'_h__local & %st'_h__foreign & %st'_h__sub & %Hst'_proj &
        %Hst'_locisloc & %Hst'_forisfor & %Hst'_subisfor & %Hst'_cc &
        Hst'_own__local & Hst'_own__foreign & Hst'_own__sub &
        Hst'_own__cc & Hst'_own__cc')]".
    iDestruct (princ_ev__subset_cc' with "Hown__snap Hst'_own__cc'")
      as "[Hst'_own__cc' [%Hh_sub _]]".
    rewrite -Hst'_proj in Hh_sub.
    iDestruct ((forall_fin' f')
      with "[$Hothers
        Hst'_own__local Hst'_own__foreign Hst'_own__sub
        Hst'_own__cc Hst'_own__cc']")
      as "HS".
    { iExists st'_h__local, st'_h__foreign, st'_h__sub.
      by iFrame. }

    iDestruct ((forall_fin f) with "HS")
      as "[Hothers (%st_h__local' & %st_h__foreign' & %st_h__sub' & %Hst_proj &
        %Hst_locisloc & %Hst_forisfor & %Hst_subisfor & %Hst_cc &
        Hst_own__local & Hst_own__foreign & Hst_own__sub &
        Hst_own__cc & Hst_own__cc')]".
    iDestruct "Hown__lockinv" as "(%f_ & %Hf_ & _ & _ & Hst_own__local' & Hst_own__foreign')".

    (** Unify f and f_ *)
    assert (f_ = f) as ->. { apply fin_to_nat_inj. by rewrite Hf_. }

    (** Unify the names of st_h_* *)
    iDestruct (both_agree_agree with "Hst_own__local Hst_own__local'")
      as "(Hst_own__local & Hst_own__local' & ->)".
    iDestruct (both_agree_agree with "Hst_own__foreign Hst_own__foreign'")
      as "(Hst_own__foreign & Hst_own__foreign' & ->)".


    (** Closing everythig and framing the resulting resources. *)
    iMod ("Hclose"
      with "[Hothers
        Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc'
        Hg_ag Hg_auth]") as "_"; last iModIntro.
    { iNext. iExists g. iFrame. iFrame "%".
      iApply ((forall_fin' f) with "[$Hothers Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc']").
      iExists st_h__local, st_h__foreign, st_h__sub'.
      iFrame "%". iFrame. }

    iSplitL "Hst_own__local' Hst_own__foreign'".
    { iExists f. by iFrame. }

    iPureIntro.
    assert(H1: h ⊆ g.1).
    { intros x Hx_in%Hh_sub. by apply (gst_valid_inclusion g f'). }
    assert(H2: filter (λ e : Event LogOp, EV_Orig e = f) h ⊆ g.2 !!! f).
    { intros x [Hx_proj Hx_in%H1]%elem_of_filter.
      destruct (VGst_incl_orig _ Hv x Hx_in) as (i & Hi & Hin).
      assert(i = f) as ->. { apply fin_to_nat_inj. by rewrite Hi Hx_proj. }
      assumption. }
    rewrite Hst_proj in H2.
    intros x [Hx_orig Hx_in%H1]%elem_of_filter.
    destruct (VGst_incl_orig _ Hv x Hx_in) as (i & Hi & Hin).
    assert(i = f) as ->. { apply fin_to_nat_inj. by rewrite Hi Hx_orig. }
    rewrite Hst_proj in Hin.
    by apply elem_of_union in Hin as [?|Hx_in'%Hst_forisfor]; first assumption.
  Qed.



  Lemma LocState_LockInv__sub_in_foreign E (i: fRepId) st_h__local st_h__foreign st_h__sub:
    ⌜ ↑CRDT_InvName ⊆ E ⌝ -∗
    StLib_GlobalInv
      -∗ StLib_OwnLocalState i st_h__local st_h__sub
      -∗ StLib_OwnLockInv i st_h__local st_h__foreign
      ={E}=∗ StLib_OwnLocalState i st_h__local st_h__sub
        ∗ StLib_OwnLockInv i st_h__local st_h__foreign
        ∗ ⌜ st_h__sub ⊆ st_h__foreign ⌝.
  Proof.
    iIntros (Hincl) "#Hinv Hown__local Hown__lockinv".

    iInv "Hinv" as ">(%g & Hg_ag & Hg_auth & %Hv & HS)" "Hclose".
    iDestruct ((forall_fin i) with "HS")
      as "[Hothers (%st_h__local' & %st_h__forign' & %st_h__sub' & %Hst_proj &
        %Hlocisloc & %Hforisfor & %Hsubisfor & %Hcc &
        Hst_own__local & Hst_own__foreign & Hst_own__sub &
        Hst_own__cc & Hst_own__cc')]".
    iDestruct "Hown__local" as "(%f & %Hf & _ & _ & Hst_own__local' & Hst_own__sub' & #Hlocsnap)".
    iDestruct "Hown__lockinv" as "(%f' & %Hf' & _ & _ & Hst_own__local'' & Hst_own__foreign'')".

    (** Unify i, f and f' *)
    assert (i = f) as ->. { apply fin_to_nat_inj. by rewrite Hf. }
    assert (f' = f) as ->. { apply fin_to_nat_inj. by rewrite Hf'. }

    (** Unify the names of st_h_* *)
    iDestruct (both_agree_agree with "Hst_own__local Hst_own__local''")
      as "(Hst_own__local & Hst_own__local'' & ->)".
    iDestruct (both_agree_agree with "Hst_own__sub Hst_own__sub'")
      as "(Hst_own__sub & Hst_own__sub' & ->)".
    iDestruct (both_agree_agree with "Hst_own__foreign Hst_own__foreign''")
      as "(Hst_own__foreign & Hst_own__foreign'' & ->)".
    
    (** Closing everythig and framing the resulting resources. *)
    iMod ("Hclose"
      with "[Hothers
        Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc'
        Hg_ag Hg_auth]") as "_"; last iModIntro.
    { iNext. iExists g. iFrame. iFrame "%".
      iApply ((forall_fin' f) with "[$Hothers Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc']").
      iExists st_h__local, st_h__foreign, st_h__sub.
      iFrame "%". iFrame. }

    iSplitL "Hst_own__local' Hst_own__sub'".
    { iExists f. iFrame.  by iFrame "Hlocsnap". }
    iSplitL.
    { iExists f. by iFrame. }
    iPureIntro.
    destruct Hcc as [Hsub _].
    by apply ( own_foreign_subset_foreign f st_h__local st_h__sub st_h__local st_h__foreign).
  Qed.

  Lemma LocState_LockInv__localisvalid E (i: fRepId) st_h__local st_h__foreign st_h__sub:
    ⌜ ↑CRDT_InvName ⊆ E ⌝ -∗
    StLib_GlobalInv
      -∗ StLib_OwnLocalState i st_h__local st_h__sub
      -∗ StLib_OwnLockInv i st_h__local st_h__foreign
      ={E}=∗ StLib_OwnLocalState i st_h__local st_h__sub
        ∗ StLib_OwnLockInv i st_h__local st_h__foreign
        ∗ ⌜ Lst_Validity (st_h__local ∪ st_h__foreign) ⌝.
  Proof.
    iIntros (Hincl) "#Hinv Hown__local Hown__lockinv".

    iInv "Hinv" as ">(%g & Hg_ag & Hg_auth & %Hv & HS)" "Hclose".
    iDestruct ((forall_fin i) with "HS")
      as "[Hothers (%st_h__local' & %st_h__forign' & %st_h__sub' & %Hst_proj &
        %Hlocisloc & %Hforisfor & %Hsubisfor & %Hcc &
        Hst_own__local & Hst_own__foreign & Hst_own__sub &
        Hst_own__cc & Hst_own__cc')]".
    iDestruct "Hown__local" as "(%f & %Hf & _ & _ & Hst_own__local' & Hst_own__sub' & #Hlocsnap)".
    iDestruct "Hown__lockinv" as "(%f' & %Hf' & _ & _ & Hst_own__local'' & Hst_own__foreign'')".

    (** Unify i, f and f' *)
    assert (i = f) as ->. { apply fin_to_nat_inj. by rewrite Hf. }
    assert (f' = f) as ->. { apply fin_to_nat_inj. by rewrite Hf'. }

    (** Unify the names of st_h_* *)
    iDestruct (both_agree_agree with "Hst_own__local Hst_own__local''")
      as "(Hst_own__local & Hst_own__local'' & ->)".
    iDestruct (both_agree_agree with "Hst_own__sub Hst_own__sub'")
      as "(Hst_own__sub & Hst_own__sub' & ->)".
    iDestruct (both_agree_agree with "Hst_own__foreign Hst_own__foreign''")
      as "(Hst_own__foreign & Hst_own__foreign'' & ->)".
    
    (** Closing everythig and framing the resulting resources. *)
    iMod ("Hclose"
      with "[Hothers
        Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc'
        Hg_ag Hg_auth]") as "_"; last iModIntro.
    { iNext. iExists g. iFrame. iFrame "%".
      iApply ((forall_fin' f) with "[$Hothers Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc']").
      iExists st_h__local, st_h__foreign, st_h__sub.
      iFrame "%". iFrame. }

    iSplitL "Hst_own__local' Hst_own__sub'".
    { iExists f. iFrame.  by iFrame "Hlocsnap". }
    iSplitL.
    { iExists f. by iFrame. }
    iPureIntro.
    rewrite -Hst_proj. exact (VGst_lhst_valid _ Hv f).
  Qed.

  Lemma StLib_OwnLocalState__get_fRepId repId h__local h__sub:
    StLib_OwnLocalState repId h__local h__sub
    -∗ ∃ (f: fRepId), ⌜fin_to_nat f = repId⌝
      ∗ StLib_OwnLocalState repId h__local h__sub.
  Proof.
    iIntros "(%f & %Hf & H)".
    iExists f. iSplit; first done.
    iExists f. by iSplit.
  Qed.

  Lemma Lock_Local__same_local repId h__local h__for h__local' h__sub:
    StLib_OwnLockInv repId h__local h__for
    -∗ StLib_OwnLocalState repId h__local' h__sub
    -∗ StLib_OwnLockInv repId h__local h__for
     ∗ StLib_OwnLocalState repId h__local h__sub
     ∗ ⌜ h__local'  = h__local ⌝.
  Proof.
    iIntros "Hown__lockinv Hown__local".
    iDestruct "Hown__local" as "(%f' & %Hf' & %Hlocisloc &  %Hsubisfor & Hst_own__loc & Hst_own__sub & Hsnap)".
    iDestruct "Hown__lockinv" as "(%f'' & %Hf'' & %Hlocisloc' & %Hforisfor & Hst_own__loc' & Hst_own__for)".
    assert(f' = f'') as ->.
    { apply fin_to_nat_inj. by rewrite Hf' Hf''. }
    iDestruct (both_agree_agree with "Hst_own__loc Hst_own__loc'")
      as "(Hst_own__loc & Hst_own__loc' & %heq )".
    rewrite heq.
    iSplitR "Hst_own__loc Hst_own__sub Hsnap"; last iSplitL; last done.
    all: iExists f''; iFrame; iFrame "%".
    by rewrite -heq.
  Qed.

  Lemma locals_incl_global E (s2 st_h__local st_h__foreign: event_set LogOp) (f f': fRepId) :
    ↑CRDT_InvName ⊆ E →
    ⊢ StLib_GlobalInv -∗
    own (γ_loc_cc' !!! f') (◯ princ_ev s2) -∗
    own (γ_loc_own !!! f) ((1 / 3)%Qp, to_agree st_h__local) -∗
    own (γ_loc_for !!! f) ((1 / 2)%Qp, to_agree st_h__foreign)
    ={E}=∗
      (own (γ_loc_own !!! f) ((1 / 3)%Qp, to_agree st_h__local)
      ∗ own (γ_loc_for !!! f) ((1 / 2)%Qp, to_agree st_h__foreign)
      ∗ ⌜ ∃ (g: event_set LogOp),
        s2 ⊆_cc g
        /\ (st_h__local ∪ st_h__foreign) ⊆_cc g
        /\ Lst_Validity g ⌝).
  Proof.
    iIntros (HE) "#Hinv #Hsnap Hownloc Hownfor".
    iInv "Hinv" as ">(%g & Hown_glob & Hglob_snap & %Hv & HS)" "Hclose".

    iDestruct ((forall_fin f') with "HS")
      as "[Hothers (%st_h__local' & %st_h__foreign' & %st_h__sub' & %Hst_proj &
        %st_locisloc & %st_forisfor & %st_subisfor & %Hst_cc &
        Hst_own__local'' & Hst_own__foreign' & Hst_own__sub' & Hst_own__cc' & Hst_own__cc'')]".
    iDestruct (princ_ev__subset_cc' with "Hsnap Hst_own__cc''")
      as "[Hst_own__cc'' %Hcc2]".

    iDestruct ((forall_fin' f')
      with "[$Hothers Hst_own__local'' Hst_own__foreign' Hst_own__sub'
        Hst_own__cc' Hst_own__cc'']") as "HS".
    { iExists st_h__local', st_h__foreign', st_h__sub'. by iFrame. }

    iDestruct ((forall_fin f) with "HS")
      as "[Hothers (%st_h__local2 & %st_h__foreign2 & %st_h__sub2 & %Hst_proj2 &
        %st_locisloc2 & %st_forisfor2 & %st_subisfor2 & %Hst_cc2 &
        Hst_own__local' & Hst_own__foreign' & Hst_own__sub' & Hst_own__cc' & Hst_own__cc'')]".

    iDestruct (both_agree_agree with "Hownloc Hst_own__local'")
      as "(Hownloc & Hst_own__local' & <-)".
    iDestruct (both_agree_agree with "Hownfor Hst_own__foreign'")
      as "(Hownfor & Hst_own__foreign' & <-)".

    iDestruct ((forall_fin' f)
      with "[$Hothers Hst_own__local' Hst_own__foreign' Hst_own__sub'
        Hst_own__cc' Hst_own__cc'']") as "HS".
    { iExists st_h__local, st_h__foreign, st_h__sub2. by iFrame. }

    iFrame.
    iMod ("Hclose" with "[Hown_glob Hglob_snap HS]") as "_".
    { iNext. iExists g. by iFrame. }

    iPureIntro. exists g.1.
    pose proof (gst_local_incl_cc f' _ Hv).
    pose proof (gst_local_incl_cc f _ Hv).
    split; last split; last exact (VGst_hst_valid _ Hv).
    - destruct Hcc2 as [Hs2 Hc2]. split.
      + intros x Hx%Hs2. apply (VGst_incl_local _ Hv).
        exists f'. by rewrite Hst_proj.
      + intros e e' He_in He'_in He_e'_le He'_in'.
        eapply (Hc2 e e' _ _ He_e'_le He'_in').
        Unshelve.
        2: by apply Hs2.
        rewrite<-Hst_proj.
        apply (H1 e e' He_in He'_in He_e'_le).
        rewrite Hst_proj. by apply Hs2.
    - destruct Hst_cc2 as [Hs1 Hc1]. split.
      + intros x Hx. apply (VGst_incl_local _ Hv).
        exists f. by rewrite Hst_proj2.
      + intros e e' He_in He'_in He_e'_le He'_in'.
        rewrite -Hst_proj2.
        apply (H2 e e' He_in He'_in He_e'_le).
        by rewrite Hst_proj2.
  Qed.

  Lemma merged_sets_valid E st_h__local st_h__foreign st'_h__local st'_h__sub f f_sender :
    ↑ CRDT_InvName ⊆ E →
    StLib_GlobalInv -∗
    own (γ_loc_own !!! f) ((1 / 3)%Qp, to_agree st_h__local) -∗
    own (γ_loc_for !!! f) (½, to_agree st_h__foreign) -∗
    own (γ_loc_cc' !!! f_sender) (◯ princ_ev (st'_h__local ∪ st'_h__sub))
    ={E}=∗
    ⌜Lst_Validity ((st_h__local ∪ st_h__foreign) ∪ (st'_h__local ∪ st'_h__sub))⌝
    ∗ own (γ_loc_own !!! f) ((1 / 3)%Qp, to_agree st_h__local)
    ∗ own (γ_loc_for !!! f) (½, to_agree st_h__foreign).
  Proof.
    iIntros (HE) "#Hinv Hst_own__local Hst_own__foreign Hst'_snap".
    iInv "Hinv" as ">(%g & Hglob_ag & Hglob_auth & %Hg_val & HS)" "Hclose".

    iDestruct ((forall_fin f) with "HS")
      as "[Hothers (%st_h__local' & %st_h__foreign' & %st_h__sub' & %Hst_proj &
        %st_locisloc & %st_forisfor & %st_subisfor & %Hst_cc &
        Hst_own__local' & Hst_own__for' & Hst_own__sub' & Hst_own__cc' & Hst_own__cc'')]".
    iDestruct (both_agree_agree with "Hst_own__local Hst_own__local'")
      as "(Hst_own__local & Hst_own__local' & <-)".
    iDestruct (both_agree_agree with "Hst_own__foreign Hst_own__for'")
      as "(Hst_own__foreign & Hst_own__foreign' & <-)".
    iDestruct ((forall_fin' f)
      with "[$Hothers Hst_own__local' Hst_own__foreign' Hst_own__sub'
        Hst_own__cc' Hst_own__cc'']") as "HS".
    { iExists st_h__local, st_h__foreign, st_h__sub'. by iFrame. }

    iDestruct ((forall_fin f_sender) with "HS")
      as "[Hothers (%st'_h__local' & %st'_h__foreign' & %st'_h__sub' & %Hst'_proj &
        %st'_locisloc & %st'_forisfor & %st'_subisfor & %Hst'_cc &
        Hst'_own__local' & Hst'_own__for' & Hst'_own__sub' & Hst'_own__cc' & Hst'_own__cc'')]".

    iCombine "Hst'_own__cc''" "Hst'_snap" as "Hboth".
    iDestruct (own_valid with "Hboth") as "%Hvalid".
    apply auth_both_valid_discrete in Hvalid as [Hsub _].
    iDestruct "Hboth" as "[Hst'_own__cc'' _]".

    iDestruct ((forall_fin' f_sender)
      with "[$Hothers Hst'_own__local' Hst'_own__for' Hst'_own__sub'
        Hst'_own__cc' Hst'_own__cc'']") as "HS".
    { iExists st'_h__local', st'_h__foreign', st'_h__sub'. by iFrame. }
    rewrite principal_included in Hsub.
    destruct Hsub as [Hsub Hcc].

    epose proof (merge_dst_valid g f f_sender (st'_h__local ∪ st'_h__sub) Hg_val _ _).
    Unshelve.
    2: by rewrite Hst'_proj.
    2: {
      intros x e Hx He.
      destruct (VLst_dep_closed _ (VGst_lhst_valid _ Hg_val f_sender) x e)
        as (y & Hy_in & Hy_e);
        [ apply Hsub in Hx; by rewrite Hst'_proj | assumption | ].
      exists y. split; last assumption.
      apply (Hcc y x);
        [ by rewrite Hst'_proj in Hy_in | by apply Hsub in Hx | | exact Hx ].
      apply (VLst_evid_incl_time_le _ (VGst_lhst_valid _ Hg_val f_sender) x y);
        [ rewrite Hst'_proj; apply Hsub, Hx | assumption | by rewrite Hy_e ]. }

    iMod ("Hclose" with "[HS Hglob_auth Hglob_ag]") as "_".
    { iNext. iExists g. by iFrame. }

    iModIntro. iFrame.
    iPureIntro.
    by rewrite -Hst_proj.
  Qed.


End Resources_utils.
