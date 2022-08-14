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
    OwnLockInv f st_h__local st_h__foreign -∗
    own (γ_loc_cc' !!! f') (◯ princ_ev h)
    ={E}=∗
      OwnLockInv f st_h__local st_h__foreign
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
      -∗ OwnLockInv i st_h__local st_h__foreign
      ={E}=∗ StLib_OwnLocalState i st_h__local st_h__sub
        ∗ OwnLockInv i st_h__local st_h__foreign
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
      -∗ OwnLockInv i st_h__local st_h__foreign
      ={E}=∗ StLib_OwnLocalState i st_h__local st_h__sub
        ∗ OwnLockInv i st_h__local st_h__foreign
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

End Resources_utils.
