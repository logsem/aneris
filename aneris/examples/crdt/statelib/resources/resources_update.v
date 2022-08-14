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
  Require Import resources utils resources_inv resources_local resources_global resources_lock resources_utils.

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



Section Resources_updates.

  Context `{LogOp: Type, LogSt : Type,
            !anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt,
            !Internal_StLibG LogOp Σ, !StLib_GhostNames}.

  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).



  Lemma get_state_update E (i: fRepId) st_h__local st_h__foreign st_h__sub:
    ⌜ ↑CRDT_InvName ⊆ E ⌝ -∗
    StLib_GlobalInv
      -∗ StLib_OwnLocalState i st_h__local st_h__sub
      -∗ OwnLockInv i st_h__local st_h__foreign
      ={E, E}=∗ StLib_OwnLocalState i st_h__local st_h__foreign
        ∗ OwnLockInv i st_h__local st_h__foreign.
  Proof.
    iIntros (Hincl) "#Hinv
      (%f & %Hf & _ & _ & Hst_own__local & Hst_own__sub & Hown_localsnap)
      (%f' & %Hf' & _ & _ & Hst_own__local' & Hst_own__foreign')".
    iInv "Hinv" as ">(%g & Hown_global & Hown_global_snap & %Hv & HS)" "Hclose".
    iDestruct ((forall_fin i) with "HS")
      as "[Hothers (%st_h__local' & %st_h__foreign' & %st_h__sub' & %Hst_proj &
        %st_locisloc & %st_forisfor & %st_subisfor & %Hst_cc &
        Hst_own__local'' & Hst_own__for'' & Hst_own__sub'' & Hst_own__cc'' & Hst_own__cc''')]".
    assert (i = f) as ->. { apply fin_to_nat_inj. by rewrite-Hf. }
    assert (f = f') as <-. { apply fin_to_nat_inj. by rewrite Hf'. }

    (** Unification of the history names *)
    iDestruct (both_agree_agree with "Hst_own__local Hst_own__local''")
      as "(Hst_own__local & Hst_own__local'' & <-)".
    iDestruct (both_agree_agree with "Hst_own__sub Hst_own__sub''")
      as "(Hst_own__sub & Hst_own__sub'' & <-)".
    iDestruct (both_agree_agree with "Hst_own__foreign' Hst_own__for''")
      as "(Hst_own__foreign' & Hst_own__for'' & <-)".
    
    (** Combination of the resources (related to sub) to prepare the updates *)
    iCombine "Hst_own__sub" "Hst_own__sub''" as "Hst_own__sub".

    (** Update st_h__sub → st_h__for *)
    iDestruct(own_update _ _ ((2/3 + 1/3)%Qp, to_agree st_h__foreign)
      with "Hst_own__sub")
      as ">[Hst_own__sub Hst_own__sub']".
    { assert (2/3 + 1/3 = 1)%Qp as ->; first compute_done.
      by apply cmra_update_exclusive. }
    iDestruct (own_update _ _
      (● princ_ev (st_h__local ∪ st_h__foreign)
        ⋅ ◯ princ_ev (st_h__local ∪ st_h__foreign ))
      with "Hst_own__cc''")
      as ">[Hst_own_cc'' #Hfrag]"; first by apply monotone_update.

    (** Closing the invariant *)
    iDestruct ((forall_fin' f)
      with "[$Hothers Hst_own__local'' Hst_own__foreign' Hst_own__sub'
        Hst_own_cc'' Hst_own__cc''']") as "HS".
    { iExists st_h__local, st_h__foreign, st_h__foreign. by iFrame. }
    iMod ("Hclose" with "[Hown_global_snap Hown_global HS]") as "_";
      last iModIntro.
    { iNext. iExists g. by iFrame. }

    iSplitR "Hst_own__for'' Hst_own__local'".
    - iExists f. rewrite/StLib_OwnLocalSnap. iFrame "%". iFrame.
      iExists f. by iFrame "#".
    - iExists f. by iFrame.
  Qed.



  Lemma update_update E (i: fRepId) op st_h__local st_h__foreign st_h__sub h:
    let fev := fresh_event (st_h__local ∪ st_h__foreign) op i in
    ⌜ ↑CRDT_InvName ⊆ E ⌝
    -∗ StLib_GlobalInv
    -∗ StLib_OwnLocalState i st_h__local st_h__sub
    -∗ OwnLockInv i st_h__local st_h__foreign
    -∗ StLib_OwnGlobalState h
    ={E,E}=∗
      StLib_OwnLocalState i (st_h__local ∪ {[fev]}) st_h__foreign
      ∗ OwnLockInv i (st_h__local ∪ {[fev]}) st_h__foreign
      ∗ StLib_OwnGlobalState (h ∪ {[ fev ]})
      ∗ ⌜fev ∉ h ⌝
      ∗ ⌜fev ∉ st_h__local ∪ st_h__foreign ⌝
      ∗ ⌜fev ∈ Maximals (h ∪ {[fev]}) ⌝
      ∗ ⌜Maximum (st_h__local ∪ {[fev]} ∪ st_h__foreign) = Some fev ⌝
      ∗ ⌜Lst_Validity (st_h__local ∪ st_h__foreign ∪ {[fev]})⌝.
  Proof.
    iIntros (fev Hincl) "#Hinv Hown__local Hown__lockinv Hown__global".

    (** Get the resources from the local state, global invariant and lock *)
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
    iDestruct (both_agree_agree with "Hst_own__local Hst_own__local'")
      as "(Hst_own__local & Hst_own__local' & ->)".
    iDestruct (both_agree_agree with "Hst_own__sub Hst_own__sub'")
      as "(Hst_own__sub & Hst_own__sub' & ->)".
    iDestruct (both_agree_agree with "Hst_own__foreign Hst_own__foreign''")
      as "(Hst_own__foreign & Hst_own__foreign'' & ->)".
    iDestruct (both_agree_agree with "Hg_ag Hown__global")
      as "(Hg_ag & Hown__global & <-)".


    (** Combining the resources to prepare their update. *)
    iCombine "Hst_own__local" "Hst_own__local'" as "Hst_own__local".
    iCombine "Hst_own__local" "Hst_own__local''" as "Hst_own__local".
    iCombine "Hst_own__sub" "Hst_own__sub'" as "Hst_own__sub".
    iCombine "Hg_ag" "Hown__global" as "Hg_ag".

    (** Update of the agreeing resources *)
    iDestruct (own_update _ _ ((1/3 + 1/3 + 1/3)%Qp, to_agree (st_h__local ∪ {[fev]}))
      with "Hst_own__local")
      as ">[[Hst_own__local Hst_own__local' ] Hst_own__local'']".
    { assert(1/3 + 1/3 + 1/3 = 1)%Qp as ->; first compute_done.
      by apply cmra_update_exclusive. }

    iDestruct (own_update _ _ ((1/3 + 2/3)%Qp, to_agree st_h__foreign)
      with "Hst_own__sub")
      as "> (Hst_own__sub & Hst_own__sub')".
    { assert(1/3 + 2/3 = 1)%Qp as ->; first compute_done.
      by apply cmra_update_exclusive. }

    iDestruct (own_update _ _ ((1/3 + 2/3)%Qp, to_agree (g.1 ∪ {[fev]}))
      with "Hg_ag")
      as "> (Hg_ag & Hown__global)".
    { assert(1/3 + 2/3 = 1)%Qp as ->; first compute_done.
      by apply cmra_update_exclusive. }

    (** Update of the authoritative resources. *)
    iDestruct (own_update _ _ (● (g.1 ∪ {[ fev ]}))
      with "Hg_auth")
      as ">Hg_auth".
    { rewrite (auth_update_auth g.1 (g.1 ∪ {[fev]})(g.1 ∪ {[fev]})); first done.
      apply gset_local_update, union_subseteq_l. }

    iDestruct (own_update _ _ (● princ_ev (st_h__local ∪ {[ fev ]} ∪ st_h__foreign) ⋅ ◯ princ_ev (st_h__local ∪ {[fev]} ∪ st_h__foreign))
      with "Hst_own__cc") as "> [Hst_own__cc #Hcc_frag]".
    { apply monotone_update; last done.
      replace (st_h__local ∪ {[fev]} ∪ st_h__foreign)
        with  (st_h__local ∪ st_h__foreign ∪ {[fev]}); last set_solver.
      destruct Hcc as [Hsubset Hcc].
      split; first set_solver.
      intros ev ev'
        [Hev_in | ->%elem_of_singleton]%elem_of_union
        [Hev'_in | ->%elem_of_singleton]%elem_of_union
        Hle Hev'_in';
        first by apply (Hcc ev ev').
      1,3: ( exfalso;
        apply Hsubset in Hev'_in';
        apply (fresh_event_is_fresh (g.2 !!! f) f op (VGst_lhst_valid _ Hv f));
        by rewrite Hst_proj -/fev).
      exfalso.
      destruct (fresh_event_time_mon (g.2 !!! f) op f) with ev' as [H1 H2];
        try by destruct (VGst_lhst_valid _ Hv f).
      - by rewrite Hst_proj.
      - apply H2.
        by rewrite Hst_proj -/fev. }
    iDestruct (own_update _ _ (● princ_ev (st_h__local ∪ {[ fev ]} ∪ st_h__foreign) ⋅ ◯ princ_ev (st_h__local ∪ {[fev]} ∪ st_h__foreign))
      with "Hst_own__cc'") as "> [Hst_own__cc' _]".
    { apply monotone_update; last done.
      replace (st_h__local ∪ {[fev]} ∪ st_h__foreign)
        with  (st_h__local ∪ st_h__foreign ∪ {[fev]}); last set_solver.
      destruct Hcc as [Hsubset Hcc].
      split; first set_solver.
      intros ev ev'
        [Hev_in | ->%elem_of_singleton]%elem_of_union
        [Hev'_in | ->%elem_of_singleton]%elem_of_union
        Hle Hev'_in'; try done.
      exfalso.
      destruct (fresh_event_time_mon (g.2 !!! f) op f) with ev' as [H1 H2];
        try by destruct (VGst_lhst_valid _ Hv f).
      - by rewrite Hst_proj.
      - apply H2.
        by rewrite Hst_proj -/fev. }

    pose (mutator_global_valid g op f Hv) as Hv'.
    assert (fresh_event (g.2 !!! f) op f = fev) as Hfev_eq.
    { unfold fev. by rewrite Hst_proj. }
     
    assert (Hloc_isloc: local_events f (st_h__local ∪ {[fev]})).
    { intros x [?%Hlocisloc | ->%elem_of_singleton]%elem_of_union;
      [ assumption | by rewrite/fev fresh_event_orig ]. }


    assert (fev ∉ st_h__local ∪ st_h__foreign).
    { rewrite/fev -Hst_proj.
      exact (fresh_event_is_fresh (g.2 !!! f) f op (VGst_lhst_valid _ Hv f)). }
    assert (fev ∉ g.1).
    { rewrite -Hfev_eq. exact (fresh_event_is_fresh_global g f op Hv). }
    assert (fev ∈ Maximals (g.1 ∪ {[fev]})).
    { rewrite/fev-Hst_proj.
      by apply fresh_events_mutator_global_maximals. }

    assert(Maximum (st_h__local ∪ {[fev]} ∪ st_h__foreign) = Some fev).
    { apply Maximum_correct; last split.
      - intros x y Hc_in Hy_in.
        destruct (VGst_lhst_valid _ Hv' f).
        apply (VLst_ext_time x y); simpl;
          rewrite vlookup_insert Hst_proj -/fev; set_solver.
      - by apply elem_of_union_l, elem_of_union_r, elem_of_singleton.
      - intros ev Hev_in Hev_neq.
        destruct (fresh_event_time_mon (g.2 !!! f) op f) with ev as [Ha j];
          try by destruct (VGst_lhst_valid _ Hv f).
        rewrite Hst_proj; set_solver.
        destruct (TM_le_eq_or_lt (time ev) (time fev)) as [?|];
          [ by rewrite /fev -Hst_proj | | assumption ].
        exfalso. apply j. rewrite H4.
        by rewrite Hst_proj -/fev. }

    assert(Lst_Validity (g.2 !!! f ∪{[fev]})).
    { pose (VGst_lhst_valid _ Hv' f) as Htmp.
      rewrite /= in Htmp.
      rewrite -Hfev_eq.
      by assert ((vinsert f (g.2 !!! f ∪ {[fresh_event (g.2 !!! f) op f]}) g.2 !!! f)
        = (g.2 !!! f ∪ {[fresh_event (g.2 !!! f) op f]})) as <-;
        first by rewrite vlookup_insert. }

    (** Closing everythig and framing the resulting resources. *)
    iMod ("Hclose"
      with "[Hothers
        Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc'
        Hg_ag Hg_auth]") as "_"; last iModIntro.
    { iNext. iExists (g.1 ∪ {[fresh_event (g.2 !!! f) op f]},
      vinsert f (g.2 !!! f ∪ {[fresh_event (g.2 !!! f) op f]}) g.2).
      simpl. rewrite Hfev_eq. iFrame. iSplit; first by rewrite -Hfev_eq.
      iApply (forall_fin' f). iSplitL "Hothers".
      - iDestruct "Hothers" as "(%S & %HS_def & HS)".
        iExists S. iSplit; first done.
        iApply (big_sepS_mono with "HS").
        iIntros (x Hx_in) "(%__local & %__foreign & %__sub & %__Hproj & %__islocal & %__isfor & %__issub & %__iscc & __ownloc & __own)".
        iExists __local, __foreign, __sub.
        repeat iSplit; try done.
        + iPureIntro. simpl. rewrite vlookup_insert_ne; first assumption.
          set_solver.
        + iPureIntro. by destruct __iscc.
        + iPureIntro. by destruct __iscc.
        + iFrame.
      - iExists (st_h__local ∪ {[ fev]}), st_h__foreign, st_h__foreign.
        iFrame. iFrame "%".
        repeat iSplit ; [ | done..].
        rewrite vlookup_insert Hst_proj.
        iPureIntro.
        set_solver. }
    rewrite Hst_proj in H5.
    iFrame. iFrame "%".
    iSplitR "Hst_own__foreign'' Hst_own__local'";
      iExists f; iFrame ; iFrame "%".
    iExists f. iFrame "%". iFrame "Hcc_frag".
  Qed.


  Lemma broadcast_update E (i: fRepId) st_h__local st_h__foreign:
    ⌜ ↑CRDT_InvName ⊆ E ⌝
    -∗ StLib_GlobalInv
    -∗ OwnLockInv i st_h__local st_h__foreign
    ={E}=∗ OwnLockInv i st_h__local st_h__foreign
      ∗ own (γ_loc_cc' !!! i) (◯ princ_ev (st_h__local ∪ st_h__foreign))
      ∗ ⌜ Lst_Validity (st_h__local ∪ st_h__foreign) ⌝.
  Proof.
    iIntros (Hincl) "#Hinv Hown__lockinv".

    iInv "Hinv" as ">(%g & Hg_ag & Hg_auth & %Hv & HS)" "Hclose".
    iDestruct ((forall_fin i) with "HS")
      as "[Hothers (%st_h__local' & %st_h__forign' & %st_h__sub' & %Hst_proj &
        %Hlocisloc & %Hforisfor & %Hsubisfor & %Hcc &
        Hst_own__local & Hst_own__foreign & Hst_own__sub &
        Hst_own__cc & Hst_own__cc')]".
    iDestruct "Hown__lockinv" as "(%f & %Hf & _ & _ & Hst_own__local' & Hst_own__foreign')".

    assert (i = f) as ->. { apply fin_to_nat_inj. by rewrite Hf. }

    (** Unify the names of st_h_* *)
    iDestruct (both_agree_agree with "Hst_own__local Hst_own__local'")
      as "(Hst_own__local & Hst_own__local' & ->)".
    iDestruct (both_agree_agree with "Hst_own__foreign Hst_own__foreign'")
      as "(Hst_own__foreign & Hst_own__foreign' & ->)".

    iDestruct (own_update _ _
      (● princ_ev (st_h__local ∪ st_h__foreign)
      ⋅ ◯ princ_ev (st_h__local ∪ st_h__foreign)) with "Hst_own__cc'")
      as ">[Hst_own__cc' #Hsnap]";
      first by apply monotone_update.

    assert (Lst_Validity (st_h__local ∪ st_h__foreign)).
    { rewrite -Hst_proj. exact (VGst_lhst_valid _ Hv f). }

    iMod ("Hclose"
      with "[Hothers
        Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc'
        Hg_ag Hg_auth]") as "_"; last iModIntro.
    { iNext. iExists g. iFrame. iFrame "%".
      iApply ((forall_fin' f) with "[$Hothers Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc']").
      iExists st_h__local, st_h__foreign, st_h__sub'.
      iFrame "%". iFrame. }

    iSplitL.
    { iExists f. by iFrame. }
    by iFrame "#".
  Qed.


  Lemma merge_update E (i j: fRepId) (st_h__local st_h__foreign st'_h__local st'_h__foreign: event_set LogOp):
    ⌜ ↑CRDT_InvName ⊆ E ⌝
    -∗ StLib_GlobalInv
    -∗ OwnLockInv i st_h__local st_h__foreign
    -∗ own (γ_loc_cc' !!! j) (◯ princ_ev (st'_h__local ∪ st'_h__foreign))
    -∗ ⌜ Lst_Validity (st'_h__local ∪ st'_h__foreign) ⌝
    ={E}=∗
      OwnLockInv i st_h__local
        (st_h__foreign ∪
          (filter (λ e, EV_Orig e ≠ i) (st'_h__local ∪ st'_h__foreign))).
  Proof.
    iIntros (Hincl) "#Hinv Hown__lockinv #Hforeign_snap %Hval".

    iInv "Hinv" as ">(%g & Hg_ag & Hg_auth & %Hv & HS)" "Hclose".

    iDestruct ((forall_fin j) with "HS")
      as "[Hothers (%st'_h__local' & %st'_h__forign' & %st'_h__sub & %Hst'_proj &
        %H'locisloc & %H'forisfor & %H'subisfor & %H'cc &
        Hst'_own__local & Hst'_own__foreign & Hst'_own__sub &
        Hst'_own__cc & Hst'_own__cc')]".
    iDestruct (princ_ev__subset_cc' with "Hforeign_snap Hst'_own__cc'")
      as "[Hst'_own__cc' %Hcc']".
    rewrite -Hst'_proj in Hcc'.
    destruct Hcc' as [Hcc'_sub Hcc'_cc].
    iDestruct ((forall_fin' j)
      with "[$Hothers Hst'_own__local Hst'_own__foreign Hst'_own__sub Hst'_own__cc Hst'_own__cc']")
      as "HS".
    { iExists st'_h__local', st'_h__forign', st'_h__sub. by iFrame. }

    iDestruct ((forall_fin i) with "HS")
      as "[Hothers (%st_h__local' & %st_h__forign' & %st_h__sub & %Hst_proj &
        %Hlocisloc & %Hforisfor & %Hsubisfor & %Hcc &
        Hst_own__local & Hst_own__foreign & Hst_own__sub &
        Hst_own__cc & Hst_own__cc')]".
    iDestruct "Hown__lockinv" as "(%f & %Hf & _ & _ & Hst_own__local' & Hst_own__foreign')".

    (** Unify i, f and f' *)
    assert (i = f) as ->. { apply fin_to_nat_inj. by rewrite Hf. }
    
    (** Unify the names of st'?_h_* *)
    iDestruct (both_agree_agree with "Hst_own__local Hst_own__local'")
      as "(Hst_own__local & Hst_own__local' & ->)".
    iDestruct (both_agree_agree with "Hst_own__foreign Hst_own__foreign'")
      as "(Hst_own__foreign & Hst_own__foreign' & ->)".

    set filtered_out := filter (λ e, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__foreign).

    assert(H1: st'_h__local ∪ st'_h__foreign ⊆ g.1).
    { by intros x Hx_in%Hcc'_sub%gst_valid_inclusion. }

    assert(Gst_Validity
           (g.1, vinsert f (g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign)) g.2)).
    { apply (merge_global_valid g f j (st'_h__local ∪ st'_h__foreign) Hv Hcc'_sub).
      by destruct Hval. }

    assert (Hccimpl: cc_impl (st_h__local ∪ st_h__foreign)
      (st_h__local ∪ st_h__foreign ∪ filtered_out)).
    { intros x y [? | Hx_in]%elem_of_union Hy_in Hxy_le Hy_in';
        first assumption.
      rewrite -Hst_proj.
      apply elem_of_filter in Hx_in as [_ Hx_in%H1].
      rewrite -Hst_proj in Hy_in'.
      assert (y ∈ g.2 !!! f) as Hy_in''; first assumption.
      apply gst_valid_inclusion in Hy_in'; try done.
      by apply (gst_local_incl_cc f g Hv x y Hx_in Hy_in'). }

    assert(foreign_events f (st_h__foreign ∪ filtered_out)).
    { intros x [?%Hforisfor|[? _]%elem_of_filter]%elem_of_union; assumption. }

    assert(st_h__local ∪ st_h__sub ⊆ st_h__local ∪ (st_h__foreign ∪ filtered_out)).
    { assert (st_h__local ∪ (st_h__foreign ∪ filtered_out) = (st_h__local ∪ st_h__foreign) ∪ filtered_out) as ->; first set_solver.
      destruct Hcc as [Hsub _].
      intros x Hx_in%Hsub. by apply elem_of_union_l. }

    assert(causally_closed LogOp (st_h__local ∪ st_h__sub) (st_h__local ∪ (st_h__foreign ∪ filtered_out))).
    { intros x y Hx_in Hy_in Hxy_le Hy_in'.
      destruct Hcc as [Hsub Hcc].
      assert(st_h__local ∪ st_h__foreign ∪ filtered_out
        = st_h__local ∪ (st_h__foreign ∪ filtered_out)) as H'.
      { (** set_solver takes a lot of time on this *)
        apply set_eq. intros z. split.
        - intros [[?|?]%elem_of_union|?]%elem_of_union;
          [ by apply elem_of_union_l
          | by apply elem_of_union_r, elem_of_union_l
          | by do 2 apply elem_of_union_r].
        - intros [?|[?|?]%elem_of_union]%elem_of_union;
          [ by do 2 apply elem_of_union_l
          | by apply elem_of_union_l, elem_of_union_r
          | by apply elem_of_union_r]. }
      assert (Hy_in'': y ∈ st_h__local ∪ st_h__foreign);
        first by apply Hsub.
      apply (Hcc x y); try done.
      apply (Hccimpl x y); try done; by rewrite H'. }

    assert(
      st_h__local ∪ st_h__foreign ∪ (st'_h__local ∪ st'_h__foreign) =
      st_h__local ∪ (st_h__foreign ∪ filtered_out)).
    { rewrite -Hst_proj
        -(in_valid_gst__eq_proj_foreign
          (st'_h__local ∪ st'_h__foreign) g f Hv H1)
        Hst_proj -/filtered_out.
      apply set_eq. intros z. split.
      - intros [[?|?]%elem_of_union|?]%elem_of_union;
        [ by apply elem_of_union_l
        | by apply elem_of_union_r, elem_of_union_l
        | by do 2 apply elem_of_union_r].
      - intros [?|[?|?]%elem_of_union]%elem_of_union;
        [ by do 2 apply elem_of_union_l
        | by apply elem_of_union_l, elem_of_union_r
        | by apply elem_of_union_r]. }

    (** Uodate the resources *)
    iCombine "Hst_own__foreign" "Hst_own__foreign'" as "Hst_own__foreign".
    iDestruct (own_update _ _ ((1/2 + 1/2)%Qp, to_agree (st_h__foreign ∪ filtered_out))
      with "Hst_own__foreign")
      as ">[Hst_own__foreign Hst_own__foreign']";
      first by apply cmra_update_exclusive.

    iDestruct (own_update _ _
      (● princ_ev (st_h__local ∪ st_h__foreign ∪ filtered_out)
        ⋅ ◯ princ_ev (st_h__local ∪ st_h__foreign ∪ filtered_out))
      with "Hst_own__cc'")
      as ">[Hst_own__cc' #Hlocksnap]".
    { apply monotone_update; last done.
      split; first by apply union_subseteq_l'.
      assumption. }

    iMod ("Hclose"
      with "[Hothers
        Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc'
        Hg_ag Hg_auth]") as "_"; last iModIntro.
    { iNext.
       iExists (g.1,
        vinsert f (g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign)) g.2).
      iFrame. iFrame "%".
      iDestruct "Hothers" as "(%S & [%S_def %S_def'] & HS)".
      iDestruct (big_sepS_mono _
        (λ k, StLib_GlibInv_local_part k (g.1, vinsert f (g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign)) g.2))
        with "HS")
        as "HS".
      { iIntros (x Hx_in) "(%h_loc & %h_for & %h_sub & Hx)".
        iExists h_loc, h_for, h_sub. simpl.
        rewrite vlookup_insert_ne; last set_solver.
        iFrame. }
      iApply ((forall_fin' f)
        with "[HS Hst_own__local Hst_own__foreign Hst_own__sub Hst_own__cc Hst_own__cc']").
      iSplitL "HS"; first (by iExists S; iFrame).
      iExists st_h__local, (st_h__foreign ∪ filtered_out), st_h__sub.
      assert(st_h__local ∪ (st_h__foreign ∪ filtered_out)
        = st_h__local ∪ st_h__foreign ∪ filtered_out) as <-; first set_solver.
      iFrame. iFrame "%".
      iPureIntro.
      repeat split; try done.
      by rewrite vlookup_insert Hst_proj. }
    iExists f. by iFrame.
  Qed.

End Resources_updates.

