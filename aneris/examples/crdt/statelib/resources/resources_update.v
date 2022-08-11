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



Section Resources_updates.

  Context `{LogOp: Type, LogSt : Type,
            !anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt,
            !Internal_StLibG LogOp Σ, !StLib_GhostNames}.

  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  Lemma merge_update
    E
    (repId: RepId) (remote_f: fRepId)
    (st_h__local st_h__foreign st'_h__local st'_h__foreign: Lst LogOp) :
    ⌜↑CRDT_InvName ⊆ E⌝ -∗
    StLib_GlobalInv -∗
    OwnLockInv repId st_h__local st_h__foreign -∗
    StLib_OwnLocalSnap remote_f st'_h__local st'_h__foreign
      ={E, E}=∗
      OwnLockInv repId
        st_h__local
        (st_h__foreign
          ∪ (filter (λ e, EV_Orig e ≠ repId) (st'_h__local ∪ st'_h__foreign)))
      ∗
        ⌜ st_h__local ∪ (st_h__foreign
          ∪ filter (λ e : Event LogOp, EV_Orig e ≠ repId)
            (st'_h__local ∪ st'_h__foreign))
          = st_h__local ∪ st_h__foreign ∪ (st'_h__local ∪ st'_h__foreign) ⌝.
  Proof.
    iIntros (Hincl)
      "#Hinv Hown_lock (%remote_f' & %Hremote_f_eq &
      %Hremote_local & %Hremote_foreign & #Hst'_own_cc)".
    assert (remote_f' = remote_f) as ->;
      first by apply fin_to_nat_inj.

    iInv "Hinv" as "> (%g & Hown_global & Hown_global_snap & %Hv & HS)" "Hclose".
    
    (* *** α) from HS:
     *       → st'__h__local ∪ st'_h__foreign ⊆_cc g.2 !!! (f_remote)
     *       → h__local ∪ h__foreign = g.2 !!! f
     *
     * *** β) from STS:
     *       → updated g is valid (Gst-wise)
     *       → filter (not from f) (st'_h__local ∪ st'_h__foreign)
     *           ⊆_cc h__local ∪ h__foreign
     * NB: remember that
     *     the updated version of g.2 !!! f
     *     is equal to (h__local ∪ h_foreign ∪ st'_h__local ∪ st'_h__foreign)
     *
     * *** γ) Actual resource update:
     *       → resources:  only affects h__foreign
     *       → properties: affects both GlobInv and OwnLock
     *)
    iDestruct ((forall_fin remote_f) with "HS")
      as "[(%T & [%HT_nin%HT_def] & HT_res)
        (%st'_h__local' & %st'_h__foreign' & %st'_h__sub' & %Hremote_proj &
        %Hst'_local' & %Hst'_foreign' & %Hst'_sub' & %Hst'_cc' &
        Hremote_own_local' & Hremote_own_foreign' & Hremote_own_sub' &
        Hremote_own_cc')]".
    iAssert (
      own (γ_loc_cc !!! remote_f) (● princ_ev (st'_h__local' ∪ st'_h__sub'))
      ∗ ⌜st'_h__local ∪ st'_h__foreign ⊆_cc g.2 !!! remote_f⌝)%I
      with "[Hremote_own_cc' Hst'_own_cc]"
      as "[Hremote_own_cc' [%Hst'_subset%Hst'_depclosed]]".
    { rewrite Hremote_proj.
      iDestruct (princ_ev__subset_cc' with "Hst'_own_cc Hremote_own_cc'")
        as "[Hremote_onw_cc %Hcc]".
      iFrame. iPureIntro.
      destruct Hst'_cc' as [Hsub' Hcc']. destruct Hcc as [Hsub Hcc].
      split.
      - intros x Hx_in%Hsub. by apply Hsub'.
      - intros x y Hx_in Hy_in Hxy_le Hy_in''.
        (** TODO: use the transitivity uf ⊆_cc instead. *)
        assert (Hy_in': y ∈ st'_h__local' ∪ st'_h__sub');
          first by apply Hsub in Hy_in''.
        by apply (Hcc x y (Hcc' x y Hx_in Hy_in Hxy_le Hy_in')). }

    iDestruct ((forall_fin' remote_f)
      with "[HT_res Hremote_own_local' Hremote_own_foreign' Hremote_own_sub'
        Hremote_own_cc']")
      as "HS".
    { iSplitL "HT_res".
      - iExists T. by iFrame "HT_res".
      - simpl.
        iExists st'_h__local', st'_h__foreign', st'_h__sub'. by iFrame. }
    clear T HT_nin HT_def.

    iDestruct "Hown_lock" as "(%f & %Hf & %Hloc & %Hfor & Hown_local & Hown_for)".
    iDestruct ((forall_fin f) with "HS")
      as "[(%T & [%HT_nin%HT_def] & HT_res)
        (%h__local & %h__foreign & %st_h__sub &
        %Hf_proj & %Hst_local & %Hst_foreign & %Hst_sub & %Hst_cc &
        Hf_own_local & Hf_own_foreign & Hf_own_sub & Hf_own_cc)]".
    (** unification of the names of local and foreign histories on repId *)
    iDestruct (both_agree_agree with "Hown_local Hf_own_local")
      as "(Hown_local & Hf_own_local & <-)".
    iDestruct (both_agree_agree with "Hown_for Hf_own_foreign")
      as "(Hown_for & Hf_own_foreign & <-)".

    (** A few assertions on the new state wrt. equality and subseteq. *)
    assert (H1in:
      filter (λ e, EV_Orig e = f) (st'_h__local ∪ st'_h__foreign)
        ⊆ g.2 !!! f).
    { intros e [He_orig He_in%Hst'_subset%gst_valid_inclusion]%elem_of_filter;  
        last exact Hv.
      destruct (VGst_incl_orig _ Hv e He_in) as (i & Hi & Hiin).
      assert (f = i) as ->.
      { apply fin_to_nat_inj. by rewrite Hi He_orig. }
      assumption. }
    assert (Heq:
      st_h__local ∪ (st_h__foreign
        ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
          (st'_h__local ∪ st'_h__foreign))
        = st_h__local ∪ st_h__foreign ∪ (st'_h__local ∪ st'_h__foreign)).
    { pose (filter_union_complement
        (λ e, EV_Orig e = f) (st'_h__local ∪ st'_h__foreign))
        as Hpartition.
      apply set_eq. intros x. split.
      - intros [?|[?|[_?]%elem_of_filter]%elem_of_union]%elem_of_union;
        [ by apply elem_of_union_l, elem_of_union_l
        | by apply elem_of_union_l, elem_of_union_r
        | by apply elem_of_union_r].
      - intros [[?|?]%elem_of_union | [Hx_in%H1in|?]%Hpartition%elem_of_union]%elem_of_union;
          [ by apply elem_of_union_l
          | by apply elem_of_union_r, elem_of_union_l
          | rewrite Hf_proj in Hx_in
          |by apply elem_of_union_r, elem_of_union_r].
        apply elem_of_union in Hx_in as [?|?];
          [ by apply elem_of_union_l
          | by apply elem_of_union_r, elem_of_union_l]. }

    assert(
      g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign) =
      g.2 !!! f
        ∪ filter
            (λ e : Event LogOp, EV_Orig e ≠ f)
            (st'_h__local ∪ st'_h__foreign)).
    { pose (filter_union_complement
        (λ e, EV_Orig e = f) (st'_h__local ∪ st'_h__foreign))
        as Hpartition.
      apply set_eq.
      intros x. split.
      - intros [?|[?%H1in|?]%Hpartition%elem_of_union]%elem_of_union;
          [by apply elem_of_union_l 
          | by apply elem_of_union_l
          | by apply elem_of_union_r].
      - intros [?|[_?]%elem_of_filter]%elem_of_union;
        [ by apply elem_of_union_l
        | by apply elem_of_union_r ]. }
    assert(
      foreign_events f
        (st_h__foreign
         ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
             (st'_h__local ∪ st'_h__foreign)));
      first by intros e
        [He_in%Hst_foreign | [He_norig _]%elem_of_filter]%elem_of_union.
    assert(
      st_h__local ∪ st_h__sub
      ⊆_cc g.2 !!! f
        ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__foreign)).
    { split. destruct Hst_cc as [Hsubset Hcc].
      - intros e He_in%Hsubset. rewrite Hf_proj.
        by apply elem_of_union_l.
      - destruct Hst_cc as [Hst_subset Hst_depclosed].
        pose (VLst_dep_closed _ (VGst_lhst_valid _ Hv f)) as Hst_dc.
        intros x y
          [ Hx_in | Hx_in ]%elem_of_union [ Hy_in | Hy_in ]%elem_of_union
          Hxy_le Hy_in'.
        + apply (Hst_depclosed x y); try done;
            [by rewrite -Hf_proj | by apply Hst_subset].
        + apply (Hst_depclosed x y); try done;
            [by rewrite -Hf_proj | by apply Hst_subset].
        + apply (Hst_depclosed x y); try done;
            [ | by apply Hst_subset].
          destruct (Hst_dc y (get_evid x) Hy_in) as (z & Hz_in & Hz_evid).
          { admit. }
          rewrite Hf_proj in Hz_in.
          assert (x = z) as ->; last done.
          { apply (VLst_ext_eqid _ (VGst_hst_valid _ Hv) x z); last done.
            - apply gst_valid_inclusion with remote_f; first assumption.
              apply elem_of_filter in Hx_in as [_ Hx_in].
              rewrite Hremote_proj.
              admit.
            - by apply gst_valid_inclusion with f; last rewrite Hf_proj. }
        + apply (Hst_depclosed x y); try done;
            [ | by apply Hst_subset].
          admit. }

    iApply fupd_frame_r.
    iSplit; last by rewrite -Hf.
    iExists f. iFrame "%".

    assert(Hdc: dep_closed (st'_h__local ∪ st'_h__foreign)).
    { intros x e Hx_in He_in.
      apply Hst'_subset in Hx_in as Hx_in'.
      destruct (VLst_dep_closed _ (VGst_lhst_valid _ Hv remote_f) x e Hx_in' He_in)
        as (e' & He'_in & He_eid).
      exists e'. split; last by rewrite He_eid.
      apply (Hst'_depclosed e' x He'_in Hx_in'); last assumption.
      admit. }
    pose (merge_global_valid g f remote_f (st'_h__local ∪ st'_h__foreign)
      Hv Hst'_subset Hdc) as Hv'.

    iDestruct (own_update_2 (γ_loc_for !!! f) (½, to_agree st_h__foreign) (½, to_agree st_h__foreign)
      (((1/2)%Qp, to_agree (st_h__foreign ∪ (filter (λ e, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__foreign))))
      ⋅ ((1/2)%Qp, to_agree (st_h__foreign ∪ (filter (λ e, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__foreign)))))
      with "Hf_own_foreign Hown_for")
      as "> [Hf_own_foreign Hown_for]".
    { do 2 rewrite -pair_op frac_op Qp_half_half agree_idemp.
        by apply cmra_update_exclusive. }

    iDestruct ((big_sepS_mono
      (λ k, StLib_GlibInv_local_part k g) (λ k, StLib_GlibInv_local_part k (g.1, vinsert f (g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign)) g.2)))
      with "[$HT_res]") as "HT_res".
    { iIntros (x Hx_in) "(%hloc & %hfor & %hsub & %Hproj & Hreste)".
      iExists hloc, hfor, hsub. iFrame.
      rewrite vlookup_insert_ne; first done.
      intros Heq'. rewrite -Heq' in Hx_in. by destruct HT_nin. }

    iDestruct ((forall_fin' f)
      with "[HT_res Hf_own_local Hf_own_foreign Hf_own_sub Hf_own_cc]")
      as "HS".
    { iSplitL "HT_res".
      - iExists T. by iFrame "HT_res".
      - simpl.
        iExists
          st_h__local,
          (st_h__foreign
            ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
                (st'_h__local ∪ st'_h__foreign)),
          st_h__sub.
        replace (
          st_h__local
          ∪ (st_h__foreign
            ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
                (st'_h__local ∪ st'_h__foreign)))
          with
            (g.2 !!! f
              ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
                  (st'_h__local ∪ st'_h__foreign)); last first.
        { rewrite Hf_proj. symmetry.
          rewrite Heq.
          pose (filter_union_complement
            (λ e, EV_Orig e = f) (st'_h__local ∪ st'_h__foreign))
            as Hpartition.
          apply set_eq. intros x. split.
          - intros [[?|?]%elem_of_union|[?%H1in|Hx_in]%Hpartition%elem_of_union]%elem_of_union;
              [ by do 2 apply elem_of_union_l
              | by apply elem_of_union_l, elem_of_union_r
              | apply elem_of_union_l; by rewrite -Hf_proj
              | by apply elem_of_union_r].
          - intros [[?|?]%elem_of_union | [_?]%elem_of_filter]%elem_of_union;
            [ by do 2 apply elem_of_union_l
            | by apply elem_of_union_l, elem_of_union_r
            | by apply  elem_of_union_r]. }
        iFrame. iFrame "%".
        by rewrite /= vlookup_insert. }
    clear T HT_nin HT_def.
    iMod ("Hclose" with "[HS Hown_global Hown_global_snap]") as "_"; last iModIntro.
    { iNext.
      iExists (g.1, vinsert f (g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign)) g.2).
      iFrame "%". simpl. iFrame. }
    iFrame "Hown_local".
    iSplit.
    { iPureIntro.
      intros ev [Hev_in%Hst_foreign | [Hev_f _]%elem_of_filter]%elem_of_union;
        [ by rewrite -Hf | done]. }
    by rewrite Hf.
  Admitted.

End Resources_updates.
