From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import proofmode.
From iris.base_logic Require Import invariants bi.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.

From aneris.examples.crdt.spec
  Require Import crdt_events crdt_resources crdt_denot crdt_time crdt_base.
From aneris.examples.crdt.statelib.resources
  Require Import resources_update resources utils resources_utils
    resources_inv resources_local resources_global resources_lock
    resources_allocation.

From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.user_model
  Require Import params model semi_join_lattices.
From aneris.examples.crdt.statelib.time Require Import time maximality.
From aneris.examples.crdt.statelib.STS
  Require Import utils gst lst mutation merge.
From aneris.examples.crdt.statelib.proof
  Require Import spec events utils
    stlib_proof_utils internal_specs stlib_proof.

Instance timeinst : Log_Time := timestamp_time.



Section StLibSetup.

  Context `{LogOp: Type, LogSt : Type,
            !anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !EventSetValidity LogOp, !StLib_Params LogOp LogSt,
            !Internal_StLibG LogOp Σ}.

  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  (* TODO: cleanup *)
  Ltac rewrite_lookup := repeat (
    match goal with
    | [ H1 : _ !! ?i = Some ?v1, H2 : _ !! ?i = Some ?v2 |- _ ] =>
          rewrite H1 in H2; inversion H2
    end); subst.

  (* The following lemma is inspired by the OpLib corresponding lemma *)
  Lemma stlib_setup E :
    True ⊢ |={E}=> ∃ (GNames : StLib_GhostNames),
      StLib_GlobalInv ∗
      StLib_OwnGlobalState ∅ ∗
      (∃ (S: gset (fin (length CRDT_Addresses))),
        (∀ i, ⌜i ∈ S⌝)
        ∗ [∗ set] f ∈ S, stlib_init_token f) ∗
      internal_init_spec.
  Proof.
    iIntros (_).
    iMod (alloc_loc_own with "[//]") as (γ_own) "(%S & %HS_def & HS_own0 & HS_own1 & HS_own2)".
    iMod (alloc_loc_for with "[//]") as (γ_for) "(%S' & %HS'_def & HS_for0 & HS_for1)".
      assert(S' = S) as ->; [ by apply set_eq | clear HS'_def ].
    iMod (alloc_loc_sub with "[//]") as (γ_sub) "(%S' & %HS'_def & HS_sub0 & HS_sub1)".
      assert(S' = S) as ->; [ by apply set_eq | clear HS'_def ].
    iMod (alloc_loc_cc  with "[//]") as (γ_cc)  "(%S' & %HS'_def & HS_cc_auth & #HS_cc_frag)".
      assert(S' = S) as ->; [ by apply set_eq | clear HS'_def ].
    iMod (alloc_loc_cc' with "[//]") as (γ_cc') "(%S' & %HS'_def & HS_cc'_auth & #HS_cc'_frag)".
      assert(S' = S) as ->; [ by apply set_eq | clear HS'_def ].
    iMod (alloc_global  with "[//]") as (γ_global) "[Hglobal Hglobal']".
    iMod (alloc_global_snap  with "[//]") as (γ_global_snap) "[Hglobal_snap_auth #Hglobal_snap_snap]".
    set HNames := (Build_StLib_GhostNames γ_global γ_global_snap γ_own γ_for γ_sub γ_cc γ_cc').
    iExists HNames.
    iMod (inv_alloc CRDT_InvName _ (StLib_GlobalInv_prop)
      with "[HS_own1 HS_for1 HS_sub1 HS_cc_auth HS_cc'_auth Hglobal' Hglobal_snap_auth]")
      as "#Hinv".
    { iNext. iExists (∅, vreplicate (length CRDT_Addresses) ∅).
      iFrame.
      iSplit; first (iPureIntro; apply gst_init_valid).
      iExists S; first iFrame"%".
      rewrite /StLib_GlibInv_local_part.
      iDestruct (big_sepS_sep_2 with "HS_own1 HS_for1") as "HS".
      iDestruct (big_sepS_sep_2 with "HS_sub1 HS") as "HS".
      iDestruct (big_sepS_sep_2 with "HS_cc_auth HS") as "HS".
      iDestruct (big_sepS_sep_2 with "HS_cc'_auth HS") as "HS".
      iApply (big_sepS_mono with "HS").
      iIntros (x Hx_in) "(H0 & H1 & H2 & H3 & H4)".
      repeat iExists ∅. rewrite union_empty_R. iFrame.
      iPureIntro.
      by split; first by rewrite vlookup_replicate. }
    iModIntro.
    iFrame "Hinv".

    iDestruct (internal_init_spec_holds with "Hinv") as "#Hinit".
    iFrame "#". iFrame "Hglobal".

    iExists S. iFrame "%".
    rewrite/stlib_init_token/locstate_tok/lockinv_tok.
    iDestruct (big_sepS_sep_2 with "HS_own0 HS_for0") as "HS".
    iDestruct (big_sepS_sep_2 with "HS_own2 HS") as "HS".
    iDestruct (big_sepS_sep_2 with "HS_sub0 HS") as "HS".
    iDestruct (big_sepS_sep_2 with "HS_cc_frag HS") as "HS".
    (*iDestruct (big_sepS_sep_2 with "HS_cc'_frag HS") as "HS".*)
    iApply (big_sepS_mono with "HS").
    iIntros (x Hx_in) "(H0 & H1 & H2 & H3 & H4)".
    iFrame.
  Qed.

End StLibSetup.

(** TODO: setup the library for aient to use:
  * From true, derive the existence of initial resources (using the above
  * section)
  * + init spec. *)

Section Instantiation.

  Context {LogOp LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !EventSetValidity LogOp, !StLib_Params LogOp LogSt,
            !Internal_StLibG LogOp Σ}.

  Global Instance init_fun_instance : StLib_Init_Function := {
    init := statelib_init
      StLib_StSerialization.(s_serializer).(s_ser)
      StLib_StSerialization.(s_serializer).(s_deser) }.

  Global Instance stlib_res_instance `{!StLib_GhostNames}
    : StLib_Res LogOp := {
      StLib_InitToken := stlib_init_token;
      StLib_SocketProto := socket_proto;
  }.

  Section EventSetValidity.

    Global Instance event_set_validity : EventSetValidity LogOp.
    Proof.
      refine {|
        event_set_valid := Lst_Validity ; |}.
      - intros s e e' Hv He_in He'_in Ht_eq.
        exact (VLst_same_orig_comp _ Hv e e' He_in He'_in Ht_eq).
      - by intros s [].
      - intros s e e' Hv He_in He'_in Hevid.
        exact (VLst_ext_eqid _ Hv e e' He_in He'_in Hevid).
      - intros s e e' Hv He_in He'_in Ht.
        exact (VLst_ext_time _ Hv e e' He_in He'_in Ht).
      - intros s e Hv He_in.
        exact (VLst_evid_incl_event _ Hv e He_in).
      - intros s s' Hv Hv' Hv'' i.
        destruct (decide ( fil ( s ∪ s' ) i = ∅ )) as [ | n ]; first (left; set_solver).
        epose proof (iffLR (compute_maximum_non_empty (fil (s ∪ s') i) _ _) n)
          as (m & [[Hm_orig [Hm_in|Hm_in]%elem_of_union]%elem_of_filter Hm_ismax]%compute_maximum_correct); last first.
        { intros??[_?]%elem_of_filter[_?]%elem_of_filter?.
          by apply (VLst_ext_time _ Hv''). }
        1: left. 2: right.
        all: intros x [Hx_orig Hx_in]%elem_of_filter.
        all: apply elem_of_filter; split; try assumption.
        all: destruct (decide (x = m)) as [ -> | ]; first assumption.
        all: assert (Hx: x ∈ fil (s ∪ s') i); first set_solver.
        all: pose proof (Hm_ismax x Hx n0).
        1: pose proof (VLst_evid_incl_event _ Hv x Hx_in).
        2: pose proof (VLst_evid_incl_event _ Hv' x Hx_in).
        all: assert (H2: get_evid x ∈ EV_Time m); first set_solver.
        + destruct (VLst_dep_closed _ Hv' m (get_evid x) Hm_in H2)
            as (x' & Hx'_in & Hx'_evid).
          by rewrite <-(VLst_ext_eqid _ Hv''
            x' x (elem_of_union_r x' s s' Hx'_in) (elem_of_union_l x s s' Hx_in)
            Hx'_evid).
        + destruct (VLst_dep_closed _ Hv m (get_evid x) Hm_in H2)
            as (x' & Hx'_in & Hx'_evid).
          by rewrite <-(VLst_ext_eqid _ Hv''
            x' x (elem_of_union_l x' s s' Hx'_in) (elem_of_union_r x s s' Hx_in)
            Hx'_evid).
      - trivial.
      Unshelve.
      all: intros x y [Hx_orig Hx_in]%elem_of_filter [Hy_orig Hy_in]%elem_of_filter.
      apply (VLst_same_orig_comp _ Hv'' _ _ Hx_in Hy_in).
      by rewrite Hx_orig Hy_orig.
      apply (VLst_ext_time _ Hv'' _ _ Hx_in Hy_in).
    Defined.

    Lemma Lst_Validity_implies_event_set_valid (s: Lst LogOp):
      Lst_Validity s → event_set_validity.(event_set_valid) s.
    Proof. trivial. Qed.

  End EventSetValidity.


  Global Instance stlib_setup_instance : StLibSetup.
  Proof.
    iIntros (E) "_".
    iMod (stlib_setup with "[//]") as (names) "(#Hinv & Hglob & Htoks & #Hinit)".
    iModIntro.
    iExists stlib_res_instance, event_set_validity.
    simpl.
    iFrame "Hinv Hglob Htoks Hinit".
  Qed.

End Instantiation.
