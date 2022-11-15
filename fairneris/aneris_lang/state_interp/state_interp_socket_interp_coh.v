From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From fairneris.prelude Require Import misc.
From fairneris.lib Require Import gen_heap_light.
From fairneris.aneris_lang Require Import
     aneris_lang network resources.
From fairneris.aneris_lang.state_interp Require Import
     state_interp_def.
From fairneris.algebra Require Import disj_gsets.
From iris.algebra Require Import auth.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  (* socket_interp_coh *)
  Lemma socket_interp_coh_init C :
    socket_address_group_ctx C -∗
    unallocated_groups_auth C -∗
    saved_si_auth ∅ -∗
    socket_interp_coh.
  Proof.
    iIntros "Hsags Hunallocated Hsis".
    iExists _, _. iFrame. iSplit; [done|].
    rewrite difference_diag_L.
    iExists _.
    iFrame. iSplit; [by iPureIntro; set_solver|done].
  Qed.

  Lemma socket_interp_coh_allocate_singleton sag φ :
    socket_interp_coh -∗ unallocated_groups {[sag]} ==∗
    socket_interp_coh ∗ sag ⤇* φ.
  Proof.
    iIntros "Hinterp Hsag".
    iDestruct "Hinterp" as (sags A Hle) "(Hsags & Hunallocated & Hsis)".
    iAssert (⌜sag ∈ A⌝)%I as %Hin.
    { iDestruct (own_valid_2 with "Hunallocated Hsag") as %Hvalid.
      rewrite auth_both_valid_discrete in Hvalid.
      destruct Hvalid as [Hincluded Hvalid].
      rewrite gset_disj_included in Hincluded.
      iPureIntro. set_solver. }    
    iAssert (socket_address_group_own sag) as "#Hsag'".
    { rewrite /socket_address_group_own.
      iApply (socket_address_group_own_subseteq sags); [set_solver|].
      by iApply socket_address_groups_ctx_own. }    
    iMod (unallocated_update_dealloc with "[$Hunallocated $Hsag]") as "Hunallocated".
    iDestruct "Hsis" as (sis) "(Hsaved & %Hdom & Hsis)".
    iMod (socket_interp_alloc with "Hsag' Hsaved")
      as (γsi) "[Hsaved #Hsi]".
    { apply not_elem_of_dom. set_solver. }
    iModIntro. iFrame "#∗".
    iExists sags, (A ∖ {[sag]}).
    iSplit; [iPureIntro; set_solver|].
    iFrame. iExists _. iSplit; [done|].    
    iSplit; [iPureIntro|].
    { rewrite dom_insert_L.
      rewrite Hdom. rewrite difference_difference_union; set_solver. }
    rewrite difference_difference_union; [|set_solver].
    iApply big_sepS_union; [set_solver|].
    iFrame. iApply big_sepS_singleton.
    iExists _. iFrame "#".
  Qed.

  Lemma socket_interp_coh_allocate_fun sags f :
    socket_interp_coh -∗ unallocated_groups sags ==∗
    socket_interp_coh ∗ [∗ set] sag ∈ sags, sag ⤇* (f sag).
  Proof.
    iIntros "Hinterp Hsags".
    iInduction sags as [|sag sags Hnin] "IHsags" using set_ind_L; [by eauto|].
    iDestruct (unallocated_groups_split with "Hsags") as "[Hsag Hsags]";
      [set_solver|].
    rewrite big_sepS_union; [|set_solver].
    rewrite big_sepS_singleton.
    iMod ("IHsags" with "Hinterp Hsags") as "[Hinterp $]".
    iApply (socket_interp_coh_allocate_singleton with "Hinterp Hsag").
  Qed.

  Lemma socket_interp_coh_allocate sags φ :
    socket_interp_coh -∗ unallocated_groups sags ==∗
    socket_interp_coh ∗ [∗ set] sag ∈ sags, sag ⤇* φ.
  Proof. iApply socket_interp_coh_allocate_fun. Qed.

End state_interpretation.
