From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc gset_map.
From aneris.examples.crdt Require Import crdt_spec crdt_events crdt_time.
From aneris.examples.crdt.statelib.time Require Import evtime time maximality.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.STS Require Import lst gst utils.

Section Gst_merge_local_valid.
  Context `{!anerisG Mdl Σ, !CRDT_Params}.
  Context `{Op: Type, !EqDecision Op, !Countable Op}.

  Lemma merge_dst_valid
    (g: Gst Op) (i j: fin (length CRDT_Addresses)) (s: event_set Op) :
    Gst_Validity g → s ⊆ g.2 !!! j → dep_closed s → Lst_Validity (g.2 !!! i ∪ s).
  Proof.
    intros Hv Hs Hs_dc.
    inversion Hv as [Hlocal Horig Hvloc Hldc].
    assert (Hs_incl: ∀ e, e ∈ s → e ∈ g.2 !!! j).
    { set_solver. }
    split.
    - destruct (Hldc i) as [Hdc _ _ _ _ _ _].
      destruct (Hldc j) as [Hdc' _ _ _ _ _ _].
      intros e eid [He_in | He_in]%elem_of_union Heid_in.
      + destruct (Hdc e eid He_in Heid_in) as (e' & He'_in & Heid_in').
        exists e'. by split; first apply elem_of_union_l.
      + destruct (Hs_dc e eid He_in Heid_in) as (e' & He'_in & Heid_in').
        exists e'.
        by split; first apply elem_of_union_r.
    - destruct (Hvloc) as [_ Hcomp _ _ _ _ _].
      intros e e'
        [He_in%(gst_valid_inclusion g _ Hv)
          | He_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union
        [He'_in%(gst_valid_inclusion g _ Hv)
          | He'_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union Heq_orig;
      by apply Hcomp.
    - intros e e'
        [He_in%(gst_valid_inclusion g _ Hv)
          | He_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union
        [He'_in%(gst_valid_inclusion g _ Hv)
          |He'_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union Heq_evid;
      destruct Hvloc as [_ _ Hlv _ _ _ _ _]; by apply Hlv.
    - intros e e'
        [He_in%(gst_valid_inclusion g _ Hv)
          | He_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union
        [He'_in%(gst_valid_inclusion g _ Hv)
          |He'_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union Heq_evid;
      destruct Hvloc as [_ _ _ Hlv _ _ _ _]; by apply Hlv.
    - intros e
        [He_in%(gst_valid_inclusion g _ Hv)
          | He_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union;
      destruct Hvloc as [_ _ _ _ H' _ _ _]; by apply H'.
    - intros e
        [He_in%(gst_valid_inclusion g _ Hv)
          | He_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union;
      destruct Hvloc as [_ _ _ _ _ H' _ _]; by apply H'.
    - intros ev [Hev_in | Hev_in]%elem_of_union rid sid Hevid_le;
        first by apply (VLst_orig_deps_seq (g.2 !!! i) (VGst_lhst_valid g Hv i)).
      apply (VLst_orig_deps_seq (g.2 !!! j) (VGst_lhst_valid g Hv j)); last assumption.
      by apply Hs_incl.
    - intros ev [Hev_in | Hev_in]%elem_of_union.
      + by apply (VLst_seqnum_non_O _ (VGst_lhst_valid _ Hv i)).
      + by apply (VLst_seqnum_non_O _ (VGst_lhst_valid _ Hv j)), Hs_incl.
    - intros rid Hrid.
      destruct (set_choose_or_empty (hproj rid (g.2 !!! i ∪ s)))
        as [(a & Ha) | <-]; last by left.
      right.
      pose proof (compute_maximals_non_empty Ha) as
        [elt
          [[Helt_orig Helt_in]%elem_of_filter
          Helt_max]%compute_maximals_correct]%set_choose_L.
      exists elt. split; first assumption.
      unfold compute_maximum.
      assert (compute_maximals (hproj rid (g.2 !!! i ∪ s)) = {[ elt ]})
        as Heq.
      { apply set_eq. intros x.
        split.
        - intros [[Hx_orig Hx_in]%elem_of_filter Hx_max]%compute_maximals_correct;
          apply elem_of_singleton.
          destruct (VLst_same_orig_comp g.1 Hvloc x elt) as [Hlt | [Heq | Hlt] ].
          + apply elem_of_union in Hx_in as [?|?];
            [by apply (gst_valid_inclusion g i)
              | by apply (gst_valid_inclusion g j), Hs_incl].
          + apply elem_of_union in Helt_in as [?|?];
            [by apply (gst_valid_inclusion g i)
              |by apply (gst_valid_inclusion g j), Hs_incl].
          + by rewrite Helt_orig Hx_orig.
          + exfalso.
            apply (Hx_max elt); last assumption.
            by apply elem_of_filter.
          + apply (VLst_ext_time g.1 Hvloc x elt); try done;
            [ apply elem_of_union in Hx_in as [?|?]
            | apply elem_of_union in Helt_in as [?|?] ].
            1, 3: by apply (gst_valid_inclusion g i).
            all: by apply (gst_valid_inclusion g j), Hs_incl.
          + exfalso.
            apply (Helt_max x); last assumption.
            by apply elem_of_filter.
        - intros<-%elem_of_singleton. apply compute_maximals_correct. split.
          + by apply elem_of_filter.
          + intros y Hy. by apply Helt_max. }
      by rewrite Heq elements_singleton.
    - intros e e'
        [He_in%(gst_valid_inclusion g _ Hv)
          | He_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union
        [He'_in%(gst_valid_inclusion g _ Hv)
          | He'_in%Hs_incl%(gst_valid_inclusion g _ Hv)]%elem_of_union;
      destruct Hvloc as [_ _ _ _ _ _ _ _ _ H']; by apply H'.
    - intros ev [Hev_in | Hev_in%(iffLR (elem_of_subseteq s (g.2 !!! j)) Hs_incl)]%elem_of_union.
      + by apply (VLst_evid_incl_event _ (VGst_lhst_valid g Hv i)).
      + by apply (VLst_evid_incl_event _ (VGst_lhst_valid g Hv j)).
   - intros x y [Hx_in | Hx_in%Hs_incl]%elem_of_union [Hy_in | Hy_in%Hs_incl]%elem_of_union.
    + by apply (VLst_evid_incl_time_le _ (VGst_lhst_valid _ Hv i)).
    + by apply (VLst_evid_incl_time_le _ (VGst_hst_valid _ Hv));
        [ apply gst_valid_inclusion with i
        | apply gst_valid_inclusion with j ].
    + by apply (VLst_evid_incl_time_le _ (VGst_hst_valid _ Hv));
        [ apply gst_valid_inclusion with j
        | apply gst_valid_inclusion with i ].
    + by apply (VLst_evid_incl_time_le _ (VGst_hst_valid _ Hv));
        [ apply gst_valid_inclusion with j
        | apply gst_valid_inclusion with j ].
  Qed.

  Lemma merge_loc_valid
    (g: Gst Op) (dst ext: fin (length CRDT_Addresses)) (s: event_set Op):
    Gst_Validity g →
    s ⊆ g.2 !!! ext → dep_closed s →
    Gst_lhst_valid (g.1, vinsert dst (g.2 !!! dst ∪ s) g.2).
  Proof.
    intros Hv Hs Hs_dc i.
    destruct (decide (i = dst)) as [-> | Hneq].
    - rewrite vlookup_insert. by apply merge_dst_valid with ext.
    - rewrite vlookup_insert_ne; last done.
      (** TODO: understand why this does not work: apply (Hv.(VGst_lhst_valid g)). *)
      exact (VGst_lhst_valid g Hv i).
  Qed.


  Lemma merge_global_valid
    (g: Gst Op) (dst ext: fin (length CRDT_Addresses)) (s: event_set Op):
    Gst_Validity g → s ⊆ g.2 !!! ext → dep_closed s →
    Gst_Validity (g.1, vinsert dst (g.2 !!! dst ∪ s) g.2).
  Proof.
    intros Hv Hs Hs_dc.
    split; [| | by destruct Hv | by apply merge_loc_valid with ext]; last first.
    { simpl. intros e He_in.
      destruct (VGst_incl_orig g Hv e He_in) as (i & Hi & He_in').
      exists i. split; first assumption.
      destruct (decide (dst = i)) as [-> | Hneq]; last by rewrite vlookup_insert_ne.
      rewrite vlookup_insert.
      by apply elem_of_union_l. }
    intros ev; split.
    - intros Hev_in; simpl in *.
      rewrite (VGst_ghst_lhsts_coh g Hv) in Hev_in.
      apply elem_of_union_list in Hev_in as (li & Hli_in & Hev_in).
      apply elem_of_vlookup in Hli_in as [i <-].
      exists i.
      destruct (decide (dst = i)) as [-> | Hneq].
      + rewrite vlookup_insert. by apply elem_of_union_l.
      + by rewrite vlookup_insert_ne ; last assumption.
    - intros [i Hev_in].
      rewrite (VGst_ghst_lhsts_coh g Hv).
      apply elem_of_union_list.
      destruct (decide (dst = i)) as [-> | Hneq];
      [rewrite vlookup_insert in Hev_in
        | rewrite vlookup_insert_ne in Hev_in]; last assumption.
      + by apply elem_of_union in Hev_in as [Hev_in|Hev_in];
          [exists (g.2 !!! i) | exists (g.2 !!! ext) ]; split; try done;
        [ apply elem_of_vlookup; by exists i
        | apply elem_of_vlookup; by exists ext
        | apply elem_of_subseteq with s ].
      + exists (g.2 !!! i). split; try done.
        apply elem_of_vlookup. by exists i.
  Qed.
End Gst_merge_local_valid.
