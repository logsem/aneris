From aneris.aneris_lang Require Import lang resources.
From stdpp Require Import gmap.
From aneris.prelude Require Import misc gset_map.
From aneris.examples.crdt Require Import crdt_spec crdt_events crdt_time.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.time Require Import evtime time maximality.
From aneris.examples.crdt.statelib.STS Require Import lst.

Require Import Decidable.

Section Gst_definition.
  Context `{!anerisG Mdl Σ, !CRDT_Params}.
  Context `{Op: Type, !EqDecision Op, !Countable Op}.

  Definition Gst : Type :=
    (Lst Op) * vec (Lst Op) (length CRDT_Addresses).

  Definition fRepId : Type := fin (length CRDT_Addresses).

  Definition Gst_ghst_lhsts_coh (st: Gst) : Prop :=
    st.1 = ⋃ st.2.

  Definition Gst_incl_local (st: Gst) : Prop :=
    ∀ (ev: Event Op), ev ∈ st.1 ↔ ∃ i, ev ∈ st.2 !!! i.

  Definition Gst_incl_orig (st: Gst) : Prop :=
    ∀ (ev: Event Op), ev ∈ st.1 →
      ∃ (i: fin (length CRDT_Addresses)),
        fin_to_nat i = ev.(EV_Orig) ∧ ev ∈ st.2 !!! i.
  
  Definition Gst_hst_valid (st: Gst) : Prop :=
    Lst_Validity st.1.

  Definition Gst_lhst_valid (st: Gst) : Prop :=
    ∀ (i: fRepId), Lst_Validity (st.2 !!! i).

  Record Gst_Validity (ls: Gst) :=
    {
      VGst_incl_local : Gst_incl_local ls;
      VGst_incl_orig : Gst_incl_orig ls;
      VGst_hst_valid : Gst_hst_valid ls;
      VGst_lhst_valid : Gst_lhst_valid ls;
    }.

  Lemma VGst_ghst_lhsts_coh (ls : Gst) :
    Gst_Validity ls → Gst_ghst_lhsts_coh ls.
  Proof.
    intros [Horigin Hv Hvloc].
    apply set_eq. intros x. split; [intros Hx_in | intros (li & (i & <-)%elem_of_vlookup & Hx_in)%elem_of_union_list].
    - destruct (iffLR (Horigin x) Hx_in) as (i & Hx_in').
      apply elem_of_union_list. exists (ls.2 !!! i).
      split; last done.
      assert (i < length ls.2) as Hlen.
      { assert (length ls.2 = length CRDT_Addresses) as ->;
      first apply vec_to_list_length.
      apply fin_to_nat_lt. }
      apply elem_of_vlookup. by exists i.
    - apply (Horigin x). by exists i.
  Qed.

  Lemma gst_valid_inclusion (g: Gst) (i: fin (length CRDT_Addresses)):
    Gst_Validity g → ∀ ev, ev ∈ g.2 !!! i → ev ∈ g.1.
  Proof.
    intros Hv ev Hev_in.
    rewrite (VGst_ghst_lhsts_coh g Hv).
    apply elem_of_union_list. exists (g.2 !!! i).
    split ; [ apply elem_of_vlookup | assumption ].
    by exists i.
  Qed.

End Gst_definition.
Arguments Gst {_} (Op) {_ _}.


