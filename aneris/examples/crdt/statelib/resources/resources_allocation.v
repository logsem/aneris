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
  Require Import resources_update resources utils resources_utils
    resources_inv resources_local resources_global resources_lock.

From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.user_model
  Require Import params model semi_join_lattices.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS
  Require Import utils gst lst mutation merge.
From aneris.examples.crdt.statelib.proof
  Require Import spec events utils
    stlib_proof_utils internal_specs.



Section ResourcesInstantiationStandAlone.
  Context {LogOp : Type}.
  Context `{!EqDecision LogOp, !Countable LogOp, !Internal_StLibG LogOp Σ, !CRDT_Params}.
  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  Lemma alloc_global:
    True ==∗ ∃ γ,
      own γ ((2/3)%Qp, to_agree ∅)
      ∗ own γ ((1/3)%Qp, to_agree ∅).
  Proof.
    iIntros "_".
    iMod (own_alloc ((1/3 + 2/3)%Qp, to_agree ∅))
      as "(%γ & H1 & H2)";
      first done.
    iModIntro.
    iExists γ. iFrame.
  Qed.

  Lemma alloc_global_snap:
    True ==∗ ∃ γ,
      own γ (● ∅)
      ∗ own γ (◯ ∅).
  Proof.
    iIntros "_".
    iMod (own_alloc (● ∅ ⋅ ◯ ∅))
      as "(%γ & H1 & H2)";
      first by apply auth_both_valid.
    iModIntro.
    iExists γ. iFrame.
  Qed.
End ResourcesInstantiationStandAlone.



Section ResourcesInstantiationLists.
  Context {LogOp : Type}.
  Context `{!EqDecision LogOp, !Countable LogOp, !Internal_StLibG LogOp Σ, !CRDT_Params}.
  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  Lemma alloc_agree (n: nat) (q: Qp) (s: event_set LogOp):
    ⌜ q = 1%Qp ⌝ ==∗ ∃ (γ_list: list gname),
      ⌜length γ_list = n ⌝ ∗
      [∗ list] γ ∈ γ_list, own γ (q%Qp, to_agree s).
  Proof.
    iIntros "%Heq".
    iInduction n as [|n] "IHn".
    - iModIntro.
      iExists nil.
      by iSplit.
    - iMod "IHn".
      iDestruct ("IHn") as "(%γ_list & %γlist_len & Hsep)".
      iMod (own_alloc (q%Qp, to_agree s)) as (γ) "h"; first by rewrite Heq.
      iModIntro.
      iExists (γ :: γ_list).
      iSplit; first by rewrite -γlist_len.
      iApply big_sepL_cons.
      iFrame.
  Qed.

  Lemma alloc_cc n:
    True ==∗ ∃ (γ_list: list gname),
      ⌜length γ_list = n ⌝ ∗
      [∗ list] γ ∈ γ_list, own γ (● princ_ev ∅) ∗ own γ (◯ princ_ev ∅).
  Proof.
    iIntros "%Heq".
    iInduction n as [|n] "IHn".
    - iModIntro.
      iExists nil.
      by iSplit.
    - iMod "IHn".
      iDestruct ("IHn") as "(%γ_list & %γlist_len & Hsep)".
      iMod (own_alloc (● princ_ev ∅ ⋅ ◯ princ_ev ∅)) as (γ) "[H1 H2]";
        first by apply auth_both_valid.
      iModIntro.
      iExists (γ :: γ_list).
      iSplit; first by rewrite -γlist_len.
      iFrame.
  Qed.

  Lemma alloc_loc_cc_list:
    True ==∗ ∃ (γ_loc_cc_list: list gname),
      ⌜ length γ_loc_cc_list = length CRDT_Addresses ⌝
      ∗ [∗ list] γ ∈ γ_loc_cc_list, own γ (● princ_ev ∅) ∗ own γ (◯ princ_ev ∅).
  Proof.
    iIntros "_".
    iMod ((alloc_cc (length CRDT_Addresses)) with "[]") as "(%l & %Hlen & H)";
      first trivial.
    iModIntro.
    iExists l. by iFrame.
  Qed.

  (** This lemma is a copy of the precedent one. It is there nonetheless in case
   * the definitions attached to the vector γ_loc_cc' change. *)
  Lemma alloc_loc_cc'_list:
    True ==∗ ∃ (γ_loc_cc'_list: list gname),
      ⌜ length γ_loc_cc'_list = length CRDT_Addresses ⌝
      ∗ [∗ list] γ ∈ γ_loc_cc'_list, own γ (● princ_ev ∅) ∗ own γ (◯ princ_ev ∅).
  Proof.
    iIntros "_".
    iMod ((alloc_cc (length CRDT_Addresses)) with "[]") as "(%l & %Hlen & H)";
      first trivial.
    iModIntro.
    iExists l. by iFrame.
  Qed.
  
  Lemma alloc_loc_own_list:
    True ==∗ ∃ (γ_loc_own_list: list gname),
      ⌜ length γ_loc_own_list = length CRDT_Addresses ⌝
      ∗ ([∗ list] γ ∈ γ_loc_own_list, own γ ((1/3)%Qp, to_agree ∅))
      ∗ ([∗ list] γ ∈ γ_loc_own_list, own γ ((1/3)%Qp, to_agree ∅))
      ∗ ([∗ list] γ ∈ γ_loc_own_list, own γ ((1/3)%Qp, to_agree ∅)).
  Proof.
    iIntros "_".
    iMod ((alloc_agree (length CRDT_Addresses) (1/3 + 1/3 + 1/3)%Qp ∅)
      with "[]")
      as "(%lily & %Hlen & H)"; first (iPureIntro; compute_done).
    iModIntro. iExists lily. iSplit; first done.
    iDestruct ((big_sepL_mono _
      (λ _ γ, own γ ((1/3)%Qp, to_agree ∅)
        ∗ own γ ((1/3)%Qp, to_agree ∅)
        ∗ own γ ((1/3)%Qp, to_agree ∅))%I)
      with "H") as "H".
    { simpl. iIntros (k γ Hlily) "[[H1 H2] H3]". iFrame. }
    do 2 (iDestruct (big_sepL_sep with "H")
      as "[H1 H]"; iFrame).
  Qed.
  
  Lemma alloc_loc_sub_list:
    True ==∗ ∃ (γ_loc_sub_list: list gname),
      ⌜ length γ_loc_sub_list = length CRDT_Addresses ⌝
      ∗ ([∗ list] γ ∈ γ_loc_sub_list, own γ ((2/3)%Qp, to_agree ∅))
      ∗ ([∗ list] γ ∈ γ_loc_sub_list, own γ ((1/3)%Qp, to_agree ∅)).
  Proof.
    iIntros "_".
    iMod ((alloc_agree (length CRDT_Addresses) (2/3 + 1/3)%Qp ∅)
      with "[]")
      as "(%lily & %Hlen & H)"; first (iPureIntro; compute_done).
    iModIntro. iExists lily. iSplit; first done.
    iDestruct ((big_sepL_mono _
      (λ _ γ, own γ ((2/3)%Qp, to_agree ∅)
        ∗ own γ ((1/3)%Qp, to_agree ∅))%I)
      with "H") as "H".
    { simpl. iIntros (k γ Hlily) "[H1 H2]". iFrame. }
    iDestruct (big_sepL_sep with "H")
      as "[H1 H]"; iFrame.
  Qed.
  
  Lemma alloc_loc_for_list:
    True ==∗ ∃ (γ_loc_for_list: list gname),
      ⌜ length γ_loc_for_list = length CRDT_Addresses ⌝
      ∗ ([∗ list] γ ∈ γ_loc_for_list, own γ ((1/2)%Qp, to_agree ∅))
      ∗ ([∗ list] γ ∈ γ_loc_for_list, own γ ((1/2)%Qp, to_agree ∅)).
  Proof.
    iIntros "_".
    iMod ((alloc_agree (length CRDT_Addresses) (1/2 + 1/2)%Qp ∅)
      with "[]")
      as "(%lily & %Hlen & H)"; first (iPureIntro; compute_done).
    iModIntro. iExists lily. iSplit; first done.
    iDestruct ((big_sepL_mono _
      (λ _ γ, own γ ((1/2)%Qp, to_agree ∅)
        ∗ own γ ((1/2)%Qp, to_agree ∅))%I)
      with "H") as "H".
    { simpl. iIntros (k γ Hlily) "[H1 H2]". iFrame. }
    iDestruct (big_sepL_sep with "H")
      as "[H1 H]"; iFrame.
  Qed.


End ResourcesInstantiationLists.

Section ResourcesInstantiationVecs.
  Context {LogOp : Type}.
  Context `{!EqDecision LogOp, !Countable LogOp, !Internal_StLibG LogOp Σ, !CRDT_Params}.
  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  Lemma alloc_loc_cc:
    True ==∗ ∃ (γ_loc_cc_vec: vec gname (length CRDT_Addresses)),
      ∃ (S: gset (fin (length CRDT_Addresses))),
        ⌜ ∀ f, f ∈ S ⌝
        ∗ ([∗ set] f ∈ S, own (γ_loc_cc_vec !!! f) (● princ_ev ∅))
        ∗ ([∗ set] f ∈ S, own (γ_loc_cc_vec !!! f) (◯ princ_ev ∅)).
  Proof. Admitted.

  (** This lemma is a copy of the precedent one. It is there nonetheless in case
   * the definitions attached to the vector γ_loc_cc' change. *)
  Lemma alloc_loc_cc':
    True ==∗ ∃ (γ_loc_cc'_vec: vec gname (length CRDT_Addresses)),
      ∃ (S: gset (fin (length CRDT_Addresses))),
        ⌜ ∀ f, f ∈ S ⌝
        ∗ ([∗ set] f ∈ S, own (γ_loc_cc'_vec !!! f) (● princ_ev ∅))
        ∗ ([∗ set] f ∈ S, own (γ_loc_cc'_vec !!! f) (◯ princ_ev ∅)).
  Proof. exact alloc_loc_cc. Qed.

  Lemma alloc_loc_own:
    True ==∗ ∃ (γ_loc_own_vec: vec gname (length CRDT_Addresses)),
      ∃ (S: gset (fin (length CRDT_Addresses))),
        ⌜ ∀ f, f ∈ S ⌝
        ∗ ([∗ set] f ∈ S, own (γ_loc_own_vec !!! f) ((1/3)%Qp, to_agree ∅))
        ∗ ([∗ set] f ∈ S, own (γ_loc_own_vec !!! f) ((1/3)%Qp, to_agree ∅))
        ∗ ([∗ set] f ∈ S, own (γ_loc_own_vec !!! f) ((1/3)%Qp, to_agree ∅)).
  Proof. Admitted.

  Lemma alloc_loc_sub:
    True ==∗ ∃ (γ_loc_sub_vec: vec gname (length CRDT_Addresses)),
      ∃ (S: gset (fin (length CRDT_Addresses))),
        ⌜ ∀ f, f ∈ S ⌝
        ∗ ([∗ set] f ∈ S, own (γ_loc_sub_vec !!! f) ((2/3)%Qp, to_agree ∅))
        ∗ ([∗ set] f ∈ S, own (γ_loc_sub_vec !!! f) ((1/3)%Qp, to_agree ∅)).
  Proof. Admitted.

  Lemma alloc_loc_for:
    True ==∗ ∃ (γ_loc_for_vec: vec gname (length CRDT_Addresses)),
      ∃ (S: gset (fin (length CRDT_Addresses))),
        ⌜ ∀ f, f ∈ S ⌝
        ∗ ([∗ set] f ∈ S, own (γ_loc_for_vec !!! f) ((1/2)%Qp, to_agree ∅))
        ∗ ([∗ set] f ∈ S, own (γ_loc_for_vec !!! f) ((1/2)%Qp, to_agree ∅)).
  Proof. Admitted.

End ResourcesInstantiationVecs.

