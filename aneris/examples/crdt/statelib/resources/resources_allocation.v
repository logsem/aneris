From stdpp Require Import gmap finite.

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

  Lemma conv_list_vec {A} n (l: list A) (R: A → iProp Σ) :
      ([∗ list] k ∈ l, R k) -∗
      [∗ set] i ∈ (Sn n),
        let j := fin_to_nat i in
        match decide (j < (length l))%nat with
        | left Hlt =>
         R ((Vector.of_list l) !!! (nat_to_fin Hlt))
        | right _ => True
        end.
  Proof.
    iInduction l as [|h t] "IHl" using rev_ind forall (n).
    - iIntros "_".
      iInduction (Sn n) as [] "H" using set_ind_L; first done.
      iApply big_sepS_union; first set_solver.
      iFrame "H".
      by iApply big_sepS_singleton.
    - iIntros "[Ht [Hh _]]".
      iDestruct ("IHl" $! n with "Ht") as "H".
      iAssert([∗ set] i ∈ (Sn n), match decide (fin_to_nat i = length t)%nat with
                      | left Heq => R h
                      | right _ => True
                      end)%I with "[Hh]" as "H1".
      { destruct (decide (length t < n)%nat) as [Hlt | Hnlt].
        - iApply ((big_sepS_delete_2 (nat_to_fin Hlt)) with "[Hh]").
          by destruct (decide); iFrame.
          iApply big_sepS_intro. iIntros "!> %x %Hx_in".
          rewrite decide_False; first done.
          replace (length t) with (fin_to_nat (nat_to_fin Hlt));
            first set_solver.
          apply fin_to_nat_to_fin.
        - iApply big_sepS_intro. iIntros "!> %x %Hx_in".
          rewrite decide_False; first done.
          intros Hx_eq. rewrite -Hx_eq in Hnlt.
          by pose (fin_to_nat_lt x). }
      iDestruct (big_sepS_sep_2 with "H H1") as "H".
      iApply (big_sepS_mono with "H").
      iIntros (x Hx_in) "[H H']".
      destruct decide.
      + destruct (decide (x < _)%nat); last trivial.
        assert(list_to_vec t !!! nat_to_fin l
          = list_to_vec (t ++ [h]) !!! nat_to_fin l0) as ->; last by iFrame.
        symmetry. rewrite vlookup_lookup.
        rewrite !vec_to_list_to_vec.
        rewrite lookup_app_l; last by rewrite fin_to_nat_to_fin.
        destruct (lookup_lt_is_Some_2 t (fin_to_nat (nat_to_fin l0))) as [a Ha];
          first by rewrite fin_to_nat_to_fin.
        rewrite Ha.
        f_equal.
        symmetry.
        by rewrite vlookup_lookup -Ha !fin_to_nat_to_fin vec_to_list_to_vec.
      + destruct (decide (_ < _)%nat); last done.
        pose proof l as l'.
        rewrite app_length in l'.
        simpl in *.
        assert(x = length t:>nat) as ?; first lia.
        rewrite decide_True; last assumption.
        assert(list_to_vec (t ++ [h]) !!! nat_to_fin l = h) as ->; last done.
        rewrite vlookup_lookup.
        rewrite !vec_to_list_to_vec.
        rewrite fin_to_nat_to_fin H0.
        rewrite lookup_app_r; last done.
        by rewrite Nat.sub_diag.
  Qed.

  Lemma conv_list_vec' {A} (l: list A) (R: A → iProp Σ) :
    ([∗ list] k ∈ l, R k) -∗
      [∗ set] i ∈ (Sn (length l)), R ((Vector.of_list l) !!! i).
  Proof.
    iIntros "Hl".
    iDestruct (conv_list_vec with "Hl") as "H".
    iApply (big_sepS_mono with "H").
    iIntros (x Hx_in) "H".
    destruct decide as [Hlt | Hnlt]; last first.
    { destruct Hnlt. apply fin_to_nat_lt. }
    assert(list_to_vec l !!! x = list_to_vec l !!! nat_to_fin Hlt) as ->;
      [ by rewrite nat_to_fin_to_nat | iFrame ].
  Qed.

  Lemma alloc_loc_cc:
    True ==∗ ∃ (γ_loc_cc_vec: vec gname (length CRDT_Addresses)),
        ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_cc_vec !!! f) (● princ_ev ∅))
        ∗ ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_cc_vec !!! f) (◯ princ_ev ∅)).
  Proof.
    iIntros (_). 
    iMod (alloc_loc_cc_list with "[//]") as "(%l & %Hlen & Hl)".
    iModIntro.
    iDestruct (conv_list_vec' with "Hl") as "HS".
    repeat rewrite -Hlen.
    iExists (list_to_vec l).
    iApply big_sepS_sep. iFrame.
  Qed.

  (** This lemma is a copy of the precedent one. It is there nonetheless in case
   * the definitions attached to the vector γ_loc_cc' change. *)
  Lemma alloc_loc_cc':
    True ==∗ ∃ (γ_loc_cc'_vec: vec gname (length CRDT_Addresses)),
        ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_cc'_vec !!! f) (● princ_ev ∅))
        ∗ ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_cc'_vec !!! f) (◯ princ_ev ∅)).
  Proof. exact alloc_loc_cc. Qed.

  Lemma alloc_loc_own:
    True ==∗ ∃ (γ_loc_own_vec: vec gname (length CRDT_Addresses)),
        ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_own_vec !!! f) ((1/3)%Qp, to_agree ∅))
        ∗ ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_own_vec !!! f) ((1/3)%Qp, to_agree ∅))
        ∗ ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_own_vec !!! f) ((1/3)%Qp, to_agree ∅)).
  Proof.
    iIntros (_). 
    iMod (alloc_loc_own_list with "[//]") as "(%l & %Hlen & Hl0 & Hl1 & Hl2)".
    iModIntro. repeat rewrite -Hlen.
    iDestruct (conv_list_vec' with "Hl0") as "HS0".
    iDestruct (conv_list_vec' with "Hl1") as "HS1".
    iDestruct (conv_list_vec' with "Hl2") as "HS2".
    iExists (list_to_vec l).
    iFrame.
  Qed.

  Lemma alloc_loc_sub:
    True ==∗ ∃ (γ_loc_sub_vec: vec gname (length CRDT_Addresses)),
        ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_sub_vec !!! f) ((2/3)%Qp, to_agree ∅))
        ∗ ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_sub_vec !!! f) ((1/3)%Qp, to_agree ∅)).
  Proof.
    iIntros (_). 
    iMod (alloc_loc_sub_list with "[//]") as "(%l & %Hlen & Hl0 & Hl1)".
    iModIntro. repeat rewrite -Hlen.
    iDestruct (conv_list_vec' with "Hl0") as "HS0".
    iDestruct (conv_list_vec' with "Hl1") as "HS1".
    iExists (list_to_vec l).
    iFrame.
  Qed.

  Lemma alloc_loc_for:
    True ==∗ ∃ (γ_loc_for_vec: vec gname (length CRDT_Addresses)),
        ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_for_vec !!! f) ((1/2)%Qp, to_agree ∅))
        ∗ ([∗ set] f ∈ (Sn (length CRDT_Addresses)), own (γ_loc_for_vec !!! f) ((1/2)%Qp, to_agree ∅)).
  Proof.
    iIntros (_). 
    iMod (alloc_loc_for_list with "[//]") as "(%l & %Hlen & Hl0 & Hl1)".
    iModIntro. repeat rewrite -Hlen.
    iDestruct (conv_list_vec' with "Hl0") as "HS0".
    iDestruct (conv_list_vec' with "Hl1") as "HS1".
    iExists (list_to_vec l).
    iFrame.
  Qed.

End ResourcesInstantiationVecs.

