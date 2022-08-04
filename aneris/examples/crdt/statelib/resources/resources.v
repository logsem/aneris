From aneris.aneris_lang Require Import resources proofmode.
From iris.algebra Require Import auth csum excl agree.
From aneris.algebra Require Import monotone.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.examples.crdt.spec Require Import crdt_base crdt_time crdt_events crdt_resources.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.proof Require Import utils events.
From aneris.examples.crdt.statelib.STS Require Import gst.

Instance timetouse: Log_Time := timestamp_time.



Section RequiredRAs.
  Context `{!anerisG Mdl Σ, !CRDT_Params,
            CRDT_Op: Type, !EqDecision CRDT_Op, !Countable CRDT_Op}.

  Class Internal_StLibG Σ := mkInternalG {
      (* Global state, global snap and local state *)
      Int_StLibG_auth_gset_ev :> inG Σ (authUR (gsetUR (Event CRDT_Op)));
      (* Local state *)
      Int_StLibG_frac_agree :> inG Σ (prodR fracR (agreeR (gsetO (Event CRDT_Op))));
      (* Local state *)
      Int_StLibG_frac_agreeaeee :> inG Σ (agreeR (gsetO (Event CRDT_Op)));
      (* Local and global snapshots *)
      Int_StLibG_mono :> inG Σ (authUR (monotoneUR (@cc_subseteq CRDT_Op _ _)));
      (* Used to define the lock invariant (in the proof) *)
      Int_StLibG_lockG :> lockG Σ;
      Int_StLibG_frac_nat :> inG Σ (prodR fracR (agreeR natO))
    }.

  Class StLib_GhostNames := {
    γ_global: gname;
    γ_global_snap: gname;
    (** local gnames *)
    γ_loc_own: vec gname (length CRDT_Addresses);
    γ_loc_for: vec gname (length CRDT_Addresses);
    γ_loc_sub: vec gname (length CRDT_Addresses);
    γ_loc_cc : vec gname (length CRDT_Addresses);
  }.
End RequiredRAs.
Arguments Internal_StLibG (CRDT_Op) {_ _} (Σ).


Section Utils.
  Context `{CRDT_Op: Type,
            !anerisG Mdl Σ, !CRDT_Params,
            !EqDecision CRDT_Op, !Countable CRDT_Op,
            !StLib_GhostNames, !Internal_StLibG CRDT_Op Σ}.
  Notation princ_ev := (@principal (gset (Event CRDT_Op)) cc_subseteq).

  Lemma princ_ev__subset_cc h s γ :
    own γ (◯ princ_ev s) -∗
    own γ (● princ_ev h) -∗
    ⌜ s ⊆_cc h ⌝.
  Proof.
    iIntros "#Hfrag Hauth".
    iCombine "Hauth" "Hfrag" as "Hboth".
    iDestruct (own_valid with "Hboth") as "%Hvalid".
    apply auth_both_valid_discrete in Hvalid as [Hsub Hvalid].
    iPureIntro. by apply principal_included.
  Qed.

  Lemma princ_ev__union_frag_auth h s s' γ :
    own γ (◯ princ_ev s) -∗
    own γ (◯ princ_ev s') -∗
    own γ (● princ_ev h) ==∗
    own γ (● princ_ev h) ∗ own γ (◯ princ_ev (s ∪ s')).
  Proof.
    iIntros "#Hfrag #Hfrag' Hauth".
    iPoseProof (princ_ev__subset_cc with "Hfrag Hauth") as "%Hsubset".
    iPoseProof (princ_ev__subset_cc with "Hfrag' Hauth") as "%Hsubset'".
    assert (cc_subseteq (s ∪ s') h) as Hunion.
    { apply cc_subseteq_union; done. }
    iMod (own_update _ _ (● (princ_ev h) ⋅ ◯ (princ_ev (s ∪ s'))) with "Hauth") as "Hres".
    { eapply monotone_update; done. }
    iModIntro.
    by iApply own_op.
  Qed.

  Lemma forall_fin (f: fRepId) (P: fRepId → iProp Σ) :
    (∃ S : gset fRepId, (∀ r : fRepId, ⌜r ∈ S⌝) ∗
           ([∗ set] k ∈ S, P k))
    -∗
    ((∃ S : gset fRepId, (⌜ f ∉ S ⌝ ∗ ∀ r : fRepId, ⌜r ≠ f⌝ -∗ ⌜r ∈ S⌝) ∗ [∗ set] k ∈ S, P k)
      ∗ P f).
  Proof.
    iIntros "(%S & %Hdef_S & HS)".
    iApply bi.sep_exist_r.
    iExists ( S ∖ {[ f ]} ).
    iPoseProof (big_sepS_union _ ( S ∖ {[ f ]} ) {[f]}) as "[Hsep _]"; first set_solver.
    assert ((S ∖ {[f]} ∪ {[f]}) = S) as ->.
    { 
      assert (S ∪ {[f]} = S) as Heq.
      { assert (S ∪ {[f]} = {[f]} ∪ S) as ->; first set_solver.
        by apply subseteq_union_1_L, elem_of_subseteq. }
      pose proof (difference_union_L S {[f]}) as p.
      by rewrite Heq in p. }
    iDestruct ("Hsep" with "HS") as "[Hall Hone]".
    iSplitR "Hone";
      last by iApply big_sepS_singleton.
    iSplitR; [iPureIntro | iAssumption].
    set_solver.
  Qed.

  Lemma forall_fin' (f: fRepId) (P: fRepId → iProp Σ) :
    ((∃ S : gset fRepId, (⌜ f ∉ S ⌝ ∗ ∀ r : fRepId, ⌜r ≠ f⌝ -∗ ⌜r ∈ S⌝) ∗ [∗ set] k ∈ S, P k)
      ∗ P f)
    -∗
    (∃ S : gset fRepId, (∀ r : fRepId, ⌜r ∈ S⌝) ∗
           ([∗ set] k ∈ S, P k)).
  Proof.
    iIntros "[(%S & [%Hdef_S' %Hdef_S] & HS) Hone]".
    iExists ( S ∪ {[ f ]} ).
    iPoseProof (big_sepS_union _ S {[f]}) as "[_ Hsep]"; first set_solver.

    iDestruct ("Hsep" with "[HS Hone]") as "H".
    { iFrame. by iApply big_sepS_singleton. }
    iFrame.
    
    iPureIntro. intros r.
    destruct (decide (r = f)).
    - by apply elem_of_union_r, elem_of_singleton.
    - by apply elem_of_union_l, Hdef_S.
  Qed.

  Lemma both_agree_agree (γ: gname) (p q: Qp) (s s': event_set CRDT_Op):
    own γ (q, to_agree s) -∗ own γ (p, to_agree s') -∗
    own γ (q, to_agree s) ∗ own γ (p, to_agree s) ∗ ⌜ s = s' ⌝.
  Proof.
    iStartProof.
    iIntros "H1 H2".
    iCombine "H1" "H2" as "H".
    iDestruct (own_valid_l with "H") as "[%Hvalid [H1 H2]]".
    apply pair_valid in Hvalid as [_ ->%to_agree_op_inv_L].
    rewrite agree_idemp.
    by iFrame "H1 H2".
  Qed.

End Utils.
