From iris.algebra Require Import agree auth excl gmap cmra.
From aneris.aneris_lang Require Import resources.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.algebra Require Import monotone.
From iris.base_logic Require Import invariants.
From aneris.prelude Require Export time.
From aneris.examples.rcb.model Require Import events.

(** Modular specification for causal memory
    vector-clock based implementation. *)

Definition seen_relation : relation (gset local_event) :=
  λ s s', s ⊆ s' ∧
          ∀ ae ae',
            ae ∈ s' → ae' ∈ s' →
            vector_clock_lt (le_time ae) (le_time ae') → ae' ∈ s → ae ∈ s.

Global Instance seen_relation_partial_order : PartialOrder seen_relation.
Proof.
  split.
  - split.
    + rewrite /Reflexive /seen_relation. set_solver.
    + rewrite /Transitive /seen_relation. set_solver.
  - rewrite /AntiSymm /seen_relation. set_solver.
Qed.

Lemma seen_relation_union s1 s2 s :
  seen_relation s1 s → seen_relation s2 s → seen_relation (s1 ∪ s2) s.
Proof. intros [Hs11 Hs12] [Hs21 Hs22]; split; set_solver. Qed.

Class internal_RCBG Σ := InternalRCBG {
  IRCBG_global_history_excl :> inG Σ (prodR fracR (agreeR (gsetO global_event)));
  IRCBG_global_history_pers :> inG Σ (authUR (gsetUR global_event));
  IRCBG_local_history_excl :> inG Σ (prodR fracR (agreeR (gsetO local_event)));
  IRCBG_lockG :> lockG Σ;
}.

(* Utility lemmas *)
Section utility.

  Context {T : cmra}.

  Lemma frac_pair_valid_implies_false (p q : Qp) (a1 a2 : T) :
    ✓ ((p, a1) ⋅ (q, a2)) ->
    (1 < p + q)%Qp ->
    False.
  Proof.
    intros Hv Hlt.
    rewrite -pair_op frac_op in Hv.
    apply (iffLR (pair_valid _ _)) in Hv as [Hl _].
    apply (iffLR (frac_valid _)) in Hl.
    pose proof (Qp.lt_le_trans _ _ _ Hlt Hl) as Hc.
    by eapply (irreflexivity Qp.lt).
  Qed.

End utility.

