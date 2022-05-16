From iris.algebra Require Import agree auth excl gmap.
From aneris.aneris_lang Require Import resources.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.algebra Require Import monotone.
From iris.base_logic Require Import invariants.
From aneris.prelude Require Export time.
From aneris.examples.ccddb.model Require Import events.

(** Modular specification for causal memory
    vector-clock based implementation. *)

Definition seen_relation : relation (gset apply_event) :=
  λ s s', s ⊆ s' ∧
          ∀ ae ae',
            ae ∈ s' → ae' ∈ s' →
            vector_clock_lt (ae_time ae) (ae_time ae') → ae' ∈ s → ae ∈ s.

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

Class internal_DBG Σ := {
  IDBG_Global_mem_excl :>
    inG Σ (authUR (gmapUR Key (exclR (gsetO write_event))));
  IDBG_Global_mem_mono :> inG Σ (authUR (gmapUR Key (gsetUR write_event)));
  IDBG_local_history_mono :> inG Σ (authUR (monotoneUR seen_relation));
  IDBG_local_history_gset :> inG Σ (authUR (gsetUR apply_event));
  IDBG_lockG :> lockG Σ;
}.
