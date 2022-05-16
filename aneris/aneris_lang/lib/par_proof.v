From iris.algebra Require Import excl.
From aneris.prelude Require Import misc.
From iris.base_logic.lib Require Export invariants.
From aneris.aneris_lang Require Import proofmode.
From aneris.aneris_lang Require Import inject.
From aneris.aneris_lang.lib Require Export par_code.
From aneris.aneris_lang.lib Require Export spawn_proof.

(* Adapted directly from the heaplang proof. *)

Section proof.
  Context `{anerisG Mdl Σ, !spawnG Σ} (N : namespace).

  Local Set Default Proof Using "Type*".

  Definition parN : namespace := nroot .@ "par".


  (* Notice that this allows us to strip a later *after* the two Ψ have been
   brought together.  That is strictly stronger than first stripping a later
   and then merging them, as demonstrated by [tests/joining_existentials.v].
   This is why these are not Texan triples. *)
  Lemma par_spec ip (Ψ1 Ψ2 : val → iProp Σ) (f1 f2 : val) (Φ : val → iProp Σ) :
    WP f1 #() @[ip] {{ Ψ1 }} -∗ WP f2 #() @[ip] {{ Ψ2 }} -∗
    (▷ ∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1,v2)%V) -∗
    WP par f1 f2 @[ip] {{ Φ }}.
  Proof.
    iIntros "Hf1 Hf2 HΦ". wp_lam. wp_let.
    wp_apply (spawn_spec parN with "Hf1").
    iIntros (l) "Hl". wp_let. wp_bind (f2 _).
    wp_apply (aneris_wp_wand with "Hf2"); iIntros (v) "H2". wp_let.
    wp_apply (join_spec with "[$Hl]"). iIntros (w) "H1".
    iSpecialize ("HΦ" with "[$H1 $H2]"). by wp_pures.
  Qed.

  Lemma wp_par ip (Ψ1 Ψ2 : val → iProp Σ) (e1 e2 : expr) (Φ : val → iProp Σ) :
    WP e1 @[ip] {{ Ψ1 }} -∗ WP e2 @[ip] {{ Ψ2 }} -∗
    (∀ v1 v2, Ψ1 v1 ∗ Ψ2 v2 -∗ ▷ Φ (v1,v2)%V) -∗
    WP (e1 ||| e2)%V @[ip] {{ Φ }}.
  Proof.
    iIntros "H1 H2 H".
    wp_apply (par_spec ip Ψ1 Ψ2 with "[H1] [H2] [H]"); [by wp_lam..|auto].
  Qed.
End proof.
