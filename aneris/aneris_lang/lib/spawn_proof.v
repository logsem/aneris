From iris.algebra Require Import excl.
From aneris.prelude Require Import misc.
From iris.base_logic.lib Require Export invariants.
From aneris.aneris_lang Require Import proofmode.
From aneris.aneris_lang Require Import inject.
From aneris.aneris_lang.lib Require Export spawn_code.

(* Adapted directly from the heaplang proof. *)


(** The CMRA & functor we need. *)
Class spawnG Σ := SpawnG { spawn_tokG :> inG Σ (exclR unitO) }.
Definition spawnΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_spawnΣ {Σ} : subG spawnΣ Σ → spawnG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{anerisG Mdl Σ, !spawnG Σ} (N : namespace).

Definition spawn_inv  (ip : ip_address) (γ : gname) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ lv, l ↦[ip] lv ∗ (⌜lv = NONEV⌝ ∨
                  ∃ w, ⌜lv = SOMEV w⌝ ∗ (Ψ w ∨ own γ (Excl ()))).

Definition join_handle (ip : ip_address) (l : loc) (Ψ : val → iProp Σ) : iProp Σ :=
  ∃ γ, own γ (Excl ()) ∗ inv N (spawn_inv ip γ l Ψ).

Global Instance spawn_inv_ne ip n γ l :
  Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv ip γ l).
Proof. solve_proper. Qed.
Global Instance join_handle_ne ip n l :
  Proper (pointwise_relation val (dist n) ==> dist n) (join_handle ip l).
Proof. solve_proper. Qed.

(** The main proofs. *)
Lemma spawn_spec ip (Ψ : val → iProp Σ) (f : val) :
  {{{ WP f #() @[ip] {{ Ψ }} }}} spawn f @[ip] {{{ l, RET #l; join_handle ip l Ψ }}}.
Proof.
  iIntros (Φ) "Hf HΦ". rewrite /spawn /=. wp_lam.
  wp_alloc l as "Hl".
  iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
  iMod (inv_alloc N _ (spawn_inv ip γ l Ψ) with "[Hl]") as "#Hinv".
  { iNext. iExists NONEV. iFrame; eauto. }
  wp_pures.
  wp_bind (Fork _).
  iApply (aneris_wp_fork with "[-]").
  iSplitL "HΦ Hγ". iNext. wp_pures. iApply "HΦ". rewrite /join_handle. eauto.
  iNext. wp_pures. wp_bind (f _).
  iApply (aneris_wp_wand with "[$Hf]"). iIntros (v) "Hv".
  wp_inj. iInv N as (v') "[Hl _]".
  wp_store. iSplitL; last done. iIntros "!> !>". iExists (SOMEV v). iFrame. eauto.
Qed.

Lemma join_spec ip (Ψ : val → iProp Σ) l :
  {{{ join_handle ip l Ψ }}} join #l @[ip] {{{ v, RET v; Ψ v }}}.
Proof.
  iIntros (Φ) "H HΦ". iDestruct "H" as (γ) "[Hγ #?]".
  iLöb as "IH". wp_rec. wp_bind (! _)%E. iInv N as (v) "[Hl Hinv]".
  wp_load. iDestruct "Hinv" as "[%|Hinv]"; subst.
  - iModIntro. iSplitL "Hl"; [iNext; iExists _; iFrame; eauto|].
    wp_smart_apply ("IH" with "Hγ [HΦ]"). auto.
  - iDestruct "Hinv" as (v' ->) "[HΨ|Hγ']".
    + iModIntro. iSplitL "Hl Hγ"; [iNext; iExists _; iFrame; eauto|].
      wp_pures. by iApply "HΦ".
    + iDestruct (own_valid_2 with "Hγ Hγ'") as %[].
Qed.
End proof.

Typeclasses Opaque join_handle.
