From iris Require Import invariants.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction.
From aneris.aneris_lang Require Import lang tactics proofmode.
From aneris.aneris_lang.lib Require Import lock_proof.
From aneris.aneris_lang.lib Require Export bag_code.

Section spec.
  Context `{!anerisG Mdl Σ, !lockG Σ}.

  Local Notation iProp := (iProp Σ).

  Fixpoint bagList (Ψ : val → iProp) (v : val) : iProp :=
    match v with
    | NONEV => ⌜True⌝%I
    | SOMEV (x, r) => (Ψ x ∗ bagList Ψ r)%I
    | _ => ⌜False⌝%I
    end.

  Definition isBag (n : ip_address)
             (v : val) (Ψ : val → iProp) :=
    (∃ (l : loc) v' γ, ⌜v = PairV #l v'⌝ ∗
      is_lock n γ v' (∃ u, l ↦[n] u ∗ bagList Ψ u))%I.

  Global Instance bag_persistent n v Ψ: Persistent (isBag n v Ψ).
  Proof. apply _. Qed.

  Lemma newbag_spec ip Ψ :
     {{{ True }}} newbag #() @[ip] {{{ v, RET v; isBag ip v Ψ }}}.
  Proof.
    iIntros (Φ) "Hn HΦ".
    wp_lam; wp_alloc ℓ as "Hℓ"; wp_let.
    wp_bind (newlock _)%E.
    iApply ((newlock_spec ip (∃ u, ℓ ↦[ip] u ∗ bagList Ψ u)%I) with "[Hn Hℓ]").
    - iFrame. iExists NONEV. iFrame.
    - iNext. iIntros (v γ) "IL". wp_pures.
      iApply "HΦ". iExists ℓ, v, γ. iSplit; auto.
  Qed.

  Lemma bag_insert_spec ip v Ψ e:
    {{{ isBag ip v Ψ ∗ Ψ e }}} insert v e @[ip] {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#HC HΨ] HΦ".
    iDestruct "HC" as (ℓ u γ) "[% #HLock]"; subst.
    wp_lam. wp_pures. wp_bind (acquire _)%E.
    iApply (acquire_spec _ _ _ (∃ u, ℓ ↦[ip] u ∗ bagList Ψ u))%I;
      first by iFrame "#".
    iNext. iIntros (v) "(-> & HLocked &  HInv)".
    iDestruct "HInv" as (u') "[Hpt Hisbag]".
    wp_pures. wp_load. wp_store.
    iApply (release_spec _ _ _ (∃ u0, ℓ ↦[ip] u0 ∗ bagList Ψ u0)
              with "[-HΦ]")%I.
    - iFrame; iFrame "#". iExists (SOMEV (e, u')) ; iFrame.
    - iNext. iIntros (?) "->". by iApply "HΦ".
  Qed.

  Lemma bag_remove_spec ip v Ψ:
    {{{ isBag ip v Ψ }}}
      remove v @[ip]
    {{{ v, RET v; ⌜v = NONEV⌝ ∨ ∃ x, ⌜v = SOMEV x⌝ ∗ Ψ x }}}.
  Proof.
    iIntros (Φ) "HC HΦ".
    iDestruct "HC" as (ℓ u γ) "[% #HLock]"; subst.
    wp_lam. wp_pures. wp_bind (acquire _)%E.
    iApply (acquire_spec _ _ _ (∃ u, ℓ ↦[ip] u ∗ bagList Ψ u))%I;
      first by iFrame "#".
    iNext. iIntros (v) "(-> & HLocked &  HInv)".
    iDestruct "HInv" as (u') "[Hpt Hisbag]".
    wp_pures. wp_load. wp_pures.
    destruct u'; try (iDestruct "Hisbag" as "%" ; contradiction).
    - wp_pures. wp_bind (release _)%E.
      iApply (release_spec _ _ _ (∃ u0, ℓ ↦[ip] u0 ∗ bagList Ψ u0)
                with "[-HΦ]")%I; iFrame "#"; iFrame.
      + iExists (InjLV u') ; iFrame.
      + iNext. iIntros (v) "-> /=". wp_pures.
        iApply "HΦ". eauto.
    - wp_pures.
      destruct u'; try (iDestruct "Hisbag" as "%" ; contradiction).
      wp_pures; wp_store; wp_pures. wp_bind (release _)%E.
      iDestruct "Hisbag" as "[HΨ Hisbag]".
      iApply (release_spec _ _ _ (∃ u0, ℓ ↦[ip] u0 ∗ bagList Ψ u0)
                with "[HLocked Hisbag Hpt]")%I; iFrame "#"; iFrame.
      + iExists u'2. iFrame.
      + iNext. iIntros (?) "-> /=". wp_pures.
        iApply "HΦ". iRight.
        iExists _. by iFrame.
  Qed.

End spec.
