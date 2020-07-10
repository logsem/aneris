From iris Require Import invariants.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import coq_tactics reduction.
From aneris Require Import lang lifting tactics proofmode notation.

Definition newlock : ground_lang.val := λ: <>, ref #false.
Definition try_acquire : ground_lang.val := λ: "l", CAS "l" #false #true.
Definition acquire : ground_lang.val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".
Definition release : ground_lang.val := λ: "l", "l" <- #false.

(** The CMRA we need. *)
Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitO) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!distG Σ, !lockG Σ} (N : namespace).

  Definition lock_inv (n : Network.ip_address) (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦[n] #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (n : Network.ip_address) (γ : gname) (lk : ground_lang.val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, ⌜lk = #l⌝ ∧ inv N (lock_inv n γ l R))%I.

  Definition locked (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Global Instance lock_inv_ne n γ l : NonExpansive (lock_inv n γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne n γ l : NonExpansive (is_lock n γ l).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent n γ l R : Persistent (is_lock n γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Lemma newlock_spec n (R : iProp Σ):
    {{{ IsNode n ∗ R }}} ⟨n; newlock #()⟩ {{{ lk γ, RET 〈n;lk〉; is_lock n γ lk R }}}.
  Proof.
    iIntros (Φ) "[Hn HR] HΦ". rewrite -wp_fupd /newlock /=.
    wp_lam. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv n γ l R) with "[-HΦ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iApply "HΦ". iExists l. eauto.
  Qed.

  Lemma try_acquire_spec n γ lk R :
    {{{ is_lock n γ lk R }}}
      ⟨n; try_acquire lk⟩
    {{{ b, RET 〈n;#b〉; if b is true then locked γ ∗ R else True }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iDestruct "Hl" as (l ->) "#Hinv".
    wp_rec. wp_apply wp_atomic.
    iInv N as ([]) "[>Hl HR]" "Hclose".
    - iModIntro. wp_apply (wp_cas_fail with "Hl"); first done. iIntros "Hl".
      iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists _. iFrame. }
      iModIntro. by iApply "HΦ".
    - iModIntro. wp_apply (wp_cas_suc with "Hl"). iIntros "Hl".
      iMod ("Hclose" with "[Hl]") as "_".
      { iNext. iExists _. iFrame. }
      by iApply "HΦ".
  Qed.

  Lemma acquire_spec n γ lk R :
    {{{ is_lock n γ lk R }}} ⟨n; acquire lk⟩ {{{ v, RET 〈n;v〉; ⌜v = #()⌝ ∗ locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hl"). iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; by iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma release_spec n γ lk R :
    {{{ is_lock n γ lk R ∗ locked γ ∗ R }}} ⟨n; release lk⟩ {{{ v, RET 〈n;v〉; ⌜v = #()⌝ }}}.
  Proof.
    iIntros (Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l ->) "#Hinv".
    rewrite /release /=. wp_lam.
    wp_apply wp_atomic.
    iInv N as (b) "[>Hl _]" "Hclose". iModIntro.
    wp_store.
    iMod ("Hclose" with "[Hl Hlocked HR]") as "_".
    { iNext. iExists _. iFrame. iFrame. }
    iModIntro. by iApply "HΦ".
  Qed.
End proof.

Typeclasses Opaque is_lock locked.
