From iris Require Import invariants.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import coq_tactics reduction proofmode.
From aneris.aneris_lang Require Import ast lang tactics proofmode.
From aneris.aneris_lang.lib Require Import lock_proof.

(* Class monitorG Σ := MonitorG { monitor_tokG :> lockG Σ }. *)
(* Definition monitorΣ : gFunctors := #[lockΣ]. *)
(* #[local] Instance monitorsubG_monitorΣ {Σ} : subG monitorΣ Σ → monitorG Σ. *)
(* Proof. econstructor; solve_inG. Qed. *)

Section proof.
  Context `{!anerisG Mdl Σ, !lockG Σ}.

  Definition monitor_inv (n : ip_address) (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    lock_inv n γ l R.

  Definition is_monitor (n : ip_address) (γ : gname) (mon : val) (R : iProp Σ) : iProp Σ :=
    ∃ (lk : val), ⌜mon = (#(), lk)%V⌝ ∗ (is_lock n γ lk R)%I.

  Global Instance monitor_inv_ne n γ l : NonExpansive (monitor_inv n γ l).
  Proof. solve_proper. Qed.
  Global Instance is_monitor_ne n γ l : NonExpansive (is_monitor n γ l).
  Proof. solve_proper. Qed.

  Global Instance is_monitor_persistent n γ l R : Persistent (is_monitor n γ l R).
  Proof. apply _. Qed.

  Lemma new_monitor_spec ip R :
    {{{ R }}}
      new_monitor #() @[ip]
    {{{ γ mon, RET mon; is_monitor ip γ mon R }}}.
  Proof.
    iIntros (Φ) "HR HΦ". rewrite /new_monitor seal_eq /new_monitor_def.
    wp_lam. wp_apply (newlock_spec _ R with "[$HR]").
    iIntros (mon γ) "#Hmon". wp_pures. iApply ("HΦ" $! γ). rewrite /is_monitor.
    iExists _; iSplit; first done. iFrame "#".
  Qed.

  Lemma monitor_try_acquire_spec ip γ mon R :
    {{{ is_monitor ip γ mon R }}}
      monitor_try_acquire mon @[ip]
    {{{ b, RET #b; if b is true then locked γ ∗ R else True }}}.
  Proof.
    iIntros (Φ) "#Hmon HΦ".
    iDestruct "Hmon" as (lk ->) "#Hinv".
    rewrite /monitor_try_acquire seal_eq /monitor_try_acquire_def.
    wp_pures. by wp_apply (try_acquire_spec with "[$Hinv]").
  Qed.

  Lemma monitor_acquire_spec ip γ mon R :
    {{{ is_monitor ip γ mon R }}}
      monitor_acquire mon @[ip]
    {{{ v, RET v; ⌜v = #()⌝ ∗ locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hmon HΦ".
    iDestruct "Hmon" as (lk ->) "#Hinv".
    rewrite /monitor_acquire seal_eq /monitor_acquire_def.
    wp_pures. by wp_apply (acquire_spec with "[$Hinv]").
  Qed.

  Lemma monitor_release_spec ip γ mon R :
    {{{ is_monitor ip γ mon R ∗ locked γ ∗ R }}}
      monitor_release mon @[ip]
    {{{ v, RET v; ⌜v = #()⌝ }}}.
  Proof.
    iIntros (Φ) "(#Hmon & Hlocked & HR) HΦ".
    iDestruct "Hmon" as (lk ->) "#Hinv".
    rewrite /monitor_release seal_eq /monitor_release_def.
    wp_pures. by wp_apply (release_spec with "[$Hinv $Hlocked $HR]").
  Qed.

  Lemma monitor_signal_spec ip γ mon R :
    {{{ is_monitor ip γ mon R ∗ locked γ ∗ R }}}
      monitor_signal mon @[ip]
    {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "((%lk & -> & #Hcv) & Hlkd & HR) HΦ".
    rewrite /monitor_signal seal_eq /monitor_signal_def.
    wp_pures. iApply "HΦ". iFrame; eauto.
  Qed.

  Lemma monitor_broadcast_spec ip γ mon R :
    {{{ is_monitor ip γ mon R ∗ locked γ ∗ R }}}
      monitor_broadcast mon @[ip]
    {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "((%lk & -> & #Hcv) & Hlkd & HR) HΦ".
    rewrite /monitor_broadcast seal_eq /monitor_broadcast_def.
    wp_pures. iApply "HΦ". iFrame; eauto.
  Qed.

   Lemma monitor_wait_spec ip γ mon R :
    {{{ is_monitor ip γ mon R ∗ locked γ ∗ R }}}
      monitor_wait mon @[ip]
    {{{ v, RET v; ⌜v = #()⌝ ∗ locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "((%lk & -> & #Hcv) & Hlkd & HR) HΦ".
    rewrite /monitor_wait seal_eq /monitor_wait_def.
    wp_pures. wp_apply (release_spec ip γ _ R with "[$Hlkd $HR $Hcv][HΦ]").
    iNext. iIntros. wp_pures.
    wp_apply (acquire_spec ip γ _ R with "[$Hcv][HΦ]").
    iNext. by iApply "HΦ".
  Qed.

End proof.

Typeclasses Opaque monitor_inv is_monitor.
Global Opaque monitor_inv is_monitor.
