From trillium Require Import finitary.
From aneris.aneris_lang Require Import adequacy proofmode.
From aneris.aneris_lang.program_logic Require Import aneris_adequacy.

(** If we don't care about Trillium-style refinement we can always just pick the trivial model *)
Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

#[global] Notation anerisG Σ := (anerisG unit_model Σ).

Theorem adequacy_hoare_no_model Σ `{anerisPreG Σ unit_model} IPs A lbls obs_send_sas obs_rec_sas e σ φ ip :
  obs_send_sas ⊆ A →
  obs_rec_sas ⊆ A →
  (∀ `{anerisG Σ}, ⊢
          {{{ unallocated A ∗
              ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              ([∗ set] lbl ∈ lbls, alloc_evs lbl []) ∗
              ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) ∗
              ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) ∗
              observed_send obs_send_sas ∗
              observed_receive obs_rec_sas }}}
          e @[ip]
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros ?? Hspec ?????.
  eapply (adequacy_hoare Σ _ IPs A lbls obs_send_sas obs_rec_sas);
    [set_solver|set_solver|..|done|set_solver|set_solver|set_solver|done].
  { apply unit_model_rel_finitary. }
  iIntros (? Φ) "!# (?&?&?&?&?&?&?&?&?) HΦ".
  iApply (Hspec with "[-HΦ]"); [|done].
  iFrame.
Qed.
