From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import network adequacy.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre aneris_hoare.

Import Network.

Definition aneris_adequate (e : base_lang.expr) (ip : ip_address) (σ : state)
           (φ : base_lang.val → Prop) :=
  adequate NotStuck (mkExpr ip e) σ (λ v _, ∃ w, v = mkVal ip w ∧ φ w).

Theorem adequacy `{anerisPreG Σ} IPs A e ip σ φ :
  (∀ `{anerisG Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
     fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     WP e @[ip] ⊤ {{ v, ⌜φ v⌝ }}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros Hwp Hipdom Hpiiu Hip Hfixdom Hste Hsce Hmse.
  eapply adequacy; [|done..].
  intros dg.
  iMod (Hwp dg) as (f) "Hwp".
  iModIntro. iExists _. iIntros "???? /=".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iSpecialize ("Hwp" with "[$] [$] [$] [$]").
  iApply (wp_wand with "Hwp").
  eauto.
Qed.

Theorem adequacy_hoare `{anerisPreG Σ} IPs A e σ φ ip :
  (∀ `{anerisG Σ}, ⊢ ∃ (f : socket_address → socket_interp Σ),
      {{{ fixed A ∗ ([∗ set] a ∈ A, a ⤇ (f a)) ∗ ([∗ set] ip ∈ IPs, free_ip ip) }}}
          e @[ip]
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros Hwp ???????.
  eapply adequacy; [|done..].
  intros ?. iModIntro.
  iDestruct Hwp as (f) "#Hwp".
  iExists f. iIntros "???".
  iApply ("Hwp" with "[$]"); auto.
Qed.
