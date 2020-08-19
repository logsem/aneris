From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre adequacy.
From aneris.aneris_lang Require Export lang resources state_interp network.
Set Default Proof Using "Type".

Import Network.

Theorem adequacy `{anerisPreG Σ} IPs A s e ip σ φ :
  (∀ `{anerisG Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
     fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
     WP (mkExpr ip e) @ s; ⊤ {{v, ⌜φ v⌝ }}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate s (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros Hwp Hipdom Hpiiu Hip Hfixdom Hste Hsce Hmse.
  eapply (wp_adequacy _ _); iIntros (??) "/=".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (fixed_init A) as (γsif) "#Hsif".
  iMod (free_ips_init IPs) as (γips) "[HIPsCtx HIPs]".
  iMod free_ports_auth_init as (γpiu) "HPiu".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_fixed_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
         |}).
  iMod (Hwp dg) as (f) "Hwp".
  iMod (saved_si_update A with "[$Hsi $Hsi']") as (M HMfs) "[HM #Hsa]".
  assert (dom (gset _) M = A) as Hdmsi.
  { apply elem_of_equiv_L => ?.
    split; intros ?%elem_of_elements;
      apply elem_of_elements; [by rewrite -HMfs|].
    by rewrite HMfs. }
  iAssert ([∗ set] s ∈ A, s ⤇ f s)%I as "#Hsa'".
  { rewrite -Hdmsi -!big_sepM_dom.
    iApply (big_sepM_mono with "[$Hsa]"); simpl; auto.
    iIntros (? ? Hx) "[? ?]"; iExists _; iFrame. }
  iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
  iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp #Hγn]"; [done|].
  iAssert (is_node ip) as "Hn".
  { iExists _. eauto. }
  iModIntro.
  iExists (λ σ _, aneris_state_interp σ), (λ _, True)%I.
  iSplitR "Hwp HIPs"; last first.
  { iApply ("Hwp" with "Hsif Hsa' HIPs Hn"). }
  by iApply (@aneris_state_interp_init _ dg
            with "Hmp Hγn Hh Hs Hsif HM Hsa' HIPsCtx HPiu").
Qed.

Definition safe e σ := @adequate aneris_lang NotStuck e σ (λ _ _, True).

Theorem adequacy_safe `{anerisPreG Σ} IPs A e ip σ :
  (∀ `{anerisG Σ}, ⊢ |={⊤}=> ∃ (f : socket_address → socket_interp Σ),
     fixed A -∗ ([∗ set] a ∈ A, a ⤇ (f a)) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
     WP (mkExpr ip e) {{v, True }}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ ip, ip ∈ IPs → state_ports_in_use σ !! ip = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  safe (mkExpr ip e) σ.
Proof. apply adequacy. Qed.

Theorem adequacy_hoare `{anerisPreG Σ} IPs A e σ φ ip :
  (∀ `{anerisG Σ}, ⊢ ∃ (f : socket_address → socket_interp Σ),
      {{{ fixed A ∗ ([∗ set] a ∈ A, a ⤇ (f a)) ∗ ([∗ set] ip ∈ IPs, free_ip ip) ∗ is_node ip }}}
          (mkExpr ip e)
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  dom (gset ip_address) (state_ports_in_use σ) = IPs →
  (∀ i, i ∈ IPs → state_ports_in_use σ !! i = Some ∅) →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate NotStuck (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros Hwp ???????.
  eapply adequacy; [|done..].
  intros ?. iModIntro.
  iDestruct Hwp as (f) "#Hwp".
  iExists f. iIntros "????".
  iApply ("Hwp" with "[$]"); auto.
Qed.
