From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import network adequacy.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.
From aneris.algebra Require Import disj_gsets.


Definition aneris_adequate (e :expr) (ip : ip_address) (σ : state)
           (φ : val → Prop) :=
  adequate NotStuck (mkExpr ip e) σ (λ v _, ∃ w, v = mkVal ip w ∧ φ w).

Theorem adequacy_groups Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs ports A lbls obs_send_sas obs_rec_sas e ip σ φ :
  all_disjoint A →
  set_Forall (λ sag, sag ≠ ∅) A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=>
     unallocated_groups A -∗
     ([∗ set] b ∈ A, b ⤳*[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     ([∗ map] ip↦p ∈ ports, free_ports ip p) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs_groups sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs_groups sa []) -∗
     observed_send_groups obs_send_sas -∗
     observed_receive_groups obs_rec_sas -∗
     WP e @[ip] ⊤ {{ v, ⌜φ v⌝ }}) →
  ip ∉ IPs →
  (∀ sag sa, sag ∈ A → sa ∈ sag → ip_of_address sa ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros Hdisj Hne Hsendle Hrecvle.
  intros HMdlfin Hwp Hip Hfixdom Hste Hsce Hmse.
  eapply (adequacy_groups _ _ A _ obs_send_sas obs_rec_sas);
    [done|done|done|done|done| |done|done|done|done|done].
  intros dg.
  iMod (Hwp dg) as "Hwp".
  iModIntro. iIntros "??????????? /=".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iSpecialize ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  iApply (wp_wand with "Hwp").
  eauto.
Qed.

Theorem adequacy1 Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs ports A lbls obs_send_sas obs_rec_sas e ip σ φ :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳1[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     ([∗ map] ip↦p ∈ ports, free_ports ip p) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     WP e @[ip] ⊤ {{ v, ⌜φ v⌝ }}) →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros HMdlfin Hwp Hsendle Hrecvle Hip Hfixdom Hste Hsce Hmse.
  eapply adequacy1; [done| |apply Hsendle|done|done|done|done|done|done].
  intros dg.
  iMod (Hwp dg) as "Hwp".
  iModIntro. iIntros "??????????? /=".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iSpecialize ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  iApply (wp_wand with "Hwp").
  eauto.
Qed.

Theorem adequacy Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs ports A lbls obs_send_sas obs_rec_sas e ip σ φ :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     ([∗ map] ip↦p ∈ ports, free_ports ip p) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     WP e @[ip] ⊤ {{ v, ⌜φ v⌝ }}) →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  (∀ a, a ∈ A → ip_of_address a ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros HMdlfin Hwp Hsendle Hrecvle Hip Hfixdom Hste Hsce Hmse.
  eapply adequacy; [done| |apply Hsendle|done|done|done|done|done|done].
  intros dg.
  iMod (Hwp dg) as "Hwp".
  iModIntro. iIntros "??????????? /=".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iSpecialize ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  iApply (wp_wand with "Hwp").
  eauto.
Qed.

Theorem adequacy_hoare_groups Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs ports A lbls obs_send_sas obs_rec_sas e σ φ ip :
  all_disjoint A →
  set_Forall (λ sag, sag ≠ ∅) A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢
          {{{ unallocated_groups A ∗
              ([∗ set] a ∈ A, a ⤳*[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) ∗
              frag_st Mdl.(model_state_initial) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              ([∗ map] ip↦p ∈ ports, free_ports ip p) ∗
              ([∗ set] lbl ∈ lbls, alloc_evs lbl []) ∗
              ([∗ set] sa ∈ obs_send_sas, sendon_evs_groups sa []) ∗
              ([∗ set] sa ∈ obs_rec_sas, receiveon_evs_groups sa []) ∗
              observed_send_groups obs_send_sas ∗
              observed_receive_groups obs_rec_sas }}}
          e @[ip]
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  (∀ sag sa, sag ∈ A → sa ∈ sag → ip_of_address sa ∈ IPs) →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros Hdisj Hne Hsendle Hrecvle.
  intros ? Hwp ?????.
  eapply (adequacy_groups _ _ _ ports A _ obs_send_sas obs_rec_sas); eauto.
  intros ?. iModIntro.
  iDestruct Hwp as "#Hwp".
  iIntros "??????????".
  iApply ("Hwp" with "[$]"); auto.
Qed.

Theorem adequacy1_hoare Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs ports A lbls obs_send_sas obs_rec_sas e σ φ ip :
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢
          {{{ unallocated A ∗
              ([∗ set] a ∈ A, a ⤳1[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) ∗
              frag_st Mdl.(model_state_initial) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              ([∗ map] ip↦p ∈ ports, free_ports ip p) ∗
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
  intros ??? Hwp ?????.
  eapply (adequacy1 _ _ _ _ _ _ obs_send_sas obs_rec_sas); eauto.
  intros ?. iModIntro.
  iDestruct Hwp as "#Hwp".
  iIntros "??????????".
  iApply ("Hwp" with "[$]"); auto.
Qed.

Theorem adequacy_hoare Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs ports A lbls obs_send_sas obs_rec_sas e σ φ ip :
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢
          {{{ unallocated A ∗
              ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) ∗
              frag_st Mdl.(model_state_initial) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              ([∗ map] ip↦p ∈ ports, free_ports ip p) ∗
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
  intros ??? Hwp ?????.
  eapply (adequacy _ _ _ _ _ _ obs_send_sas obs_rec_sas); eauto.
  intros ?. iModIntro.
  iDestruct Hwp as "#Hwp".
  iIntros "??????????".
  iApply ("Hwp" with "[$]"); auto.
Qed.
