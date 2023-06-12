From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import network adequacy.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.
From aneris.algebra Require Import disj_gsets.

Notation aneris_wptp ts Φs :=
  ([∗ list] t;Φ ∈ ts;Φs, WP (expr_e t) @[expr_n t] ⊤ {{ Φ }})%I.

Definition aneris_adequate_multiple
           (es : list aneris_expr) (σ : state) (φs : list (val → Prop))  :=
  adequate_multiple
    NotStuck es σ
    ((λ φ v _, φ v) <$>
     ((λ eφ, λ v, ∃ w, v = mkVal (expr_n eφ.1) w ∧ eφ.2 w) <$> (zip es φs))).

Lemma big_sepL_prefixes_l {PROP:bi} {X Y}
      (xs xs' : list X) (ys : list Y) (Φ : X → Y → PROP) :
  ([∗ list] x;y ∈ xs;ys, Φ x y) -∗
  ([∗ list] x;y ∈ prefixes_from xs' xs;ys, Φ x.2 y).
Proof.
  iIntros "HΦs".
  iInduction xs as [|x xs] "IHxs" forall (ys xs'); [done|].
  destruct ys; [done|]=> /=.
  iDestruct "HΦs" as "[$ HΦs]".
  by iApply "IHxs".
Qed.

Theorem adequacy_strong Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        A lbls obs_send_sas obs_rec_sas (es : list aneris_expr) σ (φs : list (val → Prop)) :
  length es >= 1 →
  aneris_model_rel_finitary Mdl →
  (∀ (aG : anerisG Mdl Σ), ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] sa ∈ A, sa ⤳[bool_decide (sa ∈ obs_send_sas),
                           bool_decide (sa ∈ obs_rec_sas)] (∅, ∅)) -∗
     ([∗ set] ip ∈ get_ips es,
        ([∗ map] l ↦ v ∈ (state_heaps σ !!! ip), l ↦[ip] v) ∗
        ([∗ map] sh ↦ s ∈ (state_sockets σ !!! ip), sh ↪[ip] s.1)) -∗
     ([∗ map] ip ↦ ports ∈ (addrs_to_ip_ports_map
                              (A ∖ (ports_in_use $ state_sockets σ))),
        free_ports ip ports)%I -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas ={⊤}=∗
     aneris_wptp es ((λ φ, (λ v, ⌜φ v⌝):val → iProp Σ) <$> φs)) →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  dom $ state_heaps σ = get_ips es →
  dom $ state_sockets σ = get_ips es →
  (* Port coherence *)
  ((∀ ip ps, (GSet <$> (addrs_to_ip_ports_map
                              (A ∖ (ports_in_use $ state_sockets σ))))
               !! ip = Some (GSet ps) →
             ∀ Sn, (state_sockets σ) !! ip = Some Sn →
                   ∀ p, p ∈ ps → port_not_in_use p Sn)) →
  (* Socket buffers are initially empty *)
  map_Forall (λ ip s, map_Forall (λ sh sb, sb.2 = []) s) (state_sockets σ) →
  map_Forall (λ ip s, socket_handlers_coh s) (state_sockets σ) →
  map_Forall (λ ip s, socket_addresses_coh s ip) (state_sockets σ) →
  (* Message soup is initially empty *)
  state_ms σ = ∅ →
  aneris_adequate_multiple es σ φs.
Proof.
  intros Hlen HMdlfin Hwp Hsendle Hrecvle Hσ Hskts Hports Hbs Hcoh1 Hcoh2 Hms.
  rewrite /aneris_adequate_multiple.
  rewrite /aneris_adequate_multiple. simpl.
  eapply (adequacy_strong A _ obs_send_sas obs_rec_sas);
    [done|done|done|done| |done..].
  intros dg.
  iMod (Hwp dg) as "Hwp".
  iModIntro. iIntros "????? #Hns ????? /=".
  iSpecialize ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  iMod "Hwp". iModIntro. clear Hwp Hlen Hσ Hskts.
  setoid_rewrite aneris_wp_unfold. rewrite /aneris_wp_def.
  assert (∃ es', [] = es') as [es' ->] by eauto.
  iDestruct (big_sepL_prefixes_l _ es' with "Hwp") as "Hwp".
  iInduction es as [|e es] "IHes" forall (φs es'); [done|].
  destruct φs; [done|].
  rewrite /get_ips.
  simpl.
  iDestruct "Hwp" as "[Hwp Hwps]".
  iDestruct (big_sepS_elem_of _ _ (expr_n e) with "Hns") as "Hn";
    [set_solver|].
  iSplitL "Hwp Hn".
  { rewrite /locale_of. simpl.
    destruct e; simpl.
    iSpecialize ("Hwp" with "[$]").
    iApply (wp_wand with "Hwp"). by eauto. }
  iDestruct (big_sepS_subseteq _ _ (list_to_set
                            (list_fmap aneris_expr ip_address expr_n es)) with "Hns") as "Hns'"; [set_solver|].
  iDestruct ("IHes" with "Hns' Hwps") as "Hwps".
  iApply (big_sepL2_impl with "Hwps").
  by iIntros "!>" (i eφs1 eφs2 HSome1 HSome2) "Hwp".
Qed.

Definition aneris_adequate (e :expr) (ip : ip_address) (σ : state)
           (φ : val → Prop) :=
  adequate NotStuck (mkExpr ip e) σ (λ v _, ∃ w, v = mkVal ip w ∧ φ w).

Theorem adequacy_groups Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e ip σ φ :
  all_disjoint A →
  set_Forall (λ sag, sag ≠ ∅) A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=>
     unallocated_groups A -∗
     ([∗ set] b ∈ A, b ⤳*[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs_groups sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs_groups sa []) -∗
     observed_send_groups obs_send_sas -∗
     observed_receive_groups obs_rec_sas -∗
     WP e @[ip] ⊤ {{ v, ⌜φ v⌝ }}) →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros Hdisj Hne Hsendle Hrecvle.
  intros HMdlfin Hwp Hip Hste Hsce Hmse.
  eapply (adequacy_groups _ A _ obs_send_sas obs_rec_sas);
    [done|done|done|done|done| |done|done|done|done].
  intros dg.
  iMod (Hwp dg) as "Hwp".
  iModIntro. iIntros "?????????? /=".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iSpecialize ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  iApply (wp_wand with "Hwp").
  eauto.
Qed.

Theorem adequacy1 Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e ip σ φ :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳1[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     WP e @[ip] ⊤ {{ v, ⌜φ v⌝ }}) →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros HMdlfin Hwp Hsendle Hrecvle Hip Hste Hsce Hmse.
  eapply adequacy1; [done| |apply Hsendle|done|done|done|done|done].
  intros dg.
  iMod (Hwp dg) as "Hwp".
  iModIntro. iIntros "?????????? /=".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iSpecialize ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  iApply (wp_wand with "Hwp").
  eauto.
Qed.

Theorem adequacy Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e ip σ φ :
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     WP e @[ip] ⊤ {{ v, ⌜φ v⌝ }}) →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros HMdlfin Hwp Hsendle Hrecvle Hip Hste Hsce Hmse.
  eapply adequacy; [done| |apply Hsendle|done|done|done|done|done].
  intros dg.
  iMod (Hwp dg) as "Hwp".
  iModIntro. iIntros "?????????? /=".
  rewrite !aneris_wp_unfold /aneris_wp_def.
  iSpecialize ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  iApply (wp_wand with "Hwp").
  eauto.
Qed.

Theorem adequacy_hoare_groups Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e σ φ ip :
  all_disjoint A →
  set_Forall (λ sag, sag ≠ ∅) A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢
          {{{ unallocated_groups A ∗
              ([∗ set] a ∈ A, a ⤳*[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) ∗
              frag_st Mdl.(model_state_initial) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              ([∗ set] lbl ∈ lbls, alloc_evs lbl []) ∗
              ([∗ set] sa ∈ obs_send_sas, sendon_evs_groups sa []) ∗
              ([∗ set] sa ∈ obs_rec_sas, receiveon_evs_groups sa []) ∗
              observed_send_groups obs_send_sas ∗
              observed_receive_groups obs_rec_sas }}}
          e @[ip]
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros Hdisj Hne Hsendle Hrecvle.
  intros ? Hwp ????.
  eapply (adequacy_groups _ _ _ A _ obs_send_sas obs_rec_sas); eauto.
  intros ?. iModIntro.
  iDestruct Hwp as "#Hwp".
  iIntros "?????????".
  iApply ("Hwp" with "[$]"); auto.
Qed.

Theorem adequacy1_hoare Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e σ φ ip :
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢
          {{{ unallocated A ∗
              ([∗ set] a ∈ A, a ⤳1[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) ∗
              frag_st Mdl.(model_state_initial) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              ([∗ set] lbl ∈ lbls, alloc_evs lbl []) ∗
              ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) ∗
              ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) ∗
              observed_send obs_send_sas ∗
              observed_receive obs_rec_sas }}}
          e @[ip]
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros ??? Hwp ????.
  eapply (adequacy1 _ _ _ _ _ obs_send_sas obs_rec_sas); eauto.
  intros ?. iModIntro.
  iDestruct Hwp as "#Hwp".
  iIntros "?????????".
  iApply ("Hwp" with "[$]"); auto.
Qed.

Theorem adequacy_hoare Σ Mdl `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e σ φ ip :
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  (∀ `{anerisG Mdl Σ}, ⊢
          {{{ unallocated A ∗
              ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) ∗
              frag_st Mdl.(model_state_initial) ∗
              ([∗ set] ip ∈ IPs, free_ip ip) ∗
              ([∗ set] lbl ∈ lbls, alloc_evs lbl []) ∗
              ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) ∗
              ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) ∗
              observed_send obs_send_sas ∗
              observed_receive obs_rec_sas }}}
          e @[ip]
      {{{ v, RET v; ⌜φ v⌝ }}}) →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  aneris_adequate e ip σ φ.
Proof.
  intros ??? Hwp ????.
  eapply (adequacy _ _ _ _ _ obs_send_sas obs_rec_sas); eauto.
  intros ?. iModIntro.
  iDestruct Hwp as "#Hwp".
  iIntros "?????????".
  iApply ("Hwp" with "[$]"); auto.
Qed.
