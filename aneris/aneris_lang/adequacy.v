From stdpp Require Import finite.
From iris.algebra Require Import auth gmap.
From iris.proofmode Require Import tactics.
From trillium.prelude Require Import quantifiers classical_instances finitary.
From trillium.program_logic Require Export weakestpre adequacy.
From aneris.lib Require Import gen_heap_light.
From aneris.prelude Require Export gmultiset.
From aneris.lib Require Import singletons.
From aneris.algebra Require Import disj_gsets.
From aneris.aneris_lang Require Export lang resources network.
From aneris.aneris_lang.state_interp Require Export state_interp.
Set Default Proof Using "Type".

Definition aneris_model_rel_finitary (Mdl : Model) :=
  ∀ mdl : Mdl, smaller_card {mdl' : Mdl | Mdl mdl mdl'} nat.

Definition get_ips (es : list aneris_expr) : gset ip_address :=
  list_to_set $ expr_n <$> es.

Definition addrs_to_ip_ports_map (A : gset socket_address) : gmap ip_address (gset port) :=
  fold_right union ∅ $
             (λ sa, {[ip_of_address sa := {[port_of_address sa]}]}) <$> (elements A).

Definition ports_in_use (skts : gmap ip_address sockets) : gset socket_address :=
  map_fold (λ ip skts A,
              map_fold
                (λ sh skt A, match saddress skt.1 with
                             | Some a => {[a]}
                             | None => ∅
                             end ∪ A) ∅ skts ∪ A) ∅ skts.

(* TODO: Can this be generalised? *)
Lemma ports_in_use_empty_map M :
  ports_in_use (gset_to_gmap ∅ M) = ∅.
Proof.
  induction M as [|m M Hnin IHM] using set_ind_L; [done|].
  rewrite /ports_in_use.
  rewrite gset_to_gmap_union_singleton.
  rewrite map_fold_insert_L;
    [set_solver|set_solver|by rewrite lookup_gset_to_gmap_None].
Qed.

Definition wp_group_proto_multiple_strong `{anerisPreG Σ Mdl} A
           (lbls: gset string)
           (obs_send_sas obs_rec_sas : gset socket_address_group)
           σ s (es : list aneris_expr) (φs : list (aneris_val → Prop)) :=
  (∀ (aG : anerisG Mdl Σ), ⊢ |={⊤}=>
     unallocated_groups A -∗
     ([∗ set] sag ∈ A, sag ⤳*[bool_decide (sag ∈ obs_send_sas),
                              bool_decide (sag ∈ obs_rec_sas)] (∅, ∅)) -∗
     ([∗ set] ip ∈ get_ips es,
        ([∗ map] l ↦ v ∈ (state_heaps σ !!! ip), l ↦[ip] v) ∗
        ([∗ map] sh ↦ s ∈ (state_sockets σ !!! ip), sh ↪[ip] s.1)) -∗
     ([∗ map] ip ↦ ports ∈ (addrs_to_ip_ports_map
                              ((union_set A) ∖ (ports_in_use $ state_sockets σ))),
        free_ports ip ports)%I -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] ip ∈ get_ips es, is_node ip) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sag ∈ obs_send_sas, sendon_evs_groups sag []) -∗
     ([∗ set] sag ∈ obs_rec_sas, receiveon_evs_groups sag []) -∗
     observed_send_groups obs_send_sas -∗
     observed_receive_groups obs_rec_sas -∗
     aneris_state_interp σ (∅, ∅) ={⊤}=∗
     aneris_state_interp σ (∅, ∅) ∗
     wptp s es ((λ φ, (λ v, ⌜φ v⌝):aneris_val → iProp Σ) <$> φs)).

Definition wp_group_proto_multiple `{anerisPreG Σ Mdl} A
           (lbls: gset string)
           (obs_send_sas obs_rec_sas : gset socket_address_group)
           σ s (es : list aneris_expr) (φs : list (aneris_val → Prop)) :=
  (∀ (aG : anerisG Mdl Σ), ⊢ |={⊤}=>
     unallocated_groups A -∗
     ([∗ set] sag ∈ A, sag ⤳*[bool_decide (sag ∈ obs_send_sas),
                              bool_decide (sag ∈ obs_rec_sas)] (∅, ∅)) -∗
     ([∗ map] ip ↦ ports ∈ addrs_to_ip_ports_map $ union_set A,
        free_ports ip ports)%I -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] ip ∈ get_ips es, is_node ip) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sag ∈ obs_send_sas, sendon_evs_groups sag []) -∗
     ([∗ set] sag ∈ obs_rec_sas, receiveon_evs_groups sag []) -∗
     observed_send_groups obs_send_sas -∗
     observed_receive_groups obs_rec_sas -∗
     aneris_state_interp σ (∅, ∅) ={⊤}=∗
     aneris_state_interp σ (∅, ∅) ∗
     wptp s es ((λ φ, (λ v, ⌜φ v⌝):aneris_val → iProp Σ) <$> φs)).

Definition wp_proto_multiple_strong `{anerisPreG Σ Mdl} A
           (lbls: gset string)
           (obs_send_sas obs_rec_sas : gset socket_address)
           σ s (es : list aneris_expr) (φs : list (aneris_val → Prop)) :=
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
     ([∗ set] ip ∈ get_ips es, is_node ip) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     aneris_state_interp σ (∅, ∅) ={⊤}=∗
     aneris_state_interp σ (∅, ∅) ∗
     wptp s es ((λ φ, (λ v, ⌜φ v⌝):aneris_val → iProp Σ) <$> φs)).

Definition wp_proto_multiple `{anerisPreG Σ Mdl} A
           (lbls: gset string)
           (obs_send_sas obs_rec_sas : gset socket_address)
           σ s (es : list aneris_expr) (φs : list (aneris_val → Prop)) :=
  (∀ (aG : anerisG Mdl Σ), ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] sa ∈ A, sa ⤳[bool_decide (sa ∈ obs_send_sas),
                           bool_decide (sa ∈ obs_rec_sas)] (∅, ∅)) -∗
     ([∗ map] ip ↦ ports ∈ addrs_to_ip_ports_map A, free_ports ip ports)%I -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] ip ∈ get_ips es, is_node ip) -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     aneris_state_interp σ (∅, ∅) ={⊤}=∗
     aneris_state_interp σ (∅, ∅) ∗
     wptp s es ((λ φ, (λ v, ⌜φ v⌝):aneris_val → iProp Σ) <$> φs)).

Definition wp_group_proto `{anerisPreG Σ Mdl} IPs A
           (lbls: gset string)
           (obs_send_sas obs_rec_sas : gset socket_address_group) s e ip φ :=
  (∀ (aG : anerisG Mdl Σ), ⊢ |={⊤}=>
     unallocated_groups A -∗
     ([∗ set] sag ∈ A, sag ⤳*[bool_decide (sag ∈ obs_send_sas), bool_decide (sag ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sag ∈ obs_send_sas, sendon_evs_groups sag []) -∗
     ([∗ set] sag ∈ obs_rec_sas, receiveon_evs_groups sag []) -∗
     observed_send_groups obs_send_sas -∗
     observed_receive_groups obs_rec_sas ={⊤}=∗
     WP (mkExpr ip e) @ s; (ip, 0); ⊤ {{v, ⌜φ v⌝ }}).

Definition wp_group_single_proto `{anerisPreG Σ Mdl} IPs A
           (lbls: gset string)
           (obs_send_sas obs_rec_sas : gset socket_address) s e ip φ :=
  (∀ (aG : anerisG Mdl Σ), ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳1[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas ={⊤}=∗
     WP (mkExpr ip e) @ s; (ip,0); ⊤ {{v, ⌜φ v⌝ }}).

Definition wp_proto `{anerisPreG Σ Mdl} IPs A
           (lbls: gset string)
           (obs_send_sas obs_rec_sas : gset socket_address) s e ip φ :=
  (∀ (aG : anerisG Mdl Σ), ⊢ |={⊤}=>
     unallocated A -∗
     ([∗ set] a ∈ A, a ⤳[bool_decide (a ∈ obs_send_sas), bool_decide (a ∈ obs_rec_sas)] (∅, ∅)) -∗
     frag_st Mdl.(model_state_initial) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗
     is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas ={⊤}=∗
     WP (mkExpr ip e) @ s; (ip,0); ⊤ {{v, ⌜φ v⌝ }}).

Theorem adequacy_multiple_strong_groups `{anerisPreG Σ Mdl}
        `{EqDecision (aneris_to_trace_model Mdl)} A
        (lbls: gset string)
        (obs_send_sas obs_rec_sas : gset socket_address_group)
        s (es : list aneris_expr) σ (φs : list (aneris_val → Prop)) :
  length es >= 1 →
  all_disjoint A →
  set_Forall is_ne A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  wp_group_proto_multiple_strong A lbls obs_send_sas obs_rec_sas σ s es φs →
  dom $ state_heaps σ = get_ips es →
  dom $ state_sockets σ = get_ips es →
  (* Port coherence *)
  ((∀ ip ps, (GSet <$> (addrs_to_ip_ports_map
                              ((union_set A) ∖
                                             (ports_in_use $ state_sockets σ))))
               !! ip = Some (GSet ps) →
             ∀ Sn, (state_sockets σ) !! ip = Some Sn →
                   ∀ p, p ∈ ps → port_not_in_use p Sn)) →
  (* Socket buffers are initially empty *)
  map_Forall (λ ip s, map_Forall (λ sh sb, sb.2 = []) s) (state_sockets σ) →
  map_Forall (λ ip s, socket_handlers_coh s) (state_sockets σ) →
  map_Forall (λ ip s, socket_addresses_coh s ip) (state_sockets σ) →
  (* Message soup is initially empty *)
  state_ms σ = ∅ →
  adequate_multiple s es σ ((λ φ v _, φ v) <$> φs).
Proof.
  intros Hlen Hdisj Hne Hsendle Hrecvle.
  intros HMdlfin Hwp Hheaps_dom Hsockets_dom Hports Hsockets Hsockets_coh1 Hsockets_coh2 Hms. simpl.
  eapply (adequacy_multiple_xi _ _ _ _ (sim_rel (λ _ _, True)) _ _ _
                      (Mdl.(model_state_initial) : mstate (aneris_to_trace_model Mdl))); [done| |].
  { by eapply aneris_sim_rel_finitary. }
  iIntros (?) "/=".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (unallocated_init A) as (γsif) "[Hunallocated_auth Hunallocated]".
  iMod (free_ips_init ∅) as (γips) "[HIPsCtx _]".
  iMod (free_ports_auth_init_multiple) as (γpiu) "[HPiu HPs]".
  iMod (allocated_address_groups_init obs_send_sas) as
      (γobserved_send) "#Hobserved_send".
  iMod (allocated_address_groups_init obs_rec_sas) as
      (γobserved_receive) "#Hobserved_receive".
  iMod (socket_address_group_ctx_init) as (γC) "Hauth"; [done|].
  iMod (socket_address_group_own_alloc_subseteq_pre _ A A with "Hauth") as
      "[Hauth HownA]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "HownA") as "#HownAS".
  iMod (messages_ctx_init A _ _ _ _ with "HownAS Hobserved_send Hobserved_receive" ) as (γms) "[Hms HB]".
  iMod steps_init as (γsteps) "[Hsteps _]".
  iMod (model_init Mdl.(model_state_initial)) as (γm) "[Hmfull Hmfrag]".
  assert (rtc Mdl Mdl.(model_state_initial) Mdl.(model_state_initial)).
  { constructor. }
  iMod (alloc_evs_init lbls) as (γalevs) "[Halobctx Halobs]".
  iMod (sendreceive_evs_init obs_send_sas) as
      (γsendevs) "[Hsendevsctx Hsendevs]".
  iMod (sendreceive_evs_init obs_rec_sas) as
    (γreceiveevs) "[Hreceiveevsctx Hreceiveevs]".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_socket_address_group_name := γC;
           aneris_unallocated_socket_address_groups_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           aneris_model_name := γm;
           aneris_steps_name := γsteps;
           aneris_allocEVS_name := γalevs;
           aneris_sendonEVS_name := γsendevs;
           aneris_receiveonEVS_name := γreceiveevs;
           aneris_observed_send_name := γobserved_send;
           aneris_observed_recv_name := γobserved_receive;
         |}).
  iMod (Hwp dg) as "Hwp".
  iMod (is_node_alloc_multiple σ with "[Hmp]")
    as (γs Hheaps_dom' Hsockets_dom') "[Hγs [#Hn [Hσctx Hσ]]]"; [set_solver|done|].
  iExists
    (λ ex atr,
      aneris_events_state_interp ex ∗
      aneris_state_interp
        (trace_last ex).2
        (trace_messages_history ex) ∗
      auth_st (trace_last atr) ∗
        ⌜valid_state_evolution ex atr⌝ ∗
        steps_auth (trace_length ex))%I, (λ _ _, True)%I,
      ((λ φ v, ⌜φ v⌝)%I <$> φs), (λ _ _, True)%I.
  iSplitR; [by rewrite !fmap_length|].
  iSplitR; [iApply config_wp_correct|].
  iMod (socket_address_group_own_alloc_subseteq_pre _ A obs_send_sas with "Hauth")
    as "[Hauth Hown_send]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "Hown_send") as "Hown_send".
  iMod (socket_address_group_own_alloc_subseteq_pre _ A obs_rec_sas with "Hauth")
    as "[Hauth Hown_recv]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "Hown_recv") as "Hown_recv".
  iSplitR.
  { iModIntro. rewrite big_sepL2_fmap_l.
    iApply big_sepL2_intro; [done|].
    iIntros "!>" (k x1 x2 Heq1 Heq2). simplify_eq. by eauto. }
  iMod (socket_address_group_own_alloc_subseteq_pre _ A (obs_send_sas ∪ obs_rec_sas) with "Hauth")
    as "[Hauth Hown_send_recv]"; [by set_solver|].
  iPoseProof (aneris_events_state_interp_init with "[$] [$] [$] [$] [$] [$]") as "$".
  simpl.
  rewrite Hms gset_of_gmultiset_empty.
  iMod (socket_address_group_own_alloc_subseteq_pre _ A A with "Hauth")
    as "[Hauth Hown]"; [by set_solver|].
  iPoseProof (@aneris_state_interp_init_strong _ _ dg ∅ _ (addrs_to_ip_ports_map (⋃ₛ A ∖ ports_in_use (state_sockets σ)))
               with "Hγs Hσctx Hms [$Hauth $Hown]
               Hunallocated_auth Hsi HIPsCtx HPiu") as "Hinterp";
    [set_solver|set_solver|set_solver|set_solver|set_solver|
      done|done|done|done|done|done|..].
  iMod ("Hwp" with "Hunallocated HB [Hσ] HPs [$Hmfrag //] [Hn] Halobs [Hsendevs Hown_send] [Hreceiveevs Hown_recv] Hobserved_send Hobserved_receive Hinterp") as "[Hinterp Hwp]".
  { rewrite Hheaps_dom. done. }
  { rewrite Hheaps_dom. done. }
  { iApply big_sepS_sep. iFrame "Hsendevs Hown_send". }
  { iApply big_sepS_sep. iFrame "Hreceiveevs Hown_recv". }
  iFrame.
  iSplitR; [done|].
  iModIntro. iIntros (???) "% % % % % % % (?& Hsi & Htr & % & Hauth) Hpost".
  iSplit; last first.
  { iIntros (?). iApply fupd_mask_intro_discard; done. }
  iIntros "!> ((?&?&?&%&?) &?) /=". iFrame. done.
Qed.

Theorem adequacy_multiple_groups `{anerisPreG Σ Mdl}
        `{EqDecision (aneris_to_trace_model Mdl)} A
        (lbls: gset string)
        (obs_send_sas obs_rec_sas : gset socket_address_group)
        s (es : list aneris_expr) σ (φs : list (aneris_val → Prop)) :
  length es >= 1 →
  all_disjoint A →
  set_Forall is_ne A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  wp_group_proto_multiple A lbls obs_send_sas obs_rec_sas σ s es φs →
  state_heaps σ = gset_to_gmap ∅ $ get_ips es →
  state_sockets σ = gset_to_gmap ∅ $ get_ips es →
  state_ms σ = ∅ →
  adequate_multiple s es σ ((λ φ v _, φ v) <$> φs).
Proof.
  intros Hlen Hdisj Hne Hsendle Hrecvle
         HMdlfin Hwp Hheaps_dom Hsockets_dom Hms. simpl.
  eapply (adequacy_multiple_strong_groups A _ obs_send_sas obs_rec_sas); try done.
  { iIntros (aG) "!> HA Hhist Hσ HPs Hmdl Hns Halloc
      Hsend Hrecv Hsend_obs Hrecv_obs HSI".
    iMod (Hwp with "HA Hhist [HPs] Hmdl Hns Halloc Hsend Hrecv Hsend_obs Hrecv_obs HSI") as "$".
    by rewrite Hsockets_dom ports_in_use_empty_map difference_empty_L. }
  { by rewrite Hheaps_dom dom_gset_to_gmap. }
  { by rewrite Hsockets_dom dom_gset_to_gmap. }
  { intros ip ps Hps Sn HSn p Hp ??????.
    rewrite Hsockets_dom in HSn.
    rewrite lookup_gset_to_gmap_Some in HSn.
    destruct HSn as [HSn1 <-]. set_solver. }
  { intros i Sn HSn.
    rewrite Hsockets_dom in HSn.
    rewrite lookup_gset_to_gmap_Some in HSn.
    destruct HSn as [HSn1 <-]. done. }
  { intros i Sn HSn.
    rewrite Hsockets_dom in HSn.
    rewrite lookup_gset_to_gmap_Some in HSn.
    destruct HSn as [HSn1 <-]. done. }
  { intros i Sn HSn.
    rewrite Hsockets_dom in HSn.
    rewrite lookup_gset_to_gmap_Some in HSn.
    destruct HSn as [HSn1 <-]. done. }
Qed.

Theorem adequacy_multiple_strong `{anerisPreG Σ Mdl}
        `{EqDecision (aneris_to_trace_model Mdl)} A
        (lbls: gset string)
        (obs_send_sas obs_rec_sas : gset socket_address)
        s (es : list aneris_expr) σ (φs : list (aneris_val → Prop)) :
  length es >= 1 →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  wp_proto_multiple_strong A lbls obs_send_sas obs_rec_sas σ s es φs →
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
  adequate_multiple s es σ ((λ φ v _, φ v) <$> φs).
Proof.
  intros Hlen Hsendle Hrecvle.
  intros HMdlfin Hwp Hheaps_dom Hsockets_dom Hports Hsockets Hsockets_coh1 Hsockets_coh2 Hms. simpl.
  eapply (adequacy_multiple_strong_groups
                          (to_singletons A)
                          _
                          (to_singletons obs_send_sas) (to_singletons obs_rec_sas)
         ); eauto.
  { apply to_singletons_all_disjoint. }
  { apply to_singletons_is_ne. }
  { set_solver. }
  { set_solver. }
  iIntros (Mdl').
  iMod (Hwp Mdl') as "Hwp".
  iModIntro.
  iIntros "HA Hhist Hσ Hports Hfrag Hips Hlbls Hsend Hrecv Hsend_obs Hrecv_obs".
  iApply ("Hwp" with "HA [Hhist] Hσ [Hports] Hfrag Hips Hlbls [Hsend] [Hrecv] Hsend_obs Hrecv_obs").
  { iDestruct (big_sepS_to_singletons _
                                      (λ xs, xs ⤳*[ bool_decide (xs ∈ to_singletons obs_send_sas),
                                                      bool_decide (xs ∈ to_singletons obs_rec_sas)] (∅, ∅))%I
                                      (λ x, x ⤳[ bool_decide (x ∈ obs_send_sas),
                                                   bool_decide (x ∈ obs_rec_sas)] (∅, ∅))%I
                with "[] Hhist") as "Hhist".
    { iIntros "!>" (x) "Hx".
      iSplit; [| by iApply big_sepS_empty ].
      erewrite <-bool_decide_ext; last apply elem_of_to_singletons.
      erewrite <-(bool_decide_ext _ ({[x]} ∈ to_singletons obs_rec_sas)); last by apply elem_of_to_singletons. done. }
    done. }
  { by rewrite union_set_to_singletons. }
  { iDestruct (big_sepS_to_singletons _
                                      (λ xs, sendon_evs_groups xs [])%I
                                      (λ x, sendon_evs x [])%I
                with "[] Hsend") as "$".
    iIntros "!>" (x) "Hx". eauto. }
  { iDestruct (big_sepS_to_singletons _
                                      (λ xs, receiveon_evs_groups xs [])%I
                                      (λ x, receiveon_evs x [])%I
                with "[] Hrecv") as "$".
    iIntros "!>" (x) "Hx". eauto. }
  by rewrite union_set_to_singletons.
Qed.

Theorem adequacy_multiple `{anerisPreG Σ Mdl}
        `{EqDecision (aneris_to_trace_model Mdl)} A
        (lbls: gset string)
        (obs_send_sas obs_rec_sas : gset socket_address)
        s (es : list aneris_expr) σ (φs : list (aneris_val → Prop)) :
  length es >= 1 →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  wp_proto_multiple A lbls obs_send_sas obs_rec_sas σ s es φs →
  state_heaps σ = gset_to_gmap ∅ $ get_ips es →
  state_sockets σ = gset_to_gmap ∅ $ get_ips es →
  state_ms σ = ∅ →
  adequate_multiple s es σ ((λ φ v _, φ v) <$> φs).
Proof.
  intros Hlen Hsendle Hrecvle
         HMdlfin Hwp Hheaps_dom Hsockets_dom Hms. simpl.
  eapply (adequacy_multiple_strong A _ obs_send_sas obs_rec_sas); try done.
  { iIntros (aG) "!> HA Hhist Hσ HPs Hmdl Hns Halloc
      Hsend Hrecv Hsend_obs Hrecv_obs HSI".
    iMod (Hwp with "HA Hhist [HPs] Hmdl Hns Halloc Hsend Hrecv Hsend_obs Hrecv_obs HSI") as "$".
    by rewrite Hsockets_dom ports_in_use_empty_map difference_empty_L. }
  { by rewrite Hheaps_dom dom_gset_to_gmap. }
  { by rewrite Hsockets_dom dom_gset_to_gmap. }
  { intros ip ps Hps Sn HSn p Hp ??????.
    rewrite Hsockets_dom in HSn.
    rewrite lookup_gset_to_gmap_Some in HSn.
    destruct HSn as [HSn1 <-]. set_solver. }
  { intros i Sn HSn.
    rewrite Hsockets_dom in HSn.
    rewrite lookup_gset_to_gmap_Some in HSn.
    destruct HSn as [HSn1 <-]. done. }
  { intros i Sn HSn.
    rewrite Hsockets_dom in HSn.
    rewrite lookup_gset_to_gmap_Some in HSn.
    destruct HSn as [HSn1 <-]. done. }
  { intros i Sn HSn.
    rewrite Hsockets_dom in HSn.
    rewrite lookup_gset_to_gmap_Some in HSn.
    destruct HSn as [HSn1 <-]. done. }
Qed.

Theorem adequacy_groups `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)} IPs A
        (lbls: gset string)
        (obs_send_sas obs_rec_sas : gset socket_address_group)
        s e ip σ φ :
  all_disjoint A →
  set_Forall is_ne A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  wp_group_proto IPs A lbls obs_send_sas obs_rec_sas s e ip φ →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate s (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros Hdisj Hne Hsendle Hrecvle.
  intros HMdlfin Hwp Hip Hste Hsce Hmse.
  eapply (adequacy_xi _ _ _ _ (sim_rel (λ _ _, True))  _ _ _
                      (Mdl.(model_state_initial) : mstate (aneris_to_trace_model Mdl))).
  { by eapply aneris_sim_rel_finitary. }
  iIntros (?) "/=".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (unallocated_init A) as (γsif) "[Hunallocated_auth Hunallocated]".
  iMod (free_ips_init IPs) as (γips) "[HIPsCtx HIPs]".
  iMod (free_ports_auth_init ∅) as (γpiu) "HPiu". rewrite (fmap_empty GSet).
  iMod (allocated_address_groups_init obs_send_sas) as
      (γobserved_send) "#Hobserved_send".
  iMod (allocated_address_groups_init obs_rec_sas) as
      (γobserved_receive) "#Hobserved_receive".
  iMod (socket_address_group_ctx_init) as (γC) "Hauth"; [done|].
  iMod (socket_address_group_own_alloc_subseteq_pre _ A A with "Hauth") as
      "[Hauth HownA]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "HownA") as "#HownAS".
  iMod (messages_ctx_init A _ _ _ _ with "HownAS Hobserved_send Hobserved_receive" ) as (γms) "[Hms HB]".
  iMod steps_init as (γsteps) "[Hsteps _]".
  iMod (model_init Mdl.(model_state_initial)) as (γm) "[Hmfull Hmfrag]".
  assert (rtc Mdl Mdl.(model_state_initial) Mdl.(model_state_initial)).
  { constructor. }
  iMod (alloc_evs_init lbls) as (γalevs) "[Halobctx Halobs]".
  iMod (sendreceive_evs_init obs_send_sas) as
      (γsendevs) "[Hsendevsctx Hsendevs]".
  iMod (sendreceive_evs_init obs_rec_sas) as
    (γreceiveevs) "[Hreceiveevsctx Hreceiveevs]".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_socket_address_group_name := γC;
           aneris_unallocated_socket_address_groups_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           aneris_model_name := γm;
           aneris_steps_name := γsteps;
           aneris_allocEVS_name := γalevs;
           aneris_sendonEVS_name := γsendevs;
           aneris_receiveonEVS_name := γreceiveevs;
           aneris_observed_send_name := γobserved_send;
           aneris_observed_recv_name := γobserved_receive;
         |}).
  iMod (Hwp dg) as "Hwp".
  iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
  iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp #Hγn]"; [done|].
  iAssert (is_node ip) as "Hn".
  { iExists _. eauto. }
  iExists
    (λ ex atr,
      aneris_events_state_interp ex ∗
      aneris_state_interp
        (trace_last ex).2
        (trace_messages_history ex) ∗
      auth_st (trace_last atr) ∗
        ⌜valid_state_evolution ex atr⌝ ∗
        steps_auth (trace_length ex))%I, (λ _ _, True)%I, _, (λ _ _, True)%I.
  iSplitR; [iApply config_wp_correct|].
  iMod (socket_address_group_own_alloc_subseteq_pre _ A obs_send_sas with "Hauth")
    as "[Hauth Hown_send]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "Hown_send") as "Hown_send".
  iMod (socket_address_group_own_alloc_subseteq_pre _ A obs_rec_sas with "Hauth")
    as "[Hauth Hown_recv]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "Hown_recv") as "Hown_recv".
  iSplitR.
  { eauto. }
  iSplitR "Hwp Hunallocated HIPs HB Hmfrag Halobs Hsendevs Hreceiveevs Hown_send Hown_recv"; last first.
  {
    iDestruct ("Hwp" with "Hunallocated HB [$Hmfrag //] HIPs Hn Halobs [Hsendevs Hown_send] [Hreceiveevs Hown_recv] Hobserved_send Hobserved_receive") as "Hwp".
    { iApply big_sepS_sep. iFrame "Hsendevs Hown_send". }
    { iApply big_sepS_sep. iFrame "Hreceiveevs Hown_recv". }
    iMod "Hwp". iModIntro. iFrame.
    iIntros (???) "% % % % % % % (?& Hsi & Htr & % & Hauth) Hpost". iSplit; last first.
    { iIntros (?). iApply fupd_mask_intro_discard; done. }
    iIntros "!> ((?&?&?&%&?) &?) /=". iFrame. done. }
  iMod (socket_address_group_own_alloc_subseteq_pre _ A (obs_send_sas ∪ obs_rec_sas) with "Hauth")
    as "[Hauth Hown_send_recv]"; [by set_solver|].
  iPoseProof (aneris_events_state_interp_init with "[$] [$] [$] [$] [$] [$]") as "$".
  simpl.
  rewrite Hmse gset_of_gmultiset_empty.
  iMod (socket_address_group_own_alloc_subseteq_pre _ A A with "Hauth")
    as "[Hauth Hown]"; [by set_solver|].
  iPoseProof (@aneris_state_interp_init _ _ dg IPs
               with "Hmp [//] Hh Hs Hms [$Hauth $Hown] Hunallocated_auth Hsi HIPsCtx HPiu") as "$"; eauto.
  simpl.
  iFrame "Hmfull Hsteps".
  done.
Qed.

Theorem adequacy1 `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)} IPs A
        (lbls: gset string)
        (obs_send_sas obs_rec_sas : gset socket_address)
        s e ip σ φ :
  aneris_model_rel_finitary Mdl →
  wp_group_single_proto IPs A lbls obs_send_sas obs_rec_sas s e ip φ →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate s (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros HMdlfin Hwp Hsendle Hrecvle Hip Hste Hsce Hmse.
  eapply (adequacy_groups _
                         (to_singletons A)
                         _
                         (to_singletons obs_send_sas) (to_singletons obs_rec_sas)
         ); eauto.
  { apply to_singletons_all_disjoint. }
  { apply to_singletons_is_ne. }
  { set_solver. }
  { set_solver. }
  iIntros (Mdl').
  iMod (Hwp Mdl') as "Hwp".
  iModIntro.
  iIntros "Hfix HA Hfrag HIP Hnode Hlbls Hsend Hrecv Hsend_obs Hrecv_obs".
  iApply ("Hwp" with "Hfix [HA] Hfrag HIP Hnode Hlbls [Hsend] [Hrecv] Hsend_obs Hrecv_obs").
  { iDestruct (big_sepS_to_singletons _
      (λ xs, xs ⤳*[ bool_decide (xs ∈ to_singletons obs_send_sas),
                    bool_decide (xs ∈ to_singletons obs_rec_sas)] (∅, ∅))%I
      (λ x, x ⤳1[ bool_decide (x ∈ obs_send_sas),
                  bool_decide (x ∈ obs_rec_sas)] (∅, ∅))%I
                 with "[] HA") as "HA".
    { iIntros "!>" (x) "Hx".
      erewrite <-bool_decide_ext; last apply elem_of_to_singletons.
      erewrite <-(bool_decide_ext _ ({[x]} ∈ to_singletons obs_rec_sas)); last by apply elem_of_to_singletons.
      done. }
    done. }
  { iDestruct (big_sepS_to_singletons _
      (λ xs, sendon_evs_groups xs [])%I
      (λ x, sendon_evs x [])%I
                 with "[] Hsend") as "$".
    iIntros "!>" (x) "Hx". eauto. }
  { iDestruct (big_sepS_to_singletons _
      (λ xs, receiveon_evs_groups xs [])%I
      (λ x, receiveon_evs x [])%I
                 with "[] Hrecv") as "$".
    iIntros "!>" (x) "Hx". eauto. }
Qed.

Theorem adequacy `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)} IPs A
        (lbls: gset string)
        (obs_send_sas obs_rec_sas : gset socket_address)
        s e ip σ φ :
  aneris_model_rel_finitary Mdl →
  wp_proto IPs A lbls obs_send_sas obs_rec_sas s e ip φ →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  adequate s (mkExpr ip e) σ (λ v _, φ v).
Proof.
  intros HMdlfin Hwp Hsendle Hrecvle Hip Hste Hsce Hmse.
  eapply (adequacy_groups _
                         (to_singletons A)
                         _
                         (to_singletons obs_send_sas) (to_singletons obs_rec_sas)
         ); eauto.
  { apply to_singletons_all_disjoint. }
  { apply to_singletons_is_ne. }
  { set_solver. }
  { set_solver. }
  iIntros (Mdl').
  iMod (Hwp Mdl') as "Hwp".
  iModIntro.
  iIntros "Hfix HA Hfrag HIP Hnode Hlbls Hsend Hrecv Hsend_obs Hrecv_obs".
  iApply ("Hwp" with "Hfix [HA] Hfrag HIP Hnode Hlbls [Hsend] [Hrecv] Hsend_obs Hrecv_obs").
  { iDestruct (big_sepS_to_singletons _
      (λ xs, xs ⤳*[ bool_decide (xs ∈ to_singletons obs_send_sas),
                   bool_decide (xs ∈ to_singletons obs_rec_sas)] (∅, ∅))%I
      (λ x, x ⤳[ bool_decide (x ∈ obs_send_sas),
                 bool_decide (x ∈ obs_rec_sas)] (∅, ∅))%I
                 with "[] HA") as "HA".
    { iIntros "!>" (x) "Hx".
      iSplit; [| by iApply big_sepS_empty ].
      erewrite <-bool_decide_ext; last apply elem_of_to_singletons.
      erewrite <-(bool_decide_ext _ ({[x]} ∈ to_singletons obs_rec_sas)); last by apply elem_of_to_singletons. done. }
    done. }
  { iDestruct (big_sepS_to_singletons _
      (λ xs, sendon_evs_groups xs [])%I
      (λ x, sendon_evs x [])%I
                 with "[] Hsend") as "$".
    iIntros "!>" (x) "Hx". eauto. }
  { iDestruct (big_sepS_to_singletons _
      (λ xs, receiveon_evs_groups xs [])%I
      (λ x, receiveon_evs x [])%I
                 with "[] Hrecv") as "$".
    iIntros "!>" (x) "Hx". eauto. }
Qed.

Definition safe e σ := @adequate aneris_lang NotStuck e σ (λ _ _, True).

Theorem adequacy_groups_safe `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e ip σ :
  all_disjoint A →
  set_Forall (λ sag, sag ≠ ∅) A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  aneris_model_rel_finitary Mdl →
  wp_group_proto IPs A lbls obs_send_sas obs_rec_sas NotStuck e ip (λ _, True) →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  safe (mkExpr ip e) σ.
Proof. by apply adequacy_groups. Qed.

Theorem adequacy1_safe `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e ip σ :
  aneris_model_rel_finitary Mdl →
  wp_group_single_proto IPs A lbls obs_send_sas obs_rec_sas NotStuck e ip (λ _, True) →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  safe (mkExpr ip e) σ.
Proof. by apply adequacy1. Qed.

Theorem adequacy_safe `{anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
        IPs A lbls obs_send_sas obs_rec_sas e ip σ :
  aneris_model_rel_finitary Mdl →
  wp_proto IPs A lbls obs_send_sas obs_rec_sas NotStuck e ip (λ _, True) →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  ip ∉ IPs →
  state_heaps σ = {[ip:=∅]} →
  state_sockets σ = {[ip:=∅]} →
  state_ms σ = ∅ →
  safe (mkExpr ip e) σ.
Proof. by apply adequacy. Qed.

Definition simulation_adequacy_with_trace_inv_groups `{!anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
           (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A obs_send_sas obs_rec_sas : gset socket_address_group)
           (ξ: execution_trace aneris_lang → auxiliary_trace (aneris_to_trace_model Mdl) → Prop)
           (φ: language.val aneris_lang → Prop)
           ip e1 σ1 :
  all_disjoint A →
  set_Forall (λ sag, sag ≠ ∅) A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  rel_finitary (sim_rel ξ) ->
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
      ⊢ |={⊤}=>
        (* There exists a trace invariant and a socket interpretation function *)
     ∃ (trace_inv : execution_trace aneris_lang → auxiliary_trace _ → iProp Σ)
       (Φ : language.val aneris_lang → iProp Σ),
     (* Given resources reflecting initial configuration, we need to prove two goals *)
     unallocated_groups A -∗
     ([∗ set] b ∈ A, b ⤳*[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs_groups sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs_groups sa []) -∗
     observed_send_groups obs_send_sas -∗
     observed_receive_groups obs_rec_sas -∗
     frag_st Mdl.(model_state_initial) ={⊤}=∗
     (∀ v, Φ v -∗ ⌜φ v⌝) ∗
     WP (mkExpr ip e1) @ s; (ip,0); ⊤ {{ Φ }} ∗
     (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) c3,
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
         ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
         ⌜trace_ends_in ex c3⌝ -∗
         ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
         state_interp ex atr -∗
         posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
         □ (state_interp ex atr ∗
           (∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
            ={⊤}=∗ state_interp ex atr ∗ trace_inv ex atr) ∗
           ((∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
     ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  (* The coinductive pure coq proposition given by adequacy *)
  (continued_simulation ξ (trace_singleton ([(mkExpr ip e1)], σ1))
                          (trace_singleton Mdl.(model_state_initial)) ∧
     adequate s (mkExpr ip e1) σ1 (λ v _, φ v)).
Proof.
  intros Hdisj Hne Hsendle Hrecvle.
  intros Hsc Hips Hheaps Hsockets Hms Hwp.
  epose proof (sim_and_adequacy_xi _ _ Σ s (sim_rel ξ) φ (mkExpr ip e1) σ1 Mdl.(model_state_initial) Hsc _)
    as [? ?] =>//.
  split; [|done].
  eapply continued_simulation_impl; [|done].
  by intros ? ? [? ?]. Unshelve.
  iIntros (?) "".
  iMod node_gnames_auth_init as (γmp) "Hmp".
  iMod saved_si_init as (γsi) "[Hsi Hsi']".
  iMod (unallocated_init A) as (γsif) "[Hunallocated_auth Hunallocated]".
  iMod (free_ips_init IPs) as (γips) "[HIPsCtx HIPs]".
  iMod (free_ports_auth_init ∅) as (γpiu) "HPiu". rewrite (fmap_empty GSet).
  iMod (allocated_address_groups_init obs_send_sas) as
      (γobserved_send) "#Hobserved_send".
  iMod (allocated_address_groups_init obs_rec_sas) as
      (γobserved_receive) "#Hobserved_receive".
  iMod (socket_address_group_ctx_init) as (γC) "Hauth"; [done|].
  iMod (socket_address_group_own_alloc_subseteq_pre _ A A with "Hauth") as
      "[Hauth HownA]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "HownA") as "HownAS".
  iMod (messages_ctx_init A _ _ _ _ with "HownAS Hobserved_send Hobserved_receive" ) as (γms) "[Hms HB]".
  iMod steps_init as (γsteps) "[Hsteps _]".
  iMod (model_init Mdl.(model_state_initial)) as (γm) "[Hmfull Hmfrag]".
  assert (rtc Mdl Mdl.(model_state_initial) Mdl.(model_state_initial)).
  { constructor. }
  iMod (alloc_evs_init lbls) as (γalevs) "[Halobctx Halobs]".
  iMod (sendreceive_evs_init obs_send_sas) as
      (γsendevs) "[Hsendevsctx Hsendevs]".
  iMod (sendreceive_evs_init obs_rec_sas) as
      (γreceiveevs) "[Hreceiveevsctx Hreceiveevs]".
  set (dg :=
         {|
           aneris_node_gnames_name := γmp;
           aneris_si_name := γsi;
           aneris_socket_address_group_name := γC;
           aneris_unallocated_socket_address_groups_name := γsif;
           aneris_freeips_name := γips;
           aneris_freeports_name := γpiu;
           aneris_messages_name := γms;
           aneris_model_name := γm;
           aneris_steps_name := γsteps;
           aneris_allocEVS_name := γalevs;
           aneris_sendonEVS_name := γsendevs;
           aneris_receiveonEVS_name := γreceiveevs;
           aneris_observed_send_name := γobserved_send;
           aneris_observed_recv_name := γobserved_receive;
         |}).
  iMod (Hwp dg) as "Hwp". iDestruct "Hwp" as (trace_inv Φ) "Himpl".
  iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
  iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp #Hγn]"; [done|].
  iAssert (is_node ip) as "Hn".
  { iExists _. eauto. }
  iMod (socket_address_group_own_alloc_subseteq_pre _ A obs_send_sas with "Hauth")
    as "[Hauth Hown_send]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "Hown_send") as "Hown_send".
  iMod (socket_address_group_own_alloc_subseteq_pre _ A obs_rec_sas with "Hauth")
    as "[Hauth Hown_recv]"; [done|].
  iDestruct (socket_address_group_own_big_sepS with "Hown_recv") as "Hown_recv".
  iMod ("Himpl" with "[$] [$] [$] [$] [$] [Hsendevs Hown_send]
[Hreceiveevs Hown_recv] [$] [$] [$Hmfrag //]") as "(HΦ & Hwp & Himpl)".
  { iApply big_sepS_sep. iFrame "Hsendevs Hown_send". }
  { iApply big_sepS_sep. iFrame "Hreceiveevs Hown_recv". }
  iMod (socket_address_group_own_alloc_subseteq_pre _ A (obs_send_sas ∪ obs_rec_sas) with "Hauth")
    as "[Hauth Hown_send_recv]"; [by set_solver|].
  iMod (socket_address_group_own_alloc_subseteq_pre _ A A with "Hauth")
    as "[Hauth Hown]"; [by set_solver|].
  iModIntro. iExists state_interp, trace_inv, Φ, fork_post.
  iSplitL ""; first by iApply config_wp_correct.
  iFrame "Hwp HΦ".
  iPoseProof (aneris_events_state_interp_init with "[$] [$] [$] [$] [$] [$]") as "$".
  iPoseProof (@aneris_state_interp_init _ _ dg IPs
               with "Hmp [//] Hh Hs Hms [$Hauth $Hown] Hunallocated_auth Hsi HIPsCtx HPiu") as "Hsi"; eauto; [].
  rewrite /= Hms gset_of_gmultiset_empty.
  iFrame. iSplit; [done|].
  iIntros (??????? Hcontr ??) "(Hev & Hsi & Hauth & % & Hsteps) Hpost".
  iDestruct ("Himpl" with "[//] [//] [//] [//] [] [//] [$Hev $Hsi $Hauth $Hsteps //] [$Hpost]") as "[$ Hrel]".
  { iPureIntro. intros ??????. by eapply Hcontr. }
  iIntros "Hct". iMod ("Hrel" with "Hct") as "%".
  iModIntro. eauto.
Qed.

Definition simulation_adequacy1_with_trace_inv Σ Mdl `{!anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
           (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A obs_send_sas obs_rec_sas : gset socket_address)
           (ξ: execution_trace aneris_lang → auxiliary_trace (aneris_to_trace_model Mdl) → Prop)
           (φ: language.val aneris_lang → Prop)
           ip e1 σ1 :
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  (* The model has finite branching *)
  rel_finitary (sim_rel ξ) →
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
      ⊢ |={⊤}=>
        (* There exists a trace invariant, a postcondition and a socket interpretation function *)
     ∃ (trace_inv : execution_trace aneris_lang → auxiliary_trace _ → iProp Σ)
       (Φ : language.val aneris_lang → iProp Σ),
       (* Given resources reflecting initial configuration, we need to prove two goals *)
       unallocated A -∗
       ([∗ set] b ∈ A, b ⤳1[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
       ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
       ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
       ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
       ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
       observed_send obs_send_sas -∗
       observed_receive obs_rec_sas -∗
       frag_st Mdl.(model_state_initial) ={⊤}=∗
       (∀ v, Φ v -∗ ⌜φ v⌝) ∗
       WP (mkExpr ip e1) @ s; (ip, 0); ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) c3,
           ⌜valid_system_trace ex atr⌝ -∗
           ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
           ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
           ⌜trace_ends_in ex c3⌝ -∗
           ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
      ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
      state_interp ex atr -∗
      posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
      □ (state_interp ex atr ∗
          (∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
         ={⊤}=∗ state_interp ex atr ∗ trace_inv ex atr) ∗
      ((∀ ex' atr' oζ ℓ,
           ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
       ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  (* The coinductive pure coq proposition given by adequacy *)
  (continued_simulation ξ (trace_singleton ([(mkExpr ip e1)], σ1))
                          (trace_singleton Mdl.(model_state_initial)) ∧
     adequate s (mkExpr ip e1) σ1 (λ v _, φ v)).
Proof.
  intros Hsendle Hrecvle Hsc Hips Hheaps Hsockets Hms Hwp.
  eapply (simulation_adequacy_with_trace_inv_groups _ _ _
                         (to_singletons A)
                         (to_singletons obs_send_sas) (to_singletons obs_rec_sas)); eauto.
  { apply to_singletons_all_disjoint. }
  { apply to_singletons_is_ne. }
  { set_solver. }
  { set_solver. }
  iIntros (Mdl').
  iMod (Hwp Mdl') as (trace_inv Φ) "Hwp".
  iModIntro.
  iExists trace_inv, Φ.
  iIntros "Hfix HA HIP Hnode Hlbls Hsend Hrecv Hsend_obs Hrecv_obs Hfrag".
  iApply ("Hwp" with "Hfix [HA] HIP Hnode Hlbls [Hsend] [Hrecv] Hsend_obs Hrecv_obs Hfrag").
  { iDestruct (big_sepS_to_singletons _
      (λ xs, xs ⤳*[ bool_decide (xs ∈ to_singletons obs_send_sas),
                    bool_decide (xs ∈ to_singletons obs_rec_sas)] (∅, ∅))%I
      (λ x, x ⤳1[ bool_decide (x ∈ obs_send_sas),
                  bool_decide (x ∈ obs_rec_sas)] (∅, ∅))%I
                 with "[] HA") as "HA".
    { iIntros "!>" (x) "Hx".
      erewrite <-bool_decide_ext; last apply elem_of_to_singletons.
      erewrite <-(bool_decide_ext _ ({[x]} ∈ to_singletons obs_rec_sas)); last by apply elem_of_to_singletons.
      done. }
    done. }
  { iDestruct (big_sepS_to_singletons _
      (λ xs, sendon_evs_groups xs [])%I
      (λ x, sendon_evs x [])%I
                 with "[] Hsend") as "$".
    iIntros "!>" (x) "Hx". eauto. }
  { iDestruct (big_sepS_to_singletons _
      (λ xs, receiveon_evs_groups xs [])%I
      (λ x, receiveon_evs x [])%I
                 with "[] Hrecv") as "$".
    iIntros "!>" (x) "Hx". eauto. }
Qed.

Definition simulation_adequacy_with_trace_inv `{!anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
           (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A obs_send_sas obs_rec_sas : gset socket_address)
           (ξ: execution_trace aneris_lang → auxiliary_trace (aneris_to_trace_model Mdl) → Prop)
           (φ: language.val aneris_lang → Prop)
           ip e1 σ1 :
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  (* The model has finite branching *)
  rel_finitary (sim_rel ξ) ->
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
      ⊢ |={⊤}=>
        (* There exists a trace invariant, a postcondition and a socket interpretation function *)
     ∃ (trace_inv : execution_trace aneris_lang → auxiliary_trace _ → iProp Σ)
       (Φ : language.val aneris_lang → iProp Σ),
       (* Given resources reflecting initial configuration, we need to prove two goals *)
       unallocated A -∗
       ([∗ set] b ∈ A, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
       ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
       ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
       ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
       ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
       observed_send obs_send_sas -∗
       observed_receive obs_rec_sas -∗
       frag_st Mdl.(model_state_initial) ={⊤}=∗
       (∀ v, Φ v -∗ ⌜φ v⌝) ∗
       WP (mkExpr ip e1) @ s; (ip, 0); ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) c3,
           ⌜valid_system_trace ex atr⌝ -∗
           ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
           ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
           ⌜trace_ends_in ex c3⌝ -∗
           ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
      ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
      state_interp ex atr -∗
      posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
      □ (state_interp ex atr ∗
         (∀ ex' atr' oζ ℓ, ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
          ={⊤}=∗ state_interp ex atr ∗ trace_inv ex atr) ∗
      ((∀ ex' atr' oζ ℓ,
          ⌜trace_contract ex oζ ex'⌝ → ⌜trace_contract atr ℓ atr'⌝ → trace_inv ex' atr')
       ={⊤, ∅}=∗ ⌜ξ ex atr⌝))) →
  (* The coinductive pure coq proposition given by adequacy *)
  (continued_simulation ξ (trace_singleton ([(mkExpr ip e1)], σ1))
                          (trace_singleton Mdl.(model_state_initial)) ∧
   adequate s (mkExpr ip e1) σ1 (λ v _, φ v)).
Proof.
  intros Hsendle Hrecvle Hsc Hips Hheaps Hsockets Hms Hwp.
  eapply (simulation_adequacy_with_trace_inv_groups _ _ _
                         (to_singletons A)
                         (to_singletons obs_send_sas) (to_singletons obs_rec_sas)
         ); eauto.
  { apply to_singletons_all_disjoint. }
  { apply to_singletons_is_ne. }
  { set_solver. }
  { set_solver. }
  iIntros (Mdl').
  iMod (Hwp Mdl') as (trace_inv Φ) "Hwp".
  iModIntro.
  iExists trace_inv, Φ.
  iIntros "Hfix HA HIP Hnode Hlbls Hsend Hrecv Hsend_obs Hrecv_obs Hfrag".
  iApply ("Hwp" with "Hfix [HA] HIP Hnode Hlbls [Hsend] [Hrecv] Hsend_obs Hrecv_obs Hfrag").
  { iDestruct (big_sepS_to_singletons _
      (λ xs, xs ⤳*[ bool_decide (xs ∈ to_singletons obs_send_sas),
                    bool_decide (xs ∈ to_singletons obs_rec_sas)] (∅, ∅))%I
      (λ x, x ⤳[ bool_decide (x ∈ obs_send_sas),
                 bool_decide (x ∈ obs_rec_sas)] (∅, ∅))%I
                 with "[] HA") as "HA".
    { iIntros "!>" (x) "Hx".
      iSplit; [|by iApply big_sepS_empty].
      erewrite <-bool_decide_ext; last apply elem_of_to_singletons.
      erewrite <-(bool_decide_ext _ ({[x]} ∈ to_singletons obs_rec_sas)); last by apply elem_of_to_singletons.
      done. }
    done. }
  { iDestruct (big_sepS_to_singletons _
      (λ x, sendon_evs_groups x [])%I
      (λ x, sendon_evs x [])%I
                 with "[] Hsend") as "$".
    iIntros "!>" (x) "Hx". eauto. }
  { iDestruct (big_sepS_to_singletons _
      (λ x, receiveon_evs_groups x [])%I
      (λ x, receiveon_evs x [])%I
                 with "[] Hrecv") as "$".
    iIntros "!>" (x) "Hx". eauto. }
Qed.

Definition simulation_adequacy_groups Σ Mdl `{!anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
           (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A obs_send_sas obs_rec_sas : gset socket_address_group)
           (ξ: execution_trace aneris_lang → auxiliary_trace (aneris_to_trace_model Mdl) → Prop)
           ip e1 σ1 :
  all_disjoint A →
  set_Forall (λ sag, sag ≠ ∅) A →
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  (* The model has finite branching *)
  rel_finitary (sim_rel ξ) →
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
      ⊢ |={⊤}=>
        (* There exists a postcondition and a socket interpretation function *)
     ∃ (Φ : language.val aneris_lang → iProp Σ)
       (f : socket_address_group → socket_interp Σ),
     (* Given resources reflecting initial configuration, we need *)
     (* to prove two goals *)
       unallocated_groups A -∗
       ([∗ set] b ∈ A, b ⤳*[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
       ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
       ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
       ([∗ set] sa ∈ obs_send_sas, sendon_evs_groups sa []) -∗
       ([∗ set] sa ∈ obs_rec_sas, receiveon_evs_groups sa []) -∗
       observed_send_groups obs_send_sas -∗
       observed_receive_groups obs_rec_sas -∗
       frag_st Mdl.(model_state_initial) ={⊤}=∗
       WP (mkExpr ip e1) @ s; (ip,0); ⊤ {{ Φ }} ∗
       (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) c3,
         ⌜valid_system_trace ex atr⌝ -∗
         ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
         ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
         ⌜trace_ends_in ex c3⌝ -∗
         ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
         ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
         state_interp ex atr -∗
         posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
         |={⊤, ∅}=> ⌜ξ ex atr⌝)) →
  (* The coinductive pure coq proposition given by adequacy *)
  continued_simulation
    ξ
    (trace_singleton ([(mkExpr ip e1)], σ1))
    (trace_singleton Mdl.(model_state_initial)).
Proof.
  intros Hdisj Hne Hsendle Hrecvle.
  intros Hsc Hips Hheaps Hsockets Hms Hwp.
  eapply (simulation_adequacy_with_trace_inv_groups
          _ _ _ A obs_send_sas obs_rec_sas ξ (λ _, True)) =>//.
  iIntros (?) "".
  iMod Hwp as (Φ f) "Hwp".
  iModIntro.
  iExists (λ _ _, True)%I, Φ.
  iIntros "? ? ? ? ? ? ? ? ? ?".
  iMod ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "[$ Hstep]".
  iModIntro.
  iSplitR; [eauto|].
  iIntros (ex atr c3 ? ? ? ? ? ?) "HSI Hposts".
  iSplit; last first.
  { iIntros "_". iApply ("Hstep" with "[] [] [] [] [] [] HSI"); auto. }
  iModIntro; iIntros "[$ _]"; done.
Qed.

Definition simulation_adequacy1 Σ Mdl `{!anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
           (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A obs_send_sas obs_rec_sas : gset socket_address)
           (ξ: execution_trace aneris_lang → auxiliary_trace (aneris_to_trace_model Mdl) → Prop)
           ip e1 σ1 :
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  (* The model has finite branching *)
  rel_finitary (sim_rel ξ) →
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
     ⊢ |={⊤}=>
        (* There exists a postcondition and a socket interpretation function *)
     ∃ (Φ : language.val aneris_lang → iProp Σ)
       (f : socket_address → socket_interp Σ),
     (* Given resources reflecting initial configuration, we need *)
     (* to prove two goals *)
     unallocated A -∗
     ([∗ set] b ∈ A, b ⤳1[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     frag_st Mdl.(model_state_initial) ={⊤}=∗
     WP (mkExpr ip e1) @ s; (ip,0); ⊤ {{ Φ }} ∗
     (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) c3,
       ⌜valid_system_trace ex atr⌝ -∗
       ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
       ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
       ⌜trace_ends_in ex c3⌝ -∗
       ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
       ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
       state_interp ex atr -∗
       posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
       |={⊤, ∅}=> ⌜ξ ex atr⌝)) →
  (* The coinductive pure coq proposition given by adequacy *)
  continued_simulation
    ξ
    (trace_singleton ([(mkExpr ip e1)], σ1))
    (trace_singleton Mdl.(model_state_initial)).
Proof.
  intros Hsendle Hrecvle Hsc Hips Hheaps Hsockets Hms Hwp.
  eapply (simulation_adequacy1_with_trace_inv
          _ _ _ _ _ A obs_send_sas obs_rec_sas ξ (λ _, True))=>//.
  iIntros (?) "".
  iMod Hwp as (Φ f) "Hwp".
  iModIntro.
  iExists (λ _ _, True)%I, Φ.
  iIntros "? ? ? ? ? ? ? ? ? ?".
  iMod ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "[$ Hstep]".
  iModIntro.
  iSplitR; [eauto|].
  iIntros (ex atr c3 ? ? ? ? ? ? ) "HSI Hposts".
  iSplit; last first.
  { iIntros "_". iApply ("Hstep" with "[] [] [] [] [] [] HSI"); auto. }
  iModIntro; iIntros "[$ _]"; done.
Qed.

Definition simulation_adequacy Σ Mdl `{!anerisPreG Σ Mdl} `{EqDecision (aneris_to_trace_model Mdl)}
           (s: stuckness)
           (IPs: gset ip_address)
           (lbls : gset string)
           (A obs_send_sas obs_rec_sas : gset socket_address)
           (φ : language.val aneris_lang → Prop)
           (ξ: execution_trace aneris_lang → auxiliary_trace (aneris_to_trace_model Mdl) → Prop)
           ip e1 σ1 :
  obs_send_sas ⊆ A → obs_rec_sas ⊆ A →
  (* The model has finite branching *)
  rel_finitary (sim_rel ξ) →
  (* The initial configuration satisfies certain properties *)
  ip ∉ IPs →
  state_heaps σ1 = {[ip:=∅]} →
  state_sockets σ1 = {[ip:=∅]} →
  state_ms σ1 = ∅ →
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!anerisG Mdl Σ},
     ⊢ |={⊤}=>
     (* There exists a postcondition and a socket interpretation function *)
     ∃ Φ,
     (* Given resources reflecting initial configuration, we need *)
     (* to prove two goals *)
     unallocated A -∗
     ([∗ set] b ∈ A, b ⤳[bool_decide (b ∈ obs_send_sas), bool_decide (b ∈ obs_rec_sas)] (∅, ∅)) -∗
     ([∗ set] i ∈ IPs, free_ip i) -∗ is_node ip -∗
     ([∗ set] lbl ∈ lbls, alloc_evs lbl []) -∗
     ([∗ set] sa ∈ obs_send_sas, sendon_evs sa []) -∗
     ([∗ set] sa ∈ obs_rec_sas, receiveon_evs sa []) -∗
     observed_send obs_send_sas -∗
     observed_receive obs_rec_sas -∗
     frag_st Mdl.(model_state_initial) ={⊤}=∗
     (∀ v, Φ v -∗ ⌜φ v⌝) ∗
     WP (mkExpr ip e1) @ s; (ip,0); ⊤ {{ Φ }} ∗
     (∀ (ex : execution_trace aneris_lang) (atr : auxiliary_trace (aneris_to_trace_model Mdl)) c3,
       ⌜valid_system_trace ex atr⌝ -∗
       ⌜trace_starts_in ex ([mkExpr ip e1], σ1)⌝ -∗
       ⌜trace_starts_in atr Mdl.(model_state_initial)⌝ -∗
       ⌜trace_ends_in ex c3⌝ -∗
       ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' atr'⌝ -∗
       ⌜∀ e2, s = NotStuck → e2 ∈ c3.1 → not_stuck e2 c3.2⌝ -∗
       state_interp ex atr -∗
       posts_of c3.1 (Φ :: (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [mkExpr ip e1] (drop (length [mkExpr ip e1]) c3.1)))) -∗
       |={⊤, ∅}=> ⌜ξ ex atr⌝)) →
  (* The coinductive pure coq proposition given by adequacy *)
  (continued_simulation
    ξ
    (trace_singleton ([(mkExpr ip e1)], σ1))
    (trace_singleton Mdl.(model_state_initial)) ∧
     adequate s (mkExpr ip e1) σ1 (λ v _, φ v)).
Proof.
  intros Hsendle Hrecvle Hsc Hips Hheaps Hsockets Hms Hwp.
  eapply (simulation_adequacy_with_trace_inv
          _ _ _ A obs_send_sas obs_rec_sas)=>//.
  iIntros (?) "".
  iMod Hwp as (Φ) "Hwp".
  iModIntro.
  iExists (λ _ _, True)%I, Φ.
  iIntros "? ? ? ? ? ? ? ? ? ?".
  iMod ("Hwp" with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "($ & $ & Hstep)".
  iModIntro.
  iIntros (ex atr c3 ? ? ? ? ? ?) "HSI Hposts".
  iSplit; last first.
  { iIntros "_". iApply ("Hstep" with "[] [] [] [] [] [] HSI"); auto. }
  iModIntro; iIntros "[$ _]"; done.
Qed.
