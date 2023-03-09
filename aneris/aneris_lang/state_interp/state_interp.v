From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From iris.algebra Require Import auth excl.
From aneris.prelude Require Import collect gset_map gmultiset.
From trillium.program_logic Require Export weakestpre.
From aneris.lib Require Import gen_heap_light.
From aneris.algebra Require Import disj_gsets.
From aneris.aneris_lang Require Export
     aneris_lang network resources events.
From aneris.aneris_lang.state_interp Require Export
     state_interp_def
     state_interp_local_coh
     state_interp_gnames_coh
     state_interp_free_ips_coh
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_resource_coh
     state_interp_messages_history_coh
     state_interp_config_wp
     state_interp_messages_history.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  (** aneris_state_interp *)
  Lemma mapsto_node_heap_valid n γs σ mh :
    aneris_state_interp σ mh -∗
    mapsto_node n γs -∗
    ∃ h, ⌜state_heaps σ !! n = Some h⌝.
  Proof.
    iDestruct 1 as (Mγ ?????) "(Hnauth & Hscoh & Hlcoh & Hfip & Hmrcoh)".
    iIntros "Hn".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %Hninm.
    iDestruct (local_state_coh_heaps with "Hlcoh") as (h) "%"; [done|].
    eauto.
  Qed.

  Lemma is_node_heap_valid n σ mh:
    aneris_state_interp σ mh -∗
    is_node n -∗
    ∃ h, ⌜state_heaps σ !! n = Some h⌝.
  Proof.
    iIntros "Hσ". iDestruct 1 as (γs) "Hn".
    iApply (mapsto_node_heap_valid with "[$] [$]").
  Qed.

  Lemma mapsto_node_valid_sockets n γs σ mh:
    aneris_state_interp σ mh -∗
    mapsto_node n γs -∗
    ∃ Sn, ⌜state_sockets σ !! n = Some Sn⌝.
  Proof.
    iDestruct 1 as (Mγ ?????) "(Hnauth & Hscoh & Hlcoh & Hfip & Hmrcoh)".
    iIntros "Hn".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %Hninm.
    iDestruct (local_state_coh_sockets with "Hlcoh") as (h) "%"; [done|].
    eauto.
  Qed.

  Lemma is_node_valid_sockets n σ mh:
    aneris_state_interp σ mh -∗
    is_node n -∗
    ∃ Sn, ⌜state_sockets σ !! n = Some Sn⌝.
  Proof.
    iIntros "Hσ". iDestruct 1 as (γs) "Hn".
    iApply (mapsto_node_valid_sockets with "[$] [$]").
  Qed.

  Definition addrs_to_ip_ports_map (A : gset socket_address) :
    gmap ip_address (gset port) :=
    ∅.

  (** free_ips_coh *)
  Lemma free_ips_coh_init ips Ps σ :
    dom Ps ## ips →
    (∀ ip, ip ∈ ips → ip_is_free ip σ) →
    ((∀ ip ps, Ps !! ip = Some (GSet ps) →
              ∀ Sn, (state_sockets σ) !! ip = Some Sn →
                    ∀ p, p ∈ ps → port_not_in_use p Sn)) →   
    free_ips_auth ips ∗ free_ports_auth Ps -∗
    free_ips_coh σ.
  Proof.
    iIntros (Hdisj Hip Hnuse) "[HipsCtx HPiu]".
    iExists _, _; iFrame.
    iPureIntro. done.
  Qed.

  (* (* aneris_state_interp *) *)
  (* Lemma aneris_state_interp_init A fips σ γs : *)
  (*   (* Free Ips [fips] are disjoint from initial allocted nodes *)
  (*      [dom (state_heaps σ]) *) *)
  (*   fips ## dom (state_heaps σ) → *)
  (*   (* dom (addrs_to_ip_ports_map (union_set A)) → *) *)
  (*   (∀ ip : ip_address, ip ∈ fips → ip_is_free ip σ) → *)
  (*   dom (state_sockets σ) = dom (state_heaps σ) → *)
  (*   dom γs =dom (state_heaps σ) → *)
  (*   dom (state_heaps σ) = dom (addrs_to_ip_ports_map (union_set A)) → *)
  (*   dom (state_sockets σ) = dom (addrs_to_ip_ports_map (union_set A)) → *)
  (*   map_Forall (λ _ σh, σh = ∅) (state_heaps σ) → *)
  (*   map_Forall (λ _ skts, skts = ∅) (state_sockets σ) → *)
  (*   state_ms σ = ∅ → *)
  (*   node_gnames_auth γs -∗ *)
  (*   ([∗ map] ip↦γ ∈ γs, mapsto_node ip γ ∗ heap_ctx γ ∅ ∗ sockets_ctx γ ∅) -∗ *)
  (*   messages_ctx (gset_to_gmap (∅, ∅) A)  -∗ *)
  (*   socket_address_group_ctx A -∗ *)
  (*   unallocated_groups_auth A -∗ *)
  (*   saved_si_auth ∅ -∗ *)
  (*   free_ips_auth fips -∗ *)
  (*   free_ports_auth (GSet <$> addrs_to_ip_ports_map (union_set A)) -∗ *)
  (*   aneris_state_interp σ (∅, ∅). *)
  (* Proof. *)
  (*    iIntros (Hfips Hfips' Hfips'' Hheap Hskt Hheaps Hskts Hms) *)
  (*           "Hγs_auth Hγs Hm Hsags Hunallocated Hsif HipsCtx HPiu_auth". *)
  (*   iDestruct (socket_address_group_ctx_valid with "Hsags") as %[Hdisj Hne]. *)
  (*   iExists _, _; iFrame. *)
  (*   iSplit. *)
  (*   (* messages_received_sent *) *)
  (*   { iPureIntro. apply messages_received_sent_init. } *)
  (*   iSplit. *)
  (*   (* gnames_coh *) *)
  (*   { iPureIntro. *)
  (*     (* TODO: Dont break abstraction here. *) *)
  (*     by rewrite /gnames_coh Hheap Hskt. } *)
  (*   iSplitR. *)
  (*   (* network_sockets_coh *) *)
  (*   { iPureIntro. *)
  (*     (* TODO: Dont break abstraction here. *) *)
  (*     rewrite /network_sockets_coh. *)
  (*     intros ip Sn HSome. apply Hskts in HSome as ->. *)
  (*     split. *)
  (*     { rewrite /socket_handlers_coh. set_solver. } *)
  (*     split. *)
  (*     { rewrite /socket_messages_coh. set_solver. } *)
  (*     split. *)
  (*     { rewrite /socket_addresses_coh. set_solver. } *)
  (*     rewrite /socket_unbound_empty_buf_coh. set_solver. } *)
  (*   iSplitR. *)
  (*   (* messages_history_coh *) *)
  (*   { iPureIntro. *)
  (*     (* TODO: Dont break abstraction here. *) *)
  (*     rewrite /messages_history_coh. rewrite Hms. *)
  (*     split. *)
  (*     { rewrite /message_soup_coh. set_solver. } *)
  (*     split. *)
  (*     { rewrite /receive_buffers_coh. *)
  (*       intros ip Sn sh skt r m HSome. apply Hskts in HSome as ->. *)
  (*       set_solver. } *)
  (*     split. *)
  (*     { rewrite /messages_addresses_coh. *)
  (*       rewrite dom_gset_to_gmap. *)
  (*       split; [done|]. *)
  (*       split; [set_solver|]. *)
  (*       intros sag R T HSome. rewrite lookup_gset_to_gmap_Some in HSome. *)
  (*       destruct HSome. set_solver. } *)
  (*     rewrite /messages_received_from_sent_coh. *)
  (*     rewrite messages_received_init messages_sent_init. set_solver. } *)
  (*   (* socket_interp_coh *) *)
  (*   iDestruct (socket_address_groups_ctx_own with "Hsags") as "#Hsags'". *)
  (*   iSplitL "Hsags Hunallocated Hsif". *)
  (*   { by iApply (socket_interp_coh_init with "Hsags Hunallocated Hsif"). } *)
  (*   iSplitL "Hγs". *)
  (*   (* local_state_coh *) *)
  (*   { iApply (big_sepM_impl with "Hγs"). *)
  (*     iIntros "!>" (k x HSome) "(Hnode & Hheap & Hskt)". *)
  (*     assert (is_Some ((state_heaps σ) !! k)) as [y HSomey]. *)
  (*     { apply elem_of_dom. rewrite Hheap. apply elem_of_dom. by exists x. } *)
  (*     assert (is_Some ((state_sockets σ) !! k)) as [z HSomez]. *)
  (*     { apply elem_of_dom. rewrite Hskt. apply elem_of_dom. by exists x. } *)
  (*     iExists _, _. *)
  (*     iSplit; [done|].  *)
  (*     iSplit; [done|]. *)
  (*     apply Hheaps in HSomey as ->. *)
  (*     apply Hskts in HSomez as ->. *)
  (*     rewrite fmap_empty. *)
  (*     iFrame. } *)
  (*   iSplitL "HipsCtx HPiu_auth". *)
  (*   (* free_ips_coh *) *)
  (*   { by iApply (free_ips_coh_init with "[$]"). } *)
  (*   (* messages_resource_coh *) *)
  (*   iApply messages_resource_coh_init. *)
  (*   iFrame "#". *)
  (* Qed. *)


  (* aneris_state_interp *)
  Lemma aneris_state_interp_init fips A σ γs :
    fips ## dom γs →
    fips ## dom (addrs_to_ip_ports_map (union_set A)) →
    (∀ ip : ip_address, ip ∈ fips → ip_is_free ip σ) →
    dom (state_heaps σ) = dom γs →
    dom (state_sockets σ) = dom γs →
    map_Forall (λ _ σh, σh = ∅) (state_heaps σ) →
    map_Forall (λ _ skts, skts = ∅) (state_sockets σ) →
    state_ms σ = ∅ →
    node_gnames_auth γs -∗
    ([∗ map] ip↦γ ∈ γs, mapsto_node ip γ ∗ heap_ctx γ ∅ ∗ sockets_ctx γ ∅) -∗
    messages_ctx (gset_to_gmap (∅, ∅) A)  -∗
    socket_address_group_ctx A -∗
    unallocated_groups_auth A -∗
    saved_si_auth ∅ -∗
    free_ips_auth fips -∗
    free_ports_auth (GSet <$> addrs_to_ip_ports_map (union_set A)) -∗
    (* ([∗ map] ip ↦ ports ∈ addrs_to_ip_ports_map (union_set A), *)
    (*    free_ports ip ports)%I -∗ *)
    aneris_state_interp σ (∅, ∅).
  Proof.
     iIntros (Hfips Hfips' Hfips'' Hheap Hskt Hheaps Hskts Hms)
            "Hγs_auth Hγs Hm Hsags Hunallocated Hsif HipsCtx HPiu_auth".
    iDestruct (socket_address_group_ctx_valid with "Hsags") as %[Hdisj Hne].
    iExists _, _; iFrame.
    iSplit.
    (* messages_received_sent *)
    { iPureIntro. apply messages_received_sent_init. }
    iSplit.
    (* gnames_coh *)
    { iPureIntro.
      (* TODO: Dont break abstraction here. *)
      by rewrite /gnames_coh Hheap Hskt. }
    iSplitR.
    (* network_sockets_coh *)
    { iPureIntro.
      (* TODO: Dont break abstraction here. *)
      rewrite /network_sockets_coh.
      intros ip Sn HSome. apply Hskts in HSome as ->.
      split.
      { rewrite /socket_handlers_coh. set_solver. }
      split.
      { rewrite /socket_messages_coh. set_solver. }
      split.
      { rewrite /socket_addresses_coh. set_solver. }
      rewrite /socket_unbound_empty_buf_coh. set_solver. }
    iSplitR.
    (* messages_history_coh *)
    { iPureIntro.
      (* TODO: Dont break abstraction here. *)
      rewrite /messages_history_coh. rewrite Hms.
      split.
      { rewrite /message_soup_coh. set_solver. }
      split.
      { rewrite /receive_buffers_coh.
        intros ip Sn sh skt r m HSome. apply Hskts in HSome as ->.
        set_solver. }
      split.
      { rewrite /messages_addresses_coh.
        rewrite dom_gset_to_gmap.
        split; [done|].
        split; [set_solver|].
        intros sag R T HSome. rewrite lookup_gset_to_gmap_Some in HSome.
        destruct HSome. set_solver. }
      rewrite /messages_received_from_sent_coh.
      rewrite messages_received_init messages_sent_init. set_solver. }
    (* socket_interp_coh *)
    iDestruct (socket_address_groups_ctx_own with "Hsags") as "#Hsags'".
    iSplitL "Hsags Hunallocated Hsif".
    { by iApply (socket_interp_coh_init with "Hsags Hunallocated Hsif"). }
    iSplitL "Hγs".
    (* local_state_coh *)
    { iApply (big_sepM_impl with "Hγs").
      iIntros "!>" (k x HSome) "(Hnode & Hheap & Hskt)".
      assert (is_Some ((state_heaps σ) !! k)) as [y HSomey].
      { apply elem_of_dom. rewrite Hheap. apply elem_of_dom. by exists x. }
      assert (is_Some ((state_sockets σ) !! k)) as [z HSomez].
      { apply elem_of_dom. rewrite Hskt. apply elem_of_dom. by exists x. }
      iExists _, _.
      iSplit; [done|]. 
      iSplit; [done|].
      apply Hheaps in HSomey as ->.
      apply Hskts in HSomez as ->.
      rewrite fmap_empty.
      iFrame. }
    iSplitL "HipsCtx HPiu_auth".
    (* free_ips_coh *)
    { by iApply (free_ips_coh_init with "[$]"). }
    (* messages_resource_coh *)
    iApply messages_resource_coh_init.
    iFrame "#".
  Qed.

  (* aneris_state_interp *)
  Lemma aneris_state_interp_init ips A σ γs ip :
    state_heaps σ = {[ip:=∅]} →
    state_sockets σ = {[ip:=∅]} →
    state_ms σ = ∅ →
    ip ∉ ips →
    node_gnames_auth {[ip:=γs]} -∗
    mapsto_node ip γs -∗
    heap_ctx γs ∅ -∗
    sockets_ctx γs ∅ -∗
    messages_ctx (gset_to_gmap (∅, ∅) A)  -∗
    socket_address_group_ctx A -∗
    unallocated_groups_auth A -∗
    saved_si_auth ∅ -∗
    free_ips_auth ips -∗
    free_ports_auth ∅ -∗
    aneris_state_interp σ (∅, ∅).
  Proof.
    iIntros (Hste Hsce Hmse Hip)
            "Hmp #Hn Hh Hs Hm Hsags Hunallocated Hsif HipsCtx HPiu".
    iDestruct (socket_address_group_ctx_valid with "Hsags") as %[Hdisj Hne].
    iExists _, _; iFrame.
    rewrite !Hste !Hsce !Hmse.
    iSplit.
    (* messages_received_sent *)
    { iPureIntro. apply messages_received_sent_init. }
    iSplit.
    (* gnames_coh *)
    { iPureIntro. apply gnames_coh_singleton. }
    iSplitR.
    (* network_sockets_coh *)
    { iPureIntro. apply network_sockets_coh_init. }
    iSplitR.
    (* messages_history_coh *)
    { iPureIntro.
      apply messages_history_coh_init.
      { by eapply all_disjoint_subseteq. }
      intros x Hx. apply Hne. set_solver. }
    (* socket_interp_coh *)
    iDestruct (socket_address_groups_ctx_own with "Hsags") as "#Hsags'".
    iSplitL "Hsags Hunallocated Hsif".
    { by iApply (socket_interp_coh_init with "Hsags Hunallocated Hsif"). }
    iSplitL "Hh Hs".
    (* local_state_coh *)
    { rewrite big_sepM_singleton /local_state_coh Hste Hsce !lookup_singleton.
      iExists ∅, ∅.
      rewrite fmap_empty. iFrame; iFrame "#"; eauto. }
    iSplitL "HipsCtx HPiu".
    (* free_ips_coh *)
    { by iApply (free_ips_coh_init with "[$]"). }
    (* messages_resource_coh *)
    iApply messages_resource_coh_init.
    iFrame "#".
  Qed.

  Lemma aneris_events_state_interp_init c As Ar lbls :
    observed_send_groups As -∗
    observed_receive_groups Ar -∗
    own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
        (◯ (DGSets (As ∪ Ar))) -∗
    sendon_evs_ctx (gset_to_gmap [] As) -∗
    receiveon_evs_ctx (gset_to_gmap [] Ar) -∗
    alloc_evs_ctx (gset_to_gmap [] lbls) -∗
    aneris_events_state_interp {tr[c]} .
  Proof.
    iIntros "#HAs #HAr #Hown Hs Hr Ha".
    iExists _, _, lbls; iFrame "#".
    erewrite (const_fn_to_gmap _ (λ sag, events_of_trace (sendonEV_groups sag) {tr[ c ]}));
      first iFrame "Hs"; last by auto using events_of_singleton_trace.
    erewrite (const_fn_to_gmap _ (λ sag, events_of_trace (receiveonEV_groups sag) {tr[ c ]}));
      first iFrame "Hr"; last by auto using events_of_singleton_trace.
    erewrite (const_fn_to_gmap _ (λ sa, events_of_trace (allocEV sa) {tr[ c ]}));
      first iFrame "Ha"; last by auto using events_of_singleton_trace.
  Qed.

  Lemma aneris_state_interp_free_ip_valid σ ip mh:
    aneris_state_interp σ mh -∗
    free_ip ip -∗
    ⌜state_heaps σ !! ip = None ∧
    state_sockets σ !! ip = None⌝.
  Proof.
    iDestruct 1 as (mγ mn) "(?&?&%&?&?& Hsi & Hlcoh & Hfreeips & ?)".
    iIntros "Hfip".
    iDestruct "Hfreeips"
      as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]".
    iDestruct (free_ip_included with "HfCtx Hfip") as %Hin.
    iPureIntro. by apply HFip. 
  Qed.

  Lemma aneris_state_interp_free_ports_valid σ a mh Sn:
    state_sockets σ !! ip_of_address a = Some Sn → 
    aneris_state_interp σ mh -∗
    free_ports (ip_of_address a) {[port_of_address a]} -∗
    ⌜port_not_in_use (port_of_address a) Sn⌝.      
  Proof.
    iDestruct 1 as (mγ mn) "(?&?&?&%&?&?& Hsi & Hlcoh & Hfreeips & ?)".
    by iApply free_ips_coh_free_ports_valid.
  Qed. 

  Lemma aneris_state_interp_alloc_node σ ip ports mh :
    aneris_state_interp σ mh ∗ free_ip ip ==∗
    ⌜network_sockets_coh (state_sockets σ)⌝ ∗
    is_node ip ∗ free_ports ip ports ∗
    aneris_state_interp
      (σ <| state_heaps := <[ip:=∅]> (state_heaps σ)|>
                           <| state_sockets := <[ip:=∅]> (state_sockets σ) |>)
      mh.
  Proof.
    iIntros "[Hσ Hfip]".
    iDestruct (aneris_state_interp_free_ip_valid with "Hσ Hfip")
      as "(% & %)".
    iDestruct "Hσ"
      as (mγ mh')
           "(%Hhst & %Hgcoh & %Hnscoh & %Hmhcoh
                     & Hnauth & Hsi & Hlcoh & HFip & Hmctx & Hmres)".
    iMod (free_ips_coh_alloc_node _ _ ports with "HFip Hfip")
      as "[HFip Hports]".
    iMod (node_ctx_init ∅ ∅) as (γn) "(Hh & Hs)".
    assert (mγ !! ip = None) as Hnone by eapply gnames_coh_valid=>//.
    iMod (node_gnames_alloc γn with "Hnauth") as "[Hnauth #Hγn]"; [done|].
    set σ' := (σ <| state_heaps := <[ip:=∅]> (state_heaps σ)|>
                                   <| state_sockets := <[ip:=∅]> (state_sockets σ) |>).
    iModIntro. iSplit; first done.
    iSplitR.
    { iExists _; eauto. }
    iFrame "Hports".
    iExists _, _. iFrame.
    iSplit; [done|].
    iSplitR.
    { iPureIntro. by apply gnames_coh_alloc_node. }
    iSplitR.
    { iPureIntro. by apply network_sockets_coh_alloc_node. }
    iSplitR.
    { iPureIntro. by apply messages_history_coh_alloc_node. }
    iApply (big_sepM_local_state_coh_insert ip γn
              with "[Hh Hs] [Hlcoh]").
    - rewrite lookup_insert //.
    - iExists ∅, ∅.
      iFrame. iFrame "#". rewrite !lookup_insert fmap_empty.
      repeat iSplit; eauto.
    - rewrite delete_insert //.
      by iApply big_sepM_local_state_coh_alloc_node.
  Qed.

  Lemma aneris_state_interp_heap_valid σ l n q v mh:
    aneris_state_interp σ mh -∗
    l ↦[n]{q} v -∗
    ∃ h, ⌜state_heaps σ !! n = Some h ∧ h !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". iDestruct "Hl" as (?) "[#Hn Hl]".
    iDestruct (mapsto_node_heap_valid with "Hσ Hn") as (h) "%".
    iDestruct "Hσ"
      as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iApply (local_state_coh_valid_heap with "Hstate [Hl]").
    iExists _;  eauto.
  Qed.

  Lemma aneris_state_interp_alloc_heap σ n h l v mh :
    let σ' := (σ <| state_heaps := <[n:= <[l:=v]>h]>(state_heaps σ) |>) in
    state_heaps σ !! n = Some h →
    h !! l = None →
    is_node n -∗
    aneris_state_interp σ mh ==∗ aneris_state_interp σ' mh ∗ l ↦[n] v.
  Proof.
    simpl. iIntros (??) "Hn Hσ".
    iDestruct "Hn" as (γs) "Hn".
    iDestruct "Hσ"
      as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_alloc_heap with "[Hn] Hstate") as "[Hstate' Hl]";
      [done|done|..].
    { by iExists _. }
    iDestruct (big_sepM_local_state_coh_update_heap_notin n with "Hlcoh")
      as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "[$] Hlcoh")
      as "HX"; [done|].
    iModIntro. iFrame. iExists _, _. iFrame. simplify_eq /=.
    iSplitR.
    { iPureIntro. by eapply gnames_coh_update_heap. }
    iSplitR; first done.
    iSplitR; first done.
    by iApply free_ips_coh_update_heap.
  Qed.

  Lemma aneris_state_interp_heap_update σ1 n h l v1 v2 mh:
    let σ2 := (σ1 <| state_heaps := <[n:=<[l:=v2]> h]> (state_heaps σ1) |>) in
    state_heaps σ1 !! n = Some h →
    aneris_state_interp σ1 mh ∗ l ↦[n] v1 ==∗
    aneris_state_interp σ2 mh ∗ l ↦[n] v2.
  Proof.
    simpl. iIntros (?) "[Hσ Hl]".
    iDestruct "Hl" as (?) "[#Hn Hl]".
    iDestruct "Hσ"
      as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_update_heap with "[$Hstate Hl]") as "[Hstate' Hl]";
      [done|..].
    { iExists _; eauto. }
    iDestruct (big_sepM_local_state_coh_update_heap_notin n with "Hlcoh")
      as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh") as "HX";
      [done|].
    iModIntro. iFrame. iExists _, _. iFrame.
    iSplitR.
    { iPureIntro. by eapply gnames_coh_update_heap. }
    iSplitR; first done.
    iSplitR; first done.
    by iApply free_ips_coh_update_heap.
  Qed.

  Lemma mapsto_socket_node q ip sh skt :
    sh ↪[ip]{q} skt ⊢ ∃ γ, mapsto_node ip γ ∗ sh ↪[ip]{q} skt.
  Proof.
    iDestruct 1 as (γs) "[#Hip Hsh]".
    iExists _; iSplitR; eauto with iFrame.
    iExists _; by iFrame.
  Qed.

  Lemma aneris_state_interp_socket_valid σ sh ip q skt mh :
    aneris_state_interp σ mh -∗
    sh ↪[ip]{q} skt -∗
    ∃ Sn r,
      ⌜state_sockets σ !! ip = Some Sn ∧
      Sn !! sh = Some (skt, r) ∧
      (saddress skt = None → r = [])⌝.
  Proof.
    iIntros "Hσ Hsh".
    iDestruct "Hσ"
      as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iPoseProof (mapsto_socket_node with "Hsh") as (γn) "(#Hip & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hip") as "%Hmin".
    iPoseProof (local_state_coh_valid_sockets  _ _ γn _ q with "[Hlcoh] [$Hsh]")
      as (Sn r0) "(%Hp1 & %Hp2)".
    - iDestruct (big_sepM_lookup with "Hlcoh") as "Hl"; done.
    - iExists Sn, r0.
      iPureIntro.
      repeat split; try done.
      specialize (Hnscoh ip Sn Hp1) as (?&?&?&Hb).
      by eapply Hb.
  Qed.

  Lemma aneris_state_interp_sblock_update σ1 a b sh skt Sn r mh :
    let ip := ip_of_address a in
    let S := <[ip := <[sh:= (skt<| sblock := b|>, r)]> Sn]>(state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    aneris_state_interp σ1 mh -∗
    sh ↪[ip_of_address a] skt ==∗
    aneris_state_interp σ2 mh ∗ sh ↪[ip] (skt<| sblock := b |>).
  Proof.
    simpl. iIntros (HS HSn) "Hσ Hsh".
    iDestruct "Hσ"
      as (mγ mn)
           "(? &  %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_update_sblock with "[$Hstate Hsh]") as
        "[Hstate' $]"; try done.
    iDestruct
      (big_sepM_local_state_coh_update_socket_notin with "Hlcoh")
      as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh")
      as "Hlcoh"; [done|].
    iMod (free_ips_coh_update_sblock with "Hfreeips") as "Hfreeips"; eauto.
    iModIntro. iExists mγ, _. iFrame. rewrite /set /=.
    iSplit.
    { iPureIntro; by eapply gnames_coh_update_sockets. }
    iSplitR.
    { iPureIntro. by apply network_sockets_coh_update_sblock. }
    iPureIntro. destruct Hmhcoh as (Hc1&Hc2&Hc3&Hc4). split_and!; eauto.
    by apply receive_buffers_coh_update_sblock.
  Qed.

  Lemma aneris_state_interp_alloc_socket s ip sh Sn σ mh :
    let σ' := σ <| state_sockets :=
                <[ip:=<[sh:=(s, [])]> Sn]> (state_sockets σ) |> in
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    saddress s = None →
    is_node ip -∗
    aneris_state_interp σ mh ==∗ aneris_state_interp σ' mh ∗ sh ↪[ip] s.
  Proof.
    simpl. iIntros (???) "Hn Hσ".
    iDestruct "Hn" as (γs) "Hn".
    iDestruct "Hσ"
      as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_alloc_socket with "[Hn] Hstate") as "[Hstate' Hl]";
      [done|done|..].
    { by iExists _. }
    iDestruct (big_sepM_local_state_coh_update_socket_notin ip with "Hlcoh")
      as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh")
      as "HX"; [done|].
    iModIntro. iFrame. iExists _, _. iFrame.
    rewrite /set /=.
    iSplitR.
    { iPureIntro. by eapply gnames_coh_update_sockets. }
    iSplitR.
    { iPureIntro.
      by apply network_sockets_coh_alloc_socket. }
    iSplitR.
    { rewrite /messages_history_coh.
      iPureIntro.
      destruct Hmhcoh as (? & Hrcoh & ?).
      eauto using receive_buffers_coh_alloc_socket. }
    { by iApply free_ips_coh_alloc_socket. }
  Qed.

  Lemma aneris_state_interp_socket_interp_allocate_singleton σ mh sag φ :
    aneris_state_interp σ mh -∗ unallocated_groups {[sag]} ==∗
    aneris_state_interp σ mh ∗ sag ⤇* φ.
  Proof.
    iIntros "Hσ Hunallocated".
    iDestruct "Hσ"
        as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iMod (socket_interp_coh_allocate_singleton with "Hsi Hunallocated")
      as "[Hφ Hsi]". 
    iModIntro. iFrame. iExists _, _. iFrame. eauto.
  Qed.

  Lemma aneris_state_interp_socket_interp_allocate_fun σ mh sags f :
    aneris_state_interp σ mh -∗ unallocated_groups sags ==∗
    aneris_state_interp σ mh ∗ [∗ set] sag ∈ sags, sag ⤇* f sag.
  Proof.
    iIntros "Hσ Hunallocated".
    iDestruct "Hσ"
        as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iMod (socket_interp_coh_allocate_fun with "Hsi Hunallocated")
      as "[Hφ Hsi]". 
    iModIntro. iFrame. iExists _, _. iFrame. eauto.
  Qed.

  Lemma aneris_state_interp_socket_interp_allocate σ mh sags φ :
    aneris_state_interp σ mh -∗ unallocated_groups sags ==∗
    aneris_state_interp σ mh ∗ [∗ set] sag ∈ sags, sag ⤇* φ.
  Proof.
    iIntros "Hσ Hunallocated".
    iDestruct "Hσ"
        as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iMod (socket_interp_coh_allocate with "Hsi Hunallocated")
      as "[Hφ Hsi]". 
    iModIntro. iFrame. iExists _, _. iFrame. eauto.
  Qed.

  Lemma aneris_state_interp_socketbind σ1 sa sh skt Sn mh :
    let ip := ip_of_address sa in
    let S' :=
        <[ip := <[sh:=(skt<| saddress := Some sa |>, [])]> Sn]>
        (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |>  in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, []) →
    port_not_in_use (port_of_address sa) Sn →
    saddress skt = None →
    aneris_state_interp σ1 mh -∗
    sh ↪[ip_of_address sa] skt -∗
    free_ports ip {[port_of_address sa]} ==∗
    aneris_state_interp σ2 mh ∗ sh ↪[ip] (skt<| saddress := Some sa |>).
  Proof.
    simpl. iIntros (????) "Hσ Hsh Hp".
    iDestruct "Hσ"
      as (mγ mn)
           "(? & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_socketbind with "[$Hstate Hsh]") as
        "[Hstate' $]"; try done.
    iDestruct
      (big_sepM_local_state_coh_update_socket_notin with "Hlcoh")
      as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh")
      as "Hlcoh"; [done|].
    iMod (free_ips_coh_dealloc _ _ sh skt with "Hfreeips Hp")
      as "Hfreeips"; [done..|].
    iModIntro. iExists mγ, _. iFrame. rewrite /set /=.
    iSplit.
    { iPureIntro; by eapply gnames_coh_update_sockets. }
    iSplitR.
    { iPureIntro.
      apply network_sockets_coh_socketbind; eauto with set_solver.
    }
    iPureIntro. by apply messages_history_coh_socketbind.
  Qed.

  Lemma aneris_state_interp_send
        sh saT sagT saR sagR bs br skt Sn r R T φ mbody σ1 mh msg' :
    let ip := ip_of_address saT in
    let msg := mkMessage saT saR mbody in
    let M' := {[+ msg +]} ⊎ state_ms σ1 in
    let σ2 := σ1 <| state_ms := M' |> in
    state_sockets σ1 !! ip_of_address saT = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some saT →
    msg ≡g{sagT,sagR} msg' →
    saT ∈g sagT -∗
    saR ∈g sagR -∗
    sh ↪[ip_of_address saT] skt -∗
    sagT ⤳*[bs, br] (R, T) -∗
    sagR ⤇* φ -∗
    φ msg' -∗
    aneris_state_interp σ1 mh ==∗
    ⌜(mh.1, {[msg]} ∪ mh.2) =
    message_history_evolution
      (state_ms σ1) M' (state_sockets σ1) (state_sockets σ1) mh⌝ ∗
    aneris_state_interp σ2 (mh.1, {[msg]} ∪ mh.2) ∗
    sh ↪[ip_of_address saT] skt ∗
    sagT ⤳*[bs, br] (R, {[msg]} ∪ T).
  Proof.
    simpl.
    iIntros (HS HSn Hskt Hmeq) "#HsagT #HsagR Hsh Hrt #Hφ Hmsg Hσ".
    iDestruct "Hσ"
      as (mγ mh')
           "(%Hhst & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    set (msg := {|
            m_sender := saT;
            m_destination := saR;
            m_body := mbody |}).
    iDestruct (messages_mapsto_ctx_valid with "Hrt Hmctx") as %Hma.
    destruct (decide (msg ∈ T)).
    - assert (T = {[msg]} ∪ T) as <- by set_solver.
      iFrame. iModIntro.
      iSplit.
      + iPureIntro.
        destruct Hmhcoh as (Hmscoh & ? & ? & ?).
        eapply message_history_evolution_send_message.
        rewrite /messages_received_sent in Hhst.
        inversion Hhst as [[ Hrcvd Hsent ]].
        simplify_eq /=.
        intros m0 Hm0.
        apply elem_of_messages_sent.
        edestruct Hmscoh as (R0 & T0 & sag0 & ? & ? & ?); first by apply gmultiset_elem_of_dom.
        exists sag0, (R0,T0). set_solver.
      + iExists mγ, (<[sagT:=(R, T)]> mh'). iFrame.
        simpl.
        rewrite {2 3 4} (insert_id mh'); eauto.
        iFrame.
        iDestruct (elem_of_group_unfold with "HsagT") as "[%HsagT _]".
        iPureIntro; split_and!; eauto.
        * rewrite /messages_received_sent.
          rewrite /messages_received_sent in Hhst.
          apply insert_id in Hma. simplify_eq /=.
          rewrite - {3 4} Hma.
          rewrite !messages_sent_insert.
          rewrite !messages_received_insert.
          assert (T = {[msg]} ∪ T) as Ht by set_solver.
          rewrite {1} Ht. f_equal; set_solver.
        * assert (mh' = <[sagT := (R, {[msg]} ∪ T)]> mh') as ->.
          assert (T = {[msg]} ∪ T) as <- by set_solver.
          -- by rewrite insert_id.
          -- by eapply messages_history_coh_send.
    - iMod (messages_mapsto_update sagT bs br R T R ({[msg]} ∪ T) mh'
              with "[$Hrt $Hmctx]") as "[Hmctx Hrt]".
      iFrame. iModIntro.
      iSplit. iPureIntro.
      destruct Hmhcoh as (Hmscoh & ? & ? & ?).
      eapply  message_history_evolution_send_message.
      rewrite /messages_received_sent in Hhst.
      inversion Hhst as [[ Hrcvd Hsent ]].
      simplify_eq /=.
      intros m0 Hm0.
      apply elem_of_messages_sent.
      edestruct Hmscoh as (R0 & T0 & sag0 & ? & ?); first by apply gmultiset_elem_of_dom.
      exists sag0, (R0,T0). set_solver.
      iExists mγ, (<[sagT:=(R, {[msg]} ∪ T)]> mh'). iFrame.
      simpl.
      iSplit.
      { iPureIntro.
        rewrite /messages_received_sent.
        rewrite /messages_received_sent in Hhst.
        apply insert_id in Hma. simplify_eq /=.
        rewrite - {3 4} Hma.
        rewrite !messages_sent_insert.
        rewrite !messages_received_insert.
        f_equal; set_solver. }
      do 2 (iSplit; [done|]).
      iDestruct (elem_of_group_unfold with "HsagT") as "[%HsagT _]".
      iSplit.
      { iPureIntro. by eapply messages_history_coh_send. }
      iApply (messages_resource_coh_send with "[HsagR] [Hφ] [$Hmres] [Hmsg]"); eauto.
      by destruct Hmhcoh; intuition.
  Qed.

  Lemma aneris_state_interp_send_duplicate sh saT sagT saR sagR bs br skt Sn r R T mbody σ1 mh :
    let ip := ip_of_address saT in
    let msg := mkMessage saT saR mbody in
    let M' := {[+ msg +]} ⊎ state_ms σ1 in
    let σ2 := σ1 <| state_ms := M' |> in
    state_sockets σ1 !! ip_of_address saT = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some saT →
    set_Exists (λ m, m ≡g{sagT,sagR} msg) T →
    saT ∈g sagT -∗
    saR ∈g sagR -∗
    sh ↪[ip_of_address saT] skt -∗
    sagT ⤳*[bs, br] (R, T) -∗
    aneris_state_interp σ1 mh ==∗
    ⌜(mh.1, {[msg]} ∪ mh.2) =
    message_history_evolution
      (state_ms σ1) M' (state_sockets σ1) (state_sockets σ1) mh⌝ ∗
    aneris_state_interp σ2 (mh.1, {[msg]} ∪ mh.2) ∗
    sh ↪[ip_of_address saT] skt ∗
    sagT ⤳*[bs, br] (R, {[msg]} ∪ T).
  Proof.
    simpl.
    iIntros (HS HSn Hskt Hexist) "#HsagT #HsagR Hsh Hrt Hσ".
    iDestruct "Hσ"
      as (mγ mh')
           "(%Hhst & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    set (msg := {|
            m_sender := saT;
            m_destination := saR;
            m_body := mbody |}).
    iDestruct (messages_mapsto_ctx_valid with "Hrt Hmctx") as %Hma.
    destruct (decide (msg ∈ T)).
    - assert (T = {[msg]} ∪ T) as <- by set_solver.
      iFrame. iModIntro.
      iSplit.
      + iPureIntro.
        destruct Hmhcoh as (Hmscoh & ? & ? & ?).
        eapply message_history_evolution_send_message.
        rewrite /messages_received_sent in Hhst.
        inversion Hhst as [[ Hrcvd Hsent ]].
        simplify_eq /=.
        intros m0 Hm0.
        apply elem_of_messages_sent.
        edestruct Hmscoh as (R0 & T0 & sag0 & ? & ? & ?); first by apply gmultiset_elem_of_dom.
        exists sag0, (R0,T0). set_solver.
      + iExists mγ, (<[sagT:=(R, T)]> mh'). iFrame.
        simpl.
        rewrite {2 3 4} (insert_id mh'); eauto.
        iFrame.
        iDestruct (elem_of_group_unfold with "HsagT") as "[%HsagT _]".
        iPureIntro; split_and!; eauto.
        * rewrite /messages_received_sent.
          rewrite /messages_received_sent in Hhst.
          apply insert_id in Hma. simplify_eq /=.
          rewrite - {3 4} Hma.
          rewrite !messages_sent_insert.
          rewrite !messages_received_insert.
          assert (T = {[msg]} ∪ T) as Ht by set_solver.
          rewrite {1} Ht. f_equal; set_solver.
        * assert (mh' = <[sagT := (R, {[msg]} ∪ T)]> mh') as ->.
          assert (T = {[msg]} ∪ T) as <- by set_solver.
          -- by rewrite insert_id.
          -- by eapply messages_history_coh_send.
    - iMod (messages_mapsto_update sagT bs br R T R ({[msg]} ∪ T) mh'
              with "[$Hrt $Hmctx]") as "[Hmctx Hrt]".
      iFrame. iModIntro.
      iSplit. iPureIntro.
      destruct Hmhcoh as (Hmscoh & ? & ? & ?).
      eapply  message_history_evolution_send_message.
      rewrite /messages_received_sent in Hhst.
      inversion Hhst as [[ Hrcvd Hsent ]].
      simplify_eq /=.
      intros m0 Hm0.
      apply elem_of_messages_sent.
      edestruct Hmscoh as (R0 & T0 & sag0 & ? & ?); first by apply gmultiset_elem_of_dom.
      exists sag0, (R0,T0). set_solver.
      iExists mγ, (<[sagT:=(R, {[msg]} ∪ T)]> mh'). iFrame.
      simpl.
      iDestruct (elem_of_group_unfold with "HsagT") as "[%HsagT _]".
      iSplit.
      { iPureIntro.
        rewrite /messages_received_sent.
        rewrite /messages_received_sent in Hhst.
        apply insert_id in Hma. simplify_eq /=.
        rewrite - {3 4} Hma.
        rewrite !messages_sent_insert.
        rewrite !messages_received_insert.
        f_equal; set_solver. }
      do 2 (iSplit; [done|]).
      iSplit.
      { iPureIntro. by eapply messages_history_coh_send. }
      iApply (messages_resource_coh_send_duplicate with "[HsagR] [$Hmres]"); eauto.
      by destruct Hmhcoh; intuition.
  Qed.

  Lemma messages_addresses_coh_disj mhm :
    messages_addresses_coh mhm → all_disjoint (dom mhm).
  Proof. rewrite /messages_addresses_coh. naive_solver. Qed.

  Lemma aneris_state_interp_receive_some sa sag bs br sh skt
        (Ψo : option (socket_interp Σ)) σ1 Sn r R T m mh :
    let ip := ip_of_address sa in
    let S' := <[ip :=<[sh:=(skt, r)]> Sn]> (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r ++ [m]) →
    saddress skt = Some sa →
    sa ∈g sag -∗
    match Ψo with Some Ψ => sag ⤇* Ψ | _ => True end -∗
    aneris_state_interp σ1 mh -∗
    sh ↪[ip] skt -∗
    sag ⤳*[bs, br] (R, T) -∗
    ∃ R' sagT,
      ⌜m_destination m = sa⌝ ∗
      m_sender m ∈g sagT ∗
      ⌜(R' ∪ mh.1, mh.2) =
      message_history_evolution
        (state_ms σ1) (state_ms σ1) (state_sockets σ1) S'  mh⌝ ∗
      ⌜R' = {[ m ]} ∪ R⌝ ∗
      ((⌜set_Forall (λ m', ¬ m ≡g{sagT, sag} m') R⌝ ∗
        ∃ m', ⌜m ≡g{sagT, sag} m'⌝ ∗
              ▷ match Ψo with Some Ψ => Ψ m' | _ => ∃ φ, sag ⤇* φ ∗ φ m' end)
       ∨
       ⌜set_Exists (λ m', m ≡g{sagT, sag} m') R⌝)
      ∗ |==> aneris_state_interp σ2 (R' ∪ mh.1, mh.2)
             ∗ sh ↪[ip_of_address sa] skt ∗ sag ⤳*[bs, br] (R', T).
  Proof.
    simpl. iIntros (HS HSn Hskt) "#Hsag #Hproto Hσ Hsh Ha".
    iDestruct (elem_of_group_unfold with "Hsag") as "[%Hsag _]".
    rewrite {1}/aneris_state_interp.
    iDestruct "Hσ"
      as (mγ mh')
           "(%Hhst & %Hgcoh & %Hnscoh & %Hmhcoh
                            & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    assert ( network_sockets_coh (state_sockets σ1))
      as Hnscoh2 by eauto.
    destruct (Hnscoh (ip_of_address sa) Sn)
      as (Hshcoh & Hsmcoh & Hsacoh & Hsucoh);
      first done.
    iDestruct (messages_mapsto_ctx_valid with "[$Ha] [$Hmctx]") as %Hmha.
    assert (m_destination m = sa) as Hma by (eapply Hsmcoh =>//; set_solver).
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iDestruct (local_state_coh_update_rb sa sh skt σ1 γs Sn (r ++ [m]) r
                 with "[$Hstate $Hsh]") as "Hstate"; eauto.
    destruct Hmhcoh as (? & Hrscoh & Hacoh & Hrsbcoh).
    assert ( ∃ sagT R' T', m_sender m ∈ sagT ∧ mh' !! sagT = Some (R', T') ∧
                           m ∈ T') as Hrcoh2.
    { destruct (Hrscoh (ip_of_address sa) Sn sh skt _ m HS HSn ltac:(set_solver)).
      destruct H1 as (T' & sagT & HsagT & Hlookup & HinT).
      eexists _,_,_.
      eauto. }
    destruct Hrcoh2 as (sagT&R'&T'&HsagT&Hmh&Hm).
    iPoseProof (messages_resource_coh_socket_address_group_own sagT with "Hmres")
      as "[Hmres #HownT]".
    { apply elem_of_dom. eexists _. set_solver. }
    iAssert (m_sender m ∈g sagT) as "#HsagT".
    { iSplit; done. }
    iExists ({[m]} ∪ R), sagT. iSplit; first done.
    iSplit; [iSplit;done|].
    destruct (set_Forall_Exists_message_group_equiv_dec sagT sag m R)
      as [Hmeq | Hmeq]; last first.
    - pose proof Hmeq as [m' [Hmin Hmq]].
      iPoseProof
        (messages_resource_coh_receive sag sagT _ _ _ _ m with "[Hsag] [HsagT] Hmres")
        as "(Hmres & _)"; [set_solver..|by simplify_eq|by simplify_eq|].
      iSplitR.
      { iPureIntro.
        eapply message_history_evolution_receive; eauto.
        intros ???. destruct (Hnscoh2 ip Sn0); eauto. naive_solver.
        rewrite /messages_received_sent in Hhst.
        inversion Hhst as [[ Hrcvd Hsent ]].
        simplify_eq /=.
        intros m0 Hm0.
        apply elem_of_messages_received.
        exists sag, (R,T); done. }
      iSplit; [done|].
      iSplitR; [ by iRight | ].
      iMod "Hstate" as "(Hstate & Hsh)".
      iDestruct (big_sepM_local_state_coh_insert
                   with "[$Hstate] [Hlcoh]") as "Hlcoh"; eauto.
      { iApply (big_sepM_mono with "Hlcoh").
        iIntros (ip' γs' Hdel) "Hlcoh".
        ddeq ip' (ip_of_address sa).
        rewrite lookup_delete_ne in Hdel; last done.
        iDestruct "Hlcoh" as (h' s') "Hlcoh".
        iExists h', s'. rewrite !lookup_insert_ne; eauto. }
      iMod (messages_mapsto_update sag bs br R T ({[m]} ∪ R) T mh'
              with "[$Ha $Hmctx]") as "[Hmctx Ha]".
      iModIntro.
      iFrame.
      iExists mγ, (<[sag:=({[m]} ∪ R, T)]> mh').
      simpl. iFrame. simpl. iSplit; eauto. iPureIntro.
      { rewrite /messages_received_sent.
        rewrite /messages_received_sent in Hhst.
        destruct mh. simplify_eq /=.
        apply insert_id in Hmha. rewrite - {4} Hmha.
        rewrite !messages_sent_insert.
        f_equal.
        rewrite - {2} Hmha.
        rewrite !messages_received_insert.
        set_solver. }
      iPoseProof
      (free_ips_coh_update_msg with "Hfreeips") as "Hfreeips"; eauto.
      iFrame.
      iPureIntro.
      split_and!.
      + by eapply gnames_coh_update_sockets.
      + by eapply network_sockets_coh_receive.
      + eapply messages_history_coh_receive_2; eauto.
        by rewrite /messages_history_coh.
    - iPoseProof
        (messages_resource_coh_receive sag sagT _ _ _ _ m
           with "[Hsag] [HsagT] Hmres")
        as "(Hmres & Hres)";
        [set_solver..|by simplify_eq|by simplify_eq|].
      iDestruct ("Hres" with "[//]") as "(%φ & %m'' & %Hmeq' & #Hφ & Hres)".
      iSplitR.
      { iPureIntro.
        eapply message_history_evolution_receive; eauto.
        intros ???. destruct (Hnscoh2 ip Sn0); eauto. naive_solver.
        rewrite /messages_received_sent in Hhst.
        inversion Hhst as [[ Hrcvd Hsent ]].
        simplify_eq /=.
        intros m0 Hm0.
        apply elem_of_messages_received.
        exists sag, (R,T); split; last done.
        eauto. }
      iSplit; [done|].
      iSplitL "Hres".
      { iLeft. iSplit; eauto. destruct Ψo as [ψ|].
        - iPoseProof (socket_interp_agree _ _ _ _ _ m'' with "Hproto Hφ")
            as (?) "Heq"; eauto.
          iExists _. iSplit; [done|].
          iNext. by iRewrite "Heq".
        - iExists m''. iSplit; [done|]. iNext.
          iExists φ. by iFrame. }
      iMod "Hstate" as "(Hstate & Hsh)".
      iDestruct (big_sepM_local_state_coh_insert
                   with "[$Hstate] [Hlcoh]") as "Hlcoh"; eauto.
      { iApply (big_sepM_mono with "Hlcoh").
        iIntros (ip' γs' Hdel) "Hlcoh".
        ddeq ip' (ip_of_address sa).
        rewrite lookup_delete_ne in Hdel; last done.
        iDestruct "Hlcoh" as (h' s') "Hlcoh".
        iExists h', s'. rewrite !lookup_insert_ne; eauto. }
      iMod (messages_mapsto_update sag bs br R T ({[m]} ∪ R) T mh'
              with "[$Ha $Hmctx]") as "[Hmctx Ha]".
      iModIntro. iFrame.
      iExists mγ, (<[sag:=({[m]} ∪ R, T)]> mh').
      iFrame. simpl. iSplitR.
      { iPureIntro.
        rewrite /messages_received_sent.
        rewrite /messages_received_sent in Hhst.
        destruct mh. simplify_eq /=.
        apply insert_id in Hmha. rewrite - {4} Hmha.
        rewrite !messages_sent_insert.
        f_equal.
        rewrite - {2} Hmha.
        rewrite !messages_received_insert.
        set_solver. }
      iSplit.
      { iPureIntro. by eapply gnames_coh_update_sockets. }
      iSplit.
      { iPureIntro. by eapply network_sockets_coh_receive. }
      iSplit.
      { iPureIntro. by eapply messages_history_coh_receive_2; eauto. }
      by iApply free_ips_coh_update_msg.
  Qed.

  Lemma aneris_state_interp_model_agree m ex atr :
    state_interp ex atr -∗ frag_st m -∗ ⌜(trace_last atr) = m⌝.
  Proof.
    iIntros "(_ & _ & Ha & _) Hf".
    by iDestruct (auth_frag_st_agree with "Ha Hf") as %<-.
  Qed.

  Lemma aneris_state_interp_model_extend m1 m2 ex atr :
    state_interp ex (atr :tr[()]: m1) -∗
    frag_st m1 -∗
    ⌜trace_last atr = m1⌝ -∗
    ⌜m1 = m2 ∨ Mdl.(model_rel) m1 m2⌝ ==∗
    state_interp ex (atr :tr[()]: m2) ∗ frag_st m2.
  Proof.
    iIntros "Hsi Hfrag %Hm1 %Hrel".
    iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %Heq.
    iDestruct "Hsi" as "(? & ? & Hauth & %Hv & Hsteps)". simpl.
    iDestruct (frag_st_rtc with "Hfrag") as %?.
    iMod (auth_frag_st_update _ m2 with "Hauth Hfrag") as "[Hauth Hfrag]".
    { destruct Hrel as [->|?]; [done|]. by eapply rtc_r. }
    iModIntro. iFrame. iPureIntro. simpl in *.
    rewrite Hm1. destruct Hrel as [->|?]; by [left|right].
  Qed.

  Definition messages_sent_from (sag: socket_address_group) (rt: messages_history) : message_soup :=
    filter (λ m, m.(m_sender) ∈ sag) rt.2.

  Lemma aneris_state_interp_sent_mapsto_agree_group sag R T ex atr:
    sag ⤳* (R, T) -∗
    state_interp ex atr -∗
    ⌜messages_sent_from sag (trace_messages_history ex) = T⌝.
  Proof.
    iIntros "Hlt Hsi".
    rewrite /state_interp /= /aneris_state_interp /messages_sent_from.
    iDestruct "Hsi" as "(? & Hsi & Hauth)".
    iDestruct "Hsi" as (γm mh Hmh Hgnms Hnetsock Hhistcoh) "(?&?&?&?& Hctx &?)".
    rewrite -Hmh /=.
    iDestruct (messages_mapsto_ctx_valid with "Hlt Hctx") as %Hma.
    iPureIntro.
    rewrite /messages_sent.
    destruct Hhistcoh as (Hmspcoh&?&Haddrcoh&?).
    destruct Haddrcoh as (Hdisj & Hne & Haddrcoh).
    apply set_eq_subseteq; split.
    - intros m; rewrite elem_of_filter elem_of_collect.
      intros [? (sag'&[R' T']& Hma' & HmT')]; simpl in *.
      destruct (Haddrcoh _ _ _ Hma') as [Hma'1 Hma'2].
      pose proof (Hma'2 _ HmT'); simplify_eq /=.
      assert (sag = sag') as <-.
      { eapply elem_of_all_disjoint_eq; eauto.
        apply elem_of_dom. by eexists _.
        apply elem_of_dom. by eexists _. }
      rewrite Hma in Hma'; simplify_eq; done.
    - intros m; rewrite elem_of_filter elem_of_collect.
      intros HmT.
      destruct (Haddrcoh _ _ _ Hma) as [Hma1 Hma2].
      pose proof (Hma2 _ HmT); eauto.
  Qed.

  Lemma aneris_state_interp_sent_mapsto_agree sa R T ex atr :
    sa ⤳ (R, T) -∗
    state_interp ex atr -∗
    ⌜messages_sent_from {[sa]} (trace_messages_history ex) = T⌝.
  Proof.
    iIntros "[Hlt H'] Hsi".
    by iApply (aneris_state_interp_sent_mapsto_agree_group with "Hlt Hsi").
  Qed.

End state_interpretation.

Global Opaque aneris_state_interp.
