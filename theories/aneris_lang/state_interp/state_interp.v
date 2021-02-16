From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export
     aneris_lang notation network resources.
From aneris.aneris_lang.state_interp Require Export
     state_interp_def
     state_interp_local_coh
     state_interp_gnames_coh
     state_interp_free_ips_coh
     state_interp_network_sockets_coh
     state_interp_socket_interp_coh
     state_interp_messages_resource_coh
     state_interp_messages_history_coh
     state_interp_config_wp.

From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Σ}.

  (** aneris_state_interp *)
  Lemma mapsto_node_heap_valid n γs σ :
    aneris_state_interp σ -∗
    mapsto_node n γs -∗
    ∃ h, ⌜state_heaps σ !! n = Some h⌝.
  Proof.
    iDestruct 1 as (m Mγ ???) "(Hnauth & Hscoh & Hlcoh & Hfip & Hmrcoh)".
    iIntros "Hn".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %Hninm.
    iDestruct (local_state_coh_heaps with "Hlcoh") as (h) "%"; [done|].
    eauto.
  Qed.

  Lemma is_node_heap_valid n σ :
    aneris_state_interp σ -∗
    is_node n -∗
    ∃ h, ⌜state_heaps σ !! n = Some h⌝.
  Proof.
    iIntros "Hσ". iDestruct 1 as (γs) "Hn".
    iApply (mapsto_node_heap_valid with "[$] [$]").
  Qed.

  Lemma mapsto_node_valid_sockets n γs σ :
    aneris_state_interp σ -∗
    mapsto_node n γs -∗
    ∃ Sn, ⌜state_sockets σ !! n = Some Sn⌝.
  Proof.
    iDestruct 1 as (m Mγ ???) "(Hnauth & Hscoh & Hlcoh & Hfip & Hmrcoh)".
    iIntros "Hn".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %Hninm.
    iDestruct (local_state_coh_sockets with "Hlcoh") as (h) "%"; [done|].
    eauto.
  Qed.

  Lemma is_node_valid_sockets n σ :
    aneris_state_interp σ -∗
    is_node n -∗
    ∃ Sn, ⌜state_sockets σ !! n = Some Sn⌝.
  Proof.
    iIntros "Hσ". iDestruct 1 as (γs) "Hn".
    iApply (mapsto_node_valid_sockets with "[$] [$]").
  Qed.


  Lemma messages_ctx_alloc_node ip γn ports mh :
    ports ≠ ∅ →
    (∀ p, mh !! (SocketAddressInet ip p) = None) →
    mapsto_node ip γn -∗
    messages_ctx mh ==∗
    messages_ctx ((history_init ip ports) ∪ mh) ∗
    ([∗ set] p ∈ ports, SocketAddressInet ip p ⤳ (∅, ∅)).
    Proof.

    iIntros (Hports Hpis) "#Hn Hmctx".
    rewrite /messages_ctx.
    iMod (gen_heap_light_alloc_gen
            _ (history_init ip ports) with "Hmctx") as "(? & Hfrag)".
    { by apply history_init_disj. }
    iFrame.
    iModIntro.
    iInduction ports as [| p ps Hps] "IH"  using set_ind_L; first done.
    destruct (decide (ps = ∅)) as [->|].
    - rewrite right_id_L.
      rewrite{2} /history_init.
      rewrite gset_map_singleton gset_to_gmap_singleton.
      rewrite big_opS_singleton big_opM_singleton.
      iExists _; iFrame "#".
      iFrame.
    - iApply big_opS_union; first by set_solver.
      rewrite{2} /history_init.
      rewrite gset_map_union  gset_map_singleton.
      rewrite gset_to_gmap_union_singleton.
      rewrite big_opM_insert; last first.
      { rewrite lookup_gset_to_gmap_None. set_solver. }
      iDestruct "Hfrag" as "(Hp & Hps)".
      iSplitL "Hp".
      { rewrite big_opS_singleton. iExists _; iFrame "#". iFrame. }
      iApply "IH"; first done.
      iFrame.
    Qed.

    (* aneris_state_interp *)
  Lemma aneris_state_interp_init ips A σ f M ip ports γs :
    ports ≠ ∅ →
    dom (gset socket_address) M = A →
    dom (gset ip_address) (state_ports_in_use σ) = ips →
    (∀ ip, ip ∈ ips → state_ports_in_use σ !! ip = Some ∅) →
    (∀ a, a ∈ A → ip_of_address a ∈ ips) →
    state_heaps σ = {[ip:=∅]} →
    state_sockets σ = {[ip:=∅]} →
    state_ms σ = ∅ →
    ip ∉ ips →
    node_gnames_auth {[ip:=γs]} -∗
    mapsto_node ip γs -∗
    heap_ctx γs ∅ -∗
    sockets_ctx γs ∅ -∗
    messages_ctx (history_init ip ports)  -∗
    fixed A -∗
    saved_si_auth M -∗
    ([∗ set] a ∈ A, a ⤇ (f a)) -∗
    free_ips_auth ips -∗
    free_ports_auth ∅ -∗
    aneris_state_interp σ.
  Proof.
    iIntros (Hnports HMdom Hipdom Hpiiu Hfixdom Hste Hsce Hmse Hip)
            "Hmp #Hn Hh Hs Hm #Hsif HM #Hsa HipsCtx HPiu".
    iExists _, _; iFrame.
    rewrite !Hste !Hsce !Hmse.
    iSplit.
    (* gnames_coh *)
    { iPureIntro. apply gnames_coh_singleton.
      by rewrite /history_init dom_gset_to_gmap history_init_dom. }
    iSplitR.
    (* network_sockets_coh *)
    { iPureIntro. apply network_sockets_coh_init. }
    iSplitR.
    (* messages_history_coh *)
    { iPureIntro. apply messages_history_coh_init. }
    (* socket_interp_coh *)
    iSplitL "HM".
    { by iApply (socket_interp_coh_init with "Hsa Hsif HM"). }
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
  Qed.


  Lemma aneris_state_interp_free_ip_valid σ ip :
    aneris_state_interp σ -∗
    free_ip ip -∗
    ⌜state_heaps σ !! ip = None ∧
     state_sockets σ !! ip = None ∧
     is_Some (state_ports_in_use σ !! ip)⌝.
  Proof.
    iDestruct 1 as (m mh) "(? & % & ? & ? & Hsi & Hlcoh & Hfreeips & ?)".
    iIntros "Hfip".
    iDestruct "Hfreeips"
      as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iDestruct (free_ip_included with "HfCtx Hfip") as %Hin.
    iPureIntro. destruct (HFip2 _ Hin) as [??]. eauto.
  Qed.

  Lemma aneris_state_interp_free_ports_valid σ a :
    aneris_state_interp σ -∗
    free_ports (ip_of_address a) {[port_of_address a]} -∗
    ∃ ps, ⌜state_ports_in_use σ !! ip_of_address a = Some ps ∧
           port_of_address a ∉ ps⌝.
  Proof.
    iDestruct 1 as (m mh) "(? & % & ? & ? & Hsi & Hlcoh & Hfreeips & ?)".
      by iApply free_ips_coh_free_ports_valid.
  Qed.


  Lemma aneris_state_interp_alloc_node σ ip ports :
    ports ≠ ∅ →
    aneris_state_interp σ ∗ free_ip ip ==∗
    is_node ip ∗ free_ports ip ports ∗
    ([∗ set] p ∈ ports, (SocketAddressInet ip p) ⤳ (∅, ∅)) ∗
    aneris_state_interp (σ <| state_heaps   := <[ip:=∅]> (state_heaps σ)|>
                           <| state_sockets := <[ip:=∅]> (state_sockets σ) |>).
  Proof.
   iIntros (Hnp) "[Hσ Hfip]".
    iDestruct (aneris_state_interp_free_ip_valid with "Hσ Hfip")
      as "(% & % & %)".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & HFip & Hmctx & Hmres)".
    iMod (free_ips_coh_alloc_node _ _ ports with "HFip Hfip")
      as "[HFip Hports]".
    iMod (node_ctx_init ∅ ∅) as (γn) "(Hh & Hs)".
    assert (m !! ip = None) as Hnone by eapply gnames_coh_valid=>//.
    iMod (node_gnames_alloc γn with "Hnauth") as "[Hnauth #Hγn]"; [done|].
    set σ' := (σ <| state_heaps   := <[ip:=∅]> (state_heaps σ)|>
                 <| state_sockets := <[ip:=∅]> (state_sockets σ) |>).
    set mh' := history_init ip ports ∪ mh.
    assert (∀ p : positive, mh !! SocketAddressInet ip p = None) as HmhNone.
    { intro p.
      apply not_elem_of_dom.
      assert (ip ∉ gset_map ip_of_address (dom (gset socket_address) mh))
        as Hnip.
      { rewrite /gnames_coh in Hgcoh.
        destruct Hgcoh as (?&?&Hcoh).
        apply not_elem_of_dom in Hnone.
        set_solver. }
        by apply not_elem_of_dom_history. }
    iPoseProof (messages_ctx_alloc_node ip γn ports with "Hγn Hmctx")
      as ">(Hmctx & Hmto)"; [done | done |].
    iModIntro. iSplitR.
    { iExists _; eauto. }
    iFrame "Hports Hmto".
    iExists _, mh'. iFrame.
    iSplitR.
    { iPureIntro.  subst σ' mh'; simpl.
      by apply gnames_coh_alloc_node. }
    iSplitR.
    { iPureIntro.
      by apply network_sockets_coh_alloc_node. }
    iSplitR.
    { iPureIntro.
      apply messages_history_coh_alloc_node; intuition.
        by apply history_init_disj. }
    iSplitL "Hh Hs Hlcoh".
    { iApply (big_sepM_local_state_coh_insert ip γn
                with "[Hh Hs] [Hlcoh]").
      - rewrite lookup_insert //.
      - iExists ∅, ∅.
        iFrame. iFrame "#". rewrite !lookup_insert fmap_empty.
        repeat iSplit; eauto.
      - rewrite delete_insert //.
          by iApply big_sepM_local_state_coh_alloc_node. }
    iApply (messages_resource_coh_alloc_node with "Hmres").
      by apply history_init_disj.
  Qed.

  Lemma aneris_state_interp_heap_valid σ l n q v :
    aneris_state_interp σ -∗
    l ↦[n]{q} v -∗
    ∃ h, ⌜state_heaps σ !! n = Some h ∧ h !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". iDestruct "Hl" as (?) "[#Hn Hl]".
    iDestruct (mapsto_node_heap_valid with "Hσ Hn") as (h) "%".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iApply (local_state_coh_valid_heap with "Hstate [Hl]").
    iExists _;  eauto.
  Qed.

  Lemma aneris_state_interp_alloc_heap σ n h l v :
    let σ' := (σ <| state_heaps := <[n:= <[l:=v]>h]>(state_heaps σ) |>) in
    state_heaps σ !! n = Some h →
    h !! l = None →
    is_node n -∗
    aneris_state_interp σ ==∗ aneris_state_interp σ' ∗ l ↦[n] v.
  Proof.
    simpl. iIntros (??) "Hn Hσ".
    iDestruct "Hn" as (γs) "Hn".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
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


  Lemma aneris_state_interp_heap_update σ1 n h l v1 v2 :
    let σ2 := (σ1 <| state_heaps := <[n:=<[l:=v2]> h]> (state_heaps σ1) |>) in
    state_heaps σ1 !! n = Some h →
    aneris_state_interp σ1 ∗ l ↦[n] v1 ==∗ aneris_state_interp σ2 ∗ l ↦[n] v2.
  Proof.
    simpl. iIntros (?) "[Hσ Hl]".
    iDestruct "Hl" as (?) "[#Hn Hl]".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
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

  Lemma aneris_state_interp_socket_valid σ sh ip q skt:
    aneris_state_interp σ -∗
    sh ↪[ip]{q} skt -∗
    ∃ Sn r,
      ⌜state_sockets σ !! ip = Some Sn ∧
      Sn !! sh = Some (skt, r) ∧
      (saddress skt = None → r = ∅)⌝.
  Proof.
    iIntros "Hσ Hsh".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iPoseProof (mapsto_socket_node with "Hsh") as (γn) "(#Hip & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hip") as "%Hmin".
    iPoseProof (local_state_coh_valid_sockets  _ _ γn _ q with "[Hlcoh] [$Hsh]")
                 as (Sn r0) "(%Hp1 & %Hp2)".
    - iDestruct (big_sepM_lookup with "Hlcoh") as "Hl"; done.
    - iExists Sn, r0.
      iPureIntro.
      repeat split; try done.
      specialize (Hnscoh ip Sn Hp1) as (?&?&?&?&Hb).
      by eapply Hb.
  Qed.

  Lemma aneris_state_interp_alloc_socket s ip sh Sn σ :
    let σ' :=
        σ <| state_sockets :=
          <[ip:=<[sh:=(s, ∅)]> Sn]> (state_sockets σ) |> in
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    saddress s = None →
    is_node ip -∗
    aneris_state_interp σ ==∗ aneris_state_interp σ' ∗ sh ↪[ip] s.
  Proof.
    simpl. iIntros (???) "Hn Hσ".
    iDestruct "Hn" as (γs) "Hn".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
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

  Lemma aneris_state_interp_socketbind_static σ1 a sh skt ps Sn A :
    let ip := ip_of_address a in
    let S' :=
        <[ip := <[sh:=(skt<| saddress := Some a |>, ∅)]> Sn]>
        (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅) →
    state_ports_in_use σ1 !! ip = Some ps →
    saddress skt = None →
    a ∈ A →
    aneris_state_interp σ1 -∗
    fixed A -∗
    sh ↪[ip_of_address a] skt -∗
    free_ports ip {[port_of_address a]} ==∗
    aneris_state_interp σ2 ∗ sh ↪[ip] (skt<| saddress := Some a |>) ∗
    ∃ φ, a ⤇ φ.
  Proof.
    simpl. iIntros (?????) "Hσ #HA Hsh Hp".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
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
    iDestruct (free_ips_coh_free_ports_valid with "Hfreeips Hp")
      as (?) "[% %]".
    iDestruct (socket_interp_coh_fixed_valid with "Hsi HA") as "#$"; [done|].
    iMod (free_ips_coh_dealloc _ _ sh skt with "Hfreeips Hp")
      as "Hfreeips"; [done..|].
    iModIntro. iExists m, mh. iFrame. rewrite /set /=.
    iSplit.
    { iPureIntro; by eapply gnames_coh_update_sockets. }
    iSplitR.
    { iPureIntro.
      apply network_sockets_coh_socketbind; eauto with set_solver. }
    iSplitR.
    { iPureIntro. by apply messages_history_coh_socketbind. }
    iSplitL "Hsi".
    { iApply socket_interp_coh_socketbind_static; eauto with set_solver. }
    assert (ps = ps0) as -> by set_solver.
    iFrame.
  Qed.

  Lemma aneris_state_interp_socketbind_dynamic σ1 a sh skt ps Sn A φ:
    let ip := ip_of_address a in
    let S' :=
        <[ip := <[sh:=(skt<| saddress := Some a |>, ∅)]> Sn]>
        (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅) →
    state_ports_in_use σ1 !! ip = Some ps →
    saddress skt = None →
    a ∉ A →
    aneris_state_interp σ1 -∗
    fixed A -∗
    sh ↪[ip_of_address a] skt -∗
    free_ports ip {[port_of_address a]} ==∗
    aneris_state_interp σ2 ∗ sh ↪[ip] (skt<| saddress := Some a |>) ∗
    a ⤇ φ.
  Proof.
      simpl. iIntros (?????) "Hσ #HA Hsh Hp".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
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
    iDestruct (free_ips_coh_free_ports_valid with "Hfreeips Hp")
      as (?) "[% %]".
     iMod (socket_interp_coh_socketbind_dynamic with "HA Hsi")
      as "[Hsi #$]"; try done.
    iMod (free_ips_coh_dealloc _ _ sh skt with "Hfreeips Hp")
      as "Hfreeips"; [done..|].
    iModIntro. iExists m, mh. iFrame. rewrite /set /=.
    iSplit.
    { iPureIntro; by eapply gnames_coh_update_sockets. }
    iSplitR.
    { iPureIntro.
     eapply network_sockets_coh_socketbind; eauto with set_solver. }
    iSplitR.
    { iPureIntro. by apply messages_history_coh_socketbind. }
    assert (ps = ps0) as -> by set_solver.
    iFrame.
  Qed.

  Lemma aneris_state_interp_send sh a skt Sn r R T φ to mbody σ1 :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) mbody in
    let M' := {[msg]} ∪ state_ms σ1 in
    let σ2 := σ1 <| state_ms := M' |> in
    state_sockets σ1 !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    sh ↪[ip_of_address a] skt -∗
    a ⤳ (R, T) -∗
    to ⤇ φ -∗
    φ msg -∗
    aneris_state_interp σ1 ==∗
    aneris_state_interp σ2 ∗ sh ↪[ip_of_address a] skt ∗
    a ⤳ (R, {[msg]} ∪ T).
  Proof.
    simpl.
    iIntros (HS HSn Hskt) "Hsh Hrt #Hφ Hmsg Hσ".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    set (msg := {|
               m_sender := a;
               m_destination := to;
               m_protocol := sprotocol skt;
               m_body := mbody |}).
    iDestruct (messages_mapsto_valid with "Hrt Hmctx") as %?.
    destruct (decide (msg ∈ T)).
    -  assert (T = {[msg]} ∪ T) as <- by set_solver.
       iFrame. iModIntro. iExists m, mh. iFrame.
       simpl.
       iSplit; eauto.
       iSplit; eauto.
       iPureIntro.
       assert (mh = <[a := (R, {[msg]} ∪ T)]> mh) as ->.
       assert (T = {[msg]} ∪ T) as <- by set_solver.
       by rewrite insert_id.
        by eapply messages_history_coh_send.
    - iMod (messages_mapsto_update a R T R ({[msg]} ∪ T) mh
            with "[$Hrt $Hmctx]") as "[Hmctx Hrt]".
       iFrame. iModIntro. iExists m, (<[a:=(R, {[msg]} ∪ T)]> mh). iFrame.
       simpl.
       iSplit.
       { iPureIntro. by eapply gnames_coh_update_history. }
       iSplit; first done.
       iSplit.
       { iPureIntro. by eapply messages_history_coh_send. }
       iApply
       (messages_resource_coh_send with "[Hφ] [$Hmres] [Hmsg]"); eauto.
         by destruct Hmhcoh; intuition.
  Qed.

  Lemma aneris_state_interp_send_duplicate sh a skt Sn r R T to mbody σ1 :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) mbody in
    let M' := {[msg]} ∪ state_ms σ1 in
    let σ2 := σ1 <| state_ms := M' |> in
    state_sockets σ1 !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    msg ∈ T →
    sh ↪[ip_of_address a] skt -∗
    a ⤳ (R, T) -∗
    aneris_state_interp σ1 ==∗
    aneris_state_interp σ2 ∗ sh ↪[ip_of_address a] skt ∗
    a ⤳ (R, T).
  Proof.
    simpl. iIntros (HS HSn Hskt Hmsg) "Hsh Hrt Hσ".
    iDestruct "Hσ"
      as (m mh)
           "(%Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    set (msg := {|
                 m_sender := a;
                 m_destination := to;
                 m_protocol := sprotocol skt;
                 m_body := mbody |}).
     iDestruct (messages_mapsto_valid with "Hrt Hmctx") as %?.
     iFrame. iModIntro.
     iExists m,  (<[a:=(R, {[msg]} ∪ T)]> mh).
     simpl.
    iSplit.
    { iPureIntro. by eapply gnames_coh_update_history. }
    iSplit; first done.
    iSplit.
    { iPureIntro. by eapply messages_history_coh_send. }
    assert (T = {[msg]} ∪ T) as <- by set_solver.
    rewrite insert_id; last done.
    iFrame.
  Qed.


   Lemma aneris_state_interp_receive_some a sh skt
        (Ψo : option (socket_interp Σ))  σ1 Sn r R T m :
     let ip := ip_of_address a in
     let S' := <[ip :=<[sh:=(skt, r ∖ {[m]})]> Sn]> (state_sockets σ1) in
     let σ2 := σ1 <| state_sockets := S' |> in
     state_sockets σ1 !! ip = Some Sn →
     Sn !! sh = Some (skt, r) →
     saddress skt = Some a →
     m ∈ r →
    match Ψo with Some Ψ => a ⤇ Ψ | _ => True end -∗
    aneris_state_interp σ1 -∗
    sh ↪[ip] skt -∗
    a ⤳ (R, T) -∗
    ∃ R',
      ((⌜m ∉ R⌝ ∗
        ⌜R' = {[ m ]} ∪ R⌝ ∗
         ▷ match Ψo with Some Ψ => Ψ m | _ => ∃ φ, a ⤇ φ ∗ φ m end)
       ∨
       ⌜m ∈ R⌝ ∗ ⌜R' = R⌝)
     ∗ |==> aneris_state_interp σ2 ∗ sh ↪[ip_of_address a] skt ∗ a ⤳ (R', T).
   Proof. Admitted.
 (* iIntros (ip S' σ2 ??? [<- ?]%elem_of_filter) "HΨ [Hσ Hsh]". rewrite /σ2 /S'.
    destruct (decide (msg ∈ R)).
    - assert ({[msg]} ∪ R = R) as -> by set_solver.
      assert (<[sh:=(skt, R, T)]> Sn = Sn) as -> by apply insert_id=>//.
      assert (<[ip:=Sn]> (state_sockets σ1) = (state_sockets σ1))
        as -> by apply insert_id=>//.
      iExists R. iSplitR; eauto.
      iModIntro. iFrame; eauto.
    - iDestruct "Hσ" as (m) "(Hnauth & % & Hsock & Hlcoh & Hfreeips & Hnet)".
      iDestruct "Hsh" as (?) "[#Hn Hsh]".
      iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
      iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
        as "(Hstate & Hlcoh)"; [done|].
      iDestruct (network_coh_receive with "Hnet") as "[Hnet Hφ]"; [done..|].
      iExists ({[msg]} ∪ R). iSplitL "Hφ HΨ".
      { iLeft. do 2 (iSplitR; [done|]).
        destruct Ψo as [ψ|]; [|iNext; done].
        iDestruct "Hφ" as (φ) "[Hφ Hmsg]".
        iDestruct (socket_interp_agree _ _ _ msg with "HΨ Hφ") as "H".
        iNext. by iRewrite "H". }
      iMod (local_state_coh_update_ms with "[$Hstate Hsh]") as "[Hstate' Hsh]";
        [done|done|..].
      { iExists _; eauto. }
      iDestruct (big_sepM_local_state_coh_update_socket_notin with "Hlcoh") as "Hlcoh".
      { apply lookup_delete. }
      iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh") as "Hlcoh"; [done|].
      iModIntro. iFrame.
      iExists _; simpl. iFrame.
      iSplit; [|by iApply free_ips_coh_update_msg].
      iPureIntro; by eapply gnames_coh_update_sockets.
   Qed.  *)

End state_interpretation.

Global Opaque aneris_state_interp.


  (*Definition gset_ipofsa := gset_map ip_of_address.

  Definition messages_history_new_node ip ps mh :=
   set_fold (fun p acc => <[(SocketAddressInet ip p):=(∅, ∅)]> acc) mh ps.*)


  (* Definition get_message_history mh sa := *)
  (*   pms ← (mh !! (ip_of_address sa)); pms !! (port_of_address sa). *)
