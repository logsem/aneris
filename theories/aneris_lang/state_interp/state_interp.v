From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From iris.algebra Require Import auth excl.
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
     state_interp_config_wp
     auxiliary_state.

From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
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

  (* aneris_state_interp *)
  Lemma aneris_state_interp_init ips B A σ f M γs ip :
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
    messages_ctx (gset_to_gmap (∅, ∅) B)  -∗
    fixed A -∗
    saved_si_auth M -∗
    ([∗ set] a ∈ A, a ⤇ (f a)) -∗
    free_ips_auth ips -∗
    free_ports_auth ∅ -∗
    aneris_state_interp σ (∅, ∅).
  Proof.
    iIntros (HMdom Hipdom Hpiiu Hfixdom Hste Hsce Hmse Hip)
            "Hmp #Hn Hh Hs Hm #Hsif HM #Hsa HipsCtx HPiu".
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

  Lemma aneris_state_interp_free_ip_valid σ ip mh:
    aneris_state_interp σ mh -∗
    free_ip ip -∗
    ⌜state_heaps σ !! ip = None ∧
     state_sockets σ !! ip = None ∧
     is_Some (state_ports_in_use σ !! ip)⌝.
  Proof.
    iDestruct 1 as (mγ mn) "(?&?&%&?&?& Hsi & Hlcoh & Hfreeips & ?)".
    iIntros "Hfip".
    iDestruct "Hfreeips"
      as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iDestruct (free_ip_included with "HfCtx Hfip") as %Hin.
    iPureIntro. destruct (HFip2 _ Hin) as [??]. eauto.
  Qed.

  Lemma aneris_state_interp_free_ports_valid σ a mh :
    aneris_state_interp σ mh -∗
    free_ports (ip_of_address a) {[port_of_address a]} -∗
    ∃ ps, ⌜state_ports_in_use σ !! ip_of_address a = Some ps ∧
           port_of_address a ∉ ps⌝.
  Proof.
    iDestruct 1 as (mγ mn) "(?&?&?&%&?&?& Hsi & Hlcoh & Hfreeips & ?)".
    by iApply free_ips_coh_free_ports_valid.
  Qed.

  Lemma aneris_state_interp_alloc_node σ ip ports mh :
    aneris_state_interp σ mh ∗ free_ip ip ==∗
    ⌜network_sockets_coh (state_sockets σ) (state_ports_in_use σ)⌝ ∗
    is_node ip ∗ free_ports ip ports ∗
    aneris_state_interp
      (σ <| state_heaps   := <[ip:=∅]> (state_heaps σ)|>
         <| state_sockets := <[ip:=∅]> (state_sockets σ) |>)
      mh.
  Proof.
    iIntros "[Hσ Hfip]".
    iDestruct (aneris_state_interp_free_ip_valid with "Hσ Hfip")
      as "(% & % & %)".
    iDestruct "Hσ"
      as (mγ mh')
           "(%Hhst & %Hgcoh & %Hnscoh & %Hmhcoh
                     & Hnauth & Hsi & Hlcoh & HFip & Hmctx & Hmres)".
    iMod (free_ips_coh_alloc_node _ _ ports with "HFip Hfip")
      as "[HFip Hports]".
    iMod (node_ctx_init ∅ ∅) as (γn) "(Hh & Hs)".
    assert (mγ !! ip = None) as Hnone by eapply gnames_coh_valid=>//.
    iMod (node_gnames_alloc γn with "Hnauth") as "[Hnauth #Hγn]"; [done|].
    set σ' := (σ <| state_heaps   := <[ip:=∅]> (state_heaps σ)|>
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
      (saddress skt = None → r = ∅)⌝.
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
      specialize (Hnscoh ip Sn Hp1) as (?&?&?&?&Hb).
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
                   <[ip:=<[sh:=(s, ∅)]> Sn]> (state_sockets σ) |> in
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

  Lemma aneris_state_interp_socketbind_static σ1 a sh skt ps Sn A mh :
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
    aneris_state_interp σ1 mh -∗
    fixed A -∗
    sh ↪[ip_of_address a] skt -∗
    free_ports ip {[port_of_address a]} ==∗
    aneris_state_interp σ2 mh ∗ sh ↪[ip] (skt<| saddress := Some a |>) ∗
    ∃ φ, a ⤇ φ.
  Proof.
    simpl. iIntros (?????) "Hσ #HA Hsh Hp".
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
    iDestruct (free_ips_coh_free_ports_valid with "Hfreeips Hp")
      as (?) "[% %]".
    iDestruct (socket_interp_coh_fixed_valid with "Hsi HA") as "#$"; [done|].
    iMod (free_ips_coh_dealloc _ _ sh skt with "Hfreeips Hp")
      as "Hfreeips"; [done..|].
    iModIntro. iExists mγ, _. iFrame. rewrite /set /=.
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

  Lemma aneris_state_interp_socketbind_dynamic σ1 a sh skt ps Sn A φ mh :
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
    aneris_state_interp σ1 mh -∗
    fixed A -∗
    sh ↪[ip_of_address a] skt -∗
    free_ports ip {[port_of_address a]} ==∗
    aneris_state_interp σ2 mh ∗ sh ↪[ip] (skt<| saddress := Some a |>) ∗
    a ⤇ φ.
  Proof.
      simpl. iIntros (?????) "Hσ #HA Hsh Hp".
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
    iDestruct (free_ips_coh_free_ports_valid with "Hfreeips Hp")
      as (?) "[% %]".
     iMod (socket_interp_coh_socketbind_dynamic with "HA Hsi")
      as "[Hsi #$]"; try done.
    iMod (free_ips_coh_dealloc _ _ sh skt with "Hfreeips Hp")
      as "Hfreeips"; [done..|].
    iModIntro. iExists mγ, _. iFrame. rewrite /set /=.
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

  Lemma aneris_state_interp_send sh a skt Sn r R T φ to mbody σ1 mh:
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
    aneris_state_interp σ1 mh ==∗
    ⌜(mh.1, {[msg]} ∪ mh.2) =
    message_history_evolution
      (state_ms σ1) M' (state_sockets σ1) (state_sockets σ1) mh⌝ ∗
    aneris_state_interp σ2 (mh.1, {[msg]} ∪ mh.2) ∗
    sh ↪[ip_of_address a] skt ∗
    a ⤳ (R, {[msg]} ∪ T).
  Proof.
    simpl.
    iIntros (HS HSn Hskt) "Hsh Hrt #Hφ Hmsg Hσ".
    iDestruct "Hσ"
      as (mγ mh')
           "(%Hhst & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    set (msg := {|
               m_sender := a;
               m_destination := to;
               m_protocol := sprotocol skt;
               m_body := mbody |}).
    iDestruct (messages_mapsto_valid with "Hrt Hmctx") as %Hma.
    destruct (decide (msg ∈ T)).
    -  assert (T = {[msg]} ∪ T) as <- by set_solver.
       iFrame. iModIntro.
       iSplit. iPureIntro.
       destruct Hmhcoh as (Hmscoh & ? & ? & ?).
       eapply message_history_evolution_send_message.
       rewrite /messages_received_sent in Hhst.
       inversion Hhst as [[ Hrcvd Hsent ]].
       simplify_eq /=.
       intros m0 Hm0.
       apply elem_of_messages_sent.
       apply Hmscoh in Hm0 as (R0 & T0 & ?).
       exists (m_sender m0), (R0,T0). set_solver.
       iExists mγ, (<[a:=(R, T)]> mh'). iFrame.
       simpl.
       rewrite {2 3 4} (insert_id mh'); eauto.
       iFrame.
       iPureIntro; split_and!; eauto.
       + rewrite /messages_received_sent.
         rewrite /messages_received_sent in Hhst.
         apply insert_id in Hma. simplify_eq /=.
         rewrite - {3 4} Hma.
         rewrite !messages_sent_insert.
         rewrite !messages_received_insert.
         assert (T = {[msg]} ∪ T) as Ht by set_solver.
         rewrite {1} Ht. f_equal; set_solver.
       + assert (mh' = <[a := (R, {[msg]} ∪ T)]> mh') as ->.
         assert (T = {[msg]} ∪ T) as <- by set_solver.
           by rewrite insert_id. by eapply messages_history_coh_send.
    - iMod (messages_mapsto_update a R T R ({[msg]} ∪ T) mh'
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
       apply Hmscoh in Hm0 as (R0 & T0 & ?).
       exists (m_sender m0), (R0,T0). set_solver.
      iExists mγ, (<[a:=(R, {[msg]} ∪ T)]> mh'). iFrame.
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
       iSplit.
       { iPureIntro. by eapply messages_history_coh_send. }
       iApply (messages_resource_coh_send with "[Hφ] [$Hmres] [Hmsg]"); eauto.
       by destruct Hmhcoh; intuition.
  Qed.

  Lemma aneris_state_interp_send_duplicate sh a skt Sn r R T to mbody σ1 mh :
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
    aneris_state_interp σ1 mh ==∗
     ⌜(mh.1, mh.2) =
    message_history_evolution
      (state_ms σ1) M' (state_sockets σ1) (state_sockets σ1) mh⌝ ∗
    aneris_state_interp σ2 mh ∗ sh ↪[ip_of_address a] skt ∗
    a ⤳ (R, T).
  Proof.
    simpl. iIntros (HS HSn Hskt Hmsg) "Hsh Hrt Hσ".
    iDestruct "Hσ"
      as (mγ mh')
           "(%Hhst & %Hgcoh & %Hnscoh & %Hmhcoh
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
     iSplit. rewrite - /msg in Hmsg.
     iPureIntro.
     destruct Hmhcoh as (Hmscoh & ? & ? & ?).
     eapply message_history_evolution_send_duplicate_message.
     rewrite /messages_received_sent in Hhst.
     inversion Hhst as [[ Hrcvd Hsent ]].
     simplify_eq /=.
     apply elem_of_messages_sent.
     exists (m_sender msg), (R,T). set_solver.
     iExists mγ, mh'. simpl. iSplit.
     { iPureIntro. eauto. } iFrame.
     iPureIntro; split_and!; eauto.
     assert (mh' = (<[a:=(R, {[msg]} ∪ T)]> mh')) as ->.
     assert (T = {[msg]} ∪ T) as <- by set_solver.
       by rewrite insert_id. by eapply messages_history_coh_send.
  Qed.

  Lemma aneris_state_interp_receive_some a sh skt
        (Ψo : option (socket_interp Σ))  σ1 Sn r R T m mh :
    let ip := ip_of_address a in
    let S' := <[ip :=<[sh:=(skt, r ∖ {[m]})]> Sn]> (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    saddress skt = Some a →
    m ∈ r →
    match Ψo with Some Ψ => a ⤇ Ψ | _ => True end -∗
    aneris_state_interp σ1 mh -∗
    sh ↪[ip] skt -∗
    a ⤳ (R, T) -∗
    ∃ R',
      ⌜m_destination m = a⌝ ∗
      ⌜(R' ∪ mh.1, mh.2) =
      message_history_evolution
        (state_ms σ1) (state_ms σ1) (state_sockets σ1) S'  mh⌝ ∗
      ((⌜m ∉ R⌝ ∗
        ⌜R' = {[ m ]} ∪ R⌝ ∗
         ▷ match Ψo with Some Ψ => Ψ m | _ => ∃ φ, a ⤇ φ ∗ φ m end)
       ∨
       ⌜m ∈ R⌝ ∗ ⌜R' = R⌝)
      ∗ |==> aneris_state_interp σ2 (R' ∪ mh.1, mh.2)
      ∗ sh ↪[ip_of_address a] skt ∗ a ⤳ (R', T).
   Proof.
     simpl. iIntros (HS HSn Hskt Hmsg) "#Hproto Hσ Hsh Ha".
     iDestruct "Hσ"
       as (mγ mh')
           "(%Hhst & %Hgcoh & %Hnscoh & %Hmhcoh
                    & Hnauth & Hsi & Hlcoh & Hfreeips & Hmctx & Hmres)".
    iDestruct (mapsto_socket_node with "Hsh") as (γs) "(#Hn & Hsh)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    assert ( network_sockets_coh (state_sockets σ1) (state_ports_in_use σ1))
           as Hnscoh2 by eauto.
    destruct (Hnscoh (ip_of_address a) Sn)
      as (Hbcoh & Hshcoh & Hsmcoh & Hsacoh & Hsucoh);
      first done.
    iDestruct (messages_mapsto_valid with "[$Ha] [$Hmctx]") as %Hmha.
    assert (m_destination m = a) as Hma by by eapply Hsmcoh.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iDestruct (local_state_coh_update_rb a sh skt σ1 γs Sn r (r ∖ {[m]})
                 with "[$Hstate $Hsh]") as "Hstate"; eauto.
    destruct (decide (m ∈ R)).
    - iExists R.  iSplit; first done. iSplitR.
      assert (R = {[m]} ∪ R) as -> by set_solver.
      iPureIntro.
      destruct Hmhcoh as (? & Hrscoh & Hacoh & Hrsbcoh).
      eapply message_history_evolution_receive; eauto.
      intros ???. destruct (Hnscoh2 ip Sn0); eauto. naive_solver.
      rewrite /messages_received_sent in Hhst.
      inversion Hhst as [[ Hrcvd Hsent ]].
      simplify_eq /=.
      intros m0 Hm0.
      apply elem_of_messages_received.
      exists (m_destination m0), (R,T); split; last done.
      assert (m_destination m0 = m_destination m) as ->; last done.
      specialize (Hacoh (m_destination m) _ _ Hmha) as (Hacoh & _).
      eauto.
      iSplitR; eauto.
      iMod "Hstate" as "(Hstate & Hsh)".
      iDestruct (big_sepM_local_state_coh_insert
                   with "[$Hstate] [Hlcoh]") as "Hlcoh"; eauto.
      { iApply (big_sepM_mono with "Hlcoh").
        iIntros (ip' γs' Hdel) "Hlcoh".
        ddeq ip' (ip_of_address a).
        rewrite lookup_delete_ne in Hdel; last done.
        iDestruct "Hlcoh" as (h' s') "Hlcoh".
        iExists h', s'. rewrite !lookup_insert_ne; eauto. }
      iModIntro. iFrame.
      iExists mγ, mh'. simpl. iFrame. simpl. iSplit; eauto. iPureIntro.
      { rewrite /messages_received_sent.
        rewrite /messages_received_sent in Hhst.
        destruct mh. simplify_eq /=.
        f_equal.
        assert (R ⊆ messages_received mh').
        apply insert_id in Hmha. rewrite -Hmha.
        rewrite messages_received_insert. set_solver.
        set_solver. }
      iPoseProof
        (free_ips_coh_update_msg with "Hfreeips") as "Hfreeips"; eauto.
      iFrame. iPureIntro.
      split_and!.
      + by eapply gnames_coh_update_sockets.
      + by eapply network_sockets_coh_receive.
      + by eapply messages_history_coh_receive; eauto.
    - iExists ({[m]} ∪ R). iSplit; first done.
      destruct Hmhcoh as (? & Hrscoh & Hacoh & Hrsbcoh).
      assert ( ∃ R T, mh' !! m_sender m = Some (R, T) ∧ m ∈ T) as Hrcoh2.
      { destruct (Hrscoh (ip_of_address a) Sn sh skt r m HS HSn Hmsg).
        eauto. } destruct Hrcoh2 as (R'&T'&Hmh&Hm).
      iPoseProof
        (messages_resource_coh_receive with "Hmres")
        as "(Hmres & Hres)"; eauto.
      iSplitR.
      iPureIntro.
      eapply message_history_evolution_receive; eauto.
      intros ???. destruct (Hnscoh2 ip Sn0); eauto. naive_solver.
      rewrite /messages_received_sent in Hhst.
      inversion Hhst as [[ Hrcvd Hsent ]].
      simplify_eq /=.
      intros m0 Hm0.
      apply elem_of_messages_received.
      exists (m_destination m0), (R,T); split; last done.
      assert (m_destination m0 = m_destination m) as ->; last done.
      specialize (Hacoh (m_destination m) _ _ Hmha) as (Hacoh & _).
      eauto.
      iSplitL "Hres".
      { iLeft. iSplit; eauto. iSplit; eauto. destruct Ψo as [ψ|]; [|iNext].
        iDestruct "Hres" as (φ) "(Hφ & Hres)". rewrite Hma.
        iPoseProof (socket_interp_agree _ _ _ m  with "Hproto Hφ") as "Heq".
        iNext. by iRewrite "Heq". rewrite Hma. iFrame. }
      iMod "Hstate" as "(Hstate & Hsh)".
      iDestruct (big_sepM_local_state_coh_insert
                   with "[$Hstate] [Hlcoh]") as "Hlcoh"; eauto.
      { iApply (big_sepM_mono with "Hlcoh").
        iIntros (ip' γs' Hdel) "Hlcoh".
        ddeq ip' (ip_of_address a).
        rewrite lookup_delete_ne in Hdel; last done.
        iDestruct "Hlcoh" as (h' s') "Hlcoh".
        iExists h', s'. rewrite !lookup_insert_ne; eauto. }
      iMod (messages_mapsto_update a R T ({[m]} ∪ R) T mh'
           with "[$Ha $Hmctx]") as "[Hmctx Ha]".
      iModIntro. iFrame.
      iExists mγ, (<[a:=({[m]} ∪ R, T)]> mh').
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

   Lemma aneris_state_interp_model m1 m2 σ (δ1: aneris_aux_state) κs n:
     state_interp σ δ1 κs n -∗ frag_st m1 ==∗
     state_interp σ
     ({| aneris_AS_mhist := aneris_AS_mhist δ1; aneris_AS_model := m2 |}: aux_state aneris_AS)
     κs n ∗
     frag_st m2.
   Proof.
     iIntros "[? Hauth] Hfrag".
     iMod ((own_update _
                       (● (Excl' (aneris_AS_model δ1)) ⋅ ◯ (Excl' m1))
                       (● (Excl' m2) ⋅ ◯ (Excl' m2))
           ) with "[Hauth Hfrag]") as "[??]".
     { apply auth_update. apply option_local_update.
       eapply exclusive_local_update. by vm_compute. }
     { by iCombine "Hauth Hfrag" as "H". }
     iModIntro. iFrame.
   Qed.

   Lemma aneris_state_interp_model_agree m σ (δ: aneris_aux_state) κs n:
     state_interp σ δ κs n -∗ frag_st m -∗ ⌜ δ.(aneris_AS_model) = m ⌝.
   Proof.
     iIntros "[_ Ha] Hf". iDestruct (own_valid_2 with "Ha Hf") as "%H".
     iPureIntro. apply leibniz_equiv.
     apply auth_both_valid_discrete in H as [H Hval].
     by apply Excl_included in H.
   Qed.

   Definition messages_sent_from (a: socket_address) (rt: messages_history):
     message_soup :=
     filter (fun m => m.(m_sender) = a) rt.2.

   Lemma aneris_state_interp_sent_mapsto_agree a R T δ σ κs n:
     a ⤳ (R, T) -∗ state_interp σ δ κs n -∗
       ⌜ messages_sent_from a δ.(aneris_AS_mhist) = T ⌝.
   Proof.
     iIntros "Hlt Hsi".
   Admitted.


End state_interpretation.

Global Opaque aneris_state_interp.
