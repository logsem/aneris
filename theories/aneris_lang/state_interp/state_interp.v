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
     ip ∉ (gset_map ip_of_address (dom (gset socket_address) mh)) →
     mapsto_node ip γn -∗
     messages_ctx mh ==∗
                  messages_ctx ((history_init ip ports) ∪ mh) ∗
                  ([∗ set] p ∈ ports, SocketAddressInet ip p ⤳ (∅, ∅)).
  Proof.
  (*   revert σ;
       induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (gen_heap_light_alloc with "Hσ'σ") as "($ & $ & $)";
      first by apply lookup_union_None.
  Qed. *)
  Admitted.



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
    iPoseProof (messages_ctx_alloc_node ip γn ports with "Hγn Hmctx")
      as ">(Hmctx & Hmto)".
    { destruct Hgcoh as (? & ? & Hdom).
      apply not_elem_of_dom in Hnone.
      by rewrite Hdom in Hnone. }
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
      (* apply messages_history_coh_alloc_node. *)
      admit. }
    iSplitL "Hh Hs Hlcoh".
    { iApply (big_sepM_local_state_coh_insert ip γn
                with "[Hh Hs] [Hlcoh]").
      - rewrite lookup_insert //.
      - iExists ∅, ∅.
        iFrame. iFrame "#". rewrite !lookup_insert fmap_empty.
        repeat iSplit; eauto.
      - rewrite delete_insert //.
          by iApply big_sepM_local_state_coh_alloc_node. }
    admit.
  Admitted.

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
    (* rewrite mapsto_socket_eq. *)
  (*   iDestruct "Hsh" as (γs' r) "[#Hip Hsh]". *)
  (*   iDestruct (node_gnames_valid with "Hnauth Hip") as "%Hmin". *)
  (*   iPoseProof (local_state_coh_valid_sockets  _ _ γs' _ q with "[Hlcoh] [Hsh]") *)
  (*     as (Sn r0 ) "(%Hp1 & %Hp2)". *)
  (*   - iDestruct (big_sepM_lookup with "Hlcoh") as "Hl"; done. *)
  (*   - rewrite mapsto_socket_eq. *)
  (*     unfold mapsto_socket_def. *)
  (*     eauto with iFrame. *)
  (*   - iExists Sn, r0. *)
  (*     iPureIntro. *)
  (*     repeat split; try done. *)
  (*     specialize (Hnscoh ip Sn Hp1) as (?&?&?&?&Hb). *)
  (*     by eapply Hb. *)
  (* Qed. *)
  Admitted.

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


  Lemma mapsto_socket_mapsto_node h s ip :
    h ↪[ip] s ⊢ h ↪[ip] s ∗ ∃ γs, mapsto_node ip γs.
  Proof.
    rewrite /mapsto_socket.
    iDestruct 1 as (γs') "[#Hn Hsh]".
    iSplitL; eauto with iFrame.
  Qed.

  Lemma aneris_state_interp_socketbind_static σ1 a sh skt ps Sn A r :
    let ip := ip_of_address a in
    let S' :=
        <[ip := <[sh:=(skt<| saddress := Some a |>, r)]> Sn]>
        (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
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
    iDestruct (mapsto_socket_mapsto_node with "Hsh") as "(Hsh & #Hn)".
    iDestruct "Hn" as (γs) "Hn".
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
    { iPureIntro. admit. }
    iSplitR.
    { iPureIntro. admit. }
    iSplitL "Hsi".
    {  iApply socket_interp_coh_socketbind_static; eauto with set_solver. }
    iFrame.
    admit.
      (* by iApply network_coh_socketbind. *)
  Admitted.

  Lemma aneris_state_interp_socketbind_dynamic σ1 a sh skt ps Sn A φ r:
    let ip := ip_of_address a in
    let S' :=
        <[ip := <[sh:=(skt<| saddress := Some a |>, r)]> Sn]>
        (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
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
  Admitted.
 (*
  Proof.
    simpl. iIntros (?????) "Hσ #HA Hsh Hp".
    iDestruct "Hσ" as (m) "(Hnauth & % & Hsock & Hlcoh & Hfreeips & Hnet)".
    iDestruct "Hsh" as (?) "[#Hn Hsh]".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_socketbind with "[$Hstate Hsh]") as "[Hstate' $]"; try done.
    { iExists _; eauto. }
    iDestruct (big_sepM_local_state_coh_update_socket_notin with "Hlcoh") as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh") as "Hlcoh"; [done|].
    iDestruct (free_ips_coh_free_ports_valid with "Hfreeips Hp") as (?) "[% %]".
    iMod (socket_interp_coh_socketbind_dynamic with "HA Hsock")
      as "[Hsock #$]"; try done.
    simplify_eq.
    iMod (free_ips_coh_dealloc with "Hfreeips Hp") as "Hfreeips"; [done..|].
    iModIntro. iExists _. iFrame. rewrite /set /=.
    iSplit.
    { iPureIntro; by eapply gnames_coh_update_sockets. }
    by iApply network_coh_socketbind.
  Qed.
  *)

(*
  Lemma aneris_state_interp_send sh a skt Sn R T φ to mbody σ1 :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) mbody in
    let S' := <[ip := <[sh:=(skt, R, {[msg]} ∪ T)]> Sn]> (state_sockets σ1) in
    let M' := {[msg]} ∪ state_ms σ1 in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ms := M' |> in
    state_sockets σ1 !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    sh ↪[ip_of_address a] (skt, R, T) -∗
    to ⤇ φ -∗
    φ msg -∗
    aneris_state_interp σ1 ==∗
    aneris_state_interp σ2 ∗ sh ↪[ip_of_address a] (skt, R, {[msg]} ∪ T).
  Proof.
    iIntros (????????) "Hsh #Hφ Hmsg Hσ".
    iDestruct "Hσ" as (m) "(Hnauth & % & Hsock & Hlcoh & Hfreeips & Hnet)".
    iDestruct "Hsh" as (?) "[#Hn Hsh]".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_update_ms with "[$Hstate Hsh]") as "[Hstate' Hsh]";
      [done|done|..].
    { iExists _; eauto. }
    iDestruct (big_sepM_local_state_coh_update_socket_notin with "Hlcoh") as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh") as "Hlcoh"; [done|].
    iModIntro. iFrame. iExists _. iFrame. simpl.
    iSplit.
    { iPureIntro; by eapply gnames_coh_update_sockets. }
    iSplitL "Hfreeips".
    { by iApply (free_ips_coh_update_msg with "Hfreeips"). }
    rewrite /msg.
    by iApply (network_coh_insert_sent with "Hφ Hmsg Hnet").
  Qed.

  Lemma aneris_state_interp_send_duplicate sh a skt Sn R T to mbody σ1 :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) mbody in
    let S' := <[ip := <[sh:=(skt, R, {[msg]} ∪ T)]> Sn]> (state_sockets σ1) in
    let M' := {[msg]} ∪ state_ms σ1 in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ms := M' |> in
    state_sockets σ1 !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    msg ∈ T →
    sh ↪[ip_of_address a] (skt, R, T) -∗
    aneris_state_interp σ1 ==∗
    aneris_state_interp σ2 ∗ sh ↪[ip_of_address a] (skt, R, T).
  Proof.
    iIntros (????? HSn ???) "Hsh Hσ".
    iDestruct "Hσ" as (m) "(Hnauth & % & Hsock & Hlcoh & Hfreeips & Hnet)".
    iDestruct "Hsh" as (?) "[#Hn Hsh]".
    iDestruct (network_coh_sent_valid with "Hnet") as "%"; [done..|].
    iModIntro. rewrite /σ2 /M' /S' /ip.
    assert (T = {[msg]} ∪ T) as <- by set_solver.
    assert ({[msg]} ∪ state_ms σ1 = state_ms σ1) as -> by set_solver.
    assert (<[ip_of_address a := <[sh:=(skt, R, T)]> Sn]> (state_sockets σ1) =
            state_sockets σ1) as -> by rewrite !insert_id //.
    iSplitR "Hsh"; [|iExists _; eauto].
    iExists _; iFrame; eauto.
  Qed.

  Lemma aneris_state_interp_receive a sh skt msg (Ψo : option (socket_interp Σ))  σ1 Sn R T :
    let ip := ip_of_address a in
    let S' := <[ip :=<[sh:=(skt, {[msg]} ∪ R, T)]> Sn]> (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    msg ∈ messages_to_receive_at a (state_ms σ1) →
    match Ψo with Some Ψ => a ⤇ Ψ | _ => True end -∗
    aneris_state_interp σ1 ∗ sh ↪[ip] (skt, R, T) -∗ ∃ R' ,
    ((⌜msg ∉ R⌝ ∗ ⌜R' = {[ msg ]} ∪ R⌝ ∗
         ▷ match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
     ⌜msg ∈ R⌝ ∗ ⌜R' = R⌝) ∗
    |==> aneris_state_interp σ2 ∗ sh ↪[ip_of_address a] (skt, R', T).
  Proof.
    iIntros (ip S' σ2 ??? [<- ?]%elem_of_filter) "HΨ [Hσ Hsh]". rewrite /σ2 /S'.
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
   Qed. *)

End state_interpretation.

Global Opaque aneris_state_interp.


  (*Definition gset_ipofsa := gset_map ip_of_address.

  Definition messages_history_new_node ip ps mh :=
   set_fold (fun p acc => <[(SocketAddressInet ip p):=(∅, ∅)]> acc) mh ps.*)


  (* Definition get_message_history mh sa := *)
  (*   pms ← (mh !! (ip_of_address sa)); pms !! (port_of_address sa). *)
