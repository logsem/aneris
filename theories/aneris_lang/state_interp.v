From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang notation network resources.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

(* TODO: come up with something more reliable *)
Ltac ddeq k1 k2 :=
  destruct (decide (k1 = k2)); subst;
  repeat
    match goal with
    | Hyp : context[ (<[_:=_]>_) !! _ ] |- _ =>
      rewrite lookup_insert in Hyp || (rewrite lookup_insert_ne in Hyp; last done);
      simplify_eq /=
    | Hyp : is_Some _ |- _ => destruct Hyp
    | |- context[ (<[_:=_]>_) !! _ ] =>
      rewrite lookup_insert || (rewrite lookup_insert_ne; last done);
      simplify_eq /=
    |  H1 : ?x = ?z, Heq : ?x = ?y |- _ =>
       rewrite Heq in H1; simplify_eq /=; try eauto
    | Hdel : context[ delete ?n ?m !! ?n = _] |- _ =>
      rewrite lookup_delete in Hdel; simplify_eq /=
    end.

Section definitions.
  Context `{anerisG Σ}.
  Implicit Types σ : state.
  Implicit Types h : heap.
  Implicit Types H : gmap ip_address heap.
  Implicit Types S : gmap ip_address sockets.
  Implicit Types Sn : sockets .
  Implicit Types P : ports_in_use.
  Implicit Types ps : gset port.
  Implicit Types ips : gset ip_address.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types A B : gset socket_address.
  Implicit Types sis : gmap socket_address gname.
  Implicit Types a : socket_address.
  Implicit Types ip : ip_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.
  Implicit Types γm : gmap ip_address node_gnames.

  (* The domains of heaps and sockets coincide with the gname map [γm] *)
  Definition gnames_coh γm H S :=
    dom (gset ip_address) γm = dom (gset ip_address) H ∧
    dom (gset ip_address) γm = dom (gset ip_address) S.

  (* Addresses with socket interpretations are bound *)
  Definition socket_interp_coh P :=
    (∃ sis A,
        (* [A] is the set of addresses with fixed interpretations *)
        fixed A ∗
        (* [si] is the map from addresses to name of saved socket interpretations *)
        saved_si_auth sis ∗
        (* there exists a socket interpretation for all addresses in this map *)
        ([∗ set] s ∈ (dom (gset socket_address) sis), ∃ φ, s ⤇ φ) ∗
        (* the addresses in A are in the domain of P *)
        ⌜∀ a, a ∈ A → ip_of_address a ∈ dom (gset ip_address) P⌝ ∗
        (* all addresses in [si] either have a fixed interpretation ([a ∈ A]) or
           are dynamically bound. *)
        ⌜∀ a, (ip_of_address a ∈ dom (gset ip_address) P) →
              (a ∈ dom (gset socket_address) sis ↔
                 a ∈ A ∨ (a ∉ A ∧ ∀ ps, P !! ip_of_address a = Some ps →
                                        port_of_address a ∈ ps))⌝)%I.

  (* The local state of the node at [ip] is coherent with [σ] and [γs] *)
  Definition local_state_coh σ ip γs :=
    (∃ h Sn ,
        (* there should be a heap *)
        ⌜state_heaps σ !! ip = Some h⌝ ∗
        (* there should be a socket map *)
        ⌜state_sockets σ !! ip = Some Sn⌝ ∗
        (* it's a valid node *)
        mapsto_node ip γs ∗
        (* we own the authoritative part of the heap and sockets *)
        heap_ctx γs h ∗
        sockets_ctx γs Sn)%I.

  (* The ports of all bound addresses in [Sn] are also in [P] *)
  Definition bound_ports_coh Sn P :=
    ∀ sh skt a ps R T,
      Sn !! sh = Some (skt, R, T) →
      saddress skt = Some a →
      P !! ip_of_address a = Some ps →
      (port_of_address a) ∈ ps.

  (* All sockets in [Sn] with the same address have the same handler *)
  Definition socket_handlers_coh Sn  :=
    ∀ sh sh' skt skt' R R' T T',
      Sn !! sh = Some (skt, R, T) →
      Sn !! sh' = Some (skt', R', T') →
      is_Some (saddress skt) →
      saddress skt = saddress skt' →
      sh = sh'.

  (* Sent and received messages at all socket in [Sn] are in [M] *)
  Definition socket_messages_coh Sn M :=
    ∀ sh skt R T a,
      Sn !! sh = Some (skt, R, T) →
      saddress skt = Some a →
      (∀ m, m ∈ R → m_destination m = a ∧ m ∈ M) ∧
      (∀ m, m ∈ T → m_sender m = a ∧ m ∈ M).

  (* all sockets in [Sn] are bound to ip address [ip] *)
  Definition socket_addresses_coh Sn ip :=
    ∀ sh skt R T a,
      Sn !! sh = Some (skt, R, T) →
      saddress skt = Some a →
      ip_of_address a = ip.

  (* The sockets, ports, and message in [S], [M], and [P] are coherent *)
  Definition network_sockets_coh S M P :=
    ∀ ip Sn,
      S !! ip = Some Sn →
      bound_ports_coh Sn P ∧
      socket_handlers_coh Sn ∧
      socket_messages_coh Sn M ∧
      socket_addresses_coh Sn ip.

  (* [m] has been received *)
  Definition message_received S m :=
    ∃ Sn sh skt a R T,
      S !! ip_of_address a = Some Sn ∧
      Sn !! sh = Some (skt, R, T) ∧
      saddress skt = Some a ∧
      m ∈ R.

  (* For all messages [m] in [M], either the network owns the resources [Φ m]
     described by some socket protocol [Φ] or it has been delivered *)
  Definition network_messages_coh S M :=
    ([∗ set] m ∈ M,
     (* either [m] is governed by a protocol and the network owns the resources *)
     (∃ (Φ : socket_interp Σ), (m_destination m) ⤇ Φ ∗ ▷ Φ m) ∨
     (* or [m] has been delivered somewhere *)
     ⌜message_received S m⌝)%I.

  Definition network_coh S M P :=
    (⌜network_sockets_coh S M P⌝ ∗ network_messages_coh S M)%I.

  (* Free ips have no bound ports, no heap, and no sockets  *)
  Definition free_ips_coh σ :=
    (∃ free_ips free_ports,
        (* the domains of [free_ips] and [free_ports] are disjoint *)
        (⌜dom (gset _) free_ports ## free_ips ∧
         (* if the ip [ip] is free, no ports have been bound  *)
         (∀ ip, ip ∈ free_ips → state_ports_in_use σ !! ip = Some ∅) ∧
         (* if the ip [ip] is free, neither a heap nor a socket map has been
            allocated *)
         (∀ ip, ip ∈ free_ips →
                state_heaps σ !! ip = None ∧ state_sockets σ !! ip = None) ∧
         (* free ports and bound ports are disjoint *)
         (∀ ip ps, free_ports !! ip = Some (GSet ps) →
             ∃ bound_ports,
               (state_ports_in_use σ) !! ip = Some bound_ports ∧
               ps ## bound_ports )⌝) ∗
         (* we have the auth parts of the resources for free ips and ports *)
         free_ips_auth free_ips ∗
         free_ports_auth free_ports)%I.

  Definition aneris_state_interp σ :=
    (∃ γm,
        node_gnames_auth γm ∗
        ⌜gnames_coh γm (state_heaps σ) (state_sockets σ)⌝ ∗
        socket_interp_coh (state_ports_in_use σ) ∗
        ([∗ map] ip ↦ γs ∈ γm, local_state_coh σ ip γs) ∗
        free_ips_coh σ ∗
        network_coh (state_sockets σ) (state_ms σ) (state_ports_in_use σ)
    )%I.

End definitions.

Global Instance anerisG_irisG `{!anerisG Σ} : irisG aneris_lang Σ := {
  iris_invG := _;
  state_interp σ κ _ := aneris_state_interp σ;
  fork_post _ := True%I;
}.

Global Opaque iris_invG.

Section state_interpretation.
  Context `{!anerisG Σ}.

  (** local_state_coh *)
  Lemma local_state_coh_heaps n γs γm σ :
    γm !! n = Some γs →
    ([∗ map] n' ↦ γs ∈ γm, local_state_coh σ n' γs) -∗
    ∃ h, ⌜(state_heaps σ) !! n = Some h⌝.
  Proof.
    iIntros (?) "Hmap".
    iDestruct (big_sepM_lookup with "Hmap") as "Hl"; [done|].
    iDestruct "Hl" as (???) "(% & _)"; eauto.
  Qed.

  Lemma local_state_coh_sockets n γs γm σ :
    γm !! n = Some γs →
    ([∗ map] n' ↦ γs ∈ γm, local_state_coh σ n' γs) -∗
    ∃ Sn, ⌜(state_sockets σ) !! n = Some Sn⌝.
  Proof.
    iIntros (?) "Hmap".
    iDestruct (big_sepM_lookup with "Hmap") as "Hl"; [done|].
    iDestruct "Hl" as (??) "(_ & % & _)"; eauto.
  Qed.

  Lemma local_state_coh_alloc_heap σ n γs l v h :
    let σ' := σ <| state_heaps := <[n:=<[l:=v]> h]> (state_heaps σ) |> in
    state_heaps σ !! n = Some h →
    h !! l = None →
    is_node n -∗
    local_state_coh σ n γs ==∗ local_state_coh σ' n γs ∗ l ↦[n] v.
  Proof.
    simpl. iIntros (??) "Hn Hstate". iDestruct "Hn" as (?) "#Hn".
    iDestruct "Hstate" as (h' S Hh Hs) "(Hn' & Hheap & ?)".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    simplify_eq.
    iMod (gen_heap_light_alloc with "Hheap") as "[Hheap Hl]"; [done|].
    iModIntro. iFrame.
    iSplitR "Hl"; [| iExists _; eauto].
    iExists _, _. iFrame.
    rewrite lookup_insert //.
  Qed.

  Lemma local_state_coh_valid_heap σ n γs l v q :
    local_state_coh σ n γs -∗
    l ↦[n]{q} v -∗
    ∃ h, ⌜state_heaps σ !! n = Some h ∧ h !! l = Some v⌝.
  Proof.
    iDestruct 1 as (h' S Hh Hs) "(Hn & Hheap & ?)".
    iDestruct 1 as (γs') "[Hn' Hl]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    iDestruct (gen_heap_light_valid with "Hheap Hl") as "%".
    iExists _. iPureIntro; eauto.
  Qed.

  Lemma local_state_coh_update_heap σ1 n γs h l v1 v2 :
    let σ2 := (σ1 <| state_heaps := <[n:=<[l:=v2]> h]> (state_heaps σ1) |>) in
    state_heaps σ1 !! n = Some h →
    local_state_coh σ1 n γs ∗ l ↦[n] v1 ==∗ local_state_coh σ2 n γs ∗ l ↦[n] v2.
  Proof.
    simpl. iIntros (?) "[Hstate Hl]".
    iDestruct "Hstate" as (h' S Hh Hs) "(#Hn & Hheap & ?)".
    iDestruct "Hl" as (γs') "[Hn' Hl]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    simplify_eq.
    iMod (gen_heap_light_update with "Hheap Hl") as "[Hheap' Hl]".
    iModIntro. iFrame.
    iSplitR "Hl"; [| iExists _; eauto].
    iExists _, _. iFrame.
    rewrite lookup_insert /set /=; eauto.
  Qed.

  Lemma local_state_coh_valid_sockets σ ip γs sh q skt R T :
    local_state_coh σ ip γs -∗
    sh ↪[ip]{q} (skt, R, T) -∗
    ∃ Sn, ⌜state_sockets σ !! ip = Some Sn ∧ Sn !! sh = Some (skt, R, T)⌝.
  Proof.
    iDestruct 1 as (h' S Hh Hs) "(Hn & ? & Hsock)".
    iDestruct 1 as (γs') "[Hn' Hsh]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    iDestruct (gen_heap_light_valid with "Hsock Hsh") as "%".
    iExists _. iPureIntro; eauto.
  Qed.

  Lemma local_state_coh_alloc_socket σ ip γs sh Sn sock:
    let σ' := σ <| state_sockets := <[ip:=<[sh:=sock]> Sn]> (state_sockets σ) |> in
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    is_node ip -∗
    local_state_coh σ ip γs ==∗ local_state_coh σ' ip γs ∗ sh ↪[ip] sock.
  Proof.
    simpl. iIntros (??) "Hn Hstate". iDestruct "Hn" as (?) "#Hn".
    iDestruct "Hstate" as (h' S Hh Hs) "(Hn' & ? & Hsock)".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    simplify_eq.
    iMod (gen_heap_light_alloc _ _ _ sock with "Hsock") as "[Hsock Hsh]"; [done|].
    iModIntro. iFrame.
    iSplitR "Hsh"; [| iExists _; eauto].
    iExists _, _. iFrame.
    rewrite lookup_insert //.
  Qed.

  Lemma local_state_coh_socketbind σ1 γs sh skt a Sn ps :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt<| saddress := Some a |>, ∅, ∅)]> Sn]> (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    state_ports_in_use σ1 !! ip = Some ps →
    saddress skt = None →
    local_state_coh σ1 ip γs ∗ sh ↪[ip] (skt, ∅, ∅) ==∗
    local_state_coh σ2 ip γs ∗ sh ↪[ip] (skt<| saddress := Some a |>, ∅, ∅).
  Proof.
    simpl. iIntros (????) "[Hlcoh Hsh]".
    iDestruct "Hlcoh" as (h' S Hh Hs) "(#Hn & ? & Hsock)".
    iDestruct "Hsh" as (γs') "[Hn' Hsh]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %<-.
    simplify_eq.
    iMod (gen_heap_light_update _ _ _ _ (skt<| saddress := Some a |>, ∅, ∅)
            with "Hsock Hsh") as "[Hsock' Hsh]".
    iModIntro. iFrame.
    iSplitR "Hsh"; [| iExists _; eauto].
    iExists _, _. iFrame.
    rewrite lookup_insert /set /=; eauto.
  Qed.

  Lemma local_state_coh_update_ms a sh skt σ1 γs Sn R T R' T' M' :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt, R', T')]> Sn]> (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ms := M' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    local_state_coh σ1 ip γs ∗ sh ↪[ip] (skt, R, T) ==∗
    local_state_coh σ2 ip γs ∗ sh ↪[ip] (skt, R', T').
  Proof.
    iIntros (?????) "[Hstate Hsh]".
    iDestruct "Hstate" as (h' S Hh Hs) "(#Hn & ? & Hsock)".
    iDestruct "Hsh" as (γs') "[Hn' Hsh]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    simplify_eq.
    iMod (gen_heap_light_update _ _ _ _ (skt, R', T')
            with "Hsock Hsh") as "[Hsock' Hsh]".
    iModIntro. iFrame. iSplitR "Hsh".
    { iExists _, _. iFrame. rewrite lookup_insert //. }
    iExists _; eauto.
  Qed.

  (** big_sepM_local_state_coh *)
  Lemma big_sepM_local_state_coh_insert n γs γm σ :
    γm !! n = Some γs →
    local_state_coh σ n γs -∗
    ([∗ map] n' ↦ x ∈ delete n γm, local_state_coh σ n' x) -∗
    [∗ map] n' ↦ x ∈ γm, local_state_coh σ n' x.
  Proof.
    iIntros (Hlookup%insert_id) "Hl Hmap".
    iDestruct (big_sepM_insert with "[$]") as "HP".
    { apply lookup_delete. }
    rewrite insert_delete Hlookup //.
  Qed.

  Lemma big_sepM_local_state_coh_delete n γs γm σ :
    γm !! n = Some γs →
    ([∗ map] n' ↦ x ∈ γm, local_state_coh σ n' x) -∗
    local_state_coh σ n γs ∗
    [∗ map] n' ↦ x ∈ delete n γm, local_state_coh σ n' x.
  Proof. iIntros (?) "?"; rewrite -big_sepM_delete //. Qed.

  Lemma big_sepM_local_state_coh_alloc_node n γm σ :
    γm !! n = None →
    ([∗ map] n' ↦ x ∈ γm, local_state_coh σ n' x) -∗
    [∗ map] n' ↦ x ∈ γm,
    local_state_coh (σ <| state_heaps   := <[n:=∅]> (state_heaps σ)|>
                       <| state_sockets := <[n:=∅]> (state_sockets σ) |>) n' x.
  Proof.
    intros ?.
    rewrite big_sepM_mono; [done|].
    intros n' x Hdel.
    destruct (decide (n = n')); simplify_eq.
    rewrite /local_state_coh !lookup_insert_ne //.
  Qed.

  Lemma big_sepM_local_state_coh_update_heap_notin n γm σ1 h :
    let σ2 := (σ1 <| state_heaps := <[n:=h]>(state_heaps σ1) |>) in
    γm !! n = None →
    ([∗ map] n' ↦ x ∈ γm, local_state_coh σ1 n' x) -∗
    [∗ map] n' ↦ x ∈ γm, local_state_coh σ2 n' x.
  Proof.
    simpl. intros ?.
    rewrite big_sepM_mono; [done|].
    intros n' x Hdel.
    destruct (decide (n = n')); simplify_eq.
    rewrite /local_state_coh lookup_insert_ne //.
  Qed.

  Lemma big_sepM_local_state_coh_update_socket_notin n γm Sn σ1 :
    let σ2 := (σ1 <| state_sockets := <[n:=Sn]>(state_sockets σ1) |>) in
    γm !! n = None →
    ([∗ map] n' ↦ x ∈ γm, local_state_coh σ1 n' x) -∗
    [∗ map] n' ↦ x ∈ γm, local_state_coh σ2 n' x.
  Proof.
    simpl. intros ?.
    rewrite big_sepM_mono; [done|].
    intros n' x Hdel.
    destruct (decide (n = n')); simplify_eq.
    rewrite /local_state_coh lookup_insert_ne //.
  Qed.

  (** gnames_coh *)
  Lemma gnames_coh_singleton ip γs h Sn :
    gnames_coh {[ip:=γs]} {[ip:=h]} {[ip:=Sn]}.
  Proof. rewrite /gnames_coh !dom_singleton_L //. Qed.

  Lemma gnames_coh_valid γm H S ip :
    H !! ip = None →
    gnames_coh γm H S →
    γm !! ip = None.
  Proof. rewrite -!not_elem_of_dom => _ [-> _] //. Qed.

  Lemma gnames_coh_alloc_node γm H S ip γn :
    gnames_coh γm H S →
    gnames_coh (<[ip:=γn]> γm) (<[ip:=∅]> H) (<[ip:=∅]> S).
  Proof. rewrite /gnames_coh !dom_insert_L. move=> [-> ->] //=. Qed.

  Lemma gnames_coh_update_heap n γm H S h h' :
    H !! n = Some h →
    gnames_coh γm H S →
    gnames_coh γm (<[n:=h']> H) S.
  Proof.
    intros ?%elem_of_dom_2 [? ?].
    rewrite /gnames_coh dom_insert_L subseteq_union_1_L //=.
    set_solver.
  Qed.

  Lemma gnames_coh_update_sockets n γm H S Sn Sn' :
    S !! n = Some Sn →
    gnames_coh γm H S →
    gnames_coh γm H (<[n:=Sn']> S).
  Proof.
    intros ?%elem_of_dom_2 [? ?].
    rewrite /gnames_coh dom_insert_L subseteq_union_1_L //=.
    set_solver.
  Qed.

  (** free_ips_coh *)
  Lemma free_ips_coh_init ip ips σ :
    ip ∉ ips →
    dom (gset ip_address) (state_ports_in_use σ) = ips →
    (∀ ip, ip ∈ ips → state_ports_in_use σ !! ip = Some ∅) →
    state_heaps σ = {[ip:=∅]} →
    state_sockets σ = {[ip:=∅]} →
    state_ms σ = ∅ →
    free_ips_auth ips ∗ free_ports_auth ∅ -∗ free_ips_coh σ.
  Proof.
    iIntros (??? Hste Hsce ?) "[HipsCtx HPiu]".
    iExists _, _; iFrame.
    rewrite Hste Hsce.
    iPureIntro.
    do 2 (split; [set_solver|]).
    split; [|set_solver].
    intros ip' ?.
    assert (ip ≠ ip') by set_solver.
    rewrite !lookup_insert_ne //.
  Qed.

  Lemma free_ips_coh_free_ports_valid σ a :
    free_ips_coh σ -∗
    free_ports (ip_of_address a) {[port_of_address a]} -∗
    ∃ ps, ⌜state_ports_in_use σ !! ip_of_address a = Some ps ∧
           port_of_address a ∉ ps⌝.
  Proof.
    iDestruct 1 as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iIntros "Hp".
    iDestruct (free_ports_included with "HpCtx Hp") as (?) "[%Hlookup %]".
    destruct (HPiu _ _ Hlookup) as (?&?&?).
    iExists _. iPureIntro. split; [done|set_solver].
  Qed.

  Lemma free_ips_coh_alloc_node σ ip ports :
    free_ips_coh σ -∗
    free_ip ip ==∗
    free_ips_coh (σ <| state_heaps   := <[ip:=∅]> (state_heaps σ)|>
                    <| state_sockets := <[ip:=∅]> (state_sockets σ) |>) ∗
    free_ports ip ports.
  Proof.
    iDestruct 1 as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iIntros "Hfip".
    iDestruct (free_ip_included with "HfCtx Hfip") as %Hin.
    iMod (free_ip_dealloc with "HfCtx Hfip") as "HfCtx".
    iMod (free_ports_alloc _ ip ports with "HpCtx") as "[HpCtx Hports]";
      [set_solver|].
    iModIntro. iFrame. iExists _, _. simpl. iFrame. iPureIntro.
    split; [set_solver|]. split; [set_solver|]. split.
    { intros. rewrite !lookup_insert_ne //; set_solver. }
    intros ip' ??.
    destruct (decide (ip = ip')); simplify_map_eq; [|eauto].
    eexists; split; eauto. set_solver.
  Qed.

  Lemma free_ips_coh_update_heap σ ip h h' :
    state_heaps σ !! ip = Some h →
    free_ips_coh σ -∗
    free_ips_coh (σ <| state_heaps := <[ip:=h']> (state_heaps σ) |>).
  Proof.
    iIntros (?).
    iDestruct 1 as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iExists _, _. simpl. iFrame. iPureIntro.
    do 3 (split; auto).
    intros ip' ?.
    split; [|set_solver].
    destruct (decide (ip = ip')); simplify_map_eq; [set_solver|].
    by apply HFip2.
  Qed.

  Lemma free_ips_coh_alloc_socket σ ip Sn sh sock :
    let σ' := σ <| state_sockets := <[ip:=<[sh:=sock]> Sn]> (state_sockets σ) |> in
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    free_ips_coh σ -∗ free_ips_coh σ'.
  Proof.
    iIntros (???).
    iDestruct 1 as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iExists _, _. simpl. iFrame. iPureIntro.
    do 3 (split; auto).
    intros ip' ?.
    split; [by eapply HFip2|].
    destruct (decide (ip = ip')); simplify_map_eq; [set_solver|].
    by apply HFip2.
  Qed.

  Lemma free_ips_coh_dealloc σ1 a sh skt Sn ps :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt<| saddress := Some a |>, ∅, ∅)]> Sn]> (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    state_ports_in_use σ1 !! ip = Some ps →
    free_ips_coh σ1 -∗
    free_ports (ip_of_address a) {[port_of_address a]} ==∗
    free_ips_coh σ2.
  Proof.
    rewrite /free_ips_coh /=.
    iDestruct 1 as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iIntros "Hp".
    iMod (free_ports_dealloc with "HpCtx Hp")
               as (ps' [Hps' Hin%elem_of_subseteq_singleton]) "HpCtx".
    iModIntro. iExists _, _; iFrame. iPureIntro.
    split; [set_solver|].
    split.
    { intros ip ?.
      destruct (decide (ip = ip_of_address a)); simplify_eq; [set_solver|].
      rewrite lookup_insert_ne //. by apply HFip. }
    split.
    { intros ip ?. split; [set_solver|].
      destruct (decide (ip = ip_of_address a)); simplify_eq; [set_solver|].
      rewrite lookup_insert_ne //. by apply HFip2. }
    intros ip ??.
    destruct (decide (ip = ip_of_address a)); simplify_map_eq.
    - destruct (HPiu _ _ Hps') as [Q [Ha HQ]]. simplify_map_eq.
      eexists. split; [done|]. set_solver.
    - rewrite lookup_insert_ne //. set_solver.
  Qed.

  Lemma free_ips_coh_update_msg sh a skt Sn R T R' T' M' σ1 :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt, R', T')]> Sn]> (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ms := M' |> in
    state_sockets σ1 !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    free_ips_coh σ1 -∗ free_ips_coh σ2.
  Proof.
    rewrite /free_ips_coh /=.
    iDestruct 1 as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iExists _, _. simpl. iFrame. iPureIntro.
    do 2 (split; [auto|]).
    split; [|done].
    intros ip ?. split; [set_solver|].
    destruct (decide (ip = ip_of_address a)); simplify_map_eq; [set_solver|].
    by apply HFip2.
  Qed.

  (** message_received *)
  Lemma message_received_alloc_socket S m Sn ip sh s:
    S !! ip = Some Sn →
    Sn !! sh = None →
    message_received S m →
    message_received (<[ip:=<[sh:=(s, ∅, ∅)]> Sn]> S) m.
  Proof.
    rewrite /message_received.
    intros HSn HhNone (Sn' & sh' & s' & a & R & T & HS' & HSn' & Ha & Hm).
    destruct (decide (ip = ip_of_address a)); simplify_map_eq.
    - eexists  (<[sh:=(s, ∅, ∅)]> Sn), _, _, a, _, _.
      rewrite lookup_insert. repeat split; try done.
      rewrite lookup_insert_ne //.
    - do 6 eexists. rewrite lookup_insert_ne //.
  Qed.

  Lemma message_received_socketbind S m Sn sh skt a:
    let ip := ip_of_address a in
    let S' := (<[ip:=<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn]> S) in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    message_received S m →
    message_received S' m.
  Proof.
    rewrite /message_received.
    intros HSn HhSome (? & sh' &?& a' &?&?&HS&?&?&?).
    destruct (decide (ip_of_address a = ip_of_address a')) as [Heq|];
      simplify_map_eq.
    - rewrite -Heq in HS.
      destruct (decide (sh = sh')); simplify_map_eq; [done|].
      eexists (<[sh:=(skt<| saddress := Some a |>, ∅, ∅)]> Sn), _, _, a',  _, _.
      rewrite Heq lookup_insert lookup_insert_ne //.
    - do 6 eexists. rewrite lookup_insert_ne //.
  Qed.

  Lemma message_received_receive a skt sh S Sn R T m :
    let S' := (<[ip_of_address a:=<[sh:=(skt, {[m]} ∪ R, T)]> Sn]> S) in
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    message_received S' m.
  Proof.
    intros ????. rewrite /message_received /S'.
    exists (<[sh:=(skt, {[m]} ∪ R, T)]> Sn), sh, skt, a, ({[m]} ∪ R), T.
    rewrite !lookup_insert //. repeat split; eauto. set_solver.
  Qed.

  Lemma message_received_insert a skt sh S Sn R T m m' :
    let S' := (<[ip_of_address a:=<[sh:=(skt, {[m']} ∪ R, T)]> Sn]> S) in
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    message_received S m →
    message_received S' m.
  Proof.
    intros S' HS HSn ? Hr.
    destruct (decide (m = m')); simplify_eq.
    { by apply message_received_receive. }
    destruct Hr as (Sn' & sh' & skt' & a' & R' & T' & HS' & HSn' & Ha' & Hm).
    rewrite /S' /message_received.
    destruct (decide (ip_of_address a = ip_of_address a')) as [Heq | ?].
    - exists (<[sh:=(skt, {[m']} ∪ R, T)]> Sn).
      rewrite -Heq in HS'.
      assert (Sn = Sn') as <- by set_solver.
      destruct (decide (sh' = sh)); simplify_eq.
      + exists sh, skt, a, ({[m']} ∪ R), T.
        rewrite !lookup_insert. repeat split; eauto with set_solver.
      + exists sh', skt', a', R', T'.
        rewrite Heq ?lookup_insert ?lookup_insert_ne //.
    - do 6 eexists. rewrite lookup_insert_ne //.
   Qed.

  (** network_messages_coh *)
  Lemma network_messages_coh_alloc_node Sn M ip :
    Sn !! ip = None →
    network_messages_coh Sn M -∗
    network_messages_coh (<[ip:=∅]> Sn) M.
  Proof.
    iIntros (Hnone) "H".
    iApply big_sepS_mono; last done.
    iIntros (??) "[? | %Hr]"; first by iLeft.
    destruct Hr as (a & h & Sn' & s & R & T &?&?&?&?).
    iRight. iPureIntro. exists a, h, Sn', s, R, T.
    simplify_map_eq. set_solver.
  Qed.

  Lemma network_messages_coh_alloc_socket S Sn M n h sh :
    S !! n = Some Sn →
    Sn !! h = None →
    network_messages_coh S M -∗
    network_messages_coh (<[n:=<[h:=(sh, ∅, ∅)]>Sn]> S) M.
  Proof.
    iIntros (??) "Hsent". rewrite /network_messages_coh.
    rewrite big_sepS_mono; first done.
    iIntros (??) "[Htt | %]"; [by iLeft|].
    iRight. iPureIntro. by apply message_received_alloc_socket.
  Qed.

  Lemma network_messages_coh_socketbind S M Sn sh skt a :
    let ip := ip_of_address a in
    let S' := (<[ip:=<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn]> S) in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    saddress skt = None →
    network_messages_coh S M -∗
    network_messages_coh S' M.
  Proof.
    rewrite /network_messages_coh /=.
    iIntros (???) "Hsent".
    rewrite big_sepS_mono; first done.
    iIntros (??) "[? | %]"; [by iLeft|].
    iRight. iPureIntro. by apply message_received_socketbind.
  Qed.

  Lemma network_messages_coh_insert_sent S M Sn sh skt a to m R T φ P :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) m in
    let S' := <[ip := <[sh:=(skt, R, {[msg]} ∪ T)]> Sn]> S in
    let M' := {[msg]} ∪ M in
    saddress skt = Some a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    network_sockets_coh S M P →
    to ⤇ φ -∗
    φ msg -∗
    network_messages_coh S M -∗ network_messages_coh S' M'.
  Proof.
    iIntros (ip msg ?? Hsa Hh Hsi HnetCoh) "Hsi Hmsg Hsent".
    rewrite /network_messages_coh /S'.
    destruct (decide (msg ∈ M)).
    - assert (M = M') as <- by set_solver.
      iApply (big_sepS_mono with "Hsent").
      iIntros (msg' Hmsg') "[Htt | Hrd]"; first by iLeft.
      iDestruct "Hrd" as %Hrd. iRight; iPureIntro.
      rewrite /message_received.
      destruct Hrd as (Sa'&sh'&skt'&a'&R'&T'&Hsi'&Hs'&Hsa'&HinR').
      destruct (decide (ip = ip_of_address a')) as [Heq | Heq]; simplify_map_eq.
      + eexists (<[sh:=(skt, R, {[msg]} ∪ T)]> Sn),sh',skt',a'.
        destruct Heq.
        destruct (decide (sh = sh')); do 2 eexists;
          simplify_map_eq; [done|].
        rewrite lookup_insert_ne //.
      + do 6 eexists. rewrite lookup_insert_ne //.
    - rewrite (big_sepS_union _ _ M ) // /=; last by set_solver.
      iSplitL "Hmsg Hsi". rewrite big_sepS_singleton. iLeft. eauto.
      iApply (big_sepS_mono with "Hsent").
      iIntros (msg' Hmsg') "[Htt | Hrd]"; first by iLeft.
      iDestruct "Hrd" as %Hrd. iRight; iPureIntro.
      rewrite /message_received.
      destruct Hrd as (Sa'&sh'&skt'&a'&R'&T'&Hsi'&Hs'&Hsa'&HinR').
      destruct (decide (ip = ip_of_address a')) as [Heq | Heq]; simplify_map_eq.
      + eexists (<[sh:=(skt, R, {[msg]} ∪ T)]> Sn),sh',skt',a'.
        destruct Heq. rewrite lookup_insert.
        destruct (decide (sh = sh')); do 2 eexists;
          simplify_map_eq; [done|].
        rewrite lookup_insert_ne //.
      + do 6 eexists. rewrite lookup_insert_ne //.
  Qed.

  (** bound_ports_coh *)
  Lemma bound_ports_coh_alloc_socket Sn P sh skt :
    Sn !! sh = None →
    saddress skt = None →
    bound_ports_coh Sn P →
    bound_ports_coh (<[sh:=(skt, ∅, ∅)]> Sn) P.
  Proof.
    intros ??? sh' ?????.
    destruct (decide (sh = sh')) as [Heq|];
      simplify_map_eq; [set_solver|].
    rewrite lookup_insert_ne //. eauto.
  Qed.

  Lemma bound_ports_coh_socketbind P Sn ps sh skt a :
    let Sn' := (<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn) in
    let P' := (<[ip_of_address a:={[port_of_address a]} ∪ ps]> P) in
    P !! ip_of_address a = Some ps →
    bound_ports_coh Sn P →
    bound_ports_coh Sn' P'.
  Proof.
    rewrite /bound_ports_coh /=.
    intros HP HbpsCoh sh' skt' a' P' R' T' Hsh' Hskt' HP'.
    destruct (decide (sh' = sh)); simplify_map_eq.
    - rewrite lookup_insert in Hsh'; simplify_map_eq.
      rewrite lookup_insert in HP'; by set_solver.
    - rewrite lookup_insert_ne // in Hsh'.
      destruct (decide ((ip_of_address a') = (ip_of_address a)))
        as [Heq|]; simplify_map_eq.
      + destruct Heq.
        rewrite lookup_insert in HP'. simplify_eq /=.
        destruct (decide (port_of_address a' = port_of_address a));
          [set_solver|].
        apply elem_of_union_r. by eapply HbpsCoh.
      + rewrite lookup_insert_ne in HP'; [|done].
        by eapply HbpsCoh.
  Qed.

  Lemma bound_ports_coh_insert_received a skt sh Sn P R T m :
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    bound_ports_coh Sn P →
    bound_ports_coh (<[sh:=(skt, {[m]} ∪ R, T)]> Sn) P.
  Proof.
    intros ??? sh' skt' ????.
    destruct (decide (sh = sh')); simplify_map_eq.
    - intros; simplify_eq; eauto.
    - rewrite lookup_insert_ne //; eauto.
  Qed.

  (** socket_handlers_coh *)
  Lemma socket_handlers_coh_alloc_socket Sn sh s :
    saddress s = None →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(s, ∅, ∅)]> Sn).
  Proof.
    intros ?? sh1 sh2 * ??? H. symmetry in H.
    ddeq sh1 sh2; ddeq sh1 sh; ddeq sh2 sh; eauto.
  Qed.

  Lemma socket_handlers_coh_socketbind Sn sh skt a :
    (∀ sh' skt' R' T' a',
        Sn !! sh' = Some (skt', R', T') →
        saddress skt' = Some a' →
        port_of_address a' ≠ port_of_address a) →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn).
  Proof.
    intros ? Hscoh sh1 sh2 skt1 skt2 ??????? Heq.
    ddeq sh1 sh; ddeq sh2 sh; simplify_eq=>//.
    - destruct skt, skt2; simplify_map_eq. set_solver.
    - destruct skt, skt1. simplify_map_eq. set_solver.
    - destruct skt1, skt2. simplify_map_eq. eapply Hscoh; eauto.
  Qed.

  Lemma socket_handlers_coh_insert_received Sn sh skt m R T :
    Sn !! sh = Some (skt, R, T) →
    socket_handlers_coh Sn →
    socket_handlers_coh (<[sh:=(skt, {[m]} ∪ R, T)]> Sn).
  Proof.
    intros ?? sh1 sh2 * ??? H. symmetry in H.
    ddeq sh1 sh2; ddeq sh1 sh; ddeq sh2 sh; eauto.
  Qed.

  (** socket_messages_coh *)
  Lemma socket_messages_coh_update_socket Sn M sh skt :
    socket_messages_coh Sn M  →
    socket_messages_coh (<[sh:=(skt, ∅, ∅)]> Sn) M.
  Proof. intros ? sh' **. ddeq sh sh'; [set_solver|]. eauto. Qed.

  Lemma socket_messages_coh_insert_received a sh skt m R T Sn M :
    Sn !! sh = Some (skt, R, T) →
    m_destination m = a →
    saddress skt = Some a →
    m ∈ M →
    socket_messages_coh Sn M →
    socket_messages_coh (<[sh:=(skt, {[m]} ∪ R, T)]> Sn) M.
  Proof.
    intros ???? Hmcoh sh' skt' R' T' a' Hsh' ?.
    destruct (decide (sh = sh')); simplify_eq; last first.
    { rewrite lookup_insert_ne // in Hsh'. by eapply Hmcoh. }
    rewrite lookup_insert in Hsh'; simplify_eq.
    split; [|by eapply Hmcoh].
    intros m' [?%elem_of_singleton_1 | HR]%elem_of_union; subst; [done|].
    by eapply Hmcoh.
  Qed.

  (** socket_addresses_coh *)
  Lemma socket_addresses_coh_alloc_socket Sn sh skt n :
    saddress skt = None →
    socket_addresses_coh Sn n →
    socket_addresses_coh (<[sh:=(skt, ∅, ∅)]> Sn) n.
  Proof. intros ? ? sh' **. ddeq sh' sh; eauto. Qed.

  Lemma socket_addresses_coh_socketbind Sn sh skt a :
    saddress skt = None →
    socket_addresses_coh Sn (ip_of_address a) →
    socket_addresses_coh (<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn) (ip_of_address a).
  Proof. intros ? ? sh' **; ddeq sh sh'; eauto. Qed.

  Lemma socket_addresses_coh_insert_received sh a skt m R T Sn :
    saddress skt = Some a →
    socket_addresses_coh Sn (ip_of_address a) →
    socket_addresses_coh (<[sh:=(skt, {[m]} ∪ R, T)]> Sn) (ip_of_address a).
  Proof. intros ?? sh' **; ddeq sh sh'; eauto. Qed.

  (** network_sockets_coh *)
  Lemma network_sockets_coh_alloc_node Sn M ps ip :
    Sn !! ip = None →
    network_sockets_coh Sn M ps →
    network_sockets_coh (<[ip:=∅]> Sn) M ps.
  Proof.
    rewrite /network_sockets_coh.
    intros ? Hcoh ip' ? Hst.
    destruct (decide (ip' = ip)); simplify_eq.
    - apply lookup_insert_rev in Hst. subst. split; done.
    - eapply Hcoh; by rewrite lookup_insert_ne in Hst.
  Qed.

  Lemma network_sockets_coh_alloc_socket S Sn M P n sh skt :
    S !! n = Some Sn →
    Sn !! sh = None →
    saddress skt = None →
    network_sockets_coh S M P →
    network_sockets_coh (<[n:=<[sh:=(skt, ∅, ∅)]> Sn]> S) M P.
  Proof.
    rewrite /network_sockets_coh.
    intros ??? Hnets n' Sn' HSn. ddeq n' n; [|eauto].
    destruct (Hnets n Sn) as (?&?&?&?); [done|].
    split; [by apply bound_ports_coh_alloc_socket|].
    split; [by apply socket_handlers_coh_alloc_socket|].
    split; [by apply socket_messages_coh_update_socket|].
    by apply socket_addresses_coh_alloc_socket.
  Qed.

  Lemma network_sockets_coh_socketbind S P M Sn ps sh skt a :
    let ip := ip_of_address a in
    let S' := <[ip:= <[sh:= (skt <| saddress := Some a |>, ∅, ∅)]> Sn]> S in
    let P' := (<[ip:={[port_of_address a]} ∪ ps]> P) in
    S !! ip = Some Sn →
    P !! ip = Some ps →
    Sn !! sh = Some (skt, ∅, ∅) →
    port_of_address a ∉ ps →
    saddress skt = None →
    network_sockets_coh S M P  →
    network_sockets_coh S' M P'.
  Proof.
    rewrite /network_sockets_coh /=.
    intros ????? Hncoh ip Sn' ?.
    assert
      (∀ sh' skt' R' T' a',
          Sn !! sh' = Some (skt', R', T') →
          saddress skt' = Some a' →
          port_of_address a' ≠ port_of_address a ).
    { destruct (Hncoh (ip_of_address a) Sn) as (HBpCoh & HshCoh & HmrCoh & HsaCoh);
        [done|].
      intros ** Hp.
      assert (ip_of_address a' = ip_of_address a) as Heq.
      { eapply HsaCoh; eauto. }
      assert (port_of_address a' ∈ ps) as Hin.
      { eapply HBpCoh; eauto. rewrite Heq //. }
      rewrite Hp in Hin. set_solver. }
    ddeq ip (ip_of_address a).
    - destruct (Hncoh (ip_of_address a) Sn) as (?&?&?&?); [done|].
      split; [by eapply bound_ports_coh_socketbind|].
      split; [by eapply socket_handlers_coh_socketbind|].
      split; [by eapply socket_messages_coh_update_socket|].
      by eapply socket_addresses_coh_socketbind.
    - destruct (Hncoh ip Sn') as (HBpCoh & HshCoh & HmrCoh & HsaCoh); [done|].
      split; [|done].
      intros ? skt' a' ????? Hps.
      assert (ip_of_address a' = ip).
      { eapply HsaCoh; eauto. }
      simplify_eq /=. rewrite lookup_insert_ne in Hps; [|done].
      by eapply HBpCoh.
  Qed.

  Lemma network_sockets_coh_insert_sent S P M Sn sh skt a to m R T :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) m in
    saddress skt = Some a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    network_sockets_coh S M P →
    network_sockets_coh (<[ip:=<[sh:=(skt, R, {[msg]} ∪ T)]> Sn]> S) ({[msg]} ∪ M) P.
  Proof.
    intros ip msg Hsa Hsi Hh HnetCoh ip' Sn' Hip'.
    ddeq ip' ip.
    - destruct (HnetCoh ip Sn Hsi) as (HBpCoh & HshCoh & HsmCoh & HsaCoh).
      split.
      { intros sh' skt' **. ddeq sh' sh; eauto using HBpCoh. }
      split.
      { intros sh1 sh2 skt1 skt2 ???? Hsh1 Hsh2 Hskt1 Hsaddr.
        ddeq sh1 sh; ddeq sh2 sh; simplify_eq /=;
          eapply HshCoh; eauto; eapply mk_is_Some; rewrite Hsaddr //. }
      split.
      { intros sh' **; ddeq sh' sh; split; intros;
          edestruct HsmCoh; set_solver. }
      intros sh' **; ddeq sh' sh; eauto.
    - destruct (HnetCoh ip' Sn' Hip') as (HBpCoh & HshCoh & HsmCoh & HsaCoh).
      split; eauto. split; eauto. split; last done.
      intros sh' **. edestruct HsmCoh; eauto.
      split; intros ??; set_solver.
  Qed.

  Lemma network_sockets_coh_not_received a skt sh S Sn P M R T m :
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m_destination m = a →
    m ∈ M →
    m ∉ R →
    network_sockets_coh S M P →
    ¬ message_received S m.
  Proof.
    intros HS HSn Hskt Hd HM HR Hsock Hr.
    destruct Hr as (Sn' & sh' & skt' & a' & R' & T' & HS' & HSn' & Hs' & Hm).
    destruct (decide (a = a')) as [ | Ha]; simplify_eq.
    - assert (sh = sh') as <-.
      { eapply Hsock; eauto. rewrite Hs' //. }
      by simplify_eq.
    - destruct (Hsock (ip_of_address a') Sn')
        as (?&Hhandlers'&Hmsg'&?); [done|].
      destruct (Hmsg' _ _ _ _ a' HSn') as [HR' ?]; [done|].
      by destruct (HR' _ Hm) as [? ?].
  Qed.

  Lemma network_sockets_coh_insert_received a skt sh S Sn P M R T m :
    let S' := (<[ip_of_address a:=<[sh:=(skt, {[m]} ∪ R, T)]> Sn]> S) in
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m_destination m = a →
    m ∈ M →
    m ∉ R →
    network_sockets_coh S M P →
    network_sockets_coh S' M P.
  Proof.
    rewrite /network_sockets_coh.
    intros HS HSn ???? Hnet ip' Sn' HSn'.
    destruct (decide (ip_of_address a = ip'));
      simplify_map_eq; [|by eapply Hnet].
    destruct (Hnet _ _ HS) as (?&?&?&?).
    split; [by eapply bound_ports_coh_insert_received|].
    split; [by eapply socket_handlers_coh_insert_received|].
    split; [by eapply socket_messages_coh_insert_received|].
    by eapply socket_addresses_coh_insert_received.
  Qed.

  Lemma network_sockets_messages_coh_insert_received a skt sh S Sn P M R T m :
    let S' := (<[ip_of_address a:=<[sh:=(skt, {[m]} ∪ R, T)]> Sn]> S) in
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m_destination m = a →
    m ∈ M →
    m ∉ R →
    network_sockets_coh S M P →
    network_messages_coh S M -∗
    network_messages_coh S' M ∗
      ∃ φ : socket_interp Σ, m_destination m ⤇ φ ∗ ▷ φ m.
  Proof.
    iIntros (S' ???????) "Hmcoh".
    rewrite /network_messages_coh big_sepS_delete //.
    iDestruct "Hmcoh" as "[[Hm | %Hr] Hmsgs]";
      [|exfalso; by eapply network_sockets_coh_not_received].
    iFrame.
    assert (message_received S' m) as Hr.
    { by eapply message_received_receive. }
    rewrite (big_sepS_delete _ M m) //. iFrame "%".
    iApply big_sepS_mono; [|done].
    iIntros (??) "[? | %Hr']"; [eauto|].
    iRight. iPureIntro.
    by eapply message_received_insert.
  Qed.

  (** network_coh **)
  Lemma network_coh_init ip ips P :
    dom (gset ip_address) P = ips →
    (∀ ip, ip ∈ ips → P !! ip = Some ∅) →
    ⊢ network_coh {[ip:=∅]} ∅ P.
  Proof.
    intros ??. rewrite /network_coh /network_messages_coh.
    iSplit; [|done].
    iPureIntro. rewrite /network_sockets_coh.
    intros ?? [<- <-]%lookup_singleton_Some.
    rewrite /bound_ports_coh /socket_handlers_coh
            /socket_messages_coh /socket_addresses_coh.
    set_solver.
  Qed.

  Lemma network_coh_sent_valid m sh a skt S Sn M P R T :
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m ∈ T →
    network_coh S M P -∗ ⌜m ∈ M⌝.
  Proof.
    iIntros (Hs HSn Ha Hm) "(%Hscoh & _)". iPureIntro.
    destruct (Hscoh _ Sn Hs) as (?&?& Hmsgs &?).
    edestruct (Hmsgs sh) as [? HT]; [done..|].
    by apply HT.
  Qed.

  Lemma network_coh_received_valid m sh a skt S Sn M P R T :
    S !! ip_of_address a = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    saddress skt = Some a →
    m ∈ R →
    network_coh S M P -∗ ⌜m ∈ M⌝.
  Proof.
    iIntros (Hs HSn Ha Hm) "(%Hscoh & _)". iPureIntro.
    destruct (Hscoh _ Sn Hs) as (?&?& Hmsgs &?).
    edestruct (Hmsgs sh) as [HR ?]; [done..|].
    by apply HR.
  Qed.

  Lemma network_coh_alloc_node Sn M ps ip :
    Sn !! ip = None →
    network_coh Sn M ps -∗
    network_coh (<[ip:=∅]>Sn) M ps.
  Proof.
    iIntros (Hnone) "[% Hmsg]".
    rewrite /network_coh.
    iSplitR; last first.
    { by iApply network_messages_coh_alloc_node. }
    iPureIntro.
    by apply network_sockets_coh_alloc_node.
  Qed.

  Lemma network_coh_alloc_socket S M P Sn n sh skt :
    S !! n = Some Sn →
    Sn !! sh = None →
    saddress skt = None →
    network_coh S M P -∗
    network_coh (<[n:=<[sh:=(skt, ∅, ∅)]> Sn]> S) M P.
  Proof.
    iIntros (? ? ?) "(% & Hmsg)". iSplitR.
    - iPureIntro. by apply network_sockets_coh_alloc_socket.
    - by iApply network_messages_coh_alloc_socket.
  Qed.

  Lemma network_coh_socketbind S P M Sn ps sh skt a :
    let ip := ip_of_address a in
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    P !! ip = Some ps →
    saddress skt = None →
    port_of_address a ∉ ps →
    network_coh S M P -∗
    network_coh
    (<[ip:=<[sh:=(skt <| saddress := Some a |>, ∅, ∅)]> Sn]> S) M
    (<[ip:= {[port_of_address a]} ∪ ps]> P).
  Proof.
    iIntros (??????) "(% & Hmsg)". iSplit.
    - iPureIntro; by apply network_sockets_coh_socketbind.
    - by iDestruct (network_messages_coh_socketbind with "Hmsg") as "Hmsg".
  Qed.

  Lemma network_coh_insert_sent S P M Sn sh skt a to m (φ : socket_interp Σ) R T :
    let ip := ip_of_address a in
    let msg := mkMessage a to (sprotocol skt) m in
    let S' := <[ip := <[sh:=(skt, R, {[msg]} ∪ T)]> Sn]> S in
    let M' := {[msg]} ∪ M in
    saddress skt = Some a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    to ⤇ φ -∗
    φ msg -∗
    network_coh S M P -∗ network_coh S' M' P.
  Proof.
    iIntros (???????) "Hpred Hr [% Hmsg]". iSplit.
    - iPureIntro. by apply network_sockets_coh_insert_sent.
    - by iApply (network_messages_coh_insert_sent with "Hpred Hr Hmsg").
  Qed.

  Lemma network_coh_receive a sh skt S Sn M P R T m :
    let ip := ip_of_address a in
    let S' := (<[ip:=<[sh:=(skt, {[m]} ∪ R, T)]> Sn]> S) in
    saddress skt = Some a →
    S !! ip = Some Sn →
    Sn !! sh = Some (skt, R, T) →
    m_destination m = a →
    m ∈ M →
    m ∉ R →
    network_coh S M P -∗ network_coh S' M P ∗ ∃ φ, m_destination m ⤇ φ ∗ ▷ φ m.
  Proof.
    simpl. iIntros (??????) "[%Hsock Hmcoh]".
    rewrite /network_coh.
    iDestruct (network_sockets_messages_coh_insert_received with "Hmcoh")
      as "[Hmcoh Hφ]"; [done..|].
    iFrame. iPureIntro.
    by apply network_sockets_coh_insert_received.
   Qed.

  (** socket_interp_coh *)
  Lemma socket_interp_coh_init ips A M σ f :
    dom (gset _) M = A →
    dom (gset _) (state_ports_in_use σ) = ips →
    (∀ ip, ip ∈ ips → state_ports_in_use σ !! ip = Some ∅) →
    (∀ a, a ∈ A → ip_of_address a ∈ ips) →
    ([∗ set] a ∈ A, a ⤇ f a)%I -∗
    fixed A -∗
    saved_si_auth M -∗
    socket_interp_coh (state_ports_in_use σ).
  Proof.
    iIntros (Hdmsi Hipdom Hpiiu Hfixdom) "? ? ?".
    rewrite /socket_interp_coh. iExists _; iFrame.
    iExists _; iFrame; iFrame "#".
    rewrite -!Hdmsi.
    iSplit; [iApply (big_sepS_mono with "[$]"); auto|].
    iSplit; [iPureIntro; set_solver|].
    iPureIntro. intros b Hbips. split; auto.
    intros [Hb | [Hb HP]]; [done|].
    simplify_eq.
    specialize (Hpiiu _ Hbips).
    specialize (HP _ Hpiiu). done.
  Qed.

  Lemma socket_interp_coh_fixed_valid a A ips :
    a ∈ A →
    socket_interp_coh ips -∗ fixed A -∗ ∃ φ, a ⤇ φ.
  Proof.
    iIntros (HaA) "Hscoh #HA".
    iDestruct "Hscoh" as (si A') "(HA' & Hsiauth & Hsis & % & H)".
    iDestruct "H" as %Hdom.
    iDestruct (fixed_agree with "HA HA'") as %->.
    iDestruct (big_sepS_elem_of with "Hsis") as "$".
    erewrite Hdom; eauto.
  Qed.

  Lemma socket_interp_coh_socketbind_static ps P a A:
    a ∈ A →
    P !! ip_of_address a = Some ps →
    port_of_address a ∉ ps →
    fixed A -∗
    socket_interp_coh P -∗
    socket_interp_coh (<[ip_of_address a:={[port_of_address a]} ∪ ps]> P).
  Proof.
    iIntros (???) "HA". rewrite /socket_interp_coh.
    iDestruct 1 as (si A') "(HA' & Hsiauth & Hsis & %Hf & %Hdms)".
    iDestruct (fixed_agree with "HA HA'") as %->.
    iExists _,_. iFrame. iPureIntro. split.
    { intros ??. rewrite dom_insert elem_of_union; right. by apply Hf. }
    intros b. rewrite dom_insert elem_of_union. intros Hb.
    rewrite Hdms; last first.
    { destruct (decide (a = b)); subst; first by apply Hf.
      destruct Hb as [->%elem_of_singleton_1|]; [|done]. by apply Hf. }
    split; intros [|[Hnb Hdm]]; auto.
    { right. split; [done|].
      destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
      - intros P'. rewrite Heq lookup_insert. intros; simplify_eq.
        apply elem_of_union_r, Hdm. rewrite -Heq //.
      - intros P'. rewrite lookup_insert_ne //. apply Hdm. }
    destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
    { right. split; [done|]. intros P'.
      rewrite Heq lookup_insert in Hdm.
      specialize (Hdm ({[port_of_address a]} ∪ _) eq_refl).
      apply elem_of_union in Hdm. destruct Hdm as [Hdm%elem_of_singleton_1 | Hdm].
      - destruct a, b; simpl in *. by subst.
      - rewrite -Heq. by intros; simplify_eq. }
    right. split; [done|].
    rewrite lookup_insert_ne in Hdm; done.
  Qed.

  Lemma socket_interp_coh_socketbind_dynamic ps P a A φ :
    a ∉ A →
    P !! ip_of_address a = Some ps →
    port_of_address a ∉ ps →
    fixed A -∗
    socket_interp_coh P ==∗
    socket_interp_coh (<[ip_of_address a:={[port_of_address a]} ∪ ps]> P) ∗
    a ⤇ φ.
  Proof.
    iIntros (? Hpa Hps) "#HA". rewrite /socket_interp_coh.
    iDestruct 1 as (si A') "(HA' & Hsiauth & Hsis & %Hf & %Hdms)".
    iDestruct (fixed_agree with "HA HA'") as %<-.
    assert (si !! a = None).
    { destruct (si !! a) eqn:Heq; last done.
      destruct (Hdms a) as [[|[Hfx HP]] _]; try done.
      - by eapply elem_of_dom_2.
      - rewrite elem_of_dom. eauto.
      - by apply HP in Hpa. }
    iMod (socket_interp_alloc a φ with "Hsiauth")
      as (?) "[Hsiauth #Hφ]"; [done|].
    iFrame "Hφ". iModIntro. iExists _, _; iFrame.
    iSplitL "Hsis".
    { rewrite dom_insert_L big_sepS_insert;
        last rewrite not_elem_of_dom //.
      iFrame. iExists _. iFrame "Hφ". }
    iSplit.
    { iPureIntro. intros b Hb.
      destruct (decide (a = b)); subst; first done.
      apply dom_insert, elem_of_union. by auto. }
    iPureIntro. intros b Hbdom.
    rewrite dom_insert elem_of_union elem_of_singleton Hdms; last first.
    { destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
      - destruct Heq. by eapply elem_of_dom_2.
      - apply dom_insert, elem_of_union in Hbdom. set_solver. }
    split.
    - intros [Hb | Hdom]; subst.
      + right. split; [done|]. rewrite lookup_insert.
        intros; simplify_eq. by apply elem_of_union_l, elem_of_singleton.
      + destruct Hdom as [? | [Hb HP]]; first by left.
        right. split; first done.
        destruct (decide (ip_of_address a = ip_of_address b)) as [Heq |Hneq].
        * destruct Heq. rewrite lookup_insert. intros; simplify_eq.
          apply elem_of_union_r, HP; eauto.
        * by rewrite lookup_insert_ne.
    - intros [Hb | [Hb Hdom]]; first by auto.
      destruct (decide (a = b)) as [Heq | Hneq]; first by auto.
      right; right. split; first done.
      destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
      + intros ps'.
        rewrite Heq in Hdom.
        rewrite lookup_insert in Hdom.
        specialize (Hdom ({[port_of_address a]} ∪ ps) eq_refl).
        apply elem_of_union in Hdom. destruct Hdom as [Hdom | Hport].
        * apply elem_of_singleton_1 in Hdom.
          destruct a,b; simpl in *; simplify_eq.
        * intros. destruct Heq; simplify_eq; eauto.
      + intros. apply Hdom. rewrite lookup_insert_ne //.
  Qed.

  (** aneris_state_interp *)
  Lemma mapsto_node_heap_valid n γs σ :
    aneris_state_interp σ -∗
    mapsto_node n γs -∗
    ∃ h, ⌜state_heaps σ !! n = Some h⌝.
  Proof.
    iDestruct 1 as (m) "(Hnauth & _ & _ & Hlcoh & _)".
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
    iDestruct 1 as (m) "(Hnauth & _ & _ & Hlcoh & _)".
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

  (* aneris_state_interp *)
  Lemma aneris_state_interp_init ips A σ f M ip γs :
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
    fixed A -∗
    saved_si_auth M -∗
    ([∗ set] a ∈ A, a ⤇ (f a)) -∗
    free_ips_auth ips -∗
    free_ports_auth ∅ -∗
    aneris_state_interp σ.
  Proof.
    iIntros (HMdom Hipdom Hpiiu Hfixdom Hste Hsce Hmse Hip)
            "Hmp #Hn Hh Hs #Hsif HM #Hsa HipsCtx HPiu".
    iExists _; iFrame.
    rewrite !Hste !Hsce !Hmse.
    iSplit.
    { iPureIntro. apply gnames_coh_singleton. }
    iSplitL "HM".
    { by iApply (socket_interp_coh_init with "Hsa Hsif HM"). }
    iSplitL "Hh Hs".
    { rewrite big_sepM_singleton /local_state_coh Hste Hsce !lookup_singleton.
      iExists _, _. by iFrame; iFrame "#". }
    iSplitL "HipsCtx HPiu".
    { by iApply (free_ips_coh_init with "[$]"). }
    by iApply network_coh_init.
  Qed.

  Lemma aneris_state_interp_free_ip_valid σ ip :
    aneris_state_interp σ -∗
    free_ip ip -∗
    ⌜state_heaps σ !! ip = None ∧
     state_sockets σ !! ip = None ∧
     is_Some (state_ports_in_use σ !! ip)⌝.
  Proof.
    iDestruct 1 as (m) "(? & % & ? & ? & Hfreeips & ?)". iIntros "Hfip".
    iDestruct "Hfreeips" as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iDestruct (free_ip_included with "HfCtx Hfip") as %Hin.
    iPureIntro. destruct (HFip2 _ Hin) as [??]. eauto.
  Qed.

  Lemma aneris_state_interp_free_ports_valid σ a :
    aneris_state_interp σ -∗
    free_ports (ip_of_address a) {[port_of_address a]} -∗
    ∃ ps, ⌜state_ports_in_use σ !! ip_of_address a = Some ps ∧
           port_of_address a ∉ ps⌝.
  Proof.
    iDestruct 1 as (m) "(?&%&?&?&?&?)".
    by iApply free_ips_coh_free_ports_valid.
  Qed.

  Lemma aneris_state_interp_alloc_node σ ip ports :
    aneris_state_interp σ ∗ free_ip ip ==∗
    is_node ip ∗ free_ports ip ports ∗
    aneris_state_interp (σ <| state_heaps   := <[ip:=∅]> (state_heaps σ)|>
                           <| state_sockets := <[ip:=∅]> (state_sockets σ) |>).
  Proof.
    iIntros "[Hσ Hfip]".
    iDestruct (aneris_state_interp_free_ip_valid with "Hσ Hfip") as "(% & % & %)".
    iDestruct "Hσ" as (m) "(Hnauth & % & Hsock & Hlcoh & HFip & Hnet)".
    iMod (free_ips_coh_alloc_node with "HFip Hfip") as "[HFip Hports]".
    iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
    assert (m !! ip = None) by eapply gnames_coh_valid=>//.
    iMod (node_gnames_alloc γn with "Hnauth") as "[Hnauth #Hγn]"; [done|].
    set σ' := (σ <| state_heaps   := <[ip:=∅]> (state_heaps σ)|>
                 <| state_sockets := <[ip:=∅]> (state_sockets σ) |>).
    iModIntro. iSplitR.
    { iExists _; eauto. }
    iFrame. iExists _. iFrame. iSplitR.
    { iPureIntro. by eapply gnames_coh_alloc_node. }
    iSplitR "Hnet".
    { iApply (big_sepM_local_state_coh_insert ip γn with "[Hh Hs] [Hlcoh]").
      - rewrite lookup_insert //.
      - iExists _, _. iFrame. iFrame "#". rewrite !lookup_insert. eauto.
      - rewrite delete_insert //. by iApply big_sepM_local_state_coh_alloc_node. }
    by iApply network_coh_alloc_node.
  Qed.

  Lemma aneris_state_interp_heap_valid σ l n q v :
    aneris_state_interp σ -∗
    l ↦[n]{q} v -∗
    ∃ h, ⌜state_heaps σ !! n = Some h ∧ h !! l = Some v⌝.
  Proof.
    iIntros "Hσ Hl". iDestruct "Hl" as (?) "[#Hn Hl]".
    iDestruct (mapsto_node_heap_valid with "Hσ Hn") as (h) "%".
    iDestruct "Hσ" as (m) "(Hnauth & % & ? & Hlcoh & Hfreeips & ?)".
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
    iDestruct "Hσ" as (m) "(Hnauth & % & ? & Hlcoh & Hfreeips & ?)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_alloc_heap with "[Hn] Hstate") as "[Hstate' Hl]";
      [done|done|..].
    { by iExists _. }
    iDestruct (big_sepM_local_state_coh_update_heap_notin n with "Hlcoh") as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "[$] Hlcoh") as "HX"; [done|].
    iModIntro. iFrame. iExists _. iFrame.
    iSplitR.
    { iPureIntro. by eapply gnames_coh_update_heap. }
    by iApply free_ips_coh_update_heap.
  Qed.

  Lemma aneris_state_interp_heap_update σ1 n h l v1 v2 :
    let σ2 := (σ1 <| state_heaps := <[n:=<[l:=v2]> h]> (state_heaps σ1) |>) in
    state_heaps σ1 !! n = Some h →
    aneris_state_interp σ1 ∗ l ↦[n] v1 ==∗ aneris_state_interp σ2 ∗ l ↦[n] v2.
  Proof.
    simpl. iIntros (?) "[Hσ Hl]".
    iDestruct "Hl" as (?) "[#Hn Hl]".
    iDestruct "Hσ" as (m) "(Hnauth & % & ? & Hlcoh & Hfreeips & ?)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_update_heap with "[$Hstate Hl]") as "[Hstate' Hl]";
      [done|..].
    { iExists _; eauto. }
    iDestruct (big_sepM_local_state_coh_update_heap_notin n with "Hlcoh") as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh") as "HX";
      [done|].
    iModIntro. iFrame. iExists _. iFrame.
    iSplitR.
    { iPureIntro. by eapply gnames_coh_update_heap. }
    by iApply free_ips_coh_update_heap.
  Qed.

  Lemma aneris_state_interp_socket_valid σ sh ip q skt R T:
    aneris_state_interp σ -∗
    sh ↪[ip]{q} (skt, R, T) -∗
    ∃ Sn, ⌜state_sockets σ !! ip = Some Sn ∧ Sn !! sh = Some (skt, R, T)⌝.
  Proof.
    iIntros "Hσ Hsh". iDestruct "Hsh" as (?) "[#Hn Hl]".
    iDestruct (mapsto_node_heap_valid with "Hσ Hn") as (h) "%".
    iDestruct "Hσ" as (m) "(Hnauth & % & ? & Hlcoh & Hfreeips & ?)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iApply (local_state_coh_valid_sockets with "Hstate [Hl]").
    iExists _;  eauto.
  Qed.

  Lemma aneris_state_interp_alloc_socket s ip sh Sn σ :
    let σ' := σ <| state_sockets := <[ip:=<[sh:=(s, ∅, ∅)]> Sn]> (state_sockets σ) |> in
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    saddress s = None →
    is_node ip -∗
    aneris_state_interp σ ==∗ aneris_state_interp σ' ∗ sh ↪[ip] (s, ∅, ∅).
  Proof.
    simpl. iIntros (???) "Hn Hσ".
    iDestruct "Hn" as (γs) "Hn".
    iDestruct "Hσ" as (m) "(Hnauth & % & ? & Hlcoh & Hfreeips & Hnet)".
    iDestruct (node_gnames_valid with "Hnauth Hn") as %?.
    iDestruct (big_sepM_local_state_coh_delete with "Hlcoh")
      as "(Hstate & Hlcoh)"; [done|].
    iMod (local_state_coh_alloc_socket with "[Hn] Hstate") as "[Hstate' Hl]";
      [done|done|..].
    { by iExists _. }
    iDestruct (big_sepM_local_state_coh_update_socket_notin ip with "Hlcoh") as "Hlcoh".
    { apply lookup_delete. }
    iDestruct (big_sepM_local_state_coh_insert with "Hstate' Hlcoh") as "HX"; [done|].
    iModIntro. iFrame. iExists _. iFrame.
    iSplitR.
    { iPureIntro. by eapply gnames_coh_update_sockets. }
    iSplitL "Hfreeips".
    { by iApply free_ips_coh_alloc_socket. }
    rewrite /set /=.
    by iApply network_coh_alloc_socket.
  Qed.

  Lemma aneris_state_interp_socketbind_static σ1 a sh skt ps Sn A :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt<| saddress := Some a |>, ∅, ∅)]> Sn]> (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    state_ports_in_use σ1 !! ip = Some ps →
    saddress skt = None →
    a ∈ A →
    aneris_state_interp σ1 -∗
    fixed A -∗
    sh ↪[ip_of_address a] (skt, ∅, ∅) -∗
    free_ports ip {[port_of_address a]} ==∗
    aneris_state_interp σ2 ∗ sh ↪[ip] (skt<| saddress := Some a |>, ∅, ∅) ∗
    ∃ φ, a ⤇ φ.
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
    iDestruct (socket_interp_coh_fixed_valid with "Hsock HA") as "#$"; [done|].
    simplify_eq.
    iMod (free_ips_coh_dealloc with "Hfreeips Hp") as "Hfreeips"; [done..|].
    iModIntro. iExists _. iFrame. rewrite /set /=.
    iSplit.
    { iPureIntro; by eapply gnames_coh_update_sockets. }
    iSplitL "Hsock".
    { by iApply socket_interp_coh_socketbind_static. }
    by iApply network_coh_socketbind.
  Qed.

  Lemma aneris_state_interp_socketbind_dynamic σ1 a sh skt ps Sn A φ :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt<| saddress := Some a |>, ∅, ∅)]> Sn]> (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, ∅, ∅) →
    state_ports_in_use σ1 !! ip = Some ps →
    saddress skt = None →
    a ∉ A →
    aneris_state_interp σ1 -∗
    fixed A -∗
    sh ↪[ip_of_address a] (skt, ∅, ∅) -∗
    free_ports ip {[port_of_address a]} ==∗
    aneris_state_interp σ2 ∗ sh ↪[ip] (skt<| saddress := Some a |>, ∅, ∅) ∗
    a ⤇ φ.
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
   Qed.

End state_interpretation.

Global Opaque aneris_state_interp.
