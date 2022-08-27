From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Export state_interp_def.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  (** local_state_coh *)
  Lemma local_state_coh_heaps n γs γm σ :
    γm !! n = Some γs →
    ([∗ map] n' ↦ γs ∈ γm, local_state_coh σ n' γs) -∗
    ∃ h, ⌜(state_heaps σ) !! n = Some h⌝.
  Proof.
    iIntros (?) "Hmap".
    iDestruct (big_sepM_lookup with "Hmap") as "Hl"; [done|].
    iDestruct "Hl" as (????) "_"; eauto.
  Qed.

  Lemma local_state_coh_sockets n γs γm σ :
    γm !! n = Some γs →
    ([∗ map] n' ↦ γs ∈ γm, local_state_coh σ n' γs) -∗
    ∃ Sn, ⌜(state_sockets σ) !! n = Some Sn⌝.
  Proof.
    iIntros (?) "Hmap".
    iDestruct (big_sepM_lookup with "Hmap") as "Hl"; [done|].
    iDestruct "Hl" as (????) "_"; eauto.
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
    iDestruct 1 as (h' S Hh Hs) "(Hn & Hheap & Hsock)".
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
    iDestruct "Hstate" as (h' Sn Hh Hs) "(#Hn & Hheap & ?)".
    iDestruct "Hl" as (γs') "[Hn' Hl]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    simplify_eq.
    iMod (gen_heap_light_update with "Hheap Hl") as "[Hheap' Hl]".
    iModIntro. iFrame.
    iSplitR "Hl"; [| iExists _; eauto].
    iExists _, _. iFrame.
    rewrite lookup_insert /set /=; eauto.
  Qed.

  Lemma local_state_coh_valid_sockets σ ip γs sh q skt :
    local_state_coh σ ip γs -∗
    sh ↪[ip]{q} skt -∗
    ∃ Sn r, ⌜state_sockets σ !! ip = Some Sn ∧ Sn !! sh = Some (skt, r)⌝.
  Proof.
    iDestruct 1 as (h' Sn Hh Hs) "(Hn & Hh & Hs)".
    iDestruct 1 as (γs') "[Hn' Hsh]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    iDestruct (gen_heap_light_valid with "Hs Hsh") as "%Hfd".
    rewrite lookup_fmap in Hfd.
    destruct (@lookup _ _ (gmap _ _) _ sh Sn) as [[skt' r]|] eqn:Hskteq;
      simplify_eq/=; eauto.
  Qed.

  Lemma local_state_coh_alloc_socket σ ip γs sh Sn skt:
    let σ' := σ <| state_sockets :=
                <[ip:=<[sh:=(skt, [])]> Sn]> (state_sockets σ)|> in
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    is_node ip -∗
    local_state_coh σ ip γs ==∗
    local_state_coh σ' ip γs ∗ sh ↪[ip] skt.
  Proof.
    simpl. iIntros (? HSn) "Hn Hstate". iDestruct "Hn" as (?) "#Hn".
    iDestruct "Hstate" as (h' Sn' Hh Hs) "(Hn' & Hh & Hs)".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    simplify_eq.
    iMod (gen_heap_light_alloc _ sh _ ((skt, ∅ : message_soup).1)  with "Hs")
      as "[Hsock Hsh]".
    { rewrite lookup_fmap HSn //. }
    iModIntro. iFrame.
    iSplitR "Hsh"; [|iExists _; eauto].
    iExists _, (<[sh:=(skt, [])]> Sn).
    rewrite lookup_insert fmap_insert.
    eauto with iFrame.
  Qed.

  Lemma local_state_coh_socketbind σ1 γs sh skt a Sn ps r :
    let ip := ip_of_address a in
    let S' :=
        <[ip :=
            <[sh:=(skt<| saddress := Some a |>, r)]> Sn]> (state_sockets σ1) in
    let P' := <[ip := {[port_of_address a]} ∪ ps]> (state_ports_in_use σ1) in
    let σ2 := σ1 <| state_sockets := S' |> <| state_ports_in_use := P' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    state_ports_in_use σ1 !! ip = Some ps →
    saddress skt = None →
    local_state_coh σ1 ip γs ∗ sh ↪[ip] skt ==∗
    local_state_coh σ2 ip γs ∗ sh ↪[ip] (skt<| saddress := Some a |>).
  Proof.
    simpl. iIntros (????) "[Hlcoh Hsh]".
    iDestruct "Hlcoh" as (h' S Hh Hs) "(#Hn & ? & Hsock)".
    iDestruct "Hsh" as (γs') "[Hn' Hsh]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %<-.
    simplify_eq.
    iMod (gen_heap_light_update _ _ _ _ ((skt<| saddress := Some a |>, r).1)
            with "Hsock Hsh") as "[Hsock' Hsh]".
    rewrite -fmap_insert /=.
    iModIntro. iFrame.
    iSplitR "Hsh"; [| iExists _; eauto].
    iExists _, _; iFrame.
    rewrite lookup_insert /=; eauto.
  Qed.

  Lemma local_state_coh_update_rb a sh skt σ1 γs Sn r r' :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt, r')]> Sn]> (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    local_state_coh σ1 ip γs ∗ sh ↪[ip] skt ==∗
    local_state_coh σ2 ip γs ∗ sh ↪[ip] skt.
  Proof.
    iIntros (?????) "[Hstate Hsh]".
    iDestruct "Hstate" as (h' S Hh Hs) "(#Hn & ? & Hsock)".
    iDestruct "Hsh" as (γs') "[Hn' Hsh]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    simplify_eq.
    iMod (gen_heap_light_update _ _ _ _ ((skt, r').1)
            with "Hsock Hsh") as "[Hsock' Hsh]".
    iModIntro. iFrame. iSplitR "Hsh".
    { iExists _, _. iFrame. rewrite lookup_insert //.
      iSplit; first done. iSplit; first done.
      rewrite fmap_insert /=. eauto with iFrame. }
    iExists _; eauto.
  Qed.

  Lemma local_state_coh_update_sblock a sh skt σ1 γs Sn r b :
    let ip := ip_of_address a in
    let S := <[ip := <[sh:= (skt<| sblock := b|>, r)]> Sn]>(state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    local_state_coh σ1 ip γs ∗ sh ↪[ip] skt ==∗
    local_state_coh σ2 ip γs ∗ sh ↪[ip] (skt<|sblock := b|>).
  Proof.
    simpl. iIntros (??) "[Hstate Hsh]".
    iDestruct "Hstate" as (h' S Hh Hs) "(#Hn & ? & Hsock)".
    iDestruct "Hsh" as (γs') "[Hn' Hsh]".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %->.
    simplify_eq.
    iMod (gen_heap_light_update _ _ _ _ ((skt<|sblock := b|>, r).1)
            with "Hsock Hsh") as "[Hsock' Hsh]".
    iModIntro. iFrame. iSplitR "Hsh".
    { iExists _, _. iFrame. rewrite lookup_insert //.
      iSplit; first done. iSplit; first done.
      rewrite fmap_insert /=. eauto with iFrame. }
    iExists _; eauto.
  Qed.

  Lemma big_sepM_local_state_coh_insert n γs γm σ :
    γm !! n = Some γs →
    local_state_coh σ n γs -∗
    ([∗ map] n' ↦ x ∈ delete n γm, local_state_coh σ n' x) -∗
    [∗ map] n' ↦ x ∈ γm, local_state_coh σ n' x.
  Proof.
    iIntros (Hlookup%insert_id) "Hl Hmap".
    iDestruct (big_sepM_insert with "[$]") as "HP".
    { apply lookup_delete. }
    rewrite insert_delete_insert Hlookup //.
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
    local_state_coh (σ <| state_heaps := <[n:=∅]> (state_heaps σ)|>
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

  Lemma local_state_coh_deliver_message γm σ M Sn Sn' ip sh skt a R m :
    m ∈ messages_to_receive_at a M →
    (state_sockets σ) !! ip = Some Sn →
    Sn !! sh = Some (skt, R) →
    Sn' = <[sh:=(skt, m :: R)]> Sn →
    saddress skt = Some a →
    ([∗ map] ip0↦γs ∈ γm, local_state_coh σ ip0 γs) -∗
    [∗ map] ip0↦γs ∈ γm, local_state_coh
                           {| state_heaps := state_heaps σ;
                              state_sockets := <[ip:=Sn']> (state_sockets σ);
                              state_ports_in_use := state_ports_in_use σ;
                              state_ms := state_ms σ;
                              state_adversaries := state_adversaries σ;
                              state_public_addrs := state_public_addrs σ;
                           |} ip0 γs.
  Proof.
    iIntros (HM Hσ Hsh -> Hskt) "Hγm".
    iApply big_sepM_mono; last done.
    iIntros (ip' γ Hγ) "Hx".
    iDestruct "Hx" as (h Sn' Hip' Hσip') "(Hγ1 & Hγ2 & Hγ3)".
    destruct (decide (ip = ip')) as [->|].
    - simplify_eq.
      rewrite /local_state_coh /= lookup_insert.
      iExists _, _.
      iSplit; first done.
      iSplit; first done.
      rewrite fmap_insert /=.
      rewrite insert_id; first by iFrame.
      rewrite lookup_fmap Hsh //=.
    - rewrite /local_state_coh /= lookup_insert_ne //=.
      iExists _, _; eauto with iFrame.
  Qed.

End state_interpretation.
