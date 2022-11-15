From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From fairneris.lib Require Import gen_heap_light.
From fairneris.aneris_lang Require Import
     aneris_lang network resources.
From fairneris.aneris_lang.state_interp Require Import
     state_interp_def.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  (** free_ips_coh *)
  Lemma free_ips_coh_init ip ips σ :
    ip ∉ ips →
    dom (state_ports_in_use σ) = ips →
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
    free_ips_coh (σ <| state_heaps := <[ip:=∅]> (state_heaps σ)|>
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
    let σ' :=
        σ <| state_sockets := <[ip:=<[sh:=sock]> Sn]> (state_sockets σ) |> in
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
    let S' := <[ip := <[sh:=(skt<| saddress := Some a |>, [])]> Sn]>
              (state_sockets σ1) in
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

  Lemma free_ips_coh_update_msg sh a skt Sn r' σ1 :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt, r')]> Sn]> (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |> in
    state_sockets σ1 !! ip_of_address a = Some Sn →
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

  Lemma free_ips_coh_deliver_message σ M Sn Sn' ip sh skt a R m :
    m ∈ messages_to_receive_at a M →
    (state_sockets σ) !! ip = Some Sn →
    Sn !! sh = Some (skt, R) →
    Sn' = <[sh:=(skt, m :: R)]> Sn →
    saddress skt = Some a →
    free_ips_coh σ -∗
    free_ips_coh
      {| state_heaps := state_heaps σ;
         state_sockets := <[ip:=Sn']> (state_sockets σ);
         state_ports_in_use := state_ports_in_use σ;
         state_ms := state_ms σ |}.
  Proof.
    rewrite /free_ips_coh /=.
    iDestruct 1 as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iExists _, _. simpl. iFrame. iPureIntro.
    do 2 (split; [auto|]).
    split; [|done].
    intros ip' ?. split; [set_solver|].
    ddeq ip ip'.
    - naive_solver.
    - destruct (decide (ip' = ip_of_address a)); simplify_map_eq; [set_solver|].
      by apply HFip2.
  Qed.

  Lemma free_ips_coh_update_sblock σ1 a Sn sh skt b r :
    let ip := ip_of_address a in
    let S := <[ip := <[sh:= (skt<| sblock := b|>, r)]> Sn]>(state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S |> in
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r) →
    free_ips_coh σ1 ==∗ free_ips_coh σ2.
  Proof.
    iIntros (?).
    iDestruct 1 as (Fip Piu (Hdsj & HFip & HFip2 & HPiu)) "[HfCtx HpCtx]".
    iExists _, _. simpl. iFrame. iPureIntro.
    do 3 (split; auto).
    intros ip' Hip'.
    simplify_map_eq. subst S.
    ddeq ip ip'; set_solver.
  Qed.

  Lemma free_ips_coh_ms hps skts ports ms1 ms2 :
    free_ips_coh {|
      state_heaps := hps;
      state_sockets := skts;
      state_ports_in_use := ports;
      state_ms := ms1;
      |} -∗
    free_ips_coh {|
      state_heaps := hps;
      state_sockets := skts;
      state_ports_in_use := ports;
      state_ms := ms2;
    |}.
  Proof. done. Qed.

End state_interpretation.
