From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import saved_prop gen_heap.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import
     aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

  Definition ip_is_free (ip : ip_address) (σ : state) : Prop :=
    state_heaps σ !! ip = None ∧ state_sockets σ !! ip = None.

  (** free_ips_coh *)
  Lemma free_ips_coh_init ips σ :
    (∀ ip, ip ∈ ips → ip_is_free ip σ) →
    free_ips_auth ips ∗ free_ports_auth ∅ -∗
    free_ips_coh σ.
  Proof.
    iIntros (Hip) "[HipsCtx HPiu]".
    iExists _, _; iFrame.
    iPureIntro. set_solver.
  Qed.

  (** free_ips_coh_strong *)
  Lemma free_ips_coh_init_strong ips Ps σ :
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

  Lemma free_ips_coh_free_ports_valid σ a Sn :
    state_sockets σ !! ip_of_address a = Some Sn →
    free_ips_coh σ -∗
    free_ports (ip_of_address a) {[port_of_address a]} -∗
    ⌜port_not_in_use (port_of_address a) Sn⌝.
  Proof.
    iDestruct 1 as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]". iIntros "Hp".
    iDestruct (free_ports_included with "HpCtx Hp") as (?) "[%Hlookup %]".
    unfold port_not_in_use. iPureIntro. intros sh skt sa r Hsh Hsa.
    destruct HFip as [? HFip]. eapply HFip; eauto. set_solver.
  Qed.

  Lemma free_ips_coh_alloc_node σ ip ports :
    free_ips_coh σ -∗
    free_ip ip ==∗
    free_ips_coh (σ <| state_heaps := <[ip:=∅]> (state_heaps σ)|>
                    <| state_sockets := <[ip:=∅]> (state_sockets σ) |>) ∗
    free_ports ip ports.
  Proof.
    iDestruct 1 as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]".
    iIntros "Hfip".
    iDestruct (free_ip_included with "HfCtx Hfip") as %Hin.
    iMod (free_ip_dealloc with "HfCtx Hfip") as "HfCtx".
    iMod (free_ports_alloc _ ip ports with "HpCtx") as "[HpCtx Hports]";
      [set_solver|].
    iModIntro. iFrame. iExists _, _. simpl. iFrame. iPureIntro.
    split; [set_solver|]. split.
    { intros. rewrite !lookup_insert_ne //; set_solver. }
    intros ip' ??????????.
    destruct (decide (ip = ip')).
    - subst. simpl_map. naive_solver.
    - simplify_map_eq. eapply HFip; eauto.
  Qed.

  Lemma free_ips_coh_update_heap σ ip h h' :
    state_heaps σ !! ip = Some h →
    free_ips_coh σ -∗
    free_ips_coh (σ <| state_heaps := <[ip:=h']> (state_heaps σ) |>).
  Proof.
    iIntros (?).
    iDestruct 1 as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]".
    iExists _, _. simpl. iFrame. iPureIntro.
    split; auto. split; try apply HFip.
    intros ip' ?.
    split; [|set_solver].
    destruct (decide (ip = ip')); simplify_map_eq; [set_solver|].
    by apply HFip.
  Qed.

  Lemma free_ips_coh_alloc_socket σ ip Sn sh s:
    let σ' :=
        σ <| state_sockets := <[ip:=<[sh:=(s, [])]> Sn]> (state_sockets σ) |> in
    saddress s = None →
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    free_ips_coh σ -∗ free_ips_coh σ'.
  Proof.
    iIntros (????).
    iDestruct 1 as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]".
    iExists _, _. iFrame. iPureIntro.
    split; [done|]. simpl. split.
    - intros ip' ?. split; [by eapply HFip|].
      destruct (decide (ip = ip')); simplify_map_eq; [set_solver|].
      by apply HFip.
    - intros ip' ??????????.
      destruct (decide (ip = ip')) as [->|Hipneq].
      + simplify_map_eq.
        destruct (decide (sh = sh0)) as [->|Hshneq].
        * intros Hsocket ?. rewrite lookup_insert in Hsocket. by simplify_eq.
        * intros Hsocket ?. apply (lookup_insert_ne Sn sh sh0 (s, [])) in Hshneq.
          rewrite Hshneq in Hsocket. by eapply HFip.
      + simplify_map_eq. by eapply HFip.
  Qed.

  Lemma free_ips_coh_dealloc σ1 a sh skt Sn :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt<| saddress := Some a |>, [])]> Sn]>
              (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |>  in
    state_sockets σ1 !! ip = Some Sn →
    free_ips_coh σ1 -∗
    free_ports (ip_of_address a) {[port_of_address a]} ==∗
    free_ips_coh σ2.
  Proof.
    rewrite /free_ips_coh /=.
    iDestruct 1 as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]".
    iIntros "Hp".
    iMod (free_ports_dealloc with "HpCtx Hp")
      as (ps' [Hps' Hin%elem_of_subseteq_singleton]) "HpCtx".
    iModIntro. iExists _, _; iFrame. iPureIntro.
    split; [set_solver|]. split.
    - intros ip ?.
    destruct (decide (ip = ip_of_address a)); simplify_eq; [set_solver|].
    rewrite lookup_insert_ne //. by apply HFip.
    - intros ip ??????????.
      destruct (decide (ip= (ip_of_address a))) as [->|Hipneq].
      + simplify_map_eq. destruct (decide (sh = sh0)) as [->|Hsneq].
        * intros Hsockets ?. apply lookup_insert_rev in Hsockets. set_solver.
        * apply (lookup_insert_ne Sn sh sh0
        ({| saddress := Some a; sblock := sblock skt |}, []))  in Hsneq.
        intros Hsockets ?. rewrite Hsneq in Hsockets. set_solver.
      + simplify_map_eq. eapply HFip; eauto.
  Qed.

Lemma free_ips_coh_update_msg sh a skt Sn r m σ1 :
    let ip := ip_of_address a in
    let S' := <[ip := <[sh:=(skt, r)]> Sn]> (state_sockets σ1) in
    let σ2 := σ1 <| state_sockets := S' |> in
    Sn !! sh = Some (skt, r ++ [m]) →
    state_sockets σ1 !! ip_of_address a = Some Sn →
    free_ips_coh σ1 -∗ free_ips_coh σ2.
  Proof.
    rewrite /free_ips_coh /=.
    iDestruct 1 as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]".
    iExists _, _. iFrame. iPureIntro.
      split; [auto|]. split.
      - intros ip ?. split; [set_solver|].
        destruct (decide (ip = ip_of_address a)); simplify_map_eq; [set_solver|].
        by apply HFip.
      - intros ip ??????????. destruct (decide (ip = (ip_of_address a))) as [->|Hipneq].
        + simpl_map. simplify_eq. intros Hsockets ?.
           destruct (decide (sh = sh0)) as [->|Hshneq].
           * apply (lookup_insert_rev Sn sh0
           (skt, r) (skt0, r0)) in Hsockets. simplify_eq.
           eapply HFip; eauto.
           * apply (lookup_insert_ne Sn sh sh0 (skt, r))  in Hshneq.
           rewrite Hshneq in Hsockets. eapply HFip; eauto.
        + simplify_map_eq. eapply HFip; eauto.
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
         state_ms := state_ms σ;
         state_trace := state_trace σ  |}.
  Proof.
    rewrite /free_ips_coh /=.
    iDestruct 1 as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]".
    iExists _, _. simpl. iFrame. iPureIntro.
    split; [auto|]. split.
    - intros ip' ?.
      ddeq ip ip'.
      + naive_solver.
      + destruct (decide (ip' = ip_of_address a)); simplify_map_eq; [set_solver|].
        by apply HFip.
    - intros ip' ??????????.
      destruct (decide (ip = ip')) as [->|Hipneq].
      + simpl_map. simplify_eq. intros Hsockets ?.
         destruct (decide (sh = sh0)) as [->|Hshneq].
         * apply (lookup_insert_rev Sn sh0
         (skt, m :: R) (skt0, r)) in Hsockets.
         simplify_eq. eapply HFip; eauto.
         * apply (lookup_insert_ne Sn sh sh0
         (skt, m :: R)) in Hshneq. rewrite Hshneq in Hsockets.
         eapply HFip; eauto.
      + simplify_map_eq. eapply HFip; eauto.
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
    iDestruct 1 as (Fip Piu (Hdsj & HFip)) "[HfCtx HpCtx]".
    iExists _, _. simpl. iFrame. iPureIntro.
    split; auto. split.
    - intros ip' Hip'.
    simplify_map_eq. subst S.
    ddeq ip ip'; set_solver.
    - intros ip' ??????????. unfold S in H2.
      destruct (decide (ip = ip')) as [->|Hipneq].
      -- simpl_map. simplify_eq. intros Hsockets ?.
      destruct (decide (sh = sh0)) as [->|Hshneq].
      + apply (lookup_insert_rev Sn sh0
      ({| saddress := saddress skt; sblock := b |}, r) (skt0, r0)) in Hsockets.
      simplify_eq. eapply HFip; eauto.
      + apply (lookup_insert_ne Sn sh sh0
      ({| saddress := saddress skt; sblock := b |}, r)) in Hshneq.
      rewrite Hshneq in Hsockets. eapply HFip; eauto.
      -- simplify_map_eq. eapply HFip; eauto.
  Qed.

  Lemma free_ips_coh_ms hps skts ms1 ms2 trace1 trace2:
    free_ips_coh {|
      state_heaps := hps;
      state_sockets := skts;
      state_ms := ms1;
      state_trace := trace1 
      |} -∗
    free_ips_coh {|
      state_heaps := hps;
      state_sockets := skts;
      state_ms := ms2;
      state_trace := trace2
    |}.
  Proof. done. Qed.

End state_interpretation.
