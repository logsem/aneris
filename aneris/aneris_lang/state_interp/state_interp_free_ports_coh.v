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

  Lemma free_ports_coh_init free_ports σ :
    set_Forall
      (λ p,
         (∀ Sn, (state_sockets σ) !! (ip_of_address p) = Some Sn →
                port_not_in_use (port_of_address p) Sn)) free_ports →
    free_ports_auth free_ports -∗
    free_ports_coh σ.
  Proof. iIntros (?) "?". by iExists _; iFrame. Qed.

  Lemma free_ports_coh_free_ports_valid σ a Sn :
    state_sockets σ !! ip_of_address a = Some Sn →
    free_ports_coh σ -∗
    free_ports {[a]} -∗
    ⌜port_not_in_use (port_of_address a) Sn⌝.
  Proof.
    iIntros (Hskts). iDestruct 1 as (ports Hports) "HpCtx". iIntros "Hp".
    iDestruct (free_ports_included with "HpCtx Hp") as "%".
    iPureIntro. eapply Hports; [set_solver|done].
  Qed.

  Lemma free_ports_coh_alloc_node ip σ :
    state_sockets σ !! ip = None →
    free_ports_coh σ -∗
    free_ports_coh (σ <| state_sockets := <[ip := ∅]> (state_sockets σ) |>).
  Proof.
    intros Hip.
    iDestruct 1 as (ps Hps) "HpsCtx".
    iExists _. iFrame. iPureIntro.
    intros sa Hin Sn' HPs'.
    destruct (decide (ip = ip_of_address sa)); simplify_map_eq.
    - intros ???????. set_solver.
    - by eapply Hps.
  Qed.

  Lemma free_ports_coh_alloc_socket ip σ Sn sh s r :
    state_sockets σ !! ip = Some Sn →
    Sn !! sh = None →
    saddress s = None →
    free_ports_coh σ -∗
    free_ports_coh
      (σ <| state_sockets :=
         <[ip := <[sh := (s,r)]>Sn]>
           (state_sockets σ) |>).
  Proof.
    intros Hip.
    iDestruct 1 as (ps Hps) "HpsCtx".
    iExists _. iFrame. iPureIntro.
    intros sa Hin Sn' HSn'.
    destruct (decide (ip = ip_of_address sa)); simplify_map_eq.
    - intros sh' skt' a' r' Hsh' Haddr.
      destruct (decide (sh = sh')) as [->|Hneq].
      + rewrite lookup_insert in Hsh'. simplify_eq.
      + rewrite lookup_insert_ne in Hsh'; [|done]. by eapply Hps.
    - by eapply Hps.
  Qed.

  Lemma free_ports_coh_update_socket sh ip skt1 skt2 Sn r1 r2 σ1 :
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt1, r1) →
    saddress skt1 = saddress skt2 →
    free_ports_coh σ1 -∗
    free_ports_coh
      (σ1 <| state_sockets :=
         <[ip := <[sh:=(skt2, r2)]> Sn]>
                     (state_sockets σ1) |>).
  Proof.
    destruct skt1, skt2.
    intros Hskt HSn Hsh.
    iDestruct 1 as (ps Hps) "HpsCtx".
    iExists _. iFrame. iPureIntro.
    intros sa Hin Sn' HSn'.
    destruct (decide (ip = ip_of_address sa)); simplify_map_eq.
    - intros sh' skt' a' r' Hsh' Haddr.
      destruct (decide (sh = sh')) as [->|Hneq].
      + rewrite lookup_insert in Hsh'. simplify_eq. by eapply Hps.
      + rewrite lookup_insert_ne in Hsh'; [|done]. by eapply Hps.
    - by eapply Hps.
  Qed.

  (* Special case of [free_ports_coh_update_socket]
     that matches some goals better syntactically *)
  Lemma free_ports_coh_update_sblock sh ip skt b Sn r1 r2 σ1 :
    state_sockets σ1 !! ip = Some Sn →
    Sn !! sh = Some (skt, r1) →
    free_ports_coh σ1 -∗
    free_ports_coh
      (σ1 <| state_sockets :=
         <[ip := <[sh:=(skt<| sblock := b|>, r2)]> Sn]>
                     (state_sockets σ1) |>).
  Proof. iIntros (??) "?". by iApply free_ports_coh_update_socket. Qed.

  Lemma free_ports_coh_bind_socket σ1 sa r sh skt Sn :
    state_sockets σ1 !! ip_of_address sa = Some Sn →
    free_ports_coh σ1 -∗
    free_ports {[sa]} ==∗
    free_ports_coh
      (σ1 <| state_sockets :=
         <[ip_of_address sa :=
             <[sh:=(skt<| saddress := Some sa |>, r)]> Sn]>
                 (state_sockets σ1) |>).
  Proof.
    intros HSome.
    iDestruct 1 as (Ps HPs) "HpCtx".
    iIntros "Hp".
    iMod (free_ports_dealloc with "HpCtx Hp") as "HpCtx".
    iModIntro. iExists _; iFrame. iPureIntro.
    destruct sa as [ip p].
    intros [ip' p'] Hin Sn' HSn'.
    destruct (decide (ip = ip')); simplify_map_eq.
    - intros sh' skt' a' r' Hsh' Haddr.
      destruct (decide (sh = sh')) as [->|Hneq].
      + rewrite lookup_insert in Hsh'. simplify_eq. simpl in Haddr.
        simplify_eq. by set_solver.
      + rewrite lookup_insert_ne in Hsh'; [|done].
        eapply (HPs (SocketAddressInet ip' p')); try done. set_solver.
    - eapply (HPs (SocketAddressInet ip' p')); try done. set_solver.
  Qed.

  Lemma free_ports_coh_update hps1 hps2 skts ms1 ms2 :
    free_ports_coh {|
      state_heaps := hps1;
      state_sockets := skts;
      state_ms := ms1;
      |} -∗
    free_ports_coh {|
      state_heaps := hps2;
      state_sockets := skts;
      state_ms := ms2;
    |}.
  Proof.
    iDestruct 1 as (ps Hps) "HpsCtx".
    iExists _. by iFrame.
  Qed.

End state_interpretation.
