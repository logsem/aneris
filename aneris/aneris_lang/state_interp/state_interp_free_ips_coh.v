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

  (** free_ips_coh *)
  Lemma free_ips_coh_init ips σ :
    (∀ ip, ip ∈ ips → ip_is_free ip σ) →
    free_ips_auth ips -∗
    free_ips_coh σ.
  Proof. iIntros (?) "?". by iExists _; iFrame. Qed.

  Lemma free_ips_coh_valid σ ip :
    free_ips_coh σ -∗ free_ip ip -∗
    ⌜state_heaps σ !! ip = None ∧
     state_sockets σ !! ip = None⌝.
  Proof.
    iIntros "Hcoh Hfip".
    iDestruct "Hcoh" as  (Fip HFip) "HfCtx".
    iDestruct (free_ip_included with "HfCtx Hfip") as %Hin.
    iPureIntro. by apply HFip.
  Qed.

  Lemma free_ips_coh_alloc_node σ ip :
    free_ips_coh σ -∗
    free_ip ip ==∗
    free_ips_coh (σ <| state_heaps := <[ip:=∅]> (state_heaps σ)|>
                    <| state_sockets := <[ip:=∅]> (state_sockets σ) |>).
  Proof.
    iDestruct 1 as (Fip HFip) "HfCtx".
    iIntros "Hfip".
    iDestruct (free_ip_included with "HfCtx Hfip") as %Hin.
    iMod (free_ip_dealloc with "HfCtx Hfip") as "HfCtx".
    iModIntro. iExists _. iFrame. iPureIntro.
    intros ip' Hip'. rewrite elem_of_difference in Hip'.
    destruct Hip' as [Hin' Hneq%not_elem_of_singleton].
    split; simplify_map_eq; by apply HFip.
  Qed.

  Lemma free_ips_coh_update_heap σ ip h h' :
    state_heaps σ !! ip = Some h →
    free_ips_coh σ -∗
    free_ips_coh (σ <| state_heaps := <[ip:=h']> (state_heaps σ) |>).
  Proof.
    iIntros (?).
    iDestruct 1 as (Fip HFip) "HfCtx".
    iExists _. simpl. iFrame. iPureIntro.
    intros ip' Hip'. apply HFip in Hip' as [Hheap Hskt].
    destruct (decide (ip = ip')); simplify_map_eq.
    split; [|done]. by rewrite lookup_insert_ne.
  Qed.

  Lemma free_ips_coh_update_sockets σ ip Sn Sn' :
    state_sockets σ !! ip = Some Sn →
    free_ips_coh σ -∗
    free_ips_coh (σ <| state_sockets := <[ip:= Sn']> (state_sockets σ)|>).
  Proof.
    iIntros (?). iDestruct 1 as (Fip HFip) "HfCtx".
    iExists _. simpl. iFrame. iPureIntro.
    intros ip' Hip'. apply HFip in Hip' as [Hheap Hskt].
    destruct (decide (ip = ip')); simplify_map_eq.
    split; [done|]. by rewrite lookup_insert_ne.
  Qed.

  Lemma free_ips_coh_ms hps skts ms1 ms2 :
    free_ips_coh {|
      state_heaps := hps;
      state_sockets := skts;
      state_ms := ms1;
      |} -∗
    free_ips_coh {|
      state_heaps := hps;
      state_sockets := skts;
      state_ms := ms2;
    |}.
  Proof. done. Qed.

End state_interpretation.
