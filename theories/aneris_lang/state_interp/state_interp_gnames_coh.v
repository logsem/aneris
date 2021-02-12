From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import
     aneris_lang notation network resources.
From aneris.aneris_lang.state_interp Require Import
     state_interp_def.
From aneris.aneris_lang.lib Require Import util.

From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Σ}.

  (** gnames_coh *)
  (* TODO: check whether this works out. *)
  Lemma gnames_coh_singleton ip γs h Sn mh:
    gset_map ip_of_address (dom (gset socket_address) mh) = {[ ip ]} →
    gnames_coh {[ip:=γs]} {[ip:=h]} {[ip:=Sn]} mh.
  Proof. rewrite /gnames_coh !dom_singleton_L //. Qed.

  Lemma gnames_coh_valid γm H S ip Mγ :
    H !! ip = None →
    gnames_coh γm H S Mγ →
    γm !! ip = None.
  Proof. rewrite -!not_elem_of_dom => _ [-> _] //. Qed.

  Lemma gnames_coh_alloc_node γm H S ip γn mh ports:
    ports ≠ ∅ →
    gnames_coh γm H S mh →
    gnames_coh (<[ip:=γn]> γm) (<[ip:=∅]> H) (<[ip:=∅]> S)
               (history_init ip ports ∪ mh).
  Proof. rewrite /gnames_coh !dom_insert_L.
         intro Hports.
         move=> [->] [->] [->] //=.
         split_and!; [ set_solver | set_solver |].
           by rewrite dom_union_L gset_map_union
                      dom_gset_to_gmap history_init_dom.
  Qed.

  Lemma gnames_coh_update_heap n γm H S h h' mh:
    H !! n = Some h →
    gnames_coh γm H S mh →
    gnames_coh γm (<[n:=h']> H) S mh.
  Proof.
    intros ?%elem_of_dom_2 [? ?].
    rewrite /gnames_coh dom_insert_L subseteq_union_1_L //=.
    set_solver.
  Qed.

  Lemma gnames_coh_update_sockets n γm H S Sn Sn' mh :
    S !! n = Some Sn →
    gnames_coh γm H S mh →
    gnames_coh γm H (<[n:=Sn']> S) mh.
  Proof.
    intros ?%elem_of_dom_2 [? ?].
    rewrite /gnames_coh dom_insert_L subseteq_union_1_L //=.
    set_solver.
  Qed.

  Lemma gnames_coh_update_history m a γs H S mh v:
    m !! ip_of_address a = Some γs →
    gnames_coh m H S mh →
    gnames_coh m H S (<[a:=v]> mh).
  Proof.
    intros ?%elem_of_dom_2 [? [? Hdmh]].
    rewrite /gnames_coh dom_insert_L //=.
    split_and!; eauto.
    rewrite Hdmh.
    rewrite gset_map_union gset_map_singleton.
    set_solver.
  Qed.


End state_interpretation.
