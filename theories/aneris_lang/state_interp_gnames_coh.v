From stdpp Require Import fin_maps gmap.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris_string_ident Require Import ltac2_string_ident.
From aneris.program_logic Require Export weakestpre adequacy.
From aneris.program_logic Require Import ectx_lifting.
From aneris.program_logic Require Export gen_heap_light.
From aneris.aneris_lang Require Export
     aneris_lang notation network resources
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
  Lemma gnames_coh_singleton_empty ip γs :
    gnames_coh {[ip:=γs]} {[ip:=∅]} {[ip:=∅]} {[ip:=∅]}.
  Proof. rewrite /gnames_coh !dom_singleton_L //. Qed.

  Lemma gnames_coh_singleton ip γs h Sn p R T:
    gnames_coh {[ip:=γs]} {[ip:=h]} {[ip:=Sn]} {[ip:= {[p:=(R,T)]} ]}.
  Proof. rewrite /gnames_coh !dom_singleton_L //. Qed.

  Lemma gnames_coh_valid γm H S ip Mγ :
    H !! ip = None →
    gnames_coh γm H S Mγ →
    γm !! ip = None.
  Proof. rewrite -!not_elem_of_dom => _ [-> _] //. Qed.

  Lemma gnames_coh_alloc_node γm H S ip γn mhγ ports:
    gnames_coh γm H S mhγ →
    gnames_coh (<[ip:=γn]> γm) (<[ip:=∅]> H) (<[ip:=∅]> S)
               (<[ip:= messages_init ports]> mhγ).
  Proof. rewrite /gnames_coh !dom_insert_L.
         move=> [->] //=. set_solver.
  Qed.

  Lemma gnames_coh_update_heap n γm H S h h' Mγ:
    H !! n = Some h →
    gnames_coh γm H S Mγ →
    gnames_coh γm (<[n:=h']> H) S Mγ.
  Proof.
    intros ?%elem_of_dom_2 [? ?].
    rewrite /gnames_coh dom_insert_L subseteq_union_1_L //=.
    set_solver.
  Qed.

  Lemma gnames_coh_update_sockets n γm H S Sn Sn' Mγ :
    S !! n = Some Sn →
    gnames_coh γm H S Mγ →
    gnames_coh γm H (<[n:=Sn']> S) Mγ.
  Proof.
    intros ?%elem_of_dom_2 [? ?].
    rewrite /gnames_coh dom_insert_L subseteq_union_1_L //=.
    set_solver.
  Qed.

End state_interpretation.
