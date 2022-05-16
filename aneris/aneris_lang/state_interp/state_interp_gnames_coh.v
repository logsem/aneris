From stdpp Require Import fin_maps gmap.
From aneris.aneris_lang Require Import aneris_lang network resources.
From aneris.aneris_lang.state_interp Require Import state_interp_def.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import RecordSetNotations.

Section state_interpretation.
  Context `{!anerisG Mdl Σ}.

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
  Proof. rewrite /gnames_coh. set_solver. Qed.

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

End state_interpretation.
