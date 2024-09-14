From iris.proofmode Require Import tactics coq_tactics.
(* From iris.algebra Require Import auth gmap gset excl. *)
(* From iris.base_logic Require Export gen_heap. *)
(* From trillium.program_logic Require Export weakestpre adequacy ectx_lifting. *)
From trillium.fairness Require Import locales_helpers utils.
From trillium.fairness.lawyer Require Import obligations_model obls_utils obligations_resources program_logic.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


Close Scope Z.

(* Definition EODegree n := Fin.t (S n). *)
(* Definition EOLevel n := Fin.t (S n). *)
Definition EODegree n := { i | i < n }. 
Definition EOLevel n := { i | i < n }. 

Section EoFin.
  Context (LIM: nat).
  Let MAX_OBL_STEPS := 10.
  
  Instance EO_OP: ObligationsParams (EODegree LIM) (EOLevel LIM) (locale heap_lang) MAX_OBL_STEPS.
  Proof using.
    esplit; try by apply _.
    - rewrite /EODegree.
      exact (fun d1 d2 => proj1_sig d1 < proj1_sig d2).
    - exact (fun d1 d2 => proj1_sig d1 < proj1_sig d2).
  Defined.

  Let OM := ObligationsModel EO_OP.

  Let EODegreeOfe := sigO (fun i => i < LIM). 
  Let EOLevelOfe := sigO (fun i => i < LIM).

  Instance foo: LeibnizEquiv EOLevelOfe.
  Admitted. 
  
  Let EM := @ObligationsEM EODegreeOfe EOLevelOfe _ _ _ heap_lang _ _ _ EO_OP. 

  Context `{hGS: @heapGS Σ _ EM}.
  Let oGS : ObligationsGS EO_OP Σ := heap_fairnessGS (heapGS := hGS).

  


End EoFin.
