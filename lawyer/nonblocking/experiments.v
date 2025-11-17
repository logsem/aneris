From iris.proofmode Require Import proofmode coq_tactics.
From lawyer.nonblocking.logrel Require Export persistent_pred logrel substitutions valid_client.
From lawyer.nonblocking Require Export pwp trace_context. 
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
From heap_lang Require Import heap_lang_defs sswp_logic tactics lang notation. 
From trillium.traces Require Import exec_traces  inftraces trace_lookup.
From fairness Require Import fairness locales_helpers utils.

(* Section EctxLe. *)
(*   Context {Λ: language}.  *)

(*   Definition ectx_le (K1 K2: ectx Λ) := exists K', K2 = ectx_comp K1 K'. *)

(*   Global Instance ectx_le_preorder: PreOrder ectx_le. *)
(*   Proof using. *)
(*     split. *)
(*     - red. intros ?. eexists. apply _.  *)

(* End EctxLe.  *)
  
Close Scope Z. 


