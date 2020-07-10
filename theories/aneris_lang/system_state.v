From iris.algebra Require Import auth gmap frac agree.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris Require Export lang network.
Set Default Proof Using "Type".
Import uPred.
Import Network.

(** The System State CMRA we need. *)
Class system_stateG (Σ : gFunctors) := SystemStateG {
  system_state_inG :> inG Σ (authR (gmapUR node
                                           (prodR (gen_heapUR loc val)
                                                  (gen_heapUR socket_handle socket))));
  system_state_name : gname
}.

Arguments system_state_name {_} _ : assert.
