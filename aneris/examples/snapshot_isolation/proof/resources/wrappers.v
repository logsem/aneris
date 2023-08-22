From iris.algebra Require Import agree auth excl gmap updates local_updates.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.mt_server Require Import user_params.
From aneris.examples.snapshot_isolation.specs Require Import user_params resources.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import resource_algebras server_resources proxy_resources
     global_invariant.

Section Wrapper_defs.
  Context `{!anerisG Mdl Σ, !IDBG Σ, !MTS_resources}.
  Context `{!User_params}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT : gname).

  Definition to_hist (h : list write_event) : list val := (λ e, e.(we_val)) <$> h.

  Definition to_local_state (s : proxy_state) : local_state :=
    match s with
      PSCanStart => CanStart
    | PSActive m => Active ((λ h, to_hist h) <$> m)
    end.

  Lemma to_hist_prefix_mono hw hw' :
    hw `prefix_of` hw' →  to_hist hw `prefix_of` to_hist hw'.
  Proof.
    intros Hp.
    generalize dependent hw'.
    induction hw as [|x l]; intros hw' Hp.
    - by apply prefix_nil.
    - destruct hw' as [|x' l'].
      -- by apply prefix_nil_not in Hp.
      -- simplify_eq /=.
         assert (x = x') as -> by by apply prefix_cons_inv_1 in Hp.
         apply prefix_cons.
         apply IHl.
         by apply prefix_cons_inv_2 in Hp.
  Qed.

  Definition GlobalInv_def : iProp Σ :=
    Global_Inv clients γKnownClients γGauth γGsnap γT.

  Definition OwnMemKey_def k h : iProp Σ :=
    ∃ hw, ownMemUser γGauth γGsnap k hw ∗ ⌜h = to_hist hw⌝.

  Definition ConnectionState_def c sa s : iProp Σ :=
    ∃ sp, connection_state γGsnap γT γKnownClients c sa sp ∗ ⌜s = to_local_state sp⌝.

  Definition Seen_def k h : iProp Σ :=
    ∃ hw, ownMemSeen γGsnap k hw ∗ ⌜h = to_hist hw⌝.

  Definition client_can_connect_res sa : iProp Σ :=
    client_can_connect γKnownClients sa.

  Lemma mem_key_map_we_exists m :
    ([∗ map] k↦hv ∈ m, OwnMemKey_def k hv) -∗
    ∃ M, ([∗ map] k↦h ∈ M, ownMemUser γGauth γGsnap k h) ∗
         ⌜m = (λ h, to_hist h)<$>M⌝.
  Proof. Admitted.


End Wrapper_defs.
