(** Realisation of the DB_resources interface *)
From iris.algebra Require Import agree auth excl gmap.
From aneris.algebra Require Import monotone.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting.
From aneris.aneris_lang.lib Require Import list_proof map_proof vector_clock_proof lock_proof.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import model_lst model_spec.
From aneris.examples.ccddb.resources Require Import
     base resources_gmem resources_lhst.

Import ast.

Section Local_invariant.
  Context `{anerisG Mdl Σ, !DB_params, !internal_DBG Σ}.
  Context (γGauth γGsnap γGkeep : gname) (γLs : list (gname * gname)).

  Definition InQueue_of_write_events ip Q lq vq : iProp Σ :=
    Q ↦[ip] vq ∗
    ⌜is_list lq vq⌝ ∗
    ([∗ list] a ∈ lq, own_mem_snapshot γGsnap a.(we_key) {[a]}).

  Definition OutQueue_of_write_events i ip Q lq vq : iProp Σ :=
    Q ↦[ip] vq ∗
    ⌜is_list lq vq⌝ ∗
    ([∗ list] a ∈ lq, ⌜DB_Serializable a.(we_val)⌝ ∗
                      ⌜a.(we_key) ∈ DB_keys⌝ ∗
                      ⌜a.(we_orig) = i⌝ ∗
                      own_mem_snapshot γGsnap a.(we_key) {[a]})%I.

  Definition local_inv_def (i : nat) (DB T IQ OQ : loc) : iProp Σ :=
    ∃ (vd vt viq voq : val) (d : gmap Key val)
      (t: vector_clock) (liq loq: list write_event) (s: gset apply_event)
      (ip : ip_address),
      ⌜ip_of_address <$> DB_addresses !! i = Some ip⌝ ∗
      DB ↦[ip] vd ∗ T ↦[ip] vt ∗
      InQueue_of_write_events ip IQ liq viq ∗
      OutQueue_of_write_events i ip OQ loq voq ∗
      ⌜is_map vd d⌝ ∗ ⌜is_vc vt t⌝ ∗
      local_history_Local_inv γLs i s ∗
      ⌜DBM_Lst_valid i {| Lst_mem := d; Lst_time := t; Lst_hst := s|}⌝.

  Definition local_invariant
             (i : nat) (DB T InQueue OutQueue : loc) (lk : val)
             (γlk : gname) (z : socket_address) : iProp Σ :=
    is_lock (ip_of_address z) γlk lk
            (local_inv_def i DB T InQueue OutQueue).

  Instance local_invariant_persistent i DB IQ OQ T lk γLk z :
    Persistent (local_invariant i DB T IQ OQ lk γLk z).
  Proof. apply _. Qed.

End Local_invariant.
