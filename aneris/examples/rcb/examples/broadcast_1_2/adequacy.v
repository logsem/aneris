From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang Require Import proofmode adequacy resources.
From aneris.aneris_lang.program_logic Require Import
  aneris_adequacy.
From aneris.examples.rcb Require Import spec.
From aneris.examples.rcb.util Require Import list_proof_alt.
From aneris.examples.rcb.instantiation Require Import events proof.
From aneris.examples.rcb.examples.broadcast_1_2 Require Import
  prog proof_resources proof_of_main.

Definition broadcast_1_2_is : state :=
  {|
    state_heaps :=  {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $ <["0.0.0.1" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

Definition Σ := #[anerisΣ unit_model; GFunctor (exclR unitO); RCBΣ].

Definition addrs : gset socket_address := {[ z0; z1 ]}.

Definition addr_to_id a : nat :=
  (if bool_decide (a = z0) then 0 else 1)%nat.

Theorem broadcast_1_2_safe :
  aneris_adequate main "system" broadcast_1_2_is (λ _, True).
Proof.
  eapply (@adequacy Σ unit_model _ _ ips addrs ∅ ∅ ∅);
    [ apply unit_model_rel_finitary |  | done | set_solver.. | done | done].
  iIntros (dInvG).
  iMod (main_spec) as (RCBRS) "Hmain".
  iModIntro.
  iIntros "Hf Hsoups _ Hfree _ _ _ _ _".
  iDestruct (big_sepS_delete _ _ z0 with "Hsoups") as "[Hz0 Hsoups]"; first set_solver.
  iDestruct (big_sepS_delete _ _ z1 with "Hsoups") as "[Hz1 _]"; first set_solver.
  iDestruct (unallocated_split with "Hf") as "[Hf1 Hf2]"; [set_solver|].
  iApply (aneris_wp_socket_interp_alloc_singleton (RCB_socket_proto 0)
    with "Hf1").
  iIntros "#Hsi1".
  iApply (aneris_wp_socket_interp_alloc_singleton (RCB_socket_proto 1)
    with "Hf2").
  iIntros "#Hsi2".
  iApply ("Hmain" with "[] [$Hz0] [$Hz1] [$Hfree]").
  repeat iSplitL; last done.
  - iApply "Hsi1".
  - iApply "Hsi2".
Qed.
