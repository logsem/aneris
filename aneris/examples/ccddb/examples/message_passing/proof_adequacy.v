From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     lang network tactics proofmode.
From aneris.aneris_lang.program_logic Require Import aneris_adequacy.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb Require Import spec_util.
From aneris.examples.ccddb.examples Require Import lib.
From aneris.examples.ccddb.examples.message_passing Require Import prog.
From aneris.examples.ccddb.examples.message_passing Require Import
     proof_resources proof_of_node0 proof_of_node1 proof_of_main.


Definition init_state :=
  {|
    state_heaps := {[ "system" := ∅ ]};
    state_sockets := {[ "system" := ∅ ]};
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $ <["0.0.0.1" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition fixed_dom : gset socket_address := {[ z0; z1 ]}.

(* TODO: factor this out, together with the proof of finite branching *)
Definition dummy_model := model unit (fun x y => True) ().

Lemma dummy_model_finitary : adequacy.aneris_model_rel_finitary dummy_model.
Proof.
 intros st.
 intros f Hnot.
 pose proof (Hnot 0%nat 1%nat) as H.
 assert (0%nat = 1%nat -> False) as Himpl. {
   intros Heq.
   discriminate Heq.
 }
 apply Himpl; apply H.
 destruct (f 0%nat) as [s0 r0].
 destruct (f 1%nat) as [s1 r1].
 destruct s0, s1, st, r0, r1.
 reflexivity.
Qed.

(* TODO: why can't we rewrite with this
Lemma decide_aux z : bool_decide (elem_of (B := gset socket_address) z ∅) = false.
Proof.
  set d := elem_of (B := gset socket_address) z ∅.
  destruct (bool_decide d) eqn:Heq; [exfalso; set_solver |].
  done.
Qed.
*)

From aneris.examples.ccddb.instantiation Require Import proof.

Theorem adequacy : aneris_adequate main "system" init_state (λ _, True).
Proof.
 set (Σ := #[anerisΣ dummy_model; mpΣ; DBΣ]).
 eapply (@adequacy Σ dummy_model _ _ ips fixed_dom ∅ ∅ ∅);
   try done; last first.
  { set_solver. }
  { intros i. rewrite /ips !elem_of_union !elem_of_singleton.
    intros [|]; subst; simpl; set_solver. }
  { rewrite /ips /= !dom_insert_L dom_empty_L right_id_L //. }
  2: { apply dummy_model_finitary. }
  iIntros (Hdg) "".
  iPoseProof (main_spec fixed_dom) as "Hmain".
  iMod "Hmain" as (dbr) "Hmain".
  iModIntro.
  iIntros "Hfx Hproto Hrs Hips".
  iDestruct (big_sepS_delete _ _ z0 with "Hproto") as "[Hz0 Hproto]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ z1 with "Hproto") as "[Hz1 _]";
    first set_solver.
  set d0 := elem_of (B := gset socket_address) z0 ∅.
  destruct (bool_decide d0) eqn:Heq0; [exfalso; set_solver |].
  set d1 := elem_of (B := gset socket_address) z1 ∅.
  destruct (bool_decide d1) eqn:Heq1; [exfalso; set_solver |].
  iIntros "?????".
  iApply (aneris_wp_socket_interp_alloc DB_socket_proto with "Hfx").
  iIntros "Hsi".
  iApply ("Hmain" with "[Hsi] Hz0 Hz1 Hips").
  rewrite /DB_addresses /fixed_dom. simpl.
  rewrite big_sepS_union; [|set_solver].
  rewrite !big_sepS_singleton.
  iDestruct "Hsi" as "[Hsi1 Hsi2]".
  iFrame.
Qed.
