(* From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From aneris.examples.snapshot_isolation.examples.function_call
      Require Import function_call_code.
Import ser_inj.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
From aneris.examples.snapshot_isolation.util Require Import util_proof.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_addr := SocketAddressInet "0.0.0.1" 80.

Program Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Section proof_of_code.

  Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !SI_specs}.

  Definition f_spec (f : val) (P : option val → iProp Σ)
    (Q : option val → SerializableVal → iProp Σ) : iProp Σ :=
    ∀ vo sa, {{{ P vo }}} f $vo @[ip_of_address sa]
              {{{ v', RET (SV_val v'); Q vo v' }}}.

  Lemma transaction_spec :
    ∀ (cst f : val) sa h P Q,
    f_spec f P Q -∗
    {{{ P (hist_val h) ∗ "x" ↦ₖ h ∗ ConnectionState cst CanStart }}}
      transaction cst f @[ip_of_address sa]
    {{{ v', RET #(); Q (hist_val h) v' ∗ "x" ↦ₖ ((SV_val v') :: h) ∗
                    ConnectionState cst CanStart }}}.
  Proof.
    iIntros (cst f sa h P Q) "#f_spec %Φ !>(P & x_h & CanStart) HΦ".
    rewrite/transaction.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ ⊤ with "[//]").
    iModIntro.
    iExists {[ "x" := h ]}.
    iFrame.
    iSplitL "x_h"; first iApply (big_sepM_singleton with "x_h").
    iIntros "!>(Active & mem & cache & _)!>".
    wp_pures.
    iPoseProof (big_sepM_insert with "cache") as "((x_h & x_upd) & _)"; first done.
    wp_apply (SI_read_spec with "[] x_h"); first set_solver.
    iIntros "x_h".
    wp_pures.
    wp_apply ("f_spec" with "P").
    iIntros (v') "Q".
    wp_pures.
    wp_apply (SI_write_spec with "[] [$x_h $x_upd]"); first set_solver.
    iIntros "(x_v' & x_upd)".
    wp_pures.
    wp_apply (commitU_spec _ _ ⊤ with "[//]").
    iModIntro.
    iExists _, _, {[ "x" := (Some (SV_val v'), true) ]}.
    iFrame.
    iSplitL "x_v' x_upd".
    {
      iSplit; first done.
      iSplit; first by rewrite 2!dom_singleton_L.
      iApply big_sepM_singleton.
      iFrame.
    }
    iIntros "!>(CanStart & [(_ & mem) | (%abs & _)])!>".
    {
      iApply ("HΦ" with "[$Q $CanStart mem]").
      by iPoseProof (big_sepM2_insert with "mem") as "((x_v' & _) & _)".
    }
    exfalso.
    apply abs.
    rewrite bool_decide_spec.
    move=>k k_keys.
    by rewrite (elem_of_singleton_1 _ _ k_keys) lookup_singleton bool_decide_true.
  Qed.

















 *)
