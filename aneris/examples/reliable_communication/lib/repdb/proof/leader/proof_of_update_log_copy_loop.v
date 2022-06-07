From iris.algebra.lib Require Import mono_list.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code model.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events resources.
From aneris.examples.reliable_communication.lib.repdb.resources
     Require Import
     ras log_resources resources_def
     resources_global_inv resources_local_inv.
From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import
     repdb_serialization log_proof.
From aneris.examples.reliable_communication.lib.repdb.proof.leader
     Require Import
     clients_mt_user_params.

Import log_proof.

Section UpdateLogCopy_Proof.
  Context `{!anerisG Mdl Σ, dbparams : !DB_params, !IDBG Σ}.
  Context (γL γM : gname).

  Definition own_replog_loop γ l : iProp Σ :=
    known_replog_token DB_addrF γ ∗ own_logL_obs γL l ∗ own_log_auth γ (1/4) l.

  Lemma update_log_copy_loop_spec
    (γF mFγ mCγ : gname) (kvsL logCL logFL : loc) (mvC mvF : val) :
    {{{ leader_local_main_inv γL kvsL logCL mCγ mvC ∗
       leader_local_secondary_inv γL logFL γF mFγ mvF ∗
       own_replog_loop γF []
    }}}
      update_log_copy_loop #logCL mvC #logFL mvF #() @[ip_of_address DB_addr]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#HinvL & #HinvF & Hloop) HΦ".
    rewrite /update_log_copy_loop.
    do 12 wp_pure _.
    (* pose (@nil_length) as Hnl. *)
    replace 0%Z with (Z.of_nat 0%nat); last done.
    iAssert (⌜0%nat = List.length (@nil write_eventO)⌝)%I as "Hlen".
    { done. }
    iRevert "Hlen".
    generalize 0%nat at 1 2 as m.
    generalize (@nil write_eventO) as l.
    iIntros (lF n Hlen).
    iLöb as "IH" forall (lF n Hlen) "Hloop".
    wp_pures.
    wp_apply (monitor_acquire_spec with "[HinvL]"); first by iFrame "#".
    iIntros (v) "( -> & Hlocked & Hres)".
    wp_pures.
    iDestruct "Hres" as (logV logM) "(Hlog & Hpl & HmainLog & HmainRes)".
    wp_apply (wp_log_wait_until
               with "[$HinvL $Hlocked $Hpl $HmainLog $Hlog $HmainRes][]").
    admit.
    iNext.
    iIntros (logV' logM').
    iIntros "(%Hlen' & %Hlog' & Hlocked & HmainRes & Hpl & HmainLog)".
    wp_pures.
    wp_load.
    wp_pures.
  Admitted.

End UpdateLogCopy_Proof.
