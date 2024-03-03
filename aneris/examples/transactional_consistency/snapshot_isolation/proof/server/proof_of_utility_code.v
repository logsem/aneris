From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list dfrac_agree.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Import lang resources inject tactics proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params mt_server_code.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.transactional_consistency.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events aux_defs resource_algebras.
From aneris.examples.transactional_consistency Require Import user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof
     Require Import utils model kvs_serialization rpc_user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Section Proof_of_utility_code.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT γTrs).
  Import code_api.
  Import assert_proof.

  Lemma kvs_get_spec_some (k : Key) (kvsV : val) (h : whist)
       (m : gmap Key val) (M : global_mem) :
   is_map kvsV m →
   M !! k = Some h →
   kvsl_in_model_empty_coh m M →
   kvsl_in_model_some_coh m M →
   kvsl_in_local_some_coh m M →
   {{{ ⌜True⌝ }}}
       kvs_get #k kvsV  @[ip_of_address MTC.(MTS_saddr)]
   {{{ (v : val), RET v; ⌜v = $ (reverse h)⌝ }}}.
  Proof.
    iIntros (Hmap HMk Hc1 Hc2 Hc3 Φ) "_ HΦ".
    wp_lam. wp_pures. wp_apply (wp_map_lookup $! Hmap).
    iIntros (v) "%Hkv".
    destruct h as [|e h'] eqn:Heq; simplify_eq /=.
    - specialize (Hc1 k HMk).
      destruct (m !! k) as [hv | ] eqn:Hmk; first done.
      simplify_eq /=. do 3 wp_pure _. wp_pures.
      by iApply "HΦ".
    - destruct (m !! k) as [hv | ] eqn:Hmk.
      2: { specialize (Hc2 k (e :: h') HMk). naive_solver. }
      assert (m !! k = Some $ (reverse (e :: h'))) as Hmk'.
      { by apply (Hc2 k (e :: h') HMk). }
      simplify_eq /=. specialize (Hc3 k (reverse (e :: h')) Hmk).
      do 3 wp_pure _. wp_smart_apply wp_assert. wp_pures.
      destruct ((reverse (e :: h'))) as [| x l] eqn:Hrev.
      -- rewrite reverse_nil in Hc3.
         by rewrite HMk in Hc3.
      -- wp_pures. iSplit; first done. iNext. wp_pures.
         by iApply "HΦ".
  Qed.

  Lemma kvs_get_spec_none (k : Key) (kvsV : val)
      (m : gmap Key val) (M : global_mem) :
    is_map kvsV m →
    M !! k = None →
    kvsl_dom m ->
    kvs_dom M ->
    {{{ ⌜True⌝ }}}
        kvs_get #k kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (v : val), RET v; ⌜v = $ []⌝ }}}.
  Proof.
    iIntros (Hmap HMk Hc1 Hc2 Φ) "_ HΦ".
    wp_lam. wp_pures. wp_apply (wp_map_lookup $! Hmap).
    iIntros (v) "%Hkv".
    destruct (m !! k) as [hv | ] eqn:Hmk.
    - rewrite -not_elem_of_dom in HMk.
      assert (is_Some (m !! k)) as Hsome; first by rewrite Hmk.
      rewrite -elem_of_dom in Hsome.
      set_solver.
    - simplify_eq.
      wp_pures.
      by iApply "HΦ".
  Qed.

End Proof_of_utility_code.
