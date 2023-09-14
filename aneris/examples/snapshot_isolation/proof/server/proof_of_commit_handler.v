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
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.examples.snapshot_isolation.proof
     Require Import time events model kvs_serialization rpc_user_params.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     resource_algebras server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
Section Proof_of_commit_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTss γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT).
  Import snapshot_isolation_code_api.

  Lemma commit_handler_spec
    (lk : val)
    (kvs vnum : loc)
    (reqd : ReqData)
    (Φ : val → iPropI Σ)
    (E : coPset)
    (P : iProp Σ)
    (Q : val → iProp Σ)
    (ts : nat) 
    (cache_updatesM : gmap Key val)
    (cache_logicaM : gmap Key (option val * bool))
    (Msnap : gmap Key (list write_event))
    (cmapV : val)
    (Tss : gset nat) :
    reqd = inr (inr (E, ts, cache_updatesM, cache_logicaM, Msnap, P, Q)) →
    ↑KVS_InvName ⊆ E →
    is_map cmapV cache_updatesM →
    is_coherent_cache cache_updatesM cache_logicaM Msnap →
    kvs_valid_snapshot Msnap ts Tss →
    map_Forall (λ (_ : Key) (v : val), KVS_Serializable v) cache_updatesM →
    server_lock_inv γGauth γT γTss γlk lk kvs vnum -∗
    Global_Inv clients γKnownClients γGauth γGsnap γT γTss -∗
    ownTimeSnap γT γTss ts -∗
    ([∗ map] k↦h' ∈ Msnap, ownMemSeen γGsnap k h') -∗
    P -∗
    (P ={⊤,E}=∗
        ∃ m_current : gmap Key (list val), ⌜dom m_current = dom Msnap⌝ ∗
          ([∗ map] k↦hv ∈ m_current, OwnMemKey_def γGauth γGsnap k hv) ∗
          ▷ (∀ b : bool,
              ⌜b = true⌝ ∗
              ⌜can_commit m_current
                  ((λ h : list write_event, to_hist h) <$> Msnap)
                  cache_logicaM⌝ ∗
              ([∗ map] k↦h;p ∈ m_current;cache_logicaM, 
                OwnMemKey_def γGauth γGsnap k (commit_event p h) ∗
                Seen_def γGsnap k (commit_event p h)) ∨ ⌜
              b = false⌝ ∗
              ⌜¬ can_commit m_current
                    ((λ h : list write_event, to_hist h) <$> Msnap)
                    cache_logicaM⌝ ∗
              ([∗ map] k↦h ∈ m_current, OwnMemKey_def γGauth γGsnap k h ∗
                Seen_def γGsnap k h) ={E,⊤}=∗ Q #b)) -∗
    (∀ (repv : val) (repd : RepData),
         ⌜sum_valid_val (option_serialization KVS_serialization)
            (sum_serialization int_serialization bool_serialization) repv⌝ ∗
         ReqPost clients γKnownClients γGauth γGsnap γT γTss repv reqd repd -∗
         Φ repv) -∗
    WP let: "res" := InjR
                      (InjR 
                        (acquire lk ;; 
                        let: "res" := (λ: <>,
                                        let: "tc" := 
                                        ! #vnum + #1 in
                                        let: "kvs_t" := 
                                        ! #kvs in
                                        let: "ts" := 
                                        Fst (#ts, cmapV)%V in
                                        let: "cache" := 
                                        Snd (#ts, cmapV)%V in
                                        if: list_is_empty "cache" then #true
                                        else let: "b" := 
                                             map_forall
                                               (λ: "k" "_v",
                                                  let: "vlsto" := 
                                                  map_lookup "k" "kvs_t" in
                                                  let: "vs" := 
                                                  if: 
                                                  "vlsto" = InjL #()
                                                  then 
                                                  InjL #()
                                                  else 
                                                  network_util_code.unSOME
                                                    "vlsto" in
                                                  check_at_key "k" "ts" "tc" "vs")
                                               "cache" in
                                             if: "b"
                                             then #vnum <- "tc" ;; 
                                                  #kvs <-
                                                  snapshot_isolation_code.update_kvs
                                                    "kvs_t" "cache" "tc" ;; #true
                                             else #false)%V #() in
                       release lk ;; "res")) in "res" @[
      ip_of_address KVS_address] {{ v, Φ v }}.
  Proof.
  Admitted.

End Proof_of_commit_handler.
