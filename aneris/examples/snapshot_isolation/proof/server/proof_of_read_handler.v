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

Section Proof_of_read_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT).
  Import snapshot_isolation_code_api.



  Lemma kvs_get_spec (k : Key) (kvsV : val) (h : list write_event)
       (m : gmap Key val) :
   is_map kvsV m →
   {{{ ownMemSeen γGsnap k h }}}
       kvs_get #k kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (h : list write_event), RET $h;
        (⌜$h = InjLV #()⌝ ∗ ⌜h = []⌝) ∨ 
        (∃ hv : list val, ⌜hv = to_hist h⌝)
    }}}.
  Proof.
  Admitted.

  Lemma kvs_get_last_spec (k : Key) (ts : nat) (T : nat) (kvsV : val) (h : list write_event)
       (m : gmap Key val) (M : gmap Key (list write_event)) :
   (∀ e : events.write_event, e ∈ h → we_time e < ts) →
   (∀ e : events.write_event, e ∈ h → we_time e < ts) →
   is_map kvsV m →
   kvsl_valid m M T →
   ts < T →
    {{{
          ownTimeSnap γT ts ∗
          ownMemSeen γGsnap k h
    }}}
        kvs_get_last (#k, #ts)%V kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (vo : option val), RET $vo;
        (⌜$vo = InjLV #()⌝ ∗ ⌜h = []⌝ ∨
        (∃ e : events.write_event, ⌜$vo = InjRV (we_val e)⌝ ∗
             ⌜hist_to_we h = Some e⌝))
    }}}.
  Proof.
  Admitted.

  Lemma read_handler_spec
        (k : string)
        (lk : val)
        (kvs vnum : loc)
        (reqd : ReqData)
        (ts : nat)
        (h : list write_event)
        (Φ : val → iPropI Σ) :
    k ∈ KVS_keys →
    reqd = inl (k, ts, h) →
    (∀ e : events.write_event, e ∈ h → we_time e < ts) →
    server_lock_inv γGauth γT γlk lk kvs vnum -∗
    Global_Inv clients γKnownClients γGauth γGsnap γT -∗
    ownTimeSnap γT ts -∗
    ownMemSeen γGsnap k h -∗
    (∀ (repv : val) (repd : RepData),
       ⌜sum_valid_val (option_serialization KVS_serialization)
        (sum_serialization int_serialization bool_serialization) repv⌝ ∗
         ReqPost clients γKnownClients γGauth γGsnap γT repv reqd repd -∗
           Φ repv) -∗
    WP let: "res" := InjL
                     (acquire lk ;;
                      let: "res" := (λ: <>, kvs_get_last (#k, #ts)%V ! #kvs)%V
                                      #() in release lk ;; "res") in "res" @[
  ip_of_address KVS_address] {{ v, Φ v }}.
  Proof.
    iIntros (Hin Hreqd Hts) "#Hlk #HGlobInv #HsnapT #HsnapH HΦ".
    wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#".
    iIntros (?) "(-> & Hlock & Hlkres)".
    wp_pures.
    iDestruct "Hlkres"
      as (kvsV T m M Hmap Hvalid)
           "(HmemLoc & HtimeLoc & HkvsL & HvnumL)".
    wp_load.
    wp_lam.
    wp_pures.
    (* wp_apply (kvs_get_last_spec); try done. eauto. *)
  Admitted.


End Proof_of_read_handler.
