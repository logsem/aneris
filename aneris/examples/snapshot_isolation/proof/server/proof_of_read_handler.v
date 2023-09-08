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
  Import assert_proof.

  Lemma kvs_get_spec (k : Key) (kvsV : val) (h : list write_event)
       (m : gmap Key val) (M : gmap Key (list write_event)) :
   is_map kvsV m →
   M !! k = Some h →
   kvsl_in_model_empty_coh m M →
   kvsl_in_model_some_coh m M →
   kvsl_in_local_some_coh m M →
   {{{ ⌜True⌝ }}}
       kvs_get #k kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ v, RET v; ⌜v = $(reverse h)⌝ ∧
                 ((⌜v = InjLV #()⌝ ∗ ⌜h = []⌝) ∨
                  (∃ e h', ⌜v = InjRV ($e, $h')⌝ ∗ ⌜h = (reverse (e :: h'))⌝))
    }}}.
  Proof.
    iIntros (Hmap HMk Hc1 Hc2 Hc3 Φ) "_ HΦ".
    wp_lam.
    wp_pures.
    wp_apply (wp_map_lookup $! Hmap).
    iIntros (v) "%Hkv".
    destruct h as [|e h'] eqn:Hh; simplify_eq /=.
    - specialize (Hc1 k HMk).
      destruct (m !! k) as [hv | ] eqn:Hmk; first done.
      simplify_eq /=.
      do 3 wp_pure _.
      wp_pures.
      by iApply ("HΦ"); eauto.
    - destruct (m !! k) as [hv | ] eqn:Hmk.
      2: { specialize (Hc2 k (e :: h') HMk).
           naive_solver. }
      assert (m !! k = Some $ (reverse (e :: h'))) as Hmk'.
      { by apply (Hc2 k (e :: h') HMk). }
      simplify_eq /=.
      specialize (Hc3 k (reverse (e :: h')) Hmk).
      do 3 wp_pure _.
      wp_smart_apply wp_assert.
      wp_pures.
      destruct ((reverse (e :: h'))) as [| x l] eqn:Hrev.
      -- rewrite reverse_nil in Hc3.
         by rewrite HMk in Hc3.
      -- wp_pures.
         iSplit; first done.
         iNext.
         wp_pures.
         iApply "HΦ".
         iSplit; first done.
         iRight.
         iExists _, _.
         iPureIntro.
         split; first done.
         apply Inj_instance_2.
         rewrite Hrev.
         by rewrite reverse_involutive.
  Qed.

  Lemma kvs_get_last_spec (k : Key) (ts : nat) (T : nat) (kvsV : val)
        (h Hk : list write_event)
       (m : gmap Key val) (M : gmap Key (list write_event)) :
   (∀ e : events.write_event, e ∈ h → we_time e < ts) →
   is_map kvsV m →
   kvsl_valid m M T →
   ts < T →
   M !! k = Some Hk →
   h `prefix_of` Hk →
    {{{
          ownTimeSnap γT ts ∗
          ownMemSeen γGsnap k h ∗
          ownMemSeen γGsnap k Hk
    }}}
        kvs_get_last (#k, #ts)%V kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (vo : option val), RET $vo;
        (⌜$vo = InjLV #()⌝ ∗ ⌜h = []⌝ ∨
        (∃ e : events.write_event, ⌜$vo = InjRV (we_val e)⌝ ∗
             ⌜hist_to_we (reverse h) = Some e⌝))
    }}}.
  Proof.
    iIntros (Het Hm Hcoh HtT Hin Hpre Φ) "(#Ht & #Hsh & #HsH) HΦ".
    wp_lam.
    wp_pures.
    destruct Hcoh.
    wp_smart_apply (kvs_get_spec k kvsV Hk m M Hm Hin ); eauto.
    iIntros (vget Hget).
    destruct Hget as (Hget & [(<- & ->) | (hv &  Hhv & Heq1 & Heq2)]).
    - apply prefix_nil_inv in Hpre.
      rewrite Hget.
      rewrite reverse_nil.
      wp_pures.
      iApply ("HΦ" $! None); eauto.
    - rewrite Heq1.
      iLöb as "IH".
      wp_pures.
      case_bool_decide.
      (** should be proven by contradiction. *)
      { admit. }
      wp_pures.
      case_bool_decide.
      { wp_pures.
        iApply ("HΦ" $! (Some (we_val hv))).
        iRight.
        iPureIntro.
        exists hv.
        split; first done.
        assert (Some hv = last (reverse (hv :: Hhv))) as HvkL.
        { assert (Some hv = head (hv :: Hhv)) as ->. done.
          by rewrite last_reverse. }
        rewrite /hist_to_we.
        rewrite HvkL.
        assert ((reverse h) `suffix_of` (reverse (hv :: Hhv))) as Hsuf.
        { rewrite Heq2 in Hpre.
          admit. }
        admit.
      }
      wp_pure _.
      (* iApply ("IH" with "[$HΦ]"). *)
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
      as (kvsV T m M Hmap Hvalid Hforall)
           "(HmemLoc & HtimeLoc & HkvsL & HvnumL)".
    wp_load.
    admit.
    (* wp_apply (kvs_get_last_spec); try done. eauto. *)
  Admitted.


End Proof_of_read_handler.
