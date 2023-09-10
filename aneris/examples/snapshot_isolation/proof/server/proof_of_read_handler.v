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
  Context (γKnownClients γGauth γGsnap γT γTss γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT γTss).
  Import snapshot_isolation_code_api.
  Import assert_proof.

  Lemma kvs_get_spec (k : Key) (kvsV : val)
        (Hh : list write_event)
       (m : gmap Key val) (M : gmap Key (list write_event)) :
   is_map kvsV m →
   M !! k = Some Hh →
   kvsl_in_model_empty_coh m M →
   kvsl_in_model_some_coh m M →
   kvsl_in_local_some_coh m M →
   {{{ ⌜True⌝ }}}
       kvs_get #k kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (vlo : option (list write_event)) (v : val), RET v;
        ⌜match vlo with
         | None =>
             v = NONEV ∧
             Hh = []
         | Some l =>
             v = $l ∧
             m !! k = Some v ∧
             l ≠ [] ∧
             l = reverse Hh
         end⌝
    }}}.
  Proof.
    iIntros (Hmap HMk Hc1 Hc2 Hc3 Φ) "_ HΦ".
    wp_lam.
    wp_pures.
    wp_apply (wp_map_lookup $! Hmap).
    iIntros (v) "%Hkv".
    destruct Hh as [|e h'] eqn:Heq; simplify_eq /=.
    - specialize (Hc1 k HMk).
      destruct (m !! k) as [hv | ] eqn:Hmk; first done.
      simplify_eq /=.
      do 3 wp_pure _.
      wp_pures.
      by iApply ("HΦ" $! None).
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
         by iApply ("HΦ" $! (Some (x :: l))).
  Qed.

  Lemma kvs_get_last_spec (k : Key) (ts : nat) (T : nat) (Tss : gset nat) (kvsV : val)
        (h Hk : list write_event)
       (m : gmap Key val) (M : gmap Key (list write_event)) :
   (∀ e : events.write_event, e ∈ h → we_time e < ts) →
   is_map kvsV m →
   kvsl_valid m M T Tss →
   ts < T →
   M !! k = Some Hk →
   h `prefix_of` Hk →
    {{{
          ownTimeSnap γT γTss ts ∗
          ownMemSeen γGsnap k h ∗
          ownMemSeen γGsnap k Hk
    }}}
        kvs_get_last (#k, #ts)%V kvsV  @[ip_of_address MTC.(MTS_saddr)]
    {{{ (vo : option val), RET $vo;
        (⌜$vo = InjLV #()⌝ ∗ ⌜h = []⌝ ∨
        (∃ e : events.write_event, ⌜$vo = InjRV (we_val e)⌝ ∗
             ⌜hist_to_we h = Some e⌝))
    }}}.
  Proof.
    iIntros (Het Hm Hcoh HtT Hin Hpre Φ) "(#Ht & #Hsh & #HsH) HΦ".
    wp_lam.
    do 15 wp_pures.
    destruct Hcoh.
    wp_smart_apply (kvs_get_spec k kvsV Hk m M Hm Hin); eauto.
    iIntros (vlo v) "%Hvlo".
    iLöb as "IH" forall (v Hk vlo Hin Hpre Hvlo) "HsH".
    destruct vlo as [l | ] eqn: Hvloeq; last first.
    - destruct Hvlo as (-> & ->).
      apply prefix_nil_inv in Hpre.
      subst.
      wp_pures.
      iApply ("HΦ" $! None); eauto.
    - destruct Hvlo as (Hvl & Hmk & Hlneq & HlHk).
      rewrite Hvl HlHk.
      assert (∃ e Hr, reverse Hk = e :: (reverse Hr)) as (e & Hr & HkLast).
      { admit. }
      rewrite HkLast.
      wp_pures.
      case_bool_decide.
      (** should be proven by contradiction: *)
(*            we_time hv.t = ts *)
(*            either hv ∈ h, then hv.t < ts *)
(*            or hv ∉ h but hv ∈ Hk, then ts < hv.t *)
      { admit. }
      wp_pures.
      case_bool_decide.
      { wp_pures.
        iApply ("HΦ" $! (Some (we_val e))).
        iRight.
        iExists e.
        iSplit; first done.
        iPureIntro.
        admit. }
      wp_pure _.
      iApply ("IH" $! ($(reverse Hr)) Hr with "[][][][$HΦ]").
      + admit.
      + admit.
      + admit.
      + admit.
  Admitted.
    (*   iPureIntro. *)
 (*      split. *)
 (*      -- simpl.  *)
 (*      split_and!; eauto. done. *)
 (*    (** --------------------------- old stuff --------------------------- *) *)
 (*    destruct Hget as (Hget & Hdis). *)
 (*    rewrite Hget. *)

 (*    iLöb as "IH". *)
 (*    destruct Hdis as [(Hvgeteq & Hkeq) | (hv &  Hhv & Heq1 & Heq2)]. *)

 (*    - rewrite -Hget Heq1.   *)
 (*      wp_pures. *)
 (*      case_bool_decide. *)
 (*      (** should be proven by contradiction:  *) *)
(*  (*           we_time hv.t = ts  *) *)
(*  (*           either hv ∈ h, then hv.t < ts *) *)
(*  (*           or hv ∉ h but hv ∈ Hk, then ts < hv.t *) *)
 (*      { admit. } *)
 (*      wp_pures. *)
 (*      case_bool_decide. *)
 (*      { wp_pures.  *)
 (*        iApply ("HΦ" $! (Some (we_val hv))). *)
 (*        iRight. *)
 (*        iExists hv. *)
 (*        iSplit; first done. *)
 (*        iPureIntro. *)
 (*        admit. } *)
 (*      wp_pure _.  *)

 (*    (* --------------------------------------------------------------------- *) *)
 (*    iLöb as "IH"forall (Hk Hget Hin Hpre Hdis) "HsH". *)
 (*    destruct Hdis as [(Hvgeteq & Hkeq) | (hv &  Hhv & Heq1 & Heq2)]. *)
 (*    - subst.  *)
 (*      apply prefix_nil_inv in Hpre. *)
 (*      rewrite reverse_nil. *)
 (*      wp_pures. *)
 (*      iApply ("HΦ" $! None); eauto. *)
 (*    - rewrite -Hget Heq1.   *)
 (*      wp_pures. *)
 (*      case_bool_decide. *)
 (*      (** should be proven by contradiction:  *) *)
(*  (*           we_time hv.t = ts  *) *)
(*  (*           either hv ∈ h, then hv.t < ts *) *)
(*  (*           or hv ∉ h but hv ∈ Hk, then ts < hv.t *) *)
 (*      { admit. } *)
 (*      wp_pures. *)
 (*      case_bool_decide. *)
 (*      { wp_pures.  *)
 (*        iApply ("HΦ" $! (Some (we_val hv))). *)
 (*        iRight. *)
 (*        iExists hv. *)
 (*        iSplit; first done. *)
 (*        iPureIntro. *)
 (*        admit. } *)
 (*      wp_pure _.  *)

 (*      assert ($ Hhv = reverse  *)
 (*      iDestruct ("IH" $! . *)
 (* destruct (reverse Hk) as [| e Hkl] eqn: Hkeq; first done. *)
 (*      wp_pures. *)
 (*      case_bool_decide. *)
 (*      (** should be proven by contradiction. *) *)
 (*      { admit. } *)
 (*      wp_pures. *)
 (*      case_bool_decide. *)
 (*      { wp_pures. *)
 (*        iApply ("HΦ" $! (Some (we_val e))). *)
 (*         iRight. *)
 (*         iExists e. *)
 (*         iSplit; first done. *)
 (*         iPureIntro. *)
 (*      -- apply prefix_nil_inv in Hpre. *)
 (*         rewrite reverse_nil. *)
 (*         wp_pures. *)
 (*         iApply ("HΦ" $! None); eauto. *)
 (*      --        list_simplifier. *)
 (*         simpl in Heq1. *)
 (*         inversion Heq1. *)
 (*         rewrite Heq2. *)
 (*         rewrite reverse_involutive. *)
 (*         wp_pures. *)
 (*      case_bool_decide. *)
 (*      (** should be proven by contradiction. *) *)
 (*      { admit. } *)
 (*      wp_pures. *)
 (*      case_bool_decide. *)
 (*      { wp_pures. *)
 (*        iApply ("HΦ" $! (Some (we_val hv))). *)
 (*        iRight. *)
 (*        iPureIntro. *)
 (*        exists hv. *)
 (*        split; first done. *)
 (*        rewrite /hist_to_we. *)
 (*        assert (Some hv = head (hv :: Hhv)) as Hsomehv by done. *)
 (*        rewrite -last_reverse in Hsomehv. *)
 (*        rewrite Hsomehv. *)
 (*        rewrite reverse_cons. *)
 (*        rewrite last_snoc. *)
 (*        assert ((reverse h) `suffix_of` ((hv :: Hhv))) as Hsuf. *)
 (*        { rewrite Heq2 in Hpre. *)
 (*          admit. } *)
 (*        admit. *)
 (*      } *)
 (*      wp_pure _. *)
 (*      (* iApply ("IH" with "[$HΦ]"). *) *)
 (*   Admitted. *)

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
    server_lock_inv γGauth γT γTss γlk lk kvs vnum -∗
    Global_Inv clients γKnownClients γGauth γGsnap γT γTss -∗
    ownTimeSnap γT γTss ts -∗
    ownMemSeen γGsnap k h -∗
    (∀ (repv : val) (repd : RepData),
       ⌜sum_valid_val (option_serialization KVS_serialization)
        (sum_serialization int_serialization bool_serialization) repv⌝ ∗
         ReqPost clients γKnownClients γGauth γGsnap γT γTss repv reqd repd -∗
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
      as (kvsV T Tss m M Hmap Hvalid Hforall)
           "(HmemLoc & HtimeLoc & #Hstarts & HkvsL & HvnumL)".
    wp_load.
    admit.
    (* wp_apply (kvs_get_last_spec); try done. eauto. *)
  Admitted.


End Proof_of_read_handler.
