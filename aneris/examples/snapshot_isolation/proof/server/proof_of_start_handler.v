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
Section Proof_of_start_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γlk : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT).
  Import snapshot_isolation_code_api.

  Lemma start_handler_spec
        (lk : val)
        (kvs vnum : loc)
        (reqd : ReqData)
        (Φ : val → iPropI Σ)
        (E : coPset)
        (P : iProp Σ)
        (Q : val → iProp Σ) :
    reqd = inr (inl (E, P, Q)) →
    ↑KVS_InvName ⊆ E →
    server_lock_inv γGauth γT γlk lk kvs vnum -∗
    Global_Inv clients γKnownClients γGauth γGsnap γT -∗
    P -∗
    (P ={⊤,E}=∗
          ∃ m : gmap Key (list val),
            ([∗ map] k↦h ∈ m, OwnMemKey_def γGauth γGsnap k h) ∗
            ▷ (∀ (ts : Time) (M : gmap Key (list write_event)),
                 ⌜m = (λ h : list write_event, to_hist h) <$> M⌝ -∗
                 ⌜kvs_valid_snapshot M ts⌝ ∗ 
                 ⌜map_Forall (λ k l, Forall (λ we, KVS_Serializable (we_val we)) l) M⌝ ∗
                 ownTimeSnap γT ts ∗
                 ([∗ map] k↦h ∈ m, OwnMemKey_def γGauth γGsnap k h) ∗
                 ([∗ map] k↦h ∈ M, ownMemSeen γGsnap k h) ={E,⊤}=∗
                 Q #ts)) -∗
    (∀ (repv : val) (repd : RepData),
           ⌜sum_valid_val (option_serialization KVS_serialization)
              (sum_serialization int_serialization bool_serialization) repv⌝ ∗
           ReqPost clients γKnownClients γGauth γGsnap γT repv reqd repd -∗
           Φ repv) -∗
    WP let: "res" := InjR
                     (InjL
                        (acquire lk ;;
                         let: "res" := (λ: <>,
                                          let: "vnext" :=
                                          ! #vnum + #1 in
                                          #vnum <- "vnext" ;; "vnext")%V #() in
                         release lk ;; "res")) in "res" @[
  ip_of_address KVS_address] {{ v, Φ v }}.
  Proof.
    iIntros (Hreqd HinE) "#Hlk #HGlobInv HP Hsh HΦ".
    wp_pures.
    wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#".
    iIntros (?) "(-> & Hlock & Hlkres)".
    wp_pures.
    iDestruct "Hlkres"
      as (kvsV T m M Hmap Hvalid)
           "(%Hser & HmemLoc & HtimeLoc & HkvsL & HvnumL)".
    wp_load.
    wp_pures.
    (* This is where the viewshift is happening. *)
    wp_bind (Store _ _).
    wp_apply (aneris_wp_atomic _ _ E).
    iMod ("Hsh" with "[$HP]") as (mu) "(Hkeys & Hpost)".
    iInv KVS_InvName
      as (Mg Tg gMg) ">(HmemGlob & HtimeGlob & Hccls & %Hdom & %HkvsValid)".
    (* Logical updates. *)
    rewrite /ownTimeGlobal /ownTimeLocal.
    iDestruct (mono_nat.mono_nat_auth_own_agree with "[$HtimeGlob][$HtimeLoc]")
      as "(%Hleq & ->)".
    iAssert (mono_nat.mono_nat_auth_own γT (1 / 2) T -∗
             mono_nat.mono_nat_auth_own γT (1 / 2) T -∗
             mono_nat.mono_nat_auth_own γT 1 T)%I as "Htime".
    { iIntros "H1 H2".
      by iSplitL "H1". }
    iDestruct ("Htime" with "[$HtimeGlob][$HtimeLoc]") as "HtimeAuth".
    iMod (mono_nat.mono_nat_own_update (T + 1) with "HtimeAuth")
      as "((HtimeGlob & HtimeLoc) & #HtimeSnap)"; first by lia.
    iAssert (⌜M = Mg⌝%I) as "<-".
    { iDestruct "HmemGlob" as "(Hg1 & Hg2)".
      rewrite /ownMemAuthLocal /ownMemAuthGlobal.
      iApply (ghost_map.ghost_map_auth_agree γGauth (1/2)%Qp (1/2)%Qp M
               with "[$HmemLoc][$Hg1]"). }
    iDestruct (big_sepM_split_frac M mu (1/2)%Qp with "HmemLoc") as "HmemLoc".
    iDestruct (big_sepM_sep with "[$Hkeys $HmemLoc]") as "HmemKeys".
    iDestruct (mem_auth_lookup_big _ _ (1/2)%Qp mu M) as "Hkeys_map".
    iDestruct (big_sepM_wand with "[$HmemKeys][$Hkeys_map]") as "Hcln".
    iDestruct (big_sepM_sep with "Hcln") as "(Hkeys & Hcln)".
    iDestruct (big_sepM_sep with "Hcln") as "(HauthFrags & %Hmap_eq)".
    iDestruct (big_sepM_split_frac with "[$HauthFrags]") as "HmemLoc"; try eauto.
    apply map_eq_filter_dom in Hmap_eq.
    iAssert ( [∗ map] k↦h ∈ filter (λ k : Key * list write_event, k.1 ∈ dom mu) M,
                ownMemSeen γGsnap k h)%I as "#Hsnapshot".
    { (** TODO: should be enough to prove using HmemGlob *)
      admit. }
    iSplitL "HtimeGlob HmemGlob Hccls".
    { iModIntro. iNext.
      iExists M, (T+1), gMg.
      iFrame "#∗".
      iSplit; first done.
      iPureIntro.
      apply kvs_valid_next.
    }
    iModIntro.
    iModIntro.
    wp_store.
    iDestruct ("Hpost" $! (T+1)%nat ((filter (λ k, k.1 ∈ dom mu) M))
                with "[][Hkeys]") as "HQ"; first done.
    iFrame "#∗".
    iPureIntro.
    split; first by apply kvs_valid_snapshot_filter_next.
    {
      apply map_Forall_lookup_2.
      intros k x H_filter_some.
      apply map_filter_lookup_Some_1_1 in H_filter_some.
      by apply Hser in H_filter_some.
    }
    iMod "HQ".
    iModIntro.
    wp_pures.
    wp_smart_apply (release_spec with "[-HQ HΦ]").
    iFrame "#∗".
    { rewrite /lkResDef.
      iExists  kvsV, ((T+1)%nat), m, M.
      replace (Z.of_nat T + 1)%Z with (Z.of_nat (T + 1)) by lia.
      iFrame "#∗".
      iSplit; first done.
      iSplit; last done.
      iPureIntro; first apply kvsl_valid_next. }
    iIntros (? ->).
    wp_pures.
    iApply ("HΦ" $! _ _).
    iSplit.
    -- iPureIntro. by apply ser_start_reply_valid.
    -- rewrite /ReqPost.
       iFrame "#".
       iRight.
       iLeft.
       iExists E, P, Q, (T+1), (filter (λ k : Key * list write_event, k.1 ∈ dom mu) M).
       iFrame "#∗".
       iPureIntro.
       split_and!; eauto.
       replace (Z.of_nat T + 1)%Z with (Z.of_nat (T + 1)) by lia.
       done.
  Admitted.

End Proof_of_start_handler.
