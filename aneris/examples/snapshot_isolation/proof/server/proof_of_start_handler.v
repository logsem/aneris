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
From aneris.examples.snapshot_isolation.specs Require Import
  user_params time events aux_defs resource_algebras.
From aneris.examples.snapshot_isolation.proof
     Require Import utils model kvs_serialization rpc_user_params.
From aneris.examples.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources
     global_invariant local_invariant wrappers.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
Section Proof_of_start_handler.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs γlk : gname).
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
    Global_Inv clients γKnownClients γGauth γGsnap γT γTrs -∗
    P -∗
    (P ={⊤,E}=∗
          ∃ m : gmap Key (list val),
            ([∗ map] k↦h ∈ m, OwnMemKey_def γGauth γGsnap k h) ∗
              ▷ (∀ (ts : Time) (Msnap Msnap_full : gmap Key (list write_event)),
                 ⌜Msnap ⊆ Msnap_full⌝ ∗
                 ⌜m = (λ h : list write_event, to_hist h) <$> Msnap⌝ ∗
                 ⌜kvs_valid_snapshot Msnap ts⌝ ∗
                 ⌜map_Forall (λ k l, Forall (λ we, KVS_Serializable (we_val we)) l) Msnap⌝ ∗
                 ownTimeSnap γT ts ∗
                 ownSnapFrag γTrs ts Msnap_full ∗
                 ([∗ map] k↦h ∈ m, OwnMemKey_def γGauth γGsnap k h) ∗
                 ([∗ map] k↦h ∈ Msnap, ownMemSeen γGsnap k h) ={E,⊤}=∗
                 Q #ts)) -∗
    (∀ (repv : val) (repd : RepData),
           ⌜sum_valid_val (option_serialization KVS_serialization)
              (sum_serialization int_serialization bool_serialization) repv⌝ ∗
           ReqPost clients γKnownClients γGauth γGsnap γT γTrs repv reqd repd -∗
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
    wp_pures. wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#".
    iIntros (?) "(-> & Hlock & Hlkres)". wp_pures.
    iDestruct "Hlkres"
      as (M S T m kvsV Hmap Hvalid)
           "(%Hser & HmemLoc & HtimeLoc & HkvsL & HvnumL)".
    wp_load. wp_pures.
    (* This is where the viewshift is happening. *)
    wp_bind (Store _ _).
    wp_apply (aneris_wp_atomic _ _ E).
    iMod ("Hsh" with "[$HP]") as (mu) "(Hkeys & Hpost)".
    iInv KVS_InvName
      as (Mg Sg Tg gMg) ">(HmemGlob & HsnapG & HtimeGlob & Hccls & %Hdom & %HkvsValid)".
    (* Logical updates. *)
    rewrite /ownTimeGlobal /ownTimeLocal.
    iDestruct (mono_nat.mono_nat_auth_own_agree with "[$HtimeGlob][$HtimeLoc]")
      as "(%_ & ->)".
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
    iDestruct (mem_auth_lookup_big with "[$HmemLoc] [$Hkeys]")
      as "(HmemLoc & Hkeys & %Hmap_eq)".
    apply map_eq_filter_dom in Hmap_eq.
    iAssert ( [∗ map] k↦h ∈ filter (λ k : Key * list write_event, k.1 ∈ dom mu) M,
                ownMemSeen γGsnap k h)%I as "#Hsnapshot".
    { iDestruct (mem_auth_lookup_big_some with "[$HmemLoc] [$Hkeys]")
      as "(HmemLoc & Hkeys)".
      Unshelve.
      all : try done.
      iApply big_sepM_filter.
      rewrite Hmap_eq.
      iDestruct (big_sepM_fmap (λ h : list write_event, to_hist h) with "Hkeys" ) as "Hkeys".
      iDestruct (big_sepM_filter with "Hkeys" ) as "Hkeys".
      iApply (big_sepM_mono with "Hkeys").
      iIntros (k hwe H_lookup) "H_key_def H_dom".
      rewrite -Hmap_eq.
      iSpecialize ("H_key_def" with "H_dom").
      iDestruct "H_key_def" as "[%hwe' ((_ & Hseen) & _ & %H_lookup')]".
      by simplify_map_eq /=. }
    iMod (own_update
            _ _ (● (((λ M, to_agree (global_memUR M)) <$> (<[(T + 1)%nat :=M]> Sg)) : gmap _ _) ⋅
                 ◯ ({[(T + 1)%nat := to_agree (global_memUR M) ]}))
      with "HsnapG") as "(HsnapG & #HsnapFrag)".
    { 
      apply auth_update_alloc.
      simplify_eq /=.
      rewrite fmap_insert.
      eapply alloc_local_update; last done.
      rewrite lookup_fmap.
      destruct (Sg !! (T + 1)%nat) as [Mx|] eqn:Hsg; last by rewrite Hsg.
      assert (is_Some (Sg !! (T+1)%nat)) as Habs by naive_solver.
      apply elem_of_dom in Habs.
      destruct HkvsValid.
      specialize (kvs_ValidSnapshotTimesTime (T+1)%nat Habs). 
      by lia. }
    iSplitL "HtimeGlob HmemGlob Hccls HsnapG".
     { iModIntro. iNext. iExists M, (<[(T + 1)%nat:=M]> Sg), (T+1)%nat, _.
      iFrame "#∗". iSplit; first done. iPureIntro.
      by apply kvs_valid_step_start_transaction. }
     do 2 iModIntro. wp_store.
     iDestruct ("Hpost" $! (T+1)%nat ((filter (λ k, k.1 ∈ dom mu) M)) M
                 with "[Hkeys]") as "HQ".
     { iFrame "#∗".
       iSplit; first by iPureIntro; apply map_filter_subseteq. 
       iSplit; first done.
       iPureIntro.
       split.
       - intros k h H_lookup e H_e_in_h.
         apply map_filter_lookup_Some_1_1 in H_lookup.
         assert ((we_time e ≤ T)%Z); first by eapply kvs_ValidCommitTimes. lia.
       - apply map_Forall_lookup_2.
         intros k x H_filter_some.
         apply map_filter_lookup_Some_1_1 in H_filter_some.
         by apply Hser in H_filter_some. }
    iMod "HQ".
    iModIntro.
    wp_pures.
    wp_smart_apply (release_spec with "[-HQ HΦ]").
    iFrame "#∗".
    { rewrite /lkResDef.
      iExists  M, _, ((T+1)%nat), m, kvsV.
      replace (Z.of_nat T + 1)%Z with (Z.of_nat (T + 1)) by lia.
      iFrame "#∗".
      iSplit; first done.
      iSplit; last done.
      iPureIntro; first by apply kvsl_valid_next. }
    iIntros (? ->).
    wp_pures.
    iApply ("HΦ" $! _ _).
    iSplit.
    -- iPureIntro. by apply ser_start_reply_valid.
    -- rewrite /ReqPost.
       iFrame "#". iRight. iLeft.
       iExists E, P, Q, (T+1)%nat, (filter (λ k : Key * list write_event, k.1 ∈ dom mu) M).
       iFrame "#∗".
       iPureIntro.
       split_and!; eauto.
       replace (Z.of_nat T + 1)%Z with (Z.of_nat (T + 1)) by lia.
       done.
  Qed.

End Proof_of_start_handler.
