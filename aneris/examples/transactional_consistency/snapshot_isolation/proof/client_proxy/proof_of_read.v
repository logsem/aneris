From iris.algebra Require Import auth gmap dfrac frac_auth excl csum.
From iris.algebra.lib Require Import mono_list.
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
  user_params time events aux_defs resource_algebras.
From aneris.examples.transactional_consistency.snapshot_isolation.proof
     Require Import utils model kvs_serialization rpc_user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.proof.resources
     Require Import
     server_resources proxy_resources global_invariant wrappers.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.

Section Read_Proof.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (clients : gset socket_address).
  Context (γKnownClients γGauth γGsnap γT γTrs : gname).
  Context (srv_si : message → iProp Σ).
  Notation MTC := (client_handler_rpc_user_params
                     clients γKnownClients γGauth γGsnap γT γTrs).
  Import snapshot_isolation_code_api.


 Definition read_spec_internal `{!MTS_resources} : Prop :=
    ∀ (c : val) (sa : socket_address)
      (k : Key) (vo : option val),
    ⌜k ∈ KVS_keys⌝ -∗
      @make_request_spec _ _ _ _ MTC _ -∗
      {{{ Global_Inv clients γKnownClients γGauth γGsnap γT γTrs ∗
          is_connected γGsnap γT γTrs γKnownClients c sa ∗
        ownCacheUser γKnownClients k c vo }}}
      SI_read c #k @[ip_of_address sa]
    {{{ RET $vo; ownCacheUser γKnownClients k c vo }}}.


 Lemma read_spec_internal_holds `{!MTS_resources} :
   read_spec_internal.
  Proof.
    iIntros (c sa k vo Hk) "#HSpec !#".
    iIntros (Φ) "(#Hinv & #Hisc & Hcache) Hpost".
    iDestruct "Hisc" as (lk cst l) "Hisc".
    iDestruct "Hisc" as (γCst γlk γS γA γCache γMsnap ->) "#(Hc1 & Hisc)". rewrite /make_request_spec.
    rewrite /SI_read /= /read.
    wp_pures.
    wp_apply (acquire_spec (KVS_InvName.@socket_address_to_str sa)
               with "[$Hisc]").
    iIntros (uu) "(_ & Hlk & Hres)".
    wp_pures.
    iDestruct "Hres"
      as (?) "(Hl & Hcr & [( -> & Hres_abs & Hms & Htk) | Hres])".
    { iDestruct "Hcache" as (? ? ? ? ? ? ? ? ? Heq) "Hcache".
      symmetry in Heq. simplify_eq.
      iDestruct "Hcache" as "(#Hc2 & Helem & %Hval)".
      iDestruct (client_connected_agree with "[$Hc2][$Hc1]") as "%Heq'".
      simplify_eq /=.
      by iDestruct (@ghost_map.ghost_map_lookup
                  with "[$Hres_abs][$Helem]")
                  as "%Habs". }
    iDestruct "Hres"
      as (ts Msnap Msnap_full cuL cuV cuM cM -> Hcoh Hser) "Hres".
    iDestruct "Hres" as (Hvalid)
           "(%Hm & %Hsub & #Hts & #Hsn & #Hf & HcM & Hauth & Htk)".
    wp_load.
    wp_pures.
    wp_load.
    wp_apply (wp_map_lookup $! Hm).
    iIntros (vo1 Hvo1).
    assert (is_coherent_cache cuM cM Msnap) as Hcohc by done.
    destruct Hcoh as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & Hc7 & Hc8) .
    iDestruct "Hcache" as (? ? ? ? ? ? ? ? ? Heq)
                            "(#Hc4 & Hcache & %Hvb)".
    simplify_eq /=.
    iDestruct (client_connected_agree with "[$Hc4][$Hc1]") as "%Heq'".
    simplify_eq.
    iDestruct (@ghost_map.ghost_map_lookup with
                "[$Hauth][$Hcache]") as "%Hkin".
    destruct (cuM !! k) eqn:Hkv1.
    (* Read from cache. *)
    1:{ rewrite Hvo1.
        wp_pures.
        specialize (Hc6 k v).
        apply Hc6 in Hkv1.
        simplify_eq /=.
        wp_apply (release_spec with
                   "[$Hisc $Hlk Hl Hcr HcM Hauth Htk] [Hcache Hpost]").
        { iExists _.
          iFrame "#∗".
          iRight.
          iExists ts, Msnap, _, cuL, cuV, cuM, cM.
          by iFrame "#∗". }
        iNext.
        iIntros (v0 ->).
        wp_pures.
        iApply "Hpost".
        iExists _, _, _, _, _, _, _, _.
        iExists _.
        by iFrame "#∗". }
    (* Read from the database. *)
    rewrite Hvo1.
    wp_pures.
    assert (is_Some (Msnap !! k)) as Hsnapk.
    { apply elem_of_dom.
      assert (is_Some (cM !! k)) as Hin. set_solver.
      apply elem_of_dom in Hin. set_solver. }
    destruct Hsnapk as (h & Hinh).
    iAssert (ownMemSeen γGsnap k h)%I as "df".
    { iDestruct (big_sepM_lookup with "[$Hsn]") as "Hsnap"; done. }
    wp_apply ("HSpec" with "[$Hcr]").
    instantiate (1 := (inl (k, ts, h))).
    assert (k ∈ dom cM) as Hdomk.
    { apply elem_of_dom. set_solver. }
    specialize (Hc7 k vo) as (Hd & _).
    {  set_solver. }
    { rewrite Hinh. simplify_eq /=.
      destruct vo eqn:Hvo.
      - simplify_eq /=.
        destruct b.
        -- destruct (Hc6 k v) as (Hc61 & Hc62).
           specialize (Hc62 Hkin). set_solver.
        -- specialize (Hc4 k v Hkin).
           destruct Hc4 as (h0 & e0 & Hmk & Hh & Hev).
           rewrite /hist_to_we in Hh.
           simplify_eq /=.
           rewrite Hh.
           done.
      -  simplify_eq /=.
         specialize (Hc5 k Hkin).
         by simplify_eq /=. }
    specialize (Hd Hkv1).
    specialize (Hvalid k h Hinh).
    (* Handler precondition. *)
    { iSplit.
      - iPureIntro.
        simplify_eq /=.
        eapply sum_is_ser_valid.
        rewrite /sum_is_ser.
        eexists (#k, #ts)%V, _. left.
        split; first eauto.
        simpl. split; last done.
        eexists _, _, _, _.
        split_and!; try done.
        simplify_eq /=.
        eexists _; try done.
      -  rewrite /MTS_handler_pre /= /ReqPre.
         iSplit; first done.
         iLeft.
         iExists k, ts, h, Msnap_full.
         iFrame "#∗".
         iPureIntro; split_and!; try done.
         intros e He. specialize (Hvalid e He). lia.
         specialize (Hsub k).
         rewrite Hinh in Hsub.
         simplify_eq /=.
         destruct (Msnap_full !! k) as [hk|] eqn:Heq;
         by simplify_map_eq /=. }
    (* Getting the reply. *)
    iIntros (repd repv) "[Hreq Hhpost]".
    wp_pures.
    rewrite /MTS_handler_post /= /ReqPost.
    iDestruct "Hhpost" as "(_ & [Hhpost|Habs])".
    -- iDestruct "Hhpost" as
         (? ? ? vo2 Heq1 Heq2 Heq3) "Hhpost".
       symmetry in Heq1, Heq2, Heq3.
       simplify_eq /=.
       wp_pures.
       iDestruct "Hhpost" as "(_ & Hcnd)".
       wp_apply (release_spec with
                  "[$Hisc $Hlk Hl Hreq HcM Hauth Htk] [Hcache Hpost Hcnd]").
       { iExists _.
         iFrame "#∗".
         iRight.
         iExists ts, Msnap, _,  cuL, cuV, cuM, cM.
         by iFrame "#∗". }
       iNext.
       iIntros (? ->).
       wp_pures.
       specialize (Hc7 k vo) as (Hd & _).
       { apply elem_of_dom. set_solver. }
       { rewrite Hinh. simplify_eq /=.
         destruct vo eqn:Hvo.
         - simplify_eq /=.
           destruct b.
           -- destruct (Hc6 k v) as (Hc61 & Hc62).
              specialize (Hc62 Hkin). set_solver.
           -- specialize (Hc4 k v Hkin).
              destruct Hc4 as (h0 & e0 & Hmk & Hh & Hev).
              rewrite /hist_to_we in Hh.
              simplify_eq /=.
              rewrite Hh.
              done.
         -  simplify_eq /=.
            specialize (Hc5 k Hkin).
            by simplify_eq /=. }
       apply Hd in Hkv1.
       iDestruct "Hcnd" as "[(-> & ->) | %Hhe ]".
       (* Case 2 : There is nothing to read. *)
       --- assert (vo = None) as ->.
           by destruct vo; first by specialize (Hc4 k v Hkv1); set_solver.
           iApply "Hpost".
           iExists _, _, _, _, _, _, _, _.
           iExists _.
           iSplit; first done.
           iFrame "#∗".
           eauto.
       (* Case 2 : There is a value to read. *)
       --- destruct Hhe as (rv & -> & Hrv).
           destruct vo as [v|]; last by set_solver.
           { specialize (Hc4 k v Hkv1) as (h' & e & Hmk & Hhe & Hev).
             simplify_eq /=.
             iApply "Hpost".
             iExists _, _, _, _, _, _, _, _.
             iExists _.
             iSplit; first done.
             iFrame "#∗".
             eauto. }
    (* Absurd *)
    -- by iDestruct "Habs"
         as "[(% & % & % & % & % & % & Habs) |
              (% & % & % & % & % & % & % & % & % & Habs)]".
  Qed.

End Read_Proof.
