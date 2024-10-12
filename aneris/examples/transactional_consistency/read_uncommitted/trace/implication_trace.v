From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency Require Import code_api wrapped_library.
From aneris.examples.transactional_consistency.read_uncommitted.specs Require Import specs resources.
From aneris.examples.transactional_consistency 
  Require Import resource_algebras user_params aux_defs state_based_model implication_trace_util.

Section trace_proof.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params}.

  (** Wrapped resources *)

  Global Program Instance wrapped_resources (γmstate γmlin γmpost γmname γl : gname) (clients : gset socket_address) 
  `(res : !RU_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_ru ∗ 
                    inv KVS_InvName (∃ T, GlobalInvExt commit_test_ru T extract γmstate γmlin γmpost γmname γl clients))%I;
      OwnMemKey k V := (OwnMemKey k V  ∗ (∀ v, ⌜v ∈ V⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
                        ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗ ∃ (sa : socket_address) γ, ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
                             ⌜extract c = Some #sa⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ ⌜sa ∈ clients⌝)%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ ghost_map_elem γmstate sa (DfracOwn 1%Qp) (s, Some c))%I; 
      IsConnected c sa := (IsConnected c sa ∗ ⌜sa ∈ clients⌝ ∗ ⌜extract c = Some #sa⌝ ∗ 
                           ∃ γ, ghost_map_elem γmname sa DfracDiscarded (γ, c))%I;
      KVS_ru := KVS_ru;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ ghost_map_elem γmstate sa (DfracOwn 1%Qp) (CanStart, None) ∗ ⌜sa ∈ clients⌝)%I;
      Seen k V := Seen k V%I;
      extract c := res.(read_uncommitted.specs.resources.extract) c;
    |}.
  Next Obligation.
    iIntros (??????????) "(Hkey & [%sa [%γ (Hghost_elem_per & %Hextract & Hghost_elem  & %Hin_sa)]])".
    iDestruct (res.(read_uncommitted.specs.resources.OwnLocalKey_serializable) 
      with "Hkey") as "(Hkey & Hser)".
    iFrame.
    iExists sa, γ.
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (????????????) "#(HGinv & Hinv) (#Hseen & Hkey & Hin)".
    iMod (res.(read_uncommitted.specs.resources.Seen_valid) 
      with "[$HGinv][$Hseen $Hkey]") as "(Hkey & Hsub)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    iIntros (???????????) "#(HGinv & Hinv) (Hkey & Hin)".
    iMod (res.(read_uncommitted.specs.resources.Seen_creation) 
      with "[$HGinv][$Hkey]") as "(Hkey & #Hseen)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    simpl.
    iIntros (????? clients res sa c) "(Hconn & _)".
    iApply (res.(read_uncommitted.specs.resources.Extraction_of_address) 
      with "[$Hconn]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (????? clients res sa sa' c c' Heq1 Heq2 Hneq).
    by eapply res.(read_uncommitted.specs.resources.Extraction_preservation).
  Qed.

  (** Per operation implications *)

  Lemma init_client_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (∃ T, GlobalInvExt commit_test_ru T extract γmstate γmlin γmpost γmname γl clients) -∗
    @init_client_proxy_spec _ _ _ _ lib res -∗
    @init_client_proxy_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hinit_cli".
    rewrite /init_client_proxy_spec.
    iIntros (sa Φ) "!# (Hunall & Hsock & Hmes & (Hcan & (Hsa_pointer & %Hsa_in)) & Hfree) HΦ".
    rewrite /TC_init_client_proxy /KVS_wrapped_api /wrap_init_client_proxy.
    wp_pures.
    wp_bind (ast.Fresh _).
    iInv "HinvExt" as ">[%T [%t [%lt [%exec (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex 
      & %Hvalid_trans & %Hvalid_seq & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]]]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_in_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    rewrite /init_pre_emit_event.
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, init_pre_emit_event)%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, init_pre_emit_event)%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Htr_is HOwnLin Hlin_res Hpost_res Hstate_res]").
    {
      iNext.
      iExists T, (t ++ [(#tag1, init_pre_emit_event)%V]), lt, exec.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_in_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply ("Hinit_cli" $! sa with "[$Hunall $Hsock $Hmes $Hcan $Hfree]").
    iIntros (c) "(Hconn_state & #His_conn)".
    wp_pures.
    wp_bind (ast.Emit _).
    rewrite /init_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T' [%t' [%lt' [%exec' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & %Hbased' & %Hvalid_exec' & Hstate_res' & Hlin_res' & Hpost_res')]]]]" "Hclose'".
    iMod (own_lin_add _ _ (#tag1, (c, #"InLin"))%V with "[$HOwnLin']") as "HOwnLin'".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, #"InPre")%V ∈ t') as Hin'.
    {
      apply (elem_of_prefix (t ++ [(#tag1, #"InPre")%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, #"InLin"))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "Hstate_res'" as "[%mstate (Hghost_map_mstate & [%mname (Hghost_map_mname & Hext_rest1')])]".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mstate][$Hsa_pointer]") as "%Hlookup".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {4} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hext_rest1'" as "(Hext_rest1_sa & Hext_rest1)".
    rewrite big_sepS_singleton.
    iAssert ((⌜mname !! sa = None⌝ ∧ ⌜no_emit_with_address sa lt' extract⌝)%I) as "(%Hlookup_none & %Hno_emit)".
    {
      iDestruct ("Hext_rest1_sa") as "[(_ & %Hnot_lookup & %Hno_emit)|[%s [%c' [%γ [%m (%Hfalse & asd)]]]]]".
      - iPureIntro. 
        destruct (mname !! sa) as [γ|] eqn:Hfalse; last done.
        exfalso.
        apply Hnot_lookup.
        by exists γ.
      - set_solver.
    }
    iDestruct (res.(read_uncommitted.specs.resources.Extraction_of_address) 
          with "[$His_conn]") as "%Hextract".
    assert (lin_trace_of (lt' ++ [(#tag1, (c, #"InLin"))%V])
      (t' ++ [(#tag1, (c, #"InPost"))%V])) as Hlin_trace'.
    {
      apply (lin_trace_valid tag1); try done.
      - right.
        split.
        + do 4 right. 
          rewrite /is_in_post_event; eauto.
        + exists (#tag1, (c, #"InLin"))%V.
          set_solver.
      - apply (lin_trace_lin lt' (#tag1, #"InPre")%V 
          (#tag1, (c, #"InLin"))%V tag1 c t'); try done;
          rewrite /is_lin_event /is_in_lin_event /is_pre_event /is_in_pre_event;
          set_solver.
    }
    assert (valid_sequence (lt' ++ [(#tag1, (c, #"InLin"))%V])) as Hvalid_seq''.
    {
      apply valid_sequence_in_lin; try done.
      eapply unique_init_events_add_init; try done.
      rewrite /valid_sequence in Hvalid_seq'; set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      rewrite /valid_trace_ru /valid_trace.
      exists (lt' ++ [(#tag1, (c, #"InLin"))%V]).
      split_and!; try done.
      eexists T', exec'.
      split_and!; try done.
      apply extraction_of_add_init_lin; rewrite /is_in_lin_event;
        set_solver.
    }
    iIntros "Htr_is".
    iDestruct (lin_tag_add_post (lt' ++ [(#tag1, (c, #"InLin"))%V]) t' γmlin (#tag1, (c, #"InPost"))%V 
      with "[$Hlin_res']") as "Hlin_res'".
    iDestruct (post_tag_add t' γmpost (#tag1, (c, #"InPost"))%V tag1 with "[$Hpost_res' $Hpost_tag_res]")
      as "Hpost_res'".
    {
      iPureIntro.
      simpl.
      split; first done.
      do 4 right.
      rewrite /is_in_post_event.
      by eexists _, _.
    }
    iMod (ghost_map_alloc ((gset_to_gmap None KVS_keys : gmap Key (option val))))
      as "[%γ (Hghost_map_m & Hghost_elems_m)]".
    iMod (ghost_map_update (CanStart, Some c) with "[$Hghost_map_mstate] [$Hsa_pointer]") 
      as "(Hghost_map_mstate & Hsa_pointer)".
    iMod (ghost_map_insert_persist sa (γ, c) Hlookup_none with "[$Hghost_map_mname]") 
      as "(Hghost_map_mname & #Hkey_pers_mname)".
    iMod ("Hclose'" with "[Htr_is HOwnLin' Hghost_map_mname Hext_rest1 Hext_rest1_sa 
      Hghost_map_mstate Hghost_map_m Hghost_elems_m Hlin_res' Hpost_res']").
    {
      iNext.
      iExists T', (t' ++ [(#tag1, (c, #"InPost"))%V]), 
        (lt' ++ [(#tag1, (c, #"InLin"))%V]), exec'.
      iFrame.
      do 2 (iSplit; first by iPureIntro).
      iSplit; first iPureIntro.
      {
        apply extraction_of_add_init_lin; rewrite /is_in_lin_event;
        set_solver.
      }
      do 4 (iSplit; first by iPureIntro).
      iClear "HinvExt Hinit_cli Htr_inv".
      iExists (<[sa:=(CanStart, Some c)]> mstate).
      iFrame.
      iExists (<[sa:=(γ, c)]> mname).
      iFrame.
      rewrite {2} Heq_sa_clients.
      rewrite big_sepS_union; last set_solver.
      iSplitL "Hghost_map_m Hghost_elems_m".
      + iApply big_sepS_singleton.
        iRight.
        iExists CanStart, c, γ, (gset_to_gmap None KVS_keys).
        rewrite lookup_insert.
        iFrame "#∗".
        do 2 (iSplit; first by iPureIntro).
        iSplit.
        {
          iPureIntro.
          exists (#tag1, (c, #"InLin"))%V.
          simpl.
          rewrite /is_in_lin_event.
          split_and!; try done; eauto.
          apply elem_of_app.
          right.
          set_solver.
        }
        iLeft.
        iSplit; first by iPureIntro.
        iSplit.
        * iPureIntro.
          rewrite /commit_closed.
          intros e_st Hin Hconn Hstart.
          exfalso.
          apply Hno_emit.
          assert (e_st ∈ lt') as Hin_st; last set_solver.
          rewrite elem_of_app in Hin.
          destruct Hin as [Hin|Hin]; first done.
          rewrite /is_st_lin_event in Hstart.
          set_solver.
        * iSplit. 
          -- iPureIntro. 
             intros (trans & (op & Ht'_in & Hlast & Hconn_last & _)).
             destruct Hex' as (_ & Hex' & _).
             apply last_Some_elem_of in Hlast.
             specialize (Hex' trans op Ht'_in Hlast).
             apply Hno_emit.
             exists (toLinEvent op), c.
             split_and!; try done.
             destruct op; destruct s; 
              simpl in Hconn_last; subst; 
              simpl; try done.
              by destruct ov.
          -- rewrite big_sepM_gset_to_gmap.
             iApply (big_sepS_wand with "[$Hghost_elems_m]").
             iApply big_sepS_intro.
             iModIntro.
             iIntros (k Hk_in) "Hkey".
             iExists None.
             iFrame.
      + iApply (big_sepS_wand with "[$Hext_rest1]").
        iApply big_sepS_intro.
        iModIntro.
        iIntros (sa' Hsa'_in) "Hext_res".
        iApply (client_trace_state_resources_neq3 sa sa' c with "[][][][$]"); try done.
        iPureIntro; set_solver.
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    rewrite /ConnectionState.
    simpl.
    iFrame "∗#".
    do 2 (iSplit; first by iPureIntro).
    iExists γ.
    iFrame "#".
 Qed.

  Lemma read_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (∃ T, GlobalInvExt commit_test_ru T extract γmstate γmlin γmpost γmname γl clients) -∗
    @read_spec _ _ _ _ lib res -∗
    @read_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hread".
    rewrite /read_spec.
    iModIntro.
    iIntros (c sa E k) "%Hsub %Hin (#Hconn & %Hsa_in_clients & %Hsa_extract & #Hpers_pointer) !# %Φ Hshift".
    rewrite /TC_read /KVS_wrapped_api /wrap_read.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /read_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T [%t [%lt [%exec
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq 
       & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]]]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_rd_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, (c, #"RdPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, (c, #"RdPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, (t ++ [(#tag1, (c, #"RdPre"))%V]), lt, exec.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_rd_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hread"; try done.
    iClear "Hread".
    iMod "Hshift" as "(%vo & %V & (Hkey_c & Hkey) & Hshift)".
    iDestruct "Hkey_c" as "(Hkey_c & (%sa' & %γ & #Hsa'_pointer & %Hsa'_extract & Himp & %Hsa'_in))".
    destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
    iDestruct "Hkey" as "(Hkey & Hall)".
    iModIntro.
    iExists vo, V.
    iFrame.
    iNext.
    iIntros (wo) "(Hkey_c & Hkey)".
    iInv "HinvExt" as ">[%T' [%t' [%lt' [%exec'
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hbased' & %Hvalid_exec' & %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]]]]" "Hclose'".
    iMod (own_lin_add _ _ (#tag1, (c, (#"RdLin", (#k, $wo))))%V with "[$HOwnLin']") as "HOwnLin'".
    iMod (own_lin_hist with "[$HOwnLin']") as "(HOwnLin' & #HOwnLinHist')".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, (c, #"RdPre"))%V ∈ t') as Hin'.
    {
      apply (elem_of_prefix (t ++ [(#tag1, (c, #"RdPre"))%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, (#"RdLin", (#k, $wo))))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "HstateRes'" as "(%mstate & Hmap_mstate & %mname & Hmap_mname & Hdisj_trace_res)".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {4} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hdisj_trace_res" as "(Hdisj_trace_res_sa & Hdisj_trace_res)".
    rewrite big_sepS_singleton.
    iDestruct (@ghost_map_lookup with "[$Hmap_mname][$Hsa'_pointer]") as "%Hlookup_mname".
    iDestruct "Hdisj_trace_res_sa" as "[(_ & %Hnot & _) | Htrace_res]"; first set_solver.
    iAssert (ghost_map_elem γ k (DfracOwn 1%Qp) vo) with "[Himp]" as "Hkey_internal"; 
      first by iApply "Himp".
    assert (KVS_keys = {[k]} ∪ (KVS_keys ∖ {[k]})) as Heq_k_keys.
    {
      apply union_difference_L.
      set_solver.
    }
    iDestruct "Htrace_res" as "(%s & %c' & %γ' & %m & %Hlookup_mstate & %Hextract & #Hsa_pointer
      & Hmap_m & Htrace_res)".
    iAssert ((⌜γ = γ'⌝ ∗ ⌜c = c'⌝)%I) as "(<- & <-)".
    {
      iAssert ((⌜(γ, c) = (γ', c')⌝)%I) as "%Heq_pair".
      - iApply (ghost_map_elem_agree sa γmname _ _ (γ, c) (γ', c') with "[$Hsa'_pointer][$Hsa_pointer]").
      - iSplit; set_solver.
    }
    iDestruct "Htrace_res" as "(%Hinit & [(_ & _ & _ & Hfalse)|Htrace_res])".
    {
      rewrite {1} Heq_k_keys.
      rewrite (big_sepS_union _ {[k]} (KVS_keys ∖ {[k]})); last set_solver.
      rewrite big_sepS_singleton.
      iDestruct "Hfalse" as "((%ov' & Hfalse) & _)".
      iCombine "Hkey_internal" "Hfalse" as "Hfalse".
      iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
      by rewrite dfrac_valid_own in Hfalse.
    }
    iDestruct "Hkey" as "(Hkey & %Hkey_res)".
    iAssert ((⌜∀ v, wo = Some v → ∃ t' s', t' ∈ T' ∧ Wr s' k v ∈ t'⌝ ∗
             ⌜latest_write c k vo T'⌝)%I) 
            as "(%Hread_res_1 & %Hread_res_2)".
    {
      iDestruct (@ghost_map_lookup with "[$Hmap_m][$Hkey_internal]") as "%Hlookup_m".
      iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & %Hopen_tail &
          Hkeys & Hkey_info)".
      destruct (decide (k ∈ domain ∩ KVS_keys)) as [Hk_in_dom|Hk_nin_dom].
      - iAssert (⌜latest_write c k vo T'⌝%I) as "%Hlatest_write"; 
            first iApply "Hkey_info"; try done.
        iSplit; last iPureIntro; last eauto.
        destruct Hkey_res as [(-> & [(v & -> & Hin_V)|Heq])| (Hneq & ->)].
        2: rewrite Heq; by iPureIntro.
        + iDestruct ("Hall" $! v with "[//]") as "(%lh & %tag' & %c' & #Hlh_lin_hist & %Hin_lh)".
          iAssert (⌜(#tag', (c', (#"WrLin", (#k, v))))%V ∈ lt'⌝%I) as "%Hin_lt'".
          {
            iDestruct (own_lin_prefix with "[$HOwnLin' $Hlh_lin_hist]") 
              as "(HOwnLin' & Hlh_lin_hist' & %Hprefix_lh)".
            iPureIntro.
            assert ((#tag', (c', (#"WrLin", (#k, v))))%V ∈ 
              lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ (Some v)))))%V]) as Hin_lt_app;
              first by apply (elem_of_prefix _ _ _ Hin_lh Hprefix_lh).
            rewrite elem_of_app in Hin_lt_app.
            destruct Hin_lt_app as [Hin_lt | Hin_lt]; set_solver.
          }
          iPureIntro.
          intros v' Heq_some.
          inversion Heq_some as [Heq_v_v'].
          rewrite -Heq_v_v'.
          destruct Hex' as (Hex' & _).
          destruct (Hex' (#tag', (c', (#"WrLin", (#k, v))))%V (Wr (tag', c') k v) Hin_lt')
            as (t_wr & Ht_wr_in & Hwr_in); first by simpl.
          eauto.
        + iPureIntro.
          intros v' Heq_some.
          inversion Heq_some as [Heq_v_v'].
          rewrite Heq_v_v' in Hlatest_write.
          destruct Hlatest_write as [Hfalse | 
            (v & t_wr & s & Heq_some' & (_ & Ht_wr_in & _) & Hwr_in & _)];
            set_solver.
      - assert ((KVS_keys ∖ (domain ∩ KVS_keys)) = 
            {[k]} ∪ ((KVS_keys ∖ (domain ∩ KVS_keys)) ∖ {[k]})) as Heq_k_keys'.
        {
          apply union_difference_L.
          set_solver.
        }
        rewrite Heq_k_keys'.
        rewrite (big_sepS_union _ {[k]} ((KVS_keys ∖ (domain ∩ KVS_keys)) ∖ {[k]})); 
          last set_solver.
        iDestruct "Hkeys" as "(Hkeys_k & _)".
        rewrite big_sepS_singleton.
        iDestruct "Hkeys_k" as "(%ov & Hkeys_k)".
        iCombine "Hkeys_k" "Hkey_internal" as "Hfalse".
        iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
        by rewrite dfrac_valid_own in Hfalse.
    }
    iMod ("Hclose'" with "[Htr_is' Hmap_mstate Hmap_mname Hmap_m Htrace_res Hdisj_trace_res 
      HOwnLin' Hpost_res' Hlin_res']").
    {
      iNext.
      assert (Decision (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
        as Hdecision.
      {
        do 2 (apply list_exist_dec; intros).
        apply _.
      }
      destruct (decide (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
          as [(trans & Htrans_in & Hop)|Hdec].
      - destruct (elem_of_list_split _ _ Htrans_in) as (T1 & T2 & ->).
        iExists (T1 ++ (trans ++ [Rd (tag1, c) k wo]) :: T2), t', (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ wo))))%V]), exec'.
        iFrame.
        iSplit.
        + iPureIntro.
          apply (lin_trace_lin lt' (#tag1, (c, #"RdPre"))%V
            (#tag1, (c, (#"RdLin", (#k, $ wo))))%V tag1 c t'); try done;
            rewrite /is_lin_event /is_rd_lin_event /is_pre_event /is_rd_pre_event;
            destruct wo; set_solver.
        + iSplit.
          * iPureIntro.
            by apply trans_add_non_empty.
          * iSplit.
            -- iPureIntro.
               destruct wo; by apply extraction_of_add2.
            -- iSplit.
               ++ iPureIntro.
                  apply (valid_transactions_add2 _ _ tag1 _ _ c); try done;
                    first by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
                  ** intros s' k' ov' tag' v' Heq Hin_wr Hnot.
                     destruct Hkey_res as [(-> & Hdisj)| (Hneq & <-)].
                     --- exfalso. 
                         destruct Hread_res_2 as [(_ & Hno_write)|Hfalse]; last set_solver.
                         assert (open_trans trans c (T1 ++ trans :: T2)) as Hopen_trans; 
                          last set_solver.
                         destruct Hop as (op_last & Hop_in & Hlast_trans & Hconn_last & Hcm_last).
                         exists op_last.
                         split_and!; try done.
                         intros (tag_cm & b & ->).
                         by simpl in Hcm_last.
                     --- destruct (decide (ov' = Some v')) as [Heq'|Hneq']; first done.
                         exfalso.
                         apply Hnot.
                         destruct wo as [v|]; last done.
                         assert (k = k') as <-; first set_solver.
                         destruct Hread_res_2 as [Hfalse| (v'' & trans' & tag_wr & Heq_some' & Hopen_trans & Hwr_in & Hrel)]; 
                          first set_solver.
                         assert (v  = v'') as <-; first set_solver.
                         exists tag_wr, v.
                         assert (trans = trans') as <-.
                         {
                           destruct Hvalid_trans' as (_ & Hvalid_trans').
                           destruct Hopen_trans as (op_last & Htrans'_in & Hlast' & Hconn_last' & Hcm_last').
                           rewrite elem_of_list_lookup in Htrans_in.
                           rewrite elem_of_list_lookup in Htrans'_in.
                           destruct Htrans_in as (i & Htrans_in).
                           destruct Htrans'_in as (i' & Htrans'_in).
                           assert (i = i'); last set_solver.
                           destruct Hop as (op & _ & Hlast & Hop_conn & Hop_cm).
                           apply (Hvalid_trans' trans trans' op op_last i i' c); try done.
                           intros (tag_cm & b & ->).
                           by simpl in Hop_cm.
                         }
                         rewrite elem_of_list_lookup in Hwr_in.
                         destruct Hwr_in as (i & Hwr_in).
                         split.
                         +++ apply rel_list_imp.
                             set_solver.
                         +++ assert (i < length trans) as Hlength; 
                              first by eapply lookup_lt_Some.
                             rewrite /rel_list.
                             exists i, (length trans).
                             split_and!; try done; 
                              first by apply lookup_app_l_Some.
                             assert (Init.Nat.pred (length (trans ++ [Rd (tag1, c) k (Some v)])) = 
                              length trans) as <-; 
                              last by rewrite -last_lookup last_snoc.
                             rewrite last_length.
                             lia.
                  ** destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
                     exists op.
                     split_and!; try done.
                     intros (s' & b' & ->).
                     set_solver.
               ++ iSplit.
                  ** iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & 
                       %Hopen_start & Hrest)".
                     iPureIntro.
                     apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done.
                     --- right.
                         rewrite /is_rd_lin_event.
                         destruct wo; set_solver.
                     --- by exists t'.
                     --- intros tag' c' k' v' Heq.
                         inversion Heq.
                         destruct wo as [v|]; last done.
                         subst.
                         assert (v = v') as <-; first set_solver.
                         destruct (Hread_res_1 v) as (t1 & s1 & Ht1_in & Hwr_in); first done.
                         destruct Hex' as (_ & Hex' & _).
                         specialize (Hex' t1 (Wr s1 k v) Ht1_in Hwr_in).
                         destruct s1.
                         simpl in Hex'.
                         eauto.
                  ** iSplit.
                     --- iPureIntro. 
                         eapply based_on_add1; rewrite /is_cm_op; set_solver.
                     --- iSplit; first by simpl.
                         iApply (trace_state_resources_read_lin2 clients c tag1 lt' T1 T2 trans k sa wo
                            s γ γmstate γmname extract mstate mname m with "[][][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                            [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
                          +++ iPureIntro.
                              intros Hfalse.
                              eapply two_trans_implies_false_app_cons; try done.
                          +++ iPureIntro.
                              destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                              exists e.
                              split_and!; try done.
                              apply elem_of_app; eauto.
      - iExists (T' ++ [[Rd (tag1, c) k wo]]), t', (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ wo))))%V]), exec'.
        iFrame.
        iSplit.
        + iPureIntro.
          apply (lin_trace_lin lt' (#tag1, (c, #"RdPre"))%V
            (#tag1, (c, (#"RdLin", (#k, $ wo))))%V tag1 c t'); try done;
            rewrite /is_lin_event /is_rd_lin_event /is_pre_event /is_rd_pre_event;
            destruct wo; set_solver.
        + iSplit.
          * iPureIntro.
            intros t'' Ht''_in.
            rewrite elem_of_app in Ht''_in.
            destruct Ht''_in as [Ht''_in | Ht''_in]; set_solver.
          * iSplit.
            -- iPureIntro.
               destruct wo; by apply extraction_of_add1.
            -- iSplit.
               ++ iPureIntro.
                  apply (valid_transactions_add1 T' _ c); try done.
                  ** set_solver.
                  ** exists (Rd (tag1, c) k wo).
                     by simpl.
                  ** apply valid_transaction_singleton.
                  ** intros (t'' & Ht''_in & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
                     apply Hdec.
                     exists t''.
                     split; first done.
                     exists op.
                     split_and!; try done.
                     rewrite /is_cm_op in Hop_cm.
                     destruct op; try done.
                     exfalso.
                     eauto.
               ++ iSplit.
                  ** iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & 
                       %Hopen_start & Hrest)".
                     iPureIntro.
                     apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done.
                     --- right.
                         rewrite /is_rd_lin_event.
                         destruct wo; set_solver.
                     --- by exists t'.
                     --- intros tag' c' k' v' Heq.
                         inversion Heq.
                         destruct wo as [v|]; last done.
                         subst.
                         assert (v = v') as <-; first set_solver.
                         destruct (Hread_res_1 v) as (t1 & s1 & Ht1_in & Hwr_in); first done.
                         destruct Hex' as (_ & Hex' & _).
                         specialize (Hex' t1 (Wr s1 k v) Ht1_in Hwr_in).
                         destruct s1.
                         simpl in Hex'.
                         eauto.
                  ** iSplit. 
                     --- iPureIntro.
                         apply based_on_add2; rewrite /is_cm_op; set_solver.
                     --- iSplit; first by simpl.
                         iApply (trace_state_resources_read_lin1 clients c tag1 lt' T' k sa wo
                           s γ γmstate γmname extract mstate mname m with "[][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                           [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
                         iPureIntro.
                         destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                         exists e.
                         split_and!; try done.
                         apply elem_of_app; eauto.
    }
    iMod ("Hshift" $! wo with "[Hkey_internal Hall Hkey_c Hkey]").
    {
      simpl.
      iSplitL "Hkey_c Hkey_internal"; iFrame; last by iPureIntro.
      iExists sa, γ.
      iFrame "#".
      iSplit; first by iPureIntro.
      iSplit; last by iPureIntro.
      iIntros (_).
      iFrame.
    }
    iModIntro.
    rewrite /read_post_emit_event.
    wp_pures.
    wp_bind (Emit _).
    iInv "HinvExt" as ">[%T'' [%t'' [%lt'' [%exec''
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]]]]" "Hclose''".
    iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
      as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
    assert ((#tag1, (c, (#"RdLin", (#k, $ wo))))%V ∈ lt'') as HstLinIn.
    {
      apply (elem_of_prefix (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ wo))))%V])); last done.
      set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      eapply valid_trace_post; try done; destruct wo;
        rewrite /is_post_event /is_rd_post_event;
        set_solver.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, (#"RdPost", (#k, $wo))))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γmpost (#tag1, (c, (#"RdPost", (#k, $wo))))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
     as "Hpost_res''".
    {
      simpl.
      iSplitL; first by iPureIntro.
      iPureIntro.
      destruct wo;
      rewrite /is_post_event /is_rd_post_event;
      set_solver.
    }
    iMod ("Hclose''" with "[Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', (t'' ++ [_]), lt'', exec''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      destruct wo;
      rewrite /is_post_event /is_rd_post_event;
      set_solver.
    }
    iModIntro.
    wp_pures.
    destruct wo; simpl; iFrame.
  Qed.

  Lemma write_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (∃ T, GlobalInvExt commit_test_ru T extract γmstate γmlin γmpost γmname γl clients) -∗
    @write_spec _ _ _ _ lib res -∗
    @write_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hwrite".
    rewrite /write_spec.
    iModIntro.
    iIntros (c sa E k v) "%Hsub %Hin (#Hconn & %Hsa_in_clients & %Hsa_extract & #Hpers_pointer) !# %Φ Hshift".
    rewrite /TC_write /KVS_wrapped_api /wrap_write.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /write_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T [%t [%lt [%exec 
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq &
      %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]]]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_wr_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, (c, #"WrPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, (c, #"WrPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, (t ++ [(#tag1, (c, #"WrPre"))%V]), lt, exec.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_wr_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hwrite"; try done.
    iClear "Hwrite".
    iMod "Hshift" as "(%vo & %V & (Hkey_c & Hkey) & Hshift)".
    iDestruct "Hkey_c" as "(Hkey_c & (%sa' & %γ & #Hsa'_pointer & %Hsa'_extract & Himp & %Hsa'_in))".
    destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
    iDestruct "Hkey" as "(Hkey & Hall)".
    iModIntro.
    iExists vo, V.
    iFrame.
    iNext.
    iIntros "(Hkey_c & Hkey)".
    iInv "HinvExt" as ">[%T' [%t' [%lt' [%exec'
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hbased' & %Hvalid_exec' & %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]]]]" "Hclose'".
    iMod (own_lin_add _ _ (#tag1, (c, (#"WrLin", (#k, v))))%V with "[$HOwnLin']") as "HOwnLin'".
    iMod (own_lin_hist with "[$HOwnLin']") as "(HOwnLin' & #HOwnLinHist')".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, (c, #"WrPre"))%V ∈ t') as Hin'.
    {
      apply (elem_of_prefix (t ++ [(#tag1, (c, #"WrPre"))%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, (#"WrLin", (#k, v))))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "HstateRes'" as "(%mstate & Hmap_mstate & %mname & Hmap_mname & Hdisj_trace_res)".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {4} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hdisj_trace_res" as "(Hdisj_trace_res_sa & Hdisj_trace_res)".
    rewrite big_sepS_singleton.
    iDestruct (@ghost_map_lookup with "[$Hmap_mname][$Hsa'_pointer]") as "%Hlookup_mname".
    iDestruct "Hdisj_trace_res_sa" as "[(_ & %Hnot & _) | Htrace_res]"; first set_solver.
    iAssert (ghost_map_elem γ k (DfracOwn 1%Qp) vo) with "[Himp]" as "Hkey_internal"; 
      first by iApply "Himp".
    assert (KVS_keys = {[k]} ∪ (KVS_keys ∖ {[k]})) as Heq_k_keys.
    {
      apply union_difference_L.
      set_solver.
    }
    iDestruct "Htrace_res" as "(%s & %c' & %γ' & %m & %Hlookup_mstate & %Hextract & #Hsa_pointer
      & Hmap_m & Htrace_res)".
    iAssert ((⌜γ = γ'⌝ ∗ ⌜c = c'⌝)%I) as "(<- & <-)".
    {
      iAssert ((⌜(γ, c) = (γ', c')⌝)%I) as "%Heq_pair".
      - iApply (ghost_map_elem_agree sa γmname _ _ (γ, c) (γ', c') with "[$Hsa'_pointer][$Hsa_pointer]").
      - iSplit; set_solver.
    }
    iDestruct "Htrace_res" as "(%Hinit & [(_ & _ & Hfalse)|Htrace_res])".
    {
      rewrite {1} Heq_k_keys.
      rewrite (big_sepS_union _ {[k]} (KVS_keys ∖ {[k]})); last set_solver.
      rewrite big_sepS_singleton.
      iDestruct "Hfalse" as "(_ & (%ov' & Hfalse) & _)".
      iCombine "Hkey_internal" "Hfalse" as "Hfalse".
      iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
      by rewrite dfrac_valid_own in Hfalse.
    }
    iMod (ghost_map_update (Some v.(SV_val)) with "[$Hmap_m] [$Hkey_internal]") 
      as "(Hmap_m & Hkey_internal)".
    iMod ("Hclose'" with "[Htr_is' Hmap_mstate Hmap_mname Hmap_m Htrace_res Hdisj_trace_res 
      HOwnLin' Hpost_res' Hlin_res']").
    {
      iNext.
      assert (Decision (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
        as Hdecision.
      {
        do 2 (apply list_exist_dec; intros).
        apply _.
      }
      destruct (decide (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
          as [(trans & Htrans_in & Hop)|Hdec].
      - destruct (elem_of_list_split _ _ Htrans_in) as (T1 & T2 & ->).
        iExists (T1 ++ (trans ++ [Wr (tag1, c) k v]) :: T2), t', (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]), exec'.
        iFrame.
        iSplit.
        + iPureIntro.
          apply (lin_trace_lin lt' (#tag1, (c, #"WrPre"))%V 
            (#tag1, (c, (#"WrLin", (#k, v))))%V tag1 c t'); try done;
            rewrite /is_lin_event /is_wr_lin_event /is_pre_event /is_wr_pre_event; 
            do 2 right; left; eauto.
        + iSplit.
          * iPureIntro.
            by apply trans_add_non_empty.
          * iSplit.
            -- iPureIntro.
               by apply extraction_of_add2.
            -- iSplit.
               ++ iPureIntro.
                  apply (valid_transactions_add2 _ _ tag1 _ _ c); try done;
                    first by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
                  destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
                  exists op.
                  split_and!; try done.
                  intros (s' & b' & ->).
                  set_solver.
               ++ iSplit.
                  ** iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & 
                       %Hopen_start & Hrest)".
                     iPureIntro.
                     apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done.
                     --- rewrite /is_wr_lin_event.
                         set_solver.
                     --- by exists t'.
                  ** iSplit.
                    --- iPureIntro. 
                        eapply based_on_add1; rewrite /is_cm_op; set_solver.
                    --- iSplit; first by simpl.
                        iApply (trace_state_resources_write_lin2 clients c tag1 lt' T1 T2 trans k v sa 
                          s γ γmstate γmname extract mstate mname m with "[][][][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                          [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
                        +++ iPureIntro.
                            intros Hfalse.
                            eapply two_trans_implies_false_app_cons; try done.
                        +++ iPureIntro.
                            destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                            exists e.
                            split_and!; try done.
                            apply elem_of_app; eauto. 
      - iExists (T' ++ [[Wr (tag1, c) k v]]), t', (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]), exec'.
        iFrame.
        iSplit.
        + iPureIntro.
          apply (lin_trace_lin lt' (#tag1, (c, #"WrPre"))%V 
            (#tag1, (c, (#"WrLin", (#k, v))))%V tag1 c t'); try done;
            rewrite /is_lin_event /is_wr_lin_event /is_pre_event /is_wr_pre_event; 
            do 2 right; left; eauto.
        + iSplit.
          * iPureIntro.
            intros t'' Ht''_in.
            rewrite elem_of_app in Ht''_in.
            destruct Ht''_in as [Ht''_in | Ht''_in]; set_solver.
          * iSplit.
            -- iPureIntro.
               by apply extraction_of_add1.
            -- iSplit.
               ++ iPureIntro.
                  apply (valid_transactions_add1 T' _ c); try done.
                  ** set_solver.
                  ** exists (Wr (tag1, c) k v).
                     by simpl.
                  ** apply valid_transaction_singleton.
                  ** intros (t'' & Ht''_in & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
                     apply Hdec.
                     exists t''.
                     split; first done.
                     exists op.
                     split_and!; try done.
                     rewrite /is_cm_op in Hop_cm.
                     destruct op; try done.
                     exfalso.
                     eauto.
               ++ iSplit.
                  ** iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & 
                       %Hopen_start & Hrest)".
                     iPureIntro.
                     apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done.
                     --- rewrite /is_wr_lin_event.
                         set_solver.
                     --- by exists t'.
                  ** iSplit. 
                     --- iPureIntro.
                         apply based_on_add2; rewrite /is_cm_op; set_solver.
                     --- iSplit; first by simpl.
                         iApply (trace_state_resources_write_lin1 clients c tag1 lt' T' k v.(SV_val) sa
                          s γ γmstate γmname extract mstate mname m with "[][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                          [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
                         iPureIntro.
                         destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                         exists e.
                         split_and!; try done.
                         apply elem_of_app; eauto.
    }
    iMod ("Hshift" with "[Hkey_internal Hall Hkey_c Hkey]").
    {
      simpl.
      iSplitL "Hkey_c Hkey_internal".
      - iFrame.
        iExists sa, γ.
        iFrame "#".
        iSplit; first by iPureIntro.
        iSplit; last by iPureIntro.
        iIntros (_).
        iFrame.
      - iFrame.
        iIntros (v' Hv'_in).
        rewrite elem_of_union in Hv'_in.
        destruct Hv'_in as [Hv'_in | Hv'_in]; first by iApply "Hall".
        iExists (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]), tag1, c.
        iFrame "#".
        iPureIntro.
        set_solver.
    }
    iModIntro.
    rewrite /write_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T'' [%t'' [%lt'' [%exec''
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]]]]" "Hclose''".
    iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
      as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
    assert ((#tag1, (c, (#"WrLin", (#k, v))))%V ∈ lt'') as HstLinIn.
    {
      apply (elem_of_prefix (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V])); last done.
      set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      eapply valid_trace_post; 
      rewrite /is_post_event /is_wr_post_event;
      set_solver.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, (#"WrPost", (#k, v))))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γmpost (#tag1, (c, (#"WrPost", (#k, v))))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
     as "Hpost_res''".
    {
      simpl.
      iSplitL; first by iPureIntro.
      iPureIntro.
      rewrite /is_post_event /is_wr_post_event.
      set_solver.
    }
    iMod ("Hclose''" with "[Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', (t'' ++ [(#tag1, (c, (#"WrPost", (#k, v))))%V]), lt'', exec''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_post_event /is_wr_post_event.
      set_solver.
    }
    set_solver.
  Qed.

  Lemma start_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (∃ T, GlobalInvExt commit_test_ru T extract γmstate γmlin γmpost γmname γl clients) -∗
    @start_spec _ _ _ _ lib res -∗
    @start_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hstart".
    rewrite /start_spec.
    iModIntro.
    iIntros (c sa E) "%Hsub (#Hconn & %Hsa_in_clients & %Hsa_extract & #Hpers_pointer) !# %Φ Hshift".
    rewrite /TC_start /KVS_wrapped_api /wrap_start.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /start_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T [%t [%lt [%exec
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq &
      %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]]]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_st_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, (c, #"StPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, (c, #"StPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, (t ++ [(#tag1, (c, #"StPre"))%V]), lt, exec.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_st_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hstart"; try done.
    iClear "Hstart".
    iMod "Hshift" as "[%m (((Hconn_state & Hsa_pointer) & Hkeys) & Hshift)]".
    iModIntro.
    iExists m.
    iFrame.
    rewrite big_sepM_sep.
    iDestruct "Hkeys" as "(Hkeys1 & Hkeys2)".
    iFrame.
    iModIntro.
    iIntros "(Hconn_state & Hkeys1 & Hkeys_conn)".
    iInv "HinvExt" as ">[%T' [%t' [%lt' [%exec' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hbased' & %Hvalid_exec' & %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]]]]" "Hclose'".
    simpl; rewrite /trace_state_resources.
    iDestruct "HstateRes'" as "(%mstate' & Hghost_map_mstate' & %mname' & Hghost_map_mname' & Hdisj_trace_res)".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_mstate'][$Hsa_pointer]") as "%Hlookup_mstate'".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {3} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hdisj_trace_res" as "(Hdisj_trace_res_sa & Hdisj_trace_res)".
    rewrite big_sepS_singleton.
    iDestruct "Hdisj_trace_res_sa" as "[(Hfalse & _) | Htrace_res]".
    {
      iDestruct "Hfalse" as "[%Hfalse | %Hfalse]"; set_solver.
    }
    iDestruct "Htrace_res" as "(%ls & %c' & %γ & %m' & %Hlookup_mstate'' & %Hextract & 
      #Hsa_c'_pointer & Hghost_map_m' & %Hinit & [(-> & %Hclosed & %Hopen_trans & Hkeys_conn_res) | Hfalse])"; last first.
    {
      assert (ls = CanStart) as ->; first set_solver.
      by iDestruct "Hfalse" as "(%domain & %sub_domain & %tail & %Hfalse & _)".
    }
    iMod (ghost_map_update (Active (dom m), Some c) with "[$Hghost_map_mstate'] [$Hsa_pointer]") 
      as "(Hghost_map_mstate' & Hsa_pointer)".
    iAssert ((|==> (([∗ set] k ∈ KVS_keys, ghost_map_elem γ k (DfracOwn 1%Qp) None) ∗ 
              (∃ m'', ghost_map_auth γ 1 m'' ∧ ⌜∀ k, k ∈ KVS_keys → m'' !! k = Some None⌝)))%I) 
      with "[Hkeys_conn_res Hghost_map_m']" as ">(Hkeys_conn_res & (%m'' & Hghost_map_m' & %Hnone))".
    {
      iRevert "Hghost_map_m'".
      iRevert (m').
      iInduction KVS_keys as [|k KVS_Keys Hnin] "IH" using set_ind_L.
      - iIntros (m') "Hghost_map_m'".
        iModIntro. 
        iSplitR "Hghost_map_m'"; first done.
        iExists m'.
        iFrame.
        iPureIntro.
        set_solver.
      - iIntros (m') "Hghost_map_m'".
        rewrite big_sepS_union; last set_solver.
        iDestruct "Hkeys_conn_res" as "(Hkeys_conn_key & Hkeys_conn_res)".
        iMod ("IH" with "[$Hkeys_conn_res][$Hghost_map_m']") 
          as "(Hkeys_conn_res & [%m'' (Hghost_map' & %Hnone)])".
        rewrite big_sepS_singleton.
        iDestruct "Hkeys_conn_key" as "(%ov & Hkeys_conn_key)".
        iMod (ghost_map_update None with "[$Hghost_map'] [$Hkeys_conn_key]") 
          as "(Hghost_map' & Hkeys_conn_key)".
        iModIntro.
        iSplitR "Hghost_map'".
        + rewrite big_sepS_union; last set_solver.
          iFrame. 
          rewrite big_sepS_singleton.
          iFrame.
        + iExists _.
          iFrame.
          iPureIntro.
          intros k' Hin.
          destruct (decide (k = k')) as [->|Hneq].
          * by rewrite lookup_insert.
          * rewrite lookup_insert_ne; last done.
            apply Hnone.
            set_solver.
    }
    iAssert ((([∗ set] k ∈ (dom m) ∩ KVS_keys, ghost_map_elem γ k (DfracOwn 1%Qp) None) ∗ 
              ([∗ set] k ∈ KVS_keys ∖ ((dom m) ∩ KVS_keys), ghost_map_elem γ k (DfracOwn 1%Qp) None))%I) 
      with "[Hkeys_conn_res]" as "(Hkeys_conn_res1 & Hkeys_conn_res2)".
    {
      assert (KVS_keys = (dom m ∩ KVS_keys) ∪ (KVS_keys ∖ (dom m ∩ KVS_keys))) as Heq.
      - apply union_difference_L.
        set_solver.
      - rewrite {1} Heq.
        rewrite (big_sepS_union _ (dom m ∩ KVS_keys) (KVS_keys ∖ (dom m ∩ KVS_keys))); last set_solver.
        iFrame.
    }
    iMod (own_lin_add _ _ (#tag1, (c, #"StLin"))%V with "[$HOwnLin']") as "HOwnLin'".
    iMod (own_lin_hist with "[$HOwnLin']") as "(HOwnLin' & #HOwnLinHist')".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, (c, #"StPre"))%V ∈ t') as Hin.
    {
      apply (elem_of_prefix (t ++ [(#tag1, (c, #"StPre"))%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, #"StLin"))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl. 
    }
    iMod ("Hclose'" with "[Htr_is' HOwnLin' Hghost_map_mname' Hghost_map_m' 
      Hghost_map_mstate' Hkeys_conn_res2 Hlin_res' Hpost_res' Hdisj_trace_res]").
    {
      iModIntro.
      iExists T', t', (lt' ++ [(#tag1, (c, #"StLin"))%V]), exec'.
      iFrame.
      iSplitR.
      {
        iPureIntro.
        apply (lin_trace_lin lt' ((#tag1, (c, #"StPre"))%V) ((#tag1, (c, #"StLin"))%V) tag1 c t'); 
          try done; rewrite /is_lin_event /is_pre_event; left; by exists tag1, c.
      }
      iSplitR; first by iPureIntro.
      iSplitR.
      {
        iPureIntro.
        destruct Hex' as (Hex1 & Hex2 & Hex3).
        split.
        - intros le op Hle_in Hlin_le.
          specialize (Hex1 le op).
          apply Hex1; last done.
          rewrite elem_of_app in Hle_in.
          destruct Hle_in as [Hle_in | Hle_in]; first done.
          assert (le = (#tag1, (c, #"StLin"))%V) as ->; first set_solver.
          inversion Hlin_le.
        - split.
          + intros trans op Hin_t Hin_op.
            specialize (Hex2 trans op Hin_t Hin_op).
            set_solver.
          + intros trans op1 op2 Htrans_in Hrel.
            specialize (Hex3 trans op1 op2 Htrans_in Hrel).
            destruct Hex3 as (i & j & Hle & Hlookup_i & Hlookup_j).
            exists i, j.
            split; first done.
            split; by apply lookup_app_l_Some.
      }
      iSplitR; first by iPureIntro.
      iSplitR.
      {
        iPureIntro.
        apply valid_sequence_st_lin; set_solver.
      }
      iSplit; first done.
      iSplit; first iPureIntro; first by simpl.
      iExists (<[sa:=(Active (dom m), Some c)]> mstate').
      iFrame.
      iExists mname'.
      iFrame.
      rewrite {3} Heq_sa_clients.
      rewrite big_sepS_union; last set_solver.
      iSplitL "Hkeys_conn_res2 Hghost_map_m'".
      - rewrite big_sepS_singleton.
        iRight.
        rewrite /initialized_trace_resources.
        rewrite lookup_insert.
        iExists (Active (dom m)), c, γ, m''.
        assert (c = c') as ->; first set_solver.
        iFrame "#∗".
        do 3 (iSplit; first iPureIntro; first set_solver).
        iRight.
        iExists (dom m), ((dom m) ∩ KVS_keys), [].
        do 2 (iSplit; first by iPureIntro).
        iSplitR.
        + iPureIntro.
          exists (#tag1, (c', #"StLin"))%V, lt'.
          do 2 (split; first done).
          split; first by exists tag1.
          set_solver.
        + iSplitL.
          * iApply (big_sepS_wand with "[$Hkeys_conn_res2]").
            iApply big_sepS_intro.
            iModIntro.
            iIntros (k Hk_in) "Hkey".
            iExists None.
            iFrame.
          * iIntros (k' Hk'_dom ov Hlookup).
            iPureIntro.
            destruct ov as [v|].
            -- rewrite Hnone in Hlookup; first done.
               set_solver.
            -- left.
               set_solver.
      - iApply (big_sepS_wand with "[$Hdisj_trace_res]").
        iApply big_sepS_intro.
        iModIntro.
        iIntros (sa' Hsa'_in) "Hsa'".
        iApply (client_trace_state_resources_neq2 sa sa' c with "[][][][$]"); try done.
        iPureIntro; set_solver.
    }
    iMod ("Hshift" with "[Hkeys1 Hkeys2 Hkeys_conn Hsa_pointer Hkeys_conn_res1 Hconn_state]").
    {
      iFrame.
      do 2 rewrite big_sepM_dom.
      iInduction (dom m) as [|k dom Hnin] "IH" using set_ind_L; first set_solver.
      rewrite big_sepS_union; last set_solver.
      iDestruct "Hkeys_conn" as "(Hkeys_conn_key & Hkeys_conn)".
      assert (c = c') as <-; first set_solver.
      destruct (decide (k ∈ KVS_keys)) as [Hk_in | Hk_nin].
      - assert (({[k]} ∪ dom) ∩ KVS_keys = {[k]} ∪ (dom ∩ KVS_keys)) as ->; first set_solver.
        rewrite big_sepS_union; last set_solver.
        iDestruct "Hkeys_conn_res1" as "(Hkeys_conn_res1_key & Hkeys_conn_res1)".
        iDestruct ("IH" with "[$Hkeys_conn][$Hkeys_conn_res1]") as "Hkeys_conn".
        rewrite big_sepS_union; last set_solver.
        iFrame.
        iDestruct (big_sepS_sep with "[$Hkeys_conn_key $Hkeys_conn_res1_key]") 
          as "Hkeys_conn_key".
        iApply (big_sepS_wand with "[$Hkeys_conn_key]").
        iApply big_sepS_intro.
        iModIntro.
        iIntros (key Hin') "Hres".
        iDestruct "Hres" as "(Hres1 & Hres2)".
        iFrame.
        iExists sa, γ.
        iFrame "#".
        iSplit; first done.
        iSplit; last done.
        iIntros (Hkey_in).
        iFrame.
      - assert (({[k]} ∪ dom) ∩ KVS_keys = dom ∩ KVS_keys) as ->; first set_solver.
        rewrite big_sepS_union; last set_solver.
        iDestruct ("IH" with "[$Hkeys_conn][$Hkeys_conn_res1]") as "Hkeys_conn".
        iFrame.
        iApply (big_sepS_wand with "[$Hkeys_conn_key]").
        iApply big_sepS_intro.
        iModIntro.
        iIntros (key Hin') "Hres".
        iFrame.
        iExists sa, γ.
        iFrame "#".
        iSplit; first done.
        iSplitL; last done.
        iIntros (Hkey_in).
        set_solver.
    }
    iModIntro.
    rewrite /start_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T'' [%t'' [%lt'' [%exec''
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]]]]" "Hclose''".
    iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
      as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
    assert ((#tag1, (c, #"StLin"))%V ∈ lt'') as HstLinIn.
    {
      apply (elem_of_prefix (lt' ++ [(#tag1, (c, #"StLin"))%V])); last done.
      set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      eapply valid_trace_post; 
        rewrite /is_post_event /is_st_post_event;
        set_solver.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, #"StPost"))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γmpost (#tag1, (c, #"StPost"))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
     as "Hpost_res''".
    {
      simpl.
      iSplitL; first by iPureIntro.
      iPureIntro.
      left.
      by eexists _, _.
    }
    iMod ("Hclose''" with "[Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', (t'' ++ [(#tag1, (c, #"StPost"))%V]), lt'', exec''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_post_event /is_st_post_event.
      set_solver.
    }
    set_solver.
  Qed.

  Lemma commit_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (∃ T, GlobalInvExt commit_test_ru T extract γmstate γmlin γmpost γmname γl clients) -∗
    @commit_spec _ _ _ _ lib res -∗
    @commit_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hcommit".
    rewrite /commit_spec.
    iModIntro.
    iIntros (c sa E) "%Hsub (#Hconn & %Hsa_in_clients & %Hsa_extract & (%γ & #Hsa'_pointer)) !# %Φ Hshift".
    rewrite /TC_commit /KVS_wrapped_api /wrap_commit.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /commit_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T [%t [%lt [%exec
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq &
      %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]]]]" "Hclose".
    wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      intros tag Hnin.
      eapply valid_trace_pre; try done.
      rewrite /is_pre_event /is_cm_pre_event; set_solver.
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γmlin (#tag1, (c, #"CmPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod (post_tag_create t γmpost (#tag1, (c, #"CmPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]]; 
        rewrite /is_st_post_event /is_wr_post_event /is_cm_post_event /is_in_post_event in Hfalse; 
        set_solver.
    }
    iMod ("Hclose" with "[Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, (t ++ [(#tag1, (c, #"CmPre"))%V]), lt, exec.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_pre_event /is_cm_pre_event.
      set_solver.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hcommit"; try done.
    iClear "Hcommit".
    iMod "Hshift" as "(%s & %mc & %m & ((Hstate & Hstate_pr) & %Hdom1 & %Hdom2 & Hkeys_conn & Hkeys) & Hshift)".
    iModIntro.
    iExists s, mc, m.
    rewrite big_sepM_sep.
    iDestruct "Hkeys_conn" as "(Hkeys_conn1 & Hkeys_conn2)".
    simpl.
    iAssert (([∗ map] k↦V ∈ m, k ↦ₖ V) ∗ ([∗ map] k↦V ∈ m, (∀ v, ⌜v ∈ V⌝ → 
        ∃ lh (tag : string) c, OwnLinHist γl lh ∗ ⌜(#tag, (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝)))%I 
        with "[Hkeys]" as "(Hkeys1 & Hkeys2)".
    {
      iApply big_sepM_sep.
      iFrame.
    }
    iSplitL "Hkeys_conn1 Hkeys1 Hstate".
    {
      iFrame.
      iSplit; by iPureIntro.
    }
    iModIntro.
    iIntros (b) "(Hstate & Hkeys1)".
    iInv "HinvExt" as ">[%T' [%t' [%lt' [%exec'
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hbased' & %Hvalid_exec' & %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]]]]" "Hclose'".
    iMod (own_lin_add _ _ (#tag1, (c, (#"CmLin", #b)))%V with "[$HOwnLin']") as "HOwnLin'".
    iMod (own_lin_hist with "[$HOwnLin']") as "(HOwnLin' & #HOwnLinHist')".
    iPoseProof (trace_hist_trace_is_prefix with "[$Htr_is'][$Htr_hist]") as "%Hprefix".
    assert ((#tag1, (c, #"CmPre"))%V ∈ t') as Hin'.
    {
      apply (elem_of_prefix (t ++ [(#tag1, (c, #"CmPre"))%V])); last done.
      set_solver.
    }
    iPoseProof (lin_tag_not_in lt' t' γmlin with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γmpost with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γmlin (#tag1, (c, (#"CmLin", #b)))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl.
    }
    iDestruct "HstateRes'" as "(%mstate & Hmap_mstate & %mname & Hmap_mname & Hdisj_trace_res)".
    assert (clients = {[sa]} ∪ (clients ∖ {[sa]})) as Heq_sa_clients.
    {
      apply union_difference_L.
      set_solver.
    }
    rewrite {3} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iDestruct "Hdisj_trace_res" as "(Hdisj_trace_res_sa & Hdisj_trace_res)".
    rewrite big_sepS_singleton.
    iDestruct (@ghost_map_lookup with "[$Hmap_mname][$Hsa'_pointer]") as "%Hlookup_mname".
    iDestruct "Hdisj_trace_res_sa" as "[(_ & %Hnot & _) | Htrace_res]"; first set_solver.
    iDestruct "Htrace_res" as "(%loc_st & %c' & %γ' & %m' & %Hlookup_mstate & %Hextract & #Hsa_pointer
      & Hmap_m & Htrace_res)".
    iAssert (⌜loc_st = Active s⌝)%I as "->".
    {
      iDestruct (@ghost_map_lookup with "[$Hmap_mstate][$Hstate_pr]") as "%Hlookup_mstate'".
      iPureIntro.
      set_solver.
    }
    iAssert ((⌜γ = γ'⌝ ∗ ⌜c = c'⌝)%I) as "(<- & <-)".
    {
      iAssert ((⌜(γ, c) = (γ', c')⌝)%I) as "%Heq_pair".
      - iApply (ghost_map_elem_agree sa γmname _ _ (γ, c) (γ', c') with "[$Hsa'_pointer][$Hsa_pointer]").
      - iSplit; set_solver.
    }
    iDestruct "Htrace_res" as "(%Hinit & [(%Hfalse & _ & _)|Htrace_res])"; first done.
    iMod (ghost_map_update (CanStart, Some c) with "[$Hmap_mstate] [$Hstate_pr]") 
      as "(Hmap_mstate & Hstate_pr)".
    iMod ("Hclose'" with "[Htr_is' HOwnLin' Hpost_res' Hlin_res' Htrace_res Hkeys_conn2 Hmap_mname
      Hmap_m Hdisj_trace_res Hmap_mstate]").
    {
      iModIntro.
      assert (Decision (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
        as Hdecision.
      {
        do 2 (apply list_exist_dec; intros).
        apply _.
      }
      destruct (decide (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
        op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
          as [(trans & Htrans_in & Hop)|Hdec].
      - destruct (elem_of_list_split _ _ Htrans_in) as (T1 & T2 & ->).
        destruct (exists_execution (T1 ++ (trans ++ [Cm (tag1, c) b]) :: T2)) 
          as (exec'' & Hbased'' & Hvalid_exec'').
        {
          intros trans' Hin.
          rewrite elem_of_app in Hin.
          destruct Hin as [Hin|Hin]; first set_solver.
          rewrite elem_of_cons in Hin.
          destruct Hin as [Hin|Hin]; last set_solver.
          rewrite Hin.
          intros Hfalse.
          apply app_eq_nil in Hfalse.
          set_solver.
        }
        iExists (T1 ++ (trans ++ [Cm (tag1, c) b]) :: T2), t', 
          (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V]), exec''.
        iFrame.
        iSplit.
        + iPureIntro.
          apply (lin_trace_lin lt' (#tag1, (c, #"CmPre"))%V 
            (#tag1, (c, (#"CmLin", #b)))%V tag1 c t'); try done;
            rewrite /is_lin_event /is_cm_lin_event /is_pre_event /is_cm_pre_event;
            set_solver.
        + iSplit.
          * iPureIntro.
            by apply trans_add_non_empty.
          * iSplit.
            -- iPureIntro.
               by apply extraction_of_add2.
            -- iSplit.
               ++ iPureIntro.
                  apply (valid_transactions_add2 _ _ tag1 _ _ c); try done;
                    first by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
                  destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
                  exists op.
                  split_and!; try done.
                  intros (s' & b' & ->).
                  set_solver.
              ++ iSplit.
                  ** iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & Hact_eq & -> & 
                       %Hopen_start & Hrest)".
                     iPureIntro.
                     apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done.
                     --- rewrite /is_cm_lin_event.
                         set_solver.
                     --- by exists t'.
                  ** iSplit.
                     --- by iPureIntro.
                     --- iSplit; first by simpl.
                         iApply (trace_state_resources_commit_lin2 clients c tag1 lt' T1 T2 trans sa 
                           s γ γmstate γmname extract b mc mstate mname m' with 
                           "[//][//][//][//][//][//][//][//][][$Hkeys_conn2][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                           [$Hmap_m][$Hdisj_trace_res][$Htrace_res]").
                         iPureIntro.
                         destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                         exists e.
                         split_and!; try done.
                         apply elem_of_app; eauto.
      - destruct (exists_execution (T' ++ [[Cm (tag1, c) b]])) 
          as (exec'' & Hbased'' & Hvalid_exec''); first set_solver.
        iExists (T' ++ [[Cm (tag1, c) b]]), t', (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V]), exec''.
        iFrame.
        iSplit.
        + iPureIntro.
          apply (lin_trace_lin lt' (#tag1, (c, #"CmPre"))%V 
            (#tag1, (c, (#"CmLin", #b)))%V tag1 c t'); try done;
            rewrite /is_lin_event /is_cm_lin_event /is_pre_event /is_cm_pre_event;
            set_solver. 
        + iSplit.
          * iPureIntro.
            intros t'' Ht''_in.
            rewrite elem_of_app in Ht''_in.
            destruct Ht''_in as [Ht''_in | Ht''_in]; set_solver.
          * iSplit.
            -- iPureIntro.
               by apply extraction_of_add1.
            -- iSplit.
               ++ iPureIntro.
                  apply (valid_transactions_add1 T' _ c); try done.
                  ** set_solver.
                  ** exists (Cm (tag1, c) b).
                     by simpl.
                  ** apply valid_transaction_singleton.
                  ** intros (t'' & Ht''_in & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
                     apply Hdec.
                     exists t''.
                     split; first done.
                     exists op.
                     split_and!; try done.
                     rewrite /is_cm_op in Hop_cm.
                     destruct op; try done.
                     exfalso.
                     eauto.
               ++ iSplit.
                  ** iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & Hact_eq & -> & 
                       %Hopen_start & Hrest)".
                     iPureIntro.
                     apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done.
                     --- rewrite /is_cm_lin_event.
                         set_solver.
                     --- by exists t'.
                  ** iSplit.
                     --- by iPureIntro.
                     --- iSplit; first by simpl.
                         iApply (trace_state_resources_commit_lin1 clients c tag1 lt' T' sa 
                           s γ γmstate γmname extract b mc mstate mname m' with 
                           "[//][//][//][//][//][//][//][][$Hkeys_conn2][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                           [$Hmap_m][$Hdisj_trace_res][$Htrace_res]").
                         iPureIntro.
                         destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                         exists e.
                         split_and!; try done.
                         apply elem_of_app; eauto.
    }
    iMod ("Hshift" with "[Hkeys1 Hkeys2 Hstate_pr Hstate]").
    {
      iFrame.
      iApply big_sepM_sep.
      iFrame.
    }
    iModIntro.
    rewrite /commit_post_emit_event.
    wp_pures.
    wp_bind (Emit _).
    iInv "HinvExt" as ">[%T'' [%t'' [%lt'' [%exec''
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]]]]" "Hclose''".
    iDestruct (own_lin_prefix with "[$HOwnLin'' $HOwnLinHist']") 
      as "(HOwnLin'' & HOwnLinHist & %Hprefix')".
    assert ((#tag1, (c, (#"CmLin", #b)))%V ∈ lt'') as HstLinIn.
    {
      apply (elem_of_prefix (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V])); last done.
      set_solver.
    }
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is'']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      eapply valid_trace_post; 
      rewrite /is_post_event /is_cm_post_event;
      set_solver.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, (#"CmPost", #b)))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γmpost (#tag1, (c, (#"CmPost", #b)))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
     as "Hpost_res''".
    {
      simpl.
      iSplitL; first by iPureIntro.
      iPureIntro.
      rewrite /is_post_event /is_cm_post_event.
      set_solver.
    }
    iMod ("Hclose''" with "[Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', (t'' ++ [(#tag1, (c, (#"CmPost", #b)))%V]), lt'', exec''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_post_event /is_cm_post_event.
      set_solver.
    }
    iModIntro.
    by wp_pures.
  Qed.

  (** Main theorem  *)

  Theorem library_implication  (clients : gset socket_address) (lib : KVS_transaction_api) :
    ((RU_spec clients lib) ∗ trace_is [] ∗ 
      trace_inv trace_inv_name valid_trace_ru ∗ ⌜KVS_InvName = nroot .@ "kvs_inv"⌝) ={⊤}=∗ 
    RU_spec clients (KVS_wrapped_api lib).
  Proof.
    iIntros "([%res (Hkeys & Hkvs_init & #Hglob_inv & Hcan_conn & 
      (#Hinit_kvs & #Hinit_cli & #Hread & #Hwrite & #Hstart & #Hcom))] & Htr & #Htr_inv & %Hkvs_inv_name)".    
    iMod (ghost_map_alloc ((gset_to_gmap (CanStart, None) clients : 
      gmap socket_address (local_state * option val))))
      as "[%γmstate (Hghost_map_mstate & Hghost_elems_mstate)]".
    iMod (ghost_map_alloc_empty (K:=string) (V:=bool)) as "[%γmlin Hghost_map_mlin]".
    iMod (ghost_map_alloc_empty (K:=string) (V:=bool)) as "[%γmpost Hghost_map_mpost]".
    iMod (ghost_map_alloc_empty (K:=socket_address) (V:=(gname * val))) as "[%γmname Hghost_map_mname]".
    iMod (own_alloc (● gmap_of_trace 0 ([] : list val) ⋅ 
      ◯ gmap_of_trace 0 ([] : list val))) as (γl) "Hltrace".
    {
      apply auth_both_valid. 
      split; first done. 
      by apply gmap_of_trace_valid.
    }
    iDestruct "Hltrace" as "[Hltrace Hlhist]".
    iMod (inv_alloc KVS_InvName ⊤ (∃ T, GlobalInvExt commit_test_ru T extract γmstate γmlin γmpost γmname γl clients) with 
      "[Htr Hghost_map_mstate Hghost_map_mlin Hghost_map_mpost Hghost_map_mname Hltrace Hlhist]") as "#HinvExt".
    {
      iNext.
      iExists [], [], [], [([], ∅)].
      iFrame.
      simpl.
      iSplitR.
      {
        iPureIntro.
        rewrite /lin_trace_of /rel_list.
        set_solver.
      }
      iSplitR; first iPureIntro; first set_solver.
      iSplitR.
      {
        iPureIntro.
        rewrite /extraction_of.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /valid_transactions.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /valid_sequence /unique_init_events.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /based_on.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        split_and!; try done.
        intros i e1 e2 _ Hfalse.
        rewrite list_lookup_singleton_Some in Hfalse.
        lia.
      }
      iClear "Hinit_kvs Hinit_cli Hread Hstart Hwrite Hcom".
      iSplitR "Hghost_map_mlin Hghost_map_mpost".
      - iExists (gset_to_gmap (CanStart, None) clients).
        iFrame.
        iExists ∅.
        iFrame.
        iApply big_sepS_intro.
        iModIntro.
        iIntros (sa Hin).
        iLeft.
        iSplit.
        + iRight.
          iPureIntro.
          by rewrite lookup_gset_to_gmap_Some.
        + iSplit.
          * iPureIntro.
            set_solver.
          * iPureIntro.
            rewrite /no_emit_with_address.
            set_solver.
      - iSplitL "Hghost_map_mlin". 
        + iExists ∅.
          iFrame.
          iSplitL; first set_solver.
          iIntros (tag Hexists). 
          set_solver.
        + iExists ∅.
          iFrame.
          iSplitL; first set_solver.
          iIntros (tag Hexists).
          set_solver.
    }
    iModIntro.
    iExists (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
    iFrame "Hkvs_init".
    iSplitL "Hkeys".
    {
      simpl.
      iApply (big_sepS_mono with "[$Hkeys]").
      iIntros (k Hin) "Hkey". 
      iFrame.
      by iIntros (v) "%Hfalse".
    }
    iSplitR; iFrame "∗#".
    iSplitL "Hghost_elems_mstate Hcan_conn".
    {
      simpl.
      rewrite big_sepM_gset_to_gmap.
      rewrite big_sepS_sep.
      iFrame.
      iApply (big_sepS_mono with "[$Hghost_elems_mstate]").
      iIntros (sa Hin) "Hkey".
      by iFrame.
    }
    iSplitR.
    {
      iClear "Hinit_kvs Hstart Hwrite Hread Hcom".
      iApply (init_client_implication with "[//][$Htr_inv][$HinvExt][$Hinit_cli]").
    }
    iSplitR.
    {
      iClear "Hinit_kvs Hinit_cli Hwrite Hstart Hcom".
      iApply (read_implication with "[//][$Htr_inv][$HinvExt][]").
      iIntros (c sa E k) "!# #Hsub #Hin #Hconn %Φ !# Hshift".
      iApply ("Hread" $! c sa E k with "[$][$][$][$Hshift]").
    }
    iSplitR.
    {
      iClear "Hinit_kvs Hinit_cli Hread Hstart Hcom".
      iApply (write_implication with "[//][$Htr_inv][$HinvExt][]").
      iIntros (c sa E k v) "!# #Hsub #Hin #Hconn %Φ !# Hshift".
      iApply ("Hwrite" $! c sa E k v with "[$][$][$][$Hshift]").
    }
    iSplitR.
    {
      iClear "Hinit_kvs Hinit_cli Hwrite Hread Hcom".
      iApply (start_implication with "[//][$Htr_inv][$HinvExt][]").
      iIntros (c sa E) "!# #Hsub #Hconn %Φ !# Hshift".
      iApply ("Hstart" $! c sa E with "[$][$][$Hshift]").
    }
    iClear "Hinit_kvs Hinit_cli Hwrite Hread Hstart".
    iApply (commit_implication with "[//][$Htr_inv][$HinvExt][]").
    iIntros (c sa E) "!# #Hsub #Hconn %Φ !# Hshift".
    iApply ("Hcom" $! c sa E with "[$][$][$Hshift]").
  Qed.

End trace_proof.