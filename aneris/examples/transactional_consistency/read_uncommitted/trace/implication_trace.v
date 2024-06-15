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
From aneris.examples.transactional_consistency Require Import resource_algebras user_params aux_defs state_based_model.

Section trace_proof.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params}.

  Definition trace_inv_name := nroot.@"trinv".

  (** Ghost theory for wrapped resources *)

  (* For the OwnLinTrace/OwnLinHist resources and 
     rules we are reusing trace infrastructure *)

  Definition OwnLinHist (γ : gname) (l : list val) : iProp Σ :=
    own γ (◯ (gmap_of_trace 0 l)).

  Definition OwnLinTrace (γ : gname) (l : list val) : iProp Σ := 
    own γ (● gmap_of_trace 0 l) ∗ OwnLinHist γ l.

  Lemma own_lin_hist (γ : gname) (l : list val) :
    OwnLinTrace γ l ==∗ OwnLinTrace γ l ∗ OwnLinHist γ l.
  Proof.
    rewrite /OwnLinTrace.
    iIntros "(H1 & #H2)".
    iModIntro.
    iFrame "#∗".
  Qed.

  Lemma own_lin_prefix (γ : gname) (l h : list val) :
    OwnLinTrace γ l ∗ OwnLinHist γ h -∗
    OwnLinTrace γ l ∗ OwnLinHist γ h ∗ ⌜h `prefix_of` l⌝.
  Proof.
    rewrite /OwnLinTrace /OwnLinHist.
    iIntros "((H1 & H2) & H3)".
    iDestruct (own_op with "[$H1 $H3]") as "H".
    iDestruct (own_valid with "H") as %[Hsub Hvalid]%auth_both_valid_discrete.
    iDestruct "H" as "(H1 & H3)".
    iFrame.
    iPureIntro.
    eapply gmap_of_trace_hist_valid_prefix; eauto.
  Qed.

  Lemma own_lin_add (γ : gname) (l: list val) (v : val) :
    OwnLinTrace γ l ==∗ OwnLinTrace γ (l ++ [v]).
  Proof.
    rewrite /OwnLinTrace /OwnLinHist.
    iIntros "(H1 & H2)".
    rewrite gmap_of_trace_snoc Nat.add_0_l.
    iMod (own_update_2 with "H1 H2") as "[H1 H2]".
    apply auth_update.
    eapply (alloc_local_update _ _ (length l : nat) (to_agree v)); try done.
    { 
      eapply not_elem_of_dom.
      rewrite gmap_of_trace_dom.
      intro Hfalse. 
      lia. 
    }
    iModIntro. 
    iFrame.
  Qed.

  (** Predicates for wrapped resources *)

  Definition last_commit (c le : val) (ltrace : list val) : Prop := 
   is_cm_lin_event le ∧ connOfEvent le = Some c ∧ le ∈ ltrace ∧
   (∀ i j le', connOfEvent le' = Some c →
      ltrace !! j = Some le' →
      ltrace !! i = Some le →
      j <= i).

  Definition open_start (c le : val) (ltrace : list val) : Prop := 
    le ∈ ltrace ∧ (∃ tag, le = (#tag, (c, #"StLin"))%V) ∧
    (∀ i j le', ltrace !! i = Some le → 
      i < j → 
      ltrace !! j = Some le' →
      connOfEvent le' = Some c →
      (is_wr_lin_event le' ∨ is_rd_lin_event le')).

  Definition latest_write (c : val) (k : Key) (ov : option val) (ltrace : list val ) : Prop := 
    ∃ le, le ∈ ltrace ∧ 
      ((∃ tag, ov = None ∧ le = (#tag, (c, (#"RdLin", (#k, NONEV))))%V) ∨ 
      (∃ tag v, ov = Some v ∧ le = (#tag, (c, (#"RdLin", (#k, SOMEV v))))%V)) ∧
      (∀ i j le', 
        ((∃ tag, le' = (#tag, (c, (#"RdLin", (#k, NONEV))))%V) ∨ 
        (∃ tag v, le = (#tag, (c, (#"RdLin", (#k, SOMEV v))))%V)) →
        ltrace !! j = Some le' →
        ltrace !! i = Some le →
        j <= i).
     
  Definition tag_eq (e1 e2 : val) : Prop := ∃ tag, tagOfEvent e1 = Some tag ∧ tagOfEvent e2 = Some tag.

  (** Extended global invaraint *)

  Definition GlobalInvExt (γm1 γm2 γmk γl : gname) (clients : gset socket_address) : iProp Σ := 
    ∃ t lt T, trace_is t ∗ OwnLinTrace γl lt ∗ ⌜lin_trace_of lt t⌝ ∗ 
      ⌜extraction_of lt T⌝ ∗ ⌜valid_transactions T⌝ ∗ ⌜valid_sequence lt⌝ ∗
      (∃ (m1 : gmap socket_address (local_state * option val)), ghost_map_auth γm1 (1%Qp) m1 ∗ 
       ∃ (mk : gmap (socket_address * val) gname), ghost_map_auth γmk (1%Qp) mk ∗ 
       ∀ sa, ⌜sa ∈ clients⌝ →
        (((⌜m1 !! sa = None⌝ ∨ ⌜m1 !! sa = Some (CanStart, None)⌝) ∗ ⌜¬∃ c γ, mk !! (sa, c) = Some γ⌝) ∨ 
        (∃ s c γ (m : gmap Key (option val)), ⌜m1 !! sa = Some (s, Some c)⌝ ∗ 
          ghost_map_elem γmk (sa, c) DfracDiscarded γ ∗ ghost_map_auth γ (1%Qp) m ∗ 
          ((⌜s = CanStart⌝ ∗ (∃ le, ⌜last_commit c le lt⌝) ∗ 
            (∀ k, ⌜k ∈ KVS_keys⌝ → ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov)) ∨ 
          (∃ domain, ⌜s = Active domain⌝ ∗ (∃ e, ⌜open_start c e lt⌝) ∗ 
            (∀ k, ⌜k ∈ KVS_keys ∖ domain⌝ → ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ 
            (∀ k, ⌜k ∈ domain⌝ → ∀ ov, ⌜m !! k = Some ov⌝ → ⌜latest_write c k ov lt⌝ )))))) ∗ 
      (∃ (m2 : gmap string bool), ⌜∀ (x : string), x ∈ (dom m2) → x ∈ tags t⌝ ∗ ghost_map_auth γm2 (1%Qp) m2 ∗ 
        (∀ e_pre tag, ⌜e_pre ∈ t⌝ → (⌜is_rd_pre_event e_pre ∨ is_wr_pre_event e_pre ∨ is_cm_pre_event e_pre⌝) → 
          ⌜tagOfEvent e_pre = Some tag⌝ → (∃ e_lin, ⌜e_lin ∈ lt⌝ ∧ ⌜tag_eq e_pre e_lin⌝) → 
          ghost_map.ghost_map_elem γm2 tag (DfracOwn 1%Qp) true)).

  (** Wrapped resources *)

  Global Program Instance wrapped_resources (γm1 γm2 γmk γl : gname) (clients : gset socket_address) 
  `(res : !RU_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_ru ∗ inv KVS_InvName (GlobalInvExt γm1 γm2 γmk γl clients))%I;
      OwnMemKey k V := (OwnMemKey k V  ∗ (∀ v, ⌜v ∈ V⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
                        ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗ ∃ sa γ, ghost_map_elem γmk (sa, c) DfracDiscarded γ ∗ 
                             ghost_map_elem γ k (DfracOwn 1%Qp) ov ∗ ⌜k ∈ KVS_keys⌝ ∗ ⌜sa ∈ clients⌝)%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ ghost_map_elem γm1 sa (DfracOwn 1%Qp) (s, Some c) ∗ ⌜sa ∈ clients⌝)%I; 
      IsConnected c sa := IsConnected c sa%I;
      KVS_ru := KVS_ru;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ ghost_map_elem γm1 sa (DfracOwn 1%Qp) (CanStart, None) ∗ ⌜sa ∈ clients⌝)%I;
      Seen k V := Seen k V%I;
    |}.
  Next Obligation.
    iIntros (?????????) "(Hkey & [%sa [%γ (Hghost_elem_per & Hghost_elem & %Hin_k & %Hin_sa)]])".
    iDestruct (res.(read_uncommitted.specs.resources.OwnLocalKey_serializable) 
      with "Hkey") as "(Hkey & Hser)".
    iFrame.
    iExists sa, γ.
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (???????????) "#(HGinv & Hinv) (#Hseen & Hkey & Hin)".
    iMod (res.(read_uncommitted.specs.resources.Seen_valid) 
      with "[$HGinv][$Hseen $Hkey]") as "(Hkey & Hsub)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    iIntros (??????????) "#(HGinv & Hinv) (Hkey & Hin)".
    iMod (res.(read_uncommitted.specs.resources.Seen_creation) 
      with "[$HGinv][$Hkey]") as "(Hkey & #Hseen)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    iIntros (??????????????) "#(HGinv & Hinv) ((Hconn1 & Hrest1) & (Hconn2 & Hrest2))".
    iMod (res.(read_uncommitted.specs.resources.Connection_unique) 
      with "[$HGinv][$Hconn1 $Hconn2]") as "(Hconn1 & Hconn2 & Heq)"; first done.
    iModIntro.
    iFrame.
  Qed.

  Lemma library_implication  (clients : gset socket_address) (lib : KVS_transaction_api) :
    ((RU_spec clients lib) ∗ trace_is [] ∗ 
      trace_inv trace_inv_name valid_trace_ru ∗ ⌜KVS_InvName = nroot .@ "kvs_inv"⌝) ={⊤}=∗ 
    RU_spec clients (KVS_wrapped_api lib).
  Proof.
    iIntros "([%res (Hkeys & Hkvs_init & #Hglob_inv & Hcan_conn & 
      (#Hinit_kvs & #Hinit_cli & #Hread & #Hwrite & #Hstart & #Hcom))] & Htr & #Htr_inv & %Hkvs_inv_name)".    
    iMod (ghost_map_alloc ((gset_to_gmap (CanStart, None) clients : 
      gmap socket_address (local_state * option val))))
      as "[%γm1 (Hghost_map_m1 & Hghost_elems_m1)]".
    iMod (ghost_map_alloc_empty (K:=string) (V:=bool)) as "[%γm2 Hghost_map_m2]".
    iMod (ghost_map_alloc_empty (K:=socket_address * val) (V:=gname)) as "[%γmk Hghost_map_mk]".
    iMod (own_alloc (● gmap_of_trace 0 ([] : list val) ⋅ 
      ◯ gmap_of_trace 0 ([] : list val))) as (γl) "Hltrace".
    {
      apply auth_both_valid. 
      split; first done. 
      by apply gmap_of_trace_valid.
    }
    iDestruct "Hltrace" as "[Hltrace Hlhist]".
    iMod (inv_alloc KVS_InvName ⊤ (GlobalInvExt γm1 γm2 γmk γl clients) with 
      "[Htr Hghost_map_m1 Hghost_map_m2 Hghost_map_mk Hltrace Hlhist]") as "#HinvExt".
    {
      iNext.
      rewrite /GlobalInvExt.
      iExists [], [], [].
      iFrame.
      simpl.
      iSplitR.
      {
        iPureIntro.
        rewrite /lin_trace_of.
        do 4 (split; first set_solver).
        split; last set_solver.
        rewrite /rel_list.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /extraction_of.
        do 2 (split; first set_solver).
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /valid_transactions.
        do 4 (split; first set_solver).
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /valid_sequence.
        split; intros; set_solver.
      }
      iSplitR "Hghost_map_m2".
      - iExists (gset_to_gmap (CanStart, None) clients).
        iFrame.
        iExists ∅.
        iFrame.
        iIntros (sa) "%Hin_sa".
        iLeft.
        iSplit.
        + iRight.
          iPureIntro.
          by rewrite lookup_gset_to_gmap_Some.
        + iPureIntro.
          set_solver.
      - iExists ∅.
        iFrame.
        iSplitL.
        + iPureIntro.
          set_solver.
        + iIntros.
          set_solver.
    }
    iModIntro.
    iExists (wrapped_resources γm1 γm2 γmk γl clients res).
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
    iSplitL "Hghost_elems_m1 Hcan_conn".
    {
      simpl.
      rewrite big_sepM_gset_to_gmap.
      rewrite big_sepS_sep.
      iFrame.
      iApply (big_sepS_mono with "[$Hghost_elems_m1]").
      iIntros (sa Hin) "Hkey".
      by iFrame.
    }
    iSplitR.
    {
      (* init_client_proxy method *)
      iClear "Hinit_kvs Hread Hwrite Hstart Hcom".
      rewrite /init_client_proxy_spec.
      iIntros (sa Φ) "!# (Hunall & Hsock & Hmes & (Hcan & (Hsa_pointer & %Hsa_in)) & Hfree) HΦ".
      rewrite /TC_init_client_proxy /KVS_wrapped_api /wrap_init_client_proxy.
      wp_pures.
      wp_bind (ast.Fresh _).
      iInv "HinvExt" as ">[%t [%lt [%T (Htr_is & HOwnLin & %HlinOf & %Hex & %Hvalid_trans & %Hvalid_seq & Hrest)]]]" "Hclose".
      wp_apply (aneris_wp_fresh with "[$Htr_inv $Htr_is]").
      {
        rewrite Hkvs_inv_name.
        solve_ndisj.
      }
      {
        intros tag Hnin.
        rewrite /valid_trace_ru /valid_trace.
        exists lt.
        split.
        - apply (init_valid tag); try done.
          left.
          rewrite /is_init_pre_event.
          by exists tag.
        - split; first done.
          destruct (exists_execution T) as [E (Hbased & Hvalid_exec)].
          {
            intros t' Hin.
            destruct Hvalid_trans as (_ & _ & Hvalid_trans & _).
            destruct (Hvalid_trans t' Hin) as ([s [b Hlast]] & _).
            destruct t'; last done.
            by simpl in Hlast. 
          }
          eexists T, E.
          by do 3 (split; first done).
      }
      iIntros (tag1) "(Htr_is & %Htag1_nin)".
      iMod ("Hclose" with "[Htr_is HOwnLin Hrest]").
      {
        iNext.
        rewrite /GlobalInvExt.
        iDestruct "Hrest" as "(Hrest1 & [%m2 (%Hsub_eq & Hghost_map & Himp)])". 
        iExists (t ++ [(#tag1, init_pre_emit_event)%V]), lt, T.
        iFrame.
        iSplitR.
        - iPureIntro.
          apply (init_valid tag1); try done.
          left.
          rewrite /is_init_pre_event.
          by exists tag1.
        - do 3 (iSplitR; first by iPureIntro).
          iExists m2.
          iFrame.
          iSplitR; first iPureIntro; first set_solver.
          iIntros (e_pre tag) "%He_pre_in %His_rd_wr_cm %Htag_of %Hlin_exist".
          rewrite elem_of_app in He_pre_in.
          destruct He_pre_in as [He_pre_in | He_pre_in].
          + iApply ("Himp" $! e_pre); try done. 
          + exfalso. 
            rewrite elem_of_list_singleton in He_pre_in.
            subst.
            rewrite /init_pre_emit_event in His_rd_wr_cm.
            destruct His_rd_wr_cm as [Hfalse | His_rd_wr_cm].
            * by destruct Hfalse as [tag' [c Hfalse]]. 
            * destruct His_rd_wr_cm as [Hfalse | Hfalse].
              -- by destruct Hfalse as [tag' [c [k [v Hfalse]]]].
              -- by destruct Hfalse as [tag' [b Hfalse]].
      }
      iModIntro.
      wp_pures.
      wp_apply ("Hinit_cli" $! sa with "[$Hunall $Hsock $Hmes $Hcan $Hfree]").
      iIntros (c) "(Hconn_state & #His_conn)".
      wp_pures.
      wp_bind (ast.Emit _).
      rewrite /init_post_emit_event.
      wp_pures.
      iInv "HinvExt" as ">[%t' [%lt' [%T' (Htr_is' & HOwnLin' & %HlinOf' & %Hex' & %Hvalid_trans' & %Hvalid_seq' & Hext_rest')]]]" "Hclose'".
      wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is']").
      {
        rewrite Hkvs_inv_name.
        solve_ndisj.
      }
      {
        rewrite /valid_trace_ru /valid_trace.
        exists lt'.
        split.
        - apply (init_valid tag1); try done.
          right.
          rewrite /is_init_post_event.
          set_solver.
        - split; first done.
          destruct (exists_execution T') as [E' (Hbased' & Hvalid_exec')].
          {
            intros t'' Hin.
            destruct Hvalid_trans' as (_ & _ & Hvalid_trans' & _).
            destruct (Hvalid_trans' t'' Hin) as ([s [b Hlast]] & _).
            destruct t''; last done.
            by simpl in Hlast. 
          }
          eexists T', E'.
          by do 3 (split; first done).
      }
      iIntros "Htr_is".
      iDestruct "Hext_rest'" as "([%m1 (Hghost_map_m1 & [%mk (Hghost_map_mk & Hext_rest1')])] 
        & [%m2 (%Hsub_eq & Hghost_map_m2 & Himp)])".
      iDestruct (@ghost_map_lookup with "[$Hghost_map_m1][$Hsa_pointer]") as "%Hlookup".
      iAssert (⌜mk !! (sa, c) = None⌝%I) as "%Hlookup_none".
      {
        iDestruct ("Hext_rest1'" $! sa Hsa_in) as "[(_ & %Hnot_lookup)|[%s [%c' [%γ [%m (%Hfalse & _)]]]]]".
        - iPureIntro. 
          destruct (mk !! (sa, c)) as [γ|] eqn:Hfalse; last done.
          exfalso.
          apply Hnot_lookup.
          by exists c, γ.
        - set_solver. 
      }
      (* iMod (ghost_map_alloc_empty (K:=string) (V:=option val)) as "[%γ Hghost_map_m]". *)
      iMod (ghost_map_alloc ((gset_to_gmap None KVS_keys : gmap Key (option val))))
        as "[%γ (Hghost_map_m & Hghost_elems_m)]".
      iMod (ghost_map_update (CanStart, Some c) with "[$Hghost_map_m1] [$Hsa_pointer]") 
        as "(Hghost_map_m1 & Hsa_pointer)".
      iMod (ghost_map_insert_persist (sa, c) γ Hlookup_none with "[$Hghost_map_mk]") as "(Hghost_map_mk & #Hkey_pers_mk)".
      iMod ("Hclose'" with "[Htr_is HOwnLin' Hghost_map_mk Hext_rest1' Himp Hghost_map_m1 
        Hghost_map_m2 Hghost_map_m Hghost_elems_m]").
      {
        iNext.
        rewrite /GlobalInvExt.
        iExists (t' ++ [(#tag1, (c, #"InitPost"))%V]), lt', T'.
        iFrame.
        iSplit.
        - iPureIntro.
          apply (init_valid tag1); try done.
          right.
          rewrite /is_init_post_event.
          set_solver.
        - do 3 (iSplit; first done).
          iSplitR "Himp Hghost_map_m2".
          + iExists (<[sa:=(CanStart, Some c)]> m1).
            iFrame.
            iExists (<[(sa, c):=γ]> mk).
            iFrame.
            iIntros (sa' Hsa'_in).
            destruct (decide (sa' = sa)) as [->|Hneq].
            * iRight.
              iExists CanStart, c, γ, (gset_to_gmap None KVS_keys).
              iSplit.
              -- iPureIntro.
                 by rewrite lookup_insert.
              -- iFrame "∗#".
                 iLeft.
                 iSplit; first done.
                 iSplit.
                 ++ admit.
                 ++ iIntros (k Hk_in).
                    iExists None.
                    assert (KVS_keys = {[k]} ∪ (KVS_keys ∖ {[k]})) as ->.
                    {
                      by apply union_difference_singleton_L.
                    }
                   rewrite gset_to_gmap_union_singleton.
                   rewrite big_sepM_insert_delete.
                   iDestruct "Hghost_elems_m" as "(Hghost_elem & Hghost_elems_m)".
                   iFrame.
            * rewrite lookup_insert_ne; last set_solver.
              iFrame.
              iDestruct ("Hext_rest1'" $! sa' Hsa'_in) as "[(Hext_rest1'_or & %Hext_rest1'_not) | Hext_rest1']";
                 last set_solver.
              iLeft.
              iFrame.
              iPureIntro.
              intro Hexists.
              destruct Hexists as [c' [γ' Hexists]].
              apply Hext_rest1'_not.
              exists c', γ'.
              by rewrite lookup_insert_ne in Hexists; last set_solver.
          + iExists m2.
            iFrame.
            iSplitR; first iPureIntro; first set_solver.
            iIntros (e_pre tag) "%He_pre_in %His_rd_wr_cm %Htag_of %Hlin_exist".
            rewrite elem_of_app in He_pre_in.
            destruct He_pre_in as [He_pre_in | He_pre_in].
            * iApply ("Himp" $! e_pre); try done. 
            * exfalso. 
              rewrite elem_of_list_singleton in He_pre_in.
              subst.
              rewrite /init_pre_emit_event in His_rd_wr_cm.
              destruct His_rd_wr_cm as [Hfalse | His_rd_wr_cm].
              -- by destruct Hfalse as [tag' [c' Hfalse]]. 
              -- destruct His_rd_wr_cm as [Hfalse | Hfalse].
                 ++ by destruct Hfalse as [tag' [c' [k' [v' Hfalse]]]].
                 ++ by destruct Hfalse as [tag' [b' Hfalse]].
      }
      iModIntro.
      wp_pures.
      iApply "HΦ".
      rewrite /ConnectionState.
      simpl.
      by iFrame "∗#".
    }
    iSplitR.
    {
      (* read method *)
      iClear "Hinit_kvs Hinit_cli Hwrite Hstart Hcom".
      rewrite /read_spec.
      admit.
    }
    iSplitR.
    {
      admit.
    }
    iSplitR.
    {
      admit.
    }
    admit.
  Admitted.

End trace_proof.