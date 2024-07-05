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

  (* For the OwnLinTrace/OwnLinHist resources and rules we are reusing trace infrastructure *)

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

  Definition trace_lin_resources (lt t : list val) (γ : gname) : iProp Σ :=
    ∃ (m : gmap string bool), ⌜∀ (x : string), x ∉ tags t → x ∉ (dom m)⌝ ∗ ghost_map_auth γ (1%Qp) m ∗ 
      ∀ tag, ⌜(∃ e : val, e ∈ lt ∧ tagOfEvent e = Some tag)⌝ → ghost_map.ghost_map_elem γ tag (DfracOwn 1%Qp) true.
  
  Definition trace_post_resources (t : list val) (γ : gname) : iProp Σ :=
    ∃ (m : gmap string bool), ⌜∀ (x : string), x ∉ tags t → x ∉ (dom m)⌝ ∗ ghost_map_auth γ (1%Qp) m ∗ 
      ∀ tag, ⌜(∃ e : val, e ∈ t ∧ is_post_event e ∧ tagOfEvent e = Some tag)⌝ → ghost_map.ghost_map_elem γ tag (DfracOwn 1%Qp) true.

  Definition lin_tag_res tag γ := ghost_map.ghost_map_elem γ tag (DfracOwn 1%Qp) true.

  Lemma lin_tag_create lt t γ e tag : 
    trace_lin_resources lt t γ ∗ ⌜tag ∉ tags t ∧ tagOfEvent e = Some tag ∧ ¬is_post_event e⌝ ==∗
    trace_lin_resources lt (t ++ [e]) γ ∗ lin_tag_res tag γ.
  Proof.
    iIntros "((%m & %Hdom & Hghost_map & Himp) & (%Hnin & %Htag & %Hnot))".
    assert (m !! tag = None) as Hlookup_none.
    {
      apply not_elem_of_dom_1.
      by apply Hdom.
    }
    iMod (ghost_map_insert tag true Hlookup_none with "[$Hghost_map]") as "(Hghost_map & Hkey)".
    iModIntro.
    iFrame.
    iExists (<[tag:=true]> m).
    iFrame.
    iPureIntro.
    intros tag' Hnin'.
    assert (tag' ∉ tags t) as Hnin''.
    {
      specialize (tags_sub e t) as Hsub.
      set_solver.
    }
    specialize (Hdom tag' Hnin'').
    rewrite dom_insert.
    assert (tag ∈ tags (t ++ [e])) as Hin.
    {
      apply (tags_in e); last done.
      set_solver.
    }
    set_solver.
  Qed.

  Lemma lin_tag_add lt t γ e tag : 
    trace_lin_resources lt t γ ∗ lin_tag_res tag γ ∗ ⌜tagOfEvent e = Some tag⌝ -∗
    trace_lin_resources (lt ++ [e]) t γ.
  Proof.
    iIntros "((%m & %Hdom & Hghost_map & Himp) & Hkey & %Htag)".
    rewrite /trace_lin_resources.
    iExists m.
    iFrame.
    iSplit; first by iPureIntro.
    iIntros (tag') "%Hpure". 
    destruct Hpure as (e' & Hin & Htag').
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin | Hin].
    + iApply "Himp".
      iPureIntro.
      by exists e'.
    + assert (e' = e) as ->; first set_solver.
      assert (tag = tag') as ->; first set_solver.
      iFrame.
  Qed.

  Lemma lin_tag_add_post lt t γ e : 
    trace_lin_resources lt t γ -∗
    trace_lin_resources lt (t ++ [e]) γ.
  Proof.
    iIntros "(%m & %Hdom & Hghost_map & Himp)".
    rewrite /trace_lin_resources.
    iExists m.
    iFrame.
    iPureIntro.
    intros tag Hnin.
    apply Hdom.
    specialize (tags_sub e t) as Hsub.
    set_solver.
  Qed.

  Lemma lin_tag_not_in lt t γ tag : 
    trace_lin_resources lt t γ ∗ lin_tag_res tag γ -∗ ¬⌜(∃ e : val, e ∈ lt ∧ tagOfEvent e = Some tag)⌝.
  Proof.
    iIntros "((%m & %Hdom & Hghost_map & Himp) & Hkey)".
    iIntros "Hfalse".
    iDestruct ("Himp" with "[$Hfalse]") as "Hfalse".
    rewrite /lin_tag_res.
    iCombine "Hkey" "Hfalse" as "Hfalse".
    iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
    by rewrite dfrac_valid_own in Hfalse.
  Qed.

  Definition post_tag_res tag γ := ghost_map.ghost_map_elem γ tag (DfracOwn 1%Qp) true.

  Lemma post_tag_create t γ e tag : 
    trace_post_resources t γ ∗ ⌜tag ∉ tags t ∧ tagOfEvent e = Some tag ∧ ¬is_post_event e⌝ ==∗
    trace_post_resources (t ++ [e]) γ ∗ post_tag_res tag γ.
  Proof.
    iIntros "((%m & %Hdom & Hghost_map & Himp) & (%Hnin & %Htag & %Hnot))".
    assert (m !! tag = None) as Hlookup_none.
    {
      apply not_elem_of_dom_1.
      by apply Hdom.
    }
    iMod (ghost_map_insert tag true Hlookup_none with "[$Hghost_map]") as "(Hghost_map & Hkey)".
    iModIntro.
    iFrame.
    iExists (<[tag:=true]> m).
    iFrame.
    iSplitR.
    - iPureIntro.
      intros tag' Hnin'.
      assert (tag' ∉ tags t) as Hnin''.
      {
        specialize (tags_sub e t) as Hsub.
        set_solver.
      }
      specialize (Hdom tag' Hnin'').
      rewrite dom_insert.
      assert (tag ∈ tags (t ++ [e])) as Hin.
      {
        apply (tags_in e); last done.
        set_solver.
      }
      set_solver.
    - iIntros (tag') "%Hpure".
      iApply "Himp".
      iPureIntro.
      destruct Hpure as (e' & Hin & Hevent & Htag').
      exists e'.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin | Hin]; first done.
      assert (e = e') as ->; set_solver.
  Qed.

  Lemma post_tag_add t γ e tag : 
    trace_post_resources t γ ∗ post_tag_res tag γ ∗ ⌜tagOfEvent e = Some tag ∧ is_post_event e⌝ -∗
    trace_post_resources (t ++ [e]) γ.
  Proof.
    iIntros "((%m & %Hdom & Hghost_map & Himp) & Hkey & %Htag)".
    rewrite /trace_post_resources.
    iExists m.
    iFrame.
    iSplit.
    - iPureIntro.
      intros tag' Hin.
      apply Hdom.
      specialize(tags_sub e t) as Hsub.
      set_solver.
    - iIntros (tag') "%Hpure". 
      destruct Hpure as (e' & Hin & Htag').
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin | Hin].
      + iApply "Himp".
        iPureIntro.
        by exists e'.
      + assert (e' = e) as ->; first set_solver.
        assert (tag = tag') as ->; first set_solver.
        iFrame.
    Qed.

  Lemma post_tag_not_in t γ tag : 
    trace_post_resources t γ ∗ post_tag_res tag γ -∗ ¬⌜(∃ e : val, e ∈ t ∧ is_post_event e ∧ tagOfEvent e = Some tag)⌝.
  Proof.
    iIntros "((%m & %Hdom & Hghost_map & Himp) & Hkey)".
    iIntros "Hfalse".
    iDestruct ("Himp" with "[$Hfalse]") as "Hfalse".
    rewrite /lin_tag_res.
    iCombine "Hkey" "Hfalse" as "Hfalse".
    iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
    by rewrite dfrac_valid_own in Hfalse.
  Qed.

  (** Predicates for wrapped resources *)

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

  Definition trace_state_resources (lt : list val) (γm1 γmk : gname) (clients : gset socket_address) : iProp Σ := 
   ∃ (m1 : gmap socket_address (local_state * option val)), ghost_map_auth γm1 (1%Qp) m1 ∗ 
      ∃ (mk : gmap (socket_address * val) gname), ghost_map_auth γmk (1%Qp) mk ∗ 
        ∀ sa, ⌜sa ∈ clients⌝ →
        (((⌜m1 !! sa = None⌝ ∨ ⌜m1 !! sa = Some (CanStart, None)⌝) ∗ ⌜¬∃ c γ, mk !! (sa, c) = Some γ⌝) ∨ 
        (∃ s c γ (m : gmap Key (option val)), ⌜m1 !! sa = Some (s, Some c)⌝ ∗ 
          ghost_map_elem γmk (sa, c) DfracDiscarded γ ∗ ghost_map_auth γ (1%Qp) m ∗ 
          ((⌜s = CanStart⌝ ∗ 
            ([∗ set] k ∈ KVS_keys, ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov)) ∨ 
           (∃ domain sub_domain, ⌜s = Active domain⌝ ∗ ⌜sub_domain = domain ∩ KVS_keys⌝ ∗ (∃ e, ⌜open_start c e lt⌝) ∗ 
            ([∗ set] k ∈ KVS_keys ∖ sub_domain, ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ 
            (∀ k, ⌜k ∈ sub_domain⌝ → ∀ ov, ⌜m !! k = Some ov⌝ → ⌜latest_write c k ov lt⌝))))).

  Definition GlobalInvExt (γm1 γm2 γm3 γmk γl : gname) (clients : gset socket_address) : iProp Σ := 
    ∃ t lt T, trace_is t ∗ OwnLinTrace γl lt ∗ ⌜lin_trace_of lt t⌝ ∗ ⌜∀ t, t ∈ T → t ≠ []⌝ ∗
      ⌜extraction_of lt T⌝ ∗ ⌜valid_transactions T⌝ ∗ ⌜valid_sequence lt⌝ ∗
      trace_state_resources lt γm1 γmk clients ∗
      trace_lin_resources lt t γm2 ∗
      trace_post_resources t γm3.

  (** Wrapped resources *)

  Global Program Instance wrapped_resources (γm1 γm2 γm3 γmk γl : gname) (clients : gset socket_address) 
  `(res : !RU_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_ru ∗ inv KVS_InvName (GlobalInvExt γm1 γm2 γm3 γmk γl clients))%I;
      OwnMemKey k V := (OwnMemKey k V  ∗ (∀ v, ⌜v ∈ V⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
                        ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗ ∃ sa γ, ghost_map_elem γmk (sa, c) DfracDiscarded γ ∗ 
                             (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ ⌜sa ∈ clients⌝)%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ ghost_map_elem γm1 sa (DfracOwn 1%Qp) (s, Some c) ∗ ⌜sa ∈ clients⌝)%I; 
      IsConnected c sa := IsConnected c sa%I;
      KVS_ru := KVS_ru;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ ghost_map_elem γm1 sa (DfracOwn 1%Qp) (CanStart, None) ∗ ⌜sa ∈ clients⌝)%I;
      Seen k V := Seen k V%I;
    |}.
  Next Obligation.
    iIntros (??????????) "(Hkey & [%sa [%γ (Hghost_elem_per & Hghost_elem  & %Hin_sa)]])".
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
    iIntros (???????????????) "#(HGinv & Hinv) ((Hconn1 & Hrest1) & (Hconn2 & Hrest2))".
    iMod (res.(read_uncommitted.specs.resources.Connection_unique) 
      with "[$HGinv][$Hconn1 $Hconn2]") as "(Hconn1 & Hconn2 & Heq)"; first done.
    iModIntro.
    iFrame.
  Qed.

  Lemma init_client_implication γm1 γm2 γm3 γmk γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt γm1 γm2 γm3 γmk γl clients) -∗
    @init_client_proxy_spec _ _ _ _ lib res -∗
    @init_client_proxy_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γm1 γm2 γm3 γmk γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hinit_cli".
    rewrite /init_client_proxy_spec.
    iIntros (sa Φ) "!# (Hunall & Hsock & Hmes & (Hcan & (Hsa_pointer & %Hsa_in)) & Hfree) HΦ".
    rewrite /TC_init_client_proxy /KVS_wrapped_api /wrap_init_client_proxy.
    wp_pures.
    wp_bind (ast.Fresh _).
    iInv "HinvExt" as ">[%t [%lt [%T (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex 
      & %Hvalid_trans & %Hvalid_seq & Hstate_res & Hlin_res & Hpost_res)]]]" "Hclose".
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
      - apply (lin_trace_valid tag); try done.
        left.
        split.
        {
          rewrite /is_pre_event.
          do 4 right.
          rewrite /is_init_pre_event.
          by exists tag.
        }
        split; done.
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
    iMod (lin_tag_create lt t γm2 (#tag1, init_pre_emit_event)%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]].
      - rewrite /is_st_post_event in Hfalse.
        set_solver.
      - set_solver.
      - set_solver.
      - rewrite /is_wr_post_event in Hfalse.
        set_solver.
      - rewrite /is_cm_post_event in Hfalse.
        set_solver.
      - rewrite /is_init_post_event in Hfalse.
        set_solver.
    }
    iMod (post_tag_create t γm3 (#tag1, init_pre_emit_event)%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]].
      - rewrite /is_st_post_event in Hfalse.
        set_solver.
      - set_solver.
      - set_solver.
      - rewrite /is_wr_post_event in Hfalse.
        set_solver.
      - rewrite /is_cm_post_event in Hfalse.
        set_solver.
      - rewrite /is_init_post_event in Hfalse.
        set_solver.
    }
    iMod ("Hclose" with "[Htr_is HOwnLin Hlin_res Hpost_res Hstate_res]").
    {
      iNext.
      rewrite /GlobalInvExt.
      iExists (t ++ [(#tag1, init_pre_emit_event)%V]), lt, T.
      iFrame.
      iSplitR.
      - iPureIntro.
        apply (lin_trace_valid tag1); try done.
        left.
        split.
        {
          rewrite /is_pre_event.
          do 4 right.
          rewrite /is_init_pre_event.
          by exists tag1.
        }
        split; done.
      - do 3 (iSplitR; first by iPureIntro).
        by iPureIntro.
    }
    iModIntro.
    wp_pures.
    wp_apply ("Hinit_cli" $! sa with "[$Hunall $Hsock $Hmes $Hcan $Hfree]").
    iIntros (c) "(Hconn_state & #His_conn)".
    wp_pures.
    wp_bind (ast.Emit _).
    rewrite /init_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%t' [%lt' [%T' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & Hstate_res' & Hlin_res' & Hpost_res')]]]" "Hclose'".
    wp_apply (aneris_wp_emit with "[$Htr_inv $Htr_is']").
    {
      rewrite Hkvs_inv_name.
      solve_ndisj.
    }
    {
      rewrite /valid_trace_ru /valid_trace.
      exists lt'.
      split.
      - apply (lin_trace_valid tag1); try done.
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
    iDestruct (lin_tag_add_post lt' t' γm2 (#tag1, (c, #"InitPost"))%V with "[$Hlin_res']") as "Hlin_res'".
    iDestruct (post_tag_add t' γm3 (#tag1, (c, #"InitPost"))%V tag1 with "[$Hpost_res' $Hpost_tag_res]")
      as "Hpost_res'".
    {
      iPureIntro.
      simpl.
      split; first done.
      do 4 right.
      rewrite /is_init_post_event.
      by eexists _, _.
    }
    iDestruct "Hstate_res'" as "[%m1 (Hghost_map_m1 & [%mk (Hghost_map_mk & Hext_rest1')])]".
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
    iMod (ghost_map_alloc ((gset_to_gmap None KVS_keys : gmap Key (option val))))
      as "[%γ (Hghost_map_m & Hghost_elems_m)]".
    iMod (ghost_map_update (CanStart, Some c) with "[$Hghost_map_m1] [$Hsa_pointer]") 
      as "(Hghost_map_m1 & Hsa_pointer)".
    iMod (ghost_map_insert_persist (sa, c) γ Hlookup_none with "[$Hghost_map_mk]") as "(Hghost_map_mk & #Hkey_pers_mk)".
    iMod ("Hclose'" with "[Htr_is HOwnLin' Hghost_map_mk Hext_rest1' Hghost_map_m1 
      Hghost_map_m Hghost_elems_m Hlin_res' Hpost_res']").
    {
      iNext.
      rewrite /GlobalInvExt.
      iExists (t' ++ [(#tag1, (c, #"InitPost"))%V]), lt', T'.
      iFrame.
      iSplit.
      - iPureIntro.
        apply (lin_trace_valid tag1); try done.
        right.
        rewrite /is_init_post_event.
        set_solver.
      - do 4 (iSplit; first done).
        iExists (<[sa:=(CanStart, Some c)]> m1).
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
              rewrite big_sepM_gset_to_gmap.
              iApply (big_sepS_wand with "[$Hghost_elems_m]").
              iApply (big_sepS_intro).
              iModIntro.
              iIntros (k Hin) "Hkey".
              iExists None.
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
    }
    iModIntro.
    wp_pures.
    iApply "HΦ".
    rewrite /ConnectionState.
    simpl.
    by iFrame "∗#".
  Qed.

  Lemma read_implication γm1 γm2 γm3 γmk γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt γm1 γm2 γm3 γmk γl clients) -∗
    @read_spec _ _ _ _ lib res -∗
    @read_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γm1 γm2 γm3 γmk γl clients res).
  Proof.
  Admitted.

  Lemma write_implication γm1 γm2 γm3 γmk γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt γm1 γm2 γm3 γmk γl clients) -∗
    @write_spec _ _ _ _ lib res -∗
    @write_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γm1 γm2 γm3 γmk γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hwrite".
    rewrite /write_spec.
    iModIntro.
    iIntros (c sa E k v) "%Hsub %Hin #Hconn !# %Φ Hshift".
    rewrite /TC_write /KVS_wrapped_api /wrap_write.
    wp_pures.
    wp_bind (ast.Fresh _).
  Admitted.

  Lemma start_implication γm1 γm2 γm3 γmk γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt γm1 γm2 γm3 γmk γl clients) -∗
    @start_spec _ _ _ _ lib res -∗
    @start_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γm1 γm2 γm3 γmk γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hstart".
    rewrite /start_spec.
    iModIntro.
    iIntros (c sa E) "%Hsub #Hconn !# %Φ Hshift".
    rewrite /TC_start /KVS_wrapped_api /wrap_start.
    wp_pures.
    wp_bind (ast.Fresh _).
    rewrite /start_pre_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%t [%lt [%T 
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq 
      & Hstate_res & Hlin_res & Hpost_res)]]]" "Hclose".
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
      - apply (lin_trace_valid tag); try done.
        left.
        split.
        {
          rewrite /is_pre_event.
          left.
          rewrite /is_st_pre_event.
          by eexists _, _.
        }
        split; done.
      - split; first done.
        destruct (exists_execution T) as [Ex (Hbased & Hvalid_exec)].
        {
          intros t' Hin.
          destruct Hvalid_trans as (_ & _ & Hvalid_trans & _).
          destruct (Hvalid_trans t' Hin) as ([s [b Hlast]] & _).
          destruct t'; last done.
          by simpl in Hlast. 
        }
        eexists T, Ex.
        by do 3 (split; first done).
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
    iDestruct (alloc_trace_hist with "[$Htr_is]") as "(Htr_is & #Htr_hist)".
    iMod (lin_tag_create lt t γm2 (#tag1, (c, #"StPre"))%V with "[$Hlin_res]") 
      as "(Hlin_res & Hlin_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]].
      - rewrite /is_st_post_event in Hfalse.
        set_solver.
      - set_solver.
      - set_solver.
      - rewrite /is_wr_post_event in Hfalse.
        set_solver.
      - rewrite /is_cm_post_event in Hfalse.
        set_solver.
      - rewrite /is_init_post_event in Hfalse.
        set_solver.
    }
    iMod (post_tag_create t γm3 (#tag1, (c, #"StPre"))%V with "[$Hpost_res]") 
      as "(Hpost_res & Hpost_tag_res)".
    {
      iPureIntro.
      simpl.
      do 2 (split; first done).
      intros Hfalse.
      destruct Hfalse as [Hfalse | [[Hfalse | Hfalse] | [Hfalse | [Hfalse | Hfalse]]]].
      - rewrite /is_st_post_event in Hfalse.
        set_solver.
      - set_solver.
      - set_solver.
      - rewrite /is_wr_post_event in Hfalse.
        set_solver.
      - rewrite /is_cm_post_event in Hfalse.
        set_solver.
      - rewrite /is_init_post_event in Hfalse.
        set_solver.
    }
    iMod ("Hclose" with "[Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      rewrite /GlobalInvExt.
      iExists (t ++ [(#tag1, (c, #"StPre"))%V]), lt, T.
      iFrame.
      iSplitR.
      - iPureIntro.
        apply (lin_trace_valid tag1); try done.
        left.
        split.
        {
          rewrite /is_pre_event.
          left.
          rewrite /is_st_pre_event.
          by eexists _, _.
        }
        split; done.
      - do 3 (iSplitR; first by iPureIntro).
        by iPureIntro.
    }
    iModIntro.
    wp_pures.
    wp_apply "Hstart"; try done.
    iClear "Hstart".
    iMod "Hshift" as "[%m (((Hconn_state & Hsa_pointer & %Hsa_in) & Hkeys) & Hshift)]".
    iModIntro.
    iExists m.
    iFrame.
    rewrite big_sepM_sep.
    iDestruct "Hkeys" as "(Hkeys1 & Hkeys2)".
    iFrame.
    iModIntro.
    iIntros "(Hconn_state & Hkeys1 & Hkeys_conn)".
    iInv "HinvExt" as ">[%t' [%lt' [%T' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]]]" "Hclose'".
    simpl; rewrite /trace_state_resources.
    iDestruct "HstateRes'" as "(%m1' & Hghost_map_m1' & %mk' & Hghost_map_mk' & Hdisj_trace_res)".
    iDestruct (@ghost_map_lookup with "[$Hghost_map_m1'][$Hsa_pointer]") as "%Hlookup_m1'".
    iDestruct ("Hdisj_trace_res" $! sa Hsa_in) as "[(Hfalse & _) | Htrace_res]".
    {
      iDestruct "Hfalse" as "[%Hfalse | %Hfalse]"; set_solver.
    }
    iDestruct "Htrace_res" as "(%ls & %c' & %γ & %m' & %Hlookup_m1'' & #Hsa_c'_pointer 
      & Hghost_map_m' & [(-> & Hkeys_conn_res) | Hfalse])"; last first.
    {
      assert (ls = CanStart) as ->; first set_solver.
      by iDestruct "Hfalse" as "(%domain & %sub_domain & %Hfalse & _)".
    }
    iMod (ghost_map_update (Active (dom m), Some c) with "[$Hghost_map_m1'] [$Hsa_pointer]") 
      as "(Hghost_map_m1' & Hsa_pointer)".
    iAssert ((|==> (([∗ set] k ∈ KVS_keys, ghost_map_elem γ k (DfracOwn 1%Qp) None) ∗ 
              (∃ m'', ghost_map_auth γ 1 m'')))%I) 
      with "[Hkeys_conn_res Hghost_map_m']" as ">(Hkeys_conn_res & Hghost_map_m')".
    {
      iRevert "Hghost_map_m'".
      iRevert (m').
      iInduction KVS_keys as [|k KVS_Keys Hnin] "IH" using set_ind_L.
      - iIntros (m') "Hghost_map_m'".
        iModIntro. 
        iSplitR "Hghost_map_m'"; first done.
        iExists m'.
        iFrame.
      - iIntros (m') "Hghost_map_m'".
        rewrite big_sepS_union; last set_solver.
        iDestruct "Hkeys_conn_res" as "(Hkeys_conn_key & Hkeys_conn_res)".
        iMod ("IH" with "[$Hkeys_conn_res][$Hghost_map_m']") as "(Hkeys_conn_res & [%m'' Hghost_map'])".
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
    iPoseProof (lin_tag_not_in lt' t' γm2 with "[$Hlin_res' $Hlin_tag_res]") as "%Hnot_lin_in".
    iPoseProof (post_tag_not_in t' γm3 with "[$Hpost_res' $Hpost_tag_res]") as "%Hnot_post_in".
    iDestruct (lin_tag_add lt' t' γm2 (#tag1, (c, #"StLin"))%V tag1 with "[$Hlin_res' $Hlin_tag_res]") 
      as "Hlin_res'".
    {
      iPureIntro.
      by simpl. 
    }
    iMod ("Hclose'" with "[Htr_is' HOwnLin' Hghost_map_mk' Hghost_map_m' 
      Hghost_map_m1' Hkeys_conn_res2 Hlin_res' Hpost_res']").
    {
      iModIntro.
      rewrite /GlobalInvExt.
      iExists t', (lt' ++ [(#tag1, (c, #"StLin"))%V]), T'.
      iFrame.
      iSplitR.
      {
        iPureIntro.
        apply lin_trace_start_lin; try done.
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
        apply valid_sequence_st_lin; try done.
        admit.
      }
      admit.
    }
    iMod ("Hshift" with "[Hkeys1 Hkeys2 Hkeys_conn Hsa_pointer Hkeys_conn_res1 Hconn_state]").
    {
      iFrame.
      iSplitR; first by iPureIntro.
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
        iSplitL; last done.
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
        iSplitL; last done.
        iIntros (Hkey_in).
        set_solver.
    }
    iModIntro.
    rewrite /start_post_emit_event.
    wp_pures.
    wp_bind (Emit _).
    iInv "HinvExt" as ">[%t'' [%lt'' [%T'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]]]" "Hclose''".
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
      rewrite /valid_trace_ru /valid_trace.
      exists lt''.
      split.
      - apply (lin_trace_valid tag1); try done.
        do 2 right.
        split.
        + left.
          by eexists _, _.
        + exists (#tag1, (c, #"StLin"))%V.
          split; last done.
          by simpl.
      - split; first done.
        destruct (exists_execution T'' Hno_empty'') as (exec & Hexec_props).
        by exists T'', exec.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γm2 (#tag1, (c, #"StPost"))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γm3 (#tag1, (c, #"StPost"))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
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
      iExists (t'' ++ [(#tag1, (c, #"StPost"))%V]), lt'', T''.
      iFrame.
      iSplitR.
      - iPureIntro.
        apply (lin_trace_valid tag1); try done.
        do 2 right.
        split.
        + left.
          by eexists _, _.
        + exists (#tag1, (c, #"StLin"))%V.
          split; last done.
          by simpl.
      - do 3 (iSplitR; first done).
        by iPureIntro.
    }
    iModIntro.
    wp_pures.
    iFrame.
  Admitted.

  Lemma commit_implication γm1 γm2 γm3 γmk γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt γm1 γm2 γm3 γmk γl clients) -∗
    @commit_spec _ _ _ _ lib res -∗
    @commit_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γm1 γm2 γm3 γmk γl clients res).
  Proof.
  Admitted.

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
    iMod (ghost_map_alloc_empty (K:=string) (V:=bool)) as "[%γm3 Hghost_map_m3]".
    iMod (ghost_map_alloc_empty (K:=socket_address * val) (V:=gname)) as "[%γmk Hghost_map_mk]".
    iMod (own_alloc (● gmap_of_trace 0 ([] : list val) ⋅ 
      ◯ gmap_of_trace 0 ([] : list val))) as (γl) "Hltrace".
    {
      apply auth_both_valid. 
      split; first done. 
      by apply gmap_of_trace_valid.
    }
    iDestruct "Hltrace" as "[Hltrace Hlhist]".
    iMod (inv_alloc KVS_InvName ⊤ (GlobalInvExt γm1 γm2 γm3 γmk γl clients) with 
      "[Htr Hghost_map_m1 Hghost_map_m2 Hghost_map_m3 Hghost_map_mk Hltrace Hlhist]") as "#HinvExt".
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
        do 3 (split; first set_solver).
        split; last set_solver.
        rewrite /rel_list.
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        intros.
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
      iSplitR "Hghost_map_m2 Hghost_map_m3".
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
      - iSplitL "Hghost_map_m2". 
        + iExists ∅.
          iFrame.
          iSplitL.
          * iPureIntro.
            set_solver.
          * iIntros.
            set_solver.
        + iExists ∅.
          iFrame.
          iSplitL.
          * iPureIntro.
            set_solver.
          * iIntros.
            set_solver.
    }
    iModIntro.
    iExists (wrapped_resources γm1 γm2 γm3 γmk γl clients res).
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
