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

  Definition latest_write (c : val) (k : Key) (v : val) (ltrace : list val) : Prop := 
    ∃ le tag v, le ∈ ltrace ∧ le = (#tag, (c, (#"WrLin", (#k, v))))%V ∧
      (∀ le', le' ∈ ltrace → (∃ tag' v', le' = (#tag', (c, (#"WrLin", (#k, v'))))%V) → le' ≠ le → rel_list ltrace le' le).

  Definition tag_eq (e1 e2 : val) : Prop := ∃ tag, tagOfEvent e1 = Some tag ∧ tagOfEvent e2 = Some tag.

  Definition no_emit_with_address (sa : socket_address) (trace : list val) `(res : !RU_resources Mdl Σ)  : Prop := 
    ¬∃ e c, e ∈ trace ∧ connOfEvent e = Some c ∧ extract c = Some #sa.

  Definition active_trace_resources lt s c γ (m : gmap Key (option val)) : iProp Σ :=
    ∃ domain sub_domain tail, ⌜s = Active domain⌝ ∗ 
      ⌜sub_domain = domain ∩ KVS_keys⌝ ∗ ⌜open_start c lt tail⌝ ∗ 
      ([∗ set] k ∈ KVS_keys ∖ sub_domain, ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ 
      (∀ k, ⌜k ∈ sub_domain⌝ → ∀ v, ⌜m !! k = Some (Some v)⌝ → ⌜latest_write c k v tail⌝).

  Definition inactive_trace_resources lt s c γ : iProp Σ :=
    ⌜s = CanStart⌝ ∗ ⌜commit_closed c lt⌝ ∗
    ([∗ set] k ∈ KVS_keys, ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov).

  Definition initialized_trace_resources lt sa γmname `(res : !RU_resources Mdl Σ)
  (mstate : gmap socket_address (local_state * option val)) : iProp Σ :=
    ∃ s c γ (m : gmap Key (option val)), ⌜mstate !! sa = Some (s, Some c)⌝ ∗
      ⌜extract c = Some #(LitSocketAddress sa)⌝ ∗ 
      ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
      ghost_map_auth γ (1%Qp) m ∗ 
      ⌜(∃ e, e ∈ lt ∧ connOfEvent e = Some c ∧ is_in_lin_event e)⌝ ∗ 
      (inactive_trace_resources lt s c γ ∨ active_trace_resources lt s c γ m).

  Definition unnitialized_trace_resources sa (mstate : gmap socket_address (local_state * option val)) 
  (mname : gmap socket_address (gname * val)) t `(res : !RU_resources Mdl Σ) : Prop := 
    (mstate !! sa = None ∨ mstate !! sa = Some (CanStart, None)) ∧ 
    (¬∃ p, mname !! sa = Some p) ∧ no_emit_with_address sa t res.

  Definition trace_state_resources (t lt : list val) (γmstate γmname : gname) (clients : gset socket_address) 
  `(res : !RU_resources Mdl Σ) : iProp Σ := 
    ∃ (mstate : gmap socket_address (local_state * option val)), ghost_map_auth γmstate (1%Qp) mstate ∗ 
      ∃ (mname : gmap socket_address (gname * val)), ghost_map_auth γmname (1%Qp) mname ∗ 
        ([∗ set] sa ∈ clients, (⌜unnitialized_trace_resources sa mstate mname t res⌝ ∨ 
          initialized_trace_resources lt sa γmname res mstate)).

  Definition GlobalInvExt `(res : !RU_resources Mdl Σ) (γmstate γmlin γmpost γmname γl : gname) (clients : gset socket_address) : iProp Σ := 
    ∃ t lt T, trace_is t ∗ OwnLinTrace γl lt ∗ ⌜lin_trace_of lt t⌝ ∗ ⌜∀ t, t ∈ T → t ≠ []⌝ ∗
      ⌜extraction_of lt T⌝ ∗ ⌜valid_transactions T⌝ ∗ ⌜valid_sequence lt⌝ ∗
      trace_state_resources t lt γmstate γmname clients res ∗
      trace_lin_resources lt t γmlin ∗
      trace_post_resources t γmpost.

  (** Wrapped resources *)

  Global Program Instance wrapped_resources (γmstate γmlin γmpost γmname γl : gname) (clients : gset socket_address) 
  `(res : !RU_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_ru ∗ inv KVS_InvName (GlobalInvExt res γmstate γmlin γmpost γmname γl clients))%I;
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

  (** Helper lemmas *)

  Lemma trace_state_resources_init_imp t lt γmstate γmname clients res tag : 
    trace_state_resources t lt γmstate γmname clients res -∗
    trace_state_resources (t ++ [(#tag, init_pre_emit_event)%V]) lt γmstate γmname clients res.
  Proof.
    iIntros "(%mstate & Hmap_mstate & %mname & Hmap_mname & Hres)".
    iExists mstate.
    iFrame.
    iExists mname.
    iFrame.
    iApply (big_sepS_wand with "[$Hres]").
    iApply big_sepS_intro.
    iModIntro.
    iIntros (sa Hin) "Hdisj".
    iDestruct "Hdisj" as "[%Hres|Hres]".
    - destruct Hres as (Hlookup & Hnot & Hemit).
      iLeft.
      iPureIntro.
      split_and!; try done.
      intros (e & c & Hin_e & Hconn & Hextract).
      apply Hemit.
      exists e, c.
      split; last set_solver.
      rewrite elem_of_app in Hin_e.
      destruct Hin_e as [Hin_e|Hin_e]; first done.
      assert (e = (#tag, init_pre_emit_event)%V) as ->; first set_solver.
      rewrite /init_pre_emit_event in Hconn.
      by simpl in Hconn.
    - iRight.
      iFrame.
  Qed.

  Lemma commit_closed_neq `(res : !RU_resources Mdl Σ) sa sa' c c' lt e : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfEvent e = Some c →
    commit_closed c' lt →
    commit_closed c' (lt ++ [e]).
  Proof.
    intros Hneq Hextract Hextract' Hconn Hclosed.
    intros e_st Hin Hconn' Hevent.
    rewrite elem_of_app in Hin.
    assert (c ≠ c') as Hneq'; first set_solver.
    destruct Hin as [Hin|Hin]; last set_solver.
    destruct (Hclosed e_st Hin Hconn' Hevent) as (e_cm & Hconn'' & Hevent' & Hrel & Hnot).
    exists e_cm.
    do 2 (split; first done).
    split; first by apply rel_list_imp.
    intros (e_st' & Hconn''' & Hevent'' & Hrel1 & Hrel2).
    apply Hnot.
    exists e_st'.
    split_and!; try done; apply (rel_list_last_neq lt _ _ e); set_solver.
  Qed.

  Lemma open_start_neq `(res : !RU_resources Mdl Σ) sa sa' c c' lt tail e : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfEvent e = Some c →
    open_start c' lt tail →
    open_start c' (lt  ++ [e]) (tail ++ [e]).
  Proof.
    intros Hneq Hextract Hextract' Hconn (le & l & Heq & Hclosed & ((tag & ->) & Hall)).
    exists (#tag, (c', #"StLin"))%V, l.
    split; last set_solver.
    rewrite Heq.
    by do 2 rewrite -app_assoc.
  Qed.

  Lemma latest_neq `(res : !RU_resources Mdl Σ) sa sa' c c' tail e k v : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfEvent e = Some c →
    latest_write c' k v tail →
    latest_write c' k v (tail ++ [e]).
  Proof.
    intros Hneq Hextract Hextract' Hconn (le & tag & v'& Hin & -> & Hall).
    exists (#tag, (c', (#"WrLin", (#k, v'))))%V, tag, v'.
    split; first set_solver.
    split; first done.
    intros le' Hin' Hevent Hneq'.
    rewrite elem_of_app in Hin'.
    destruct Hin' as [Hin'|Hin']; last set_solver.
    specialize (Hall le' Hin' Hevent Hneq').
    by apply rel_list_imp.
  Qed.

  Lemma trace_state_resources_neq `(res : !RU_resources Mdl Σ) clients (sa : socket_address) c t lt e γmstate γmname : 
    ⌜sa ∈ clients⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent e = Some c⌝ -∗
    (∃ p, ghost_map_elem γmname sa DfracDiscarded p) -∗
    trace_state_resources t lt γmstate γmname clients res -∗
    trace_state_resources (t ++ [e]) lt γmstate γmname clients res.
  Proof.
    iIntros "%Hin %Hextract %Hconn (%γ & #Helem) (%mstate & Hmap_mstate & %mname & Hmap_mname & Hstate)".
    iExists mstate.
    iFrame.
    iExists mname.
    iDestruct (@ghost_map_lookup with "[$Hmap_mname][$Helem]") as "%Hlookup".
    iFrame.
    iApply (big_sepS_wand with "[$Hstate]").
    iApply big_sepS_intro.
    iModIntro.
    iIntros (sa' Hin') "[(%Hdisj & %Hnot & %Hemit) | Hstate]"; last iFrame.
    destruct (decide (sa = sa')) as [<-|Hneq].
    - exfalso.
      apply Hnot.
      by exists γ.
    - iLeft.
      iPureIntro.
      split_and!; try done.
      intros (e' & c' & Hin_app & Hconn' & Hextract').
      apply Hemit.
      exists e', c'.
      rewrite elem_of_app in Hin_app.
      destruct Hin_app as [Hin_app | Hin_app]; set_solver.
  Qed.

  Lemma open_start_imp le c lt tail : 
    (is_rd_lin_event le ∨ is_wr_lin_event le) →
    open_start c lt tail →
    open_start c (lt ++ [le]) (tail ++ [le]).
  Proof.
    intros Hevent (le' & lt_pre & Hopen1 & Hopen2 & Hopen3 & Hopen4).
    exists le', lt_pre.
    split_and!; try set_solver.
    rewrite Hopen1.
    by do 2 rewrite -app_assoc.
  Qed.

  Lemma latest_write_upd c k v tag tail :
    latest_write c k v (tail ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]).
  Proof.
    exists (#tag, (c, (#"WrLin", (#k, v))))%V, tag, v.
    split_and!; try set_solver.
    intros le Hin Heq Hneq.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; last set_solver.
    rewrite elem_of_list_lookup in Hin.
    destruct Hin as (i & Hin).
    exists i, (length tail).
    split_and!.
    - by apply lookup_lt_Some in Hin.
    - by apply lookup_app_l_Some.
    - assert (length tail = Init.Nat.pred (length (tail ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]))) as ->.
      {
        rewrite last_length.
        lia.
      }
      rewrite -last_lookup.
      by rewrite last_snoc.
  Qed.

  Lemma latest_write_imp k' k c v' v tail tag :
    k' ≠ k →
    latest_write c k' v' tail →
    latest_write c k' v' (tail ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]).
  Proof.
    intros Hneq Hlatest.
    destruct Hlatest as (le & tag' & v'' & Hin & -> & Himp).
    exists (#tag', (c, (#"WrLin", (#k', v''))))%V, tag', v''.
    split_and!; try done.
    - set_solver.
    - intros le' Hin' Hexists Hneq'.
      rewrite elem_of_app in Hin'.
      destruct Hin' as [Hin' | Hin'].
      + specialize (Himp le' Hin' Hexists Hneq').
        by apply rel_list_imp.
      + assert (le' = (#tag, (c, (#"WrLin", (#k, v))))%V) as ->; set_solver.
  Qed.

  Lemma trace_state_resources_write_lin (clients : gset socket_address) (c : val) (tag : string) (lt t : list val) 
  (k : Key) (v : val) (sa : socket_address)  (s : local_state) (γ γmstate γmname : gname) (res : RU_resources Mdl Σ) 
  (mstate : gmap socket_address (local_state * option val)) (mname : gmap socket_address (gname * val)) (m : gmap Key (option val)) :
    ⌜mstate !! sa = Some (s, Some c)⌝ -∗ 
    ⌜extract c = Some #sa⌝ -∗ 
    ⌜clients = {[sa]} ∪ clients ∖ {[sa]}⌝ -∗
    ⌜∃ e : val, e ∈ lt ++ [(#tag, (c, (#"WrLin", (#k, v))))%V] ∧ 
      connOfEvent e = Some c ∧ is_in_lin_event e⌝ -∗
    ghost_map_elem γmname sa DfracDiscarded (γ, c) -∗ 
    ghost_map_auth γmstate 1 mstate -∗
    ghost_map_auth γmname 1 mname -∗
    ghost_map_auth γ 1 (<[k:=Some v]> m) -∗
    ([∗ set] y ∈ (clients ∖ {[sa]}), ⌜unnitialized_trace_resources y mstate mname t res⌝
      ∨ initialized_trace_resources lt y γmname res mstate) -∗
    active_trace_resources lt s c γ m -∗
    trace_state_resources t (lt ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]) γmstate γmname clients res.
  Proof.
    iIntros (Hlookup Hextract Heq_sa_clients) "#Hinit_in #Hpers_pointer Hmap_mstate Hmap_mname Hmap_m Hdisj_trace_res Htrace_res".
    iExists mstate.
    iFrame. 
    iExists mname.
    iFrame.
    rewrite {2} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iSplitR "Hdisj_trace_res".
    --- rewrite big_sepS_singleton.
        iRight.
        iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & 
        -> & -> & %Hopen_start & Hkeys & %Hlatest_keys)". 
        iExists (Active domain), c, γ, (<[k:=Some v]> m).
        do 2 (iSplit; first by iPureIntro).
        iFrame "∗#".
        iRight.
        iExists domain, (domain ∩ KVS_keys), 
        (tail ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]).
        do 2 (iSplit; first by iPureIntro).
        iFrame.
        iSplit.
        +++ iPureIntro.
            apply open_start_imp; last done.
            right.
            by exists tag, k, c, v.
        +++ iPureIntro.
            simpl.
            intros k' Hk'_in v' Hlookup'.
            specialize (Hlatest_keys k' Hk'_in).
            destruct (decide (k' = k)) as [->|Hneq].
            *** rewrite lookup_insert in Hlookup'.
                assert (v = v') as <-; first set_solver.
                apply latest_write_upd.
            *** rewrite lookup_insert_ne in Hlookup'; last done.
                specialize (Hlatest_keys v' Hlookup').
                apply latest_write_imp; try done.
    --- iApply (big_sepS_wand with "[$Hdisj_trace_res]"). 
        iApply big_sepS_intro.
        iModIntro.
        iIntros (sa'' Hsa''_in) "[Hres | Hres]"; first by iLeft.
        iRight.
        iDestruct "Hres" as "(%s'' & %c'' & %γ'' & %m'' & %Heq_lookup & %Hextract'' & 
        Hsa''_pointer & Hmap_m'' & %Hinit_in'' & Hdisj)".
        iExists s'', c'', γ'', m''.
        do 2 (iSplit; first by iPureIntro).
        iFrame "#∗".
        iSplit.
        {
          iPureIntro.
          destruct Hinit_in'' as (e & Hin'' & Hconn'' & Hevent'').
          exists e.
          split_and!; try done.
          apply elem_of_app; eauto.
        }
        iDestruct "Hdisj" as "[(-> & %Hclosed' & Hkeys) | 
        (%domain & %sub_domain & %tail & -> & -> & %Hopen' & Hkeys & %Hlatest)]".
        +++ iLeft.
            iFrame.
            iSplit; first done.
            iPureIntro.
            eapply (commit_closed_neq _ sa sa'' c c'' lt 
              (#tag, (c, (#"WrLin", (#k, v))))%V); set_solver.
        +++ iRight.
            iExists domain, (domain ∩ KVS_keys), 
            (tail ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]).
            do 2 (iSplit; first by iPureIntro).
            iFrame.
            iSplit.
            *** iPureIntro.
                eapply (open_start_neq _ sa sa'' c c'' lt tail 
                  (#tag, (c, (#"WrLin", (#k, v))))%V); set_solver.
            *** iPureIntro.
                simpl.
                intros k' Hk'_in k'' Hlookup'.
                specialize (Hlatest k' Hk'_in k'' Hlookup').
                eapply (latest_neq _ sa sa'' c c'' tail 
                  (#tag, (c, (#"WrLin", (#k, v))))%V); set_solver.
  Qed.

  (** Per operation implications *)

  Lemma init_client_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt res γmstate γmlin γmpost γmname γl clients) -∗
    @init_client_proxy_spec _ _ _ _ lib res -∗
    @init_client_proxy_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
  Proof.
    (* iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hinit_cli".
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
          rewrite /is_in_pre_event.
          by exists tag.
        }
        split; done.
      - split; first done.
        destruct (exists_execution T) as [E (Hbased & Hvalid_exec)]; first set_solver.
        eexists T, E.
        by do 3 (split; first done).
    }
    iIntros (tag1) "(Htr_is & %Htag1_nin)".
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
          rewrite /is_in_pre_event.
          by exists tag1.
        }
        split; done.
      - do 3 (iSplitR; first by iPureIntro).
        iSplit; first by iPureIntro.
        iApply trace_state_resources_init_imp.
        iFrame.
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
        rewrite /is_in_post_event.
        set_solver.
      - split; first done.
        destruct (exists_execution T') as [E' (Hbased' & Hvalid_exec')]; first set_solver.
        eexists T', E'.
        by do 3 (split; first done).
    }
    iIntros "Htr_is".
    iDestruct (lin_tag_add_post lt' t' γmlin (#tag1, (c, #"InitPost"))%V with "[$Hlin_res']") as "Hlin_res'".
    iDestruct (post_tag_add t' γmpost (#tag1, (c, #"InitPost"))%V tag1 with "[$Hpost_res' $Hpost_tag_res]")
      as "Hpost_res'".
    {
      iPureIntro.
      simpl.
      split; first done.
      do 4 right.
      rewrite /is_in_post_event.
      by eexists _, _.
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
    iAssert ((⌜mname !! sa = None⌝ ∧ ⌜no_emit_with_address sa t' res⌝)%I) as "(%Hlookup_none & %Hno_emit)".
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
      rewrite /GlobalInvExt.
      iExists (t' ++ [(#tag1, (c, #"InitPost"))%V]), lt', T'.
      iFrame.
      iSplit.
      - iPureIntro.
        apply (lin_trace_valid tag1); try done.
        right.
        rewrite /is_in_post_event.
        set_solver.
      - do 4 (iSplit; first done).
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
          iLeft.
          iSplit; first by iPureIntro.
          iSplit.
          * iPureIntro.
            rewrite /commit_closed.
            intros e_st Hin Hconn Hstart.
            exfalso.
            apply Hno_emit.
            destruct HlinOf' as (_ & _ & HlinOf' & _).
            destruct (HlinOf' e_st Hin) as (e_pre & _ & Hlin_to_pre & Hin_pre & _).
            exists e_pre, c.
            split; first done.
            split; last done.
            destruct Hstart as (tag' & c' & ->).
            simpl in Hlin_to_pre.
            simpl in Hconn.
            assert (e_pre = (#tag', (c', #"StPre"))%V) as ->; first set_solver.
            simpl.
            set_solver.
          * rewrite big_sepM_gset_to_gmap.
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
          iDestruct "Hext_res" as "[%Hext_res | Hext_res]".
          * iLeft. 
            iPureIntro.
            rewrite /unnitialized_trace_resources.
            rewrite lookup_insert_ne; last set_solver.
            destruct Hext_res as (Hext_res1 & Hext_res2 & Hno_emit').
            split_and!; try done.
            -- intros (γ' & Hfalse).
               apply Hext_res2.
               exists γ'.
               by rewrite lookup_insert_ne in Hfalse; last set_solver.
            -- assert (sa ≠ sa') as Hneq; first set_solver.
               intros (e & c' & Hin & Hconn & Hextract').
               apply Hno_emit'.
               exists e, c'.
               split.
               ++ rewrite elem_of_app in Hin. 
                 destruct Hin as [Hin | Hin]; first done.
                 assert (e = (#tag1, (c, #"InitPost"))%V) as ->; first set_solver.
                 simpl in Hconn.
                 assert (c = c') as <-; first set_solver.
                 exfalso.
                 eapply (res.(read_uncommitted.specs.resources.Extraction_preservation) sa sa' c c);
                   try done.
                 set_solver.
               ++ split; done.
          * iRight.
            rewrite /initialized_trace_resources.
            rewrite lookup_insert_ne; last set_solver.
            iFrame.
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
  Qed. *)
  Admitted.

  Lemma read_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt res γmstate γmlin γmpost γmname γl clients) -∗
    @read_spec _ _ _ _ lib res -∗
    @read_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
  Proof.
  Admitted.

  Lemma write_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt res γmstate γmlin γmpost γmname γl clients) -∗
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
          do 2 right.
          left.
          rewrite /is_wr_pre_event.
          by eexists _, _.
        }
        split; done.
      - split; first done.
        destruct (exists_execution T) as [Ex (Hbased & Hvalid_exec)]; first set_solver.
        eexists T, Ex.
        by do 3 (split; first done).
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
      rewrite /GlobalInvExt.
      iExists (t ++ [(#tag1, (c, #"WrPre"))%V]), lt, T.
      iFrame.
      iSplitR.
      - iPureIntro.
        apply (lin_trace_valid tag1); try done.
        left.
        split.
        {
          rewrite /is_pre_event.
          do 2 right.
          left.
          rewrite /is_wr_pre_event.
          by eexists _, _.
        }
        split; done.
      - do 4 (iSplitR; first by iPureIntro).
        iApply (trace_state_resources_neq _ _ sa c with "[][][][][$]"); 
          try by iPureIntro.
        iDestruct "Hpers_pointer" as "(%γ & #Hpers_pointer)".
        iExists _.
        iFrame "#".
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
     iInv "HinvExt" as ">[%t' [%lt' [%T' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]]]" "Hclose'".
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
      iDestruct "Hfalse" as "((%ov' & Hfalse) & _)".
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
      rewrite /GlobalInvExt.
      iExists t', (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]).
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
        iExists (T1 ++ (trans ++ [Wr (tag1, c) k v]) :: T2).
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
                  admit.
                  (* apply (valid_transactions_add T' _ c); try done.
                  ** set_solver.
                  ** exists (Wr (tag1, c) k v).
                     by simpl.
                  ** apply valid_transaction_singleton. *)
               ++ iSplit.
                  ** iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & 
                       %Hopen_start & Hrest)".
                     iPureIntro.
                     apply (valid_sequence_wr_lin _ _ tag1 c tail); try done.
                     --- left.
                         rewrite /is_wr_lin_event.
                         set_solver.
                     --- by exists t'.
                  ** iApply (trace_state_resources_write_lin clients c tag1 lt' t' k v.(SV_val) sa
                        s γ γmstate γmname res mstate mname m with "[][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                        [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
                        iPureIntro.
                        destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                        exists e.
                        split_and!; try done.
                        apply elem_of_app; eauto.
      - iExists (T' ++ [[Wr (tag1, c) k v]]).
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
                  apply (valid_transactions_add T' _ c); try done.
                  ** set_solver.
                  ** exists (Wr (tag1, c) k v).
                     by simpl.
                  ** apply valid_transaction_singleton.
               ++ iSplit.
                  ** iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & -> & -> & 
                       %Hopen_start & Hrest)".
                     iPureIntro.
                     apply (valid_sequence_wr_lin _ _ tag1 c tail); try done.
                     --- left.
                         rewrite /is_wr_lin_event.
                         set_solver.
                     --- by exists t'.
                  ** iApply (trace_state_resources_write_lin clients c tag1 lt' t' k v.(SV_val) sa
                        s γ γmstate γmname res mstate mname m with "[][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
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
    iInv "HinvExt" as ">[%t'' [%lt'' [%T'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]]]" "Hclose''".
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
      rewrite /valid_trace_ru /valid_trace.
      exists lt''.
      split.
      - apply (lin_trace_valid tag1); try done.
        right.
        split.
        + right.
          left.
          by eexists _, _, _, _.
        + exists (#tag1, (c, (#"WrLin", (#k, v))))%V.
          split; last done.
          by simpl.
      - split; first done.
        destruct (exists_execution T'' Hno_empty'') as (exec & Hexec_props).
        by exists T'', exec.
    }
    iIntros "Htr_is''".
    iDestruct (lin_tag_add_post lt'' t'' γmlin (#tag1, (c, (#"WrPost", (#k, v))))%V with "[$Hlin_res'']") as "Hlin_res''".
    iDestruct (post_tag_add t'' γmpost (#tag1, (c, (#"WrPost", (#k, v))))%V tag1 with "[$Hpost_res'' $Hpost_tag_res]")
     as "Hpost_res''".
    {
      simpl.
      iSplitL; first by iPureIntro.
      iPureIntro.
      do 2 right.
      left.
      by eexists _, _, _, _.
    }
    iMod ("Hclose''" with "[Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists (t'' ++ [(#tag1, (c, (#"WrPost", (#k, v))))%V]), lt'', T''.
      iFrame.
      iSplitR.
      - iPureIntro.
        apply (lin_trace_valid tag1); try done.
        right.
        split.
        + right.
          left.
          by eexists _, _, _, _.
        + exists (#tag1, (c, (#"WrLin", (#k, v))))%V.
          split; last done.
          by simpl.
      - do 4 (iSplitR; first done).
        iApply (trace_state_resources_neq _ _ sa c with "[][][][][$]"); 
          try by iPureIntro.
        iExists _.
        iFrame "#".
    }
    iModIntro.
    wp_pures.
    iFrame.
  Admitted.

  Lemma start_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt res γmstate γmlin γmpost γmname γl clients) -∗
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
        destruct (exists_execution T) as [Ex (Hbased & Hvalid_exec)]; first set_solver.
        eexists T, Ex.
        by do 3 (split; first done).
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
      - do 4 (iSplitR; first by iPureIntro).
        iApply (trace_state_resources_neq _ _ sa c with "[][][][][$]"); 
          try by iPureIntro.
        iDestruct "Hpers_pointer" as "(%γ & #Hpers_pointer)".
        iExists _.
        iFrame "#".
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
    iInv "HinvExt" as ">[%t' [%lt' [%T' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]]]" "Hclose'".
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
      #Hsa_c'_pointer & Hghost_map_m' & %Hinit & [(-> & %Hclosed & Hkeys_conn_res) | Hfalse])"; last first.
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
      rewrite /GlobalInvExt.
      iExists t', (lt' ++ [(#tag1, (c, #"StLin"))%V]), T'.
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
        apply valid_sequence_st_lin; try done.
        - destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
          exists e.
          split_and!; try eauto.
          by assert (c = c') as ->; first set_solver.
        - by assert (c = c') as ->; first set_solver.
      }
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
        do 2 (iSplit; first by iPureIntro).
        iSplit.
        {
          iPureIntro.
          destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
          exists e.
          split_and!; try eauto.
          by apply elem_of_app; eauto.
        }
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
          * iIntros (k' Hk'_dom v Hlookup). 
            rewrite Hnone in Hlookup; first done.
            set_solver.
      - iApply (big_sepS_wand with "[$Hdisj_trace_res]").
        iApply big_sepS_intro.
        iModIntro.
        iIntros (sa' Hsa'_in) "Hsa'".
        rewrite /unnitialized_trace_resources /initialized_trace_resources.
        rewrite lookup_insert_ne; last set_solver.
        iDestruct "Hsa'" as "[Hsa' | (%s_sa' & %c_sa' & %γ_sa' & %m_sa' & 
          Hlookup_sa' &  %Hextract_sa' & Hpointer_sa' & Hmap_sa' & Hrest)]".
        + iLeft.
          iFrame.
        + iRight.
          iFrame.
          iExists s_sa', c_sa', γ_sa', m_sa'.
          iFrame.
          iSplit; first by iPureIntro.
          iDestruct "Hrest" as "(%Hinit'' & Hrest)".
          iSplit.
          {
            iPureIntro.
            destruct Hinit'' as (e & Hin' & Hconn' & Hevent').
            exists e.
            split_and!; try eauto.
            by apply elem_of_app; eauto.
          }
          iDestruct "Hrest" as "[(-> & %Hclosed_sa' & Hkeys) | 
            (%domain_sa' & %sub_domain_sa' & %tail_sa' & 
            -> & -> & %Hopen_sa' & Hkeys)]"; iFrame.
          * iLeft.
            iSplit; first by iPureIntro.
            iFrame.
            iPureIntro.
            eapply (commit_closed_neq _ sa sa' c c_sa' lt' (#tag1, (c, #"StLin"))%V); set_solver.
          * iRight.
            iExists domain_sa', (domain_sa' ∩ KVS_keys), (tail_sa' ++ [(#tag1, (c, #"StLin"))%V]).
            iFrame.
            do 2 (iSplit; first by iPureIntro).
            iSplitR.
            -- iPureIntro.
               eapply (open_start_neq _ sa sa' c c_sa' lt' tail_sa' (#tag1, (c, #"StLin"))%V); set_solver.
            -- iDestruct "Hkeys" as "(Hkeys & %Hlatest)".
               iFrame.
               iPureIntro.
               simpl.
              intros k Hk_in v Hlookup.
              specialize (Hlatest k Hk_in v Hlookup).
              eapply (latest_neq _ sa sa' c c_sa' tail_sa' (#tag1, (c, #"StLin"))%V k v); set_solver.
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
        right.
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
      iExists (t'' ++ [(#tag1, (c, #"StPost"))%V]), lt'', T''.
      iFrame.
      iSplitR.
      - iPureIntro.
        apply (lin_trace_valid tag1); try done.
        right.
        split.
        + left.
          by eexists _, _.
        + exists (#tag1, (c, #"StLin"))%V.
          split; last done.
          by simpl.
      - do 4 (iSplitR; first done).
        iApply (trace_state_resources_neq _ _ sa c with "[][][][][$]"); 
          try by iPureIntro.
        iExists _.
        iFrame "#".
    }
    iModIntro.
    wp_pures.
    iFrame.
  Qed.

  Lemma commit_implication γmstate γmlin γmpost γmname γl clients (res : RU_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_ru -∗
    inv KVS_InvName (GlobalInvExt res γmstate γmlin γmpost γmname γl clients) -∗
    @commit_spec _ _ _ _ lib res -∗
    @commit_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γmstate γmlin γmpost γmname γl clients res).
  Proof.
  Admitted.

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
    iMod (inv_alloc KVS_InvName ⊤ (GlobalInvExt res γmstate γmlin γmpost γmname γl clients) with 
      "[Htr Hghost_map_mstate Hghost_map_mlin Hghost_map_mpost Hghost_map_mname Hltrace Hlhist]") as "#HinvExt".
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
        do 2 (split; first set_solver).
        set_solver.
      }
      iSplitR.
      {
        iPureIntro.
        rewrite /valid_sequence /unique_init_events.
        split; intros; set_solver.
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