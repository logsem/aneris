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

  Definition open_trans (t : transaction) (c : val) (T : list transaction) : Prop :=
    ∃ op, t ∈ T ∧ last t = Some op ∧ connOfOp op = c ∧ (¬is_cm_op op).

  Definition latest_write (c : val) (k : Key) (ov : option val) (T : list transaction) : Prop := 
    (ov = None ∧ (∀ t, open_trans t c T → ¬ ∃ v s, (Wr s k v) ∈ t)) ∨
    (∃ v t tag, ov = Some v ∧ open_trans t c T ∧ (Wr (tag, c) k v) ∈ t ∧
      (∀ op, op ∈ t → (∃ s' v', op = Wr s' k v' ∧ op ≠ Wr (tag, c) k v) → rel_list t op (Wr (tag, c) k v))).

  Definition tag_eq (e1 e2 : val) : Prop := ∃ tag, tagOfEvent e1 = Some tag ∧ tagOfEvent e2 = Some tag.

  Definition no_emit_with_address (sa : socket_address) (ltrace : list val) `(res : !RU_resources Mdl Σ)  : Prop := 
    ¬∃ e c, e ∈ ltrace ∧ connOfEvent e = Some c ∧ extract c = Some #sa.

  Definition active_trace_resources lt T s c γ (m : gmap Key (option val)) : iProp Σ :=
    ∃ domain sub_domain tail, ⌜s = Active domain⌝ ∗ 
      ⌜sub_domain = domain ∩ KVS_keys⌝ ∗ ⌜open_start c lt tail⌝ ∗ 
      ([∗ set] k ∈ KVS_keys ∖ sub_domain, ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ 
      (∀ k, ⌜k ∈ sub_domain⌝ → ∀ ov, ⌜m !! k = Some ov⌝ → ⌜latest_write c k ov T⌝).

  Definition inactive_trace_resources lt T s c γ : iProp Σ :=
    ⌜s = CanStart⌝ ∗ ⌜commit_closed c lt⌝ ∗ ⌜¬∃ t, open_trans t c T⌝ ∗
    ([∗ set] k ∈ KVS_keys, ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov).

  Definition initialized_trace_resources lt T sa γmname `(res : !RU_resources Mdl Σ)
  (mstate : gmap socket_address (local_state * option val)) : iProp Σ :=
    ∃ s c γ (m : gmap Key (option val)), ⌜mstate !! sa = Some (s, Some c)⌝ ∗
      ⌜extract c = Some #(LitSocketAddress sa)⌝ ∗ 
      ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
      ghost_map_auth γ (1%Qp) m ∗ 
      ⌜(∃ e, e ∈ lt ∧ connOfEvent e = Some c ∧ is_in_lin_event e)⌝ ∗ 
      (inactive_trace_resources lt T s c γ ∨ active_trace_resources lt T s c γ m).

  Definition unnitialized_trace_resources sa (mstate : gmap socket_address (local_state * option val)) 
  (mname : gmap socket_address (gname * val)) lt `(res : !RU_resources Mdl Σ) : Prop := 
    (mstate !! sa = None ∨ mstate !! sa = Some (CanStart, None)) ∧ 
    (¬∃ p, mname !! sa = Some p) ∧ no_emit_with_address sa lt res.

  Definition client_trace_state_resources (lt : list val) (T : list transaction) (sa : socket_address) 
  (γmstate γmname : gname) `(res : !RU_resources Mdl Σ)  (mstate : gmap socket_address (local_state * option val)) 
  (mname : gmap socket_address (gname * val)) : iProp Σ := 
    ⌜unnitialized_trace_resources sa mstate mname lt res⌝ ∨ initialized_trace_resources lt T sa γmname res mstate.

  Definition trace_state_resources (lt : list val) (T : list transaction) (γmstate γmname : gname) 
  (clients : gset socket_address) `(res : !RU_resources Mdl Σ) : iProp Σ := 
    ∃ (mstate : gmap socket_address (local_state * option val)), ghost_map_auth γmstate (1%Qp) mstate ∗ 
      ∃ (mname : gmap socket_address (gname * val)), ghost_map_auth γmname (1%Qp) mname ∗ 
        ([∗ set] sa ∈ clients, client_trace_state_resources lt T sa γmstate γmname res mstate mname).

  Definition GlobalInvExt `(res : !RU_resources Mdl Σ) (γmstate γmlin γmpost γmname γl : gname) (clients : gset socket_address) : iProp Σ := 
    ∃ t lt T, trace_is t ∗ OwnLinTrace γl lt ∗ ⌜lin_trace_of lt t⌝ ∗ ⌜∀ t, t ∈ T → t ≠ []⌝ ∗
      ⌜extraction_of lt T⌝ ∗ ⌜valid_transactions T⌝ ∗ ⌜valid_sequence lt⌝ ∗
      trace_state_resources lt T γmstate γmname clients res ∗
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

  Lemma open_trans_neq1 `(res : !RU_resources Mdl Σ) sa sa' c c' t T op : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfOp op = c →
    open_trans t c' (T  ++ [[op]]) →
    open_trans t c' T.
  Proof.
    intros Hneq Hextract Hextract' Hconn (op' & Hin & Hlast & Hconn' & Hcom).
    exists op'.
    set_solver.
  Qed.

  Lemma open_trans_neq2 `(res : !RU_resources Mdl Σ) sa sa' c c' t T op : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfOp op = c →
    open_trans t c' T →
    open_trans t c' (T  ++ [[op]]).
  Proof.
    intros Hneq Hextract Hextract' Hconn (op' & Hin & Hlast & Hconn' & Hcom).
    exists op'.
    set_solver.
  Qed.

  Lemma latest_neq `(res : !RU_resources Mdl Σ) sa sa' c c' T op k v : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfOp op = c →
    latest_write c' k v T →
    latest_write c' k v (T ++ [[op]]).
  Proof.
    intros Hneq Hextract Hextract' Hconn [(-> & Himp)|(v' & t & tag & -> & Hopen & Hin & Himp)].
    - left.
      split; first done.
      intros t Hopen.
      apply Himp.
      by eapply open_trans_neq1 in Hopen.
    - right.
      exists v', t, tag.
      split_and!; try done.
      by eapply open_trans_neq2 in Hopen.
  Qed.

  Lemma unique_init_events_add_init (lt t : list val) (tag : string) (c : val) 
  (sa : socket_address) (res : RU_resources Mdl Σ) :
    extract c = Some #sa →
    no_emit_with_address sa lt res →
    unique_init_events lt →
    unique_init_events (lt ++ [(#tag, (c, #"InLin"))%V]).
  Proof.
    intros Hextract Hno_emit Hunique.
    intros le le' c' i j Hlookup_i Hevent Hconn 
      Hlookup_j Hevent' Hconn'.
    rewrite /unique_init_events in Hunique.
    rewrite lookup_app_Some in Hlookup_i.
    destruct Hlookup_i as [Hlookup_i|(Hlength_i & Hlookup_i)].
    - rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j|(_ & Hlookup_j)]; 
        first set_solver.
      rewrite list_lookup_singleton_Some in Hlookup_j.
      assert (le' = (#tag, (c, #"InLin"))%V) as ->; first set_solver. 
      simpl in Hconn.
      assert (c = c') as <-; first set_solver.
      exfalso.
      apply Hno_emit.
      assert (le ∈ lt) as Hle'_in;
        first apply elem_of_list_lookup; eauto.
    - rewrite lookup_app_Some in Hlookup_j.
      destruct Hlookup_j as [Hlookup_j|(Hlength_j & Hlookup_j)].
      + rewrite list_lookup_singleton_Some in Hlookup_i.
        assert (le = (#tag, (c, #"InLin"))%V) as ->; first set_solver. 
        simpl in Hconn.
        assert (c = c') as <-; first set_solver.
        exfalso.
        apply Hno_emit.
        assert (le' ∈ lt) as Hle'_in;
          first apply elem_of_list_lookup; eauto.
      + rewrite list_lookup_singleton_Some in Hlookup_i.
        rewrite list_lookup_singleton_Some in Hlookup_j.
        lia.
  Qed.

  Lemma unnitialized_trace_resources_neq1 (sa sa' : socket_address) lt c le mstate mname 
  (res : RU_resources Mdl Σ) :
    connOfEvent le = Some c →
    sa ≠ sa' →
    extract c = Some #sa →
    unnitialized_trace_resources sa' mstate mname lt res →
    unnitialized_trace_resources sa' mstate mname (lt ++ [le]) res.
  Proof.
    intros Hconn Hneq Hextract (Hunit1 & Hunit2 & Hunit3).
    split_and!; try done.
    intros (e & c' & Hin &Hconn' & Hextract').
    apply Hunit3.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; set_solver.
  Qed.

  Lemma unnitialized_trace_resources_neq2 (sa sa' : socket_address) lt c le mstate mname 
  (res : RU_resources Mdl Σ) p :
    connOfEvent le = Some c →
    sa ≠ sa' →
    extract c = Some #sa →
    unnitialized_trace_resources sa' mstate mname lt res →
    unnitialized_trace_resources sa' (<[sa:=p]> mstate) mname (lt ++ [le]) res.
  Proof.
    intros Hconn Hneq Hextract (Hunit1 & Hunit2 & Hunit3).
    split_and!; try done.
    - by rewrite lookup_insert_ne.
    - intros (e & c' & Hin &Hconn' & Hextract').
      apply Hunit3.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hin]; set_solver.
  Qed.

  Lemma unnitialized_trace_resources_neq3 (sa sa' : socket_address) lt c le mstate mname 
  (res : RU_resources Mdl Σ) p1 p2 :
    connOfEvent le = Some c →
    sa ≠ sa' →
    extract c = Some #sa →
    unnitialized_trace_resources sa' mstate mname lt res →
    unnitialized_trace_resources sa' (<[sa:=p1]> mstate) (<[sa:=p2]> mname) (lt ++ [le]) res.
  Proof.
    intros Hconn Hneq Hextract (Hunit1 & Hunit2 & Hunit3).
    split_and!; try done.
    - by rewrite lookup_insert_ne.
    - by rewrite lookup_insert_ne.
    - intros (e & c' & Hin &Hconn' & Hextract').
      apply Hunit3.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hin]; set_solver.
  Qed.

  Lemma initialized_trace_resources_neq1 (sa sa' : socket_address) c le lt T
  γmname mstate (res : RU_resources Mdl Σ) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    initialized_trace_resources lt T sa' γmname res mstate -∗
    initialized_trace_resources  (lt ++ [le]) T sa' γmname res mstate.
  Proof.
    iIntros (Hneq Hextract Hconn) "Hres".
    iDestruct "Hres" as "(%s & %c' & %γ & %m & %Heq_lookup & %Hextract' & 
      Hsa_pointer & Hmap_m & %Hinit_in' & Hdisj)".
    iExists s, c', γ, m.
    do 2 (iSplit; first by iPureIntro).
    iFrame "#∗".
    iSplit.
    {
      iPureIntro.
      destruct Hinit_in' as (e & Hin'' & Hconn'' & Hevent'').
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
        eapply (commit_closed_neq _ sa sa' c c' lt le); set_solver.
    +++ iRight.
        iExists domain, (domain ∩ KVS_keys), (tail ++ [le]).
        do 2 (iSplit; first by iPureIntro).
        iFrame.
        iSplit.
        *** iPureIntro.
            eapply (open_start_neq _ sa sa' c c' lt tail le); set_solver.
        *** iPureIntro.
            simpl.
            intros k' Hk'_in k'' Hlookup'.
            by specialize (Hlatest k' Hk'_in k'' Hlookup').
  Qed.

  Lemma initialized_trace_resources_neq2 (sa sa' : socket_address) c le lt T
  γmname mstate p (res : RU_resources Mdl Σ) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    initialized_trace_resources lt T sa' γmname res mstate -∗
    initialized_trace_resources  (lt ++ [le]) T sa' γmname res (<[sa:=p]> mstate).
  Proof.
    iIntros (Hneq Hextract Hconn) "Hres".
    rewrite /initialized_trace_resources.
    rewrite lookup_insert_ne; last done.
    iAssert (initialized_trace_resources  (lt ++ [le]) T sa' γmname res mstate) 
      with "[Hres]" as "Hres"; last iFrame.
    by iApply (initialized_trace_resources_neq1 sa sa' c with "[][][][$Hres]"). 
  Qed.

  Lemma initialized_trace_resources_neq3 (sa sa' : socket_address) op c le lt T
  γmname mstate (res : RU_resources Mdl Σ) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    initialized_trace_resources lt T sa' γmname res mstate -∗
    initialized_trace_resources  (lt ++ [le]) (T ++ [[op]]) sa' γmname res mstate.
  Proof.
    iIntros (Hneq Hextract Hconn Hconn') "Hres".
    iDestruct "Hres" as "(%s & %c' & %γ & %m & %Heq_lookup & %Hextract' & 
      Hsa_pointer & Hmap_m & %Hinit_in' & Hdisj)".
    iExists s, c', γ, m.
    do 2 (iSplit; first by iPureIntro).
    iFrame "#∗".
    iSplit.
    {
      iPureIntro.
      destruct Hinit_in' as (e & Hin'' & Hconn'' & Hevent'').
      exists e.
      split_and!; try done.
      apply elem_of_app; eauto.
    }
    iDestruct "Hdisj" as "[(-> & %Hclosed' & %Hnot & Hkeys) | 
    (%domain & %sub_domain & %tail & -> & -> & %Hopen' & Hkeys & %Hlatest)]".
    +++ iLeft.
        iSplit; first done.
        iFrame.
        iSplitL; iPureIntro.
        *** eapply (commit_closed_neq _ sa sa' c c' lt le); set_solver.
        *** intros (t & Hopen).
            apply Hnot.
            exists t.  
            eapply (open_trans_neq1 _ sa sa'); set_solver.
    +++ iRight.
        iExists domain, (domain ∩ KVS_keys), (tail ++ [le]).
        do 2 (iSplit; first by iPureIntro).
        iFrame.
        iSplit.
        *** iPureIntro.
            eapply (open_start_neq _ sa sa' c c' lt tail le); set_solver.
        *** iPureIntro.
            simpl.
            intros k' Hk'_in k'' Hlookup'.
            specialize (Hlatest k' Hk'_in k'' Hlookup').
            eapply (latest_neq _ sa sa'); set_solver.
  Qed.

  Lemma client_trace_state_resources_neq1 (sa sa' : socket_address) T op c le lt 
  γstate γmname mstate mname (res : RU_resources Mdl Σ) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    client_trace_state_resources lt T sa' γstate γmname res mstate mname -∗
    client_trace_state_resources (lt ++ [le]) (T ++ [[op]]) sa' γstate γmname res mstate mname.
  Proof.
    iIntros (Hneq Hextract Hconn Hconn') "Hres".
    iDestruct "Hres" as "[%Hres|Hres]".
    - iLeft.
      iPureIntro.
      by apply (unnitialized_trace_resources_neq1 sa sa' lt c).
    - iRight.
      by iApply (initialized_trace_resources_neq3 sa sa' op c with "[][][][]").
  Qed.

  Lemma client_trace_state_resources_neq2 (sa sa' : socket_address) c le lt T 
  γstate γmname mstate mname p (res : RU_resources Mdl Σ) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    client_trace_state_resources lt T sa' γstate γmname res mstate mname -∗
    client_trace_state_resources (lt ++ [le]) T sa' γstate γmname res (<[sa:=p]> mstate) mname.
  Proof.
    iIntros (Hneq Hextract Hconn) "Hres".
    iDestruct "Hres" as "[%Hres|Hres]".
    - iLeft.
      iPureIntro.
      by apply (unnitialized_trace_resources_neq2 sa sa' lt c).
    - iRight.
      by iApply (initialized_trace_resources_neq2 sa sa' c with "[][][][$]").
  Qed.

  Lemma client_trace_state_resources_neq3 (sa sa' : socket_address) c le lt T
  γstate γmname mstate mname p1 p2 (res : RU_resources Mdl Σ) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    client_trace_state_resources lt T sa' γstate γmname res mstate mname -∗
    client_trace_state_resources (lt ++ [le]) T sa' γstate γmname res (<[sa:=p1]> mstate) (<[sa:=p2]> mname).
  Proof.
    iIntros (Hneq Hextract Hconn) "Hres".
    iDestruct "Hres" as "[%Hres|Hres]".
    - iLeft.
      iPureIntro.
      by apply (unnitialized_trace_resources_neq3 sa sa' lt c).
    - iRight.
      by iApply (initialized_trace_resources_neq2 sa sa' c with "[][][][$]").
  Qed.

  Lemma trace_state_resources_read_lin1 (clients : gset socket_address) (c : val) (tag : string) (lt : list val) (T : list transaction)
  (k : Key) (sa : socket_address) (wo : option val) (s : local_state) (γ γmstate γmname : gname) (res : RU_resources Mdl Σ) 
  (mstate : gmap socket_address (local_state * option val)) (mname : gmap socket_address (gname * val)) (m : gmap Key (option val)) :
    ⌜mstate !! sa = Some (s, Some c)⌝ -∗ 
    ⌜extract c = Some #sa⌝ -∗ 
    ⌜clients = {[sa]} ∪ clients ∖ {[sa]}⌝ -∗
    ⌜¬ (∃ trans : transaction, trans ∈ T ∧ (∃ op' : operation,
          op' ∈ trans ∧ last trans = Some op' ∧ connOfOp op' = c ∧ isCmOp op' = false))⌝ -∗
    ⌜∃ e : val, e ∈ lt ++ [(#tag, (c, (#"RdLin", (#k, $wo))))%V] ∧ 
      connOfEvent e = Some c ∧ is_in_lin_event e⌝ -∗
    ghost_map_elem γmname sa DfracDiscarded (γ, c) -∗ 
    ghost_map_auth γmstate 1 mstate -∗
    ghost_map_auth γmname 1 mname -∗
    ghost_map_auth γ 1 m -∗
    ([∗ set] y ∈ (clients ∖ {[sa]}), ⌜unnitialized_trace_resources y mstate mname lt res⌝
      ∨ initialized_trace_resources lt T y γmname res mstate) -∗
    active_trace_resources lt T s c γ m -∗
    trace_state_resources (lt ++ [(#tag, (c, (#"RdLin", (#k, $wo))))%V]) (T ++ [[Rd (tag, c) k wo]]) γmstate γmname clients res.
  Proof.
    iIntros (Hlookup Hextract Heq_sa_clients Hdec) "#Hinit_in #Hpers_pointer Hmap_mstate Hmap_mname Hmap_m Hdisj_trace_res Htrace_res".
    iExists mstate.
    iFrame. 
    iExists mname.
    iFrame.
    rewrite {2} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iSplitR "Hdisj_trace_res".
    - rewrite big_sepS_singleton.
      iRight.
      iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & 
      -> & -> & %Hopen_start & Hkeys & %Hlatest_keys)". 
      iExists (Active domain), c, γ, m.
      do 2 (iSplit; first by iPureIntro).
      iFrame "∗#".
      iRight.
      iExists domain, (domain ∩ KVS_keys), 
      (tail ++ [(#tag, (c, (#"RdLin", (#k, $ wo))))%V]).
      do 2 (iSplit; first by iPureIntro).
      iFrame.
      iSplit.
      + iPureIntro.
        apply open_start_imp; last done.
        left.
        rewrite /is_rd_lin_event.
        destruct wo; set_solver.
      + iPureIntro.
        simpl.
        intros k' Hk'_in v' Hlookup'.
        destruct v' as [v'|].
        * exfalso.
          apply Hdec. 
          specialize (Hlatest_keys k' Hk'_in (Some v') Hlookup').
          destruct Hlatest_keys as [Hfalse|(v1 & t & tag1 & _ & Hopen & _)]; first set_solver.
          destruct Hopen as (op & Ht_in & Hlast & Hconn & Hcm).
          exists t.
          split; first done.
          exists op.
          split_and!; try done.
          -- by apply last_Some_elem_of.
          -- rewrite /is_cm_op in Hcm.
             rewrite /isCmOp.
             destruct op; set_solver.
        * left.
          split; first done.
          intros t Hopen Hfalse.
          rewrite /open_trans in Hopen.
          destruct Hopen as (op & Ht_in & Hlast & Hconn & Hcm).
          rewrite elem_of_app in Ht_in.
          destruct Ht_in as [Ht_in | Ht_in].
          -- apply Hdec.
             exists t.
             split; first done.
             exists op.
             split_and!; try done.
             ++ by apply last_Some_elem_of.
             ++ rewrite /is_cm_op in Hcm.
                rewrite /isCmOp.
                destruct op; set_solver.
          -- assert (t = [Rd (tag, c) k wo]) as ->; set_solver.
    - iApply (big_sepS_wand with "[$Hdisj_trace_res]"). 
      iApply big_sepS_intro.
      iModIntro.
      iIntros (sa'' Hsa''_in) "Hres".
      iApply (client_trace_state_resources_neq1 sa sa'' T (Rd (tag, c) k wo) c with "[][][][]"); try done.
      iPureIntro; set_solver.
  Qed.

  Lemma trace_state_resources_write_lin1 (clients : gset socket_address) (c : val) (tag : string) (lt : list val) (T : list transaction)
  (k : Key) (v : val) (sa : socket_address) (s : local_state) (γ γmstate γmname : gname) (res : RU_resources Mdl Σ) 
  (mstate : gmap socket_address (local_state * option val)) (mname : gmap socket_address (gname * val)) (m : gmap Key (option val)) :
    ⌜mstate !! sa = Some (s, Some c)⌝ -∗ 
    ⌜extract c = Some #sa⌝ -∗ 
    ⌜clients = {[sa]} ∪ clients ∖ {[sa]}⌝ -∗
    ⌜¬ (∃ trans : transaction, trans ∈ T ∧ (∃ op' : operation,
      op' ∈ trans ∧ last trans = Some op' ∧ connOfOp op' = c ∧ isCmOp op' = false))⌝ -∗
    ⌜∃ e : val, e ∈ lt ++ [(#tag, (c, (#"WrLin", (#k, v))))%V] ∧ 
      connOfEvent e = Some c ∧ is_in_lin_event e⌝ -∗
    ghost_map_elem γmname sa DfracDiscarded (γ, c) -∗ 
    ghost_map_auth γmstate 1 mstate -∗
    ghost_map_auth γmname 1 mname -∗
    ghost_map_auth γ 1 (<[k:=Some v]> m) -∗
    ([∗ set] y ∈ (clients ∖ {[sa]}), ⌜unnitialized_trace_resources y mstate mname lt res⌝
      ∨ initialized_trace_resources lt T y γmname res mstate) -∗
    active_trace_resources lt T s c γ m -∗
    trace_state_resources (lt ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]) (T ++ [[Wr (tag, c) k v]]) γmstate γmname clients res.
  Proof.
    iIntros (Hlookup Hextract Heq_sa_clients Hdec) "#Hinit_in #Hpers_pointer Hmap_mstate Hmap_mname Hmap_m Hdisj_trace_res Htrace_res".
    iExists mstate.
    iFrame. 
    iExists mname.
    iFrame.
    rewrite {2} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iSplitR "Hdisj_trace_res".
    - rewrite big_sepS_singleton.
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
      + iPureIntro.
        apply open_start_imp; last done.
        right.
        rewrite /is_wr_lin_event.
        set_solver.
      + iPureIntro.
        simpl.
        intros k' Hk'_in v' Hlookup'.
        destruct (decide (k = k')) as [->|Hneq].
        * rewrite lookup_insert in Hlookup'.
          assert (v' = Some v) as ->; first set_solver. 
          right.
          exists v, [Wr (tag, c) k' v], tag.
          rewrite /open_trans /is_cm_op /connOfOp.
          set_solver.
        * rewrite lookup_insert_ne in Hlookup'; last done.
          specialize (Hlatest_keys k' Hk'_in v' Hlookup').
          destruct Hlatest_keys as [(-> & Himp)|(v1 & t & tag1 & _ & Hopen & _)].
          -- left.
             split; first done.
             intros t Hopen Hfalse.
             destruct Hopen as (op & Ht_in & Hlast & Hconn & Hcm).
             rewrite elem_of_app in Ht_in.
             destruct Ht_in as [Ht_in | Ht_in].
             ++ apply Hdec.
                exists t.
                split; first done.
                exists op.
                split_and!; try done.
                ** by apply last_Some_elem_of.
                ** rewrite /is_cm_op in Hcm.
                   rewrite /isCmOp.
                   destruct op; set_solver.
             ++ assert (t = [Wr (tag, c) k v]) as ->; set_solver.
          -- exfalso.
             destruct Hopen as (op & Ht_in & Hlast & Hconn & Hcm).
             apply Hdec.
             exists t.
             split; first done.
             exists op.
             split_and!; try done.
             ** by apply last_Some_elem_of.
             ** rewrite /is_cm_op in Hcm.
                rewrite /isCmOp.
                destruct op; set_solver.
    - iApply (big_sepS_wand with "[$Hdisj_trace_res]"). 
      iApply big_sepS_intro.
      iModIntro.
      iIntros (sa'' Hsa''_in) "Hres".
      iApply (client_trace_state_resources_neq1 sa sa'' T (Wr (tag, c) k v) c with "[][][][]"); try done.
      iPureIntro; set_solver.
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
      eapply valid_trace_ru_pre; try done.
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
      iExists (t ++ [(#tag1, init_pre_emit_event)%V]), lt, T.
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
    iInv "HinvExt" as ">[%t' [%lt' [%T' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & Hstate_res' & Hlin_res' & Hpost_res')]]]" "Hclose'".
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
    iAssert ((⌜mname !! sa = None⌝ ∧ ⌜no_emit_with_address sa lt' res⌝)%I) as "(%Hlookup_none & %Hno_emit)".
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
      destruct (exists_execution T') as [E' (Hbased' & Hvalid_exec')]; first set_solver.
      eexists T', E'.
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
      rewrite /GlobalInvExt.
      iExists (t' ++ [(#tag1, (c, #"InPost"))%V]), 
        (lt' ++ [(#tag1, (c, #"InLin"))%V]), T'.
      iFrame.
      do 2 (iSplit; first by iPureIntro).
      iSplit; first iPureIntro.
      {
        apply extraction_of_add_init_lin; rewrite /is_in_lin_event;
        set_solver.
      }
      do 2 (iSplit; first by iPureIntro).
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
    inv KVS_InvName (GlobalInvExt res γmstate γmlin γmpost γmname γl clients) -∗
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
      eapply valid_trace_ru_pre; try done.
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
      iExists (t ++ [(#tag1, (c, #"RdPre"))%V]), lt, T.
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
    iInv "HinvExt" as ">[%t' [%lt' [%T' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]]]" "Hclose'".
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
      rewrite /GlobalInvExt.
      iExists t', (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ wo))))%V]).
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
        iExists (T1 ++ (trans ++ [Rd (tag1, c) k wo]) :: T2).
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
                     apply (valid_sequence_wr_rd_lin _ _ tag1 c tail); try done.
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
                  ** 
                     admit.
                     (* iApply (trace_state_resources_read_lin clients c tag1 lt' T k sa wo
                        s γ γmstate γmname res mstate mname m with "[][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                        [$Hmap_m][Hdisj_trace_res][Htrace_res]"); try by iPureIntro.
                     iPureIntro.
                     destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                     exists e.
                     split_and!; try done.
                     apply elem_of_app; eauto. *)
      - iExists (T' ++ [[Rd (tag1, c) k wo]]).
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
                     apply (valid_sequence_wr_rd_lin _ _ tag1 c tail); try done.
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
                  ** iApply (trace_state_resources_read_lin1 clients c tag1 lt' T' k sa wo
                        s γ γmstate γmname res mstate mname m with "[][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
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
    iInv "HinvExt" as ">[%t'' [%lt'' [%T'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]]]" "Hclose''".
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
      eapply valid_trace_ru_post; try done; destruct wo;
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
      iExists (t'' ++ [_]), lt'', T''.
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
      eapply valid_trace_ru_pre; try done.
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
      iExists (t ++ [(#tag1, (c, #"WrPre"))%V]), lt, T.
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
                     apply (valid_sequence_wr_rd_lin _ _ tag1 c tail); try done.
                     --- left.
                         rewrite /is_wr_lin_event.
                         set_solver.
                     --- by exists t'.
                  ** admit.
                    (* iApply (trace_state_resources_write_lin clients c tag1 lt' k v.(SV_val) sa
                        s γ γmstate γmname res mstate mname m with "[][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                        [$Hmap_m][$Hdisj_trace_res][$Htrace_res]"); try by iPureIntro.
                     iPureIntro.
                     destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                     exists e.
                     split_and!; try done.
                     apply elem_of_app; eauto. *)
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
                     apply (valid_sequence_wr_rd_lin _ _ tag1 c tail); try done.
                     --- left.
                         rewrite /is_wr_lin_event.
                         set_solver.
                     --- by exists t'.
                  ** iApply (trace_state_resources_write_lin1 clients c tag1 lt' T' k v.(SV_val) sa
                        s γ γmstate γmname res mstate mname m with "[][][][][][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
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
      eapply valid_trace_ru_post; 
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
      iExists (t'' ++ [(#tag1, (c, (#"WrPost", (#k, v))))%V]), lt'', T''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_post_event /is_wr_post_event.
      set_solver.
    }
    set_solver.
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
      eapply valid_trace_ru_pre; try done.
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
      iExists (t ++ [(#tag1, (c, #"StPre"))%V]), lt, T.
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
        apply valid_sequence_st_lin; set_solver.
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
      eapply valid_trace_ru_post; 
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
      iExists (t'' ++ [(#tag1, (c, #"StPost"))%V]), lt'', T''.
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