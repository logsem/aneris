From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.examples.reliable_communication.lib.repdb.resources Require Import log_resources.
From aneris.aneris_lang.lib Require Import list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params aux_defs state_based_model.

Section trace_proof_util.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params}.

  Definition trace_inv_name := nroot.@"trinv".

  (** Ghost theory for wrapped resources *)

  Definition OwnLinTrace (γ : gname) (l : list val) : iProp Σ := 
    own_log_auth γ 1%Qp l.

  Definition OwnLinHist (γ : gname) (l : list val) : iProp Σ :=
    own_log_obs γ l.

  Lemma own_lin_hist (γ : gname) (l : list val) :
    OwnLinTrace γ l ==∗ OwnLinTrace γ l ∗ OwnLinHist γ l.
  Proof.
    rewrite /OwnLinTrace /OwnLinHist.
    iIntros "H1".
    iDestruct (get_obs with "H1") as "#H2".
    iModIntro.
    iFrame "#∗".
  Qed.

  Lemma own_lin_prefix (γ : gname) (l h : list val) :
    OwnLinTrace γ l ∗ OwnLinHist γ h -∗
    OwnLinTrace γ l ∗ OwnLinHist γ h ∗ ⌜h `prefix_of` l⌝.
  Proof.
    rewrite /OwnLinTrace /OwnLinHist.
    iIntros "(H1 & H2)".
    iDestruct (own_obs_prefix with "[$H1][$H2]") as "%Hpre".
    iFrame.
    by iPureIntro.
  Qed.

  Lemma own_lin_add (γ : gname) (l: list val) (v : val) :
    OwnLinTrace γ l ==∗ OwnLinTrace γ (l ++ [v]).
  Proof.
    rewrite /OwnLinTrace.
    iIntros "H1".
    by iMod (own_log_auth_update _ _ (l ++ [v]) with "[$H1]") as "HlFull"; 
      first by apply prefix_app_r.
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
  
  Definition com_true (trans : list operation) : Prop := ∃ s, last trans = Some (Cm s true).

  Definition tag_eq (e1 e2 : val) : Prop := ∃ tag, tagOfEvent e1 = Some tag ∧ tagOfEvent e2 = Some tag.

  Definition no_emit_with_address (sa : socket_address) (ltrace : list val) (extract : val → option val)  : Prop := 
    ¬∃ e c, e ∈ ltrace ∧ connOfEvent e = Some c ∧ extract c = Some #sa.

  Definition active_trace_resources lt T s c (γ : gname) (m : gmap Key (option val)) : iProp Σ :=
    ∃ domain sub_domain tail, ⌜s = Active domain⌝ ∗ 
      ⌜sub_domain = domain ∩ KVS_keys⌝ ∗ ⌜open_start c lt tail⌝ ∗ 
      ([∗ set] k ∈ KVS_keys ∖ sub_domain, ∃ (ov : option val), ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ 
      (∀ k, ⌜k ∈ sub_domain⌝ → ∀ (ov : option val), ⌜m !! k = Some ov⌝ → ⌜latest_write c k ov T⌝).

  Definition inactive_trace_resources lt T s c (γ : gname) : iProp Σ :=
    ⌜s = CanStart⌝ ∗ ⌜commit_closed c lt⌝ ∗ ⌜¬∃ t, open_trans t c T⌝ ∗
    ([∗ set] k ∈ KVS_keys, ∃ (ov : option val), ghost_map_elem γ k (DfracOwn 1%Qp) ov).

  Definition initialized_trace_resources lt T sa (γmname : gname) (extract : val → option val)
  (mstate : gmap socket_address (local_state * option val)) : iProp Σ :=
    ∃ (s : local_state) (c : val) (γ : gname) (m : gmap Key (option val)), ⌜mstate !! sa = Some (s, Some c)⌝ ∗
      ⌜extract c = Some #(LitSocketAddress sa)⌝ ∗ 
      ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
      ghost_map_auth γ (1%Qp) m ∗ 
      ⌜(∃ e, e ∈ lt ∧ connOfEvent e = Some c ∧ is_in_lin_event e)⌝ ∗ 
      (inactive_trace_resources lt T s c γ ∨ active_trace_resources lt T s c γ m).

  Definition unnitialized_trace_resources sa (mstate : gmap socket_address (local_state * option val)) 
  (mname : gmap socket_address (gname * val)) lt (extract : val → option val) : Prop := 
    (mstate !! sa = None ∨ mstate !! sa = Some (CanStart, None)) ∧ 
    (¬∃ p, mname !! sa = Some p) ∧ no_emit_with_address sa lt extract.

  Definition client_trace_state_resources (lt : list val) (T : list transaction) (sa : socket_address) 
  (γmstate γmname : gname) (extract : val → option val)  (mstate : gmap socket_address (local_state * option val)) 
  (mname : gmap socket_address (gname * val)) : iProp Σ := 
    ⌜unnitialized_trace_resources sa mstate mname lt extract⌝ ∨ initialized_trace_resources lt T sa γmname extract mstate.

  Definition trace_state_resources (lt : list val) (T : list transaction) (γmstate γmname : gname) 
  (clients : gset socket_address) (extract : val → option val) : iProp Σ := 
    ∃ (mstate : gmap socket_address (local_state * option val)), ghost_map_auth γmstate (1%Qp) mstate ∗ 
      ∃ (mname : gmap socket_address (gname * val)), ghost_map_auth γmname (1%Qp) mname ∗ 
        ([∗ set] sa ∈ clients, client_trace_state_resources lt T sa γmstate γmname extract mstate mname).

  Definition GlobalInvExt (test : commitTest) (T : list transaction) (extract : val → option val) 
    (γmstate γmlin γmpost γmname γl : gname) (clients : gset socket_address) (exec : execution) : iProp Σ := 
    ∃ t lt, trace_is t ∗ OwnLinTrace γl lt ∗ ⌜lin_trace_of lt t⌝ ∗ ⌜∀ t, t ∈ T → t ≠ []⌝ ∗
      ⌜extraction_of lt T⌝ ∗ ⌜valid_transactions T⌝ ∗ ⌜valid_sequence lt⌝ ∗
      ⌜based_on exec (comTrans T)⌝ ∗ ⌜valid_execution test exec⌝ ∗
      trace_state_resources lt T γmstate γmname clients extract ∗
      trace_lin_resources lt t γmlin ∗
      trace_post_resources t γmpost.

  (* Helper lemmas *)

  Lemma trans_eq c T1 T2 trans trans' :
    open_trans trans' c (T1 ++ trans :: T2) →
    valid_transactions (T1 ++ trans :: T2) →
    (∃ op, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) →
    trans = trans'.
  Proof.
    intros Hopen_trans Hvalid_trans Hop.
    destruct Hvalid_trans as (_ & Hvalid_trans & _).
    destruct Hopen_trans as (op_last & Htrans'_in & Hlast' & Hconn_last' & Hcm_last').
    assert (trans ∈ T1 ++ trans :: T2) as Htrans_in; first set_solver.
    rewrite elem_of_list_lookup in Htrans_in.
    rewrite elem_of_list_lookup in Htrans'_in.
    destruct Htrans_in as (i & Htrans_in).
    destruct Htrans'_in as (i' & Htrans'_in).
    assert (i = i'); last set_solver.
    destruct Hop as (op & _ & Hlast & Hop_conn & Hop_cm).
    apply (Hvalid_trans trans trans' op op_last i i' c); try done.
    intros (tag_cm & b & ->).
    by simpl in Hop_cm.
  Qed.

  Lemma com_trans_in trans T : 
    trans ∈ T →
    com_true trans →
    trans ∈ comTrans T.
  Proof.
    intros Hin Hcom.
    destruct (elem_of_list_split _ _ Hin) as (T1 & T2 & ->).
    rewrite /comTrans.
    rewrite List.filter_app.
    apply elem_of_app; right.
    simpl.
    destruct Hcom as (s & ->).
    set_solver.
  Qed.

  Lemma commit_closed_neq (extract : val → option val) sa sa' c c' lt e : 
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

  Lemma open_start_neq (extract : val → option val) sa sa' c c' lt tail e : 
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

  Lemma open_trans_neq1 (extract : val → option val) sa sa' c c' t T op : 
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

  Lemma open_trans_neq2 (extract : val → option val) sa sa' c c' t T op : 
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

 Lemma open_trans_neq3 (extract : val → option val) sa sa' c c' t T1 T2 trans op : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfOp op = c →
    open_trans t c' (T1 ++ (trans ++ [op]) :: T2) →
    open_trans t c' (T1 ++ trans :: T2).
  Proof.
    intros Hneq Hextract Hextract' Hconn (op' & Hin & Hlast & Hconn' & Hcom).
    exists op'.
    split_and!; try done.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; first set_solver.
    rewrite elem_of_cons in Hin.
    destruct Hin as [Hin|Hin]; last set_solver.
    exfalso.
    subst.
    rewrite last_snoc in Hlast.
    set_solver.
  Qed.

   Lemma open_trans_neq4 (extract : val → option val) sa sa' c c' t T1 T2 trans op : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfOp op = c →
    (∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) →
    open_trans t c' (T1 ++ trans :: T2) →
    open_trans t c' (T1 ++ (trans ++ [op]) :: T2).
  Proof.
    intros Hneq Hextract Hextract' Hconn Hop (op' & Hin & Hlast & Hconn' & Hcom).
    exists op'.
    split_and!; try done.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; first set_solver.
    rewrite elem_of_cons in Hin.
    destruct Hin as [Hin|Hin]; last set_solver.
    exfalso.
    destruct Hop as (op'' & _ & Hlast' & Heq_conn & _).
    subst.
    assert (op'' = op') as <-; first set_solver.
    assert (Some #sa = Some #sa') as xcv; last set_solver.
    rewrite Heq_conn in Hextract'.
    set_solver.
  Qed.

  Lemma latest_neq1 (extract : val → option val) sa sa' c c' T op k v : 
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

  Lemma latest_neq2 (extract : val → option val) sa sa' c c' T1 T2 trans op k v : 
    sa ≠ sa' →
    extract c = Some #sa →
    extract c' = Some #sa' →
    connOfOp op = c →
    (∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) →
    latest_write c' k v (T1 ++ trans :: T2) →
    latest_write c' k v (T1 ++ (trans ++ [op]) :: T2).
  Proof.
    intros Hneq Hextract Hextract' Hconn Hop [(-> & Himp)|(v' & t & tag & -> & Hopen & Hin & Himp)].
    - left.
      split; first done.
      intros t Hopen.
      apply Himp.
      by eapply open_trans_neq3 in Hopen.
    - right.
      exists v', t, tag.
      split_and!; try done.
      by eapply open_trans_neq4 in Hopen.
  Qed.

  Lemma two_trans_implies_false_app_cons (T1 T2 : list transaction) trans c : 
    valid_transactions (T1 ++ trans :: T2) →
    (∃ op, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) →
    (∃ trans', (trans' ∈ T1 ∨ trans' ∈ T2) ∧ (∃ op' : operation,
      op' ∈ trans' ∧ last trans' = Some op' ∧ connOfOp op' = c ∧ isCmOp op' = false)) →
    false.
  Proof.
    intros Hvalid_trans' Hop (trans' & Htrans'_in & Hop').
    destruct Hvalid_trans' as (_ & Hvalid_trans' & _).
    assert (length T1 = length T1) as Htrans_in'; first set_solver.
    apply (list_lookup_middle T1 T2 trans) in Htrans_in'.
    destruct Hop' as (op' & Hop'_in & Hop'_last & Hop'_conn & Hop'_cm).
    destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
    rewrite /isCmOp in Hop_cm.
    rewrite /isCmOp in Hop'_cm.
    destruct Htrans'_in as [Htrans'_in|Htrans'_in].
    +++ apply elem_of_list_lookup_1 in Htrans'_in.
        destruct Htrans'_in as (j & Htrans'_in).
        pose proof Htrans'_in as Htrans'_in'. 
        apply lookup_lt_Some in Htrans'_in'.
        apply (lookup_app_l_Some _ (trans :: T2)) in Htrans'_in.
        assert (length T1 = j) as <-; 
          last by eapply PeanoNat.Nat.lt_irrefl.
        eapply (Hvalid_trans' _ _ op op'); try done; 
        rewrite /is_cm_op; set_solver.
    +++ apply elem_of_list_lookup_1 in Htrans'_in.
        destruct Htrans'_in as (j & Htrans'_in).
        assert ((1 <= (j + 1))%nat ∧ T2 !! ((j + 1) - 1)%nat = Some trans') as (Hleq & Hlookup_j').
        {
          split; try lia.
          by assert (j + 1 - 1 = j)%nat as ->; first lia.
        }
        assert ((trans :: T2) !! (j + 1)%nat = Some trans') as Hlookup_j_cons.
        {
          apply lookup_cons_Some; set_solver.
        }
        assert ((length T1 <= j + 1 + length T1)%nat ∧ (trans :: T2) !! (((j + 1 + length T1) - length T1)%nat) = Some trans') 
          as (Hleq'' & Hlookup_j'').
        {
          split; try lia.
          by assert (j + 1 + length T1 - length T1 = j + 1)%nat as ->; first lia.
        }
        assert ((T1 ++ trans :: T2) !! (j + 1 + length T1)%nat = Some trans') as Hlookup_j_app.
        {
          apply lookup_app_Some; set_solver.
        } 
        assert (length T1 = (j + 1 + length T1)%nat) as Heq; last lia.
        eapply (Hvalid_trans' _ _ op op'); try done; 
        rewrite /is_cm_op; set_solver.
  Qed.

  Lemma latest_write_preserve tag c T1 T2 trans k k' v ov : 
    k ≠ k' →
    valid_transactions (T1 ++ trans :: T2) →
    (∃ op, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) →
    latest_write c k' ov (T1 ++ trans :: T2) →
    latest_write c k' ov (T1 ++ (trans ++ [Wr (tag, c) k v]) :: T2).
  Proof.
    intros Hneq Hvalid_trans Htrans [(-> & Himp)|(v' & t & tag1 & -> & Hopen & Hwr_in & Himp)].
    - left.
      split; first done.
      intros t (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
      rewrite elem_of_app in Hop_in.
      destruct Hop_in as [Hop_in|Hop_in].
      + apply Himp.
        exists op.
        set_solver.
      + rewrite elem_of_cons in Hop_in.
        destruct Hop_in as [->|Hop_in].
        * intros Hwr.
          apply (Himp trans); last set_solver.
          rewrite /open_trans /is_cm_op /isCmOp; set_solver.
        * apply Himp.
          exists op.
          set_solver.
    - right.
      exists v', (trans ++ [Wr (tag, c) k v]), tag1.
      assert (trans = t) as <-.
      {
        destruct Hopen as (op' & Hop'_in & Hop'_last & Hop'_conn & Hop'_cm).
        rewrite elem_of_app in Hop'_in.
        destruct Hop'_in as [Hop'_in | Hop'_in].
        - exfalso.
          eapply (two_trans_implies_false_app_cons T1 T2 trans); try done.
          exists t.
          split; first set_solver.
          exists op'.
          split_and!; try done.
          + by apply last_Some_elem_of.
          + rewrite /isCmOp. 
            rewrite /is_cm_op in Hop'_cm.
            destruct op'; set_solver.
        - rewrite elem_of_cons in Hop'_in.
          destruct Hop'_in as [-> | Hop'_in]; first done.
          exfalso.
          eapply (two_trans_implies_false_app_cons T1 T2 trans); try done.
          exists t.
          split; first set_solver.
          exists op'.
          split_and!; try done.
          + by apply last_Some_elem_of.
          + rewrite /isCmOp. 
            rewrite /is_cm_op in Hop'_cm.
            destruct op'; set_solver.
      }
      split_and!; try done.
      + rewrite /open_trans.
        exists (Wr (tag, c) k v).
        split_and!; try done.
        * set_solver.
        * by rewrite last_snoc.
        * rewrite /is_cm_op; set_solver.
      + set_solver.
      + intros op Hop_in Hop_eq.
        apply rel_list_imp.
        apply Himp; set_solver.
  Qed.

  Lemma unique_init_events_add_init (lt t : list val) (tag : string) (c : val) 
  (sa : socket_address) (extract : val → option val) :
    extract c = Some #sa →
    no_emit_with_address sa lt extract →
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
  (extract : val → option val) :
    connOfEvent le = Some c →
    sa ≠ sa' →
    extract c = Some #sa →
    unnitialized_trace_resources sa' mstate mname lt extract →
    unnitialized_trace_resources sa' mstate mname (lt ++ [le]) extract.
  Proof.
    intros Hconn Hneq Hextract (Hunit1 & Hunit2 & Hunit3).
    split_and!; try done.
    intros (e & c' & Hin &Hconn' & Hextract').
    apply Hunit3.
    rewrite elem_of_app in Hin.
    destruct Hin as [Hin|Hin]; set_solver.
  Qed.

  Lemma unnitialized_trace_resources_neq2 (sa sa' : socket_address) lt c le mstate mname 
  (extract : val → option val) p :
    connOfEvent le = Some c →
    sa ≠ sa' →
    extract c = Some #sa →
    unnitialized_trace_resources sa' mstate mname lt extract →
    unnitialized_trace_resources sa' (<[sa:=p]> mstate) mname (lt ++ [le]) extract.
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
  (extract : val → option val) p1 p2 :
    connOfEvent le = Some c →
    sa ≠ sa' →
    extract c = Some #sa →
    unnitialized_trace_resources sa' mstate mname lt extract →
    unnitialized_trace_resources sa' (<[sa:=p1]> mstate) (<[sa:=p2]> mname) (lt ++ [le]) extract.
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
  γmname mstate (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    initialized_trace_resources lt T sa' γmname extract mstate -∗
    initialized_trace_resources  (lt ++ [le]) T sa' γmname extract mstate.
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
  γmname mstate p (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    initialized_trace_resources lt T sa' γmname extract mstate -∗
    initialized_trace_resources  (lt ++ [le]) T sa' γmname extract (<[sa:=p]> mstate).
  Proof.
    iIntros (Hneq Hextract Hconn) "Hres".
    rewrite /initialized_trace_resources.
    rewrite lookup_insert_ne; last done.
    by iApply (initialized_trace_resources_neq1 sa sa' c with "[][][][$Hres]"). 
  Qed.

  Lemma initialized_trace_resources_neq3 (sa sa' : socket_address) op c le lt T
  γmname mstate (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    initialized_trace_resources lt T sa' γmname extract mstate -∗
    initialized_trace_resources  (lt ++ [le]) (T ++ [[op]]) sa' γmname extract mstate.
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
            eapply (latest_neq1 _ sa sa'); set_solver.
  Qed.

  Lemma initialized_trace_resources_neq4 (sa sa' : socket_address) op c le lt T1 T2 trans
  γmname mstate (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    ⌜(∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false)⌝ -∗
    initialized_trace_resources lt (T1 ++ trans :: T2) sa' γmname extract mstate -∗
    initialized_trace_resources  (lt ++ [le]) (T1 ++ (trans ++ [op]) :: T2) sa' γmname extract mstate.
  Proof.
    iIntros (Hneq Hextract Hconn Hconn' Hop) "Hres".
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
            eapply (open_trans_neq3 _ sa sa'); set_solver.
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
            eapply (latest_neq2 _ sa sa'); set_solver.
  Qed.

  Lemma initialized_trace_resources_neq5 (sa sa' : socket_address) c le lt T op
  γmname mstate p (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    initialized_trace_resources lt T sa' γmname extract mstate -∗
    initialized_trace_resources  (lt ++ [le]) (T ++ [[op]]) sa' γmname extract (<[sa:=p]> mstate).
  Proof.
    iIntros (Hneq Hextract Hconn_le Hconn_op) "Hres".
    rewrite /initialized_trace_resources.
    rewrite lookup_insert_ne; last done.
    by iApply (initialized_trace_resources_neq3 sa sa' with "[][][][]"). 
  Qed.

  Lemma initialized_trace_resources_neq6 (sa sa' : socket_address) c le lt T1 T2 trans op
  γmname mstate p (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    ⌜(∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false)⌝ -∗
    initialized_trace_resources lt (T1 ++ trans :: T2) sa' γmname extract mstate -∗
    initialized_trace_resources (lt ++ [le]) (T1 ++ (trans ++ [op]) :: T2) sa' γmname extract (<[sa:=p]> mstate).
  Proof.
    iIntros (Hneq Hextract Hconn_le Hconn_op Hop) "Hres".
    rewrite /initialized_trace_resources.
    rewrite lookup_insert_ne; last done.
    iApply (initialized_trace_resources_neq4 sa sa'); try done. 
  Qed.

  Lemma client_trace_state_resources_neq1 (sa sa' : socket_address) T op c le lt 
  γstate γmname mstate mname (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    client_trace_state_resources lt T sa' γstate γmname extract mstate mname -∗
    client_trace_state_resources (lt ++ [le]) (T ++ [[op]]) sa' γstate γmname extract mstate mname.
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
  γstate γmname mstate mname p (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    client_trace_state_resources lt T sa' γstate γmname extract mstate mname -∗
    client_trace_state_resources (lt ++ [le]) T sa' γstate γmname extract (<[sa:=p]> mstate) mname.
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
  γstate γmname mstate mname p1 p2 (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    client_trace_state_resources lt T sa' γstate γmname extract mstate mname -∗
    client_trace_state_resources (lt ++ [le]) T sa' γstate γmname extract (<[sa:=p1]> mstate) (<[sa:=p2]> mname).
  Proof.
    iIntros (Hneq Hextract Hconn) "Hres".
    iDestruct "Hres" as "[%Hres|Hres]".
    - iLeft.
      iPureIntro.
      by apply (unnitialized_trace_resources_neq3 sa sa' lt c).
    - iRight.
      by iApply (initialized_trace_resources_neq2 sa sa' c with "[][][][$]").
  Qed.

  Lemma client_trace_state_resources_neq4 (sa sa' : socket_address) T1 T2 trans op c le lt 
  γstate γmname mstate mname (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    ⌜(∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false)⌝ -∗
    client_trace_state_resources lt (T1 ++ trans :: T2) sa' γstate γmname extract mstate mname -∗
    client_trace_state_resources (lt ++ [le]) (T1 ++ (trans ++ [op]) :: T2) sa' γstate γmname extract mstate mname.
  Proof.
    iIntros (Hneq Hextract Hconn Hconn' Hop) "Hres".
    iDestruct "Hres" as "[%Hres|Hres]".
    - iLeft.
      iPureIntro.
      by apply (unnitialized_trace_resources_neq1 sa sa' lt c).
    - iRight.
      by iApply (initialized_trace_resources_neq4 sa sa' op c with "[][][][][]").
  Qed.

  Lemma client_trace_state_resources_neq5 (sa sa' : socket_address) c le lt T op
  γstate γmname mstate mname p (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    client_trace_state_resources lt T sa' γstate γmname extract mstate mname -∗
    client_trace_state_resources (lt ++ [le]) (T ++ [[op]]) sa' γstate γmname extract (<[sa:=p]> mstate) mname.
  Proof.
    iIntros (Hneq Hextract Hconn_le Hconn_op) "Hres".
    iDestruct "Hres" as "[%Hres|Hres]".
    - iLeft.
      iPureIntro.
      by apply (unnitialized_trace_resources_neq2 sa sa' lt c).
    - iRight.
      by iApply (initialized_trace_resources_neq5 sa sa' c with "[][][][][$]").
  Qed.

  Lemma client_trace_state_resources_neq6 (sa sa' : socket_address) c le lt T1 T2 trans op
  γstate γmname mstate mname p (extract : val → option val) :
    ⌜sa ≠ sa'⌝ -∗
    ⌜extract c = Some #sa⌝ -∗
    ⌜connOfEvent le = Some c⌝ -∗
    ⌜connOfOp op = c⌝ -∗
    ⌜(∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false)⌝ -∗
    client_trace_state_resources lt (T1 ++ trans :: T2) sa' γstate γmname extract mstate mname -∗
    client_trace_state_resources (lt ++ [le]) (T1 ++ (trans ++ [op]) :: T2) sa' γstate γmname extract (<[sa:=p]> mstate) mname.
  Proof.
    iIntros (Hneq Hextract Hconn_le Hconn_op Hop) "Hres".
    iDestruct "Hres" as "[%Hres|Hres]".
    - iLeft.
      iPureIntro.
      by apply (unnitialized_trace_resources_neq2 sa sa' lt c).
    - iRight.
      iApply (initialized_trace_resources_neq6 sa sa' c with "[][][][][]"); try done.
  Qed.

  Lemma trace_state_resources_read_lin1 (clients : gset socket_address) (c : val) (tag : string) (lt : list val) (T : list transaction)
  (k : Key) (sa : socket_address) (wo : option val) (s : local_state) (γ γmstate γmname : gname) (extract : val → option val) 
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
    ([∗ set] y ∈ (clients ∖ {[sa]}), ⌜unnitialized_trace_resources y mstate mname lt extract⌝
      ∨ initialized_trace_resources lt T y γmname extract mstate) -∗
    active_trace_resources lt T s c γ m -∗
    trace_state_resources (lt ++ [(#tag, (c, (#"RdLin", (#k, $wo))))%V]) (T ++ [[Rd (tag, c) k wo]]) γmstate γmname clients extract.
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

  Lemma trace_state_resources_read_lin2 (clients : gset socket_address) (c : val) (tag : string) (lt : list val) 
  (T1 T2 : list transaction) (trans : transaction)
  (k : Key) (sa : socket_address) (wo : option val) (s : local_state) (γ γmstate γmname : gname) (extract : val → option val) 
  (mstate : gmap socket_address (local_state * option val)) (mname : gmap socket_address (gname * val)) (m : gmap Key (option val)) :
    ⌜mstate !! sa = Some (s, Some c)⌝ -∗ 
    ⌜extract c = Some #sa⌝ -∗ 
    ⌜clients = {[sa]} ∪ clients ∖ {[sa]}⌝ -∗
    ⌜¬ (∃ trans : transaction, (trans ∈ T1 ∨ trans ∈ T2) ∧ (∃ op' : operation,
          op' ∈ trans ∧ last trans = Some op' ∧ connOfOp op' = c ∧ isCmOp op' = false))⌝ -∗
    ⌜(∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false)⌝ -∗
    ⌜∃ e : val, e ∈ lt ++ [(#tag, (c, (#"RdLin", (#k, $wo))))%V] ∧ 
      connOfEvent e = Some c ∧ is_in_lin_event e⌝ -∗
    ghost_map_elem γmname sa DfracDiscarded (γ, c) -∗ 
    ghost_map_auth γmstate 1 mstate -∗
    ghost_map_auth γmname 1 mname -∗
    ghost_map_auth γ 1 m -∗
    ([∗ set] y ∈ (clients ∖ {[sa]}), ⌜unnitialized_trace_resources y mstate mname lt extract⌝
      ∨ initialized_trace_resources lt (T1 ++ trans :: T2) y γmname extract mstate) -∗
    active_trace_resources lt (T1 ++ trans :: T2) s c γ m -∗
    trace_state_resources (lt ++ [(#tag, (c, (#"RdLin", (#k, $wo))))%V]) (T1 ++ (trans ++ [Rd (tag, c) k wo]) :: T2) γmstate γmname clients extract.
  Proof.
    iIntros (Hlookup Hextract Heq_sa_clients Hdec Hop) "#Hinit_in #Hpers_pointer Hmap_mstate Hmap_mname Hmap_m Hdisj_trace_res Htrace_res".
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
        * specialize (Hlatest_keys k' Hk'_in (Some v') Hlookup').
          destruct Hlatest_keys as [Hfalse|(v1 & t & tag1 & asd & Hopen & Hwr_in & Himp)]; first set_solver.
          destruct Hopen as (op & Ht_in & Hlast & Hconn & Hcm).
          rewrite elem_of_app in Ht_in.
          destruct Ht_in as [Ht_in|Ht_in].
          -- exfalso.
             apply Hdec.
             exists t.
             split; first set_solver.
             exists op.
             split_and!; try done; first by apply last_Some_elem_of.
             rewrite /is_cm_op in Hcm.
             rewrite /isCmOp.
             destruct op; set_solver.
          -- rewrite elem_of_cons in Ht_in.
             destruct Ht_in as [Ht_in|Ht_in].
             ++ subst. 
                right.
                exists v', (trans ++ [Rd (tag, connOfOp op) k wo]), tag1.
                split_and!; try done.
                ** exists (Rd (tag, connOfOp op) k wo).
                   rewrite last_snoc /is_cm_op; simpl; set_solver.
                ** set_solver.
                ** intros op' Hop'_in Hop'_wr.
                   apply rel_list_imp.
                   set_solver.
             ++ exfalso.
                apply Hdec.
                exists t.
                split; first set_solver.
                exists op.
                split_and!; try done; first by apply last_Some_elem_of.
                rewrite /is_cm_op in Hcm.
                rewrite /isCmOp.
                destruct op; set_solver.
        * specialize (Hlatest_keys k' Hk'_in None Hlookup').
          left.
          split; first done.
          intros t Hopen Hwr.
          destruct Hlatest_keys as [(_ & Hlatest)|Hfalse]; last set_solver.
          destruct Hopen as (op' & Ht_in & Hop'_last & Hop'_conn & Hop'_cm).
          rewrite elem_of_app in Ht_in.
          destruct Ht_in as [Ht_in|Ht_in].
          -- apply (Hlatest t); rewrite /open_trans; set_solver.
          -- rewrite elem_of_cons in Ht_in.
             destruct Ht_in as [Ht_in|Ht_in].
             ++ apply (Hlatest trans); last set_solver.
                rewrite /open_trans.
                destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
                exists op; split_and!; try done; first set_solver.
                rewrite /is_cm_op.
                rewrite /isCmOp in Hop_cm.
                destruct op; set_solver.
             ++ apply (Hlatest t); rewrite /open_trans; set_solver.
    - iApply (big_sepS_wand with "[$Hdisj_trace_res]"). 
      iApply big_sepS_intro.
      iModIntro.
      iIntros (sa'' Hsa''_in) "Hres".
      iApply (client_trace_state_resources_neq4 sa sa'' T1 T2 trans (Rd (tag, c) k wo) c with "[][][][]"); try done.
      iPureIntro; set_solver.
  Qed.

  Lemma trace_state_resources_write_lin1 (clients : gset socket_address) (c : val) (tag : string) (lt : list val) (T : list transaction)
  (k : Key) (v : val) (sa : socket_address) (s : local_state) (γ γmstate γmname : gname) (extract : val → option val) 
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
    ([∗ set] y ∈ (clients ∖ {[sa]}), ⌜unnitialized_trace_resources y mstate mname lt extract⌝
      ∨ initialized_trace_resources lt T y γmname extract mstate) -∗
    active_trace_resources lt T s c γ m -∗
    trace_state_resources (lt ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]) (T ++ [[Wr (tag, c) k v]]) γmstate γmname clients extract.
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

  Lemma trace_state_resources_write_lin2 (clients : gset socket_address) (c : val) (tag : string) (lt : list val) (T1 T2 : list transaction)
  (trans : transaction) (k : Key) (v : val) (sa : socket_address) (s : local_state) (γ γmstate γmname : gname) (extract : val → option val) 
  (mstate : gmap socket_address (local_state * option val)) (mname : gmap socket_address (gname * val)) (m : gmap Key (option val)) :
    ⌜valid_transactions (T1 ++ trans :: T2)⌝ -∗ 
    ⌜mstate !! sa = Some (s, Some c)⌝ -∗ 
    ⌜extract c = Some #sa⌝ -∗ 
    ⌜clients = {[sa]} ∪ clients ∖ {[sa]}⌝ -∗
    ⌜¬ (∃ trans, (trans ∈ T1 ∨ trans ∈ T2) ∧ (∃ op' : operation,
          op' ∈ trans ∧ last trans = Some op' ∧ connOfOp op' = c ∧ isCmOp op' = false))⌝ -∗
    ⌜(∃ op : operation, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false)⌝ -∗
    ⌜∃ e : val, e ∈ lt ++ [(#tag, (c, (#"WrLin", (#k, v))))%V] ∧ 
      connOfEvent e = Some c ∧ is_in_lin_event e⌝ -∗
    ghost_map_elem γmname sa DfracDiscarded (γ, c) -∗ 
    ghost_map_auth γmstate 1 mstate -∗
    ghost_map_auth γmname 1 mname -∗
    ghost_map_auth γ 1 (<[k:=Some v]> m) -∗
    ([∗ set] y ∈ (clients ∖ {[sa]}), ⌜unnitialized_trace_resources y mstate mname lt extract⌝
      ∨ initialized_trace_resources lt (T1 ++ trans :: T2) y γmname extract mstate) -∗
    active_trace_resources lt (T1 ++ trans :: T2) s c γ m -∗
    trace_state_resources (lt ++ [(#tag, (c, (#"WrLin", (#k, v))))%V]) (T1 ++ (trans ++ [Wr (tag, c) k v]) :: T2) γmstate γmname clients extract.
  Proof.
    iIntros (Hvalid_trans Hlookup Hextract Heq_sa_clients Hdec Hop) "#Hinit_in #Hpers_pointer Hmap_mstate Hmap_mname Hmap_m Hdisj_trace_res Htrace_res".
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
          exists v, (trans ++ [Wr (tag, c) k' v]), tag.
          split_and!; try done.
          -- exists (Wr (tag, c) k' v).
             split_and; try done; first set_solver.
             rewrite last_snoc /open_trans /is_cm_op /connOfOp.
             set_solver.
          -- set_solver.
          -- intros op Hop_in Hop_eq.
             apply elem_of_list_lookup_1 in Hop_in.
             destruct Hop_in as (i & Hop_in).
             exists i, (length trans).
             pose proof (lookup_lt_Some _ _ _ Hop_in) as Hlength.
             destruct (decide (i = length trans)) as [-> | Hneq].
             ++ rewrite lookup_snoc_Some in Hop_in.
                destruct Hop_in as [(Hfalse & _) | (_ & <-)]; first lia; set_solver.
             ++ split_and!; try done.
                ** rewrite app_length in Hlength.
                   simpl in Hlength.
                   lia.
                ** apply lookup_snoc_Some; set_solver.
        * rewrite lookup_insert_ne in Hlookup'; last done.
          specialize (Hlatest_keys k' Hk'_in v' Hlookup').
          by apply latest_write_preserve.
    - iApply (big_sepS_wand with "[$Hdisj_trace_res]"). 
      iApply big_sepS_intro.
      iModIntro.
      iIntros (sa'' Hsa''_in) "Hres".
      iApply (client_trace_state_resources_neq4 sa sa'' T1 T2 trans (Wr (tag, c) k v) c with "[][][][]"); try done.
      iPureIntro; set_solver.
  Qed.

  Lemma trace_state_resources_commit_lin1 (clients : gset socket_address) (c : val) (tag : string) (lt : list val) (T : list transaction)
  (sa : socket_address) (s : gset Key) (γ γmstate γmname : gname) (extract : val → option val) (b : bool)
  (mc : gmap Key (option val)) (mstate : gmap socket_address (local_state * option val)) 
  (mname : gmap socket_address (gname * val)) (m : gmap Key (option val)) :
    ⌜¬(∃ e : val, e ∈ lt ∧ tagOfEvent e = Some tag)⌝ -∗
    ⌜dom mc = s⌝ -∗
    ⌜valid_sequence lt⌝ -∗
    ⌜mstate !! sa = Some (Active s, Some c)⌝ -∗ 
    ⌜extract c = Some #sa⌝ -∗ 
    ⌜clients = {[sa]} ∪ clients ∖ {[sa]}⌝ -∗
    ⌜¬ (∃ trans, trans ∈ T ∧ (∃ op' : operation,
      op' ∈ trans ∧ last trans = Some op' ∧ connOfOp op' = c ∧ isCmOp op' = false))⌝ -∗
    ⌜∃ e, e ∈ lt ++ [(#tag, (c, (#"CmLin", #b)))%V] ∧ connOfEvent e = Some c ∧ is_in_lin_event e⌝ -∗
    ([∗ map] k↦x ∈ mc, ∃ (sa0 : socket_address) (γ0 : gname), ghost_map_elem γmname sa0 DfracDiscarded (γ0, c) ∗ 
    ⌜extract c = Some #sa0⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ0 k (DfracOwn 1%Qp) x) ∗ ⌜sa0 ∈ clients⌝) -∗
    ghost_map_elem γmname sa DfracDiscarded (γ, c) -∗ 
    ghost_map_auth γmstate 1 (<[sa:=(CanStart, Some c)]> mstate) -∗ 
    ghost_map_auth γmname 1 mname -∗
    ghost_map_auth γ 1 m -∗
    ([∗ set] y ∈ (clients ∖ {[sa]}), client_trace_state_resources lt T y γmstate γmname extract mstate mname) -∗
    active_trace_resources lt T (Active s) c γ m -∗
    trace_state_resources (lt ++ [(#tag, (c, (#"CmLin", #b)))%V]) (T ++ [[Cm (tag, c) b]]) γmstate γmname clients extract.
  Proof.
    iIntros (Hnot_in Hdom_eq Hvalid_seq Hlookup Hextract Heq_sa_clients Hdec) 
      "#Hinit_in Hkeys_conn #Hsa_pointer Hmap_mstate Hmap_mname Hmap_m Hdisj_trace_res Htrace_res".
    iExists (<[sa:=(CanStart, Some c)]> mstate). 
    iFrame.
    iExists mname.
    iFrame.
    rewrite {3} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iSplitR "Hdisj_trace_res".
    - rewrite big_sepS_singleton.
      iRight.
      iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & 
      %Heq_act & -> & %Hopen_start & Hkeys & %Hlatest_keys)". 
      iExists CanStart, c, γ, m.
      rewrite lookup_insert.
      do 2 (iSplit; first by iPureIntro).
      iFrame "∗#".
      iLeft.
      iSplit; first done.
      iSplit.
      {
        iPureIntro.
        eapply commit_closed_valid_seq;
          rewrite /is_cm_lin_event; set_solver. 
      }
      iSplit.
      {
        iPureIntro.
        intros (trans & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
        rewrite elem_of_app in Hop_in.
        destruct Hop_in as [Hop_in|Hop_in].
        - apply Hdec.
          exists trans.
          pose proof (last_Some_elem_of _ _ Hop_last) as Hop_in'.
          split; first done.
          exists op.
          split_and!; try done.
          rewrite /isCmOp.
          rewrite /is_cm_op in Hop_cm.
          destruct op; set_solver.
        - assert (trans = [Cm (tag, c) b]) as ->; first set_solver.
          simpl in Hop_last.
          rewrite /is_cm_op in Hop_cm.
          set_solver.
      }
      assert (KVS_keys = (domain ∩ KVS_keys) ∪ (KVS_keys ∖ (domain ∩ KVS_keys))) as Heq_keys.
      {
        apply union_difference_L.
        set_solver.
      }
      rewrite {4} Heq_keys.
      rewrite big_sepS_union; last set_solver.
      iFrame.
      iAssert ([∗ map] k↦x ∈ (mc : gmap Key (option val)), ⌜k ∈ KVS_keys⌝ → ∃ (ov : option val), ghost_map_elem γ k (DfracOwn 1%Qp) ov)%I 
        with "[Hkeys_conn]" as "Hkeys_conn".
      {
        iApply (big_sepM_wand with "[$Hkeys_conn]").
        iApply big_sepM_intro.
        iModIntro.
        iIntros (key x Hk_in) "(%sa' & %γ' & #Hsa''_pointer & %Hsa'_extract & Hkey & %Hsa'_cli) Hkey_in".
        iExists x.
        destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
        iDestruct (ghost_map_elem_agree sa γmname _ _ (γ, c) (γ', c) with "[$Hsa_pointer][$Hsa''_pointer]")
          as "%Heq_pair".
        assert (γ = γ') as <-; first set_solver.
        by iApply "Hkey".
      }
      rewrite big_sepM_dom.
      assert (dom mc = domain) as ->; first set_solver.
      assert (domain = (domain ∩ KVS_keys) ∪ (domain ∖ (domain ∩ KVS_keys))) as Heq_keys_dom.
      {
        apply union_difference_L.
        set_solver.
      }
      rewrite {1} Heq_keys_dom.
      rewrite big_sepS_union; last set_solver.
      iDestruct "Hkeys_conn" as "(Hkeys_conn & _)".
      iApply (big_sepS_wand with "[$Hkeys_conn]").
      iApply big_sepS_intro.
      iModIntro.
      iIntros (k' Hk'_in) "Himp".
      iApply "Himp".
      iPureIntro; set_solver.
    - iApply (big_sepS_wand with "[$Hdisj_trace_res]"). 
      iApply big_sepS_intro.
      iModIntro.
      iIntros (sa'' Hsa''_in) "Hres".
      iApply (client_trace_state_resources_neq5 sa sa'' with "[][][][][$]"); try done.
      iPureIntro; set_solver.
  Qed.

  Lemma trace_state_resources_commit_lin2 (clients : gset socket_address) (c : val) (tag : string) (lt : list val) (T1 T2 : list transaction)
  (trans : transaction) (sa : socket_address) (s : gset Key) (γ γmstate γmname : gname) (extract : val → option val) (b : bool)
  (mc : gmap Key (option val)) (mstate : gmap socket_address (local_state * option val)) 
  (mname : gmap socket_address (gname * val)) (m : gmap Key (option val)) :
    ⌜¬(∃ e : val, e ∈ lt ∧ tagOfEvent e = Some tag)⌝ -∗
    ⌜dom mc = s⌝ -∗
    ⌜valid_sequence lt⌝ -∗
    ⌜valid_transactions (T1 ++ trans :: T2) ⌝ -∗
    ⌜mstate !! sa = Some (Active s, Some c)⌝ -∗ 
    ⌜extract c = Some #sa⌝ -∗ 
    ⌜clients = {[sa]} ∪ clients ∖ {[sa]}⌝ -∗
    ⌜∃ op, op ∈ trans ∧ last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false⌝ -∗
    ⌜∃ e, e ∈ lt ++ [(#tag, (c, (#"CmLin", #b)))%V] ∧ connOfEvent e = Some c ∧ is_in_lin_event e⌝ -∗
    ([∗ map] k↦x ∈ mc, ∃ (sa0 : socket_address) (γ0 : gname), ghost_map_elem γmname sa0 DfracDiscarded (γ0, c) ∗ 
    ⌜extract c = Some #sa0⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ0 k (DfracOwn 1%Qp) x) ∗ ⌜sa0 ∈ clients⌝) -∗
    ghost_map_elem γmname sa DfracDiscarded (γ, c) -∗ 
    ghost_map_auth γmstate 1 (<[sa:=(CanStart, Some c)]> mstate) -∗ 
    ghost_map_auth γmname 1 mname -∗
    ghost_map_auth γ 1 m -∗
    ([∗ set] y ∈ (clients ∖ {[sa]}), client_trace_state_resources lt (T1 ++ trans :: T2) y γmstate γmname extract mstate mname) -∗
    active_trace_resources lt (T1 ++ trans :: T2) (Active s) c γ m -∗
    trace_state_resources (lt ++ [(#tag, (c, (#"CmLin", #b)))%V]) (T1 ++ (trans ++ [Cm (tag, c) b]) :: T2) γmstate γmname clients extract.
  Proof.
    iIntros (Hnot_in Hdom_eq Hvalid_seq Hvalid_trans Hlookup Hextract Heq_sa_clients Hop) 
      "#Hinit_in Hkeys_conn #Hsa_pointer Hmap_mstate Hmap_mname Hmap_m Hdisj_trace_res Htrace_res".
    iExists (<[sa:=(CanStart, Some c)]> mstate). 
    iFrame.
    iExists mname.
    iFrame.
    rewrite {3} Heq_sa_clients.
    rewrite (big_sepS_union _ {[sa]} (clients ∖ {[sa]})); last set_solver.
    iSplitR "Hdisj_trace_res".
    - rewrite big_sepS_singleton.
      iRight.
      iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & 
      %Heq_act & -> & %Hopen_start & Hkeys & %Hlatest_keys)". 
      iExists CanStart, c, γ, m.
      rewrite lookup_insert.
      do 2 (iSplit; first by iPureIntro).
      iFrame "∗#".
      iLeft.
      iSplit; first done.
      iSplit.
      {
        iPureIntro.
        eapply commit_closed_valid_seq;
          rewrite /is_cm_lin_event; set_solver. 
      }
      iSplit.
      {
        iPureIntro.
        intros (t & op' & Hop'_in & Hop'_last & Hop'_conn & Hop'_cm).
        rewrite elem_of_app in Hop'_in.
        destruct Hop'_in as [Hop'_in | Hop'_in].
        - exfalso.
          eapply (two_trans_implies_false_app_cons T1 T2 trans); try done.
          exists t.
          split; first set_solver.
          exists op'.
          split_and!; try done.
          + by apply last_Some_elem_of.
          + rewrite /isCmOp. 
            rewrite /is_cm_op in Hop'_cm.
            destruct op'; set_solver.
        - rewrite elem_of_cons in Hop'_in.
          destruct Hop'_in as [-> | Hop'_in].
          + rewrite last_snoc in Hop'_last.
            rewrite /is_cm_op in Hop'_cm.
            set_solver.
          + exfalso.
            eapply (two_trans_implies_false_app_cons T1 T2 trans); try done.
            exists t.
            split; first set_solver.
            exists op'.
            split_and!; try done.
            * by apply last_Some_elem_of.
            * rewrite /isCmOp. 
              rewrite /is_cm_op in Hop'_cm.
              destruct op'; set_solver.
      }
      assert (KVS_keys = (domain ∩ KVS_keys) ∪ (KVS_keys ∖ (domain ∩ KVS_keys))) as Heq_keys.
      {
        apply union_difference_L.
        set_solver.
      }
      rewrite {4} Heq_keys.
      rewrite big_sepS_union; last set_solver.
      iFrame.
      iAssert ([∗ map] k↦x ∈ mc, ⌜k ∈ KVS_keys⌝ → ∃ (ov : option val), ghost_map_elem γ k (DfracOwn 1%Qp) ov)%I 
        with "[Hkeys_conn]" as "Hkeys_conn".
      {
        iApply (big_sepM_wand with "[$Hkeys_conn]").
        iApply big_sepM_intro.
        iModIntro.
        iIntros (key x Hk_in) "(%sa' & %γ' & #Hsa''_pointer & %Hsa'_extract & Hkey & %Hsa'_cli) Hkey_in".
        iExists x.
        destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
        iDestruct (ghost_map_elem_agree sa γmname _ _ (γ, c) (γ', c) with "[$Hsa_pointer][$Hsa''_pointer]")
          as "%Heq_pair".
        assert (γ = γ') as <-; first set_solver.
        by iApply "Hkey".
      }
      rewrite big_sepM_dom.
      assert (dom mc = domain) as ->; first set_solver.
      assert (domain = (domain ∩ KVS_keys) ∪ (domain ∖ (domain ∩ KVS_keys))) as Heq_keys_dom.
      {
        apply union_difference_L.
        set_solver.
      }
      rewrite {1} Heq_keys_dom.
      rewrite big_sepS_union; last set_solver.
      iDestruct "Hkeys_conn" as "(Hkeys_conn & _)".
      iApply (big_sepS_wand with "[$Hkeys_conn]").
      iApply big_sepS_intro.
      iModIntro.
      iIntros (k' Hk'_in) "Himp".
      iApply "Himp".
      iPureIntro; set_solver.
    - iApply (big_sepS_wand with "[$Hdisj_trace_res]"). 
      iApply big_sepS_intro.
      iModIntro.
      iIntros (sa'' Hsa''_in) "Hres".
      iApply (client_trace_state_resources_neq6 sa sa'' with "[][][][][][$]"); try done.
      iPureIntro; set_solver.
  Qed.

End trace_proof_util.