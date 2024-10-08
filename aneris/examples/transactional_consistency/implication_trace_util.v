From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params aux_defs state_based_model.

Section trace_proof_util.
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

  Definition no_emit_with_address (sa : socket_address) (ltrace : list val) (extract : val → option val)  : Prop := 
    ¬∃ e c, e ∈ ltrace ∧ connOfEvent e = Some c ∧ extract c = Some #sa.

  Definition active_trace_resources lt T s c γ (m : gmap Key (option val)) : iProp Σ :=
    ∃ domain sub_domain tail, ⌜s = Active domain⌝ ∗ 
      ⌜sub_domain = domain ∩ KVS_keys⌝ ∗ ⌜open_start c lt tail⌝ ∗ 
      ([∗ set] k ∈ KVS_keys ∖ sub_domain, ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ 
      (∀ k, ⌜k ∈ sub_domain⌝ → ∀ ov, ⌜m !! k = Some ov⌝ → ⌜latest_write c k ov T⌝).

  Definition inactive_trace_resources lt T s c γ : iProp Σ :=
    ⌜s = CanStart⌝ ∗ ⌜commit_closed c lt⌝ ∗ ⌜¬∃ t, open_trans t c T⌝ ∗
    ([∗ set] k ∈ KVS_keys, ∃ ov, ghost_map_elem γ k (DfracOwn 1%Qp) ov).

  Definition initialized_trace_resources lt T sa γmname (extract : val → option val)
  (mstate : gmap socket_address (local_state * option val)) : iProp Σ :=
    ∃ s c γ (m : gmap Key (option val)), ⌜mstate !! sa = Some (s, Some c)⌝ ∗
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

  Definition GlobalInvExt (extract : val → option val) (γmstate γmlin γmpost γmname γl : gname) (clients : gset socket_address) : iProp Σ := 
    ∃ t lt T, trace_is t ∗ OwnLinTrace γl lt ∗ ⌜lin_trace_of lt t⌝ ∗ ⌜∀ t, t ∈ T → t ≠ []⌝ ∗
      ⌜extraction_of lt T⌝ ∗ ⌜valid_transactions T⌝ ∗ ⌜valid_sequence lt⌝ ∗
      trace_state_resources lt T γmstate γmname clients extract ∗
      trace_lin_resources lt t γmlin ∗
      trace_post_resources t γmpost.

End trace_proof_util.