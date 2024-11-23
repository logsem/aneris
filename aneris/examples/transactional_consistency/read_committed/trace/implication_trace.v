From iris.algebra Require Import gset auth frac_auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode adequacy_no_model.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency Require Import code_api wrapped_library.
From aneris.examples.transactional_consistency.read_committed.specs Require Import specs resources.
From aneris.examples.transactional_consistency 
  Require Import resource_algebras user_params aux_defs state_based_model implication_trace_util.

Section trace_proof.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params}.

  (** Definitons and lemmas for the wrapped resources *)

  Definition OwnTransSub (γ : gname) (trans : transaction) : iProp Σ :=
    ∃ (T : list transaction), own γ (◯ (gmap_of_trace 0 T)) ∗ ⌜trans ∈ T⌝.

  Definition OwnTrans (γ : gname) (T : list transaction) : iProp Σ :=
    own γ (● gmap_of_trace 0 T) ∗ own γ (◯ (gmap_of_trace 0 T)).

  Lemma own_trans (γ : gname) (T : list transaction) (trans : transaction) :
    OwnTrans γ T ==∗ OwnTrans γ (T ++ [trans]) ∗ OwnTransSub γ trans.
  Proof.
    rewrite /OwnTrans /OwnTransSub.
    iIntros "(H1 & #H2)".
    rewrite gmap_of_trace_snoc Nat.add_0_l.
    iMod (own_update_2 with "H1 H2") as "[H1 H3]".
    apply auth_update.
    eapply (alloc_local_update (gmap_of_trace 0 T) (gmap_of_trace 0 T) 
      (length T : nat) (to_agree (trans : transaction))); try done.
    { 
      eapply not_elem_of_dom.
      rewrite gmap_of_trace_dom.
      intro Hfalse. 
      lia. 
    }
    iDestruct "H3" as "#H4".
    iModIntro.
    iFrame "∗#".
    iExists (T ++ [trans]).
    rewrite gmap_of_trace_snoc Nat.add_0_l.
    iFrame "#".
    iPureIntro.
    set_solver.
  Qed.

  Lemma own_trans_in (γ : gname) (T : list transaction) (trans : transaction):
    OwnTrans γ T ∗ OwnTransSub γ trans -∗
    OwnTrans γ T ∗ OwnTransSub γ trans ∗ ⌜trans ∈ T⌝.
  Proof.
    rewrite /OwnTrans /OwnTransSub.
    iIntros "((H1 & #H2) & (%T' & #H3 & %Hin))".
    iDestruct (own_op with "[$H1 $H3]") as "H".
    iDestruct (own_valid with "H") as %[Hsub Hvalid]%auth_both_valid_discrete.
    iDestruct "H" as "(H1 & _)".
    iFrame "#∗".
    iSplit; first set_solver.
    iPureIntro.
    assert (T' `prefix_of` T) as Hprefix.
    - eapply gmap_of_trace_hist_valid_prefix; eauto.
    - by eapply elem_of_prefix.
  Qed.

  Definition GlobalInvExtRC (γ : gname) (T : list transaction) : iProp Σ := 
    ∃ T', ⌜∀ t, t ∈ T' ↔ t ∈ (comTrans T)⌝ ∗ OwnTrans γ T' ∗ 
      ⌜∀ trans s k v, trans ∈ T → (Rd s k (Some v)) ∈ trans → 
        ¬ (∃ s' v', rel_list trans (Wr s' k v') (Rd s k (Some v))) →
         ∃ trans', trans' ∈ (comTrans T) ∧ latest_write_trans k v trans'⌝.

  (** Wrapped resources  *)
  Global Program Instance wrapped_resources (γtrans γmstate γmlin γmpost γmname γl : gname) (clients : gset socket_address) 
  `(res : !RC_resources Mdl Σ) : RC_resources Mdl Σ :=
    {|
      GlobalInv := (GlobalInv ∗ trace_inv trace_inv_name valid_trace_rc ∗ 
                    inv KVS_InvName (∃ T exec, GlobalInvExtRC γtrans T ∗ GlobalInvExt commit_test_rc T extract γmstate γmlin γmpost γmname γl clients exec))%I;
      OwnMemKey k V :=  (OwnMemKey k V ∗ 
                        (∀ v, ⌜v ∈ V⌝ → ∃ trans, OwnTransSub γtrans trans ∗ ⌜latest_write_trans k v trans⌝ ∗ ⌜com_true trans⌝) ∗
                        (∀ v, ⌜v ∈ V⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
                          ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      OwnLocalKey k c ov := (OwnLocalKey k c ov ∗ ∃ (sa : socket_address) (γ : gname), ghost_map_elem γmname sa DfracDiscarded (γ, c) ∗ 
                             ⌜extract c = Some #sa⌝ ∗ (⌜k ∈ KVS_keys⌝ → ghost_map_elem γ k (DfracOwn 1%Qp) ov) ∗ ⌜sa ∈ clients⌝ ∗ 
                             ⌜∀ v, ov = Some v → k ∈ KVS_keys⌝ ∗
                             (∀ v, ⌜ov = Some v⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I;
      ConnectionState c sa s := (ConnectionState c sa s ∗ ghost_map_elem γmstate sa (DfracOwn 1%Qp) (s, Some c))%I;
      IsConnected c sa := (IsConnected c sa ∗ ⌜sa ∈ clients⌝ ∗ ⌜extract c = Some #sa⌝ ∗ 
                           ∃ (γ : gname), ghost_map_elem γmname sa DfracDiscarded (γ, c))%I;
      KVS_rc := KVS_rc;
      KVS_Init := KVS_Init%I;
      KVS_ClientCanConnect sa := (KVS_ClientCanConnect sa ∗ ghost_map_elem γmstate sa (DfracOwn 1%Qp) (CanStart, None) ∗ ⌜sa ∈ clients⌝)%I;
      Seen k V := Seen k V%I;
      extract c := res.(read_committed.specs.resources.extract) c;
    |}.
  Next Obligation.
    iIntros (???????????) "(Hkey & [%sa [%γ (Hghost_elem_per & %Hextract & Hghost_elem  & %Hin_sa & Hlin_hist)]])".
    iDestruct (res.(read_committed.specs.resources.OwnLocalKey_serializable) 
      with "Hkey") as "(Hkey & Hser)".
    iFrame.
    iExists sa, γ.
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (?????????????) "#(HGinv & Hinv) (#Hseen & Hkey & Hin)".
    iMod (res.(read_committed.specs.resources.Seen_valid) 
      with "[$HGinv][$Hseen $Hkey]") as "(Hkey & Hsub)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    iIntros (????????????) "#(HGinv & Hinv) (Hkey & Hin)".
    iMod (res.(read_committed.specs.resources.Seen_creation) 
      with "[$HGinv][$Hkey]") as "(Hkey & #Hseen)"; first done.
    iModIntro.
    iFrame "∗#".
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????? clients res sa c) "(Hconn & _)".
    iApply (res.(read_committed.specs.resources.Extraction_of_address) 
      with "[$Hconn]").
  Qed.
  Next Obligation.
    simpl.
    iIntros (?????? clients res sa sa' c c' Heq1 Heq2 Hneq).
    by eapply res.(read_committed.specs.resources.Extraction_preservation).
  Qed.

  (** Helper lemmas *)

  Lemma valid_execution_rc_imp exec s st trans T :
    optional_applied_transaction exec st (trans ++ [Cm s true]) →
    based_on exec T →
    (trans ++ [Cm s true]) ∉ T →
    (∀ s k v, Rd s k (Some v) ∈ trans → 
      ¬ (∃ s' v', rel_list trans (Wr s' k v') (Rd s k (Some v))) → 
      ∃ trans', trans' ∈ T ∧ latest_write_trans k v trans') →
    valid_execution commit_test_rc exec →
    valid_execution commit_test_rc (exec ++ [((trans ++ [Cm s true]), st)]).
  Proof.
    intros Happl Hbased Hnin Hreads Hvalid.
    split_and!.
    - destruct Happl as [(s' & t' & Hlast & Happl)|Hfalse].
      + intros i eq e2. 
        eapply extend_execution_imp; try done.
      + rewrite /valid_execution in Hvalid.
        rewrite last_None in Hfalse.
        set_solver.
    - destruct Hvalid as (_ & Hvalid & _).
      rewrite lookup_app_Some.
      set_solver.
    - intros t Hin.
      rewrite split_split in Hin.
      simpl in Hin.
      rewrite elem_of_app in Hin.
      pose proof Hvalid as Hvalid'.
      destruct Hvalid as (_ & _ & Hvalid & _).
      destruct Hin as [Hin|Hin].
      + intros tag c k ov i Hlookup Hrd_in Hnot Hsome.
        specialize (Hvalid t Hin tag c k ov i).
        rewrite split_split in Hlookup.
        simpl in Hlookup.
        rewrite lookup_app_Some in Hlookup.
        destruct Hlookup as [Hlookup| Hlookup].
        * destruct (Hvalid Hlookup Hrd_in Hnot Hsome) as (st' & j & Hleq & Hlookup_j & Hlookup_k).
          exists st', j.
          split_and!; try done.
          rewrite split_split; simpl.
          rewrite lookup_app_Some.
          set_solver.
        * exfalso.
          apply Hnin.
          destruct Hlookup as (_ & Hlookup).
          rewrite list_lookup_singleton_Some in Hlookup.
          destruct Hlookup as (_ & Hlookup).
          rewrite Hlookup.
          apply (Hbased t).
          split; first done.
          rewrite -Hlookup; intros Hfalse. 
          destruct trans; set_solver.
      +  assert (t = trans ++ [Cm s true]) as ->; first set_solver.
         intros tag c k ov i Hlookup Hrd_in Hnot (v & ->).
         assert (Rd (tag, c) k (Some v) ∈ trans) as Hrd_in'; first set_solver.
         destruct (Hreads (tag, c) k v Hrd_in') as (trans' & Hin' & Hlatest).
         {
            intros (s' & v' & Hrel).
            apply Hnot.
            exists s', v'.
            by apply rel_list_imp.
         }
         destruct (latest_write_read exec T k v trans' commit_test_rc) 
          as (st' & Hin_st' & Hlookup_st'); try done.
         rewrite elem_of_list_lookup in Hin_st'.
         destruct Hin_st' as (j & Hlookup_j).
         exists st', j.
         split_and!; try done.
         * rewrite split_split in Hlookup.
           simpl in Hlookup. 
           rewrite lookup_app_Some in Hlookup.
           destruct Hlookup as [Hlookup|Hlookup].
           -- exfalso.
              apply Hnin.
              apply (Hbased (trans ++ [Cm s true])).
              split.
              ++ apply elem_of_list_lookup. 
                 eauto.
              ++ intros Hfalse; destruct trans; set_solver.
           -- apply lookup_lt_Some in Hlookup_j.
              rewrite split_length_r in Hlookup_j.
              rewrite split_length_l in Hlookup.
              lia.
         * rewrite split_split.
           simpl.
           rewrite lookup_app_Some.
           set_solver.
    - intros t1 t2 i j Hlookup_i Hlookup_j Heq.
      rewrite split_split in Hlookup_i; simpl in Hlookup_i.
      rewrite split_split in Hlookup_j; simpl in Hlookup_j.
      rewrite lookup_snoc_Some in Hlookup_i.
      rewrite lookup_snoc_Some in Hlookup_j.
      destruct Hvalid as (_ & _ &  _ & Hvalid).
      destruct Hlookup_i as [Hlookup_i|(Hlength_i & Heq_i)]; 
        destruct Hlookup_j as [Hlookup_j|Hlookup_j].
      1, 4 : set_solver.
      all : subst.
      all : exfalso.
      all : apply Hnin.
      all : apply Hbased.
      all : split; first (apply elem_of_list_lookup; set_solver).
      all : intros Hfalse; destruct trans; set_solver.
  Qed.

  Lemma inv_ext_rc_wr_imp1 γ T1 T2 trans s k v :
    ⌜∃ op, op ∈ trans ∧ last trans = Some op ∧ isCmOp op = false⌝ -∗
    GlobalInvExtRC γ (T1 ++ trans :: T2) -∗
    GlobalInvExtRC γ (T1 ++ (trans ++ [Wr s k v]) :: T2).
  Proof.
    iIntros "%Hop (%T' & Hin_in & Hown & %Himp)".
    rewrite /GlobalInvExtRC.
    rewrite -com_trans_eq1; try done.
    - iExists T'.
      iFrame.
      iPureIntro.
      intros trans' s' k' v' Hin.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hin]; first set_solver.
      rewrite elem_of_cons in Hin.
      destruct Hin as [Hin|Hin]; last set_solver.
      rewrite Hin.
      intros Hrd_in Hnot.
      eapply (Himp trans); first set_solver.
      + rewrite elem_of_app in Hrd_in.
        destruct Hrd_in as [Hrd_in|Hrd_in]; set_solver.
      + intros (s'' & v'' & Hrel).
        apply Hnot.
        exists s'', v''.
        by apply rel_list_imp.
    - rewrite /is_cm_op.
      set_solver.
  Qed.

  Lemma inv_ext_rc_wr_imp2 γ T s k v :
    GlobalInvExtRC γ T -∗
    GlobalInvExtRC γ (T ++ [[Wr s k v]]).
  Proof.
    iIntros "(%T' & Hin_in & Hown & %Himp)".
    rewrite /GlobalInvExtRC.
    rewrite -com_trans_eq2.
    - iExists T'.
      iFrame.
      iPureIntro.
      intros trans s' k' v' Hin.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hin]; first set_solver.
      assert (trans = [Wr s k v]) as ->; set_solver.
    - rewrite /is_cm_op.
      set_solver.
  Qed.

  Lemma inv_ext_rc_rd_imp1 γ s k wo trans T1 T2:
    ⌜∃ op, op ∈ trans ∧ last trans = Some op ∧ isCmOp op = false⌝ -∗
    ⌜∀ v, wo = Some v → ((∃ s, (Wr s k v) ∈ trans) ∨ 
      (∃ trans', trans' ∈ (T1 ++ trans :: T2) ∧ 
        com_true trans' ∧ latest_write_trans k v trans'))⌝ -∗
    GlobalInvExtRC γ (T1 ++ trans :: T2) -∗
    GlobalInvExtRC γ (T1 ++ (trans ++ [Rd s k wo]) :: T2).
  Proof.
    iIntros "%Hop %Hread_res (%T' & Hin_in & Hown & %Himp)".
    rewrite /GlobalInvExtRC.
    rewrite -com_trans_eq1; try done.
    - iExists T'.
      iFrame.
      iPureIntro.
      intros trans' s' k' v' Hin.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hin]; first set_solver.
      rewrite elem_of_cons in Hin.
      destruct Hin as [->|Hin]; last set_solver.
      intros Hrd_in Hnot.
      rewrite elem_of_app in Hrd_in.
      destruct Hrd_in as [Hrd_in|Hrd_in].
      + apply (Himp trans s'); try done; first set_solver.
        intros (s'' & v'' & Hrel).
        apply Hnot.
        exists s'', v''.
        by apply rel_list_imp.
      + assert (k = k') as <-; first set_solver.
        assert (wo = Some v') as ->; first set_solver.
        destruct (Hread_res v') as [(s'' & Hwr_in)|(trans' & Htrans'_in & Htrans'_cm & Hlatest)]; try done.
        * exfalso.
          apply Hnot.
          exists s'', v'.
          assert (s = s') as <-; first set_solver.
          rewrite elem_of_list_lookup in Hwr_in.
          destruct Hwr_in as (i & Hwr_in).
          exists i, (Init.Nat.pred (length (trans ++ [Rd s k (Some v')]))).
          split_and!.
          -- apply lookup_lt_Some in Hwr_in.
             rewrite last_length.
             by simpl.
          -- by apply lookup_app_l_Some.
          -- by rewrite -last_lookup last_snoc.
        * exists trans'.
          split; last done.
          by apply com_trans_in.
    - rewrite /is_cm_op.
      set_solver.
  Qed.

  Lemma inv_ext_rc_rd_imp2 γ T s k wo :
    ⌜∀ v, wo = Some v → ∃ trans, trans ∈ T ∧ com_true trans ∧ 
      latest_write_trans k v trans⌝ -∗
    GlobalInvExtRC γ T -∗
    GlobalInvExtRC γ (T ++ [[Rd s k wo]]).
  Proof.
    iIntros "%Hread_res (%T' & Hin_in & Hown & %Himp)".
    rewrite /GlobalInvExtRC.
    rewrite -com_trans_eq2.
    - iExists T'.
      iFrame.
      iPureIntro.
      intros trans s' k' v' Hin.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hin]; first set_solver.
      assert (trans = [Rd s k wo]) as ->; first set_solver.
      intros Hrd_in Hnot.
      assert (k = k') as <-; first set_solver.
      assert (wo = Some v') as ->; first set_solver.
      destruct (Hread_res v') as (trans & Hin_trans & Hcm & Hlatest); 
        first set_solver.
      exists trans.
      split; last done.
      by apply com_trans_in.
    - rewrite /is_cm_op.
      set_solver.
  Qed.

  Lemma inv_ext_rc_cm_imp1 γ T1 T2 trans s b :
    ⌜∃ op, op ∈ trans ∧ last trans = Some op ∧ isCmOp op = false⌝ ∗
    GlobalInvExtRC γ (T1 ++ trans :: T2) ∗ 
    ⌜∀ s k v, (Rd s k (Some v)) ∈ trans → 
      ¬ (∃ s' v', rel_list trans (Wr s' k v') (Rd s k (Some v))) →
      ∃ trans', trans' ∈ comTrans (T1 ++ trans :: T2) ∧ latest_write_trans k v trans'⌝  ==∗
    GlobalInvExtRC γ (T1 ++ (trans ++ [Cm s b]) :: T2) ∗ 
    (⌜b = true⌝ → OwnTransSub γ (trans ++ [Cm s b])).
  Proof.
    iIntros "(%Hop & (%T' & %Hin_in & Hinv & %Hinv_pure) & %Hreads)".
    destruct b.
    - iDestruct (own_trans γ T' (trans ++ [Cm s true]) with "[$Hinv]") as ">(Hinv & Hsub)".
      iModIntro.
      iSplitR "Hsub"; last (iIntros; iFrame).
      iExists (T' ++ [trans ++ [Cm s true]]).
      iSplit.
      + iPureIntro.
        rewrite com_trans_eq4 in Hin_in; last done.
        intros t.
        split; intros Hin.
        * rewrite elem_of_app in Hin.
          destruct Hin as [Hin|Hin].
          -- apply com_trans_imp1.
             set_solver.
          -- rewrite /comTrans.
             rewrite List.filter_app.
             simpl.
             rewrite last_snoc elem_of_app.
             set_solver.
        * rewrite /comTrans in Hin.
          rewrite List.filter_app in Hin.
          rewrite elem_of_app in Hin.
          destruct Hin as [Hin|Hin].
          -- rewrite elem_of_app; left.
             apply Hin_in.
             rewrite /comTrans List.filter_app; set_solver.
          -- simpl in Hin.
             rewrite last_snoc in Hin.
             rewrite elem_of_cons in Hin.
             destruct Hin as [Hin|Hin]; first set_solver.
             rewrite elem_of_app; left.
             apply Hin_in.
             rewrite /comTrans List.filter_app; set_solver.
      + iSplit; first iFrame.
        iPureIntro.
        rewrite com_trans_eq4 in Hinv_pure; last done.
        intros trans' s' k v Hin Hrd_in Hnot.
        rewrite elem_of_app in Hin.
        destruct Hin as [Hin|Hin].
        * destruct (Hinv_pure trans' s' k v) as (trans'' & Htrans'_in & Hlatest); 
            try done; first set_solver.
          exists trans''.
          split; last done.
          by apply com_trans_imp1.
        * rewrite elem_of_cons in Hin.
          destruct Hin as [Hin|Hin].
          -- subst.
             rewrite com_trans_eq4 in Hreads; last done.
             destruct (Hreads s' k v) as (trans'' & Htrans'_in & Hlatest); first set_solver.
            ++ intros (s'' & v'' & Hrel).
               apply Hnot.
               exists s'', v''.
               by apply rel_list_imp.
            ++ exists trans''.
               split; last done.
               by apply com_trans_imp1.
          -- destruct (Hinv_pure trans' s' k v) as (trans'' & Htrans'_in & Hlatest); 
              try done; first set_solver.
             exists trans''.
             split; last done.
             by apply com_trans_imp1.
    - iModIntro.
      iSplit; last by iIntros (Hfalse).
      iExists T'.
      iSplit.
      + iPureIntro.
        rewrite /comTrans List.filter_app.
        simpl.
        rewrite last_snoc.
        rewrite /comTrans List.filter_app in Hin_in.
        simpl in Hin_in.
        destruct Hop as (op & _ & Hlast & Hcm).
        rewrite Hlast in Hin_in.
        rewrite /isCmOp in Hcm.
        destruct op; simpl; set_solver.
      + iSplit; first iFrame. 
        iPureIntro.
        intros trans' s' k v Hin Hrd_in Hnot.
        rewrite elem_of_app in Hin.
        rewrite -com_trans_eq3; last done.
        destruct Hin as [Hin|Hin]; first set_solver.
        rewrite elem_of_cons in Hin.
        destruct Hin as [Hin|Hin]; last set_solver.
        subst.
        eapply (Hreads s'); first set_solver.
        intros (s'' & v'' & Hrel).
        apply Hnot.
        exists s'', v''.
        by apply rel_list_imp.
  Qed.

  Lemma inv_ext_rc_cm_imp2 γ T s b :
    GlobalInvExtRC γ T ==∗
    GlobalInvExtRC γ (T ++ [[Cm s b]]).
  Proof.
    iIntros "(%T' & %Hin_in & Hinv & %Hinv_pure)".
    destruct b.
    - iDestruct (own_trans γ T' [Cm s true] with "[$Hinv]") as ">(Hinv & _)".
      iModIntro.
      iExists (T' ++ [[Cm s true]]).
      iSplit.
      + iPureIntro.
        rewrite /comTrans List.filter_app.
        rewrite /comTrans in Hin_in.
        set_solver.
      + iSplit; first iFrame.
        iPureIntro.
        intros trans s' k v Hin Hrd_in Hnot.
        rewrite elem_of_app in Hin.
        destruct Hin as [Hin|Hin].
        * specialize (Hinv_pure trans s' k v Hin Hrd_in Hnot).
            destruct Hinv_pure as (trans' & Htrans'_in & Hlatest).
            exists trans'.
            split; last done.
            rewrite /comTrans List.filter_app.
            rewrite /comTrans in Htrans'_in.
            set_solver.
        * assert (trans = [Cm s true]) as ->; set_solver.
   - iModIntro.
     iExists T'.
     iSplit.
     + iPureIntro. 
       rewrite /comTrans List.filter_app.
       simpl.
       rewrite app_nil_r.
       rewrite /comTrans in Hin_in.
       set_solver.
     + iSplit; first iFrame. 
      iPureIntro.
      intros trans s' k v Hin Hrd_in Hnot.
      rewrite elem_of_app in Hin.
      destruct Hin as [Hin|Hin].
      * specialize (Hinv_pure trans s' k v Hin Hrd_in Hnot).
        destruct Hinv_pure as (trans' & Htrans'_in & Hlatest).
        exists trans'.
        split; last done.
        rewrite /comTrans List.filter_app.
        rewrite /comTrans in Htrans'_in.
        set_solver.
      * assert (trans = [Cm s false]) as ->; set_solver.
  Qed.

  (** Per operation implications *)

  Lemma commit_implication γtrans γmstate γmlin γmpost γmname γl clients (res : RC_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_rc -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtRC γtrans T ∗ GlobalInvExt commit_test_rc T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @commit_spec _ _ _ _ lib res -∗
    @commit_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γtrans γmstate γmlin γmpost γmname γl clients res).
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
    iInv "HinvExt" as ">[%T [%exec (Htrans_res & [%t [%lt 
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq &
      %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
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
    iMod ("Hclose" with "[Htrans_res Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, (c, #"CmPre"))%V]), lt.
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
        ∃ lh (tag : string) c, OwnLinHist γl lh ∗ ⌜(#tag, (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝)) ∗
        ([∗ map] k↦V ∈ m, (∀ v, ⌜v ∈ V⌝ → ∃ trans, OwnTransSub γtrans trans ∗ ⌜latest_write_trans k v trans⌝ ∗ ⌜com_true trans⌝)))%I 
        with "[Hkeys]" as "(Hkeys1 & Hkeys3 & Hkeys2)".
    {
      do 2 rewrite big_sepM_sep.
      iDestruct "Hkeys" as "(Hkeys1 & Hkeys3 & Hkeys2)".
      iFrame.
    }
    iSplitL "Hkeys_conn1 Hkeys1 Hstate".
    {
      iFrame.
      iSplit; by iPureIntro.
    }
    iModIntro.
    iIntros (b) "(Hstate & Hkeys1_disj)".
    iInv "HinvExt" as ">[%T' [%exec' (Htrans_res' &  [%t' [%lt' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hbased' & %Hvalid_exec' & %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
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
    iAssert ([∗ map] k↦ov ∈ mc, (∀ v, ⌜ov = Some v⌝ → ∃ lh tag c, OwnLinHist γl lh ∗ 
      ⌜(#(LitString tag), (c, (#"WrLin", (#(LitString k), v))))%V ∈ lh⌝))%I 
      with "[Hkeys_conn2]" as "#Hkeys_conn_lin_hist".
    {
      iApply (big_sepM_wand with "[$Hkeys_conn2]").
      iApply big_sepM_intro.
      iModIntro.
      iIntros (k ov Hlookup) "(%sa' & %γ' & _ & _ & _ & _ & _ & Hlin_hist)".
      iFrame.
    }
    iAssert ([∗ map] k↦ov ∈ mc, ⌜∀ v : val, ov = Some v → 
      ∃ trans, (open_trans trans c T') ∧ latest_write_trans k v trans⌝)%I as "#Hcm_sep_in".
    {
      iAssert ((∀ v k, ⌜mc !! k = Some (Some v)⌝ → ⌜latest_write c k (Some v) T'⌝)%I) as "%Hsome_latest".
      {
        iIntros (v k Hlookup).
        iAssert (ghost_map_elem γ k (DfracOwn 1%Qp) (Some v) ∗ ⌜k ∈ KVS_keys⌝)%I 
          with "[Hkeys_conn2]" as "(Hkey_internal & %Hk_in_KVS)".
        {
          rewrite -(insert_delete mc k (Some v)).
          2 : done.
          rewrite insert_union_singleton_l.
          rewrite big_sepM_union.
          2 : {
            apply map_disjoint_spec.
            intros i ov1 ov2 Hlookup1 Hlookup2.
            rewrite lookup_singleton_Some in Hlookup1.
            destruct Hlookup1 as (Heq & _).
            rewrite Heq in Hlookup2.
            by rewrite lookup_delete in Hlookup2.
          }
          rewrite big_sepM_singleton.
          iDestruct "Hkeys_conn2" as "((%sa' & %γ' & #Hsa'_pointer' & %Hextract_sa' & Hkey & %Hsa'_in & %Himp & _) & _)".
          iAssert (⌜k ∈ KVS_keys⌝)%I as "#Hk_in"; first (iPureIntro; set_solver).
          iFrame "#".
          destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
          iAssert (⌜γ = γ'⌝%I) as "<-"; last by iApply "Hkey".
          iAssert ((⌜(γ', c) = (γ, c)⌝)%I) as "%Heq_pair"; last (iPureIntro; set_solver).
          iApply (ghost_map_elem_agree sa γmname _ _ (γ', c) (γ, c) with "[$Hsa'_pointer'][$Hsa'_pointer]").
        }
        iDestruct (@ghost_map_lookup with "[$Hmap_m][$Hkey_internal]") as "%Hlookup_m".
        iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & Hactive_eq & -> & %Hopen_tail &
            Hkeys & Hkey_info)".
        destruct (decide (k ∈ domain ∩ KVS_keys)) as [Hk_in_dom|Hk_nin_dom].
        - iAssert (⌜latest_write c k (Some v) T'⌝%I) as "%Hlatest_write"; 
            first iApply "Hkey_info"; try done.
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
      iApply big_sepM_intro.
      iModIntro.
      iPureIntro.
      iIntros (k ov Hlookup v Heq).
      destruct (Hsome_latest v k) as [Hfalse|(v' & trans' & tag' & Heq_some & Hopen & Hwr_in & Hop)]. 
      1, 2 : set_solver.
      exists trans'.
      split; first done.
      exists (tag', c).
      assert (v = v') as <-; first set_solver.
      split; first set_solver.
      intros (sig' & v' & (i & j & Hlt & Hlookup_i & Hlookup_j)).
      assert (Wr sig' k v' ∈ trans') as Hwr_in'.
      {
        apply elem_of_list_lookup.
        set_solver.
      }
      destruct Hopen as (_ & Htrans'_in & _).
      destruct Hvalid_trans' as (Hvalid_trans' & _).
      destruct (Hvalid_trans' trans' Htrans'_in) as (_ & _ & Hvalid_eq & _).
      assert (rel_list trans' (Wr sig' k v') (Wr (tag', c) k v)) as (i' & j' & Hlt' & Hlookup_i' & Hlookup_j').
      {
        eapply (Hop (Wr sig' k v') Hwr_in').
        exists sig', v'.
        split; first done.
        intros Hfalse.
        rewrite Hfalse in Hlookup_j.
        assert (i = j) as Heq_i_j; last lia.
        eapply Hvalid_eq; set_solver.
      }
      assert (i = j') as Heq_i_j'; first (eapply Hvalid_eq; set_solver).
      assert (i' = j) as Heq_i'_j; first (eapply Hvalid_eq; set_solver).
      lia.
    } 
    assert (Decision (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
      op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
      as Hdecision.
    {
      do 2 (apply list_exist_dec; intros).
      apply _.
    }
    assert (∀ k : Key, is_Some (m !! k) ↔ is_Some (mc !! k)) as His_some.
    {
      intros k; split; intros His_some.
      all : rewrite -elem_of_dom.
      all : rewrite -elem_of_dom in His_some.
      all : set_solver.
    }
    destruct (decide (∃ (trans : transaction), trans ∈ T' ∧ (λ trans, ∃ (op : operation), 
      op ∈ trans ∧ (λ op, last trans = Some op ∧ connOfOp op = c ∧ isCmOp op = false) op) trans)) 
        as [(trans & Htrans_in & Hop)|Hdec].
    - destruct (elem_of_list_split _ _ Htrans_in) as (T1 & T2 & ->).
      iAssert (⌜∀ s0 k v, Rd s0 k (Some v) ∈ trans → 
        ¬ (∃ s' v', rel_list trans (Wr s' k v') (Rd s0 k (Some v))) →
        ∃ trans', trans' ∈ comTrans (T1 ++ trans :: T2) ∧ latest_write_trans k v trans'⌝)%I as "%Htrans_reads".
      {
        iDestruct "Htrans_res'" as "(%Tinv & _ & _ & %Hinv_pure)".
        iPureIntro; set_solver.
      }
      iMod (inv_ext_rc_cm_imp1 _ _ _ _ (tag1, c) b with "[$Htrans_res']") as "(Htrans_res' & #Hsub)".
      {
        iSplit; last done.
        iPureIntro; set_solver.
      }
      iAssert 
        (⌜b = true⌝ ∗
          ([∗ map] k↦V;vo ∈ m;mc, k ↦ₖ commit_event vo V ∗
            (∀ v, ⌜v ∈ commit_event vo V⌝ → ∃ trans, OwnTransSub γtrans trans ∗ ⌜latest_write_trans k v trans⌝ ∗ ⌜com_true trans⌝) ∗
            (∀ v, ⌜v ∈ commit_event vo V⌝ → ∃ lh (tag : string) c0, OwnLinHist γl lh ∗ ⌜(#tag, (c0, (#"WrLin", (#k, v))))%V ∈ lh⌝)) ∨ 
        ⌜b = false⌝ ∗
          ([∗ map] k↦V ∈ m, k ↦ₖ V ∗
            (∀ v, ⌜v ∈ V⌝ → ∃ trans, OwnTransSub γtrans trans ∗ ⌜latest_write_trans k v trans⌝ ∗ ⌜com_true trans⌝) ∗
            (∀ v, ⌜v ∈ V⌝ → ∃ lh (tag : string) c0, OwnLinHist γl lh ∗ ⌜(#tag, (c0, (#"WrLin", (#k, v))))%V ∈ lh⌝)))%I
        with "[Hkeys1_disj Hkeys2 Hkeys3]" as "Hkeys_disj".
      {
        iDestruct "Hkeys1_disj" as "[(-> & Hkeys1)|(-> & Hkeys1)]".
        - iLeft.
          iSplit; first done.
          do 2 rewrite big_sepM2_sep.
          iFrame.
          iDestruct (big_sepM2_sepM_2 with "[$Hkeys2][$Hcm_sep_in]") as "Hkeys2"; first done.
          iDestruct (big_sepM2_sepM_2 with "[$Hkeys3][$Hkeys_conn_lin_hist]") as "Hkeys3"; first done.
          iSplitL "Hkeys2".
          + iApply (big_sepM2_wand with "[$Hkeys2]").
            iApply big_sepM2_intro; first done.
            iModIntro.
            iIntros (k V ov Hlookup1 Hlookup2) "(Hexists_sub & %Hopen_latest) %v %Hin".
            rewrite /commit_event in Hin.
            destruct ov as [v'|].
            * rewrite elem_of_union in Hin.
              destruct Hin as [Hin|Hin]. 
              -- iDestruct ("Hexists_sub" $! v Hin) as "(%trans' & Htrans'_sub)".
                 iExists trans'.
                 iFrame.
              -- assert (v = v') as <-; first set_solver.
                 iExists (trans ++ [Cm (tag1, c) true]).
                 destruct (Hopen_latest v) as (trans' & Htrans'_open & Htrans'_latest); first done.
                 assert (trans = trans') as ->; first by eapply trans_eq.
                 iSplitR; first by iApply "Hsub".
                 iPureIntro.
                 rewrite /com_true last_snoc.
                 split; last set_solver.
                 destruct Htrans'_latest as (sig & Hwr_in & Hnot).
                 exists sig.
                 split; first set_solver.
                 intros (sig' & v' & Hrel).
                 apply Hnot.
                 exists sig', v'.
                 eapply (rel_list_last_neq _ _ _ (Cm (tag1, c) true)); set_solver.
            * iDestruct ("Hexists_sub" $! v Hin) as "(%trans' & Htrans'_sub)".
              iExists trans'.
              iFrame.
          + iApply (big_sepM2_wand with "[$Hkeys3]").
            iApply big_sepM2_intro; first done.
            iModIntro.
            iIntros (k V ov Hlookup1 Hlookup2) "(Hlin_hist & Hlin_hist_val) %v %Hin".
            destruct ov as [v'|].
            * rewrite elem_of_union in Hin.
              destruct Hin as [Hin|Hin].
              -- iDestruct ("Hlin_hist" $! v Hin) as "(%lh' & %tag' & %c' & Hown_lin')".
                 iExists lh', tag', c'.
                 iFrame.
              -- iApply "Hlin_hist_val".
                 iPureIntro; set_solver.
            * iDestruct ("Hlin_hist" $! v Hin) as "(%lh' & %tag' & %c' & Hown_lin')".
              iExists lh', tag', c'.
              iFrame.
        - iRight.
          iSplit; first done.
          do 2 (rewrite big_sepM_sep; iFrame).
      }
      iMod ("Hclose'" with "[Htrans_res' Htr_is' HOwnLin' Hpost_res' Hlin_res' Htrace_res Hkeys_conn2 Hmap_mname
        Hmap_m Hdisj_trace_res Hmap_mstate]").
      {
        iModIntro.
        destruct (optional_applied_transaction_exists exec' (trans ++ [Cm (tag1, c) b])) as (st & Happl).
        iExists (T1 ++ (trans ++ [Cm (tag1, c) b]) :: T2), (optionalExtendExecution exec' (trans ++ [Cm (tag1, c) b]) st); iFrame.
        iExists t', (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V]).
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
                  apply (valid_transactions_add2 _ _ tag1 _ _ c); try done.
                  ** by eapply extraction_of_not_in.
                  ** by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
                  ** destruct Hop as (op & Hop_in & Hop_last & Hop_conn & Hop_cm).
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
                    --- iPureIntro; apply based_on_add4; set_solver.
                    --- iSplit.
                        +++ iPureIntro.
                            rewrite /optionalExtendExecution last_snoc.
                            destruct b; last done.
                            eapply valid_execution_rc_imp; try done.
                            intros Hfalse.
                            apply Hnot_lin_in.
                            exists (toLinEvent (Cm (tag1, c) true)).
                            simpl.
                            destruct Hex' as (_ & Hex' & _).
                            split; last done.
                            apply (Hex' (trans ++ [Cm (tag1, c) true]) (Cm (tag1, c) true)); last set_solver.
                            by apply com_trans_imp2.
                        +++ iApply (trace_state_resources_commit_lin2 clients c tag1 lt' T1 T2 trans sa 
                              s γ γmstate γmname extract b mc mstate mname m' with 
                              "[//][//][//][//][//][//][//][//][][Hkeys_conn2][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                              [$Hmap_m][$Hdisj_trace_res][$Htrace_res]").
                            *** iPureIntro.
                                destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                                exists e.
                                split_and!; try done.
                                apply elem_of_app; eauto.
                            *** iApply (big_sepM_wand with "[$Hkeys_conn2]").
                                iApply big_sepM_intro.
                                iModIntro.
                                iIntros (k ov Hlookup) "(%sa' & %γ' & Hptr' & Hextract' & Himp' & Hclients_in' & _)".
                                iExists sa', γ'.
                                iFrame.
      }
      iMod ("Hshift" with "[Hkeys_disj Hstate_pr Hstate]"); first iFrame.
      iModIntro.
      rewrite /commit_post_emit_event.
      wp_pures.
      wp_bind (Emit _).
      iInv "HinvExt" as ">[%T'' [%exec'' (Htrans_res'' &  [%t'' [%lt'' 
        (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
        %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
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
      iMod ("Hclose''" with "[Htrans_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
      {
        iModIntro.
        iExists T'', exec''.
        iFrame.
        iExists (t'' ++ [(#tag1, (c, (#"CmPost", #b)))%V]), lt''.
        iFrame.
        iSplitR; last set_solver.
        iPureIntro.
        apply (lin_trace_valid tag1); try done.
        rewrite /is_post_event /is_cm_post_event.
        set_solver.
      }
      iModIntro.
      by wp_pures.
    - iAssert 
      (⌜b = true⌝ ∗
        ([∗ map] k↦V;vo ∈ m;mc, k ↦ₖ commit_event vo V ∗
          (∀ v, ⌜v ∈ commit_event vo V⌝ → ∃ trans, OwnTransSub γtrans trans ∗ ⌜latest_write_trans k v trans⌝ ∗ ⌜com_true trans⌝) ∗
          (∀ v, ⌜v ∈ commit_event vo V⌝ → ∃ lh (tag : string) c0, OwnLinHist γl lh ∗ ⌜(#tag, (c0, (#"WrLin", (#k, v))))%V ∈ lh⌝)) ∨ 
       ⌜b = false⌝ ∗
        ([∗ map] k↦V ∈ m, k ↦ₖ V ∗
          (∀ v, ⌜v ∈ V⌝ → ∃ trans, OwnTransSub γtrans trans ∗ ⌜latest_write_trans k v trans⌝ ∗ ⌜com_true trans⌝) ∗
          (∀ v, ⌜v ∈ V⌝ → ∃ lh (tag : string) c0, OwnLinHist γl lh ∗ ⌜(#tag, (c0, (#"WrLin", (#k, v))))%V ∈ lh⌝)))%I
      with "[Hkeys1_disj Hkeys2 Hkeys3]" as "Hkeys_disj".
      {
        iDestruct "Hkeys1_disj" as "[(-> & Hkeys1)|(-> & Hkeys1)]".
        - iLeft.
          iSplit; first done.
          do 2 rewrite big_sepM2_sep.
          iFrame.
          iAssert ([∗ map] k↦ov ∈ mc, ⌜∀ v, ov = Some v → false⌝)%I as "#Hcm_sep_in'".
          {
            iApply (big_sepM_wand with "[$Hcm_sep_in]").
            iApply big_sepM_intro.
            iModIntro.
            iIntros (k ov Hlookup Himp).
            iPureIntro.
            intros v Heq.
            apply Hdec.
            destruct (Himp v Heq) as (trans & Hopen & _).
            exists trans.
            rewrite /open_trans /is_cm_op in Hopen.
            rewrite /isCmOp.
            destruct Hopen as (op & Htrans_in & Hlast & Hconn & Hcm).
            split; first done. 
            exists op.
            split_and!; try done; last (destruct op; set_solver).
            by apply last_Some_elem_of.
          }
          iDestruct (big_sepM2_sepM_2 with "[$Hkeys2][$Hcm_sep_in']") as "Hkeys2"; first done.
          iDestruct (big_sepM2_sepM_2 with "[$Hkeys3][$Hcm_sep_in']") as "Hkeys3"; first done.
          iSplitL "Hkeys2".
          + iApply (big_sepM2_wand with "[$Hkeys2]").
            iApply big_sepM2_intro; first done.
            iModIntro.
            iIntros (k V ov Hlookup1 Hlookup2) "(Hsub & %Hfalse)".
            destruct ov; set_solver.
          + iApply (big_sepM2_wand with "[$Hkeys3]").
            iApply big_sepM2_intro; first done.
            iModIntro.
            iIntros (k V ov Hlookup1 Hlookup2) "(Hwr & %Hfalse)".
            destruct ov; set_solver.
        - iRight.
          iSplit; first done.
          do 2 (rewrite big_sepM_sep; iFrame).
      }
      iMod (inv_ext_rc_cm_imp2 with "[$Htrans_res']") as "Htrans_res'".
      iMod ("Hclose'" with "[Htrans_res' Htr_is' HOwnLin' Hpost_res' Hlin_res' Htrace_res Hkeys_conn2 Hmap_mname
        Hmap_m Hdisj_trace_res Hmap_mstate]").
      {
        iModIntro.
        destruct (optional_applied_transaction_exists exec' [Cm (tag1, c) b]) as (st & Happl).
        iExists (T' ++ [[Cm (tag1, c) b]]), (optionalExtendExecution exec' [Cm (tag1, c) b] st).
        iFrame.
        iExists t', (lt' ++ [(#tag1, (c, (#"CmLin", #b)))%V]).
        iFrame.
        iSplit.
        - iPureIntro.
          apply (lin_trace_lin lt' (#tag1, (c, #"CmPre"))%V 
            (#tag1, (c, (#"CmLin", #b)))%V tag1 c t'); try done;
            rewrite /is_lin_event /is_cm_lin_event /is_pre_event /is_cm_pre_event;
            set_solver. 
        - iSplit.
          + iPureIntro.
            intros t'' Ht''_in.
            rewrite elem_of_app in Ht''_in.
            destruct Ht''_in as [Ht''_in | Ht''_in]; set_solver.
          + iSplit.
            * iPureIntro.
              by apply extraction_of_add1.
            * iSplit.
              -- iPureIntro.
                  apply (valid_transactions_add1 T' (Cm (tag1, c) b) c); try done.
                  ++ by eapply extraction_of_not_in.
                  ++ apply valid_transaction_singleton.
                  ++ intros (t'' & Ht''_in & (op & Hop_in & Hop_last & Hop_conn & Hop_cm)).
                     apply Hdec.
                     exists t''.
                     split; first done.
                     exists op.
                     split_and!; try done.
                     rewrite /is_cm_op in Hop_cm.
                     destruct op; try done.
                     exfalso.
                     eauto.
              -- iSplit.
                  ++ iDestruct "Htrace_res" as "(%domain & %sub_domain & %tail & Hact_eq & -> & 
                      %Hopen_start & Hrest)".
                    iPureIntro.
                    apply (valid_sequence_wr_rd_cm_lin _ _ tag1 c tail); try done.
                    ** rewrite /is_cm_lin_event.
                       set_solver.
                    ** by exists t'.
                  ++ iSplit.
                    ** iPureIntro; apply based_on_add3; set_solver.
                    ** iSplit.
                       --- iPureIntro.
                           destruct b; last done.
                           assert ([Cm (tag1, c) true] = [] ++ [Cm (tag1, c) true]) as ->; first set_solver.
                           eapply valid_execution_rc_imp; try done; last set_solver.
                           simpl.
                           intros Hfalse.
                           apply Hnot_lin_in.
                           exists (toLinEvent (Cm (tag1, c) true)).
                           simpl.
                           destruct Hex' as (_ & Hex' & _).
                           split; last done.
                           apply (Hex' [Cm (tag1, c) true] (Cm (tag1, c) true)); last set_solver.
                           by apply com_trans_imp2.
                       --- iApply (trace_state_resources_commit_lin1 clients c tag1 lt' T' sa 
                             s γ γmstate γmname extract b mc mstate mname m' with 
                             "[//][//][//][//][//][//][//][][Hkeys_conn2][$Hsa_pointer][$Hmap_mstate][$Hmap_mname]
                             [$Hmap_m][$Hdisj_trace_res][$Htrace_res]").
                           +++ iPureIntro.
                               destruct Hinit as (e & Hin'' & Hconn'' & Hevent'').
                               exists e.
                               split_and!; try done.
                               apply elem_of_app; eauto.
                           +++ iApply (big_sepM_wand with "[$Hkeys_conn2]").
                               iApply big_sepM_intro.
                               iModIntro.
                               iIntros (k ov Hlookup) "(%sa' & %γ' & Hptr' & Hextract' & Himp' & Hclients_in' & _)".
                               iExists sa', γ'.
                               iFrame.
      }
      iMod ("Hshift" with "[Hkeys_disj Hstate_pr Hstate]"); first iFrame.
      iModIntro.
      rewrite /commit_post_emit_event.
      wp_pures.
      wp_bind (Emit _).
      iInv "HinvExt" as ">[%T'' [%exec'' (Htrans_res'' &  [%t'' [%lt'' 
        (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
        %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
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
      iMod ("Hclose''" with "[Htrans_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
      {
        iModIntro.
        iExists T'', exec''.
        iFrame.
        iExists (t'' ++ [(#tag1, (c, (#"CmPost", #b)))%V]), lt''.
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

  Lemma read_implication γtrans γmstate γmlin γmpost γmname γl clients (res : RC_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_rc -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtRC γtrans T ∗ GlobalInvExt commit_test_rc T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @read_spec _ _ _ _ lib res -∗
    @read_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γtrans γmstate γmlin γmpost γmname γl clients res).
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
    iInv "HinvExt" as ">[%T [%exec (Htrans_res & [%t [%lt 
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq 
       & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
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
    iMod ("Hclose" with "[Htrans_res Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, (c, #"RdPre"))%V]), lt.
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
    iDestruct "Hkey_c" as "(Hkey_c & (%sa' & %γ & #Hsa'_pointer & %Hsa'_extract & Himp & %Hsa'_in & #Hlin_hist))".
    destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
    iDestruct "Hkey" as "(Hkey & #Hkey_trans & Hall)".
    iModIntro.
    iExists vo, V.
    iFrame.
    iNext.
    iIntros (wo) "(Hkey_c & Hkey)".
    iInv "HinvExt" as ">[%T' [%exec' (Htrans_res' & [%t' [%lt' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hbased' & %Hvalid_exec' & %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
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
      rewrite {2} Heq_k_keys.
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
    iAssert (⌜∀ v : val, wo = Some v → (∃ s' trans, open_trans trans c T' ∧ Wr s' k v ∈ trans) ∨ 
      (∃ trans', trans' ∈ T' ∧ com_true trans' ∧ latest_write_trans k v trans')⌝%I) 
      as "%Hread_res_3".
    {
      iDestruct "Htrans_res'" as "(%Tinv & %Hcom_imp & Htrans_res' & %Hread_res)".
      iAssert (∀ v, ⌜v ∈ V⌝ → ∃ trans, ⌜trans ∈ T'⌝ ∗ 
        ⌜latest_write_trans k v trans⌝ ∗⌜com_true trans⌝)%I 
        with "[Htrans_res']" as "%Hkey_trans'".
      {
        iIntros (v Hin_v).
        iDestruct ("Hkey_trans" $! v Hin_v) as "(%trans' & Htrans_sub & #Hrest)".
        iExists trans'.
        iFrame "#".
        iDestruct (own_trans_in with "[$Htrans_res' $Htrans_sub]") as "(_ & _ & %Hin_com)".
        iPureIntro.
        assert (trans' ∈ comTrans T') as Hin_trans'; first set_solver.
        by apply com_trans_imp2.
      }
      iPureIntro.
      intros v ->.
      rewrite /latest_write in Hread_res_2.
      set_solver.
    }
    iMod ("Hclose'" with "[Htrans_res' Htr_is' Hmap_mstate Hmap_mname Hmap_m Htrace_res Hdisj_trace_res 
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
        iExists (T1 ++ (trans ++ [Rd (tag1, c) k wo]) :: T2), exec'.
        iSplitL "Htrans_res'".
        {
          iApply inv_ext_rc_rd_imp1; try done; first (iPureIntro; set_solver).
          iPureIntro.
          intros v Heq.
          specialize (Hread_res_3 v Heq).
          destruct Hread_res_3 as [Hres|Hres]; last by right.
          left.
          destruct Hres as (s' & trans' & Hopen & Hres).
          exists s'.
          assert (trans = trans') as ->; last done.
          by eapply trans_eq.
        }
        iExists t', (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ wo))))%V]).
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
                  apply (valid_transactions_add2 _ _ tag1 _ _ c); try done.
                  ** by eapply extraction_of_not_in.
                  ** by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
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
                         assert (trans = trans') as <-; first by eapply trans_eq.
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
      - iExists (T' ++ [[Rd (tag1, c) k wo]]), exec'.
        iSplitL "Htrans_res'".
        {
          iApply inv_ext_rc_rd_imp2; try done. 
          iPureIntro.
          intros v Heq.
          specialize (Hread_res_3 v Heq).
          destruct Hread_res_3 as [(_ & trans & Hopen & _)|Hres]; last done.
          exfalso. 
          apply Hdec.
          exists trans.
          destruct Hopen as (op & Htrans_in & Hlast & Hconn & Hcm).
          split; first done.
          exists op.
          split_and!; try done.
          + by eapply last_Some_elem_of. 
          + rewrite /is_cm_op in Hcm.
            rewrite /isCmOp.
            destruct op; set_solver.
        }
        iExists t', (lt' ++ [(#tag1, (c, (#"RdLin", (#k, $ wo))))%V]).
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
                  apply (valid_transactions_add1 T' (Rd (tag1, c) k wo) c); try done.
                  ** by eapply extraction_of_not_in.
                  ** set_solver.
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
    iMod ("Hshift" $! wo with "[Hkey_internal Hkey_trans Hall Hkey_c Hkey]").
    {
      simpl.
      iSplitL "Hkey_c Hkey_internal"; iFrame "∗#"; last by iPureIntro.
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
    iInv "HinvExt" as ">[%T'' [%exec'' (Htrans_res'' & [%t'' [%lt'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
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
    iMod ("Hclose''" with "[Htrans_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', exec''.
      iFrame.
      iExists (t'' ++ [_]), lt''.
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

  Lemma write_implication γtrans γmstate γmlin γmpost γmname γl clients (res : RC_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_rc -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtRC γtrans T ∗ GlobalInvExt commit_test_rc T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @write_spec _ _ _ _ lib res -∗
    @write_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γtrans γmstate γmlin γmpost γmname γl clients res).
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
    iInv "HinvExt" as ">[%T [%exec (Htrans_res & [%t [%lt 
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq &
      %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
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
    iMod ("Hclose" with "[Htrans_res Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, (c, #"WrPre"))%V]), lt.
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
    iMod "Hshift" as "(%vo & Hkey_c & Hshift)".
    iDestruct "Hkey_c" as "(Hkey_c & (%sa' & %γ & #Hsa'_pointer & %Hsa'_extract & Himp & %Hsa'_in & #Hlin_hist))".
    destruct (decide (sa = sa')) as [<- | Hfalse]; last set_solver.
    iModIntro.
    iExists vo.
    iFrame.
    iNext.
    iIntros "Hkey_c".
    iInv "HinvExt" as ">[%T' [%exec' (Htrans_res' & [%t' [%lt' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hbased' & %Hvalid_exec' & %Hvalid_seq' & HstateRes' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
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
    rewrite {3} Heq_sa_clients.
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
      rewrite {2} Heq_k_keys.
      rewrite (big_sepS_union _ {[k]} (KVS_keys ∖ {[k]})); last set_solver.
      rewrite big_sepS_singleton.
      iDestruct "Hfalse" as "(_ & (%ov' & Hfalse) & _)".
      iCombine "Hkey_internal" "Hfalse" as "Hfalse".
      iDestruct (ghost_map_elem_valid with "Hfalse") as "%Hfalse".
      by rewrite dfrac_valid_own in Hfalse.
    }
    iMod (@ghost_map_update _ Key (option val) _ _ _ _ _ k vo (Some v.(SV_val)) with "[$Hmap_m] [$Hkey_internal]") 
      as "(Hmap_m & Hkey_internal)".
    iMod ("Hclose'" with "[Htrans_res' Htr_is' Hmap_mstate Hmap_mname Hmap_m Htrace_res Hdisj_trace_res 
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
        iExists (T1 ++ (trans ++ [Wr (tag1, c) k v]) :: T2), exec'.
        iSplitL "Htrans_res'"; first (iApply inv_ext_rc_wr_imp1; set_solver).
        iExists t', (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]).
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
                  apply (valid_transactions_add2 _ _ tag1 _ _ c); try done.
                  ** by eapply extraction_of_not_in.
                  ** by apply (extraction_of_not_tag trans lt' tag1 (T1 ++ trans :: T2)).
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
      - iExists (T' ++ [[Wr (tag1, c) k v]]), exec'.
        iSplitL "Htrans_res'"; first by iApply inv_ext_rc_wr_imp2.
        iExists t', (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]).
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
                  apply (valid_transactions_add1 T' (Wr (tag1, c) k v) c); try done.
                  ** by eapply extraction_of_not_in.
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
    iMod ("Hshift" with "[Hkey_internal Hkey_c]").
    {
      simpl.
      iFrame.
      iExists sa, γ.
      iFrame "#".
      iSplit; first by iPureIntro.
      iSplit.
      - iIntros (_).
        iFrame.
      - do 2 (iSplit; first by iPureIntro).
        iIntros (v' Heq).
        iExists (lt' ++ [(#tag1, (c, (#"WrLin", (#k, v))))%V]), tag1, c.
        assert (v.(SV_val) = v') as <-; first set_solver.
        iFrame "#".
        iPureIntro; set_solver.
    }
    iModIntro.
    rewrite /write_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T'' [%exec'' (Htrans_res'' & [%t'' [%lt'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hbased'' & %Hvalid_exec'' & %Hvalid_seq'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
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
    iMod ("Hclose''" with "[Htrans_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', exec''.
      iFrame.
      iExists (t'' ++ [(#tag1, (c, (#"WrPost", (#k, v))))%V]), lt''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_post_event /is_wr_post_event.
      set_solver.
    }
    set_solver.
  Qed.

  Lemma init_client_implication γtrans γmstate γmlin γmpost γmname γl clients (res : RC_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_rc -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtRC γtrans T ∗ GlobalInvExt commit_test_rc T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @init_client_proxy_spec _ _ _ _ lib res -∗
    @init_client_proxy_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γtrans γmstate γmlin γmpost γmname γl clients res).
  Proof.
    iIntros "%Hkvs_inv_name #Htr_inv #HinvExt #Hinit_cli".
    rewrite /init_client_proxy_spec.
    iIntros (sa Φ) "!# (Hunall & Hsock & Hmes & (Hcan & (Hsa_pointer & %Hsa_in)) & Hfree) HΦ".
    rewrite /TC_init_client_proxy /KVS_wrapped_api /wrap_init_client_proxy.
    wp_pures.
    wp_bind (ast.Fresh _).
    iInv "HinvExt" as ">[%T [%exec (Htrans_res & [%t [%lt  (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex 
      & %Hvalid_trans & %Hvalid_seq & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
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
    iMod ("Hclose" with "[Htrans_res Htr_is HOwnLin Hlin_res Hpost_res Hstate_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, init_pre_emit_event)%V]), lt.
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
    iInv "HinvExt" as ">[%T' [%exec' (Htrans_res' & [%t' [%lt' (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' 
      & %Hvalid_trans' & %Hvalid_seq' & %Hbased' & %Hvalid_exec' & Hstate_res' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
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
    iDestruct (res.(read_committed.specs.resources.Extraction_of_address) 
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
    iMod ("Hclose'" with "[Htrans_res' Htr_is HOwnLin' Hghost_map_mname Hext_rest1 Hext_rest1_sa 
      Hghost_map_mstate Hghost_map_m Hghost_elems_m Hlin_res' Hpost_res']").
    {
      iNext.
      iExists T', exec'.
      iFrame.
      iExists (t' ++ [(#tag1, (c, #"InPost"))%V]), (lt' ++ [(#tag1, (c, #"InLin"))%V]).
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

  Lemma start_implication γtrans γmstate γmlin γmpost γmname γl clients (res : RC_resources Mdl Σ) 
  (lib : KVS_transaction_api) : 
    ⌜KVS_InvName = nroot .@ "kvs_inv"⌝ -∗
    trace_inv trace_inv_name valid_trace_rc -∗
    inv KVS_InvName (∃ T exec, GlobalInvExtRC γtrans T ∗ GlobalInvExt commit_test_rc T extract γmstate γmlin γmpost γmname γl clients exec) -∗
    @start_spec _ _ _ _ lib res -∗
    @start_spec _ _ _ _ (KVS_wrapped_api lib) (wrapped_resources γtrans γmstate γmlin γmpost γmname γl clients res).
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
    iInv "HinvExt" as ">[%T [%exec (Htrans_res & [%t [%lt 
      (Htr_is & HOwnLin & %HlinOf & %Hno_empty & %Hex & %Hvalid_trans & %Hvalid_seq 
      & %Hbased & %Hvalid_exec & Hstate_res & Hlin_res & Hpost_res)]])]]" "Hclose".
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
    iMod ("Hclose" with "[Htrans_res Htr_is HOwnLin Hstate_res Hlin_res Hpost_res]").
    {
      iNext.
      iExists T, exec.
      iFrame.
      iExists (t ++ [(#tag1, (c, #"StPre"))%V]), lt.
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
    iInv "HinvExt" as ">[%T' [%exec' (Htrans_res' & [%t' [%lt' 
      (Htr_is' & HOwnLin' & %HlinOf' & %Hno_empty' & %Hex' & %Hvalid_trans' & 
      %Hvalid_seq' & %Hbased' & %Hvalid_exec' & HstateRes' & Hlin_res' & Hpost_res')]])]]" "Hclose'".
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
        iMod (@ghost_map_update _ Key (option val) _ _ _ _ _ k ov None with "[$Hghost_map'] [$Hkeys_conn_key]") 
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
    iMod ("Hclose'" with "[Htrans_res' Htr_is' HOwnLin' Hghost_map_mname' Hghost_map_m' 
      Hghost_map_mstate' Hkeys_conn_res2 Hlin_res' Hpost_res' Hdisj_trace_res]").
    {
      iModIntro.
      iExists T', exec'.
      iFrame.
      iExists t', (lt' ++ [(#tag1, (c, #"StLin"))%V]).
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
      do 2 (iSplitR; first by iPureIntro).
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
        iSplit.
        + iIntros (Hkey_in).
          iFrame.
        + do 2 (iSplit; first done).
          iIntros (v Hfalse); inversion Hfalse.
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
        iSplit.
        + iIntros (Hkey_in).
          set_solver.
        + do 2 (iSplit; first done).
          iIntros (v Hfalse); inversion Hfalse.
    }
    iModIntro.
    rewrite /start_post_emit_event.
    wp_pures.
    iInv "HinvExt" as ">[%T'' [%exec'' (Htrans_res'' & [%t'' [%lt'' 
      (Htr_is'' & HOwnLin'' & %HlinOf'' & %Hno_empty'' & %Hex'' & %Hvalid_trans'' & 
      %Hvalid_seq'' & %Hbased'' & %Hvalid_exec'' & HstateRes'' & Hlin_res'' & Hpost_res'')]])]]" "Hclose''".
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
    iMod ("Hclose''" with "[Htrans_res'' Htr_is'' HOwnLin'' HstateRes'' Hlin_res'' Hpost_res'']").
    {
      iModIntro.
      iExists T'', exec''.
      iFrame.
      iExists (t'' ++ [(#tag1, (c, #"StPost"))%V]), lt''.
      iFrame.
      iSplitR; last set_solver.
      iPureIntro.
      apply (lin_trace_valid tag1); try done.
      rewrite /is_post_event /is_st_post_event.
      set_solver.
    }
    set_solver.
  Qed.

  (* Primary lemma to be used with adequacy *)
  Lemma library_implication (clients : gset socket_address) (lib : KVS_transaction_api) :
    ((RC_spec clients lib) ∗ trace_is [] ∗ 
      trace_inv trace_inv_name valid_trace_rc ∗ ⌜KVS_InvName = nroot .@ "kvs_inv"⌝) ={⊤}=∗ 
    RC_spec clients (KVS_wrapped_api lib).
  Proof.
    iIntros "([%res (Hkeys & Hkvs_init & #Hglob_inv & Hcan_conn & 
      (#Hinit_kvs & #Hinit_cli & #Hread & #Hwrite & #Hstart & #Hcom))] & Htr & #Htr_inv & %Hkvs_inv_name)".    
    iMod (ghost_map_alloc ((gset_to_gmap (CanStart, None) clients : 
      gmap socket_address (local_state * option val))))
      as "[%γmstate (Hghost_map_mstate & Hghost_elems_mstate)]".
    iMod (ghost_map_alloc_empty (K:=string) (V:=bool)) as "[%γmlin Hghost_map_mlin]".
    iMod (ghost_map_alloc_empty (K:=string) (V:=bool)) as "[%γmpost Hghost_map_mpost]".
    iMod (ghost_map_alloc_empty (K:=socket_address) (V:=(gname * val))) as "[%γmname Hghost_map_mname]".
    iMod (own_alloc (●ML ([] : list val) ⋅ ◯ML ([] : list val))) as (γl) "[Hltrace _]".
    { 
      apply mono_list_both_dfrac_valid.
      by split; [done|exists []; done]. 
    }
    iMod (own_alloc (● gmap_of_trace 0 ([] : list transaction) ⋅ 
      ◯ gmap_of_trace 0 ([] : list transaction))) as (γtrans) "Htrans".
    {
      apply auth_both_valid. 
      split; first done. 
      by apply gmap_of_trace_valid.
    }
    iDestruct "Htrans" as "[Htrans Htrans_sub]".
    iMod (inv_alloc KVS_InvName ⊤ (∃ T exec, GlobalInvExtRC γtrans T ∗ GlobalInvExt commit_test_rc T extract γmstate γmlin γmpost γmname γl clients exec) with 
      "[Htr Hghost_map_mstate Hghost_map_mlin Hghost_map_mpost Hghost_map_mname Hltrace Htrans Htrans_sub]") as "#HinvExt".
    {
      iNext.
      iExists [], [([], ∅)].
      iSplitL "Htrans Htrans_sub".
      {
        iExists [].
        rewrite /OwnTrans.
        iFrame.
        simpl.
        iPureIntro; set_solver.
      }
      iExists [], [].
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
        rewrite /commit_test_rc /valid_execution /pre_read.
        split_and!; try done.
        - intros i e1 e2 _ Hfalse.
          rewrite list_lookup_singleton_Some in Hfalse.
          lia.
        - simpl.
          intros t Hin tag c k ov i _ Hfalse.
          assert (t = []) as ->; set_solver.
        - simpl.
          intros t1 t2 i j Hlookup_i Hlookup_j Heq.
          rewrite list_lookup_singleton_Some in Hlookup_i.
          rewrite list_lookup_singleton_Some in Hlookup_j.
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
    iExists (wrapped_resources γtrans γmstate γmlin γmpost γmname γl clients res).
    iFrame "Hkvs_init".
    iSplitL "Hkeys".
    {
      simpl.
      iApply (big_sepS_mono with "[$Hkeys]").
      iIntros (k Hin) "Hkey". 
      iFrame.
      iSplit; by iIntros (v) "%Hfalse".
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