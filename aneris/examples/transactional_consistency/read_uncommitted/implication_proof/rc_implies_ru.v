From iris.algebra Require Import gset auth gmap excl excl_auth csum.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.algebra.lib Require Import mono_list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
  Require Import serialization_proof.
From aneris.examples.reliable_communication.spec
     Require Import ras.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.transactional_consistency
     Require Import code_api.
From aneris.examples.transactional_consistency.read_committed.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency.read_uncommitted.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params aux_defs.

Section Implication.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params, !KVS_transaction_api}.

  Definition OwnAuthSet (γ : gname) (k : Key) (V : Vals) : iProp Σ := own γ (● {[k := V]}).
  Definition OwnFragSet (γ : gname) (k : Key) (V : Vals) : iProp Σ := own γ (◯ {[k := V]}).

  Lemma ownSetInclusion (γ : gname) (k : Key) (V V' : Vals) : 
    OwnAuthSet γ k V -∗ 
    OwnFragSet γ k V' -∗ 
    OwnAuthSet γ k V ∗ OwnFragSet γ k V' ∗ ⌜V' ⊆ V⌝.
  Proof.
    iIntros "Hauth Hfrag".
    unfold OwnAuthSet, OwnFragSet.
    iDestruct (own_valid_2 with "Hauth Hfrag") as %[Hord _]%auth_both_valid_discrete.
    iFrame.
    iPureIntro.
    apply (singleton_included k V' V) in Hord as [Hcase1 | Hcase2]; set_solver.
  Qed.

  Lemma ownSetAdd (γ : gname) (k : Key) (o : option val) (V : Vals) : 
    OwnAuthSet γ k V ==∗ 
    OwnAuthSet γ k (V ∪ {[o]}) ∗ OwnFragSet γ k (V ∪ {[o]}).
  Proof.
    iIntros "Hauth".
    unfold OwnAuthSet, OwnFragSet.
    iMod (own_update _ _ (● (<[k:=(V ∪ {[o]})]> {[k := V]}) ⋅ ◯ {[k := V ∪ {[o]}]}) with "Hauth") as "(Hauth & Hfrag)".
    - apply auth_update_alloc.
      apply (insert_alloc_local_update _ _ _ V).
      + by rewrite lookup_singleton.
      + by rewrite lookup_empty.
      + apply gset_local_update.
        set_solver.
    - iModIntro.
      rewrite insert_singleton.
      iFrame.
  Qed.

  Lemma ownSetCreate (γ : gname) (k : Key) (V : Vals) : 
    OwnAuthSet γ k V ==∗ 
    OwnAuthSet γ k V ∗ OwnFragSet γ k V.
  Proof.
    iIntros "Hauth".
    unfold OwnAuthSet, OwnFragSet.
    iMod (own_update _ _ (● (<[k := V]> {[k := V]}) ⋅ ◯ {[k := V]}) with "Hauth") as "(Hauth & Hfrag)".
    - apply auth_update_alloc.
      apply (insert_alloc_local_update _ _ _ V).
      + by rewrite lookup_singleton.
      + by rewrite lookup_empty.
      + by apply gset_local_update.
    - iModIntro.
      rewrite insert_singleton.
      iFrame.
  Qed.
 
  Global Program Instance RU_resources_instance (γ : gname) `(RC : !RC_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := RC.(read_committed.specs.resources.GlobalInv);
      OwnMemKey k V := (∃ (V' : Vals), ⌜V' ⊆ V⌝ ∗ 
                        RC.(read_committed.specs.resources.OwnMemKey) k V' ∗ OwnAuthSet γ k V)%I;
      OwnLocalKey k c vo := (∃ (V : Vals), ⌜vo ∈ V⌝ ∗ 
                            RC.(read_committed.specs.resources.OwnLocalKey) k c vo ∗ OwnFragSet γ k {[vo]})%I;
      ConnectionState c s sa := RC.(read_committed.specs.resources.ConnectionState) c s sa;
      IsConnected c sa := RC.(read_committed.specs.resources.IsConnected) c sa;
      KVS_ru := RC.(read_committed.specs.resources.KVS_rc);
      KVS_Init := RC.(read_committed.specs.resources.KVS_Init);
      KVS_ClientCanConnect sa := RC.(read_committed.specs.resources.KVS_ClientCanConnect) sa;
      Seen k V := OwnFragSet γ k V;
    |}.
  Next Obligation.
    iIntros (γ RC k cst v) "[%V (%Hsub & Hkey & Hfrag)]". 
    iDestruct (RC.(read_committed.specs.resources.OwnLocalKey_serializable) with "Hkey") as "(Hkey & Hser)".
    iFrame.
    by iExists V.
  Qed.
  Next Obligation.
    iIntros (γ RC E k V V' Hsub) "#Hinv (Hfrag & [%V'' (Hsub' & Hkey & Hauth)])".
    iDestruct (ownSetInclusion with "Hauth Hfrag") as "(Hauth' & Hfrag' & Hsub'')".
    iModIntro.
    iFrame.
    iExists V''.
    iFrame.
  Qed.
  Next Obligation.
    iIntros (γ RC E k V Hsub) "#Hinv [%V' (Hsub & Hkey & Hauth)]".
    iDestruct (ownSetCreate with "Hauth") as ">(dfg & asd)".
    iModIntro.
    iFrame.
    iExists V'.
    iFrame.
  Qed.

  Theorem implication_rc_ru : 
    RC_init → RU_init.
  Proof.
    intro RC_init.
    destruct RC_init.
    split.
    iIntros (E cli Hsub).
    iMod (RC_init_module E cli Hsub) as 
      "[%Hres (Hrc_keys & Hrc_kvs_init & Hrc_inv & Hrc_conn & Hrc_init_kvs
       & Hrc_init_cli & %Hrc_read & %Hrc_write & %Hrc_start & %Hrc_com)]".
    iMod (own_alloc (● (∅ : gmapUR Key (gsetUR (option val))))) as (γ) "Halgebra". 
    {
      by apply auth_auth_valid.
    }
    iAssert (|==> ([∗ set] k ∈ KVS_keys, own γ (● {[k := ∅]})))%I
              with "[Halgebra]" as "Halgebra".
    {
      clear RC_init_module.
      iInduction KVS_keys as [|k KVS_keys] "IH" using set_ind_L; first set_solver.
      (* Search "alloc". *)
      iMod ("IH" with "Halgebra") as "Halgebra".
      rewrite big_sepS_insert; last done.
      rewrite -(big_sepM_gset_to_gmap (λ k c, own γ (● {[k := c]})) KVS_keys ∅).
      (* Search "big_sepS_". *) 
      (* iMod (own_update _ _ (● (<[k := ∅]> (gset_to_gmap ∅ KVS_keys)) ⋅ ◯ {[k := ∅]}) with "Halgebra") as "(Halgebra & _)". *)
      admit.
    }
    iExists (RU_resources_instance γ Hres).
    iMod "Halgebra".
    iModIntro.
    simpl.
    iSplitL "Hrc_keys Halgebra".
    {
      unfold OwnAuthSet.
      iDestruct (big_sepS_sep with "[$Hrc_keys $Halgebra]") as "Hcombined". 
      iApply (big_sepS_mono with "[$Hcombined]").
      auto.
    }
    iSplitL "Hrc_kvs_init"; first done.
    iSplitL "Hrc_inv"; first done.
    iSplitL "Hrc_conn"; first done.
    iSplitL "Hrc_init_kvs"; first done.
    iSplitL "Hrc_init_cli"; first done.
    iSplitL.
    {
      unfold read_spec.
      iPureIntro.
      iIntros (c sa E' k vo) "Hsub' Hk_in Hconn".
      unfold read_committed.specs.specs.read_spec in Hrc_read.
      iDestruct (Hrc_read c sa E' k vo with "Hsub' Hk_in Hconn") as "Hrc_read".
      iIntros (Φ).
      iDestruct ("Hrc_read" $! Φ) as "#Hrc_read".
      iModIntro.
      simpl.
      iIntros (E'') "#Hsub' [%V (%Hin & Hloc_key & Hfrag)] Hhyp".
      iApply ("Hrc_read" $! E'' with "[$Hsub'] [$Hloc_key]").
      iMod "Hhyp".
      iDestruct ("Hhyp") as "[%V' ([%V'' (%Hsub'' & Hmem_key & Hauth)] & Hhyp)]".
      iModIntro.
      iExists V''.
      iFrame.
      iNext.
      iIntros "Hmem_key".
      iMod ("Hhyp" with "[Hmem_key Hauth]") as "Hhyp".
      - iExists V''.
        iFrame "∗".
        by iPureIntro.
      - iModIntro.
        iIntros (wo) "(Hloc_key & Heq)".
        iApply ("Hhyp" $! wo).
        iFrame.
        iSplitR.
        + iExists _.
          by iPureIntro. 
        + iDestruct ("Heq") as "[%Heq | %Heq]". 
          * iLeft.
            iPureIntro.
            set_solver.
          * by iRight.
    }
    iSplitL.
    {
      unfold read_spec.
      admit.
    }
    iSplitL.
    {
      unfold read_spec.
      admit.
    }
    admit.
  Admitted.

End Implication.