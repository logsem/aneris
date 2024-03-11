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
From aneris.aneris_lang.program_logic Require Import lightweight_atomic aneris_weakestpre.
From aneris.examples.transactional_consistency
     Require Import code_api.
From aneris.examples.transactional_consistency.read_committed.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency.read_uncommitted.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params aux_defs.

Section Implication.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params, !KVS_transaction_api}.

  Definition OwnAuthSet (γA : gname) (k : Key) (V : Vals) : iProp Σ := ghost_map_elem γA k (DfracOwn 1%Qp) V.
  Definition OwnFragSet (γF : gname) (k : Key) (V : Vals) : iProp Σ := own γF (◯ {[k := V]}).
  Definition OwnInv (γA γF: gname) : iProp Σ := ∃ (m : gmap Key Vals), ghost_map_auth γA (1%Qp) m ∗ own γF (● m).

  Lemma ownSetInclusion (γA γF: gname) (k : Key) (V V' : Vals) : 
    OwnInv γA γF -∗
    OwnAuthSet γA k V -∗ 
    OwnFragSet γF k V' -∗ 
    OwnInv γA γF ∗ OwnAuthSet γA k V ∗ OwnFragSet γF k V' ∗ ⌜V' ⊆ V⌝.
  Proof.
    iIntros "[%m (Hinv_1 & Hinv_2)] Hauth Hfrag".
    unfold OwnAuthSet, OwnFragSet.
    iPoseProof (ghost_map_lookup with "[$Hinv_1] [$Hauth]") as "%Hlook_up". 
    iDestruct (own_valid_2 with "Hinv_2 Hfrag") as %[Hord _]%auth_both_valid_discrete.
    rewrite singleton_included_l in Hord.
    destruct Hord as [V'' (<- & Hord)].
    rewrite Hlook_up in Hord.
    iFrame.
    iSplitL.
    - unfold OwnInv.
      iExists m. 
      iFrame.
    - iPureIntro.
      rewrite Some_included_total in Hord.
      set_solver.
  Qed.

  Lemma ownSetAdd (γA γF: gname) (k : Key) (o : option val) (V : Vals) : 
    OwnInv γA γF ∗ OwnAuthSet γA k V ==∗ 
    OwnInv γA γF ∗ OwnAuthSet γA k (V ∪ {[o]}) ∗ OwnFragSet γF k (V ∪ {[o]}).
  Proof.
    iIntros "([%m (Hinv_1 & Hinv_2)] & Hauth)".
    iPoseProof (ghost_map_lookup with "[$Hinv_1] [$Hauth]") as "%Hsome".
    unfold OwnInv, OwnAuthSet, OwnFragSet.
    iMod (ghost_map_update (V ∪ {[o]}) with "[$Hinv_1] [$Hauth]") 
      as "(Hinv_1 & Hauth)".
    iMod (own_update _ _ (● (<[k:=(V ∪ {[o]})]> m) ⋅ ◯ {[k := V ∪ {[o]}]}) with "Hinv_2") 
      as "(Hinv_2 & Hfrag)".
    - apply auth_update_alloc.
      apply (insert_alloc_local_update _ _ _ V).
      + done.
      + by rewrite lookup_empty.
      + apply gset_local_update.
        set_solver.
    - iModIntro.
      iFrame.
      iExists _.
      iFrame.
  Qed.

  Lemma ownSetCreate (γA γF: gname) (k : Key) (V : Vals) : 
    OwnInv γA γF ∗ OwnAuthSet γA k V ==∗ 
    OwnInv γA γF ∗ OwnAuthSet γA k V ∗ OwnFragSet γF k V.
  Proof.
    iIntros "([%m (Hinv_1 & Hinv_2)] & Hauth)".
    iPoseProof (ghost_map_lookup with "[$Hinv_1] [$Hauth]") as "%Hsome".
    unfold OwnAuthSet, OwnFragSet.
     iMod (ghost_map_update V with "[$Hinv_1] [$Hauth]") 
      as "(Hinv_1 & Hauth)".
    iMod (own_update _ _ (● (<[k := V]> m) ⋅ ◯ {[k := V]}) with "Hinv_2") as "(Hinv_2 & Hfrag)".
    - apply auth_update_alloc.
      apply (insert_alloc_local_update _ _ _ V).
      + done.
      + by rewrite lookup_empty.
      + by apply gset_local_update.
    - iModIntro.
      iFrame.
      iExists _.
      iFrame.
  Qed.

  Global Program Instance RU_resources_instance (γA γF : gname) `(RC : !RC_resources Mdl Σ) : RU_resources Mdl Σ :=
    {|
      GlobalInv := RC.(read_committed.specs.resources.GlobalInv) ∗ inv KVS_InvName (OwnInv γA γF);
      OwnMemKey k V := (∃ (V' : Vals), ⌜V' ⊆ V⌝ ∗ RC.(read_committed.specs.resources.OwnMemKey) k V' ∗ OwnAuthSet γA k V)%I;
      OwnLocalKey k c vo := (∃ (V : Vals), ⌜vo ∈ V ∨ vo = None⌝ ∗ 
                            RC.(read_committed.specs.resources.OwnLocalKey) k c vo ∗ OwnFragSet γF k {[vo]})%I;
      ConnectionState c s sa := RC.(read_committed.specs.resources.ConnectionState) c s sa;
      IsConnected c sa := RC.(read_committed.specs.resources.IsConnected) c sa;
      KVS_ru := RC.(read_committed.specs.resources.KVS_rc);
      KVS_Init := RC.(read_committed.specs.resources.KVS_Init);
      KVS_ClientCanConnect sa := RC.(read_committed.specs.resources.KVS_ClientCanConnect) sa;
      Seen k V := OwnFragSet γF k V;
    |}.
  Next Obligation.
    iIntros (_ γ RC k cst v) "[%V (%Hsub & Hkey & Hfrag)]". 
    iDestruct (RC.(read_committed.specs.resources.OwnLocalKey_serializable) with "Hkey") as "(Hkey & Hser)".
    iFrame.
    by iExists V.
  Qed.
  Next Obligation.
    iIntros (γA γF RC E k V V' Hsub) "#(_ & Hinv) (Hfrag & [%V'' (Hsub' & Hkey & Hauth)])".
    iInv KVS_InvName as ">Hinv_res" "Hinv_close".
    iDestruct (ownSetInclusion with "[$Hinv_res] [$Hauth] [$Hfrag]") as "(Hinv_res & Hauth' & Hfrag' & Hsub'')".
    iMod ("Hinv_close" with "[Hinv_res]") as "_"; first done.
    iModIntro.
    iFrame.
    iExists _.
    iFrame.
  Qed.
  Next Obligation.
    iIntros (γA γF RC E k V Hsub) "#(_ & Hinv) [%V'' (Hsub' & Hkey & Hauth)]".
    iInv KVS_InvName as ">Hinv_res" "Hinv_close".
    iDestruct (ownSetCreate with "[$Hinv_res $Hauth]") as ">(Hinv_res & Hauth & Hfrag)". 
    iMod ("Hinv_close" with "[Hinv_res]") as "_"; first done.
    iModIntro.
    iFrame.
    iExists _.
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
       & Hrc_init_cli & Hrc_read & Hrc_write & Hrc_start & Hrc_com)]".
    iMod (own_alloc (● (gset_to_gmap ∅ KVS_keys : gmap Key Vals))) as (γF) "Hauth_map". 
    {
      apply auth_auth_valid.
      clear RC_init_module.
      induction KVS_keys as [|x X Hnotin IH] using set_ind_L; first done.
      rewrite gset_to_gmap_union_singleton.
      apply insert_valid; done.
    }
    iDestruct (ghost_map_alloc (gset_to_gmap ∅ KVS_keys : gmap Key Vals)) as ">[%γA (Hghost_map & Hghost_elems)]".
    rewrite (big_sepM_gset_to_gmap (λ k v, ghost_map_elem γA k _ v) KVS_keys ∅).
    iMod (inv_alloc KVS_InvName E (OwnInv γA γF) with "[Hauth_map Hghost_map]") as "#Hinv".
    {
      iNext.
      iExists _.
      iFrame. 
    }
    iModIntro. 
    iExists (RU_resources_instance γA γF Hres).
    simpl.
    iSplitL "Hrc_keys Hghost_elems".
    {
      unfold OwnAuthSet.
      iDestruct (big_sepS_sep with "[$Hrc_keys $Hghost_elems]") as "Hcombined". 
      iApply (big_sepS_mono with "[$Hcombined]").
      iIntros (k Hk_in) "(Hk_mem & Hk_elem)".
      iExists ∅.
      by iFrame.
    }
    iSplitL "Hrc_kvs_init"; first done.
    iSplitL "Hrc_inv"; first iFrame "#∗".
    iSplitL "Hrc_conn"; first done.
    iSplitL "Hrc_init_kvs"; first done.
    iSplitL "Hrc_init_cli"; first done.
    iSplitL "Hrc_read".
    { 
      unfold read_spec, read_committed.specs.specs.read_spec.
      iIntros (c sa E' k vo) "Hsub' Hk_in Hconn".
      iDestruct ("Hrc_read" $! c sa E' k vo with "Hsub' Hk_in Hconn") as "Hrc_read".
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
    iSplitL "Hrc_write".
    {
      unfold write_spec, read_committed.specs.specs.write_spec.
      iIntros (c sa E' k v vo) "%Hsub' Hk_in Hconn".
      iDestruct ("Hrc_write" $! c sa ⊤ k v vo _ with "Hk_in Hconn") as "Hrc_write".
      iIntros (Φ).
      iDestruct ("Hrc_write" $! Φ) as "#Hrc_write".
      iModIntro. 
      simpl.
      iIntros (E'') "%Hsub'' [%V (%Hin & Hloc_key & Hfrag)] Hhyp".
      iDestruct ("Hrc_write" with "[$Hloc_key]") as "Hrc_write'".
      iApply "Hrc_write'".
      (* unfold aneris_wp.
      (* iApply "Hrc_write'".
       *)
      iAssert (▷ (read_committed.specs.resources.OwnLocalKey k c (Some v.(SV_val)) -∗ Φ #()))%I as "Hrc_write_hyp".
      - admit.
      -  
        iDestruct ("Hrc_write'" with "[$Hrc_write_hyp]") as "Hgoal".
        (* Set Printing All. *)
        iApply "Hgoal".

        iAssert (WP TC_write c #k v @[ip_of_address sa] {{ v, Φ v }})%I  with "[$Hgoal]" as "øæløæl".
        iFrame.
        admit.
        iApply "øæløæl".



        iApply "Hgoal".
        (* Unset Printing Coercion. *)
        Unset Printing Notations.


      iApply fupd_aneris_wp.
      iMod "Hhyp" as "[%V' ([%V'' (%Hsub''' & Hkey_mem & Hauth)] & Hhyp)]".
      iInv KVS_InvName as ">Hown_inv" "Hclose"; first set_solver.
      iDestruct (ownSetAdd _ _ _ (Some v.(SV_val)) with "[$Hown_inv $Hauth]") 
        as ">(Hown_inv & Hauth & Hfrag')".
      iMod ("Hclose" with "[Hown_inv]"); first done.
      iDestruct ("Hhyp" with "[Hkey_mem Hauth]") as "Hhyp".
      - iNext.
        iExists V''.
        iFrame.
        iPureIntro.
        set_solver.
      - *)
(* 
      iDestruct ("Hrc_write'" with "[]") as "Hrc_writeælk".
      {
        admit.
      }
      iApply "Hrc_write'".
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
          * by iRight. *)
      admit.
    }
    iSplitL.
    {
      (* unfold start_spec.
      iPureIntro.
      iIntros (c sa E') "#Hsub' Hconn".
      unfold read_committed.specs.specs.start_spec in Hrc_start.
      iDestruct (Hrc_start c sa E' with "Hsub' Hconn") as "Hrc_start".
      iIntros (Φ).
      iDestruct ("Hrc_start" $! Φ) as "#Hrc_start".
      iModIntro.
      simpl.
      iIntros (E'') "#Hsub'' Hconn Hhyp".
      iApply ("Hrc_start" $! E'' with "[$Hsub''] [$Hconn]").
      iMod "Hhyp".
      iDestruct ("Hhyp") as "[%m (Hres & Hhyp)]".
      iModIntro.
      (* iExists _. *)
      (* Search "big_sepM_". *)
      (* iDestruct (big_sepM_sep with "[Hres]") as "(Hres1 & Hres2)". *)
      iDestruct (big_sepM_mono 
        (λ k V, ∃ V' : Vals, ⌜V' ⊆ V⌝ ∗ read_committed.specs.resources.OwnMemKey k V' ∗ OwnAuthSet γA k V)%I
        (λ k V, (∃ V', ⌜V' ⊆ V⌝ ∗ read_committed.specs.resources.OwnMemKey k V') ∗ (OwnAuthSet γA k V))%I 
        with "[$Hres]") as "Hres".
      - iIntros (k V Hsome) "[%V' (Hsub & Hkey & Hauth)]".
        iFrame.
        iExists _.
        iFrame.
      - rewrite big_sepM_sep.
        iDestruct "Hres" as "(Hkeys & Hauths)". *)
        (* iInduction m as [|k V m H_lookup] "IH" using map_ind.
        + iExists ∅.
          do 6 rewrite big_sepM_empty.
          iFrame.
        +

        iExists _.
        iSplitL "Hkeys".
        + iApply big_sepM_intro.

        
        Search "big_sepM_dom".
        +

      Search "big_sepM_mono".
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
          * by iRight. *)
      admit.
    }
    admit.
  Admitted.

End Implication.