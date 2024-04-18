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

  Lemma ownSetAdd (γA γF: gname) (k : Key) (o : val) (V : Vals) : 
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
      OwnLocalKey k c vo := (∃ (V : Vals), ⌜(∃ v, vo = Some v ∧ v ∈ V) ∨ vo = None⌝ ∗ 
                             RC.(read_committed.specs.resources.OwnLocalKey) k c vo ∗ OwnFragSet γF k V)%I;
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
    iExists V.
    by iFrame.
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
  
  Lemma rewrite_maps_1 `{RC : !RC_resources Mdl Σ} (m : gmap Key Vals) (γA : gname) :
    ([∗ map] k↦V ∈ m, ∃ V', ⌜V' ⊆ V⌝ ∗ read_committed.specs.resources.OwnMemKey k V' ∗ 
    OwnAuthSet γA k V) -∗
    (∃ m', ⌜dom m = dom m'⌝ ∗ ([∗ map] k↦V ∈ m', (∃ V', ⌜V ⊆ V'⌝ ∗ ⌜m !! k = Some V'⌝ ∗ 
    read_committed.specs.resources.OwnMemKey k V ∗ OwnAuthSet γA k V'))).
  Proof.
    iIntros "Hmem_keys".
    iInduction m as [|k V m H_lookup] "IH" using map_ind.
    - iExists ∅.
      iSplitL; done.
    - rewrite big_sepM_insert; last done.
      iDestruct "Hmem_keys" as "([%V' (%Hsub'' & Hmem_k & Hauth_k)] & Hmem_keys)".
      iDestruct ("IH" with "[$Hmem_keys]") as "[%m' (%Hdom & Hmem_keys)]".
      iExists (<[k:=V']> m').
      iSplitR.
      {
        iPureIntro.
        set_solver.
      }
      rewrite big_sepM_insert.
      + 
        iFrame.
        iSplitL "Hauth_k".
        * iExists V.
          iFrame.
          iPureIntro.
          split; first done.
          apply lookup_insert.
        * iApply (big_sepM_mono with "[$Hmem_keys]").
          iIntros (kx x H_lookup') "[%x' (Hsub''' & %H_lookup''' & Hmem_key & Hauth_key)]".
          iExists x'.
          iFrame.
          iPureIntro.
          destruct (decide (k = kx)) as [-> | Hneq].
          -- apply elem_of_dom_2 in H_lookup'.
              rewrite -Hdom in H_lookup'.
              by rewrite -not_elem_of_dom in H_lookup.
          -- rewrite lookup_insert_ne; done.
      + rewrite -not_elem_of_dom.
        rewrite -not_elem_of_dom in H_lookup.
        set_solver.
  Qed.

  Lemma rewrite_maps_2 `{RC : !RC_resources Mdl Σ} (m m' : gmap Key Vals) (γA : gname) :
    ([∗ map] k↦V ∈ m', ∃ V', ⌜V ⊆ V'⌝ ∗ ⌜m !! k = Some V'⌝ ∗ 
    read_committed.specs.resources.OwnMemKey k V ∗ OwnAuthSet γA k V') -∗
    (([∗ map] k↦x ∈ m', ∃ V' : Vals, ⌜x ⊆ V'⌝ ∗ ⌜m !! k = Some V'⌝ ∗ OwnAuthSet γA k V') ∗ 
    ([∗ map] k↦x ∈ m', read_committed.specs.resources.OwnMemKey k x)).
  Proof.
    iIntros "Hmem_keys".
    iDestruct (big_sepM_mono 
    (λ k V, ∃ V', ⌜V ⊆ V'⌝ ∗ ⌜m !! k = Some V'⌝ ∗ read_committed.specs.resources.OwnMemKey k V ∗ OwnAuthSet γA k V')%I
    (λ k V, (∃ V', ⌜V ⊆ V'⌝ ∗ ⌜m !! k = Some V'⌝ ∗ OwnAuthSet γA k V') ∗ (read_committed.specs.resources.OwnMemKey k V))%I 
    with "[$Hmem_keys]") as "Hmem_keys".
    {
      iIntros (k V Hsome) "[%V' (Hsub & Hlookup & Hkey & Hauth)]".
      iFrame.
      iExists V'.
      iFrame.
    }
    rewrite big_sepM_sep.
    iFrame.
  Qed.

  Lemma rewrite_maps_3 `{RC : !RC_resources Mdl Σ} (m m' : gmap Key Vals) (γA : gname) :
    dom m = dom m' → 
    ([∗ map] k↦V ∈ m', read_committed.specs.resources.OwnMemKey k V) -∗
    ([∗ map] k↦x ∈ m', ∃ V', ⌜x ⊆ V'⌝ ∗ ⌜m !! k = Some V'⌝ ∗ OwnAuthSet γA k V') -∗
    ([∗ map] k↦V ∈ m, ∃ V', ⌜V' ⊆ V⌝ ∗ read_committed.specs.resources.OwnMemKey k V' ∗ 
    OwnAuthSet γA k V).
  Proof.
    generalize dependent m.
    induction m' as [|k V m' H_lookup IH] using map_ind.
    - iIntros (m Hdom) "_ _".
      rewrite dom_empty_L in Hdom.
      rewrite dom_empty_iff_L in Hdom.
      by rewrite Hdom.
    - iIntros (m Hdom) "Hmem_keys Hauth_keys".
      rewrite big_sepM_insert; last done.
      iDestruct "Hmem_keys" as "(Hmem_key & Hmem_keys)".
      rewrite big_sepM_insert; last done.
      iDestruct "Hauth_keys" as "([%V' (%Hsub'' & %H_lookup' & Hauth_key)] & Hauth_keys)".
      assert (k ∈ dom m) as Hin; first by set_solver.
      rewrite elem_of_dom in Hin.
      destruct (m !! k) as [V''|] eqn:Heq; last by destruct Hin.
      rewrite -(insert_delete _ _ _ Heq).
      rewrite -(insert_delete _ _ _ Heq) in Hdom.
      assert (dom (delete k m) = dom m') as Hdom'.
      {
        do 2 rewrite dom_insert_L in Hdom.
        rewrite -(delete_notin _ _ H_lookup) in Hdom.
        rewrite -(delete_notin _ _ H_lookup).
        set_solver.
      }
      iAssert (([∗ map] k0↦y ∈ m', ∃ V'0 : Vals, ⌜y ⊆ V'0⌝ ∗ 
                ⌜(delete k m) !! k0 = Some V'0⌝ ∗ 
                OwnAuthSet γA k0 V'0))%I 
                with "[Hauth_keys]" as "Hauth_keys".
      {
        iApply (big_sepM_mono with "[$Hauth_keys]").
        iIntros (kx x H_lookup'') "[%x' (Hsub''' & %H_lookup''' & Hauth_key)]".
        iExists x'.
        iFrame.
        iPureIntro.
        destruct (decide (k = kx)) as [-> | Hneq].
        - apply elem_of_dom_2 in H_lookup''.
          rewrite -Hdom' in H_lookup''.
          rewrite dom_delete_L in H_lookup''.
          set_solver.
        - rewrite lookup_insert_ne in H_lookup'''; done.
      }
      iDestruct (IH _  Hdom' with "[$Hmem_keys] [$Hauth_keys]") as "IH".
      rewrite big_sepM_insert.
      + iFrame.
        iExists V.
        inversion H_lookup' as [Heq'].
        iFrame.
        by iPureIntro.
      + apply lookup_delete.
  Qed.

  Lemma rewrite_maps_4 `{RC : !RC_resources Mdl Σ} (c : val) (mc : gmap Key (option val)) (γF : gname) :
    ([∗ map] k↦vo ∈ mc, ∃ V, ⌜(∃ v, vo = Some v ∧ v ∈ V) ∨ vo = None⌝ ∗ 
    read_committed.specs.resources.OwnLocalKey k c vo ∗ OwnFragSet γF k V) -∗
    (([∗ map] k↦vo ∈ mc, read_committed.specs.resources.OwnLocalKey k c vo) ∗ 
    ([∗ map] k↦vo ∈ mc, ∃ V, ⌜(∃ v, vo = Some v ∧ v ∈ V) ∨ vo = None⌝ ∗ OwnFragSet γF k V)).
  Proof.
    iIntros "Hloc_keys".
    iDestruct (big_sepM_mono 
    (λ k vo, ∃ V, ⌜(∃ v, vo = Some v ∧ v ∈ V) ∨ vo = None⌝ ∗ read_committed.specs.resources.OwnLocalKey k c vo ∗ OwnFragSet γF k V)%I
    (λ k vo, (∃ V, ⌜(∃ v, vo = Some v ∧ v ∈ V) ∨ vo = None⌝ ∗ OwnFragSet γF k V) ∗ (read_committed.specs.resources.OwnLocalKey k c vo))%I 
    with "[$Hloc_keys]") as "Hloc_keys".
    {
      iIntros (k vo Hsome) "[%V' (Hdisj & Hkey & Hfrag)]".
      iFrame.
      iExists V'.
      iFrame.
    }
    rewrite big_sepM_sep.
    iDestruct "Hloc_keys" as "(Hloc_keys & Hfrag_keys)".
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
      "[%Hres (Hrc_keys & Hrc_kvs_init & Hrc_inv & Hrc_conn & #Hrc_init_kvs
       & #Hrc_init_cli & #Hrc_read & #Hrc_write & #Hrc_start & #Hrc_com)]".
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
    iSplitL.
    { 
      iClear "Hrc_com Hrc_start Hrc_write Hrc_init_cli Hrc_init_kvs". 
      unfold read_spec, read_committed.specs.specs.read_spec.
      iModIntro.
      iIntros (c sa E' k) "Hsub' Hk_in Hconn".
      iDestruct ("Hrc_read" $! c sa E' k with "Hsub' Hk_in Hconn") as "Hrc_read'".
      iIntros (Φ).
      iDestruct ("Hrc_read'" $! Φ) as "#Hrc_read''".
      iModIntro.
      iIntros "Hhyp".
      iApply "Hrc_read''".
      iMod "Hhyp" as "[%vo [%V (([%V' (%H_or_eq & Hloc_key & Hfrag)] & 
                      [%V'' (%Hsub' & Hmem_key & Hauth)]) & Hhyp_later)]]".
      iModIntro.
      iExists vo, V''.
      iSplitL "Hloc_key Hmem_key"; first iFrame.
      iNext.
      iIntros (wo) "(Hloc_key & Hmem_key & Hdisj)".
      iApply "Hhyp_later".
      simpl.
      iSplitL "Hloc_key Hfrag".
      {
        iExists V'.
        iFrame.
        by iPureIntro.
      }
      iSplitL "Hmem_key Hauth".
      {
        iExists V''.
        iFrame.
        by iPureIntro.
      }
      iDestruct ("Hdisj") as "[%Heq | %Heq]".
      {
        iLeft.
        iSplit; by set_solver.
      } 
      by iRight.
    }
    iSplitL "Hrc_write".
    {
      iClear "Hrc_com Hrc_start Hrc_read Hrc_init_cli Hrc_init_kvs". 
      unfold write_spec, read_committed.specs.specs.write_spec.
      iModIntro.
      iIntros (c sa E' k v) "%Hsub' Hk_in Hconn".
      iDestruct ("Hrc_write" $! c sa E' k v Hsub' with "Hk_in Hconn") as "Hrc_write'".
      iIntros (Φ).
      iDestruct ("Hrc_write'" $! Φ) as "#Hrc_write''".
      iModIntro.
      iIntros "Hhyp".
      iApply "Hrc_write''".
      iMod "Hhyp" as "[%vo [%V (([%V' (%H_or_eq & Hloc_key & Hfrag)] & 
                      [%V'' (%Hsub'' & Hmem_key & Hauth)]) & Hhyp_later)]]".
      iModIntro.
      iExists vo.
      iSplitL "Hloc_key"; first iFrame.
      iNext.
      iIntros "Hloc_key".
      iInv KVS_InvName as ">Hown_inv" "Hclose".
      iDestruct (ownSetAdd _ _ _ (v.(SV_val)) with "[$Hown_inv $Hauth]") 
        as ">(Hown_inv & Hauth & Hfrag')".
      iMod ("Hclose" with "[Hown_inv]"); first done.
      iApply "Hhyp_later".
      simpl.
      iSplitL "Hloc_key Hfrag'".
      {
        iExists (V ∪ {[v.(SV_val)]}).
        iFrame.
        iPureIntro. 
        left.
        set_solver.
      }
      iExists V''.
      iFrame.
      iPureIntro. 
      set_solver.
    }
    iSplitL "Hrc_start".
    {
      iClear "Hrc_com Hrc_read Hrc_write Hrc_init_cli Hrc_init_kvs". 
      unfold start_spec, read_committed.specs.specs.start_spec.
      iModIntro.
      iIntros (c sa E') "%Hsub' Hconn".
      iDestruct ("Hrc_start" $! c sa E' Hsub' with "Hconn") as "Hrc_start'".
      iIntros (Φ).
      iDestruct ("Hrc_start'" $! Φ) as "#Hrc_start''".
      iModIntro.
      iIntros "Hhyp".
      iApply "Hrc_start''".
      iMod "Hhyp" as "[%m ((Hstate & Hmem_keys) & Hhyp_later)]".
      iModIntro.
      simpl.
      iDestruct (rewrite_maps_1 with "[$Hmem_keys]") as "[%m' (%Hdom & Hmem_keys)]".
      iExists m'.
      iFrame.
      iDestruct (rewrite_maps_2 with "[$Hmem_keys]") as "(Hauth_keys & Hmem_keys)".
      iFrame.
      iNext.
      iIntros "(Hstate & Hmem_keys & Hloc_keys)".
      iDestruct (rewrite_maps_3 _ _ _ Hdom with "[$Hmem_keys] [$Hauth_keys]") as "Hmem_keys".
      iInv KVS_InvName as ">Hinv_res" "Hinv_close".
      iAssert (|==>(([∗ map] k↦V ∈ m, ∃ V' : Vals, ⌜V' ⊆ V⌝ ∗ 
                read_committed.specs.resources.OwnMemKey k V' ∗ 
                OwnAuthSet γA k V ∗ OwnFragSet γF k V) ∗ OwnInv γA γF))%I 
              with "[Hmem_keys Hinv_res]" as ">(Hmem_keys & Hinv_res)".
      {
        clear Hdom.
        iInduction m as [|k V m H_lookup] "IH" using map_ind.
        - iModIntro.
          by iFrame.
        - rewrite big_sepM_insert; last done.
          iDestruct "Hmem_keys" as "([%V' (%Hsub'' & Hmem_k & Hauth_k)] & Hmem_keys)".
          iMod ("IH" with "[$Hmem_keys] [$Hinv_res]") as "(Hmem_keys & Hinv_res)".
          iDestruct (ownSetCreate with "[$Hinv_res $Hauth_k]") as ">(Hinv_res & Hauth_k & Hfrag_k)". 
          iModIntro.
          iFrame.
          rewrite big_sepM_insert; last done.
          iFrame.
          iExists V'.
          iFrame.
          by iPureIntro.
      }
      iMod ("Hinv_close" with "[Hinv_res]") as "_"; first done.
      iDestruct (big_sepM_mono 
                (λ k V, ∃ V', ⌜V' ⊆ V⌝ ∗ read_committed.specs.resources.OwnMemKey k V' 
                ∗ OwnAuthSet γA k V ∗ OwnFragSet γF k V)%I
                (λ k V, (∃ V', ⌜V' ⊆ V⌝ ∗ read_committed.specs.resources.OwnMemKey k V' 
                ∗ OwnAuthSet γA k V)∗ OwnFragSet γF k V)%I
                with "[$Hmem_keys]") as "Hmem_keys".
      {
        iIntros (k V Hsome) "[%V' (Hsub'' & Hmem_key & Hauth_key & Hfra_key)]".
        iFrame.
        iExists V'.
        iFrame.
      }
      rewrite big_sepM_sep.
      iDestruct "Hmem_keys" as "(Hmem_keys & Hfrag_keys)".
      iApply "Hhyp_later".
      rewrite Hdom.
      iFrame.
      rewrite big_sepM_dom.
      rewrite -Hdom.
      rewrite -big_sepM_dom.
      iDestruct (big_sepM_sep_2 with "[$Hloc_keys] [$Hfrag_keys]") as "Hloc_keys".
      iApply (big_sepM_mono with "[$Hloc_keys]").
      iIntros (k V Hsome) "Hkey".
      iExists V.
      iFrame.
      iPureIntro.
      by right.
    }
    iClear "Hrc_read Hrc_start Hrc_write Hrc_init_cli Hrc_init_kvs". 
    unfold commit_spec, read_committed.specs.specs.commit_spec.
    iModIntro.
    iIntros (c sa E') "%Hsub' Hconn".
    iDestruct ("Hrc_com" $! c sa E' Hsub' with "Hconn") as "Hrc_com'".
    iIntros (Φ).
    iDestruct ("Hrc_com'" $! Φ) as "#Hrc_com''".
    iModIntro.
    iIntros "Hhyp".
    iApply "Hrc_com''".
    iMod "Hhyp" as "[%s [%mc [%m ((Hstate & %Hdom1 & %Hdom2 & Hloc_keys & Hmem_keys) & Hhyp_later)]]]".
    iModIntro.
    simpl.
    iDestruct (rewrite_maps_1 with "[$Hmem_keys]") as "[%m' (%Hdom & Hmem_keys)]".
    iExists s, mc, m'.
    iDestruct (rewrite_maps_2 with "[$Hmem_keys]") as "(Hauth_keys & Hmem_keys)".
    iFrame.
    iDestruct (rewrite_maps_4 with "[$Hloc_keys]") as "(Hloc_keys & Hfrag_keys)".
    iSplitL "Hloc_keys".
    {
      iSplitR; first by iPureIntro.
      iSplitR.
      - iPureIntro.
        set_solver.
      - iFrame.
    }
    iNext.
    iIntros (b) "(Hstate & Hdisj)".
    iDestruct "Hdisj" as "[(_ & Hmem_keys) | (_ & Hmem_keys)]".
    - iAssert (([∗ map] k↦vo ∈ mc, emp)%I) as "Hemp_keys"; first done.
      assert (∀ k , is_Some (m' !! k) ↔ is_Some (mc !! k)) as Hsome_iff.
      {
        intro k.
        split.
        all : intro Hsome.
        by rewrite -elem_of_dom -Hdom -Hdom2 elem_of_dom in Hsome.
        1 : by rewrite -elem_of_dom Hdom2 Hdom elem_of_dom in Hsome.
      }
      iDestruct (big_sepM2_sepM_2 with "[$Hauth_keys] [$Hemp_keys]") as "Hauth_keys"; first done.
      iDestruct (big_sepM2_sep_2 with "[$Hauth_keys] [$Hmem_keys]") as "Hmem_keys".
      iAssert (([∗ map] k↦vo ∈ m', emp)%I) as "Hemp_keys'"; first done.
      iDestruct (big_sepM2_sepM_2 with "[$Hemp_keys'] [$Hfrag_keys]") as "Hfrag_keys"; first done.
      iDestruct (big_sepM2_sep_2 with "[$Hfrag_keys] [$Hmem_keys]") as "Hmem_keys".
      iInv KVS_InvName as ">Hinv_res" "Hinv_close".
      iAssert ((|==>(([∗ map] k↦V;vo ∈ m';mc,
                (∃ V', ⌜V ⊆ V'⌝ ∗ ⌜m !! k = Some V'⌝ ∗ OwnAuthSet γA k V' ∗
                (∃ V'', ⌜V'' ⊆ V'⌝ ∗ read_committed.specs.resources.OwnMemKey k V'')) ∗ emp)) ∗ OwnInv γA γF)%I) 
                 with "[Hmem_keys Hinv_res]" as ">(Hmem_keys & Hinv_res)".
      {
        iClear "Hemp_keys Hemp_keys' Hrc_com Hrc_com'' Hinv" .
        iStopProof.
        clear Hdom Hdom1 Hdom2.
        generalize dependent mc.
        induction m' as [|k V m' Hlookup IH] using map_ind.
        - iIntros (mc Hsome_iff) "(Hkeys & Hinv_res)".
          iModIntro.
          iDestruct (big_sepM2_empty_r with "Hkeys") as "->".
          iFrame.
          by do 2 rewrite big_sepM2_empty.
        - iIntros (mc Hsome_iff) "(Hkeys & Hinv_res)".
          destruct (Hsome_iff k) as (Hsome_if_1 & Hsome_if_2).
          rewrite lookup_insert in Hsome_if_1.
          assert (is_Some (Some V)) as His_some; first done.
          apply Hsome_if_1 in His_some.
          destruct (mc !! k) as [ov|] eqn:Hlookup'; last by inversion His_some.
          rewrite -(insert_delete _ _ _ Hlookup').
          do 2 rewrite big_sepM2_insert_delete.
          rewrite delete_idemp.
          iDestruct "Hkeys" as "(((_ & [%Vk (%Hdisj & Hfrag_k)]) & 
                    (([%Vk' (%Hsub_k & Hlookup_k_m & Hauth_k)] & _) & Hmem_k)) & Hkeys)".
          rewrite (delete_notin _ _ Hlookup).
          iDestruct (IH with "[$Hkeys $Hinv_res]") as ">(Hkeys & Hinv_res)".
          {
            intro key.
            split; intro Hsome.
            - destruct (decide (k = key)) as [-> | Hneq].
              + rewrite Hlookup in Hsome.
                by inversion Hsome.
              + rewrite lookup_delete_ne; last done.
                apply Hsome_iff.
                by rewrite lookup_insert_ne.
            - destruct (decide (k = key)) as [-> | Hneq].
              + rewrite lookup_delete in Hsome.
                by inversion Hsome.
              + rewrite lookup_delete_ne in Hsome; last done.
                apply Hsome_iff in Hsome.
                by rewrite lookup_insert_ne in Hsome.
          }
          iFrame "Hkeys".
          iDestruct (ownSetInclusion with "[$Hinv_res] [$Hauth_k] [$Hfrag_k]") as "(Hinv_res & Hauth_k & Hfrag_k & %Hsub'')".
          iModIntro.
          iFrame.
          iSplitL; last done.
          iExists Vk'.
          iFrame.
          iSplitR; first by iPureIntro.
          iExists (commit_event ov V).
          iFrame.
          iPureIntro.
          destruct Hdisj as [[v (Heq_some & Hin)]|Heq_none].
          + rewrite Heq_some.
            simpl.
            set_solver.
          + rewrite Heq_none.
            simpl.
            set_solver.
      }
      iMod ("Hinv_close" with "[Hinv_res]") as "_"; first done.
      iApply "Hhyp_later".
      iFrame.
      rewrite (big_sepM2_sepM _ (λ k vo, emp)%I _ _  Hsome_iff).
      iDestruct "Hmem_keys" as "(Hmem_keys & _)".
      iClear "Hinv Hrc_com Hrc_com'' Hemp_keys Hemp_keys'".
      clear Hsome_iff Hdom1 Hdom2.
      iStopProof.
      generalize dependent m.
      induction m' as [|k V m' Hlookup IH] using map_ind.
      + iIntros (m Hdom) "_".
        rewrite dom_empty_L dom_empty_iff_L in Hdom.
        rewrite Hdom. 
        by rewrite big_sepM_empty.
      + iIntros (m Hdom) "Hkeys".
        assert (k ∈ dom m) as Hin; first by set_solver.
        rewrite elem_of_dom in Hin.
        destruct (m !! k) as [V''|] eqn:Heq; last by destruct Hin.
        rewrite -(insert_delete _ _ _ Heq).
        rewrite -(insert_delete _ _ _ Heq) in Hdom.
        assert (dom (delete k m) = dom m') as Hdom'.
        {
          do 2 rewrite dom_insert_L in Hdom.
          rewrite -(delete_notin _ _ Hlookup) in Hdom.
          rewrite -(delete_notin _ _ Hlookup).
          set_solver.
        }
        rewrite big_sepM_insert; last done.
        iDestruct "Hkeys" as "(Hkey & Hkeys)".
        rewrite big_sepM_insert; last by apply lookup_delete.
        iAssert (([∗ map] k0↦y ∈ m', ∃ V' : Vals, ⌜y ⊆ V'⌝ ∗ 
                  ⌜(delete k m) !! k0 = Some V'⌝ ∗ OwnAuthSet γA k0 V' ∗ 
                  (∃ V''0 : Vals, ⌜V''0 ⊆ V'⌝ ∗ read_committed.specs.resources.OwnMemKey k0 V''0)))%I 
                with "[Hkeys]" as "Hkeys".
        {
          iApply (big_sepM_mono with "[$Hkeys]").
          iIntros (kx x H_lookup') "[%x' (Hsub_x & %H_lookup_x & Hauth & Hrest)]".
          iExists x'.
          iFrame.
          iPureIntro.
          destruct (decide (k = kx)) as [-> | Hneq].
          - apply elem_of_dom_2 in H_lookup'.
            rewrite -Hdom' in H_lookup'.
            rewrite dom_delete_L in H_lookup'.
            set_solver.
          - rewrite lookup_insert_ne in H_lookup_x; done.
        }
        iDestruct (IH _ Hdom' with "[$Hkeys]") as "Hkeys".
        iFrame. 
        iDestruct "Hkey" as "[%Vk (%Hsub_k & %Hlookup_k & Hauth_k & [%Vk' (%Hsub_k' & Hmem_k)])]".
        iExists Vk'.
        iFrame.
        rewrite lookup_insert in Hlookup_k.
        inversion Hlookup_k as [Heq'].
        iFrame.
        by iPureIntro.
    - iApply "Hhyp_later".
      iFrame.
      iDestruct (rewrite_maps_3 _ _ _ Hdom with "[$Hmem_keys] [$Hauth_keys]") as "Hmem_keys".
      iFrame.
  Qed.

End Implication.