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
From aneris.examples.transactional_consistency.snapshot_isolation.specs
  Require Import aux_defs events time resources specs.
From aneris.examples.transactional_consistency.read_committed.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params aux_defs.

Section Implication.
  Context `{!anerisG Mdl Σ, !KVSG Σ, !User_params, !KVS_transaction_api}.

  Global Program Instance RC_resources_instance `(SI : !SI_resources Mdl Σ) : RC_resources Mdl Σ :=
    {|
      GlobalInv := SI.(snapshot_isolation.specs.resources.GlobalInv);
      OwnMemKey k V := (∃ (h : Hist), ⌜∀ (v : val), v ∈ h ↔ v ∈ V⌝ ∗ SI.(snapshot_isolation.specs.resources.OwnMemKey) k h)%I;
      OwnLocalKey k c vo :=  ((∃ wo h, ⌜vo = None⌝ ∗ ⌜(∃ v, wo = Some v ∧ v ∈ h) ∨ wo = None⌝ ∗
                              SI.(snapshot_isolation.specs.resources.Seen) k h ∗
                              SI.(snapshot_isolation.specs.resources.KeyUpdStatus) c k false ∗
                              SI.(snapshot_isolation.specs.resources.OwnLocalKey) k c wo) ∨ 
                             (⌜vo ≠ None⌝ ∗
                              SI.(snapshot_isolation.specs.resources.KeyUpdStatus) c k true ∗
                              SI.(snapshot_isolation.specs.resources.OwnLocalKey) k c vo))%I;
      ConnectionState c sa st := ((⌜st = CanStart⌝ ∗ 
                                   SI.(snapshot_isolation.specs.resources.ConnectionState) c sa (snapshot_isolation.specs.aux_defs.CanStart)) ∨  
                                  (∃ (m : gmap Key Hist), ⌜st = Active (dom m)⌝ ∗ 
                                   SI.(snapshot_isolation.specs.resources.ConnectionState) c sa (snapshot_isolation.specs.aux_defs.Active m)))%I;
      IsConnected c sa := SI.(snapshot_isolation.specs.resources.IsConnected) c sa;
      KVS_rc := SI.(snapshot_isolation.specs.resources.KVS_si);
      KVS_Init := SI.(snapshot_isolation.specs.resources.KVS_Init);
      KVS_ClientCanConnect sa := SI.(snapshot_isolation.specs.resources.KVS_ClientCanConnect) sa;
      Seen k V := (∃ h, ⌜∀ v, v ∈ V → v ∈ h⌝ ∗ SI.(snapshot_isolation.specs.resources.Seen) k h)%I;
    |}.
  Next Obligation.
    iIntros (SI k cst v) "[[%V [%h (%Hfalse & _)]] | (%Hneq & Hupd & Hkey)]"; first done. 
    iDestruct (SI.(snapshot_isolation.specs.resources.OwnLocalKey_serializable) with "Hkey") as "(Hkey & Hser)".
    iFrame.
    iRight.
    iFrame.
    by iPureIntro.
  Qed.
  Next Obligation.
    iIntros (SI E k V V' Hsub) "#Hinv ([%h (%Himp & #Hseen)] & [%h' (%Himp' & Hkey)])".
    iMod (SI.(snapshot_isolation.specs.resources.Seen_valid) with "[$Hinv][$Hkey $Hseen]") as "(Hkey & %Hsub')"; first done.
    iModIntro.
    iSplitL.
    - iExists h'.
      iFrame.
      by iPureIntro.
    - iPureIntro.
      apply elem_of_subseteq.
      intros v Hin.
      apply Himp in Hin.
      apply (elem_of_prefix _ _ _ Hin) in Hsub'.
      by apply Himp' in Hsub'.
  Qed.
  Next Obligation.
    iIntros (SI E k V Hsub) "#Hinv [%h (%Himp & Hkey)]".
    iMod (SI.(snapshot_isolation.specs.resources.Seen_creation) with "[$Hinv][$Hkey]") as "(Hkey & #Hseen)"; first done.
    iModIntro.
    iSplitL.
    - iExists h.
      iFrame.
      by iPureIntro.
    - iExists h.
      iFrame "#".
      iPureIntro.
      intro v.
      by destruct (Himp v) as [_ Hgoal].
  Qed.

  Theorem implication_si_rc : 
    SI_init → RC_init.
  Proof.
    intro SI_init.
    destruct SI_init.
    split.
    iIntros (E cli Hsub).
    iMod (SI_init_module E cli Hsub) as 
      "[%Hres (Hsi_keys & Hsi_kvs_init & #Hsi_inv & Hsi_conn & #Hsi_init_kvs
       & #Hsi_init_cli & #Hsi_read & #Hsi_write & #Hsi_start & #Hsi_com)]".
    iModIntro. 
    iExists (RC_resources_instance Hres).
    simpl.
    iSplitL "Hsi_keys".
    {
      iApply (big_sepS_mono with "[$Hsi_keys]").
      iIntros (k Hk_in) "Hk_mem".
      iExists [].
      iFrame.
      iPureIntro.
      set_solver.
    }
    iSplitL "Hsi_kvs_init"; first done.
    iSplitL "Hsi_inv"; first iFrame "#∗".
    iSplitL "Hsi_conn"; first done.
    iSplitL; first done.
    iSplitL.
    {
      unfold init_client_proxy_spec.
      iIntros (sa) "!# %Φ Hpre HΦ".
      iApply ("Hsi_init_cli" with "[Hpre]"); first by iFrame.
      iNext.
      iIntros (state) "(Hcstate & Hconn)".
      iApply "HΦ".
      iFrame.
      simpl.
      iLeft.
      iFrame.
      by iPureIntro.
    }
    iSplitL.
    { 
      iClear "Hsi_com Hsi_start Hsi_write Hsi_init_cli Hsi_init_kvs". 
      unfold read_spec.
      iModIntro.
      iIntros (c sa E' k) "%Hsub' Hk_in Hconn".
      iDestruct ("Hsi_read" $! c sa E' k Hsub' with "Hk_in Hconn") as "Hsi_read'".
      iIntros (Φ).
      iDestruct ("Hsi_read'" $! Φ) as "#Hsi_read''".
      iModIntro.
      iIntros "Hhyp".
      iApply "Hsi_read''".
      iMod "Hhyp" as "[%vo [%V ((Hloc_key & Hkey) & Hhyp_later)]]".
      simpl.
      iDestruct "Hkey" as "[%h (%Hbi & Hkey)]".
      iDestruct "Hloc_key" as "[[%wo [%h' (%Heq & %Hdisj & #Hseen & Hupd & Hloc_key)]] | 
                                         (%Hneq & Hupd & Hloc_key)]".
      - iMod (snapshot_isolation.specs.resources.Seen_valid with "[$Hsi_inv][$Hkey $Hseen]") as "(Hkey & %Hsub_seen)"; first done.
        iModIntro.
        iExists wo. 
        iSplitL "Hloc_key"; first by iFrame.
        iNext.
        iIntros "Hloc_key".
        iApply "Hhyp_later".
        iSplitL "Hupd Hloc_key".
        + iLeft. 
          iExists wo, h'.
          iSplitR; first by iPureIntro.
          iSplitR; first by iPureIntro.
          iFrame "#∗".
        + iSplitL.
          * iExists h.
            iFrame.
            by iPureIntro.
          * iLeft.
            iSplitL; first by  iPureIntro.
            iPureIntro.
            destruct Hdisj as [[v (Heq' & Hin)] | Heq']; last by right.
            left.
            exists v.
            split; first done.
            apply Hbi.
            by apply (elem_of_prefix _ _ _ Hin) in Hsub_seen.
      - iModIntro.
        iExists vo.
        iSplitL "Hloc_key"; first by iFrame.
        iNext.
        iIntros "Hloc_key".
        iApply "Hhyp_later".
        iSplitL "Hupd Hloc_key".
        + iRight.
          iFrame.
          by iPureIntro.
        + iSplitL.
          * iExists h.
            iFrame.
            by iPureIntro.
          * iRight.
            iSplitL; by iPureIntro.
    }
    iSplitL "Hsi_write".
    {
      iClear "Hsi_com Hsi_start Hsi_read Hsi_init_cli Hsi_init_kvs". 
      unfold write_spec.
      iModIntro.
      iIntros (c sa E' k v) "%Hsub' Hk_in Hconn".
      iDestruct ("Hsi_write" $! c sa E' k v Hsub' with "Hk_in Hconn") as "Hsi_write'".
      iIntros (Φ).
      iDestruct ("Hsi_write'" $! Φ) as "#Hsi_write''".
      iModIntro.
      iIntros "Hhyp".
      iApply "Hsi_write''".
      simpl.
      iMod "Hhyp" as "[%vo ([[%wo [%h (%Heq & %Hdisj & #Hseen & Hupd & Hloc_key)]] | (%Hneq & Hupd & Hloc_key)] & Hhyp_later)]".
      - iModIntro.
        iExists wo, false.
        iSplitL "Hloc_key Hupd"; first by iFrame.
        iNext.
        iIntros "(Hloc_key & Hupd)".
        iApply "Hhyp_later".
        iRight.
        iFrame.
        by iPureIntro.
      - iModIntro.
        iExists vo, true.
        iSplitL "Hloc_key Hupd"; first by iFrame.
        iNext.
        iIntros "(Hloc_key & Hupd)".
        iApply "Hhyp_later".
        iRight.
        iFrame.
        by iPureIntro.
    }
    Admitted. 
(* 
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
  Admitted.  *)

End Implication.