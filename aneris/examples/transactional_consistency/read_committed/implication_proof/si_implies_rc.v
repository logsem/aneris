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

  Lemma rewrite_maps_1 `{SI : !SI_resources Mdl Σ} (m : gmap Key Vals) :
    ([∗ map] k↦V ∈ m, ∃ h : Hist, ⌜∀ v : val, v ∈ h ↔ v ∈ V⌝ ∗ 
      snapshot_isolation.specs.resources.OwnMemKey k h) -∗
    (∃ (m' : gmap Key Hist), ⌜dom m = dom m'⌝ ∗ 
      ⌜∀ (k : Key) (h : Hist) (V : Vals), (m' !! k = Some h ∧ m !! k = Some V) → (∀ (v : val), v ∈ h ↔ v ∈ V)⌝ ∗
      ([∗ map] k↦h ∈ m', snapshot_isolation.specs.resources.OwnMemKey k h)).
  Proof.
    iIntros "Hkeys".
    iInduction m as [|k V m H_lookup] "IH" using map_ind.
    - iExists ∅.
      iSplitL.
      + iPureIntro.
        set_solver.
      + iSplitL; last done.
        iPureIntro.
        set_solver.
    - rewrite big_sepM_insert; last done.
      iDestruct "Hkeys" as "([%h (%Hbi & Hkey)] & Hkeys)".
      iDestruct ("IH" with "[$Hkeys]") as "[%m' (%Hdom & %Himp & Hkeys)]".
      iExists (<[k:=h]> m').
      iSplitR.
      + iPureIntro.
        set_solver.
      + iSplitR.
        * iPureIntro.
          intros k' h' V' (Heq1 & Heq2) v.
          destruct (decide (k = k')) as [-> | Hneq].
          -- rewrite lookup_insert in Heq1.
             rewrite lookup_insert in Heq2.
             inversion Heq1 as [Heq1'].
             inversion Heq2 as [Heq2'].
             rewrite -Heq1' -Heq2'.
             apply Hbi.
          -- rewrite lookup_insert_ne in Heq1; last done.
             rewrite lookup_insert_ne in Heq2; last done.
             eapply Himp.
             split; done.
        * rewrite big_sepM_insert; first iFrame.
          rewrite -not_elem_of_dom in H_lookup.
          rewrite Hdom in H_lookup.
          by rewrite not_elem_of_dom in H_lookup.
  Qed.

  Lemma rewrite_maps_2 `{SI : !SI_resources Mdl Σ} (mc : gmap Key (option val)) (c : val) :
    ([∗ map] k↦vo ∈ mc, 
      (∃ (wo : option val) (h : Hist), ⌜vo = None⌝ ∗ ⌜(∃ v : val, wo = Some v ∧ v ∈ h) ∨ wo = None⌝ ∗ 
      snapshot_isolation.specs.resources.Seen k h ∗ KeyUpdStatus c k false ∗ 
      snapshot_isolation.specs.resources.OwnLocalKey k c wo) ∨ 
      ⌜vo ≠ None⌝ ∗ KeyUpdStatus c k true ∗ 
      snapshot_isolation.specs.resources.OwnLocalKey k c vo) -∗
    (∃ (mc' : gmap Key (option val * bool)), ⌜dom mc = dom mc'⌝ ∗
      ⌜∀ (k : Key) (v : val), (mc' !! k = Some (Some v, true) ↔ mc !! k = Some (Some v))⌝ ∗
      ([∗ map] k↦p ∈ mc', snapshot_isolation.specs.resources.OwnLocalKey k c p.1 ∗ KeyUpdStatus c k p.2)).
  Proof.
    iIntros "Hkeys".
    iInduction mc as [|k ov mc H_lookup] "IH" using map_ind.
    - iExists ∅.
      iSplitL.
      + iPureIntro.
        set_solver.
      + iSplitL; last done.
        iPureIntro.
        set_solver.
    - rewrite big_sepM_insert; last done.
      iDestruct "Hkeys" as "(Hkey & Hkeys)".
      iDestruct ("IH" with "[$Hkeys]") as "[%mc'_ (%Hdom & %Himp & Hkeys)]".
      iDestruct "Hkey" as "[[%wo [%h (%Heq & %Hdisj & _ & Hupd & Hloc_key)]] | (%Heq & Hupd & Hloc_key)]".
      + iExists (<[k:= (wo, false)]> mc'_).
        rewrite big_sepM_insert; last first.
        {
          rewrite -not_elem_of_dom in H_lookup.
          rewrite Hdom in H_lookup.
          by rewrite not_elem_of_dom in H_lookup.
        }
        iFrame.
        iSplitR.
        * iPureIntro.
          set_solver.
        * iPureIntro.
          intros k' v'.
          destruct (decide (k = k')) as [-> | Hneq].
          -- do 2 rewrite lookup_insert.
             split; first done.
             intros Hfalse.
             inversion Hfalse as [Hfalse'].
             by rewrite Heq in Hfalse'.
          -- rewrite lookup_insert_ne; last done.
             rewrite lookup_insert_ne; last done.
             apply Himp.
      + iExists (<[k:= (ov, true)]> mc'_).
        rewrite big_sepM_insert; last first.
        {
          rewrite -not_elem_of_dom in H_lookup.
          rewrite Hdom in H_lookup.
          by rewrite not_elem_of_dom in H_lookup.
        }
        iFrame.
        iSplitR.
        * iPureIntro.
          set_solver.
        * iPureIntro.
          intros k' v'.
          destruct (decide (k = k')) as [-> | Hneq].
          -- do 2 rewrite lookup_insert.
             split; intro Hhyp; by inversion Hhyp.
          -- rewrite lookup_insert_ne; last done.
             rewrite lookup_insert_ne; last done.
             apply Himp.
  Qed.

  Lemma rewrite_maps_3 `{SI : !SI_resources Mdl Σ} (m : gmap Key Vals) (m' : gmap Key Hist) :
    dom m = dom m' → 
    (∀ (k : Key) (h : Hist) (V : Vals), m' !! k = Some h ∧ m !! k = Some V → ∀ v : val, v ∈ h ↔ v ∈ V) →
    ([∗ map] k↦h ∈ m', snapshot_isolation.specs.resources.OwnMemKey k h) -∗
    ([∗ map] k↦V ∈ m, ∃ h : Hist, ⌜∀ v : val, v ∈ h ↔ v ∈ V⌝ ∗ snapshot_isolation.specs.resources.OwnMemKey k h).
  Proof.
    generalize dependent m.
    induction m' as [|k h m' H_lookup IH] using map_ind.
    * iIntros (m  Hdom _) "_".
      rewrite dom_empty_L in Hdom.
      rewrite dom_empty_iff_L in Hdom.
      by rewrite Hdom.
    * iIntros (m  Hdom Himp) "Hmem_keys".
      rewrite big_sepM_insert; last done.
      iDestruct "Hmem_keys" as "(Hmem_key & Hmem_keys)".
      assert (k ∈ dom m) as Hin; first by set_solver.
      rewrite elem_of_dom in Hin.
      destruct (m !! k) as [V|] eqn:Heq; last by destruct Hin.
      rewrite -(insert_delete _ _ _ Heq).
      rewrite -(insert_delete _ _ _ Heq) in Hdom.
      assert (dom (delete k m) = dom m') as Hdom'.
      {
        do 2 rewrite dom_insert_L in Hdom.
        rewrite -(delete_notin _ _ H_lookup) in Hdom.
        rewrite -(delete_notin _ _ H_lookup).
        set_solver.
      }
      rewrite big_sepM_insert; last by apply lookup_delete.
      iSplitL "Hmem_key".
      -- iExists h.
          iFrame.
          iPureIntro.
          apply (Himp k h V).
          split; last done.
          by rewrite lookup_insert.
      -- iDestruct (IH _ Hdom' with "[$Hmem_keys]") as "Hmem_keys'"; last by iFrame.
          intros k' h' V' (Heq1 & Heq2).
          apply (Himp k' h' V').
          destruct (decide (k = k')) as [-> | Hneq].
          ++ rewrite lookup_delete in Heq2.
            by inversion Heq2.
          ++ rewrite lookup_insert_ne; last done.
            split; first done.
            rewrite lookup_delete_ne in Heq2; done.
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
    iSplitL.
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
    iSplitL.
    {
      iClear "Hsi_com Hsi_read Hsi_write Hsi_init_cli Hsi_init_kvs". 
      unfold start_spec.
      iModIntro.
      iIntros (c sa E') "%Hsub' Hconn".
      iDestruct ("Hsi_start" $! c sa E' Hsub' with "Hconn") as "Hsi_start'".
      iIntros (Φ).
      iDestruct ("Hsi_start'" $! Φ) as "#Hsi_start''".
      iModIntro.
      iIntros "Hhyp".
      iApply "Hsi_start''".
      iMod "Hhyp" as "[%m ((Hstate & Hmem_keys) & Hhyp_later)]".
      iModIntro.
      simpl.
      iDestruct "Hstate" as "[(_ & Hstate) | [%_ (%Hfalse & _)]]"; last done.
      iDestruct (rewrite_maps_1 with "[$Hmem_keys]") as "[%m' (%Hdom & %Himp & Hmem_keys)]".
      iExists m'.
      iSplitL "Hstate Hmem_keys"; first iFrame.
      iNext. 
      iIntros "(Hstate & Hmem_keys & Hloc_keys & Hseen_keys)".
      iApply "Hhyp_later".
      iSplitL "Hstate".
      - iRight.
        iExists m'.
        iFrame.
        rewrite Hdom.
        by iPureIntro.
      - iSplitL "Hmem_keys".
        + iDestruct (rewrite_maps_3 _ _ Hdom Himp with "[$Hmem_keys]") as "Hmem_keys".
          iFrame.
        + iDestruct (big_sepM_sep_2 with "[$Hloc_keys] [$Hseen_keys]") as "Hkeys".
          rewrite big_sepM_dom.
          rewrite Hdom.
          rewrite -big_sepM_dom.
          iApply (big_sepM_mono with "[$Hkeys]").
          iIntros (k h Hlookup) "((Hloc & Hupd) & Hseen)".
          iLeft.
          iExists (last h), h.
          iFrame.
          iSplitR; first by iPureIntro.
          iPureIntro.
          destruct (last h) eqn:Heq_last; last by right.
          left.
          exists v.
          split; first done.
          by apply last_Some_elem_of.
    }
    iClear "Hsi_read Hsi_start Hsi_write Hsi_init_cli Hsi_init_kvs". 
    unfold commit_spec.
    iModIntro.
    iIntros (c sa E') "%Hsub' Hconn".
    iDestruct ("Hsi_com" $! c sa E' Hsub' with "Hconn") as "Hsi_com'".
    iIntros (Φ).
    iDestruct ("Hsi_com'" $! Φ) as "#Hsi_com''".
    iModIntro.
    iIntros "Hhyp".
    iApply "Hsi_com''".
    iMod "Hhyp" as "[%s [%mc [%m ((Hstate & %Hdom1 & %Hdom2 & Hloc_keys & Hmem_keys) & Hhyp_later)]]]".
    iModIntro.
    iDestruct "Hstate" as "[(%Hfalse & _)|[%ms (%Heq_active & Hstate)]]"; first done.
    iDestruct (rewrite_maps_1 with "[$Hmem_keys]") as "[%m' (%Hdom & %Himp & Hmem_keys)]".
    iDestruct (rewrite_maps_2 with "[$Hloc_keys]") as "[%mc' (%Hdom_mc & %Hbi_mc & Hloc_keys)]".
    iExists m', ms, mc'.
    iFrame.
    iSplitR.
    {
      iPureIntro.
      inversion Heq_active as [Heq].
      split; set_solver.
    }
    iNext.
    iIntros (b) "(Hstate & Hdisj)".
    iApply "Hhyp_later".
    iSplitL "Hstate".
    {
      simpl.
      iLeft.
      iSplitR; first by iPureIntro.
      iFrame.
    }
    iDestruct "Hdisj" as "[(-> & (_ & Hkeys)) | (-> & _ & Hkeys)]".
    - iLeft.
      iSplitR; first by iPureIntro.
      rewrite big_sepM2_sep.
      iDestruct "Hkeys" as "(Hkeys & _)".
      unfold commit_event.
      unfold aux_defs.commit_event.
      simpl.
      admit.
    - iRight.
      iSplitR; first by iPureIntro.
      simpl.
      rewrite big_sepM_sep.
      iDestruct "Hkeys" as "(Hkeys & _)".
      iDestruct (rewrite_maps_3 _ _ Hdom Himp with "[$Hkeys]") as "Hkeys".
      iFrame.
  Admitted.

End Implication.