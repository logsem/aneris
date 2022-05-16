(** Realisation of the DB_resources interface *)
From iris.algebra Require Import agree auth excl gmap.
From iris.proofmode Require Import tactics.
From aneris.algebra Require Import monotone.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang resources.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import events model_spec.
From aneris.examples.ccddb.resources Require Import base.

Section Global_memory.
  Context `{!anerisG Mdl Σ, !DB_params, !internal_DBG Σ}.

  (** Definition of resoureces for global memory and local history. *)

  Section Predicates.

    Context (γGauth γGsnap γGkeep : gname).

    (** Global memory resources. *)

    Definition make_global_mem (M : gmap Key (gset write_event)) :
      gmapUR Key (exclR (gsetO write_event)) := Excl <$> M.

    Definition own_mem_user (k : Key) (h : gset write_event) : iProp Σ :=
      own γGauth (◯ {[ k := Excl h]}) ∗ own γGsnap (◯ {[ k := h]}).

    Definition own_mem_sys (k : Key) (h : gset write_event) : iProp Σ :=
      ∃ M M', own γGauth (● (make_global_mem M)) ∗ own γGsnap (● M) ∗
                  own γGkeep (◯ (make_global_mem M')) ∗
                  own γGsnap (◯ {[ k := h]}) ∗
                  ⌜∀ j, k ≠ j → M !! j = M' !! j⌝ ∗ ⌜M !! k = Some h⌝ ∗
                  ⌜dom M' = DB_keys⌝.

    Definition own_mem_snapshot (k : Key) (h : gset write_event) : iProp Σ :=
      own γGsnap (◯ {[ k := h]}).

     (** Propreties of global memory resources. *)

    Lemma snapshot_lookup (M : gmap Key (gset write_event)) k h :
      own γGsnap (● M) ⊢
        own γGsnap (◯ {[k := h]}) -∗ ∃ h', ⌜h ⊆ h' ∧ M !! k = Some h'⌝.
    Proof.
      iIntros "H1 H2".
      iDestruct (own_valid_2 with "H1 H2") as %[Hv1 Hv2]%auth_both_valid_discrete.
      apply singleton_included_l in Hv1 as (h' & Hh'1%leibniz_equiv & Hh'2).
      revert Hh'2; rewrite Some_included_total gset_included; intros Hh'2.
      eauto.
    Qed.

    Lemma own_mem_user_excl k h h' :
      own_mem_user k h ⊢ own_mem_user k h' -∗ False.
    Proof.
      iIntros "[H1 _] [H2 _]".
      iDestruct (own_valid_2 with "H1 H2") as %Hvl.
      rewrite -auth_frag_op in Hvl; apply auth_frag_valid_1 in Hvl.
      specialize (Hvl k); revert Hvl.
        by rewrite /= lookup_op !lookup_singleton.
    Qed.

    Instance own_mem_snapshot_persistent k h :
      Persistent (own_mem_snapshot k h).
    Proof. apply _. Qed.

    Lemma own_mem_snapshot_union k h h' :
      own_mem_snapshot k h ⊢
        own_mem_snapshot k h' -∗ own_mem_snapshot k (h ∪ h').
    Proof. by iIntros "H1 H2"; iCombine "H1" "H2" as "H". Qed.

    Lemma own_mem_snapshot_weaken k h h' :
      h ⊆ h' →
      own_mem_snapshot k h' ⊢ own_mem_snapshot k h.
    Proof.
      iIntros ((h'' & -> & _)%subseteq_disjoint_union_L) "H".
      rewrite /own_mem_snapshot -gset_op -singleton_op.
      iDestruct "H" as "[$ _]".
    Qed.

    Lemma own_mem_update k h h': h ⊆ h' →
      own_mem_user k h ⊢
        own_mem_sys k h ==∗ own_mem_user k h' ∗ own_mem_sys k h'.
    Proof.
      iIntros (Hh) "[H11 H12] H2".
      iDestruct "H2" as (M M') "(H21 & H22 & Hkeep & _ & HMM' & Heq & Hdm)".
      iDestruct "Heq" as %Heq.
      iDestruct "HMM'" as %HMM'.
      iDestruct "Hdm" as %Hdm.
      iMod (own_update_2 _ _ _
                         (● make_global_mem (<[k := h']> M) ⋅ ◯ {[k := Excl h']})
              with "H21 H11") as "[H21 H11]".
      { rewrite /make_global_mem fmap_insert.
        rewrite -(insert_singleton (M := gmap _) k (Excl h) (Excl h')).
        apply auth_update.
        eapply (insert_local_update _ _ _ (Excl h) (Excl h)).
        - by rewrite lookup_fmap Heq.
        - by rewrite lookup_singleton.
        - by apply exclusive_local_update. }
      iMod (own_update_2 _ _ _ (● (<[k := h']> M) ⋅ ◯ {[k := h']})
              with "H22 H12") as "[H22 #H12]".
      { rewrite -(insert_singleton (M := gmap _) k h h').
        apply auth_update.
        eapply (insert_local_update _ _ _ h h); first done.
        - by rewrite lookup_singleton.
        - by apply gset_local_update. }
      iModIntro.
      iFrame; iFrame "#".
      iExists _, _; iFrame.
      repeat iSplit; iPureIntro; last done.
      - intros j Hjk; rewrite lookup_insert_ne //; by apply HMM'.
      - by rewrite lookup_insert.
    Qed.

    Lemma create_own_mem_sys_update M k h :
      M !! k = Some h →
      dom M = DB_keys →
      own γGauth (● (make_global_mem M)) -∗ own γGsnap (● M) -∗
          own γGkeep (● (make_global_mem M)) -∗
          own γGkeep (◯ (make_global_mem M)) ==∗
         (own_mem_sys k h) ∗
         (∀ h', own_mem_sys k h' ==∗
                  own γGauth (● (make_global_mem (<[k := h']>M))) ∗
                  own γGsnap (● <[k := h']>M) ∗
                  own γGkeep (● (make_global_mem (<[k := h']>M))) ∗
                  own γGkeep (◯ (make_global_mem (<[k := h']>M)))).
    Proof.
      iIntros (Hk Hdm) "Ha Hs Hk1 Hk2".
      iMod (own_update _ _ (● M ⋅ ◯ {[k := h]}) with "Hs") as "[Hs Hsnap]".
      { apply auth_update_alloc.
        rewrite -{2}(insert_id M k h); last done.
        rewrite -insert_empty.
        eapply @insert_alloc_local_update; [done|done|].
        by apply gset_local_update. }
      iModIntro.
      iSplitR "Hk1".
      { iExists M, M; iFrame; eauto. }
      iIntros (h').
      iDestruct 1 as (M1 M2) "(Ha&Hs&Hk2&Hsnap&HMM&Heq&Hdm)".
      iDestruct "HMM" as %HMM.
      iDestruct "Heq" as %Heq.
      iDestruct "Hdm" as %Hdm1.
      iDestruct (own_valid_2 with "Hk1 Hk2") as %[Hv1 Hv2]%auth_both_valid_discrete.
      revert Hv1; rewrite lookup_included; intros Hv1.
      assert (M2 = M) as ->.
      { apply map_eq; intros i.
        specialize (Hv1 i).
        rewrite /make_global_mem !lookup_fmap in Hv1.
        destruct (decide (i ∈ dom M2)) as [Hi|Hi].
        { revert Hi; rewrite elem_of_dom; intros [x Hx].
          rewrite Hx /= in Hv1.
          destruct (M !! i) as [y|];
            last by apply is_Some_included in Hv1 as [? ?]; eauto.
          by apply Excl_included, leibniz_equiv in Hv1 as ->. }
        pose proof Hi as ->%not_elem_of_dom.
        rewrite Hdm1 -Hdm in Hi.
        by apply not_elem_of_dom in Hi as ->. }
      assert (M1 = <[k := h']> M) as ->.
      { apply map_eq; intros i.
        destruct (decide (i = k)) as [->|].
        { by rewrite Heq lookup_insert. }
        by rewrite lookup_insert_ne //; apply HMM. }
      iMod (own_update_2
              _ _ _ (● make_global_mem (<[k := h']> M) ⋅
                     ◯ make_global_mem (<[k := h']> M)) with "Hk1 Hk2")
        as "[? ?]"; last by iFrame.
      apply auth_update.
      rewrite /make_global_mem fmap_insert.
      eapply insert_local_update;
        [by rewrite lookup_fmap Hk|by rewrite lookup_fmap Hk|].
      apply exclusive_local_update; done.
    Qed.

    Lemma create_own_mem_sys_acc M k h :
      M !! k = Some h →
      dom M = DB_keys →
      own γGauth (● (make_global_mem M)) -∗ own γGsnap (● M) -∗
          own γGkeep (● (make_global_mem M)) -∗
          own γGkeep (◯ (make_global_mem M)) ==∗
         own_mem_sys k h ∗
         (own_mem_sys k h ==∗
                  own γGauth (● (make_global_mem M)) ∗
                  own γGsnap (● M) ∗
                  own γGkeep (● (make_global_mem M)) ∗
                  own γGkeep (◯ (make_global_mem M))).
    Proof.
      iIntros (Hk HM).
      iPoseProof create_own_mem_sys_update as "H"; [done|done|].
      iIntros "H1 H2 H3 H4".
      iMod ("H" with "H1 H2 H3 H4") as "[H1 H2]".
      iModIntro.
      iFrame.
      iIntros "H1".
      iMod ("H2" with "H1") as "H2".
      by rewrite insert_id.
    Qed.

    Lemma own_mem_user_sys_agree k h h' :
      own_mem_user k h ⊢ own_mem_sys k h' -∗ ⌜h = h'⌝.
    Proof.
      iIntros "[H11 H12] H2".
      iDestruct "H2" as (M M') "(H21 & H22 & H23 & H24 & HMM & Heq & Hdm)".
      iDestruct "Heq" as %Heq.
      iDestruct (own_valid_2 with "H21 H11") as %[Hvl HMvl]%auth_both_valid_discrete.
      apply singleton_included_exclusive_l in Hvl; try typeclasses eauto; auto.
      apply leibniz_equiv in Hvl.
      rewrite /make_global_mem lookup_fmap Heq /= in Hvl.
        by simplify_eq.
    Qed.

    Lemma own_mem_user_snapshot k h :
      own_mem_user k h ⊢ own_mem_user k h ∗ own_mem_snapshot k h.
    Proof. iIntros "[? #?]"; iFrame; iFrame "#". Qed.

    Lemma own_mem_sys_snapshot k h :
      own_mem_sys k h ⊢ own_mem_sys k h ∗ own_mem_snapshot k h.
    Proof.
      iDestruct 1 as (M M') "(H1 & H2 & H3 & #H4 & HMM & Heq & Hdm)".
      iSplitL; last by iFrame "#".
      by iExists _, _; iFrame.
    Qed.

    Lemma get_snapshot M k h :
      M !! k = Some h →
      own γGsnap (● M) ⊢ |==> own γGsnap (● M) ∗ own_mem_snapshot k h.
    Proof.
      iIntros (?) "H".
      iMod (own_update _ _ (● M ⋅ ◯ {[k := h]}) with "H") as "[$ $]"; last done.
      apply auth_update_alloc.
      rewrite -{2}(insert_id M k h) // -insert_empty.
      eapply (insert_alloc_local_update _ _ _ h h); eauto.
      by apply gset_local_update.
    Qed.

  End Predicates.


  Section Alloc.


    Lemma alloc_gmem :
    True ⊢ |==> ∃ γGauth γGsnap γGkeep,
               own γGauth (● (make_global_mem empty_gmem)) ∗
               own γGsnap (● empty_gmem) ∗
               own γGkeep (● (make_global_mem empty_gmem)) ∗
               own γGkeep (◯ (make_global_mem empty_gmem)) ∗
               [∗ set] k ∈ DB_keys, own_mem_user γGauth γGsnap k ∅.
    Proof.
      rewrite /empty_gmem.
      pattern DB_keys;
        match goal with
          |- ?H DB_keys => eapply (set_ind H); simpl
        end.
      { solve_proper. }
      - rewrite !gset_to_gmap_empty.
        iIntros (_).
        iMod (own_alloc (● (make_global_mem ∅))) as (γ1) "H1";
          first by apply auth_auth_valid.
        iMod (own_alloc (● (∅ : gmapUR Key (gsetUR write_event)))) as (γ2) "H2";
          first by apply auth_auth_valid.
        iMod (own_alloc (● (make_global_mem ∅) ⋅ ◯ (make_global_mem ∅))) as
            (γ3) "[H31 H32]"; first by apply auth_both_valid_discrete.
        iExists γ1, γ2, γ3; iFrame.
        iModIntro.
          by rewrite big_sepS_empty.
      - iIntros (k K HkK IHK _).
        iMod (IHK with "[]") as (γ1 γ2 γ3) "(IH1 & IH2 & IH31 & IH32 & IH4)";
          first done; simpl.
        iMod (own_update _ _ (● make_global_mem (gset_to_gmap ∅ ({[k]} ∪ K))
                                ⋅ ◯ {[k := Excl ∅]}) with "IH1") as "[IH1 H1]".
        { rewrite gset_to_gmap_union_singleton /make_global_mem fmap_insert.
          rewrite -insert_empty.
          apply auth_update_alloc.
          apply alloc_singleton_local_update; last done.
          rewrite lookup_fmap.
          rewrite (proj1 (not_elem_of_dom (D := gset Key) (gset_to_gmap ∅ K) _));
            last rewrite dom_gset_to_gmap; done. }
        iMod (own_update_2 _ _ _
                           ((● make_global_mem (gset_to_gmap ∅ ({[k]} ∪ K)))
                              ⋅ (◯ make_global_mem (gset_to_gmap ∅ ({[k]} ∪ K))))
                with "IH31 IH32") as "[IH31 IH32]".
        { rewrite gset_to_gmap_union_singleton /make_global_mem fmap_insert.
          apply auth_update.
          apply alloc_local_update; last done.
          rewrite lookup_fmap lookup_gset_to_gmap.
            by rewrite option_guard_False. }
        iMod (own_update _ _ (● (gset_to_gmap ∅ ({[k]} ∪ K))
                                ⋅ ◯ {[k := ∅]}) with "IH2") as "[IH2 H2]".
        { rewrite gset_to_gmap_union_singleton.
          rewrite -insert_empty.
          apply auth_update_alloc.
          apply alloc_singleton_local_update; last done.
          apply (not_elem_of_dom (D := (gset Key))).
            by rewrite dom_gset_to_gmap. }
        iModIntro.
        iExists γ1, γ2, γ3.
        rewrite big_sepS_union; last set_solver.
        rewrite big_sepS_singleton; iFrame.
    Qed.

  End Alloc.

End Global_memory.
