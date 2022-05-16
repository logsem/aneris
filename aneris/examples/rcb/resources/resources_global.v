(** Realisation of the RCB_resources interface *)
From iris.algebra Require Import agree auth excl gmap.
From iris.proofmode Require Import tactics.
From aneris.algebra Require Import monotone.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang resources.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import events model_spec.
From aneris.examples.rcb.resources Require Import base.

Section Global_resources.
  Context `{!anerisG Mdl Σ, !RCB_params, !internal_RCBG Σ}.

  (** Definition of resources for global history and local history. *)

  Section Predicates.

    Context (γGown γGsnap : gname).

    (** Global history resources. *)

    Definition mk_hist (q : Qp) (h : gset global_event) : prodR fracR (agreeR (gsetO global_event)) :=
      (q, to_agree h).

    (* The user component needs to have 2/3 as the fraction so that it's exclusive. *)
    Definition own_global_user (h : gset global_event) : iProp Σ :=
      own γGown (mk_hist (2/3)%Qp h) ∗ own γGsnap (◯ h).

    (* The γGsnap fragment is needed so we can get a snapshot without a view shift
       (c.f. own_global_sys_snapshot). *)
    Definition own_global_sys (h : gset global_event) : iProp Σ :=
      own γGown (mk_hist (1/3)%Qp h) ∗ own γGsnap (● h) ∗ own γGsnap (◯ h).

    Definition own_global_snap (h : gset global_event) : iProp Σ :=
      own γGsnap (◯ h).

     (** Properties of global history resources. *)

    Lemma snap_lookup (G : gset global_event) h :
      own γGsnap (● G) ⊢
        own γGsnap (◯ h) -∗ ⌜h ⊆ G⌝ .
    Proof.
      iIntros "H1 H2".
      iDestruct (own_valid_2 with "H1 H2") as %[Hv1 Hv2]%auth_both_valid_discrete.
      by apply gset_included in Hv1; eauto with set_solver.
    Qed.

    Lemma own_global_snap_lookup G h :
      own_global_sys G ⊢ own_global_snap h -∗ ⌜h ⊆ G⌝.
    Proof.
      iIntros "[? [Hauth ?]] Hsnap".
      iApply (snap_lookup with "Hauth Hsnap").
    Qed.

    Lemma own_global_user_excl h h' :
      own_global_user h ⊢ own_global_user h' -∗ False.
    Proof.
      iIntros "[H1 _] [H2 _]".
      iDestruct (own_valid_2 with "H1 H2") as %Hvl.
      exfalso.
      eapply frac_pair_valid_implies_false; [done | by compute ].
    Qed.

    Instance own_global_snap_persistent h :
      Persistent (own_global_snap h).
    Proof. apply _. Qed.

    Lemma own_global_snap_union h h' :
      own_global_snap h ⊢
        own_global_snap h' -∗ own_global_snap (h ∪ h').
    Proof. by iIntros "H1 H2"; iCombine "H1" "H2" as "H". Qed.

    Lemma own_global_snap_weaken h h' :
      h ⊆ h' →
      own_global_snap h' ⊢ own_global_snap h.
    Proof.
      iIntros ((h'' & -> & _)%subseteq_disjoint_union_L) "H".
      rewrite /own_global_snap -gset_op auth_frag_op own_op.
      iDestruct "H" as "[$ _]".
    Qed.

    Lemma own_global_update h h': h ⊆ h' →
      own_global_user h ⊢
        own_global_sys h ==∗ own_global_user h' ∗ own_global_sys h'.
    Proof.
      iIntros (Hh) "[H11 #H12] H2".
      iDestruct "H2" as "[H21 [H22 _]]".
      iMod (own_update_2 _ _ _
                         (mk_hist (2/3)%Qp h' ⋅ mk_hist (1/3)%Qp h')
              with "H21 H11") as "[H21 H11]".
      { rewrite /mk_hist -pair_op frac_op.
        assert (Exclusive ((1 / 3 + 2 / 3)%Qp, to_agree h ⋅ to_agree h)) as Hexcl.
        { apply pair_exclusive_l.
          assert ((1 / 3 + 2 / 3 = 1)%Qp) as ->.
          { compute_done. }
          apply frac_full_exclusive. }
        apply cmra_update_exclusive.
        rewrite -pair_op pair_valid frac_valid frac_op; split.
        - simpl; auto with lia.
        - rewrite to_agree_op_valid; eauto.
      }
      iMod (own_update_2 _ _ _ ((● h') ⋅ (◯ h'))
              with "H22 H12") as "[Hauth #Hfrag]".
      { apply auth_update.
        apply (gset_local_update h h h'); done. }
      iModIntro.
      iFrame; iFrame "#".
    Qed.

    Lemma own_global_user_sys_agree h h' :
      own_global_user h ⊢ own_global_sys h' -∗ ⌜h = h'⌝.
    Proof.
      iIntros "[H11 H12] H2".
      iDestruct "H2" as "[H21 H22]".
      iDestruct (own_valid_2 with "H21 H11") as %Hv.
      iPureIntro.
      rewrite -pair_op frac_op in Hv.
      pose proof (iffLR (pair_valid _ _) Hv) as [_ Hr].
      apply (iffLR (to_agree_op_valid _ _)) in Hr.
      apply leibniz_equiv; done.
    Qed.

    Lemma own_global_user_snap h :
      own_global_user h ⊢ own_global_user h ∗ own_global_snap h.
    Proof. iIntros "[? #?]"; iFrame; iFrame "#". Qed.

    Lemma own_global_sys_snap h :
      own_global_sys h ⊢ own_global_sys h ∗ own_global_snap h.
    Proof.
      iDestruct 1 as "(Hexcl & Hauth & #Hsnap)".
      iSplitL; iFrame; iFrame "#".
    Qed.

    Lemma get_snap h :
      own γGsnap (● h) ⊢ |==> own γGsnap (● h) ∗ own_global_snap h.
    Proof.
      iIntros "H".
      iMod (own_update _ _ (● h ⋅ ◯ h) with "H") as "[$ $]"; last done.
      apply auth_update_alloc.
      apply gset_local_update; by set_solver.
    Qed.

  End Predicates.


  Section Alloc.

    Lemma alloc_global :
    True ⊢ |==> ∃ γGauth γGsnap,
               (own_global_sys γGauth γGsnap empty_ghst) ∗
               (own_global_user γGauth γGsnap empty_ghst).
    Proof.
      rewrite /empty_ghst.
      iIntros (_).
      iMod (own_alloc ((mk_hist (1/3)%Qp empty_ghst) ⋅ (mk_hist (2/3)%Qp empty_ghst))) as (γ1) "[Hsys Huser]".
      { rewrite -pair_op pair_valid.
        split.
        - apply frac_valid.
          rewrite frac_op; simpl; by auto with lia.
        - apply to_agree_op_valid; done. }
      iMod (own_alloc (● empty_ghst)) as (γ2) "H2";
        first by (apply auth_auth_valid).
      iMod (get_snap with "H2") as "[Hauth #Hsnap]".
      iModIntro. iExists γ1, γ2.
      iFrame; iFrame "#".
    Qed.

  End Alloc.

End Global_resources.
