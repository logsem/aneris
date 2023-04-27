(** Realisation of the DB_resources interface *)
From iris.algebra Require Import agree auth excl gmap.
From aneris.algebra Require Import monotone.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang resources.
From aneris.aneris_lang.lib Require Import vector_clock_proof lock_proof.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import events model_spec.
From aneris.examples.ccddb.resources Require Import
     base resources_gmem resources_lhst.

Section Global_invariant.

  Context `{!anerisG Mdl Σ, !DB_params, !DB_global_state_valid, !internal_DBG Σ}.
  Context (γGauth γGsnap γGkeep : gname) (γLs : list (gname * gname)).

    Definition Global_Inv :=
      inv DB_InvName
          (∃ M Ss,
              ⌜length γLs = length DB_addresses⌝ ∗
              ⌜DB_keys = dom M⌝ ∗
              own γGauth (● (make_global_mem M)) ∗
              own γGsnap (● M) ∗
              own γGkeep (● (make_global_mem M)) ∗
              own γGkeep (◯ (make_global_mem M)) ∗
              ([∗ list] γs; T ∈ γLs; Ss, local_history_Global_inv γs T)
              ∗ ⌜DBM_GstValid {| Gst_mem := M; Gst_hst := Ss|}⌝
          ).

    Lemma local_history_seen_union i s s' E :
      nclose DB_InvName ⊆ E →
      Global_Inv ⊢ local_history_seen γLs i s -∗
                 local_history_seen γLs i s' ={E}=∗
                 local_history_seen γLs i (s ∪ s').
    Proof.
      iIntros (?) "#Hinv".
      iDestruct 1 as (γs Hγs) "[H11 H12]".
      iDestruct 1 as (γs' Hγs') "[H21 H22]".
      simplify_eq.
      iInv DB_InvName as (M Ss) "(?&?&?&?&?&?&>HL&?)" "Hcl".
      iDestruct (big_sepL2_length with "HL") as %Hlen.
      destruct (lookup_lt_is_Some_2 Ss i) as [S HS].
      { rewrite -Hlen; apply lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_lookup_acc _ _ _ i with "HL") as "[[HS1 HS2] Hrest]";
        eauto.
      iDestruct (own_valid_2 with "HS1 H11") as %[Hs ?]%auth_both_valid_discrete.
      revert Hs; rewrite principal_included; intros Hs.
      iDestruct (own_valid_2 with "HS1 H21") as %[Hs' ?]%auth_both_valid_discrete.
      revert Hs'; rewrite principal_included; intros Hs'.
      iMod (own_update _ _ (● PrinSeen S ⋅ ◯ PrinSeen (s ∪ s')) with "HS1") as
          "[HS1 H11']".
      { apply auth_update_alloc.
        apply monotone_local_update_get_frag.
        by apply seen_relation_union. }
      iSpecialize ("Hrest" with "[$HS1 $HS2]").
      iMod ("Hcl" with "[-H12 H22 H11']") as "_".
      { iExists _, _; iFrame; eauto. }
      iCombine "H12" "H22" as "H2".
      iModIntro.
        by iExists _; iFrame.
    Qed.

    Lemma own_mem_snapshot_ext k k' h h' E :
      nclose DB_InvName ⊆ E →
      Global_Inv ⊢ own_mem_snapshot γGsnap k h -∗
      own_mem_snapshot γGsnap k' h' ={E}=∗
        ⌜∀ a a', a ∈ h → a' ∈ h' → we_time a = we_time a' → a = a'⌝.
    Proof.
      iIntros (?) "#Hinv Hh Hh'".
      rewrite /Global_Inv /own_mem_snapshot.
      iInv DB_InvName as (M Ss) "(?&?&?&>HM&?&?&?&>Hvl)" "Hcl".
      iDestruct (snapshot_lookup with "HM Hh") as (h1) "#Hh1".
      iDestruct "Hh1" as %[Hh11 Hh12].
      iDestruct (snapshot_lookup with "HM Hh'") as (h2) "#Hh2".
      iDestruct "Hh2" as %[Hh21 Hh22].
      iDestruct "Hvl" as %Hvl.
      iMod ("Hcl" with "[-]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iPureIntro.
      intros.
      eapply (DBM_GstValid_gmem_ext _ k k'); eauto.
    Qed.

    Lemma local_history_seen_ext n n' s s' E :
      nclose DB_InvName ⊆ E →
      Global_Inv ⊢
      local_history_seen γLs n s -∗ local_history_seen γLs n' s' ={E}=∗
      ⌜∀ e e', e ∈ s → e' ∈ s' → ae_time e = ae_time e' →
               e.(ae_key) = e'.(ae_key) ∧ e.(ae_val) = e'.(ae_val)⌝.
    Proof.
      iIntros (?) "#Hinv Hseen Hseen'".
      rewrite /Global_Inv /local_history_seen.
      iDestruct "Hseen" as (γs Hγs) "[Hs1 Hs2]".
      iDestruct "Hseen'" as (γs' Hγs') "[Hs1' Hs2']".
      iInv DB_InvName as (M Ss) "(?&?&?&?&?&?&>HL&>Hvl)" "Hcl".
      iDestruct "Hvl" as %Hvl.
      iDestruct (seen_lookup with "HL Hs1") as (s1) "#H1"; eauto.
      iDestruct (seen_lookup with "HL Hs1'") as (s1') "#H1'"; eauto.
      iDestruct "H1" as %[[? ?] ?].
      iDestruct "H1'" as %[[? ?] ?].
      iMod ("Hcl" with "[-]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iPureIntro.
      intros.
      eapply (DBM_GstValid_lhst_ext _ n n'); eauto.
    Qed.

    Lemma local_history_seen_strong_ext n s s' E :
      nclose DB_InvName ⊆ E →
      Global_Inv ⊢ local_history_seen γLs n s -∗
                 local_history_seen γLs n s' ={E}=∗
      ⌜∀ e e', e ∈ s → e' ∈ s' → ae_time e = ae_time e' → e = e'⌝.
    Proof.
      iIntros (?) "#Hinv Hseen Hseen'".
      iMod (local_history_seen_union with "[] Hseen Hseen'") as "Hseen"; eauto.
      rewrite /Global_Inv /local_history_seen.
      iDestruct "Hseen" as (γs Hγs) "#[Hs1 Hs2]".
      iInv DB_InvName as (M Ss) "(?&?&?&?&?&?&>HL&>Hvl)" "Hcl".
      iDestruct "Hvl" as %Hvl.
      iDestruct (seen_lookup with "HL Hs1") as (s1) "#H1"; eauto.
      iDestruct "H1" as %[[? ?] ?].
      iMod ("Hcl" with "[-]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iPureIntro.
      intros.
      eapply (DBM_GstValid_lhst_strong_ext _ n); eauto.
      - set_solver.
      - set_solver.
    Qed.

    Lemma local_history_seen_provenance n s e E :
      nclose DB_InvName ⊆ E → e ∈ s →
      Global_Inv ⊢ local_history_seen γLs n s ={E}=∗
       ∃ h, own_mem_snapshot γGsnap e.(ae_key) h ∧ ⌜erase e ∈ h⌝.
    Proof.
      iIntros (? ?) "#Hinv Hs".
      rewrite /Global_Inv /local_history_seen.
      iDestruct "Hs" as (γs Hγs) "[Hs1 Hs2]".
      iInv DB_InvName as (M Ss) "(?&?&?&>HM&?&?&>HL&>Hvl)" "Hcl".
      iDestruct "Hvl" as %Hvl.
      iDestruct (seen_lookup with "HL Hs1") as (s1) "#H1"; eauto.
      iDestruct "H1" as %[[? ?] ?].
      destruct
        (DBM_GstValid_ae_provenance {| Gst_mem := M; Gst_hst := Ss|} n s1 e)
        as (h & Hkh & Heh);
        simpl in *; auto.
      iMod (get_snapshot _ _ (ae_key e) h with "HM")
        as "[HM #Hsnap]"; first done.
      iMod ("Hcl" with "[-]") as "_"; last by eauto.
      iExists _, _; iFrame; eauto.
    Qed.

    Lemma causality n s k h E :
      nclose DB_InvName ⊆ E →
      Global_Inv ⊢ local_history_seen γLs n s -∗
                 own_mem_snapshot γGsnap k h ={E}=∗
      ⌜∀ a e, a ∈ h → e ∈ s → vector_clock_lt (we_time a) (ae_time e) →
       ∃ e', e' ∈ (restrict_key k s) ∧ erase e' = a⌝.
    Proof.
      iIntros (?) "#Hinv Hseen Hsnap".
      rewrite /Global_Inv /local_history_seen.
      iDestruct "Hseen" as (γs Hγs) "[Hs1 Hs2]".
      iInv DB_InvName as (M Ss) "(?&?&?&>HM&?&?&>HL&>Hvl)" "Hcl".
      iDestruct "Hvl" as %Hvl.
      iDestruct (seen_lookup with "HL Hs1") as (s1) "#H1"; eauto.
      iDestruct (snapshot_lookup with "HM Hsnap") as (h1) "#Hh1".
      iDestruct "H1" as %[[? Hss1] ?].
      iDestruct "Hh1" as %[? ?].
      iMod ("Hcl" with "[-]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iPureIntro.
      intros ? ? ? ? Htime.
      edestruct (DBM_GstValid_causality {| Gst_mem := M; Gst_hst := Ss|} n s1 k)
        as (e' & He' & He'a);
        eauto.
      subst.
      eexists; split; last done.
      apply elem_of_filter in He' as [? ?].
      apply elem_of_filter; split; first done.
      eapply (Hss1 _ e); eauto.
      by rewrite erase_time in Htime.
    Qed.

    Lemma observe_local_history_internal (M : gmap Key (gset write_event)) Ss n s :
      own γGsnap (● M) ⊢
      ([∗ list] γs;T ∈ γLs;Ss, own γs.1 (● PrinSeen T) ∗ own γs.2 (◯ T)) -∗
      local_history_Local_inv γLs n s ==∗
      own γGsnap (● M) ∗
      ([∗ list] γs;T ∈ γLs;Ss, own γs.1 (● PrinSeen T) ∗ own γs.2 (◯ T)) ∗
      local_history_Local_inv γLs n s ∗
      local_history_seen γLs n s.
    Proof.
      iIntros "HM HL Hls".
      iDestruct "Hls" as (γs Hγs) "[#Hs1 Hs2]".
      iDestruct (big_sepL2_length with "HL") as %Hlen.
      destruct (lookup_lt_is_Some_2 Ss n) as [S HS].
      { rewrite -Hlen; apply lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_lookup_acc _ _ _ n with "HL") as "[[HS1 HS2] Hrest]";
        eauto.
      (* This is possibly a bug! Cannot do it during destruction above! *)
      iDestruct "HS2" as "#HS2".
      iDestruct (own_valid_2 with "HS1 Hs1") as %[Hv1 Hv2]%auth_both_valid_discrete.
      revert Hv1; rewrite principal_included; eauto; intros [? ?].
      iDestruct (own_valid_2 with "Hs2 HS2") as
          %[Hv1'%gset_included Hv2']%auth_both_valid_discrete.
      assert (s = S) by set_solver; subst.
      iSpecialize ("Hrest" with "[$HS1]"); first done.
      iFrame.
      by iModIntro; iSplit; iExists _; iFrame; iFrame "#".
    Qed.

    Lemma observe_local_history n s E :
      nclose DB_InvName ⊆ E →
      Global_Inv ⊢ local_history_Local_inv γLs n s ={E}=∗
             local_history_Local_inv γLs n s ∗ local_history_seen γLs n s.
    Proof.
      iIntros (?) "#Hinv Hls".
      rewrite /Global_Inv.
      iInv DB_InvName as (M Ss) "(?&?&?&>HM&?&?&>HL&?)" "Hcl".
      iMod (observe_local_history_internal with "HM HL Hls") as
          "(HM & HL & Hls & Hseen)".
      iMod ("Hcl" with "[-Hls Hseen]") as "_".
      { iExists _, _; iFrame; eauto. }
      iFrame; done.
    Qed.

    Lemma own_mem_snapshot_included k h h' E :
      nclose DB_InvName ⊆ E →
      Global_Inv ⊢
      own_mem_user γGauth γGsnap k h -∗
      own_mem_snapshot γGsnap k h' ={E}=∗
      own_mem_user γGauth γGsnap k h ∗ ⌜h' ⊆ h⌝.
    Proof.
      iIntros (?) "#Hinv [Hu1 Hu2] Hs".
      rewrite /Global_Inv /own_mem_snapshot.
      iInv DB_InvName as (M Ss) "(?&?&>HMa&>HMs&?&?&?&>Hvl)" "Hcl".
      iDestruct (snapshot_lookup with "HMs Hs") as (h1) "#Hh1".
      iDestruct "Hh1" as %[Hh11 Hh12].
      iDestruct (own_valid_2 with "HMa Hu1") as %[Hvl1 Hvl2]%auth_both_valid_discrete.
      revert Hvl1; rewrite lookup_included; intros Hvl1.
      specialize (Hvl1 k).
      rewrite /make_global_mem lookup_fmap Hh12 lookup_singleton /= in Hvl1.
      apply Excl_included, leibniz_equiv in Hvl1 as <-.
      iMod ("Hcl" with "[-Hu1 Hu2]") as "_".
      { iExists _, _; iFrame; eauto. }
      by iModIntro; iFrame.
    Qed.

  End Global_invariant.
