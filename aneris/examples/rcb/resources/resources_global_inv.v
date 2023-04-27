(** Realisation of the RCB_resources interface *)
From iris.algebra Require Import agree auth excl gmap.
From aneris.algebra Require Import monotone.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang resources.
From aneris.aneris_lang.lib Require Import vector_clock_proof lock_proof.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import
     events model_spec.
From aneris.examples.rcb.resources Require Import
     base resources_global resources_lhst.

Section Global_invariant.
  Context `{!anerisG Mdl Σ, !RCB_params, !RCB_global_state_valid, !internal_RCBG Σ}.
  Context (γOwn γSnap : gname) (γLs : list gname).

  Definition Global_Inv :=
    inv RCB_InvName
          (∃ G Ss,
              ⌜length γLs = length RCB_addresses⌝ ∗
              own_global_sys γOwn γSnap G ∗
              ([∗ list] γs; T ∈ γLs; Ss, lhst_glob_aux γs T)
              ∗ ⌜RCBM_GstValid {| Gst_ghst := G; Gst_hst := Ss|}⌝
          ).

    Lemma own_global_snap_ext h h' E :
      nclose RCB_InvName ⊆ E →
      Global_Inv ⊢ own_global_snap γSnap h -∗
      own_global_snap γSnap h' ={E}=∗
        ⌜∀ a a', a ∈ h → a' ∈ h' → ge_time a = ge_time a' → a = a'⌝.
    Proof.
      iIntros (?) "#Hinv Hh Hh'".
      rewrite /Global_Inv /own_global_snap.
      iInv RCB_InvName as (G Ss) "(>%&>(?&HG&?)&?&>%Hv)" "Hcl".
      iDestruct (snap_lookup with "HG Hh") as "%Hh1".
      iDestruct (snap_lookup with "HG Hh'") as "%Hh2".
      iMod ("Hcl" with "[-]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iPureIntro.
      intros.
      eapply (RCBM_GstValid_ghst_ext _); eauto.
    Qed.

    Lemma lhst_user_ext n n' s s' E :
      nclose RCB_InvName ⊆ E →
      Global_Inv ⊢
      lhst_user γLs n s -∗ lhst_user γLs n' s' ={E}=∗
      ⌜∀ e e', e ∈ s → e' ∈ s' → le_time e = le_time e' →
               e.(le_payload) = e'.(le_payload) /\
               e.(le_orig) = e'.(le_orig)⌝.
    Proof.
      iIntros (?) "#Hinv Hl Hl'".
      rewrite /Global_Inv.
      iInv RCB_InvName as (G Ss) "(>%&>?&>HL&>%Hv)" "Hcl".
      iDestruct (lhst_user_lookup with "HL Hl") as "%Heq".
      iDestruct (lhst_user_lookup with "HL Hl'") as "%Heq'".
      iMod ("Hcl" with "[-]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iPureIntro.
      intros.
      eapply (RCBM_GstValid_lhst_ext _ n n'); eauto.
    Qed.

    Lemma lhst_user_strong_ext n s E :
      nclose RCB_InvName ⊆ E →
      Global_Inv ⊢ lhst_user γLs n s ={E}=∗
      ⌜∀ e e', e ∈ s → e' ∈ s → le_time e = le_time e' → e = e'⌝.
    Proof.
      iIntros (?) "#Hinv Hl".
      rewrite /Global_Inv.
      iInv RCB_InvName as (G Ss) "(>%&>?&>HL&>%Hv)" "Hcl".
      iDestruct (lhst_user_lookup with "HL Hl") as "%Heq".
      iMod ("Hcl" with "[-]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iPureIntro.
      intros.
      eapply (RCBM_GstValid_lhst_strong_ext _ n); eauto.
    Qed.

    Lemma lhst_user_provenance n s E :
      nclose RCB_InvName ⊆ E →
      Global_Inv ⊢ lhst_user γLs n s ={E}=∗
       lhst_user γLs n s ∗ (∃ h, own_global_snap γSnap h ∗ ⌜∀ e, e ∈ s -> erase e ∈ h⌝).
    Proof.
      iIntros (?) "#Hinv Hl".
      rewrite /Global_Inv.
      iInv RCB_InvName as (G Ss) "(>%&>Hsys&>HL&>%Hv)" "Hcl".
      iDestruct (lhst_user_lookup with "HL Hl") as "%Heq".
      assert (∀ e, e ∈ s -> erase e ∈ G) as Hsub.
      { intros e.
        apply (RCBM_GstValid_le_provenance {| Gst_ghst := G; Gst_hst := Ss|} n s); done. }
      iDestruct (own_global_sys_snap with "Hsys") as "[Hsys #Hsnap]".
      iMod ("Hcl" with "[-Hl]") as "_";
        iModIntro; eauto with iFrame.
    Qed.

    Lemma global_snap_provenance n s h E :
      ↑RCB_InvName ⊆ E ->
      Global_Inv ⊢ own_global_snap γSnap h
                 -∗ lhst_user γLs n s
                 ={E}=∗ ⌜∀ a, a ∈ h -> a.(ge_orig) = n -> ∃ e, e ∈ s ∧ erase e = a⌝.
    Proof.
      iIntros (?) "#Hinv #Hsnap Huser".
      iInv RCB_InvName as (G Ss) "(>%&>Hsys&>HL&>%Hv)" "Hcl".
      iDestruct (own_global_snap_lookup with "Hsys Hsnap") as "%Hinc".
      remember {| Gst_ghst := G; Gst_hst := Ss |} as gst.
      iDestruct (lhst_user_lookup with "HL Huser") as "%Hlookup_n".
      subst.
      iMod ("Hcl" with "[-]") as "_"; [eauto with iFrame|].
      iModIntro.
      iPureIntro.
      intros a Hinh Horig.
      assert (a ∈ G) as HinG by set_solver.
      pose proof (RCBM_GstValid_ge_provenance _ _ Hv HinG) as [sn [en [Hlook [Hinsn Herase]]]].
      assert (s = sn) as ->.
      { simpl in Hlook.
        subst.
        rewrite Hlook in Hlookup_n.
        inversion Hlookup_n; done. }
      eauto.
    Qed.

    Lemma causality n s h E :
      nclose RCB_InvName ⊆ E →
      Global_Inv ⊢ lhst_user γLs n s -∗
                 own_global_snap γSnap h ={E}=∗
      ⌜∀ a e, a ∈ h → e ∈ s → vector_clock_lt (ge_time a) (le_time e) →
       ∃ e', e' ∈ s ∧ erase e' = a⌝.
    Proof.
      iIntros (?) "#Hinv Huser Hsnap".
      rewrite /Global_Inv.
      iInv RCB_InvName as (G Ss) "(>%&>Hsys&>HL&>%Hv)" "Hcl".
      iDestruct (lhst_user_lookup with "HL Huser") as "%Heq".
      iDestruct (own_global_snap_lookup with "Hsys Hsnap") as "%Hin".
      iMod ("Hcl" with "[-]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iPureIntro.
      intros ? ? ? ? Htime.
      edestruct (RCBM_GstValid_causality {| Gst_ghst := G; Gst_hst := Ss|} n s)
        as (e' & He' & He'a);
        eauto.
    Qed.

    Lemma own_global_snap_included h h' E :
      nclose RCB_InvName ⊆ E →
      Global_Inv ⊢
      own_global_user γOwn γSnap h -∗
      own_global_snap γSnap h' ={E}=∗
      own_global_user γOwn γSnap h ∗ ⌜h' ⊆ h⌝.
    Proof.
      iIntros (?) "#Hinv Hu Hsnap".
      rewrite /Global_Inv /own_global_snap.
      iInv RCB_InvName as (G Ss) "(>%&>Hsys&>HL&>%Hv)" "Hcl".
      iDestruct (own_global_snap_lookup with "Hsys Hsnap") as "%Hin".
      iDestruct (own_global_user_sys_agree with "Hu Hsys") as "%".
      iMod ("Hcl" with "[-Hu]") as "_".
      { iExists _, _; iFrame; eauto. }
      iModIntro; iFrame; auto with set_solver.
    Qed.

    Lemma own_global_snap_time_length a h E :
      ↑RCB_InvName ⊆ E ->
      a ∈ h ->
      Global_Inv ⊢
      own_global_snap γSnap h ={E}=∗
      ⌜length a.(ge_time) = length RCB_addresses⌝.
    Proof.
      iIntros (? Hin) "#Hinv #Hsnap".
      iInv RCB_InvName as (G Ss) "(>%&>Hsys&>HL&>%Hv)" "Hcl".
      iDestruct (own_global_snap_lookup with "Hsys Hsnap") as "%Hsub".
      iMod ("Hcl" with "[-]") as "_"; eauto with iFrame.
      iModIntro. iPureIntro.
      eapply RCBM_GstValid_time_length; eauto with set_solver.
    Qed.

    Lemma own_global_snap_orig a h E :
      ↑RCB_InvName ⊆ E ->
      a ∈ h ->
      Global_Inv ⊢
      own_global_snap γSnap h ={E}=∗
      ⌜a.(ge_orig) < length RCB_addresses⌝.
    Proof.
      iIntros (? Hin) "#Hinv #Hsnap".
      iInv RCB_InvName as (G Ss) "(>%&>Hsys&>HL&>%Hv)" "Hcl".
      iDestruct (own_global_snap_lookup with "Hsys Hsnap") as "%Hsub".
      iMod ("Hcl" with "[-]") as "_"; eauto with iFrame.
      iModIntro. iPureIntro.
      eapply RCBM_GstValid_orig; eauto with set_solver.
    Qed.

End Global_invariant.
