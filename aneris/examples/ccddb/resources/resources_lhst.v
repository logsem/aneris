(** Realisation of the DB_resources interface *)
From iris.algebra Require Import agree auth excl gmap.
From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang resources.
From aneris.examples.ccddb.spec Require Import base.
From aneris.examples.ccddb.model Require Import events model_spec.
From aneris.examples.ccddb.resources Require Import base.

Notation PrinSeen S := (principal seen_relation S).

Section Local_history.

  Context `{!anerisG Mdl Σ, !DB_params, !internal_DBG Σ}.

  Section Predicates.

    Context (γLs : list (gname * gname)).

    Definition local_history_Global_inv
               (γs : gname * gname) (S : gset apply_event) : iProp Σ :=
      own γs.1 (● (PrinSeen S)) ∗ own γs.2 (◯ S).

    Definition local_history_Local_inv
               (i : nat) (S : gset apply_event) : iProp Σ :=
      ∃ γs, ⌜γLs !! i = Some γs⌝ ∗ own γs.1 (◯ (PrinSeen S)) ∗ own γs.2 (● S).

    Definition local_history_seen (i : nat) (S : gset apply_event) : iProp Σ :=
      ∃ γs, ⌜γLs !! i = Some γs⌝ ∗
        own γs.1 (◯ (PrinSeen S)) ∗ own γs.2 (◯ S).

    Instance local_history_seen_Persistent :
      ∀ i s, Persistent (local_history_seen i s).
    Proof. apply _. Qed.

    Lemma seen_lookup i γs s Ss :
      γLs !! i = Some γs →
      ([∗ list] γs';T ∈ γLs;Ss, local_history_Global_inv γs' T) ⊢
      own γs.1 (◯ (PrinSeen s)) -∗
      ∃ s', ⌜seen_relation s s' ∧ Ss !! i = Some s'⌝.
    Proof.
      iIntros (Hi) "HL Hs".
      iDestruct (big_sepL2_length with "HL") as %Hlen.
      destruct (lookup_lt_is_Some_2 Ss i) as [S HS].
      { rewrite -Hlen; apply lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_lookup_acc _ _ _ i with "HL") as "[[HS1 HS2] Hrest]";
        eauto.
      iDestruct (own_valid_2 with "HS1 Hs") as %[Hv1 Hv2]%auth_both_valid_discrete.
      revert Hv1; rewrite principal_included; eauto.
    Qed.

    Lemma local_history_invs_agree i s Ss :
      ([∗ list] γs;T ∈ γLs;Ss, local_history_Global_inv γs T) ⊢
      local_history_Local_inv i s -∗ ⌜Ss !! i = Some s⌝.
    Proof.
      iIntros "HL Hs".
      iDestruct "Hs" as (γs ?) "[Hs1 Hs2]".
      iDestruct (big_sepL2_length with "HL") as %Hlen.
      destruct (lookup_lt_is_Some_2 Ss i) as [s' Hs'].
      { rewrite -Hlen; apply lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_lookup_acc _ _ _ i with "HL") as "[[HS1 HS2] Hrest]";
        eauto.
      iDestruct (own_valid_2 with "HS1 Hs1") as %[Hv1 Hv2]%auth_both_valid_discrete.
      revert Hv1; rewrite principal_included; intros [Hv11 Hv12].
      iDestruct (own_valid_2 with "Hs2 HS2") as %[Hv1' Hv2']%auth_both_valid_discrete.
      revert Hv1'; rewrite gset_included; intros Hv1'.
      iPureIntro.
      rewrite Hs'; f_equal.
      set_solver.
    Qed.

    Lemma global_local_history_agree i γs s s':
      γLs !! i = Some γs →
      local_history_Global_inv γs s ⊢ local_history_Local_inv i s' -∗ ⌜s = s'⌝.
    Proof.
      iIntros (Hi) "[Hs1 Hs2]".
      iDestruct 1 as (γs' Hi') "[Hs'1 Hs'2]".
      simplify_eq.
      iDestruct (own_valid_2 with "Hs1 Hs'1") as %[Hv1 Hv2]%auth_both_valid_discrete.
      revert Hv1; rewrite principal_included; intros [Hv11 Hv12].
      iDestruct (own_valid_2 with "Hs'2 Hs2") as %[Hv'1 Hv'2]%auth_both_valid_discrete.
      apply gset_included in Hv'1.
      iPureIntro; set_solver.
    Qed.

    Lemma local_history_seen_included i s s':
      local_history_Local_inv i s' ⊢ local_history_seen i s -∗ ⌜s ⊆ s'⌝.
    Proof.
      iDestruct 1 as (γs Hi) "[Hs1 Hs2]".
      iDestruct 1 as (γs' Hi') "[Hs'1 Hs'2]".
      simplify_eq.
      iDestruct (own_valid_2 with "Hs2 Hs'2") as %[Hv'1 Hv'2]%auth_both_valid_discrete.
      by apply gset_included in Hv'1.
    Qed.

    Lemma local_history_update i s Ss e:
      (∀ (e' : apply_event),
          e' ∈ s → vector_clock_lt (ae_time e) (ae_time e') → False) →
      local_history_Local_inv i s ⊢
      ([∗ list] γs;T ∈ γLs;Ss, local_history_Global_inv γs T) ==∗
      ([∗ list] γs;T ∈ γLs; <[i := s ∪ {[e]} ]> Ss,
        local_history_Global_inv γs T) ∗
      local_history_Local_inv i (s ∪ {[e]}).
    Proof.
      iIntros (He) "Hs HL".
      iDestruct "Hs" as (γs ?) "[Hs1 Hs2]".
      iDestruct (big_sepL2_length with "HL") as %Hlen.
      destruct (lookup_lt_is_Some_2 Ss i) as [s' Hs'].
      { rewrite -Hlen; apply lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_insert_acc _ _ _ i with "HL") as "[HS Hback]";
        eauto.
      iDestruct (global_local_history_agree with "HS [Hs1 Hs2]") as %->;
        first done.
      { iExists _; iSplit; first done; iFrame. }
      iDestruct "HS" as "[HS1 HS2]".
      iMod (own_update_2 _ _ _ (● PrinSeen (s ∪ {[e]}) ⋅ ◯ PrinSeen (s ∪ {[e]}))
              with "HS1 Hs1") as "[HS1 Hs1]".
      { apply auth_update.
        apply monotone_local_update_grow.
        split; set_solver. }
      iMod (own_update_2 _ _ _ (● (s ∪ {[e]}) ⋅ ◯ (s ∪ {[e]}))
              with "Hs2 HS2") as "[Hs2 HS2]".
      { apply auth_update.
        apply gset_local_update.
        set_solver. }
      iSpecialize ("Hback" $! γs (s ∪ {[e]}) with "[$HS1 $HS2]").
      rewrite (list_insert_id γLs); last done.
      iModIntro; iFrame.
      iExists _; iSplit; first done; iFrame.
    Qed.

  End Predicates.

  Section init.

    Lemma alloc_lhst :
    True ⊢ |==>
      ∃ γLs,
        ⌜length γLs = length DB_addresses⌝ ∗
        ([∗ list] γs; T ∈ γLs; empty_lhsts, local_history_Global_inv γs T) ∗
        ([∗ list] i ↦ _ ∈ DB_addresses, local_history_Local_inv γLs i ∅).
  Proof.
    iIntros (_).
    rewrite /empty_lhsts.
    iInduction DB_addresses as [|dba] "IHdba"; simpl.
    { by iModIntro; iExists []; rewrite !big_sepL2_nil. }
    iMod ("IHdba") as (γLs Hlen) "[H1 H2]".
    iMod (own_alloc (● PrinSeen ∅ ⋅ ◯ PrinSeen ∅)) as (γ1) "[H31 H32]".
    { by apply auth_both_valid_discrete. }
    iMod (own_alloc (● ∅ ⋅ ◯ ∅)) as (γ2) "[H41 H42]".
    { by apply auth_both_valid_discrete. }
    iModIntro.
    iExists ((γ1, γ2) :: γLs).
    rewrite -Hlen /=; iSplit; first done.
    iFrame.
    iExists (γ1, γ2); iSplit; first done.
    iFrame.
  Qed.

  End init.

End Local_history.
