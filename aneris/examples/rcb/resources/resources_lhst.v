(** Realisation of the RCB_resources interface *)
From iris.algebra Require Import agree auth excl gmap.
From aneris.algebra Require Import monotone.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From aneris.aneris_lang Require Import lang resources.
From aneris.examples.rcb.spec Require Import base.
From aneris.examples.rcb.model Require Import events model_spec.
From aneris.examples.rcb.resources Require Import base.

Section Local_history.

  Context `{!anerisG Mdl Σ, !RCB_params, !internal_RCBG Σ}.

  Section Predicates.

    (* One ghost location per replica *)
    Context (γLs : list gname).

    Definition mk_hst (q : Qp)
                       (h : gset local_event) :
                       prodR fracR (agreeR (gsetO local_event)) :=
      (q, to_agree h).

    (* For some reason we can't write 6%Qp... *)
    Definition one_sixth_qp := (1 / pos_to_Qp 6)%Qp.

    (* Lives in the global invariant *)
    Definition lhst_glob_aux (γ : gname) (s : gset local_event) : iProp Σ :=
      own γ (mk_hst one_sixth_qp s).

    Definition lhst_glob (i : nat) (s : gset local_event) : iProp Σ :=
      ∃ γ, ⌜γLs !! i = Some γ⌝ ∗ lhst_glob_aux γ s.

    (* Lives in the lock invariant *)
    Definition lhst_lock_aux (γ : gname) (s : gset local_event) : iProp Σ :=
      own γ (mk_hst one_sixth_qp s).

    Definition lhst_lock (i : nat) (s : gset local_event) : iProp Σ :=
      ∃ γ, ⌜γLs !! i = Some γ⌝ ∗  lhst_lock_aux γ s.

    (* Given to the user *)
    Definition lhst_user_aux (γ : gname) (s : gset local_event) : iProp Σ :=
      own γ (mk_hst (2/3)%Qp s).

    Definition lhst_user (i : nat) (s : gset local_event) : iProp Σ :=
      ∃ γ, ⌜γLs !! i = Some γ⌝ ∗ lhst_user_aux γ s.


    Lemma lhst_glob_lock_user_full :
      (2 / 3 + 1 / pos_to_Qp 6 + 1 / pos_to_Qp 6)%Qp = 1%Qp.
    Proof. compute_done. Qed.

    Lemma lhst_user_excl (i : nat) (s s' : gset local_event) :
      lhst_user i s ⊢ lhst_user i s' -∗ False.
    Proof.
      iIntros "Hl1 Hl2".
      iDestruct "Hl1" as (γ1) "[%Heq1 Hown1]".
      iDestruct "Hl2" as (γ2) "[%Heq2 Hown2]".
      assert (γ1 = γ2) as ->.
      { rewrite Heq1 in Heq2.
        inversion Heq2; done. }
      iPoseProof (own_valid_2 with "Hown1 Hown2") as "%Hv".
      exfalso.
      rewrite /mk_hst in Hv.
      eapply frac_pair_valid_implies_false; [apply Hv | by compute ].
    Qed.

    Lemma lhst_mk_hst_agree (γ : gname) (p q : Qp) (s1 s2 : gset local_event) :
      own γ (mk_hst p s1) ⊢ own γ (mk_hst q s2)  -∗ ⌜s1 = s2⌝.
    Proof.
      iIntros "H1 H2".
      iPoseProof (own_valid_2 with "H1 H2") as "%Hv".
      iPureIntro.
      rewrite -pair_op in Hv.
      apply (iffLR (pair_valid _ _)) in Hv as [_ Hv].
      apply to_agree_op_valid in Hv.
      by (apply leibniz_equiv).
    Qed.

    Lemma lhst_user_lock_aux_agree γ s1 s2 :
      lhst_user_aux γ s1 ⊢ lhst_lock_aux γ s2 -∗ ⌜s1 = s2⌝.
    Proof. apply lhst_mk_hst_agree. Qed.

    Lemma lhst_user_glob_aux_agree γ s1 s2 :
      lhst_user_aux γ s1 ⊢ lhst_glob_aux γ s2 -∗ ⌜s1 = s2⌝.
    Proof. apply lhst_mk_hst_agree. Qed.

    Lemma lhst_lock_glob_aux_agree γ s1 s2 :
      lhst_lock_aux γ s1 ⊢ lhst_glob_aux γ s2 -∗ ⌜s1 = s2⌝.
    Proof. apply lhst_mk_hst_agree. Qed.

    Lemma lhst_user_lock_agree i s1 s2 :
      lhst_user i s1 ⊢ lhst_lock i s2 -∗ ⌜s1 = s2⌝.
    Proof.
      iIntros "Huser Hlock".
      iDestruct "Huser" as (γ1) "[%Hl1 Huser]".
      iDestruct "Hlock" as (γ2) "[%Hl2 Hlock]".
      assert (γ1 = γ2) as ->.
      { rewrite Hl1 in Hl2; inversion Hl2; done. }
      iApply (lhst_user_lock_aux_agree with "Huser Hlock").
    Qed.

    Lemma lhst_user_glob_agree i s1 s2 :
      lhst_user i s1 ⊢ lhst_glob i s2 -∗ ⌜s1 = s2⌝.
    Proof.
      iIntros "Huser Hglob".
      iDestruct "Huser" as (γ1) "[%Hl1 Huser]".
      iDestruct "Hglob" as (γ2) "[%Hl2 Hglob]".
      assert (γ1 = γ2) as ->.
      { rewrite Hl1 in Hl2; inversion Hl2; done. }
      iApply (lhst_user_glob_aux_agree with "Huser Hglob").
    Qed.

    Lemma lhst_lock_glob_agree i s1 s2 :
      lhst_lock i s1 ⊢ lhst_glob i s2 -∗ ⌜s1 = s2⌝.
    Proof.
      iIntros "Hlock Hglob".
      iDestruct "Hlock" as (γ1) "[%Hl1 Hlock]".
      iDestruct "Hglob" as (γ2) "[%Hl2 Hglob]".
      assert (γ1 = γ2) as ->.
      { rewrite Hl1 in Hl2; inversion Hl2; done. }
      iApply (lhst_lock_glob_aux_agree with "Hlock Hglob").
    Qed.

    Lemma lhst_user_lookup i s Ss :
      ([∗ list] γs';S ∈ γLs;Ss, lhst_glob_aux γs' S) ⊢
      lhst_user i s -∗
      ⌜Ss !! i = Some s⌝.
    Proof.
      iIntros "HL Hs".
      iDestruct "Hs" as (γ) "[% Hs]".
      iDestruct (big_sepL2_length with "HL") as %Hlen.
      destruct (lookup_lt_is_Some_2 Ss i) as [S HS].
      { rewrite -Hlen; apply lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_lookup_acc _ _ _ i with "HL") as "[HS Hrest]";
        eauto.
      by (iDestruct (lhst_user_glob_aux_agree with "Hs HS") as %->).
    Qed.

    Lemma lhst_lock_lookup i s Ss :
      ([∗ list] γs';S ∈ γLs;Ss, lhst_glob_aux γs' S) ⊢
      lhst_lock i s -∗
      ⌜Ss !! i = Some s⌝.
    Proof.
      iIntros "HL Hs".
      iDestruct "Hs" as (γ) "[% Hs]".
      iDestruct (big_sepL2_length with "HL") as %Hlen.
      destruct (lookup_lt_is_Some_2 Ss i) as [S HS].
      { rewrite -Hlen; apply lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_lookup_acc _ _ _ i with "HL") as "[HS Hrest]";
        eauto.
      by (iDestruct (lhst_lock_glob_aux_agree with "Hs HS") as %->).
    Qed.

    Lemma lhst_update_aux γ s e :
      lhst_user_aux γ s ⊢
      lhst_lock_aux γ s -∗
      lhst_glob_aux γ s ==∗
      lhst_user_aux γ (s ∪ {[e]}) ∗
      lhst_lock_aux γ (s ∪ {[e]}) ∗
      lhst_glob_aux γ (s ∪ {[e]}).
    Proof.
      iIntros "Hu Hl Hg".
      iMod (own_update_3 _ _ _ _
                         ((mk_hst (2/3)%Qp (s ∪ {[e]})) ⋅
                          (mk_hst one_sixth_qp (s ∪ {[e]})) ⋅
                          (mk_hst one_sixth_qp (s ∪ {[e]}))) with "Hu Hl Hg") as "Hfull".
      { assert (Exclusive (mk_hst (2 / 3) s ⋅
                           mk_hst one_sixth_qp s ⋅
                           mk_hst one_sixth_qp s)) as excl.
        { rewrite -pair_op; simpl.
          apply pair_exclusive_l.
          rewrite /one_sixth_qp.
          do 2 rewrite frac_op.
          rewrite lhst_glob_lock_user_full.
          apply frac_full_exclusive. }
        apply cmra_update_exclusive.
        rewrite /mk_hst /one_sixth_qp.
        rewrite -pair_op.
        apply pair_valid; simpl; split.
        - apply frac_valid; done.
        - do 2 rewrite agree_idemp; done. }
      iDestruct (own_op with "Hfull") as "[Hfull Hglob]".
      iDestruct (own_op with "Hfull") as "[Hfull Hlock]".
      iModIntro.
      iFrame.
    Qed.

    Lemma lhst_update i s Ss e:
      lhst_user i s ⊢
      lhst_lock i s -∗
      ([∗ list] γs;S ∈ γLs;Ss, lhst_glob_aux γs S) ==∗
      lhst_user i (s ∪ {[ e ]}) ∗
      lhst_lock i (s ∪ {[ e ]}) ∗
      ([∗ list] γs;S ∈ γLs; <[i := s ∪ {[ e ]} ]> Ss, lhst_glob_aux γs S).
    Proof.
      iIntros "Hu Hl HL".
      iDestruct "Hu" as (γu) "[%Hlu Hu]".
      iDestruct "Hl" as (γl) "[%Hll Hl]".
      iDestruct (big_sepL2_length with "HL") as %Hlen.
      destruct (lookup_lt_is_Some_2 Ss i) as [s' Hs'].
      { rewrite -Hlen; apply lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_insert_acc _ _ _ i with "HL") as "[HS Hback]";
        eauto.
      assert (γl = γu) as ->.
      { rewrite Hlu in Hll; inversion Hll; done. }
      iDestruct (lhst_lock_glob_aux_agree with "Hl HS") as %->.
      iMod ((lhst_update_aux _ _ e) with "Hu Hl HS") as "(Hu & Hl & HS)".
      iSpecialize ("Hback" $! γu (s' ∪ {[e]}) with "HS").
      rewrite (list_insert_id γLs); last done.
      iModIntro; iFrame.
      iSplitL "Hu"; iExists _; by iFrame.
    Qed.

  End Predicates.

  Section init.

    Lemma alloc_lhst :
    True ⊢ |==>
      ∃ γLs,
        ⌜length γLs = length RCB_addresses⌝ ∗
        ([∗ list] i ↦ _ ∈ RCB_addresses, lhst_glob γLs i ∅) ∗
        ([∗ list] i ↦ _ ∈ RCB_addresses, lhst_lock γLs i ∅) ∗
        ([∗ list] i ↦ _ ∈ RCB_addresses, lhst_user γLs i ∅).
    Proof.
      iIntros (_).
      iInduction RCB_addresses as [|dba] "IHdba"; simpl.
      { by iModIntro; iExists []. }
      iMod ("IHdba") as (γLs Hlen) "(Hg & Hl & Hu)".
      iMod (own_alloc (mk_hst (2 / 3)%Qp ∅ ⋅ mk_hst one_sixth_qp ∅ ⋅ mk_hst one_sixth_qp ∅)) as (γ') "Hnew".
      { rewrite -pair_op /one_sixth_qp frac_op frac_op; simpl.
        apply pair_valid; split; [ | do 2 rewrite agree_idemp; done].
        rewrite lhst_glob_lock_user_full; done. }
      iDestruct (own_op with "Hnew") as "[Hnew Hg']".
      iDestruct (own_op with "Hnew") as "[Hu' Hl']".
      iModIntro.
      iExists (γ' :: γLs).
      rewrite -Hlen /=; iSplit; first done.
      iFrame.
      iSplitL "Hg'"; [iExists γ'; iFrame; done |].
      iSplitL "Hl'"; [iExists γ'; iFrame; done |].
      iExists γ'; iFrame; done.
    Qed.

  End init.

End Local_history.
