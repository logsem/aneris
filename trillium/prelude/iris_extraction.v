From iris.base_logic Require Import bi.
From trillium.prelude Require Import quantifiers.
From iris.proofmode Require Import tactics.

Import uPred.

Local Arguments uPred_holds _ !_.

Section extraction.
  Context {M : ucmra}.

  Lemma extract_forall {A} (Φ : A → uPred M) : (⊢ ∀ x, Φ x) ↔ (∀ x, ⊢ Φ x).
  Proof.
    split; intros HP.
    - constructor; unseal.
      intros ? ? ? _.
      destruct HP as [HP]; revert HP; unseal; intros HP.
      apply HP; auto.
    - iIntros (x); iApply HP.
  Qed.

  Local Coercion uPred_holds : uPred >-> Funclass.

  Lemma extract_exists {A} (Φ : A → uPred M) :
    smaller_card A nat → (⊢ ∃ x, Φ x) ↔ (∃ x, ⊢ Φ x).
  Proof.
    intros Hcard.
    split; intros HP.
    - destruct HP as [HP]; revert HP; unseal; intros HP.
      assert (∀ n, ∃ x, Φ x n ε) as HP'.
      { intros; apply HP; eauto using ucmra_unit_validN. }
      apply (forall_exists_swap _ le) in HP' as [x Hx];
        auto using nat_regular with lia; last first.
      { intros ?????; eapply uPred_mono; eauto. }
      exists x.
      constructor; unseal.
      intros ? ? ? _.
      eapply uPred_mono; [apply Hx|apply ucmra_unit_leastN |auto].
    - destruct HP as [x Hx].
      iExists _; iApply Hx.
  Qed.

  Lemma extract_exists_alt {A} (P : A → Prop) (Φ : A → uPred M) :
    smaller_card (sig P) nat → (⊢ ∃ x, ⌜P x⌝ ∧ Φ x) ↔ (∃ x, ⊢ ⌜P x⌝ ∧ Φ x).
  Proof.
    intros Hcard.
    split; intros HP.
    - assert (⊢ ∃ x : sig P, Φ (proj1_sig x)) as HP'.
      { iDestruct HP as (x) "[HPx Hx]".
        iDestruct "HPx" as %HPx.
        iExists (exist _ _ HPx); done. }
      apply extract_exists in HP' as [[x HPx] HΦ]; last done.
      eexists; iSplit; done.
    - destruct HP as [x Hx].
      iExists _; iApply Hx.
  Qed.

  Lemma extract_exists_alt2 {A B} (P : A -> B → Prop) (Φ : A → B -> uPred M) :
    smaller_card (sig (fun '(x, y) => P x y)) nat → (⊢ ∃ x y, ⌜P x y⌝ ∧ Φ x y) ↔ (∃ x y, ⊢ ⌜P x y⌝ ∧ Φ x y).
  Proof.
    intros Hcard.
    split; intros HP.
    - assert (⊢ ∃ x : sig (fun '(x, y) => P x y), Φ (proj1_sig x).1 (proj1_sig x).2)%I as HP'.
      { iDestruct HP as (x y) "[HPx Hx]".
        iDestruct "HPx" as %HPx.
        iExists (exist _ (x,y) HPx); done. }
      apply extract_exists in HP' as [[x HPx] HΦ]; last done.
      eexists _,_; iSplit; eauto. by iPureIntro; destruct x.
    - destruct HP as [x [y Hxy]].
        by iExists _, _.
  Qed.

  Lemma extract_and (P Q : uPred M) : (⊢ P ∧ Q) ↔ ((⊢ P) ∧ (⊢ Q)).
  Proof.
    split; intros HPQ.
    - destruct HPQ as [HPQ]; revert HPQ; unseal; intros HPQ.
      repeat constructor; intros ? ? ? _; apply HPQ; auto.
    - destruct HPQ as [HP HQ].
      iSplit; [iApply HP|iApply HQ].
  Qed.

  Lemma extract_or (P Q : uPred M) : (⊢ P ∨ Q) ↔ ((⊢ P) ∨ (⊢ Q)).
  Proof.
    split; intros HPQ.
    - assert (⊢ ∃ b : bool, if b then P else Q) as HPQ'.
      { iPoseProof HPQ as "[HP|HQ]"; [iExists true|iExists false]; done. }
      apply extract_exists in HPQ'; last first.
      { intros f Hf.
        destruct (f 0) eqn:Hf0; destruct (f 1) eqn:Hf1.
        - rewrite -Hf1 in Hf0; apply Hf in Hf0; lia.
        - destruct (f 2) eqn:Hf2.
          + rewrite -Hf2 in Hf0; apply Hf in Hf0; lia.
          + rewrite -Hf2 in Hf1; apply Hf in Hf1; lia.
        - destruct (f 2) eqn:Hf2.
          + rewrite -Hf2 in Hf1; apply Hf in Hf1; lia.
          + rewrite -Hf2 in Hf0; apply Hf in Hf0; lia.
        - rewrite -Hf1 in Hf0; apply Hf in Hf0; lia. }
      destruct HPQ' as [[|] ?]; eauto.
    - destruct HPQ as [HP|HQ]; [iLeft|iRight]; done.
  Qed.

  Lemma extract_pure φ : (⊢@{uPredI M} ⌜φ⌝) ↔ φ.
  Proof.
    split; last by intros HP; auto.
    intros [Hφ]; revert Hφ; unseal; intros Hφ.
    apply (Hφ 0 ε); first apply ucmra_unit_validN; done.
 Qed.

  Lemma extract_True : (⊢@{uPredI M} True) ↔ (True).
  Proof. apply extract_pure. Qed.

  Lemma extract_False : (⊢@{uPredI M} False) ↔ (False).
  Proof. apply extract_pure. Qed.

  Lemma extract_impl (P Q : uPred M) : (⊢ P → Q) → ((⊢ P) → (⊢ Q)).
  Proof. intros HPQ HP; iApply HPQ; auto. Qed.

  Lemma extract_sep (P Q : uPred M) : (⊢ P ∗ Q) ↔ ((⊢ P) ∧ (⊢ Q)).
  Proof.
    split; intros HPQ.
    - destruct HPQ as [HPQ]; revert HPQ; unseal; intros HPQ.
      repeat constructor; intros ? ? ? _.
      + edestruct (λ He, HPQ n ε He I) as (? & ? & Hrs & ? & ?);
          [apply ucmra_unit_validN|].
        eapply uPred_mono; eauto.
        transitivity (ε : M); last apply ucmra_unit_leastN.
        rewrite Hrs; apply cmra_includedN_l.
      + edestruct (λ He, HPQ n ε He I) as (? & ? & Hrs & ? & ?);
          [apply ucmra_unit_validN|].
        eapply uPred_mono; eauto.
        transitivity (ε : M); last apply ucmra_unit_leastN.
        rewrite Hrs; apply cmra_includedN_r.
    - destruct HPQ as [HP HQ].
      iSplitL; auto.
  Qed.

  Lemma extract_wand (P Q : uPred M) : (⊢ P -∗ Q) → ((⊢ P) → (⊢ Q)).
  Proof. intros HPQ HP; iApply HPQ; auto. Qed.

  Lemma extract_later (P : uPred M) : (⊢ ▷ P) ↔ (⊢ P).
  Proof.
    split; intros HP; destruct HP as [HP]; constructor; revert HP; unseal;
      intros HP n x Hx _.
    - eapply uPred_mono; first apply (HP (S n) ε);
        eauto using ucmra_unit_validN, ucmra_unit_leastN.
    - destruct n; [|apply HP]; auto using cmra_validN_S.
  Qed.

  Lemma extract_except_0 (P : uPred M) : (⊢ ◇ P) ↔ (⊢ P).
  Proof.
    unfold bi_except_0.
    split; intros HP; destruct HP as [HP]; constructor; revert HP; unseal;
      intros HP n x Hx _.
    - specialize (HP (S n)); simpl in *.
      destruct (HP ε); auto using ucmra_unit_validN; first done.
      eapply uPred_mono; eauto using ucmra_unit_validN, ucmra_unit_leastN.
    - destruct n; first by left.
      right.
      apply HP; auto.
  Qed.

  Lemma extract_bupd (P : uPred M) `{!Plain P} : (⊢ |==> P) ↔ (⊢ P).
  Proof.
    split; intros HP.
    - iMod HP as "HP"; done.
    - iModIntro; iApply HP.
  Qed.

  Lemma extract_internal_eq (A : ofe) (x y : A) : (⊢@{uPredI M} x ≡ y) ↔ (x ≡ y).
  Proof.
    split; intros Hxy.
    - destruct Hxy as [Hxy]; revert Hxy; unseal; intros Hxy.
      apply equiv_dist; intros n.
      apply (Hxy n ε); auto using ucmra_unit_validN.
    - by rewrite Hxy; auto.
  Qed.

  Lemma extract_plainly (P : uPred M) : (⊢ ■ P) ↔ (⊢ P).
  Proof.
    split; intros HP.
    - iApply HP.
    - iModIntro; iApply HP.
  Qed.

  Lemma extract_persistently (P : uPred M) : (⊢ □ P) ↔ (⊢ P).
  Proof.
    split; intros HP.
    - iApply HP.
    - iModIntro; iApply HP.
  Qed.

  Lemma extract_own (x : M) : (⊢ uPred_ownM x) ↔ ∀ n, x ≼{n} ε.
  Proof.
    split; intros Hx.
    - destruct Hx as [Hx]; revert Hx; unseal; intros Hx.
      intros n; apply Hx; first apply ucmra_unit_validN; done.
    - constructor; intros.
      eapply uPred_mono; first (by unseal; apply (Hx n); eauto);
        auto using ucmra_unit_leastN.
  Qed.

  Lemma extract_valid {A : ucmra} (x : A) : (⊢@{uPredI M} ✓ x) ↔ ✓ x.
  Proof.
    split; intros Hx.
    - destruct Hx as [Hx]; revert Hx; unseal; intros Hx.
      apply cmra_valid_validN.
      intros n; apply (Hx n ε); first apply ucmra_unit_validN; done.
    - constructor; intros; unseal; apply cmra_valid_validN; done.
  Qed.

End extraction.
