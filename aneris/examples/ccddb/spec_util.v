From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang network proofmode.
From aneris.prelude Require Import misc gset_map.
From aneris.examples.ccddb.spec Require Import spec.

Section maximals.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events, !Maximals_Computing}.

  Lemma elem_of_Maximals e X :
    e ∈ Maximals X → e ∈ X.
  Proof. move=> /Maximals_correct [? _] //. Qed.

  Lemma elem_of_Maximals_restrict_key e k s :
    e ∈ Maximals (restrict_key k s) → AE_key e = k ∧ e ∈ s.
  Proof. move=> /elem_of_Maximals /elem_of_filter //. Qed.

  Lemma Maximum_correct_2 {T : Type} `{!EqDecision T} `{!Countable T}
        `{!Timed T} (X : gset T) (x :T) :
    (∀ x y, x ∈ X → y ∈ X → x =ₜ y → x = y) →
    Maximum X = Some x →
    IsMaximum X x.
  Proof. move=> ??. apply Maximum_correct=> //. Qed.

  Lemma Maximals_correct_2 {T : Type} `{!EqDecision T} `{!Countable T}
        `{!Timed T} (X : gset T) (t : T):
    t ∈ Maximals X →
    t ∈ X ∧ ∀ t' : T, t' ∈ X → ¬ (t <ₜ t').
  Proof. apply Maximals_correct. Qed.

  Lemma Maximum_singleton {T : Type} `{!EqDecision T} `{!Countable T}
        `{!Timed T} (t : T) :
    Maximum {[t]} = Some t.
  Proof.
    apply/Maximum_correct => [??|].
    - do 2! move/elem_of_singleton ->; move=> //.
    - split; [exact/elem_of_singleton|].
      move=> ? /elem_of_singleton -> //.
  Qed.

End maximals.

Section events.
  Context `{!DB_time, !DB_events}.

  Definition erasure_set (s : lhst) : gmem := gset_map erasure s.

  Lemma elem_of_erasure_set (a : we) (s : lhst) :
    a ∈ erasure_set s → ∃ (e : ae), a = erasure e ∧ e ∈ s.
  Proof. apply gset_map_correct2. Qed.

  Lemma union_singleton_erasure_set h s e :
    h ⊆ erasure_set s →
    h ∪ {[erasure e]} ⊆ erasure_set (s ∪ {[e]}).
  Proof. set_solver. Qed.

  Lemma ae_key_neq e1 e2 x y :
    AE_key e1 = x →
    AE_key e2 = y →
    x ≠ y →
    e1 ≠ e2.
  Proof. by intros <- <- ? ->. Qed.

  Lemma restrict_key_mono e k s s' :
    s ⊆ s' -> e ∈ restrict_key k s -> e ∈ restrict_key k s'.
  Proof.
    intros Hss' Hrk.
    apply elem_of_filter.
    apply elem_of_filter in Hrk.
    set_solver.
  Qed.

End events.

Section spec.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events,
            !DB_resources Mdl Σ, !Maximals_Computing}.

  Definition init_resources z i : iProp Σ :=
    (([∗ list] z ∈ DB_addresses, z ⤇ DB_socket_proto) ∗
               z ⤳ (∅, ∅) ∗
               unbound (ip_of_address z) {[port_of_address z]} ∗
               init_token i).

  Lemma Causality_2 e a s i k h E :
    nclose DB_InvName ⊆ E →
    e ∈ s →
    a ∈ h →
    a <ₜ e →
    GlobalInv ⊢ Seen i s -∗ k ↦ᵤ h ={E}=∗
                  ⌜∃ e, e ∈ restrict_key k s ∧ erasure e = a⌝ ∗ k ↦ᵤ h.
  Proof.
    iIntros (????) "#HIG #Hs Hku".
    iDestruct (User_Snapshot with "Hku") as "[Hxu #Hsnap]".
    iMod (Snapshot_ext with "HIG Hsnap Hsnap") as %Hext_h; [solve_ndisj|].
    iMod (Causality with "HIG Hs Hsnap") as %Hcaus; [solve_ndisj|].
    iModIntro. iFrame. iPureIntro.
    by eapply Hcaus.
  Qed.

  Lemma Maximum_ghst (s : lhst) (h : gmem) (e : ae) E i k :
    nclose DB_InvName ⊆ E →
    h ⊆ erasure_set s →
    erasure e ∈ h →
    Maximum s = Some e →
    GlobalInv ⊢
      Seen i s -∗ k ↦ᵤ h ={E}=∗ ⌜Maximum h = Some (erasure e)⌝ ∗ k ↦ᵤ h.
  Proof.
    iIntros (??? Hmax) "#HIG #Hs Hku".
    iMod (Seen_strong_ext with "HIG Hs Hs") as %Hext_s; [solve_ndisj|].
    iDestruct (User_Snapshot with "Hku") as "[Hku #Hsnap]".
    iMod (Snapshot_ext with "HIG Hsnap Hsnap") as %Hext_h; [solve_ndisj|].
    iModIntro. iFrame. iPureIntro.
    apply Maximum_correct; [done|].
    split; [done|]. intros a Ha Hneq.
    destruct (Maximum_correct_2 _ _ Hext_s Hmax) as [? Hs_lt].
    assert (∃ e', a = erasure e' ∧ e' ∈ s) as [e' [-> ?]].
    { apply elem_of_erasure_set. set_solver. }
    rewrite !erasure_time. apply Hs_lt; [set_solver|].
    destruct (decide (e' = e)); by [|subst].
  Qed.

  Lemma Maximum_lhst_gt e1 e2 s E i :
    nclose DB_InvName ⊆ E →
    e1 ≠ e2 →
    e1 ∈ s →
    Maximum s = Some e2 →
    GlobalInv ⊢ Seen i s ={E}=∗ ⌜erasure e1 <ₜ erasure e2⌝.
  Proof.
    iIntros (??? Hmax) "#HIG #Hs".
    iMod (Seen_strong_ext with "HIG Hs Hs") as %Hext; [done|].
    iModIntro. iPureIntro.
    rewrite !erasure_time.
    apply Maximum_correct in Hmax; [|done].
    destruct Hmax as [? Hs_lt].
    by apply Hs_lt.
  Qed.

  Lemma Maximum_elem_of_ghst a k h E :
    nclose DB_InvName ⊆ E →
    Maximum h = Some a →
    GlobalInv ⊢ k ↦ᵤ h ={E}=∗ ⌜a ∈ h⌝ ∗ k ↦ᵤ h.
  Proof.
    iIntros (? Hmax) "#HIG Hku".
    iDestruct (User_Snapshot with "Hku") as "[Hxu #Hsnap]".
    iMod (Snapshot_ext with "HIG Hsnap Hsnap") as %Hext_h; [solve_ndisj|].
    destruct (Maximum_correct_2 _ _ Hext_h Hmax) as [??]; auto.
  Qed.

  Lemma Maximum_causality e s a i k h E :
    nclose DB_InvName ⊆ E →
    e ∈ s →
    a <ₜ e →
    Maximum h = Some a →
    GlobalInv ⊢ Seen i s -∗ k ↦ᵤ h ={E}=∗
                  ⌜∃ e, e ∈ restrict_key k s ∧ erasure e = a⌝ ∗ k ↦ᵤ h.
  Proof.
    iIntros (??? Hmax) "#HIG #Hs Hku".
    iMod (Maximum_elem_of_ghst with "HIG Hku") as "[% Hku]"; [done|done|].
    by iApply (Causality_2 with "HIG Hs Hku").
  Qed.

  Lemma Maximum_maximals_val_agree  (e1 e2 : ae) i s k h E :
    nclose DB_InvName ⊆ E →
    Maximum h = Some (erasure e1) →
    e1 ∈ restrict_key k s →
    e2 ∈ Maximals (restrict_key k s) →
    erasure e2 ∈ h →
    GlobalInv ⊢ Seen i s -∗ k ↦ᵤ h ={E}=∗ ⌜AE_val e1 = AE_val e2⌝ ∗ k ↦ᵤ h.
  Proof.
    iIntros (? Hmax_h He1_s Hmaxi_s He2_h) "#HIG #Hs Hku".
    iDestruct (User_Snapshot with "Hku") as "[Hxu #Hsnap]".
    iMod (Snapshot_ext with "HIG Hsnap Hsnap") as %Hext_h; [done|].
    iMod (Causality with "HIG Hs Hsnap") as %Hcaus; [done|].
    iModIntro. iFrame. iPureIntro.
    destruct (Maximum_correct_2 _ _ Hext_h Hmax_h) as [He1 Hh_lt_a].
    destruct (Maximals_correct_2 _ _ Hmaxi_s) as [? He_nlt].
    rewrite -!erasure_val.
    destruct (decide (erasure e2 = erasure e1)) as [-> | Heq]; [done|].
    exfalso.
    apply (He_nlt _ He1_s).
    rewrite -!erasure_time.
    by apply Hh_lt_a.
  Qed.

End spec.
