From stdpp Require Export base list.
From aneris.aneris_lang Require Import lang tactics proofmode.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang.lib Require Import network_util_proof list_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.prelude Require Import time.
From aneris.prelude Require Import misc strings.
From aneris.aneris_lang.lib Require Export vector_clock_code.

Section vect_specs.
  Context `{!anerisG Mdl Σ}.

  Definition is_vc (v : val) (t : vector_clock) := is_list t v.

  Lemma vector_clock_to_val_is_vc t : is_vc (vector_clock_to_val t) t.
  Proof.
    induction t; simpl; first done.
    eexists _; split; done.
  Qed.

  Lemma is_vc_vector_clock_to_val v t : is_vc v t → vector_clock_to_val t = v.
  Proof.
    revert v; induction t as [|? t IHt]; intros v; simpl; first done.
    intros [? [-> ?]]; erewrite IHt; done.
  Qed.

  Lemma wp_vect_make ip len (init : nat):
    {{{ True }}}
      vect_make #len $init @[ip]
    {{{ v, RET v; ⌜is_vc v (replicate len init)⌝ }}}.
  Proof.
    revert len. iLöb as "IH". iIntros (len Φ) "_ HΦ".
    wp_rec. wp_pures. case_bool_decide; wp_if.
    - iApply (wp_list_nil _); [done|].
      iNext; iIntros (v) "%".
      iApply "HΦ".
      assert (len = 0%nat) by lia; simplify_eq. done.
    - wp_pures. wp_bind ((vect_make _ _)).
      assert (((Z.of_nat len) - 1)%Z = Z.of_nat (len - 1)) as -> by lia.
      iApply "IH"; first done.
      iNext. iIntros (? Hcoh) "/=".
      wp_apply (wp_list_cons $! Hcoh).
      iIntros (w) "%".
      iApply "HΦ". iPureIntro.
      assert (∃ n, len = S n) as [m Hlen'].
      { exists (len - 1)%nat; lia. }
      rewrite Hlen' replicate_S.
      by assert (m = (len - 1)%nat) as -> by lia.
  Qed.

  Lemma wp_vect_nth ip v (i : nat) t :
    i < length t →
    {{{ ⌜is_vc v t⌝ }}}
      vect_nth v #i @[ip]
    {{{ v, RET v; ⌜∃ (j : nat), v = #j ∧ t !! i = Some j⌝ }}}.
  Proof.
    iIntros (Hlen Φ Hcoh) "HΦ".
    wp_rec. wp_pures. wp_bind (list_nth _ _).
    iApply wp_list_nth_some.
    { iPureIntro. eauto. }
    iNext; iIntros (w [k [-> H]]) "/=".
    iApply wp_unSOME; first done.
    iNext; iIntros "_".
    iApply "HΦ". iPureIntro.
    apply nth_error_lookup in H.
    eauto.
  Qed.

  Lemma wp_vect_update ip v t (i j : nat) :
    i < length t →
    {{{ ⌜is_vc v t⌝ }}}
      vect_update v #i #j @[ip]
    {{{ v, RET v; ⌜is_vc v (<[i := j]> t)⌝ }}}.
  Proof.
    iLöb as "IH" forall (v t i).
    iIntros (Hi Φ Hcoh) "HΦ".
    wp_rec; wp_let; wp_let. destruct t as [|x t].
    - rewrite Hcoh. wp_pures. by iApply "HΦ".
    - destruct Hcoh as [k [H' Hl']].
      rewrite H'. wp_pures. case_bool_decide; wp_pures.
      + wp_bind (list_tail _).
        iApply (wp_list_tail _ _ (x :: t)).
        { iPureIntro. eexists; eauto. }
        iNext. iIntros (tm Htm) "/=".
        iApply (wp_list_cons $! Htm).
        iNext. iIntros (u Hu) "/=".
        iApply "HΦ"; iPureIntro.
        assert (i = 0)%nat as -> by lia.
        repeat split; auto.
      + wp_bind (vect_update _ _ _).
        assert (((Z.of_nat i) - 1)%Z = Z.of_nat (i - 1)) as -> by lia.
        iApply ("IH" $! _ t).
        { iPureIntro; simpl in *; lia. }
        { iPureIntro; done. }
        destruct i; first done; simpl.
        rewrite !Nat.sub_0_r.
        iNext; iIntros (tm Htm) "/=". wp_pures.
        iApply (wp_list_cons $! Htm).
        iNext; iIntros (? ?).
        by iApply "HΦ".
  Qed.

  Lemma wp_vect_inc ip v t (i j : nat) :
    i < length t →
    t !! i = Some j →
    {{{ ⌜is_vc v t⌝ }}}
      vect_inc v #i @[ip]
    {{{ v, RET v; ⌜is_vc v (incr_time t i)⌝ }}}.
  Proof.
    iIntros (Hi Hj Φ Hcoh) "HΦ".
    wp_rec. wp_pures. wp_bind (vect_nth _ _).
    iApply wp_vect_nth; eauto.
    iNext; iIntros (w [j' [-> Hj']]) "/=". simplify_eq. wp_pures.
    assert (((Z.of_nat j) + 1)%Z = Z.of_nat (S j)) as -> by lia.
    rewrite /incr_time Hj /=.
    iApply wp_vect_update; eauto.
  Qed.

  Lemma wp_vect_leq ip v1 v2 (l1 l2 : list nat) :
    {{{ ⌜is_vc v1 l1⌝ ∗ ⌜is_vc v2 l2⌝ }}}
      vect_leq v1 v2 @[ip]
    {{{ v, RET #v; ⌜v = bool_decide (vector_clock_le l1 l2)⌝ }}}.
  Proof.
    iLöb as "IH" forall (v1 v2 l1 l2).
    iIntros (Φ [Hl1 Hl2]) "HΦ".
    wp_rec. wp_pures. destruct l1 as [|a1 l1].
    - rewrite Hl1.
      destruct l2.
      + rewrite Hl2.
        wp_pures.
        iApply (wp_list_is_empty []); first done.
        iNext; iIntros (v ->).
        iApply "HΦ".
        rewrite bool_decide_eq_true_2; last constructor; done.
      + destruct Hl2 as (? & -> & Hl2).
        wp_pures.
        iApply (wp_list_is_empty (n :: _)).
        { iPureIntro; eexists; eauto. }
        iNext. iIntros (v ->).
        iApply "HΦ".
        by rewrite bool_decide_eq_false_2; last by inversion 1.
    - destruct Hl1 as [? [-> H]]. wp_pures. destruct l2 as [|a2 l2].
      + rewrite Hl2. wp_pures. iApply "HΦ".
        by rewrite bool_decide_eq_false_2; last by inversion 1.
      + destruct Hl2 as [? [-> ?]]. wp_pures.
        destruct (decide (a1 ≤ a2)%Z).
        * rewrite (bool_decide_eq_true_2 (a1 ≤ a2)%Z); last done.
          wp_pures.
          iApply "IH".
          { iSplit; iPureIntro; eauto. }
          iNext. iIntros (??).
          iApply "HΦ".
          assert (a1 ≤ a2)%nat by lia.
          destruct (decide (vector_clock_le l1 l2)).
          -- simplify_eq.
             by rewrite /= !bool_decide_eq_true_2; [done| constructor |done].
          -- simplify_eq.
             rewrite /= !bool_decide_eq_false_2; [done|by inversion 1|done].
        * rewrite (bool_decide_eq_false_2 (a1 ≤ a2)%Z); last done.
          wp_pures.
          iApply "HΦ".
          rewrite /= bool_decide_eq_false_2; first done.
          inversion 1; simplify_eq. lia.
  Qed.

  Lemma wp_vect_applicable ip v1 v2 (l1 l2 : list nat) (i : nat) :
    {{{ ⌜is_vc v1 l1⌝ ∗ ⌜is_vc v2 l2⌝ }}}
      vect_applicable v1 v2 #i @[ip]
    {{{ (b : bool), RET #b;
        if b then
          ⌜length l1 = length l2⌝ ∧
          ⌜option_Forall2 (λ x1 x2, x1 = x2 + 1)%nat (l1 !! i) (l2 !! i)⌝ ∧
          ⌜∀ j (x1 x2 : nat),
          i ≠ j →
          l1 !! j = Some x1 →
          l2 !! j = Some x2 →
          x1 ≤ x2⌝
        else
          True
    }}}.
  Proof.
    iIntros (Φ) "[Hl1 Hl2] HΦ".
    iDestruct "Hl1" as %Hl1.
    iDestruct "Hl2" as %Hl2.
    rewrite /vect_applicable.
    wp_lam; do 2 wp_let. wp_pure _.
    wp_closure.
    wp_pure _.
    pose (j := 0%nat).
    assert (j = 0%nat) as Hj0 by done.
    replace #0 with #j; last first.
    { rewrite Hj0; f_equal. }
    clearbody j.
    set (Ψ := (λ a,
                ∃ b : bool,
                  ⌜a = #b⌝ ∧
                  (if b
                   then
                     ⌜length l1 = length l2⌝
                     ∧ ⌜j ≤ i →
                        option_Forall2 (λ x1 x2 : nat, x1 = (x2 + 1)%nat)
                           (l1 !! (i - j)%nat) (l2 !! (i - j)%nat)⌝
                     ∧ ⌜∀ k x1 x2 : nat, ((i - j)%nat ≠ k ∨ j > i) → l1 !! k = Some x1 → l2 !! k =
                         Some x2 → x1 ≤ x2⌝
                   else True))%I : val → iProp Σ).
    iApply (aneris_wp_wand _ _ _ Ψ with "[] [HΦ]")%I; last first.
    { iIntros (v); rewrite /Ψ /=.
      iIntros "Hb".
      iDestruct "Hb" as (b) "[-> Hb]".
      iApply "HΦ".
      destruct b; auto with lia.
      replace (i - j)%nat with i by lia.
      iDestruct "Hb" as "(Hb1 & Hb2 & Hb3)".
      iDestruct "Hb1" as %Hb1.
      iDestruct "Hb2" as %Hb2.
      iDestruct "Hb3" as %Hb3.
      eauto 10 with lia. }
    rewrite /Ψ; clear Ψ Hj0.
    iInduction l1 as [|x1 l1] "IHl1" forall (j v1 v2 Hl1 l2 Hl2).
    { rewrite Hl1.
      wp_pures.
      wp_apply (wp_list_is_empty l2); [done|].
      iIntros (? ->).
      destruct l2; simpl; last by iExists false.
      iExists true.
      repeat iSplit; iPureIntro; [done|done| |].
      - rewrite lookup_nil; constructor.
      - by intros ? ? ? ?; rewrite lookup_nil. }
    destruct Hl1 as (v1'&->&?).
    wp_pures.
    destruct l2 as [|x2 l2].
    { rewrite Hl2; wp_pures.
      iExists false; iSplit; done. }
    destruct Hl2 as (v2'&->&?).
    wp_pures.
    destruct (decide (j = i)) as [->|].
    { rewrite bool_decide_eq_true_2; last done.
      wp_pures.
      destruct (decide (x1 = x2 + 1)%nat) as [->|]; last first.
      { rewrite bool_decide_eq_false_2; last lia.
        wp_pures.
        iExists false; iSplit; done. }
      rewrite bool_decide_eq_true_2; last lia.
      wp_if.
      do 2 wp_proj.
      wp_op.
      replace (i + 1)%Z with ((i + 1)%nat : Z); last lia.
      iApply aneris_wp_mono; last iApply "IHl1"; [|done|done].
      iIntros (v) "Hb".
      iDestruct "Hb" as (b) "[-> Hb]".
      iExists b; iSplit; first done.
      destruct b; last done.
      iDestruct "Hb" as "(Hb1 & Hb2 & Hb3)".
      iDestruct "Hb1" as %Hb1.
      iDestruct "Hb2" as %Hb2.
      iDestruct "Hb3" as %Hb3.
      repeat iSplit.
      - by rewrite /= Hb1.
      - iPureIntro.
        intros _.
        replace (i - i)%nat with 0%nat by lia; simpl.
        constructor; done.
      - iPureIntro.
        intros k z1 z2 Hk.
        destruct k; first lia; simpl.
        apply Hb3. lia. }
    rewrite bool_decide_eq_false_2; last lia.
    wp_pures.
    destruct (decide (x1 ≤ x2)).
    { rewrite bool_decide_eq_true_2; last lia.
      wp_if.
      do 2 wp_proj.
      wp_op.
      replace (j + 1)%Z with ((j + 1)%nat : Z); last lia.
      iApply aneris_wp_mono; last iApply "IHl1"; [|done|done].
      iIntros (v) "Hb".
      iDestruct "Hb" as (b) "[-> Hb]".
      iExists b; iSplit; first done.
      destruct b; last done.
      iDestruct "Hb" as "(%Hb1 & %Hb2 & %Hb3)".
      repeat iSplit.
      - by rewrite /= Hb1.
      - iPureIntro.
        intros Hji.
        destruct (i - j)%nat as [|k] eqn:Hk; simpl; first lia.
        replace (i - (j + 1))%nat with k in Hb2 by lia; auto with lia.
      - iPureIntro.
        intros k z1 z2 Hk.
        destruct k; first by simpl; intros ? ?; simplify_eq.
        apply Hb3; lia. }
    rewrite bool_decide_eq_false_2; last lia.
    wp_pures.
    iExists false; done.
  Qed.

End vect_specs.

Arguments is_vc : simpl never.

Fixpoint vc_to_string (l : vector_clock) : string :=
  match l with
  | [] => ""
  | a::l' => StringOfZ a +:+ "_" ++ vc_to_string l'
  end.

Definition vc_valid_val (v : val) :=
  ∃ l, is_vc v l.

Definition vc_is_ser (v : val) (s : string) :=
  ∃ l, is_vc v l ∧ s = vc_to_string l.

Lemma vc_is_ser_valid v s : vc_is_ser v s -> vc_valid_val v.
Proof.
  intros [l [Hvc _]].
  rewrite /vc_valid_val; eauto.
Qed.

Definition wp_vect_serialize `{!anerisG Mdl Σ} ip v:
  {{{ ⌜vc_valid_val v⌝ }}}
    vect_serialize v @[ip]
  {{{ s, RET #s; ⌜vc_is_ser v s⌝ }}}.
Proof.
  iIntros (Φ) "Hv HΦ". iLöb as "IH" forall (Φ v).
  wp_rec. iDestruct "Hv" as %[l Hv].
  destruct l as [|a l].
  - rewrite Hv. wp_pures.
    iApply "HΦ".
    iPureIntro.
    rewrite /vc_is_ser; eexists []; done.
  - destruct Hv as [w [-> Hw]].
    wp_pures. wp_bind (vect_serialize _).
    iApply "IH"; [iPureIntro; eexists; done |].
    iIntros "!>" (s) "Hs /=".
    iDestruct "Hs" as %(?&?&->).
    wp_pures.
    iApply "HΦ".
    iPureIntro; eexists (_ :: _); simpl; split; first eexists _; eauto.
Qed.

Definition wp_vect_deserialize `{!anerisG Mdl Σ} ip v s:
  {{{ ⌜vc_is_ser v s⌝ }}}
    vect_deserialize #s @[ip]
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ) "Hs HΦ". iLöb as "IH" forall (Φ v s).
  wp_rec. iDestruct "Hs" as %(l&Hl&->).
  destruct l as [|a l]; simpl.
  - rewrite Hl.
    wp_find_from; first by split_and!; [|by apply nat_Z_eq; first lia].
    wp_pures.
    iApply "HΦ"; done.
  - destruct Hl as [w [-> Hl]].
    wp_find_from; first by split_and!; [|by apply nat_Z_eq; first lia].
    erewrite (index_0_append_char ); auto; last first.
    { apply valid_tag_stringOfZ. }
    wp_pures.
    wp_substring; first by split_and!; [|by apply nat_Z_eq; first lia|done].
    rewrite substring_0_length_append.
    wp_pure _.
    { simpl. rewrite ZOfString_inv //. }
    wp_apply wp_unSOME; [done|].
    iIntros "_ /=". wp_pures.
    rewrite !length_app.
    wp_substring;
      first by split_and!;
        [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
    match goal with
    | |- context [substring ?X ?Y _] =>
      replace X with (String.length (StringOfZ a) + 1)%nat by lia;
        replace Y with (String.length (vc_to_string l)) by lia
    end.
    rewrite substring_add_length_app substring_Sn /=.
    rewrite substring_0_length.
    wp_apply "IH"; [iPureIntro; exists l; done|].
    iIntros "_ /=". wp_pures.
    wp_apply (wp_list_cons $! Hl).
    iIntros (? [u [-> Hu]]).
    rewrite (is_list_eq _ _ _ Hl Hu).
    iApply "HΦ"; done.
Qed.

Definition vc_serialization : serialization :=
  {| s_valid_val := vc_valid_val;
     s_serializer := vect_serializer;
     s_is_ser := vc_is_ser;
     s_is_ser_valid := vc_is_ser_valid;
     s_ser_spec := @wp_vect_serialize;
     s_deser_spec := @wp_vect_deserialize; |}.

Lemma vc_to_string_inj l1 l2 : vc_to_string l1 = vc_to_string l2 → l1 = l2.
Proof.
  revert l2; induction l1 as [|a l1 IHl1]; intros l2; intros Heq.
  { destruct l2; simpl; first done.
    pose proof (f_equal String.length Heq) as Heq'.
    rewrite length_app /= in Heq'; lia. }
  destruct l2 as [|b l2].
  { pose proof (f_equal String.length Heq) as Heq'.
    rewrite length_app /= in Heq'; lia. }
  simpl in *.
  destruct (Nat.lt_trichotomy (String.length (StringOfZ a)) (String.length (StringOfZ b)))
    as [|[Hleneq|]].
  - pose proof (f_equal (get (String.length (StringOfZ a))) Heq) as Heq'.
    change (String.length (StringOfZ a)) with (0 + (String.length (StringOfZ a)))%nat in Heq' at 1.
    rewrite -append_correct2 /= in Heq'.
    rewrite -append_correct1 in Heq'; last done.
    exfalso; eapply get_StringOfZ_ne; last eauto; done.
  - pose proof (f_equal (λ s, substring 0 (String.length (StringOfZ a)) s) Heq) as Heq'.
    rewrite /= substring_0_length_append Hleneq substring_0_length_append in Heq'.
    pose proof (f_equal ZOfString Heq') as Heq''.
    rewrite !ZOfString_inv in Heq''; simplify_eq.
    erewrite IHl1; done.
  - pose proof (f_equal (get (String.length (StringOfZ b))) Heq) as Heq'.
    change (String.length (StringOfZ b)) with (0 + (String.length (StringOfZ b)))%nat in Heq' at 2.
    rewrite -append_correct2 /= in Heq'.
    rewrite -append_correct1 in Heq'; last done.
    exfalso; eapply get_StringOfZ_ne; last eauto; done.
Qed.

Lemma vc_is_ser_inj v1 s1 v2 s2 : vc_is_ser v1 s1 → vc_is_ser v2 s2 → s1 = s2 → v1 = v2.
Proof.
  intros [l1 [Hl1 ->]] [l2 [Hl2 ->]].
  apply is_vc_vector_clock_to_val in Hl1 as <-.
  apply is_vc_vector_clock_to_val in Hl2 as <-.
  intros ->%vc_to_string_inj; done.
Qed.
