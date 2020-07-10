From stdpp Require Export base list.
From aneris Require Import lang lifting tactics proofmode notation adequacy.
From aneris.aneris_lang.lib Require Export util network_helpers list.
From aneris.aneris_lang.lib.serialization Require Export serialization.
From aneris.aneris_lang.lib.vector_clock Require Export time.

Section vect_code.

  Definition vect_make : ground_lang.val :=
    rec: "vect_make" "len" "init" :=
      if: "len" = #0 then list_make #()
      else list_cons "init" ("vect_make" ("len" - #1) "init").

  Definition vect_nth : ground_lang.val :=
    λ: "vec" "i", unSOME (list_nth "vec" "i").

  Definition vect_update : ground_lang.val :=
    rec: "vect_update" "vec" "i" "v" :=
      match: "vec" with
        SOME "a" =>
           if: "i" = #0 then list_cons "v" (list_tail "vec")
           else list_cons (Fst "a") ("vect_update" (Snd "a") ("i" - #1) "v")
        | NONE => NONE
      end.

  Definition vect_inc : ground_lang.val :=
    λ: "vec" "i",
      let: "v" := (vect_nth "vec" "i") + #1
      in vect_update "vec" "i" "v".

  Definition vect_leq : ground_lang.val :=
    rec: "vect_leq" "v1" "v2" :=
      match: "v1" with
        SOME "a1" => match: "v2" with
                       SOME "a2" =>
                       (Fst "a1" ≤ Fst "a2") && "vect_leq" (Snd "a1") (Snd "a2")
                     | NONE => #false
                     end
      | NONE => list_is_empty "v2"
      end.

  Definition vect_applicable : ground_lang.val :=
    λ: "v1" "v2" "i",
    (rec: "vect_applicable" "j" "v1" "v2" :=
       match: "v1" with
         SOME "a1" => match: "v2" with
                       SOME "a2" =>
                       (if: "j" = "i" then
                          ((Fst "a1") = Fst "a2" + #1)
                        else
                          (Fst "a1" ≤ Fst "a2"))
                       && "vect_applicable" ("j" + #1) (Snd "a1") (Snd "a2")
                     | NONE => #false
                     end
       | NONE => list_is_empty "v2"
       end) #0 "v1" "v2".

  Definition vect_serialize : ground_lang.val :=
    rec: "vect_serialize" "v" :=
      match: "v" with
        SOME "a" => i2s (Fst "a") ^^ #"_" ^^ "vect_serialize" (Snd "a")
      | NONE => #""
      end.

  Definition vect_deserialize : ground_lang.val :=
    rec: "vect_deserialize" "s" :=
      match: FindFrom "s" #0 #"_" with
        SOME "i" =>
          let: "x"  := unSOME (s2i (Substring "s" #0 "i")) in
          let: "tail" :=
            let: "length" := UnOp StringLength "s" in
            let: "start" := "i" + #1 in
            "vect_deserialize" (Substring "s" "start" ("length" - "start")) in
          list_cons "x" "tail"
      | NONE => list_make #()
      end.

End vect_code.

Section vect_specs.
  Context `{!distG Σ}.

  Definition is_vc (v : ground_lang.val) (t : vector_clock) :=
    list_coh (map (λ (n : nat), #n) t) v.

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

  Lemma vect_make_spec n len (init : nat):
    {{{ True }}}
      ⟨n; vect_make #len #init⟩
    {{{ v, RET 〈n;v〉; ⌜is_vc v (replicate len init)⌝ }}}.
  Proof.
    revert len. iLöb as "IH". iIntros (len Φ) "_ HΦ".
    wp_rec. wp_pures. case_bool_decide; wp_if.
    - iApply list_make_spec; [done|].
      iNext; iIntros (v) "%".
      iApply "HΦ".
      assert (len = 0%nat) by lia; simplify_eq. done.
    - wp_pures. wp_bind ((vect_make _ _)).
      assert (((Z.of_nat len) - 1)%Z = Z.of_nat (len - 1)) as -> by lia.
      iApply "IH"; first done.
      iNext. iIntros (? Hcoh) "/=".
      iApply list_cons_spec; [done|].
      iNext; iIntros (w) "%".
      iApply "HΦ". iPureIntro.
      assert (∃ n, len = S n) as [m Hlen'].
      { exists (len - 1)%nat; lia. }
      rewrite Hlen' replicate_S.
      by assert (m = (len - 1)%nat) as -> by lia.
  Qed.

  Lemma vect_nth_spec n v (i : nat) t :
    i < length t →
    {{{ ⌜is_vc v t⌝ }}}
      ⟨n; vect_nth v #i⟩
    {{{ v, RET 〈n;v〉; ⌜∃ (j : nat), v = #j ∧ t !! i = Some j⌝ }}}.
  Proof.
    iIntros (Hlen Φ Hcoh) "HΦ".
    wp_rec. wp_pures. wp_bind (list_nth _ _).
    iApply (list_nth_spec_some).
    { iPureIntro. split; eauto.
      rewrite map_length. lia. }
    iNext; iIntros (w [k [-> H]]) "/=".
    iApply unSOME_spec; first done.
    iNext; iIntros "_".
    iApply "HΦ". iPureIntro.
    apply nth_error_lookup in H.
    by apply map_lookup_Some in H.
  Qed.

  Lemma vect_update_spec n v t (i j : nat) :
    i < length t →
    {{{ ⌜is_vc v t⌝ }}}
      ⟨n; vect_update v #i #j⟩
    {{{ v, RET 〈n;v〉; ⌜is_vc v (<[i := j]> t)⌝ }}}.
  Proof.
    iLöb as "IH" forall (v t i).
    iIntros (Hi Φ Hcoh) "HΦ".
    wp_rec; wp_let; wp_let. destruct t as [|x t].
    - rewrite Hcoh. wp_pures. by iApply "HΦ".
    - destruct Hcoh as [k [H' Hl']].
      rewrite H'. wp_pures. case_bool_decide; wp_pures.
      + wp_bind (list_tail _).
        iApply (list_tail_spec _ _ (#x :: (map (λ n : nat, #n) t))).
        { iPureIntro. eexists; eauto. }
        iNext. iIntros (tm Htm) "/=".
        iApply (list_cons_spec $! Htm).
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
        iApply (list_cons_spec $! Htm).
        iNext; iIntros (? ?).
        by iApply "HΦ".
  Qed.

  Lemma vect_inc_spec n v t (i j : nat) :
    i < length t →
    t !! i = Some j →
    {{{ ⌜is_vc v t⌝ }}}
      ⟨n; vect_inc v #i⟩
    {{{ v, RET 〈n;v〉; ⌜is_vc v (incr_time t i)⌝ }}}.
  Proof.
    iIntros (Hi Hj Φ Hcoh) "HΦ".
    wp_rec. wp_pures. wp_bind (vect_nth _ _).
    iApply vect_nth_spec; eauto.
    iNext; iIntros (w [j' [-> Hj']]) "/=". simplify_eq. wp_pures.
    assert (((Z.of_nat j) + 1)%Z = Z.of_nat (S j)) as -> by lia.
    rewrite /incr_time Hj /=.
    iApply vect_update_spec; eauto.
  Qed.

  Lemma vect_leq_spec n v1 v2 (l1 l2 : list nat) :
    {{{ ⌜is_vc v1 l1⌝ ∗ ⌜is_vc v2 l2⌝ }}}
      ⟨n; vect_leq v1 v2⟩
    {{{ v, RET 〈n;#v〉; ⌜v = bool_decide (vector_clock_le l1 l2)⌝ }}}.
  Proof.
    iLöb as "IH" forall (v1 v2 l1 l2).
    iIntros (Φ [Hl1 Hl2]) "HΦ".
    wp_rec. wp_pures. destruct l1 as [|a1 l1].
    - rewrite Hl1.
      destruct l2.
      + rewrite Hl2.
        wp_pures.
        iApply (list_is_empty_spec _ []); first done.
        iNext; iIntros (v ->).
        iApply "HΦ".
        rewrite bool_decide_eq_true_2; last constructor; done.
      + destruct Hl2 as (? & -> & Hl2).
        wp_pures.
        iApply (list_is_empty_spec _ (_ :: _));
          first by iPureIntro; eexists; eauto.
        iNext; iIntros (v ->).
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

  Lemma vect_applicable_spec n v1 v2 (l1 l2 : list nat) (i : nat) :
    {{{ ⌜is_vc v1 l1⌝ ∗ ⌜is_vc v2 l2⌝ }}}
      ⟨n; vect_applicable v1 v2 #i⟩
    {{{ (b : bool), RET 〈n;#b〉;
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
    wp_lam; do 2 wp_let.
    wp_closure.
    pose (j := 0%nat).
    assert (j = 0) as Hj0 by done.
    replace #0 with #j; last first.
    { rewrite Hj0; f_equal. }
    clearbody j.
    set (Ψ := (λ a, ⌜a.(val_n) = n⌝ ∗
                ∃ b : bool,
                  ⌜a.(val_e) = #b⌝ ∧
                  (if b
                   then
                     ⌜length l1 = length l2⌝
                     ∧ ⌜j ≤ i →
                        option_Forall2 (λ x1 x2 : nat, x1 = (x2 + 1)%nat)
                           (l1 !! (i - j)) (l2 !! (i - j))⌝
                     ∧ ⌜∀ k x1 x2 : nat, (i - j ≠ k ∨ j > i) → l1 !! k = Some x1 → l2 !! k =
                         Some x2 → x1 ≤ x2⌝
                   else True))%I : aneris_lang.val → iProp Σ).
    iApply (wp_wand _ _ _ Ψ with "[] [HΦ]")%I; last first.
    { iIntros ([]); rewrite /Ψ /=.
      iIntros "[-> Hb]".
      iDestruct "Hb" as (b) "[-> Hb]".
      iApply "HΦ".
      destruct b; auto with lia.
      replace (i - j) with i by lia.
      iDestruct "Hb" as "(Hb1 & Hb2 & Hb3)".
      iDestruct "Hb1" as %Hb1.
      iDestruct "Hb2" as %Hb2.
      iDestruct "Hb3" as %Hb3.
      eauto 10 with lia. }
    rewrite /Ψ; clear Ψ Hj0.
    iInduction l1 as [|x1 l1] "IHl1" forall (j v1 v2 Hl1 l2 Hl2).
    { rewrite Hl1.
      wp_pures.
      iApply list_is_empty_spec; first done.
      iNext. iIntros (? ->).
      iSplit; first done.
      destruct l2; simpl; last by iExists false.
      iExists true.
      repeat iSplit; iPureIntro; [done|done| |].
      - rewrite lookup_nil; constructor.
      - by intros ? ? ? ?; rewrite lookup_nil. }
    destruct Hl1 as (v1'&->&?).
    wp_pures.
    destruct l2 as [|x2 l2].
    { rewrite Hl2; wp_pures.
      iSplit; first done.
      iExists false; iSplit; done. }
    destruct Hl2 as (v2'&->&?).
    wp_pures.
    destruct (decide (j = i)) as [->|].
    { rewrite bool_decide_eq_true_2; last done.
      wp_pures.
      destruct (decide (x1 = x2 + 1)) as [->|]; last first.
      { rewrite bool_decide_eq_false_2; last lia.
        wp_pures.
        iSplit; first done.
        iExists false; iSplit; done. }
      rewrite bool_decide_eq_true_2; last lia.
      wp_if.
      do 2 wp_proj.
      wp_op.
      replace (i + 1)%Z with ((i + 1)%nat : Z); last lia.
      iApply wp_mono; last iApply "IHl1"; [|done|done].
      iIntros (v) "[-> Hb]".
      iDestruct "Hb" as (b) "[-> Hb]".
      iSplit; first done.
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
        replace (i - i) with 0 by lia; simpl.
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
      iApply wp_mono; last iApply "IHl1"; [|done|done].
      iIntros (v) "[-> Hb]".
      iDestruct "Hb" as (b) "[-> Hb]".
      iSplit; first done.
      iExists b; iSplit; first done.
      destruct b; last done.
      iDestruct "Hb" as "(Hb1 & Hb2 & Hb3)".
      iDestruct "Hb1" as %Hb1.
      iDestruct "Hb2" as %Hb2.
      iDestruct "Hb3" as %Hb3.
      repeat iSplit.
      - by rewrite /= Hb1.
      - iPureIntro.
        intros Hji.
        destruct (i - j) as [|k] eqn:Hk; simpl; first lia.
        replace (i - (j + 1)) with k in Hb2 by lia; auto with lia.
      - iPureIntro.
        intros k z1 z2 Hk.
        destruct k; first by simpl; intros ? ?; simplify_eq.
        apply Hb3; lia. }
    rewrite bool_decide_eq_false_2; last lia.
    wp_pures.
    iSplit; first done.
    iExists false; done.
  Qed.

End vect_specs.

Arguments is_vc : simpl never.


Fixpoint vc_to_string (l : vector_clock) : string :=
  match l with
  | [] => ""
  | a::l' => StringOfZ a +:+ "_" ++ vc_to_string l'
  end.

Definition vc_valid_val (v : ground_lang.val) :=
  ∃ l, is_vc v l.

Definition vc_is_ser (v : ground_lang.val) (s : string) :=
  ∃ l, is_vc v l ∧ s = vc_to_string l.

Definition vect_serialize_spec `{!distG Σ} n v:
  {{{ ⌜vc_valid_val v⌝ }}}
    ⟨n; vect_serialize v⟩
  {{{ s, RET 〈n; #s〉; ⌜vc_is_ser v s⌝ }}}.
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
    rewrite -assoc //.
    iPureIntro; eexists (_ :: _); simpl; split; first eexists _; eauto.
Qed.

Definition vect_deserialize_spec `{!distG Σ} n v s:
  {{{ ⌜vc_is_ser v s⌝ }}}
    ⟨n; vect_deserialize #s⟩
  {{{ RET 〈n;v〉; True }}}.
Proof.
  iIntros (Φ) "Hs HΦ". iLöb as "IH" forall (Φ v s).
  wp_rec. iDestruct "Hs" as %(l&Hl&->).
  destruct l as [|a l]; simpl.
  - rewrite Hl.
    wp_find_from; first by split_and!; [|by apply nat_Z_eq; first lia].
    wp_pures.
    iApply list_make_spec; first done.
    iNext. iIntros (?) "->".
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
    wp_apply unSOME_spec; [done|].
    iIntros "_ /=". wp_pures.
    rewrite !length_app.
    wp_substring;
      first by split_and!;
        [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
    match goal with
    | |- context [substring ?X ?Y _] =>
      replace X with (String.length (StringOfZ a) + 1) by lia;
        replace Y with (String.length (vc_to_string l)) by lia
    end.
    rewrite substring_add_length_app substring_Sn /=.
    rewrite substring_0_length.
    wp_apply "IH"; [iPureIntro; exists l; done|].
    iIntros "_ /=". wp_pures.
    wp_apply list_cons_spec; first done.
    iIntros (? [u [-> Hu]]).
    rewrite (list_coh_eq _ _ _ Hl Hu).
    iApply "HΦ"; done.
Qed.

Definition vc_serialization : serialization :=
  {| DBS_valid_val := vc_valid_val;
     DBS_ser := vect_serialize;
     DBS_deser := vect_deserialize;
     DBS_is_ser := vc_is_ser;
     DBS_ser_spec := @vect_serialize_spec;
     DBS_deser_spec := @vect_deserialize_spec; |}.
