From stdpp Require Import base pretty.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import coq_tactics tactics.
From aneris.aneris_lang Require Import lang tactics proofmode notation network.

Set Default Proof Using "Type".

Import Network.
Import String.
Import uPred.

Section code.

  Definition tag_of_message : base_lang.val :=
    (
      λ: "msg",
      match: FindFrom "msg" #(0 : Z) #"_" with
        SOME "i" => Substring "msg" #0 "i"
      | NONE => #"UNDEFINED"
      end
    )%V.

  Definition value_of_message : base_lang.val :=
    (
      λ: "msg",
      match: FindFrom "msg" #(0 : Z) #"_" with
        SOME "i" => let: "length" := UnOp StringLength "msg" in
                    let: "start" := "i" + #1 in
                    Substring "msg" "start" ("length" - "start")
      | NONE => #"UNDEFINED"
      end
    )%V.

End code.

Section strings.

  Lemma append_nil_l s :
    "" +:+ s = s.
  Proof. done. Qed.

  Lemma append_cons s1 :
    ∀ s2 a, String a (s1 +:+ s2) = (String a s1) +:+ s2.
  Proof.
    induction s1; intros.
    - by rewrite append_nil_l.
    - rewrite -IHs1. done.
  Qed.

  Lemma append_assoc s1 s2 s3 :
    s1 +:+ s2 +:+ s3 = (s1 +:+ s2) +:+ s3.
  Proof.
    induction s1.
    - by rewrite !append_nil_l.
    - by rewrite -append_cons IHs1 append_cons.
  Qed.

  Lemma length_Sn a s :
    String.length (String a s) = S (String.length s).
  Proof. by cbn. Qed.

  Lemma length_app s1 :
    ∀ s2, String.length (s1 +:+ s2) = (String.length s1 + String.length s2)%nat.
  Proof.
   induction s1; intros.
    - by rewrite append_nil_l.
    - by rewrite -append_cons !length_Sn IHs1.
  Qed.
  Import String.
  Lemma prefix_empty_true s :
    String.prefix "" s = true.
  Proof. destruct s; cbn; auto. Qed.

  Lemma index_0_empty s :
    index 0 "" s = Some 0%nat.
  Proof. destruct s; by cbn. Qed.

  Lemma index_prefix_true s s' :
    index 0 s s' = Some 0%nat →
    String.prefix s s' = true.
  Proof.
    destruct s,s'; simpl; cbn; auto.
    - intro; inversion H.
    - intro; destruct ascii_dec.
      + destruct (String.prefix s s'); auto; destruct (index 0 _ s'); inversion H.
      + destruct (index 0 _ s'); inversion H.
  Qed.

  Lemma index_cons_0_eq a s s' :
    index 0 s s' = Some 0%nat → index 0 (String a s) (String a s') = Some 0%nat.
  Proof.
    intros Hindex.
    cbn. destruct ascii_dec.
    - assert (Hprefix: String.prefix s s' = true).
      { by apply index_prefix_true. }
        by rewrite Hprefix.
    - by destruct n.
  Qed.

  Lemma index_append_here s t :
    index 0 s (s +:+ t) = Some 0%nat.
  Proof.
    induction s.
    - apply index_0_empty.
    - apply index_cons_0_eq.
      apply IHs.
  Qed.

  Lemma index_0_append_char a t v s :
    s = String a "" →
    index 0 s t = None →
    index 0 s (t +:+ s +:+ v) = Some (String.length t).
  Proof.
    induction t; intros.
    - rewrite append_nil_l. apply index_append_here.
    - rewrite H. rewrite -append_cons. cbn.
      destruct ascii_dec; subst. cbn in H0. destruct ascii_dec.
      rewrite prefix_empty_true in H0. inversion H0.
      by destruct n.
      rewrite IHt; auto. cbn in H0. destruct ascii_dec. by destruct n.
      destruct index; auto. inversion H0.
  Qed.

  Lemma substring_0_length s :
    substring 0 (String.length s) s = s.
  Proof. induction s; simpl; auto. by rewrite IHs. Qed.

  Lemma substring_Sn a n m s :
    substring (S n) m (String a s) = substring n m s.
  Proof. induction s; destruct n,m; simpl; auto. Qed.

  Lemma substring_add_length_app n m s1 :
    ∀ s2, substring (String.length s1 + n) m (s1 +:+ s2) = substring n m s2.
  Proof. induction s1; destruct n,m; simpl; auto. Qed.

  Lemma substring_0_length_append s1 s2 :
    substring 0 (String.length s1) (s1 +:+ s2) = s1.
  Proof. apply prefix_correct, index_prefix_true, index_append_here. Qed.

  Lemma substring_length_append s1 :
    ∀ s2, substring (String.length s1) (String.length s2) (s1 +:+ s2) = s2.
  Proof.
    induction s1; intros s2.
    - rewrite append_nil_l. apply substring_0_length.
    - rewrite length_Sn substring_Sn. apply IHs1.
  Qed.

End strings.

Section library.
  Context `{dG : anerisG Σ}.

  Definition valid_tag t := index 0 "_" t = None.

  Lemma valid_tag_String c s :
    index 0 "_" (String c "") = None → valid_tag s → valid_tag (String c s).
  Proof.
    rewrite /valid_tag /=.
    repeat (case_match; try done).
  Qed.

  Lemma valid_tag_pretty_Npos p :
    valid_tag (pretty (N.pos p)).
  Proof.
    rewrite /pretty /pretty_N.
    assert (valid_tag "") as Hemp by done; revert Hemp.
    apply (λ H, N.strong_right_induction
                  (λ n, ∀ s, valid_tag s → valid_tag (pretty_N_go n s))
                  H 0%N); last done.
    { by intros ??->. }
    intros n Hn IH s Hs.
    destruct (decide (n = 0%N)); first by subst.
    rewrite pretty_N_go_step; last lia.
    destruct (decide (n < 10)%N).
    - rewrite N.div_small; last done.
      rewrite pretty_N_go_0.
      apply valid_tag_String; auto.
      rewrite /pretty_N_char.
      repeat case_match; done.
    - apply IH; first apply N.le_0_l.
      + eapply N.lt_le_trans; last apply (N.mul_div_le _ 10); last done.
        assert (n `div` 10 ≠ 0)%N.
        { by intros ?%N.div_small_iff. }
        assert (0 < n `div` 10)%N by by apply N.div_str_pos; auto with lia.
        lia.
      + apply valid_tag_String; auto.
        rewrite /pretty_N_char.
        repeat case_match; done.
  Qed.

  Lemma valid_tag_stringOfZ a :
    valid_tag (StringOfZ a).
  Proof.
    destruct a; rewrite/valid_tag /=; first done.
    apply valid_tag_pretty_Npos.
      by rewrite valid_tag_pretty_Npos.
  Qed.

  Lemma tag_of_message_spec ip (s : string) t v:
    valid_tag t →
    {{{ ⌜s = t +:+ "_" +:+ v⌝ }}}
      tag_of_message #s @[ip]
    {{{ v, RET #v; ⌜v = t⌝ }}}.
  Proof.
    iIntros (Htag Φ HP) "HΦ". rewrite /tag_of_message.
    wp_pures. wp_find_from.
    { by instantiate (1:=0%nat). }
    rewrite HP (index_0_append_char "_") /=; auto.
    wp_match. wp_substring.
    { repeat split; eauto. by instantiate (1:=0%nat). }
    rewrite substring_0_length_append. by iApply "HΦ".
  Qed.

  Lemma value_of_message_spec ip (s : string) t v :
    valid_tag t →
    {{{ ⌜s = t +:+ "_" +:+ v⌝ }}}
      value_of_message #s @[ip]
    {{{ r, RET #r; ⌜r = v⌝ }}}.
  Proof.
    iIntros (Htag Φ HP) "HΦ". rewrite /value_of_message.
    wp_pures. wp_find_from.
    { by instantiate (1:=0%nat). }
    rewrite HP (index_0_append_char "_") /=; auto.  wp_match.
    wp_pures.
    wp_substring.
    { repeat split; eauto.
      instantiate (1:=(String.length t + 1)%nat). apply Nat2Z.inj_add.
      instantiate (1:=(String.length v)%nat).
      rewrite !length_app plus_assoc length_Sn /= !Nat2Z.inj_add. ring. }
    rewrite substring_add_length_app substring_Sn substring_0_length.
      by iApply "HΦ".
  Qed.

End library.
