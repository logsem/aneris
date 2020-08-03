From iris.program_logic Require Import weakestpre.
From aneris.aneris_lang Require Import lang notation proofmode.
From aneris.aneris_lang.lib Require Import util.
From iris.algebra Require Import gmap.
From aneris.aneris_lang.lib Require Export serialization_base.
From aneris.aneris_lang.lib Require Import network_helpers assert.

Record serialization := {
  DBS_valid_val : ground_lang.val → Prop;
  DBS_ser : ground_lang.val;
  DBS_deser : ground_lang.val;
  DBS_is_ser : ground_lang.val → string → Prop;
  DBS_ser_spec :
    ∀ `{!distG Σ} ip v,
    {{{ ⌜DBS_valid_val v⌝ }}}
      DBS_ser v @[ip]
    {{{ (s : string), RET #s; ⌜DBS_is_ser v s⌝ }}};
  DBS_deser_spec :
    ∀ `{!distG Σ} ip v s,
    {{{ ⌜DBS_is_ser v s⌝ }}}
      DBS_deser #s @[ip]
    {{{ RET v; True }}}; }.

Class Serializable (s : serialization) (v : ground_lang.val) :=
  serializable : DBS_valid_val s v.

Definition int_valid_val (v : ground_lang.val) := ∃ (i : Z), v = #i.

Definition int_ser : ground_lang.val := λ: "v", i2s "v".

Definition int_deser : ground_lang.val := λ: "v", unSOME (s2i "v").

Definition int_is_ser (v : ground_lang.val) (s : string) :=
  ∃ (i : Z), v = #i ∧ s = StringOfZ i.

Lemma int_ser_spec `{!distG Σ} ip v :
  {{{ ⌜int_valid_val v⌝ }}}
    int_ser v @[ip]
  {{{ (s : string), RET #s; ⌜int_is_ser v s⌝ }}}.
Proof.
  iIntros (Φ [i ->]) "HΦ".
  rewrite /int_ser /int_is_ser.
  wp_pures.
  iApply "HΦ"; eauto.
Qed.

Lemma int_deser_spec `{!distG Σ} ip v s :
  {{{ ⌜int_is_ser v s⌝ }}}
    int_deser #s @[ip]
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ [i [-> ->]]) "HΦ".
  rewrite /int_deser /int_is_ser.
  assert (un_op_eval IntOfString #(StringOfZ i) = Some (InjRV #i)).
  { rewrite /= ZOfString_inv //=. }
  wp_pures.
  iApply unSOME_spec; done.
Qed.

Definition int_serialization : serialization :=
  {| DBS_valid_val := int_valid_val;
     DBS_ser := int_ser;
     DBS_deser := int_deser;
     DBS_is_ser := int_is_ser;
     DBS_ser_spec := @int_ser_spec;
     DBS_deser_spec := @int_deser_spec; |}.

Global Instance: ∀ i : Z, Serializable int_serialization #i.
Proof. intros i; exists i; done. Qed.

Definition unit_valid_val (v : ground_lang.val) := v = #().

Definition unit_ser : ground_lang.val := λ: "v", #"".

Definition unit_deser : ground_lang.val := λ: "v", #().

Definition unit_is_ser (v : ground_lang.val) (s : string) := v = #() ∧ s = "".

Lemma unit_ser_spec `{!distG Σ} ip v :
  {{{ ⌜unit_valid_val v⌝ }}}
    unit_ser v @[ip]
  {{{ (s : string), RET #s; ⌜unit_is_ser v s⌝ }}}.
Proof.
  iIntros (Φ ->) "HΦ".
  rewrite /unit_ser /unit_is_ser.
  wp_pures.
  iApply "HΦ"; eauto.
Qed.

Lemma unit_deser_spec `{!distG Σ} ip v s :
  {{{ ⌜unit_is_ser v s⌝ }}}
    unit_deser #s @[ip]
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ [-> ->]) "HΦ".
  rewrite /unit_deser /unit_is_ser.
  wp_pures.
  iApply "HΦ"; done.
Qed.

Definition unit_serialization : serialization :=
  {| DBS_valid_val := unit_valid_val;
     DBS_ser := unit_ser;
     DBS_deser := unit_deser;
     DBS_is_ser := unit_is_ser;
     DBS_ser_spec := @unit_ser_spec;
     DBS_deser_spec := @unit_deser_spec; |}.

Global Instance: Serializable unit_serialization #().
Proof. done. Qed.

Definition string_valid_val (v : ground_lang.val) := ∃ (s : string), v = #s.

Definition string_ser : ground_lang.val := λ: "v", "v".

Definition string_deser : ground_lang.val := λ: "v", "v".

Definition string_is_ser (v : ground_lang.val) (s : string) := v = #s.

Lemma string_ser_spec `{!distG Σ} ip v:
  {{{ ⌜string_valid_val v⌝ }}}
    string_ser v @[ip]
  {{{ (s : string), RET #s; ⌜string_is_ser v s⌝ }}}.
Proof.
  iIntros (Φ [i ->]) "HΦ".
  rewrite /string_ser /string_is_ser.
  wp_pures.
  iApply "HΦ"; eauto.
Qed.

Lemma string_deser_spec `{!distG Σ} ip v s:
  {{{ ⌜string_is_ser v s⌝ }}}
    string_deser #s @[ip]
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ ->) "HΦ".
  rewrite /string_deser /string_is_ser.
  wp_pures.
  iApply "HΦ"; done.
Qed.

Definition string_serialization : serialization :=
  {| DBS_valid_val := string_valid_val;
     DBS_ser := string_ser;
     DBS_deser := string_deser;
     DBS_is_ser := string_is_ser;
     DBS_ser_spec := @string_ser_spec;
     DBS_deser_spec := @string_deser_spec; |}.

Global Instance: ∀ s : string, Serializable string_serialization #s.
Proof. intros s; exists s; done. Qed.

Section prod_serialization.

  Definition prod_ser (serA serB : ground_lang.val) : ground_lang.val :=
    λ: "v",
    let: "s1" := serA (Fst "v") in
    let: "s2" := serB (Snd "v") in
    i2s (strlen "s1") ^^ #"_" ^^ "s1" ^^ "s2".

  Definition prod_deser (deserA deserB : ground_lang.val) : ground_lang.val :=
    λ: "s",
    match: FindFrom "s" #0 #"_" with
      SOME "i" =>
      let: "len" := unSOME (s2i (Substring "s" #0 "i")) in
      let: "s1" := Substring "s" ("i" + #1) "len" in
      let: "s2" := Substring "s" ("i" + #1 + "len")
                             (strlen "s" - ("i" + #1 + "len")) in
      let: "v1" := deserA "s1" in
      let: "v2" := deserB "s2" in
      ("v1", "v2")
    | NONE => assert: #false
    end.

  Context (A B : serialization).

  Definition prod_valid_val (v : ground_lang.val) :=
    ∃ v1 v2, v = (v1, v2)%V ∧ DBS_valid_val A v1 ∧ DBS_valid_val B v2.

  Definition prod_is_ser (v : ground_lang.val) (s : string) :=
    ∃ v1 v2 s1 s2,
      v = (v1, v2)%V ∧ DBS_is_ser A v1 s1 ∧ DBS_is_ser B v2 s2 ∧
      s = StringOfZ (String.length s1) +:+ "_" +:+ s1 +:+ s2.

  Lemma prod_ser_spec `{!distG Σ} ip v:
    {{{ ⌜prod_valid_val v⌝ }}}
      prod_ser (DBS_ser A) (DBS_ser B) v @[ip]
    {{{ (s : string), RET #s; ⌜prod_is_ser v s⌝ }}}.
  Proof.
    iIntros (Φ (v1&v2&->&?&?)) "HΦ".
    rewrite /prod_ser /prod_is_ser.
    wp_pures.
    wp_apply (DBS_ser_spec A); first done.
    iIntros (s1 Hs1).
    wp_pures.
    wp_apply (DBS_ser_spec B); first done.
    iIntros (s2 Hs2).
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    exists v1, v2, s1, s2; split_and!; auto.
    rewrite !assoc; done.
  Qed.

  Lemma prod_deser_spec `{!distG Σ} ip v s:
    {{{ ⌜prod_is_ser v s⌝ }}}
      prod_deser (DBS_deser A) (DBS_deser B) #s @[ip]
    {{{ RET v; True }}}.
  Proof.
    iIntros (Φ (v1 & v2 & s1 & s2 & -> & Hv1 & Hv2 & ->)) "HΦ".
    rewrite /prod_deser /prod_is_ser.
    wp_pures.
    wp_find_from; first by split_and!; [|by apply nat_Z_eq; first lia].
    erewrite (index_0_append_char ); auto; last first.
    { apply valid_tag_stringOfZ. }
    wp_pures.
    wp_substring; first by split_and!; [|by apply nat_Z_eq; first lia|done].
    rewrite substring_0_length_append.
    wp_pure _.
    { rewrite /= ZOfString_inv //. }
    wp_apply unSOME_spec; first done.
    iIntros "_"; simpl.
    wp_pures.
    wp_substring; first by split_and!; [|by apply nat_Z_eq; first lia|done].
    replace (Z.to_nat (Z.add (Z.of_nat
                                (String.length
                                   (StringOfZ (Z.of_nat (String.length s1)))))
                             1%Z)) with
        (String.length (StringOfZ (Z.of_nat (String.length s1))) + 1) by lia.
    rewrite substring_add_length_app /= substring_0_length_append.
    wp_pures.
    rewrite !length_app /=.
    match goal with
    | |- context [Substring _ _ ?X] =>
      replace X with (Val #(String.length s2)); last first
    end.
    { repeat f_equal; lia. }
    wp_substring; first by split_and!; [|by apply nat_Z_eq; first lia|done].
    match goal with
    | |- context [substring ?X _ _] =>
      replace X with (String.length
                        (StringOfZ (Z.of_nat (String.length s1))) + 1 +
                      String.length s1) by lia
    end.
    rewrite -plus_assoc substring_add_length_app /= substring_length_append.
    wp_pures.
    wp_apply (DBS_deser_spec A); first done.
    iIntros "_"; simpl.
    wp_pures.
    wp_apply (DBS_deser_spec B); first done.
    iIntros "_"; simpl.
    wp_pures.
    iApply "HΦ"; done.
  Qed.

  Definition prod_serialization : serialization :=
    {| DBS_valid_val := prod_valid_val;
       DBS_ser := prod_ser (DBS_ser A) (DBS_ser B);
       DBS_deser := prod_deser (DBS_deser A) (DBS_deser B);
       DBS_is_ser := prod_is_ser;
       DBS_ser_spec := @prod_ser_spec;
       DBS_deser_spec := @prod_deser_spec; |}.

Global Instance:
  ∀ v1 v2, Serializable A v1 → Serializable B v2 →
           Serializable prod_serialization (v1, v2).
Proof. rewrite /Serializable /= /prod_valid_val /=; eauto. Qed.

End prod_serialization.

Section sum_serialization.

  Definition sum_ser (serA serB : ground_lang.val) : ground_lang.val :=
    λ: "v",
    match: "v" with
      InjL "x" => #"L" ^^ #"_" ^^ serA "x"
    | InjR "x" => #"R" ^^ #"_" ^^ serB "x"
    end.

  Definition sum_deser (deserA deserB : ground_lang.val) : ground_lang.val :=
    λ: "s",
    let: "tag" := Substring "s" #0 #2 in
    let: "rest" := Substring "s" #2 (strlen "s" - #2) in
    if: "tag" = #"L_" then
      InjL (deserA "rest")
    else
      if: "tag" = #"R_" then
        InjR (deserB "rest")
      else
        assert: #false.

  Context (A B : serialization).

  Definition sum_valid_val (v : ground_lang.val) :=
    ∃ w, (v = InjLV w ∧ DBS_valid_val A w) ∨
         (v = InjRV w ∧ DBS_valid_val B w).

  Definition sum_is_ser (v : ground_lang.val) (s : string) :=
    ∃ w s',
      (v = InjLV w ∧ DBS_is_ser A w s' ∧ s = "L_" +:+ s') ∨
      (v = InjRV w ∧ DBS_is_ser B w s' ∧ s = "R_" +:+ s').

  Lemma sum_ser_spec `{!distG Σ} ip v:
    {{{ ⌜sum_valid_val v⌝ }}}
      sum_ser (DBS_ser A) (DBS_ser B) v @[ip]
    {{{ (s : string), RET #s; ⌜sum_is_ser v s⌝ }}}.
  Proof.
    iIntros (Φ [w Hw]) "HΦ".
    rewrite /sum_ser /sum_is_ser.
    wp_pures.
    destruct Hw as [[-> Hw]|[-> Hw]].
    - wp_apply (DBS_ser_spec A); first done.
      iIntros (s Hs); simpl.
      wp_pures.
      iApply "HΦ"; eauto 10.
    - wp_apply (DBS_ser_spec B); first done.
      iIntros (s Hs); simpl.
      wp_pures.
      iApply "HΦ"; eauto 10.
  Qed.

  Lemma sum_deser_spec `{!distG Σ} ip v s:
    {{{ ⌜sum_is_ser v s⌝ }}}
      sum_deser (DBS_deser A) (DBS_deser B) #s @[ip]
    {{{ RET v; True }}}.
  Proof.
    iIntros (Φ (w & s' & Hw)) "HΦ".
    rewrite /sum_deser /sum_is_ser.
    wp_pures.
    destruct Hw as [(->&?&->)|(->&?&->)].
    - wp_substring;
        first by split_and!;
              [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
      rewrite (substring_0_length_append "L_").
      wp_pures.
      wp_substring;
        first by split_and!;
              [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
      rewrite (substring_add_length_app _ _ "L_") /=.
      replace (Z.to_nat (S (S (String.length s')) - 2)) with
          (String.length s') by lia.
      rewrite substring_0_length.
      wp_pures.
      wp_apply (DBS_deser_spec A); first done.
      iIntros "_".
      wp_pures.
      iApply "HΦ"; done.
    - wp_substring;
        first by split_and!;
              [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
      rewrite (substring_0_length_append "R_").
      wp_pures.
      wp_substring;
        first by split_and!;
              [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
      rewrite (substring_add_length_app _ _ "R_") /=.
      replace (Z.to_nat (S (S (String.length s')) - 2)) with
          (String.length s') by lia.
      rewrite substring_0_length.
      wp_pures.
      wp_apply (DBS_deser_spec B); first done.
      iIntros "_".
      wp_pures.
      iApply "HΦ"; done.
  Qed.

  Definition sum_serialization : serialization :=
    {| DBS_valid_val := sum_valid_val;
       DBS_ser := sum_ser (DBS_ser A) (DBS_ser B);
       DBS_deser := sum_deser (DBS_deser A) (DBS_deser B);
       DBS_is_ser := sum_is_ser;
       DBS_ser_spec := @sum_ser_spec;
       DBS_deser_spec := @sum_deser_spec; |}.

Global Instance:
  ∀ v, Serializable A v → Serializable sum_serialization (InjLV v).
Proof. rewrite /Serializable /= /sum_valid_val /=; eauto. Qed.

Global Instance:
  ∀ v, Serializable B v → Serializable sum_serialization (InjRV v).
Proof. rewrite /Serializable /= /sum_valid_val /=; eauto. Qed.

End sum_serialization.
