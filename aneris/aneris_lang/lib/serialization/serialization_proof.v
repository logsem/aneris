From iris.algebra Require Import gmap.
From aneris.prelude Require Import misc.
From aneris.aneris_lang Require Import lang proofmode.
From aneris.aneris_lang.lib Require Import inject list_proof network_util_proof assert_proof.
From aneris.aneris_lang.lib Require Export serialization_code.

Record serialization := {
  s_valid_val : val → Prop;
  s_serializer : serializer;
  s_is_ser : val → string → Prop;
  s_is_ser_valid : ∀ v s, s_is_ser v s -> s_valid_val v;
  s_ser_spec :
    ∀ `{!anerisG Mdl Σ} ip v,
    {{{ ⌜s_valid_val v⌝ }}}
      s_serializer.(s_ser) v @[ip]
    {{{ (s : string), RET #s; ⌜s_is_ser v s⌝ }}};
  s_deser_spec :
    ∀ `{!anerisG Mdl Σ} ip v s,
    {{{ ⌜s_is_ser v s⌝ }}}
      s_serializer.(s_deser) #s @[ip]
    {{{ RET v; True }}}; }.

Local Hint Resolve  s_is_ser_valid : core.

Class Serializable (s : serialization) (v : val) :=
  serializable : s_valid_val s v.

Class SerializerOf (ser : serializer) (serion : serialization) :=
  serializer_of : serion.(s_serializer) = ser.

Definition int_valid_val (v : val) := ∃ (i : Z), v = #i.

Definition int_ser_str (i : Z) : string := StringOfZ i.

Definition int_is_ser (v : val) (s : string) :=
  ∃ (i : Z), v = #i ∧ s = int_ser_str i.

Lemma int_is_ser_valid (v : val) (s : string) : int_is_ser v s -> int_valid_val v.
Proof.
  intros [I [-> _]].
  eexists _; eauto.
Qed.

Lemma int_ser_spec `{!anerisG Mdl Σ} ip v :
  {{{ ⌜int_valid_val v⌝ }}}
    int_ser v @[ip]
  {{{ (s : string), RET #s; ⌜int_is_ser v s⌝ }}}.
Proof.
  iIntros (Φ [i ->]) "HΦ".
  rewrite /int_ser /int_is_ser.
  wp_pures.
  iApply "HΦ"; eauto.
Qed.

Lemma int_deser_spec `{!anerisG Mdl Σ} ip v s :
  {{{ ⌜int_is_ser v s⌝ }}}
    int_deser #s @[ip]
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ [i [-> ->]]) "HΦ".
  rewrite /int_deser /int_is_ser.
  assert (un_op_eval IntOfString #(StringOfZ i) = Some (InjRV #i)).
  { rewrite /= ZOfString_inv //=. }
  wp_pures.
  iApply wp_unSOME; done.
Qed.

Definition int_serialization : serialization :=
  {| s_valid_val := int_valid_val;
     s_serializer := int_serializer;
     s_is_ser := int_is_ser;
     s_is_ser_valid := int_is_ser_valid;
     s_ser_spec := @int_ser_spec;
     s_deser_spec := @int_deser_spec; |}.

Global Instance: ∀ i : Z, Serializable int_serialization #i.
Proof. intros i; exists i; done. Qed.

Global Instance int_serializer_of : SerializerOf int_serializer int_serialization.
Proof. done. Qed.

Definition bool_to_int (b : bool) := if b then 1 else 0.

Definition bool_valid_val (v : val) := ∃ (b : bool), v = #b.

Definition bool_ser_str (b : bool) : string :=
  StringOfZ (bool_to_int b).

Definition bool_is_ser (v : val) (s : string) :=
  ∃ (b : bool), v = #b ∧ s = bool_ser_str b.

Lemma bool_is_ser_valid (v : val) (s : string) :
  bool_is_ser v s -> bool_valid_val v.
Proof.
  intros [I [-> _]].
  eexists _; eauto.
Qed.

Lemma bool_ser_spec `{!anerisG Mdl Σ} ip v :
  {{{ ⌜bool_valid_val v⌝ }}}
    bool_ser v @[ip]
  {{{ (s : string), RET #s; ⌜bool_is_ser v s⌝ }}}.
Proof.
  iIntros (Φ [b ->]) "HΦ".
  rewrite /bool_ser /bool_is_ser.
  destruct b; wp_pures; iApply "HΦ"; eauto.
Qed.

Lemma bool_deser_spec `{!anerisG Mdl Σ} ip v s :
  {{{ ⌜bool_is_ser v s⌝ }}}
    bool_deser #s @[ip]
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ [b [-> ->]]) "HΦ".
  rewrite /bool_deser /bool_is_ser. wp_pures.
  assert (un_op_eval IntOfString #(StringOfZ (bool_to_int b)) =
          Some (InjRV #(bool_to_int b))).
  { rewrite /= ZOfString_inv //=. }
  by destruct b; wp_pures; iApply "HΦ".
Qed.

Definition bool_serialization : serialization :=
  {| s_valid_val := bool_valid_val;
     s_serializer := bool_serializer;
     s_is_ser := bool_is_ser;
     s_is_ser_valid := bool_is_ser_valid;
     s_ser_spec := @bool_ser_spec;
     s_deser_spec := @bool_deser_spec; |}.

Global Instance: ∀ b : bool, Serializable bool_serialization #b.
Proof. intros b; exists b; done. Qed.

Global Instance bool_serializer_of : SerializerOf bool_serializer bool_serialization.
Proof. done. Qed.

Definition unit_valid_val (v : val) := v = #().

Definition unit_is_ser (v : val) (s : string) := v = #() ∧ s = "".

Lemma unit_is_ser_valid v s : unit_is_ser v s -> unit_valid_val v.
Proof.
  intros [-> _].
  rewrite /unit_valid_val; done.
Qed.

Lemma unit_ser_spec `{!anerisG Mdl Σ} ip v :
  {{{ ⌜unit_valid_val v⌝ }}}
    unit_ser v @[ip]
  {{{ (s : string), RET #s; ⌜unit_is_ser v s⌝ }}}.
Proof.
  iIntros (Φ ->) "HΦ".
  rewrite /unit_ser /unit_is_ser.
  wp_pures.
  iApply "HΦ"; eauto.
Qed.

Lemma unit_deser_spec `{!anerisG Mdl Σ} ip v s :
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
  {| s_valid_val := unit_valid_val;
     s_serializer := unit_serializer;
     s_is_ser := unit_is_ser;
     s_is_ser_valid := unit_is_ser_valid;
     s_ser_spec := @unit_ser_spec;
     s_deser_spec := @unit_deser_spec; |}.

Global Instance: Serializable unit_serialization #().
Proof. done. Qed.

Global Instance unit_serializer_of : SerializerOf unit_serializer unit_serialization.
Proof. done. Qed.

Definition string_valid_val (v : val) := ∃ (s : string), v = #s.

Definition string_is_ser (v : val) (s : string) := v = #s.

Lemma string_is_ser_valid v s : string_is_ser v s -> string_valid_val v.
Proof.
  intros ->.
  eexists _; eauto.
Qed.

Lemma string_ser_spec `{!anerisG Mdl Σ} ip v:
  {{{ ⌜string_valid_val v⌝ }}}
    string_ser v @[ip]
  {{{ (s : string), RET #s; ⌜string_is_ser v s⌝ }}}.
Proof.
  iIntros (Φ [i ->]) "HΦ".
  rewrite /string_ser /string_is_ser.
  wp_pures.
  iApply "HΦ"; eauto.
Qed.

Lemma string_deser_spec `{!anerisG Mdl Σ} ip v s:
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
  {| s_valid_val := string_valid_val;
     s_serializer := string_serializer;
     s_is_ser := string_is_ser;
     s_is_ser_valid := string_is_ser_valid;
     s_ser_spec := @string_ser_spec;
     s_deser_spec := @string_deser_spec; |}.

Global Instance: ∀ s : string, Serializable string_serialization #s.
Proof. intros s; exists s; done. Qed.

Global Instance string_serializer_of : SerializerOf string_serializer string_serialization.
Proof. done. Qed.

Section prod_serialization.

  Context (A B : serialization).

  Definition prod_valid_val (v : val) :=
    ∃ v1 v2, v = (v1, v2)%V ∧ s_valid_val A v1 ∧ s_valid_val B v2.

  Definition prod_ser_str (s1 s2 : string) :=
    StringOfZ (String.length s1) +:+ "_" +:+ s1 +:+ s2.

  Definition prod_is_ser (v : val) (s : string) :=
    ∃ v1 v2 s1 s2,
      v = (v1, v2)%V ∧ s_is_ser A v1 s1 ∧ s_is_ser B v2 s2 ∧
      s = prod_ser_str s1 s2.

  Lemma prod_is_ser_valid v s : prod_is_ser v s -> prod_valid_val v.
  Proof.
    intros [v1 [v2 [s1 [s2 [-> [Hl [Hr _]]]]]]].
    rewrite /prod_valid_val; eauto 10.
  Qed.

  Lemma prod_ser_spec `{!anerisG Mdl Σ} ip v:
    {{{ ⌜prod_valid_val v⌝ }}}
      prod_ser A.(s_serializer).(s_ser) B.(s_serializer).(s_ser) v @[ip]
    {{{ (s : string), RET #s; ⌜prod_is_ser v s⌝ }}}.
  Proof.
    iIntros (Φ (v1&v2&->&?&?)) "HΦ".
    rewrite /prod_ser /prod_is_ser.
    wp_pures.
    wp_apply (s_ser_spec A); first done.
    iIntros (s1 Hs1).
    wp_pures.
    wp_apply (s_ser_spec B); first done.
    iIntros (s2 Hs2).
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    exists v1, v2, s1, s2; split_and!; auto.
  Qed.

  Lemma prod_deser_spec `{!anerisG Mdl Σ} ip v s:
    {{{ ⌜prod_is_ser v s⌝ }}}
      prod_deser A.(s_serializer).(s_deser) B.(s_serializer).(s_deser) #s @[ip]
    {{{ RET v; True }}}.
  Proof.
    iIntros (Φ (v1 & v2 & s1 & s2 & -> & Hv1 & Hv2 & ->)) "HΦ".
    rewrite /prod_deser /prod_is_ser /prod_ser_str.
    wp_pures.
    wp_find_from; first by split_and!; [|by apply nat_Z_eq; first lia].
    erewrite (index_0_append_char ); auto; last first.
    { apply valid_tag_stringOfZ. }
    wp_pures.
    wp_substring; first by split_and!; [|by apply nat_Z_eq; first lia|done].
    rewrite substring_0_length_append.
    wp_pure _.
    { rewrite /= ZOfString_inv //. }
    wp_apply wp_unSOME; first done.
    iIntros "_"; simpl.
    wp_pures.
    wp_substring; first by split_and!; [|by apply nat_Z_eq; first lia|done].
    replace (Z.to_nat (Z.add (Z.of_nat
                                (String.length
                                   (StringOfZ (Z.of_nat (String.length s1)))))
                             1%Z)) with
        (String.length (StringOfZ (Z.of_nat (String.length s1))) + 1)%nat by lia.
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
                      String.length s1)%nat by lia
    end.
    rewrite -plus_assoc substring_add_length_app /= substring_length_append.
    wp_pures.
    wp_apply (s_deser_spec A); first done.
    iIntros "_"; simpl.
    wp_pures.
    wp_apply (s_deser_spec B); first done.
    iIntros "_"; simpl.
    wp_pures.
    iApply "HΦ"; done.
  Qed.

  Definition prod_serialization : serialization :=
    {| s_valid_val := prod_valid_val;
       s_serializer := prod_serializer A.(s_serializer) B.(s_serializer);
       s_is_ser := prod_is_ser;
       s_is_ser_valid := prod_is_ser_valid;
       s_ser_spec := @prod_ser_spec;
       s_deser_spec := @prod_deser_spec; |}.

  Global Instance:
    ∀ v1 v2, Serializable A v1 → Serializable B v2 →
             Serializable prod_serialization (v1, v2).
  Proof. rewrite /Serializable /= /prod_valid_val /=; eauto. Qed.

  Global Instance prod_serializer_of serA serB :
    SerializerOf serA A → SerializerOf serB B →
    SerializerOf (prod_serializer serA serB) (prod_serialization).
  Proof.
    intros H1 H2.
    rewrite /SerializerOf.
    rewrite /SerializerOf in H1.
    rewrite /SerializerOf in H2.
    subst. done.
  Qed.

End prod_serialization.

Section sum_serialization.

  Context (A B : serialization).

  Definition sum_valid_val (v : val) :=
    ∃ w, (v = InjLV w ∧ s_valid_val A w) ∨
         (v = InjRV w ∧ s_valid_val B w).

  Definition inl_ser_str (s : string) := "L_" +:+ s.
  Definition inr_ser_str (s : string) := "R_" +:+ s.

  Definition sum_is_ser (v : val) (s : string) :=
    ∃ w s',
      (v = InjLV w ∧ s_is_ser A w s' ∧ s = inl_ser_str s') ∨
      (v = InjRV w ∧ s_is_ser B w s' ∧ s = inr_ser_str s').

  Lemma sum_is_ser_valid v s : sum_is_ser v s -> sum_valid_val v.
  Proof.
    intros [w [s' [(? & ? & _) | (? & ? & ?)]]];
      rewrite /sum_valid_val; eauto 10.
  Qed.

  Lemma sum_ser_spec `{!anerisG Mdl Σ} ip v:
    {{{ ⌜sum_valid_val v⌝ }}}
      sum_ser A.(s_serializer).(s_ser) B.(s_serializer).(s_ser) v @[ip]
    {{{ (s : string), RET #s; ⌜sum_is_ser v s⌝ }}}.
  Proof.
    iIntros (Φ [w Hw]) "HΦ".
    rewrite /sum_ser /sum_is_ser.
    destruct Hw as [[-> Hw]|[-> Hw]]; wp_pures.
    - wp_apply (s_ser_spec A); first done.
      iIntros (s Hs); simpl.
      wp_pures.
      iApply "HΦ"; eauto 10.
    - wp_apply (s_ser_spec B); first done.
      iIntros (s Hs); simpl.
      wp_pures.
      iApply "HΦ"; eauto 10.
  Qed.

  Lemma sum_deser_spec `{!anerisG Mdl Σ} ip v s:
    {{{ ⌜sum_is_ser v s⌝ }}}
      sum_deser A.(s_serializer).(s_deser) B.(s_serializer).(s_deser) #s @[ip]
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
      wp_apply (s_deser_spec A); first done.
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
      wp_apply (s_deser_spec B); first done.
      iIntros "_".
      wp_pures.
      iApply "HΦ"; done.
  Qed.

  Definition sum_serialization : serialization :=
    {| s_valid_val := sum_valid_val;
       s_serializer := sum_serializer A.(s_serializer) B.(s_serializer);
       s_is_ser := sum_is_ser;
       s_is_ser_valid := sum_is_ser_valid;
       s_ser_spec := @sum_ser_spec;
       s_deser_spec := @sum_deser_spec; |}.

  Global Instance :
    ∀ v, Serializable A v → Serializable sum_serialization (InjLV v).
  Proof. rewrite /Serializable /= /sum_valid_val /=; eauto. Qed.

  Global Instance :
    ∀ v, Serializable B v → Serializable sum_serialization (InjRV v).
  Proof. rewrite /Serializable /= /sum_valid_val /=; eauto. Qed.

  Global Instance sum_serializer_of serA serB :
    SerializerOf serA A → SerializerOf serB B →
    SerializerOf (sum_serializer serA serB) (sum_serialization).
  Proof.
    intros H1 H2.
    rewrite /SerializerOf.
    rewrite /SerializerOf in H1.
    rewrite /SerializerOf in H2.
    subst. done.
  Qed.

End sum_serialization.

(*
Option serialization can be defined using sum_serialization.
However, from the point of view of translation from OCaml to AnerisLang,
it was more convenient to define option serialization separately.
Indeed, in OCaml sources, option expressions (None and Some e) and sum type
expresions (InjL e1 and InjR e2) are kept separately - to make programming a
little bit more natural while in AnerisLang - which is untyped - optional
expressions are a particular type of sum expressions.
That is, translation itself takes care of translating native Ocaml
optional expressions, values and patterns into AnerisLang sum expressions.
*)
Section option_serialization.

  Context (T : serialization).


  Definition option_valid_val (v : val) :=
    (∃ w, v = InjRV w ∧ s_valid_val T w) ∨
    (v = InjLV #()).

  Definition option_None_ser_str := inl_ser_str "".
  Definition option_Some_ser_str (s : string) := inr_ser_str s.

  Definition option_is_ser (v : val) (s : string) :=
    (v = InjLV #() ∧ s = option_None_ser_str) ∨
    (∃ w s', v = InjRV w ∧ s_is_ser T w s' ∧ s = option_Some_ser_str s').

  Lemma option_is_ser_valid v s : option_is_ser v s -> option_valid_val v.
  Proof.
    intros [[-> _] | [? [? [? [? ?]]]]]; rewrite /option_valid_val; eauto 10.
  Qed.

  Lemma option_ser_spec `{!anerisG Mdl Σ} ip v:
    {{{ ⌜option_valid_val v⌝ }}}
      option_ser T.(s_serializer).(s_ser) v @[ip]
    {{{ (s : string), RET #s; ⌜option_is_ser v s⌝ }}}.
  Proof.
    iIntros (Φ Hw) "HΦ".
    rewrite /option_ser /s_ser /s_serializer /option_is_ser.
    destruct Hw as [[w (-> & Hw)]|Hw]; wp_pures.
    - wp_apply (s_ser_spec T); first done.
      iIntros (s Hs); simpl.
      wp_pures.
      iApply "HΦ"; eauto 10.
    - rewrite Hw. wp_pures.
      iApply "HΦ". eauto.
  Qed.

  Lemma option_deser_spec `{!anerisG Mdl Σ} ip v s:
    {{{ ⌜option_is_ser v s⌝ }}}
      option_deser T.(s_serializer).(s_deser) #s @[ip]
    {{{ RET v; True }}}.
  Proof.
    iIntros (Φ Hw) "HΦ".
    rewrite /option_deser /option_is_ser /s_ser /s_serializer.
    wp_pures.
    destruct Hw as [(-> & ->) |(w & (s' & (-> & ? & ->)))].
    - wp_substring;
        first by split_and!;
                          [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
      wp_pures.
      wp_substring;
        first by split_and!;
              [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
      rewrite (substring_add_length_app _ _ "L_") /=.
      wp_pures. by iApply "HΦ".
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
      wp_apply (s_deser_spec T); first done.
      iIntros "_".
      wp_pures.
      iApply "HΦ"; done.
  Qed.

  Definition option_serialization : serialization :=
    {| s_valid_val := option_valid_val;
       s_serializer := option_serializer T.(s_serializer);
       s_is_ser := option_is_ser;
       s_is_ser_valid := option_is_ser_valid;
       s_ser_spec := @option_ser_spec;
       s_deser_spec := @option_deser_spec; |}.

  Global Instance:
    ∀ v, Serializable T v → Serializable option_serialization (SOMEV v).
  Proof.
    rewrite /Serializable /= /option_valid_val /=; eauto.
  Qed.

  Global Instance: Serializable option_serialization (NONEV).
  Proof. rewrite /Serializable /= /option_valid_val /option_valid_val /=. by right. Qed.

  Global Instance option_serializer_of serT :
    SerializerOf serT T →
    SerializerOf (option_serializer serT) (option_serialization).
  Proof.
    intros H1.
    rewrite /SerializerOf.
    rewrite /SerializerOf in H1.
    subst. done.
  Qed.

End option_serialization.

Section list_serialization.

  Context (E : serialization).
  Context `{!Inject A val}.


  Definition list_valid_val (v : val) :=
    ∃ (la: list A), is_list la v ∧ (∀ x, x ∈ la → s_valid_val E $ x).

  Fixpoint list_is_ser_aux (la : list A) (s : string) :=
    match la with
      | hd :: tl =>
          ∃ s1 s2 : string,
            E.(s_is_ser) $hd s1 ∧
            s = prod_ser_str s1 s2 ∧
            list_is_ser_aux tl s2
      | [] => s = ""
  end.

  Definition list_is_ser (v : val) (s : string) :=
    ∃ (l : list A), is_list l v ∧ list_is_ser_aux l s.

  Lemma list_is_ser_aux_valid_val l :
    ∀ s x, list_is_ser_aux l s → x ∈ l → s_valid_val E $ x.
  Proof.
    induction l as [|a' l']; first by set_solver.
    intros ?? (?&?&?&?&?) [->|Hin]%elem_of_cons;
      by [eapply s_is_ser_valid| eapply IHl'].
  Qed.

  Lemma list_is_ser_valid (v : val) (s : string) :
    list_is_ser v s -> list_valid_val v.
  Proof.
    destruct 1 as (l&Hl&Hs).
    exists l. split; first done.
    intros x Hx. by eapply list_is_ser_aux_valid_val.
  Qed.

  Lemma list_ser_spec `{!anerisG Mdl Σ} ip v:
    {{{ ⌜list_valid_val v⌝ }}}
      (list_serializer (s_serializer E)).(s_ser) v @[ip]
    {{{ (s : string), RET #s; ⌜list_is_ser v s⌝ }}}.
  Proof.
    iIntros (Φ) "Hv HΦ".
    iLöb as "IH" forall (Φ v).
    wp_rec.
    iDestruct "Hv" as %(l&Hvl&Hvv).
    destruct l as [|a l].
    - rewrite Hvl.
      wp_pures.
      iApply "HΦ".
      iPureIntro.
      rewrite /list_is_ser; eexists []; done.
    - simpl in Hvl, Hvv.
      destruct Hvl as [lv [-> Hvl]].
      wp_pures.
      wp_apply (s_ser_spec E).
      { iPureIntro.
        apply Hvv.
        set_solver. }
      iIntros (s1) "%Hs1".
      wp_pures.
      wp_bind (list_ser (s_ser (s_serializer E)) _).
      iApply "IH"; [iPureIntro; exists l; set_solver |].
      iIntros "!>" (s2) "%Hs2".
      wp_pures.
      destruct Hs2 as (l'& Hs2x & Hs2y).
      iApply "HΦ".
      iPureIntro.
      exists (a :: l').
      split; first by eexists.
      by exists s1, s2.
  Qed.

  Lemma list_deser_spec `{!anerisG Mdl Σ} ip v s:
    {{{ ⌜list_is_ser v s⌝ }}}
      (list_serializer (s_serializer E)).(s_deser) #s @[ip]
      {{{ RET v; True }}}.
  Proof.
    iIntros (Φ) "Hs HΦ".
    iLöb as "IH" forall (Φ v s).
    wp_rec.
    iDestruct "Hs" as %(l & Hl1 & Hl2).
    destruct l as [|a l]; simpl.
    - rewrite Hl1 Hl2.
      wp_find_from; first by split_and!; [|by apply nat_Z_eq; first lia].
      wp_pures.
      by iApply "HΦ".
    - destruct Hl1 as [lv [-> Hl1]].
      destruct Hl2 as (s1&s2&Hs1&->&Hl2).
      rewrite! /prod_ser_str.
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
      wp_substring;
        first by split_and!;
              [|by apply nat_Z_eq; first lia|by apply nat_Z_eq; first lia].
      replace (Z.to_nat (Z.add (Z.of_nat
                                  (String.length
                                     (StringOfZ (Z.of_nat (String.length s1)))))
                               1%Z)) with
        (String.length (StringOfZ (Z.of_nat (String.length s1))) + 1)%nat by lia.
      replace (Z.to_nat (String.length s1)) with (String.length s1)%nat by lia.
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
                        String.length s1)%nat by lia
    end.
    rewrite -plus_assoc substring_add_length_app /= substring_length_append.
    wp_pures.
    wp_apply (s_deser_spec E); first done.
    iIntros "_"; simpl.
    wp_pures.
    wp_bind (list_deser _ _).
    iApply ("IH" $! _ lv); first by iPureIntro; eexists.
    iIntros "!> _".
    wp_pures.
    wp_apply (wp_list_cons _ l); first done.
    iIntros (v Hl).
    assert ((InjRV ($ a, lv) = v)) as ->.
    { destruct Hl as [lv' [-> Hl1']].
      by rewrite (is_list_eq _ _ _ Hl1 Hl1'). }
    by iApply "HΦ".
  Qed.

Definition list_serialization : serialization :=
  {| s_valid_val := list_valid_val;
     s_serializer := list_serializer E.(s_serializer);
     s_is_ser := list_is_ser;
     s_is_ser_valid := list_is_ser_valid;
     s_ser_spec := @list_ser_spec;
     s_deser_spec := @list_deser_spec; |}.

End list_serialization.


(* Recursively destructs the definition of the argument hypothesis of the shape
   [H : *_is_ser] *)
Ltac destruct_is_ser H :=
  match type of H with
  | s_is_ser _ _ _ => simpl in H; destruct_is_ser H
  | int_is_ser _ _ => destruct H as (?&?&?)
  | unit_is_ser _ _ => destruct H as [? ?]
  | prod_is_ser _ _ _ _ =>
    destruct H as (?&?&?&?&?& ?Hp1 & ?Hp2 &?);
    destruct_is_ser Hp1; destruct_is_ser Hp2
  | sum_is_ser _ _ _ _ =>
    destruct H as (?&?& [(? & ?Hl & ?)|(? & ?Hr &?)]);
    [destruct_is_ser Hl | destruct_is_ser Hr]
  | option_is_ser _ _ _ =>
    destruct H as (?&?& [(? & ?Hl & ?)|(? & ?Hr & ?)]);
    [destruct_is_ser Hl | destruct_is_ser Hr]
  | list_is_ser _ _ _ _ => destruct H as (?&?&?)
  | _ => idtac
  end; simplify_eq.
