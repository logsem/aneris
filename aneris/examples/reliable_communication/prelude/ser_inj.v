From iris.proofmode Require Import proofmode.
From aneris.prelude Require Import strings.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.

Definition ser_is_injective ser :=
  ∀ s mval1 mval2,
  s_is_ser ser mval1 s →
  s_is_ser ser mval2 s →
  mval1 = mval2.

Definition ser_is_injective_alt ser :=
  ∀ s1 s2 mval,
  s_is_ser ser mval s1 →
  s_is_ser ser mval s2 →
  s1 = s2.

Lemma int_ser_is_ser_injective :
  ser_is_injective int_serialization.
Proof.
  intros s mval1 mval2 Hs1 Hs2.
  destruct Hs1 as (v1 & s1 & Hvs1).
  destruct Hs2 as (v2 & s2 & Hvs2).
  by simplify_eq.
Qed.

Lemma string_ser_is_ser_injective :
  ser_is_injective string_serialization.
Proof. by intros s mval1 mval2 -> ->. Qed.

Lemma sum_ser_is_ser_injective ser1 ser2 :
  ser_is_injective ser1 → ser_is_injective ser2 →
  ser_is_injective (sum_serialization ser1 ser2).
Proof.
  intros Hser1 Hser2 s mval1 mval2 Hs1 Hs2.
  destruct Hs1 as (v1 & s1 & Hvs1).
  destruct Hs2 as (v2 & s2 & Hvs2).
  destruct Hvs1 as [(-> & Hs1 & Hvs1)|(-> & Hs1 & Hvs1)];
    destruct Hvs2 as [(-> & Hs2 & Hvs2)|(-> & Hs2 & Hvs2)]; simplify_eq.
  - f_equiv. by apply (Hser1 s2 v1 v2).
  - f_equiv. by apply (Hser2 s2 v1 v2).
Qed.

Lemma prod_ser_is_ser_injective ser1 ser2 :
  ser_is_injective ser1 → ser_is_injective ser2 →
  ser_is_injective (prod_serialization ser1 ser2).
Proof.
  intros Hser1 Hser2.
  intros s mval1 mval2 Hs1 Hs2.
  destruct Hs1 as (v11&v12&s11&s12&->&Hs11&Hs12&Heq1).
  destruct Hs2 as (v21&v22&s21&s22&->&Hs21&Hs22&Heq2).
  simplify_eq.
  rewrite /prod_ser_str -!append_cons in Heq2.
  assert (s11 = s21 ∧ s12 = s22) as (-> & ->).
  { eapply not_elem_of_string_app_cons_inv_l in Heq2;
      [|intros Hin; by apply StringOfZ_not_sep in Hin..].
    destruct Heq2 as (Heq&_&Heq2).
    apply string_app_inj in Heq2.
    assert (String.length s11 = String.length s21) as Hlen by naive_solver.
    assert (s11 = s21) as <-.
    { by apply (append_eq_length_inv s11 s21 s12 s22). }
    by apply string_app_inj in Heq2. }
  simplify_eq.
  f_equiv; [ by apply (Hser1 s21 v11 v21) | by apply (Hser2 s22 v12 v22)].
Qed.

Lemma int_ser_is_ser_injective_alt :
  ser_is_injective_alt int_serialization.
Proof.
  intros s1 s2 mval Hs1 Hs2.
  destruct Hs1 as (v1 & str1 & Hvs1).
  destruct Hs2 as (v2 & str2 & Hvs2).
  by simplify_eq.
Qed.

Lemma string_ser_is_ser_injective_alt :
  ser_is_injective_alt string_serialization.
Proof.
  intros s1 s2 mval Heq1 Heq2.
  inversion Heq1. inversion Heq2. by simplify_eq.
Qed.

Lemma sum_ser_is_ser_injective_alt ser1 ser2 :
  ser_is_injective_alt ser1 → ser_is_injective_alt ser2 →
  ser_is_injective_alt (sum_serialization ser1 ser2).
Proof.
  intros Hser1 Hser2 s1 s2 mval Hs1 Hs2.
  destruct Hs1 as (v1 & str1 & Hvs1).
  destruct Hs2 as (v2 & str2 & Hvs2).
  destruct Hvs1 as [(Heq1 & Hs1 & Hvs1)|(Heq1 & Hs1 & Hvs1)];
    destruct Hvs2 as [(Heq2 & Hs2 & Hvs2)|(Heq2 & Hs2 & Hvs2)]; simplify_eq.
  - f_equiv. by apply (Hser1 str1 str2 v2).
  - f_equiv. by apply (Hser2 str1 str2 v2).
Qed.

Lemma prod_ser_is_ser_injective_alt ser1 ser2 :
  ser_is_injective_alt ser1 → ser_is_injective_alt ser2 →
  ser_is_injective_alt (prod_serialization ser1 ser2).
Proof.
  intros Hser1 Hser2.
  intros s1 s2 mval Hs1 Hs2.
  destruct Hs1 as (v11&v12&s11&s12&Heq11&Hs11&Hs12&Heq12).
  destruct Hs2 as (v21&v22&s21&s22&Heq21&Hs21&Hs22&Heq22).
  simplify_eq.
  rewrite /prod_ser_str.
  assert (s11 = s21 ∧ s12 = s22) as (-> & ->).
  { split; [by apply (Hser1 s11 s21 v21)|
             by apply (Hser2 s12 s22 v22)]. }
  done.
Qed.
