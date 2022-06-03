From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.examples.reliable_communication.lib.repdb Require Import repdb_code.
From aneris.examples.reliable_communication.lib.repdb.spec Require Import db_params.

Section Repdb_ser.

  Context `{!DB_params}.

  Definition write_serialization :=
    prod_serialization string_serialization DB_serialization.

  Definition read_serialization := string_serialization.

  Definition req_c2l_serialization :=
    sum_serialization write_serialization read_serialization.

  Definition rep_l2c_serialization :=
    sum_serialization
      unit_serialization
      (option_serialization DB_serialization).

  Definition req_f2l_serialization := int_serialization.

  Definition rep_l2f_serialization :=
    prod_serialization string_serialization DB_serialization.

  Definition req_c2f_serialization := read_serialization.

  Definition rep_f2c_serialization := option_serialization DB_serialization.

  Lemma req_c2l_ser_is_injective : ser_is_injective req_c2l_serialization.
  Proof.
    apply sum_ser_is_ser_injective.
    - apply prod_ser_is_ser_injective.
      -- apply string_ser_is_ser_injective.
      -- apply DB_ser_inj.
    - apply string_ser_is_ser_injective.
  Qed.

  (* TODO : move to lib. *)
  Lemma unit_ser_is_ser_injective :
    ser_is_injective unit_serialization.
  Proof.
    intros s mval1 mval2 Hs1%s_is_ser_valid Hs2%s_is_ser_valid.
    simplify_eq /=. rewrite /unit_valid_val in Hs1, Hs2. by subst.
  Qed.

  (* TODO : move to lib. *)
  Lemma unit_ser_is_ser_injective_alt :
    ser_is_injective_alt unit_serialization.
  Proof.
    intros s1 s2 mval Heq1 Heq2.
    inversion Heq1. inversion Heq2. by simplify_eq.
  Qed.

  (* TODO : move to lib. *)
  Lemma option_ser_is_ser_injective ser:
    ser_is_injective ser →
    ser_is_injective (option_serialization ser).
  Proof.
    intros Hser s mval1 mval2 Hs1 Hs2.
    destruct Hs1 as [ (n1 & Hn1) | (v1 & s1 & -> & Hs1 & Hvs1) ];
    destruct Hs2 as [ (n2 & Hn2) | (v2 & s2 & -> & Hs2 & Hvs2) ]; simplify_eq /=.
    - done.
    - f_equal. by eapply Hser.
  Qed.

  (* TODO : move to lib. *)
  Lemma option_ser_is_ser_injective_alt ser:
    ser_is_injective_alt ser →
    ser_is_injective_alt (option_serialization ser).
  Proof.
    intros Hser1 s1 s2 mval Hs1 Hs2.
    destruct Hs1 as [(-> & Hvs1)|(v1 & str1 & Heq11 & Heq12 & Hvs1)];
    destruct Hs2 as [(v2 & Hvs2)|(v2 & str2 & Heq21 & Heq22 & Hvs2)]; simplify_eq /=.
    - done.
    - f_equal. by eapply Hser1.
  Qed.

  Lemma rep_l2c_ser_is_injective : ser_is_injective rep_l2c_serialization.
  Proof.
    apply sum_ser_is_ser_injective.
    - apply unit_ser_is_ser_injective.
    - apply option_ser_is_ser_injective.
      apply DB_ser_inj.
  Qed.

  Lemma req_c2l_ser_is_injective_alt : ser_is_injective_alt req_c2l_serialization.
  Proof.
    apply sum_ser_is_ser_injective_alt.
    - apply prod_ser_is_ser_injective_alt.
      -- apply string_ser_is_ser_injective_alt.
      -- apply DB_ser_inj_alt.
    - apply string_ser_is_ser_injective_alt.
  Qed.

  Lemma rep_l2c_ser_is_injective_alt : ser_is_injective_alt rep_l2c_serialization.
  Proof.
    apply sum_ser_is_ser_injective_alt.
    - apply unit_ser_is_ser_injective_alt.
    - apply option_ser_is_ser_injective_alt.
      apply DB_ser_inj_alt.
  Qed.

  Lemma req_f2l_ser_is_injective :
    ser_is_injective req_f2l_serialization.
  Proof. apply int_ser_is_ser_injective. Qed.

  Lemma req_f2l_ser_is_injective_alt :
    ser_is_injective_alt req_f2l_serialization.
  Proof. apply int_ser_is_ser_injective_alt. Qed.

  Lemma rep_l2f_ser_is_injective :
    ser_is_injective rep_l2f_serialization.
  Proof.
    apply prod_ser_is_ser_injective.
    - apply string_ser_is_ser_injective.
    - apply DB_ser_inj.
  Qed.

  Lemma rep_l2f_ser_is_injective_alt :
    ser_is_injective_alt rep_l2f_serialization.
  Proof.
    apply prod_ser_is_ser_injective_alt.
    - apply string_ser_is_ser_injective_alt.
    - apply DB_ser_inj_alt.
  Qed.

  Lemma req_c2f_ser_is_injective :
    ser_is_injective req_c2f_serialization.
  Proof. apply string_ser_is_ser_injective. Qed.

  Lemma req_c2f_ser_is_injective_alt :
    ser_is_injective_alt req_c2f_serialization.
  Proof. apply string_ser_is_ser_injective_alt. Qed.


  Lemma rep_f2c_ser_is_injective :
    ser_is_injective rep_f2c_serialization.
  Proof. apply option_ser_is_ser_injective, DB_ser_inj. Qed.

  Lemma rep_f2c_ser_is_injective_alt :
    ser_is_injective_alt rep_f2c_serialization.
  Proof. apply option_ser_is_ser_injective_alt, DB_ser_inj_alt. Qed.

End Repdb_ser.
