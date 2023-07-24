From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import proofmode.

From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params.

(** TODO: proof list_serialization and move to the serialization_proof file. *)
Section list_serialization.

  Context (A : serialization).

  Definition list_valid_val (v : val) := True.

  Definition list_ser_str (s1 s2 : string) := True.

  Definition list_is_ser (v : val) (s : string) := True.

  Lemma list_is_ser_valid v s : list_is_ser v s -> list_valid_val v.
  Proof.
  Admitted.

  Lemma list_ser_spec `{!anerisG Mdl Σ} ip v:
    {{{ ⌜list_valid_val v⌝ }}}
      list_ser A.(s_serializer).(s_ser) v @[ip]
    {{{ (s : string), RET #s; ⌜list_is_ser v s⌝ }}}.
  Proof.
  Admitted.

  Lemma list_deser_spec `{!anerisG Mdl Σ} ip v s:
    {{{ ⌜list_is_ser v s⌝ }}}
      list_deser A.(s_serializer).(s_deser) #s @[ip]
    {{{ RET v; True }}}.
  Proof.
  Admitted.

  Definition list_serialization : serialization :=
    {| s_valid_val := list_valid_val;
       s_serializer := list_serializer A.(s_serializer);
       s_is_ser := list_is_ser;
       s_is_ser_valid := list_is_ser_valid;
       s_ser_spec := @list_ser_spec;
       s_deser_spec := @list_deser_spec; |}.

  Global Instance:
    ∀ v1, Serializable A v1 →
             Serializable list_serialization v1.
  Proof. rewrite /Serializable /= /list_valid_val /=; eauto. Qed.

  Global Instance list_serializer_of serA :
    SerializerOf serA A →
    SerializerOf (list_serializer serA) (list_serialization).
  Proof.
    intros H1.
    rewrite /SerializerOf.
    rewrite /SerializerOf in H1.
    subst. done.
  Qed.

End list_serialization.

Section Repdb_ser.

  Context `{!User_params}.

  Definition req_serialization :=
    sum_serialization
      (prod_serialization string_serialization int_serialization)
      (sum_serialization
         unit_serialization
         (prod_serialization
            int_serialization
            (list_serialization
               (prod_serialization
                  string_serialization
                  KVS_serialization)))).


  Definition rep_serialization :=
    sum_serialization
      (option_serialization KVS_serialization)
      (sum_serialization int_serialization bool_serialization).

  Lemma req_ser_is_injective : ser_is_injective req_serialization.
  Proof.
  Admitted.
  (*   apply sum_ser_is_ser_injective. *)
  (*   - apply prod_ser_is_ser_injective. *)
  (*     -- apply string_ser_is_ser_injective. *)
  (*     -- apply DB_ser_inj. *)
  (*   - apply string_ser_is_ser_injective. *)
  (* Qed. *)

  Lemma req_ser_is_injective_alt : ser_is_injective_alt req_serialization.
  Proof.
  Admitted.

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

  Lemma rep_ser_is_injective : ser_is_injective rep_serialization.
  Proof.
  Admitted.
  (*   apply sum_ser_is_ser_injective. *)
  (*   - apply unit_ser_is_ser_injective. *)
  (*   - apply option_ser_is_ser_injective. *)
  (*     apply DB_ser_inj. *)
  (* Qed. *)

 Lemma rep_ser_is_injective_alt : ser_is_injective_alt rep_serialization.
  Proof.
  Admitted.

End Repdb_ser.
