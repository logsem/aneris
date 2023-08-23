From aneris.prelude Require Import misc.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import proofmode.
From aneris.aneris_lang.lib Require Import inject list_proof network_util_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params.

(** TODO: proof list_serialization and move to the serialization_proof file. *)
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
    rewrite -Nat.add_assoc substring_add_length_app /= substring_length_append.
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

  Global Instance list_serializer_of serA :
    SerializerOf serA E →
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