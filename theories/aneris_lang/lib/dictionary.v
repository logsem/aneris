From stdpp Require Export strings list pretty gmap.
From iris.proofmode Require Import tactics.
From aneris Require Import lang network notation tactics proofmode lifting.
From aneris.aneris_lang.lib Require Import list.

Module dict.

  Definition empty : ground_lang.val :=
    (λ: <>, list_make #())%V.

  Definition remove : ground_lang.val :=
    (λ: "key",
     (rec: "loop" "dict" :=
        match: "dict" with
          NONE => NONE
        | SOME "p" => (if: Fst (Fst "p") = "key"
                       then (Snd "p")
                       else (list_cons (Fst "p") ("loop" (Snd "p"))))
        end))%V.

  Definition insert : ground_lang.val :=
    (λ: "key" "val" "dict",
     (list_cons ("key", "val") (remove "key" "dict")))%V.

  Definition lookup : ground_lang.val :=
    (λ: "key",
     (rec: "loop" "dict" :=
        match: "dict" with
          NONE => NONE
        | SOME "p" => (if: Fst (Fst "p") = "key"
                       then SOME (Snd (Fst "p"))
                       else "loop" (Snd "p"))
        end))%V.

End dict.

Section dict_spec.
  Context `{dG : distG Σ}.

  Fixpoint embed_list
           (l : list (ground_lang.val * ground_lang.val)) : ground_lang.val :=
    match l with
    | [] => InjLV #()
    | (k, v) :: ps => InjRV ((k, v), (embed_list ps))
    end.

  Definition is_dictionary (d :  ground_lang.val)
             (m : gmap  ground_lang.val  ground_lang.val) : Prop :=
    ∃ l, m = list_to_map l ∧ d = embed_list l ∧ NoDup (fmap fst l).

  Lemma empty_spec n :
    {{{ True }}}
      ⟨n; dict.empty #()⟩
    {{{ v, RET 〈 n ; v 〉; ⌜is_dictionary v ∅⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    do 2 wp_rec. wp_pures. iApply "HΦ".
    iExists []. repeat iSplit; auto.
    iPureIntro. constructor.
  Qed.

  Lemma about_eq_val k k' : bin_op_eval EqOp k' k = Some #(bool_decide (k' = k)).
  Proof.
    destruct k, k'; cbn; try reflexivity.
    - destruct l,  l0; try reflexivity; repeat f_equal.
      { rewrite /bool_decide.
        case (decide_rel _ _ n), (decide_rel _ _ #n); congruence. }
      { rewrite /bool_decide.
        case (decide_rel _ _ b), (decide_rel _ _ #b); congruence. }
    - destruct l; try reflexivity.
    - destruct l; reflexivity.
    - destruct l; reflexivity.
    - destruct l; reflexivity.
  Qed.

  Lemma remove_spec n (k d : ground_lang.val) m :
      {{{ ⌜is_dictionary d m⌝ }}}
        ⟨n; dict.remove (Val k) (Val d)⟩
      {{{ d', RET 〈 n ; d' 〉; ⌜is_dictionary d' (delete k m)⌝ }}}.
  Proof.
    iIntros (Φ Hm) "HΦ".
    wp_rec. wp_closure. iLöb as "IH" forall (Φ d m Hm). wp_rec.
    destruct Hm as ([ | [key v] tail] & Hm & Hx & Hnodup).
    - unfold embed_list in *. subst. simpl. wp_pures. iApply "HΦ".
      simpl. iExists []. rewrite delete_empty. by repeat iSplit; auto.
    - simpl in Hx. subst. wp_match.
      do 2 wp_proj. wp_op; first apply about_eq_val.
      case_bool_decide.
      + wp_if. wp_proj. iApply "HΦ". simpl. subst.
        rewrite delete_insert; inversion Hnodup; subst.
        * by iExists tail.
        * apply not_elem_of_list_to_map. assumption.
      + wp_if. wp_proj. unfold list_cons.
        wp_bind (App _ (embed_list tail))%E. iApply "IH".
        * inversion Hnodup. subst. by iExists tail.
        * iIntros. simpl. wp_pures. iApply "HΦ".
          simpl. destruct a as (tail' & Hdelete & Himbed & Hnodup').
          iExists ((key, v) :: tail'). repeat iSplit; iPureIntro.
          -- rewrite delete_insert_ne; auto. simpl. congruence.
          -- simpl. congruence.
          -- simpl. constructor; last done.
             unshelve eapply not_elem_of_list_to_map_2; last first.
             ++ rewrite <-Hdelete. rewrite ->lookup_delete_ne by auto.
                inversion Hnodup; subst. apply not_elem_of_list_to_map_1; done.
             ++ eauto with *.
  Qed.

  Lemma insert_spec n k v d m :
      {{{ ⌜is_dictionary d m⌝ }}}
        ⟨n; dict.insert (Val k) (Val v) (Val d)⟩
      {{{ d', RET 〈 n; d' 〉; ⌜is_dictionary d' (insert k v m)⌝ }}}.
  Proof.
    iIntros (Φ) "Hdict HΦ".
    wp_rec. wp_pures. wp_bind (dict.remove k d).
    iApply (remove_spec with "Hdict").
    iNext. iIntros (d' Hdict). rewrite /list_cons. wp_pures. iApply "HΦ".
    iPureIntro. destruct Hdict as (l & ? & ? & ?). exists ((k, v) :: l).
    repeat split; simpl.
    - rewrite <-H. by rewrite insert_delete.
    - by subst.
    - constructor; last done. unshelve eapply not_elem_of_list_to_map_2; last first.
      ++ rewrite <-H. by rewrite ->lookup_delete.
      ++ eauto with *.
  Qed.

  Lemma lookup_spec n k d m :
      {{{ ⌜is_dictionary d m⌝ }}}
        ⟨n; dict.lookup (Val k) (Val d)⟩
      {{{ v, RET  〈 n; v 〉;
          ⌜match m !! k  with
             None => v = NONEV
           | Some p => v = SOMEV p
           end⌝ }}}.
  Proof.
    iIntros (Φ Hdict) "HΦ".
    wp_rec. wp_closure. iLöb as "IH" forall (m d Hdict); wp_rec.
    destruct Hdict as ([| [key v] l] & ? & ? & ?).
    - subst. simpl. wp_pures. iApply "HΦ".
      iPureIntro. by rewrite lookup_empty.
    - subst. simpl. wp_pures. wp_op; first apply about_eq_val.
      case_bool_decide; wp_if.
      + wp_pures. iApply "HΦ".
        iPureIntro. subst. by rewrite lookup_insert.
      + wp_proj. iApply "IH".
        * iPureIntro. exists l. inversion H1. by subst.
        * iIntros (v' Hres). iApply "HΦ".
          iPureIntro. by rewrite lookup_insert_ne.
  Qed.

End dict_spec.

Section dict_str_spec.
  Context `{dG : distG Σ}.


  Fixpoint embed_list_str
           (l : list (string * ground_lang.val)) : ground_lang.val :=
    match l with
    | [] => InjLV #()
    | (k, v) :: ps => InjRV ((#k, v), (embed_list_str ps))
    end.

  Definition is_dictionary_str (d :  ground_lang.val)
             (m : gmap string ground_lang.val) : Prop :=
    ∃ l, m = list_to_map l ∧ d = embed_list_str l ∧ NoDup (fmap fst l).

  Lemma empty_str_spec n :
    {{{ True }}}
      ⟨n; dict.empty #()⟩
    {{{ v, RET 〈 n ; v 〉; ⌜is_dictionary_str v ∅⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    do 2 wp_rec. wp_pures. iApply "HΦ".
    iExists []. repeat iSplit; auto.
    iPureIntro. constructor.
  Qed.

  Lemma remove_str_spec n (k: string) (d : ground_lang.val) m :
      {{{ ⌜is_dictionary_str d m⌝ }}}
        ⟨n; dict.remove (Val #k) (Val d)⟩
      {{{ d', RET 〈 n ; d' 〉; ⌜is_dictionary_str d' (delete k m)⌝ }}}.
  Proof.
    iIntros (Φ Hm) "HΦ".
    wp_rec. wp_closure. iLöb as "IH" forall (Φ d m Hm). wp_rec.
    destruct Hm as ([ | [key v] tail] & Hm & Hx & Hnodup).
    - unfold embed_list in *. subst. simpl. wp_pures. iApply "HΦ".
      simpl. iExists []. rewrite delete_empty. by repeat iSplit; auto.
    - simpl in Hx. subst. wp_match.
      do 2 wp_proj. wp_op.
      case_bool_decide.
      + wp_if. wp_proj. iApply "HΦ". simpl. subst.
        simplify_eq.
        rewrite delete_insert. inversion Hnodup; subst.
        * by iExists tail.
        * apply not_elem_of_list_to_map. by apply NoDup_cons_11.
      + wp_if. wp_proj. unfold list_cons.
        assert (key ≠ k). { intro. apply H. by subst. }
        wp_bind (App _ (embed_list_str tail))%E. iApply "IH".
        * inversion Hnodup. subst. by iExists tail.
        * iIntros. simpl. wp_pures. iApply "HΦ".
          simpl. destruct a as (tail' & Hdelete & Himbed & Hnodup').
          iExists ((key, v) :: tail'). repeat iSplit; iPureIntro.
          -- rewrite delete_insert_ne; auto. simpl. congruence.
          -- simpl. congruence.
          -- simpl. constructor; last done.
             unshelve eapply not_elem_of_list_to_map_2; last first.
             ++ rewrite <-Hdelete. rewrite ->lookup_delete_ne by auto.
                inversion Hnodup; subst. apply not_elem_of_list_to_map_1; done.
             ++ eauto with *.
  Qed.

  Lemma insert_str_spec n (k : string) v d m :
      {{{ ⌜is_dictionary_str d m⌝ }}}
        ⟨n; dict.insert #k (Val v) (Val d)⟩
      {{{ d', RET 〈 n; d' 〉; ⌜is_dictionary_str d' (insert k v m)⌝ }}}.
  Proof.
    iIntros (Φ) "Hdict HΦ".
    wp_rec. wp_pures. wp_bind (dict.remove #k d).
    iApply (remove_str_spec with "Hdict").
    iNext. iIntros (d' Hdict). rewrite /list_cons. wp_pures. iApply "HΦ".
    iPureIntro. destruct Hdict as (l & ? & ? & ?). exists ((k, v) :: l).
    repeat split; simpl.
    - rewrite <-H. by rewrite insert_delete.
    - by subst.
    - constructor; last done.
      unshelve eapply not_elem_of_list_to_map_2; last first.
      ++ rewrite <-H. by rewrite ->lookup_delete.
      ++ eauto with *.
  Qed.

  Lemma lookup_str_spec n (k : string) d m :
      {{{ ⌜is_dictionary_str d m⌝ }}}
        ⟨n; dict.lookup #k (Val d)⟩
      {{{ v, RET  〈 n; v 〉;
          ⌜match m !! k  with
             None => v = NONEV
           | Some p => v = SOMEV p
           end⌝ }}}.
  Proof.
    iIntros (Φ Hdict) "HΦ".
    wp_rec. wp_closure. iLöb as "IH" forall (m d Hdict); wp_rec.
    destruct Hdict as ([| [key v] l] & ? & ? & ?).
    - subst. simpl. wp_pures. iApply "HΦ".
      iPureIntro. by rewrite lookup_empty.
    - subst. simpl. wp_pures.
      case_bool_decide; wp_if.
      + wp_pures. iApply "HΦ".
        iPureIntro. subst. inversion H; by rewrite lookup_insert.
      + wp_proj. iApply "IH".
        * iPureIntro. exists l. inversion H1. by subst.
        * iIntros (v' Hres). iApply "HΦ".
          iPureIntro.
          assert (key ≠ k). { intro. apply H. by subst. }
            by rewrite lookup_insert_ne.
  Qed.

End dict_str_spec.
