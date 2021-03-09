From stdpp Require Export strings list pretty gmap.
From aneris.prelude Require Import quantifiers.
From aneris.aneris_lang Require Import lang network notation tactics proofmode.
From aneris.aneris_lang.lib Require Import list util.

Definition map_empty : val :=
  λ: <>, [].

Definition map_remove : val :=
  λ: "key",
  (rec: "loop" "m" :=
     match: "m" with
       NONE => NONE
     | SOME "p" =>
       if: Fst (Fst "p") = "key"
       then Snd "p"
       else Fst "p" :: "loop" (Snd "p")
     end).

Definition map_insert : val :=
  λ: "key" "val" "m", ("key", "val") :: map_remove "key" "m".

Definition map_lookup : val :=
  λ: "key",
  (rec: "loop" "m" :=
     match: "m" with
       NONE => NONE
     | SOME "p" => if: Fst (Fst "p") = "key"
                   then SOME (Snd (Fst "p"))
                   else "loop" (Snd "p")
     end).

Definition map_mem : val :=
  λ: "key" "m",
  match: map_lookup "key" "mem" with
    NONE => #false
  | SOME "p" => #true
  end.

Section map_specs.
  Context `{anerisG Mdl Σ}.
  Context `{Countable K} (f : K → val) `{!Inj (=) (=) f}.

  Fixpoint embed_list (l : list (K * val)) : val :=
    match l with
    | [] => InjLV #()
    | (k, v) :: ps => InjRV ((f k, v), embed_list ps)
    end.

  Definition is_map (d : val) (m : gmap K val) : Prop :=
    ∃ l, m = list_to_map l ∧ d = embed_list l ∧ NoDup (fmap fst l).

  Lemma wp_map_empty  ip :
    {{{ True }}}
      map_empty #() @[ip]
    {{{ v, RET v; ⌜is_map v ∅⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures. iApply "HΦ".
    iExists []. repeat iSplit; auto.
    iPureIntro. constructor.
  Qed.

  Lemma wp_map_remove ip k d m :
    {{{ ⌜is_map d m⌝ }}}
      map_remove (Val (f k)) (Val d) @[ip]
    {{{ d', RET d'; ⌜is_map d' (delete k m)⌝ }}}.
  Proof.
    iIntros (Φ Hm) "HΦ".
    wp_rec. wp_closure. iLöb as "IH" forall (Φ d m Hm). wp_rec.
    destruct Hm as ([ | [key v] tail] & Hm & Hx & Hnodup); simplify_eq/=.
    - wp_pures. iApply "HΦ". iExists []. rewrite delete_empty //.
    - wp_pures. wp_op; first apply bin_op_eval_eq_val.
      case_bool_decide as Heq.
      + wp_pures. iApply "HΦ". apply (inj f) in Heq. subst.
        rewrite delete_insert; inversion Hnodup; subst.
        * by iExists tail.
        * by apply not_elem_of_list_to_map.
      + apply inj_neq in Heq; [|apply _].
        wp_if. wp_proj.
        wp_bind (App _ (embed_list tail))%E. iApply "IH".
        { inversion Hnodup. subst. by iExists tail.  }
        iIntros (? a).
        rewrite /list_cons.
        wp_pures.
        iApply "HΦ". destruct a as (tail' & Hdelete & Himbed & Hnodup').
        iExists ((key, v) :: tail').
        repeat iSplit; iPureIntro.
        * rewrite delete_insert_ne//=. congruence.
        * simpl. congruence.
        * simpl. constructor; last done.
          eapply (@not_elem_of_list_to_map_2 _ (gmap K)); first apply _.
          rewrite -Hdelete. rewrite lookup_delete_ne //.
          inversion Hnodup; subst. apply not_elem_of_list_to_map_1; done.
  Qed.

  Lemma wp_map_insert ip k v d m :
    {{{ ⌜is_map d m⌝ }}}
      map_insert (Val (f k)) (Val v) (Val d) @[ip]
    {{{ d', RET d'; ⌜is_map d' (<[ k := v ]> m)⌝ }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    wp_rec. wp_pures. wp_bind (map_remove _ _).
    iApply (wp_map_remove with "Hm").
    iNext. iIntros (d' Hm).
    rewrite /list_cons. wp_pures. iApply "HΦ".
    iPureIntro. destruct Hm as (l & Hdel & ? & ?). exists ((k, v) :: l).
    repeat split; simpl.
    - rewrite -Hdel insert_delete //.
    - by subst.
    - constructor; last done.
      eapply (@not_elem_of_list_to_map_2 _ (gmap K)); first apply _.
      rewrite -Hdel lookup_delete //.
  Qed.

  Lemma wp_map_lookup ip k d m :
    {{{ ⌜is_map d m⌝ }}}
      map_lookup (Val (f k)) (Val d) @[ip]
    {{{ v, RET v;
        ⌜match m !! k  with
           None => v = NONEV
         | Some p => v = SOMEV p
         end⌝ }}}.
  Proof.
    iIntros (Φ Hm) "HΦ".
    wp_rec. wp_closure. iLöb as "IH" forall (m d Hm); wp_rec.
    destruct Hm as ([| [key v] l] & ? & ? & Hdup).
    - subst. simpl. wp_pures. iApply "HΦ".
      iPureIntro. by rewrite lookup_empty.
    - subst. simpl. wp_pures. wp_op; first apply bin_op_eval_eq_val.
      case_bool_decide as Heq; wp_if.
      + wp_pures. iApply "HΦ".
        iPureIntro.
        apply (inj f) in Heq. subst. rewrite lookup_insert //.
      + apply inj_neq in Heq; [|apply _].
        wp_proj. iApply "IH".
        * iPureIntro. exists l. inversion Hdup. by subst.
        * iIntros (v' Hres). iApply "HΦ".
          iPureIntro. by rewrite lookup_insert_ne.
  Qed.

End map_specs.
