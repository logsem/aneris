From stdpp Require Import strings list pretty gmap.
From aneris.prelude Require Import misc.
From aneris.aneris_lang Require Import lang tactics proofmode.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang.lib Require Import list_proof set_proof.
From aneris.aneris_lang.lib Require Export map_code.

Section map_specs.
  Context `{anerisG Mdl Σ}.
  Context `[Countable K, !Inject K val].
  Context `[V : Type, !Inject V val].

  Definition is_map (d : val) (m : gmap K V) : Prop :=
    ∃ l, m = list_to_map l ∧ d = $l ∧ NoDup (fst <$> l).

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
      map_remove $k (Val d) @[ip]
    {{{ d', RET d'; ⌜is_map d' (delete k m)⌝ }}}.
  Proof.
    iIntros (Φ Hm) "HΦ".
    wp_rec. wp_closure. iLöb as "IH" forall (Φ d m Hm). wp_rec.
    destruct Hm as ([ | [key v] tail] & Hm & Hx & Hnodup); simplify_eq/=.
    - wp_pures. iApply "HΦ". iExists []. rewrite delete_empty //.
    - wp_pures. wp_op; first apply bin_op_eval_eq_val.
      case_bool_decide as Heq.
      + wp_pures. iApply "HΦ". apply (inj _) in Heq. subst.
        rewrite delete_insert; inversion Hnodup; subst.
        * by iExists tail.
        * by apply not_elem_of_list_to_map.
      + apply not_inj_fn in Heq; [|apply _].
        wp_if. wp_proj.
        wp_apply "IH".
        { inversion Hnodup. subst. by iExists tail.  }
        iIntros (? a).
        rewrite /list_cons.
        wp_pures.
        iApply "HΦ". destruct a as (tail' & Hdelete & Himbed & Hnodup').
        iExists ((key, v) :: tail').
        repeat iSplit; iPureIntro.
        * rewrite delete_insert_ne//=. congruence.
        * simpl. by repeat f_equal.
        * simpl. constructor; last done.
          eapply (@not_elem_of_list_to_map_2 _ (gmap K)); first apply _.
          rewrite -Hdelete. rewrite lookup_delete_ne //.
          inversion Hnodup; subst. apply not_elem_of_list_to_map_1; done.
  Qed.

  Lemma wp_map_insert ip k v d m :
    {{{ ⌜is_map d m⌝ }}}
      map_insert $k $v (Val d) @[ip]
    {{{ d', RET d'; ⌜is_map d' (<[ k := v ]> m)⌝ }}}.
  Proof.
    iIntros (Φ) "Hm HΦ".
    wp_rec. wp_pures. wp_bind (map_remove _ _).
    iApply (wp_map_remove with "Hm").
    iNext. iIntros (d' Hm).
    rewrite /list_cons. wp_pures. iApply "HΦ".
    iPureIntro. destruct Hm as (l & Hdel & ? & ?). exists ((k, v) :: l).
    repeat split; simpl.
    - rewrite -Hdel insert_delete_insert //.
    - by subst.
    - constructor; last done.
      eapply (@not_elem_of_list_to_map_2 _ (gmap K)); first apply _.
      rewrite -Hdel lookup_delete //.
  Qed.

  Lemma wp_map_lookup ip k d m :
    {{{ ⌜is_map d m⌝ }}}
      map_lookup $k (Val d) @[ip]
    {{{ v, RET v;
        ⌜match m !! k  with
           None => v = NONEV
         | Some p => v = SOMEV $p
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
        apply (inj _) in Heq. subst. rewrite lookup_insert //.
      + apply not_inj_fn in Heq; [|apply _].
        wp_proj. iApply "IH".
        * iPureIntro. exists l. inversion Hdup. by subst.
        * iIntros (v' Hres). iApply "HΦ".
          iPureIntro. by rewrite lookup_insert_ne.
  Qed.

  Lemma wp_map_mem ip k d m :
    {{{ ⌜is_map d m⌝ }}}
      map_mem $k (Val d) @[ip]
    {{{ (b : bool), RET #b; if b then ⌜∃ v, m !! k = Some v⌝ else True }}}.
  Proof.
    iIntros (Φ Hm) "HΦ".
    rewrite /map_mem. wp_pures.
    wp_apply wp_map_lookup; [done|].
    destruct (m !! k) eqn:Heq; iIntros (? ->);
      wp_pures; iApply "HΦ"; eauto.
  Qed.

  Lemma wp_map_dom ip d (m : gmap K V) :
    {{{ ⌜is_map d m⌝ }}}
      map_dom (Val d) @[ip]
    {{{ v, RET v; ⌜is_set (dom m) v⌝ }}}.
  Proof.
    iIntros (Φ Hd) "HΦ".
    iLöb as "IH" forall (Φ m d Hd); wp_rec.
    destruct Hd as (? & -> & -> & Hnodup).
    destruct x as [|[k v] l].
    - wp_pures.
      wp_apply wp_set_empty; [done|].
      iIntros (??). iApply "HΦ". rewrite dom_empty_L //.
    - wp_pures.
      wp_bind (map_dom _).
      wp_apply "IH".
      { inversion Hnodup. subst. by iExists l. }
      iIntros (??).
      wp_pures.
      wp_apply wp_set_add; [done|].
      iIntros (??).
      iApply "HΦ". simpl.
      rewrite dom_insert_L //.
  Qed.

  Lemma wp_map_iter (Φ Ψ : K → V → iProp Σ) P ip d m f :
    (∀ (k : K) (v : V),
        {{{ P ∗ Φ k v }}}
          (Val f) $k $v @[ip]
        {{{ RET #(); P ∗ Ψ k v }}}) -∗
    {{{ ⌜is_map d m⌝ ∗ P ∗ [∗ map] k↦v ∈ m, Φ k v }}}
      map_iter (Val f) d @[ip]
    {{{ RET #(); P ∗ [∗ map] k↦v ∈ m, Ψ k v }}}.
  Proof.
    iIntros "#Hf" (Ξ) "!# (%Hd & HP & HΦ) HΞ".
    iLöb as "IH" forall (Ξ d m Hd); wp_rec.
    wp_pures.
    destruct Hd as (? & -> & -> & Hnodup).
    destruct x as [|[k v] l].
    - wp_pures. iApply "HΞ". by iFrame.
    - wp_pures. simpl.
      iDestruct (big_sepM_insert with "HΦ") as "[Hkv Hrest]".
      { apply not_elem_of_list_to_map_1.
        inversion Hnodup; simplify_eq. set_solver. }
      wp_apply ("Hf" with "[$HP $Hkv]").
      iIntros "[HP HΨ]".
      wp_pures.
      wp_apply ("IH" with "[] HP Hrest").
      { inversion Hnodup. subst. by iExists l. }
      iIntros "[HP Hrest]".
      iApply "HΞ".
      iFrame.
      iApply (big_sepM_insert with "[$Hrest $HΨ]").
      apply not_elem_of_list_to_map_1.
      inversion Hnodup; simplify_eq.
      set_solver.
   Qed.

  Lemma wp_map_forall Φ Ψ ip d m (f : val) :
    (∀ (k : K) (v : V),
        {{{ True }}}
          f $k $v @[ip]
        {{{ (b : bool), RET #b; if b then Φ k v else Ψ k v }}}) -∗
    {{{ ⌜is_map d m⌝ }}}
      map_forall f d @[ip]
    {{{ (b : bool), RET #b;
          if b then [∗ map] k↦v ∈ m, Φ k v
          else ∃ k v , ⌜m !! k = Some v⌝ ∗ Ψ k v }}}.
  Proof.
    iIntros "#Hf" (Ξ) "!# %Hd HΞ".
    iLöb as "IH" forall (Ξ d m Hd). wp_rec.
    wp_pures.
    destruct Hd as (? & -> & -> & Hnodup).
    destruct x as [|[k v] l].
    - wp_pures. by iApply "HΞ".
    - wp_pures. wp_apply "Hf"; [done|].
      iIntros ([]) "Hb".
      + wp_pures.
        wp_apply "IH".
        { inversion Hnodup. subst. by iExists l. }
        iIntros ([]) "HΦ".
        { iApply "HΞ". simpl.
          iApply (big_sepM_insert with "[$HΦ $Hb]").
          apply not_elem_of_list_to_map_1.
          inversion Hnodup; simplify_eq.
          set_solver. }
        iApply "HΞ".
        iDestruct "HΦ" as (??) "[% ?]".
        iExists _, _. iFrame. iPureIntro.
        simpl.
        rewrite lookup_insert_ne //.
        inversion Hnodup; simplify_map_eq.
        apply elem_of_list_to_map in H1; [|set_solver].
        intros ->. apply H4.
        apply elem_of_list_fmap.
        exists (k0, v0); done.
      + wp_pures.
        iApply "HΞ".
        iExists _, _. iFrame. iPureIntro.
        rewrite lookup_insert //.
  Qed.

End map_specs.

Global Arguments wp_map_empty : clear implicits.
Global Arguments wp_map_empty {_ _ _} _ {_ _ _} _ {_}.
