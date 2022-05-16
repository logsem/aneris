From aneris.prelude Require Import misc.
From aneris.aneris_lang Require Import proofmode.
From aneris.aneris_lang Require Import inject.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.aneris_lang.lib Require Export set_code.

Set Default Proof Using "Type".

Section set_specs.
  Context `{anerisG Mdl Σ}.
  Context `[Countable A, !Inject A val].

  Definition is_set (X : gset A) (v : val) : Prop :=
    ∃ (l : list A), is_list l v ∧ X = list_to_set l ∧ NoDup l.

  Lemma wp_set_empty ip :
    {{{ True }}}
      set_empty #() @[ip]
    {{{ v, RET v; ⌜is_set ∅ v⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures. iApply "HΦ".
    iExists []. repeat iSplit; auto.
    iPureIntro; by apply NoDup_nil.
  Qed.

  Lemma wp_set_add ip x X v :
    {{{ ⌜is_set X v⌝ }}}
      set_add $x v @[ip]
    {{{ v, RET v; ⌜is_set ({[ x ]} ∪ X) v⌝}}}.
  Proof.
    iIntros (Φ (l & ? & -> & Hdup)) "HΦ".
    wp_rec; wp_pures.
    wp_apply (wp_list_mem with "[//]").
    iIntros ([] Hb); wp_if.
    - iApply "HΦ". iPureIntro.
      exists l. do 2 (split; auto).
      set_solver.
    - wp_apply (wp_list_cons with "[//]").
      iIntros (v' Hv').
      iApply "HΦ". iPureIntro.
      eexists (_ :: _).
      repeat split; auto.
      destruct Hb; subst; constructor; auto with set_solver.
  Qed.

  Lemma wp_set_mem ip x X v :
    {{{ ⌜is_set X v⌝ }}}
      set_mem $x v @[ip]
   {{{ (b : bool), RET #b; ⌜if b then x ∈ X else x ∉ X⌝ }}}.
  Proof.
    iIntros (Φ (l & ? & -> & ?)) "HΦ".
    iApply (wp_list_mem with "[//]").
    iIntros ([] Hb); iApply "HΦ"; iPureIntro.
    { set_solver. }
    destruct Hb; set_solver.
  Qed.

  Lemma wp_set_iter Φ1 Φ2 Ψ P ip (X : gset A) v handler :
    (∀ (x : A) (X' : gset A),
       {{{ ⌜x ∈ X⌝ ∗ P ∗ Ψ X' ∗ Φ1 x }}}
         (Val handler) $x @[ip]
       {{{v, RET v; P ∗ Ψ (X' ∪ {[x]}) ∗ Φ2 x }}}) -∗
    {{{ ⌜is_set X v⌝ ∗ P ∗ Ψ ∅ ∗ [∗ set] x ∈ X, Φ1 x }}}
      set_iter (Val handler) (Val v) @[ip]
    {{{ RET #(); P ∗ Ψ X ∗ [∗ set] x ∈ X, Φ2 x }}}.
  Proof.
    iIntros "#Hhandler".
    iIntros "!#" (Ξ) "(%HX & HP & HΨ & HΦ1) HΞ".
    destruct HX as (l & ? & -> & Hdup).
    rewrite !big_sepS_list_to_set //.
    rewrite /set_iter.
    wp_apply (wp_list_iter_invariant Φ1 Φ2 (λ l, Ψ (list_to_set l)) P
                with "[] [$HP $HΦ1 $HΨ //]"); [|done].
    iIntros (a l') "!#". iIntros (Ξ') "([%l'' %] & HP & HΨ & HΦ1) HΞ' ".
    wp_apply ("Hhandler" $! a (list_to_set l')
                with "[-HΞ']"); last first.
    { rewrite list_to_set_app_L /= union_empty_r_L //. }
    iFrame. iPureIntro. set_solver.
  Qed.

  Lemma wp_set_foldl P Φ Ψ ip handler (X : gset A) acc v :
    (∀ (a : A) acc Xacc,
        {{{ P Xacc acc ∗ Φ a }}}
          (Val handler) (Val acc) $a @[ip]
        {{{v, RET v; P (Xacc ∪ {[a]}) v ∗ Ψ a }}}) -∗
    {{{ ⌜is_set X v⌝ ∗ P ∅ acc ∗ [∗ set] a ∈ X, Φ a }}}
      set_foldl handler acc v @[ip]
    {{{v, RET v; P X v ∗ [∗ set] a ∈ X, Ψ a }}}.
  Proof.
    iIntros "#Hhandler !#" (Ξ) "(%HX & HP & HΦ) HΞ".
    destruct HX as (l & ? & -> & Hdup).
    rewrite !big_sepS_list_to_set // /set_fold.
    wp_apply (wp_list_fold (λ l v, P (list_to_set l) v) Φ Ψ with "[] [$HP $HΦ //]").
    { iIntros (????) "!#". iIntros (Ξ') "(% & HP & HΦ) HΞ'".
      wp_apply ("Hhandler" with "[$HP $HΦ]").
      rewrite list_to_set_app_L /= union_empty_r_L //. }
    iIntros (?) "[? ?]".
    iApply "HΞ". iFrame.
    rewrite big_sepS_list_to_set //.
  Qed.

  Lemma wp_set_subseteq ip X Y xv yv:
    {{{ ⌜is_set X xv⌝ ∗ ⌜is_set Y yv⌝}}}
      set_subseteq (Val xv) (Val yv) @[ip]
    {{{ (b : bool), RET #b; ⌜if b then X ⊆ Y else X ⊈ Y⌝ }}}.
  Proof.
    iIntros (Φ) "[%HX %HY] HΦ".
    destruct HX as (Xl & ? & -> & ?).
    rewrite /set_subseteq. wp_pures.
    wp_apply (wp_list_forall (λ x, ⌜x ∈ Y⌝) (λ x, ⌜x ∉ Y⌝) with "[] [//]")%I.
    { iIntros (x v Ψ) "!#". iIntros "HΨ".
      wp_pures. wp_apply (wp_set_mem with "[//]").
      iIntros ([] ?); by iApply "HΨ". }
    iIntros ([]) "Hb".
    - iApply "HΦ".
      rewrite elem_of_subseteq.
      iIntros (x Hx%elem_of_list_to_set).
      rewrite big_sepL_elem_of //.
    - iApply "HΦ". iDestruct "Hb" as (x) "[% %]".
      iPureIntro; set_solver.
  Qed.

  Lemma wp_set_equal ip X Y xv yv:
    {{{ ⌜is_set X xv⌝ ∗ ⌜is_set Y yv⌝}}}
      set_equal (Val xv) (Val yv) @[ip]
    {{{ (b : bool), RET #b; ⌜if b then X = Y else X ≠ Y⌝ }}}.
  Proof.
    iIntros (Φ) "[%HX %HY] HΦ".
    rewrite /set_equal. wp_pures.
    wp_apply (wp_set_subseteq); [auto|].
    iIntros ([] ?); wp_if; last first.
    { iApply "HΦ". iPureIntro; set_solver. }
    wp_apply (wp_set_subseteq); [auto|].
    iIntros ([] ?); iApply "HΦ"; iPureIntro; set_solver.
  Qed.

  Lemma wp_set_forall Φ Ψ ip X xv (fv : val) :
    (∀ (a : A),
        {{{ True }}}
          fv $a @[ip]
        {{{ (b : bool), RET #b; if b then Φ a else Ψ a }}}) -∗
    {{{ ⌜is_set X xv⌝ }}}
      list_forall fv xv @[ip]
    {{{ (b : bool), RET #b; if b then [∗ set] x ∈ X, Φ x else ∃ x, ⌜x ∈ X⌝ ∗ Ψ x }}}.
  Proof.
    iIntros "#Hfv !#" (Ξ (?&?&->&?)) "HΞ".
    wp_apply (wp_list_forall with "[//] [//]").
    iIntros ([]) "Hb"; iApply "HΞ".
    { rewrite  big_sepS_list_to_set //. }
    iDestruct "Hb" as (?) "[% ?]".
    iExists _. rewrite elem_of_list_to_set. eauto.
  Qed.

  Lemma wp_set_cardinal ip X xv  :
    {{{ ⌜is_set X xv⌝ }}}
      set_cardinal xv @[ip]
    {{{ RET #(size X); True }}}.
  Proof.
    iIntros (Φ (?&?&->&?)) "HΦ".
    rewrite /set_cardinal.
    wp_apply wp_list_length; [done|].
    iIntros (n ->).
    rewrite list_to_set_size //.
    by iApply "HΦ".
  Qed.

End set_specs.

Global Arguments wp_set_empty : clear implicits.
Global Arguments wp_set_empty {_ _ _} _ {_ _ _}.
