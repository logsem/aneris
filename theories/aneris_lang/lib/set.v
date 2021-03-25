From aneris.aneris_lang Require Import proofmode.
From aneris.aneris_lang.lib Require Import list.
Set Default Proof Using "Type".

Definition set_empty : val := λ: <>, [].
Definition set_add : val := list_cons.
Definition set_mem : val := list_mem.

Section set_specs.
  Context `{anerisG Mdl Σ}.
  Context `{Countable A}.
  Context (toval : A → val).

  Definition is_set (X : gset A) (v : val) : Prop :=
    ∃ (l : list A), is_list (map toval l) v ∧ X = list_to_set l.

  Lemma wp_set_empty  ip :
    {{{ True }}}
      set_empty #() @[ip]
    {{{ v, RET v; ⌜is_set ∅ v⌝}}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures. iApply "HΦ".
    iExists []. repeat iSplit; auto.
  Qed.

  Lemma wp_set_add ip x X v :
    {{{ ⌜is_set X v⌝ }}}
      set_add (Val (toval x)) (Val v) @[ip]
    {{{ v, RET v; ⌜is_set ({[ x ]} ∪ X) v⌝}}}.
  Proof.
    iIntros (Φ (? & ? & ->)) "HΦ".
    wp_apply (wp_list_cons with "[//]").
    iIntros (v' Hv').
    iApply "HΦ".
    iExists (_ :: _); eauto.
  Qed.

  Lemma wp_set_mem `{!Inj (=) (=) toval} ip x X v :
    {{{ ⌜is_set X v⌝ }}}
      set_mem (Val (toval x)) (Val v) @[ip]
   {{{ (b : bool), RET #b; ⌜if b then x ∈ X else x ∉ X⌝ }}}.
  Proof.
    iIntros (Φ (l & ? & ->)) "HΦ".
    iApply (wp_list_mem _ l with "[//]"); [done|].
    iIntros ([] Hb); iApply "HΦ"; iPureIntro.
    { set_solver. }
    destruct Hb; set_solver.
  Qed.

End set_specs.
