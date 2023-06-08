From aneris.prelude Require Import misc.
From aneris.aneris_lang Require Import lang proofmode.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang.lib Require Export list_code.

Set Default Proof Using "Type".

Fixpoint inject_list `{!Inject A val} xs :=
  match xs with
  | [] => NONEV
  | x :: xs' => SOMEV ($x, inject_list xs')
  end.

Global Program Instance Inject_list `{!Inject A val} : Inject (list A) val :=
  {| inject := inject_list |}.
Next Obligation.
  intros ? [] xs. induction xs as [|x xs IH]; simpl.
  - intros []; by inversion 1.
  - intros []; [by inversion 1|].
    inversion 1 as [H'].
    f_equal; [by apply (inj _)|].
    by apply IH.
Qed.

Section list_specs.
  Context `{dG : anerisG Mdl Σ}.
  Context `[!Inject A val].

  Fixpoint is_list (l : list A) (v : val) :=
    match l with
    | [] => v = NONEV
    | a::l' => ∃ lv, v = SOMEV ($a, lv) ∧ is_list l' lv
  end.

  Lemma is_list_inject xs v :
    is_list xs v ↔ v = $xs.
  Proof.
    revert v.
    induction xs as [|x xs IH]; [done|]. split.
    - destruct 1 as (? & -> & ?). simpl.
      do 2 f_equal. by apply IH.
    - intros ->. eexists. split; [done|]. by apply IH.
  Qed.

  Lemma wp_list_nil ip :
    {{{ True }}}
      [] @[ip]
    {{{ v, RET v; ⌜is_list [] v⌝}}}.
  Proof. iIntros (Φ) "_ HΦ". wp_pures. by iApply "HΦ". Qed.

  Lemma wp_list_cons a l lv ip :
    {{{ ⌜is_list l lv⌝ }}}
      $a :: lv @[ip]
    {{{ v, RET v; ⌜is_list (a::l) v⌝}}}.
  Proof.
    iIntros (Φ) "% HΦ". wp_lam. wp_pures.
    iApply "HΦ". iPureIntro; by eexists.
  Qed.

  Lemma wp_list_singleton ip a :
    {{{ True }}}
      [$a] @[ip]
    {{{ v, RET v; ⌜is_list [a] v⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ". wp_pures.
    wp_apply (wp_list_cons _ []); [done|].
    iIntros (v' Hv').
    by iApply "HΦ".
  Qed.

  Lemma wp_list_head ip lv l :
    {{{ ⌜is_list l lv⌝ }}}
      list_head lv @[ip]
    {{{ v, RET v;
        ⌜(l = [] ∧ v = NONEV) ∨ (∃ a l', l = a :: l' ∧ v = SOMEV $a)⌝ }}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_lam. destruct l; simpl in *; subst.
    - wp_pures. iApply "HΦ". iPureIntro. by left.
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      wp_pures. iApply "HΦ". iPureIntro. right. eauto.
  Qed.

  Lemma wp_list_tail ip lv l :
    {{{ ⌜is_list l lv⌝ }}}
      list_tail lv @[ip]
    {{{ v, RET v; ⌜is_list (tail l) v⌝}}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_lam. destruct l; simpl in *; subst.
    - wp_match. wp_inj. by iApply "HΦ".
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      wp_match. wp_proj. by iApply "HΦ".
  Qed.

  Lemma wp_list_length ip l lv :
    {{{ ⌜is_list l lv⌝ }}}
      list_length lv @[ip]
    {{{ v, RET #v; ⌜v = length l⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec.
    - wp_match. iApply ("HΦ" $! 0%nat); done.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_proj. wp_bind (list_length _).
      iApply ("IH" $! _ _ Hlcoh). iNext. iIntros; simpl.
      wp_op. iSpecialize ("HΦ" $! (1 + v)%nat).
      rewrite Nat2Z.inj_add. iApply "HΦ"; by auto.
  Qed.

  Lemma wp_list_iter_invariant' Φ1 Φ2 (Ψ: list A -> iProp Σ) P ip l lv handler
         lrest:
    (∀ (a : A) l',
        {{{ ⌜∃ b, lrest ++ l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}}
          (Val handler) $a @[ip]
        {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ Ψ lrest ∗ [∗ list] a∈l, Φ1 a}}}
      list_iter (Val handler) lv @[ip]
    {{{ RET #(); P ∗ Ψ (lrest++l) ∗ [∗ list] a∈l, Φ2 a }}}.
  Proof.
    rewrite /list_iter.
    iInduction l as [|a l'] "IH" forall (lv lrest);
    iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl & HΦ) Hk";
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
    - rewrite app_nil_r. iApply "Hk"; iFrame. done.
    - assert (Helemof: a ∈ a :: l').
      { constructor. }
      destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_pures.
      iDestruct (big_sepL_cons with "HΦ") as "[Ha Hl']".
      wp_apply ("Helem" with "[HP Hl Ha]"); iFrame; eauto.
      iIntros (v) "(HP & Ha & HΦ)". simpl. wp_seq.
      iApply ("IH" $! lv' (lrest ++ [a]) with "[] [$HP Ha Hl']"); eauto.
      { iIntros (a' lrest' HΦ'') "!# (%Hin'&HP&Hlrest'&HΦ) Hk".
        wp_apply ("Helem" with "[HP Hlrest' HΦ]"); iFrame.
        iPureIntro. destruct Hin' as [b Hin']. exists b.
        by rewrite -app_assoc in Hin'. }
      { iSplit; eauto. iFrame. }
      iNext. iIntros "(HP & Hl)". iApply "Hk". iFrame.
        by rewrite -app_assoc /=.
  Qed.

  Lemma wp_list_iter_invariant Φ1 Φ2 (Ψ: list A -> iProp Σ) P ip l lv handler :
    (∀ (a : A) l',
        {{{ ⌜∃ b, l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}}
          (Val handler) (Val $a) @[ip]
        {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ Ψ [] ∗ [∗ list] a∈l, Φ1 a}}}
      list_iter (Val handler) lv @[ip]
    {{{ RET #(); P ∗ Ψ l ∗ [∗ list] a∈l, Φ2 a}}}.
  Proof.
    replace l with ([]++l); last by apply app_nil_l.
    iApply wp_list_iter_invariant'.
  Qed.

  Lemma wp_list_iter_idx_aux n Φ Ψ P ip l lv handler :
    (∀ i (a : A),
        {{{ P ∗ Φ i a }}}
          (Val handler) (Val $ a) @[ip]
        {{{v, RET v; P ∗ Ψ i a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] i↦a ∈ l, Φ (n + i)%nat a }}}
      list_iter (Val handler) lv @[ip]
    {{{ RET #(); P ∗ [∗ list] i↦a ∈ l, Ψ (n + i)%nat a }}}.
  Proof.
    rewrite /list_iter.
    iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl) HΦ".
    iLöb as "IH" forall (l lv n);
    destruct l as [|a l'];
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
    - wp_pures. iApply "HΦ"; eauto.
    - assert (Helemof: a ∈ a :: l').
      { constructor. }
      destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_pures.
      iDestruct (big_sepL_cons with "Hl") as "[Ha Hl']".
      wp_apply ("Helem" with "[HP Ha]"); iFrame; eauto.
      iIntros (v) "[HP Ha]". simpl. wp_seq.
      iApply ("IH" $! l' _ (S n) with "[] [$HP] [Hl']"); [done| |].
      { iApply (big_sepL_impl with "Hl' []").
        iIntros "!>" (k x Hlookup) "H".
        replace (n + S k)%nat with (S n + k)%nat by lia.
        done. }
      iNext. iIntros "(HP & Hl)". iApply "HΦ". iFrame.
      iApply (big_sepL_impl with "Hl []").
      iIntros "!>" (k x Hlookup) "H".
      replace (n + S k)%nat with (S n + k)%nat by lia.
      done.
  Qed.

  Lemma wp_list_iter_idx Φ Ψ P ip l lv handler :
    (∀ i (a : A),
        {{{ P ∗ Φ i a }}}
          (Val handler) (Val $ a) @[ip]
        {{{v, RET v; P ∗ Ψ i a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] i↦a ∈ l, Φ i a }}}
      list_iter (Val handler) lv @[ip]
    {{{ RET #(); P ∗ [∗ list] i↦a ∈ l, Ψ i a }}}.
  Proof.
    iIntros "#H" (Φ') "!# (%Ha & HP & Hl) HΦ".
    iApply (wp_list_iter_idx_aux 0 Φ _ _ _ _ lv with "[H] [HP $Hl] HΦ").
    { iIntros (i a). iApply "H". }
    by iFrame.
  Qed.

  Lemma wp_list_iter Φ Ψ P ip l lv handler :
    (∀ (a : A),
        {{{ P ∗ Φ a }}}
          (Val handler) (Val $ a) @[ip]
        {{{v, RET v; P ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P ∗ [∗ list] a ∈ l, Φ a }}}
      list_iter (Val handler) lv @[ip]
    {{{ RET #(); P ∗ [∗ list] a ∈ l, Ψ a }}}.
  Proof.
    rewrite /list_iter.
    iIntros "#H" (Φ') "!# (%Ha & HP & Hl) HΦ".
    iApply (wp_list_iter_idx with "[H] [HP $Hl] HΦ").
    { iIntros (i a). iApply "H". }
    by iFrame.
  Qed.

  Lemma wp_list_iteri_loop
        (k : nat) (l : list A) (fv lv : val)
        (P : iProp Σ) (Φ Ψ : nat -> A -> iProp Σ) ip :
    is_list l lv →
    (∀ (i : nat) (x : A),
      {{{ P ∗ Φ i x }}} fv #i $x @[ip] {{{ v, RET v; P ∗ Ψ i x }}}) -∗
    {{{ P ∗ ([∗ list] i ↦ a ∈ l, Φ (k+i)%nat a) }}}
      list_iteri_loop fv #k lv @[ip]
    {{{ RET #(); P ∗ [∗ list] i ↦ a ∈ l, Ψ (k+i)%nat a }}}.
  Proof.
    iIntros (Hl) "#Hf".
    iIntros (Φ') "!> [HP Hl] HΦ".
    iInduction l as [ | h l] "IH" forall (lv k Hl).
    { wp_lam. rewrite Hl. wp_pures. iApply "HΦ". by iFrame. }
    wp_lam. destruct Hl as [l' [-> Hl']]. wp_pures.
    iDestruct "Hl" as "[Ha Hl']". rewrite right_id_L.
    wp_apply ("Hf" with "[$HP $Ha]"). iIntros (v) "[HP HΨ]".
    wp_pures.
    replace (Z.add (Z.of_nat k) (Zpos xH)) with (Z.of_nat (k + 1)) by lia.
    iApply ("IH" $!l' (k+1)%nat with "[//] HP [Hl'] [HΨ HΦ]").
    { iApply (big_sepL_impl with "Hl'").
      iIntros "!>" (i x HSome) "HΦ".
      replace (k + S i)%nat with (k + 1 + i)%nat by lia. done. }
    iIntros "!> [HP Hl]".
    iApply "HΦ"=> /=. rewrite right_id_L. iFrame.
    iApply (big_sepL_impl with "Hl").
    iIntros "!>" (i x HSome) "HΦ".
    by replace (k + S i)%nat with (k + 1 + i)%nat by lia.
  Qed.

  Lemma wp_list_iteri
        (l : list A) (fv lv : val)
        (P : iProp Σ) (Φ Ψ : nat -> A -> iProp Σ) ip :
    is_list l lv →
    (∀ (i : nat) (x : A),
      {{{ P ∗ Φ i x }}} fv #i $x @[ip] {{{ v, RET v; P ∗ Ψ i x }}}) -∗
    {{{ P ∗ ([∗ list] i ↦ a ∈ l, Φ i a) }}}
      list_iteri fv lv @[ip]
    {{{ RET #(); P ∗ [∗ list] i ↦ a ∈ l, Ψ i a }}}.
  Proof.
    iIntros (Hl) "#Hf". iIntros (Φ') "!>[HP Hown] HΦ".
    wp_lam. wp_pures.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (wp_list_iteri_loop 0 l with "Hf [$HP $Hown]"); [done|].
    by iFrame.
  Qed.

  Lemma wp_list_fold P Φ Ψ ip handler (l : list A) acc lv :
    (∀ (a : A) acc lacc lrem,
        {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
          (Val handler) (Val acc) $a @[ip]
        {{{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
      list_fold handler acc lv @[ip]
    {{{v, RET v; P l v ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
    change l with ([] ++ l) at 1 4.
    generalize (@nil A) at 1 3 4 as lproc => lproc.
    iInduction l as [|x l] "IHl" forall (Ξ lproc acc lv) "Hacc Hl HΞ".
    - iDestruct "Hl" as %?; simpl in *; simplify_eq.
      wp_rec. wp_pures. iApply "HΞ".
      rewrite app_nil_r; iFrame.
    - iDestruct "Hl" as %[lw [? Hlw]]; subst.
      iDestruct "HΦ" as "[Hx HΦ]".
      wp_rec. wp_pures.
      wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
      iNext. iIntros (w) "[Hacc HΨ]"; simpl. wp_pures.
      iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
      { rewrite -app_assoc; auto. }
      iNext. iIntros (v) "[HP HΨs]".
      rewrite -app_assoc.
      iApply "HΞ"; iFrame.
  Qed.

  Lemma wp_list_fold_generalized' ip handler (l lp : list A) acc lv P Φ Ψ :
    □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
      (∀ (a : A) acc lacc lrem,
          {{{ ⌜lp ++ l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
            (Val handler) (Val acc) $a @[ip]
          {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P lp acc None l ∗ [∗ list] a∈l, Φ a }}}
      list_fold (Val handler) (Val acc) (Val lv) @[ip]
    {{{v, RET v; P (lp ++ l) v None [] ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hvs #Hcl". iIntros (Ξ) "!# (Hl & Hacc & HΦ) HΞ".
    iInduction l as [|x l] "IHl" forall (Ξ lp acc lv) "Hacc Hl HΞ".
    - iDestruct "Hl" as %?; simpl in *; simplify_eq.
      wp_rec. wp_pures. iApply "HΞ".
      rewrite app_nil_r; iFrame.
    - iDestruct "Hl" as %[lw [? Hlw]]; subst.
      iDestruct "HΦ" as "[Hx HΦ]".
      wp_rec; wp_pures.
      iPoseProof ("Hvs" with "Hacc") as "Hacc".
      wp_apply ("Hcl" with "[$Hacc $Hx] [-]"); auto.
      iNext. iIntros (w) "[Hacc HΨ]"; simpl. wp_let.
      iApply ("IHl" with "[] [$HΦ] [$Hacc] [] [HΨ HΞ]"); [|auto|].
      { rewrite -app_assoc; auto. }
      iNext. iIntros (v) "[HP HΨs]".
      rewrite -app_assoc.
      iApply "HΞ"; iFrame.
  Qed.

  Lemma wp_list_fold' ip handler (l : list A) acc lv P Φ Ψ :
    □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
      (∀ (a : A) acc lacc lrem,
          {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
            (Val handler) (Val acc) $a @[ip]
          {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ ∗ P [] acc None l ∗ [∗ list] a∈l, Φ a }}}
      list_fold (Val handler) (Val acc) lv @[ip]
    {{{v, RET v; P l v None [] ∗ [∗ list] a∈l, Ψ a }}}.
  Proof.
    iIntros "#Hvs #Hcl".
    iApply (wp_list_fold_generalized' _ handler l [] with "[-]"); eauto.
  Qed.

  Lemma wp_list_sub ip k l lv  :
    {{{ ⌜is_list l lv⌝ }}}
      list_sub #k lv @[ip]
    {{{ v, RET v; ⌜is_list (take k l) v ⌝}}}.
  Proof.
   iIntros (Φ) "Hcoh HΦ".
   iInduction l as [|a l'] "IH" forall (k lv Φ);
   iDestruct "Hcoh" as %Hcoh; simpl in Hcoh; subst; wp_rec;
   wp_pures; case_bool_decide; wp_if; wp_pures.
   - iApply "HΦ"; by rewrite take_nil.
   - iApply "HΦ"; by rewrite take_nil.
   - iApply "HΦ". assert (k = O) as H1 by lia. by rewrite H1 firstn_O.
   - destruct Hcoh as [lv' [Hlv Hlcoh]]; subst.
     wp_match. wp_proj. wp_bind (list_sub _ _). wp_op.
     destruct k as [|k]; first done.
     assert (((Z.of_nat (S k)) - 1)%Z = Z.of_nat k) as -> by lia.
     iApply ("IH" $! k _ _ Hlcoh). iIntros (tl Hcoh_tl).
     iNext. wp_pures. rewrite firstn_cons. by wp_apply (wp_list_cons).
  Qed.

  Lemma wp_list_nth ip (i: nat) l lv  :
   {{{ ⌜is_list l lv⌝ }}}
      list_nth (Val lv) #i @[ip]
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜length l <= i⌝) ∨
              ⌜∃ r, v = SOMEV $r ∧ nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec; wp_let.
    - wp_match. wp_pures.
      iApply ("HΦ" $! (InjLV #())). iLeft. simpl. eauto with lia.
    - destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_pures. case_bool_decide; wp_pures.
      + iApply "HΦ". iRight. simpl. iExists a. by destruct i.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        iApply ("IH" $! i lv' _  Hlcoh).
        iNext. iIntros (v [ (Hv & Hs) | Hps]); simpl.
        * iApply "HΦ"; try eauto with lia.
        * iApply "HΦ"; try eauto with lia.
  Qed.

  Lemma wp_list_nth_some ip (i: nat) l lv  :
    {{{  ⌜is_list l lv ∧ i < length l⌝  }}}
      list_nth (Val lv) #i @[ip]
    {{{ v, RET v; ⌜∃ r, v = SOMEV $r ∧ nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Φ (Hcoh & Hi)) "HΦ".
    iApply (wp_list_nth $! Hcoh).
    iIntros (v [H | H]); first eauto with lia.
    by iApply "HΦ".
  Qed.

  Lemma wp_list_mem `{!EqDecision A} ip (l : list A) lv a :
    {{{ ⌜is_list l lv⌝ }}}
      list_mem $a lv @[ip]
    {{{ (b : bool), RET #b; if b then ⌜a ∈ l⌝ else ⌜a ∉ l ∨ l = nil⌝ }}}.
  Proof.
    iIntros (Φ).
    iInduction l as [|a' l'] "IH" forall (lv Φ);
      iIntros (Hl) "HΦ"; wp_rec; wp_pures.
    - rewrite Hl. wp_pures. iApply "HΦ". auto.
    - destruct Hl as [lv' [-> Hl']]. wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      case_bool_decide as Heq; wp_if.
      { simplify_eq. iApply "HΦ". iPureIntro; set_solver. }
      iApply ("IH" with "[//]").
      iIntros "!>" ([] Ha).
      { iApply "HΦ". iPureIntro; set_solver. }
      iApply "HΦ".
      iPureIntro. left.
      simplify_eq.
      apply not_inj_fn in Heq; [|apply _].
      destruct Ha; set_solver.
  Qed.

  Lemma wp_find_remove ip (l : list A) lv (Ψ : A → iProp Σ) (fv : val) :
    (∀ (a : A),
        {{{ True }}}
          fv $a @[ip]
        {{{ (b : bool), RET #b; if b then Ψ a else True }}}) -∗
    {{{ ⌜is_list l lv⌝ }}}
      list_find_remove fv lv @[ip]
    {{{ v, RET v; ⌜v = NONEV⌝ ∨
                       ∃ e lv' l1 l2,
                         ⌜l = l1 ++ e :: l2 ∧
                         v = SOMEV ($e, lv') ∧
                         is_list (l1 ++ l2) lv'⌝
                         ∗ Ψ e}}}.
  Proof.
    iIntros "#Hf" (Φ).
    iInduction l as [|a l'] "IH" forall (lv Φ);
      iIntros (Hl) "!> HΦ"; wp_rec; wp_pures.
    { rewrite Hl. wp_pures. iApply "HΦ".
      iLeft; iPureIntro; split; set_solver. }
    destruct Hl as [lv' [-> Hl']]. wp_pures.
    wp_bind (fv _). iApply ("Hf" with "[//]").
    iIntros "!>" (b) "Hb /=".
    destruct b.
    { wp_pures.
      iApply "HΦ".
      iRight; iExists _, _, [], _; eauto. }
    wp_pures.
    wp_bind (list_find_remove _ _).
    iApply ("IH" with "[//]").
    iIntros "!>" (w) "[->| He] /="; wp_pures.
    { iApply "HΦ".
      iLeft; done. }
    iDestruct "He" as (e lv'' l1 l2) "[He HHΨ]".
    iDestruct "He" as %(-> & -> & Hlv'').
    wp_pures.
    wp_bind (list_cons _ _). iApply wp_list_cons; [done|].
    iIntros "!>" (v Hcoh) "/=". wp_pures.
    iApply "HΦ". iRight.
    iExists _, _, (_ :: _), _; eauto.
  Qed.

  Local Lemma wp_list_rev_aux ip l lM r rM:
   {{{ ⌜is_list lM l ∧ is_list rM r⌝ }}}
     list_rev_aux (Val l) (Val r) @[ip]
   {{{ v, RET v; ⌜is_list (rev_append lM rM) v⌝ }}}.
  Proof.
    iIntros (? [Hl Hr]) "H".
    iInduction lM as [|a lM] "IH" forall (l r rM Hl Hr).
    - simpl in *; subst. rewrite /list_rev_aux. wp_pures. by iApply "H".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      wp_rec; wp_pures.
      wp_apply wp_list_cons; [done|].
      iIntros (w Hw).
      wp_pures. by iApply "IH".
 Qed.

  Lemma wp_list_rev ip l lM :
    {{{ ⌜is_list lM l⌝ }}}
      list_rev (Val l) @[ip]
    {{{ v, RET v; ⌜is_list (reverse lM) v⌝ }}}.
  Proof.
    iIntros (??) "H". rewrite /list_rev. wp_pures.
    by iApply (wp_list_rev_aux _ _ _ NONEV []).
  Qed.

  Lemma wp_list_append ip l lM r rM :
    {{{ ⌜is_list lM l⌝ ∗ ⌜is_list rM r⌝}}}
      list_append (Val l) (Val r) @[ip]
    {{{ v, RET v; ⌜is_list (lM ++ rM) v⌝ }}}.
  Proof.
    iIntros (Φ) "[%Hl %Hr] HΦ". rewrite /list_append.
    iInduction lM as [|a lM] "IH" forall (l r Hl Hr Φ).
    - simpl in Hl; subst. wp_pures. by iApply "HΦ".
    - destruct Hl as [l' [Hl'eq Hl']]; subst.
      do 12 wp_pure _.
      wp_bind (((rec: "list_append" _ _:= _)%V _ _)).
      iApply "IH"; [done..|].
      iIntros "!>" (v Hv).
      by wp_apply wp_list_cons.
  Qed.

  Lemma wp_list_forall Φ Ψ ip (l : list A) lv (fv : val) :
    (∀ (a : A),
        {{{ True }}}
          fv $a @[ip]
        {{{ (b : bool), RET #b; if b then Φ a else Ψ a }}}) -∗
    {{{ ⌜is_list l lv⌝ }}}
      list_forall fv lv @[ip]
    {{{ (b : bool), RET #b; if b then [∗ list] a ∈ l, Φ a else ∃ a, ⌜a ∈ l⌝ ∗ Ψ a }}}.
  Proof.
    rewrite /list_forall.
    iInduction l as [|a l'] "IH" forall (lv);
      iIntros "#Hfv" (Ξ) "!# %Hl HΞ".
    - simpl in Hl; subst. wp_pures. iApply "HΞ"; auto.
    - destruct Hl as [l'' [Hl'eq Hl']]; subst.
      wp_pures.
      wp_apply "Hfv"; [done|].
      iIntros ([]) "Hb".
      + wp_if. iApply ("IH"); [done..|].
        iIntros "!>" ([]).
        * iIntros "Ha". iApply "HΞ".
          rewrite big_sepL_cons. iFrame.
        * iDestruct 1 as (a') "[% ?]".
          iApply "HΞ". iExists _. iFrame.
          iPureIntro. apply elem_of_cons. by right.
      + wp_if. iApply "HΞ". iExists _. iFrame.
        iPureIntro. apply elem_of_cons. by left.
  Qed.

  Lemma wp_list_is_empty l v ip :
    {{{ ⌜is_list l v⌝ }}}
      list_is_empty v @[ip]
    {{{ v, RET #v;
        ⌜v = match l with [] => true | _ => false end⌝ }}}.
  Proof.
    iIntros (Φ Hl) "HΦ". wp_rec. destruct l.
    - rewrite Hl. wp_pures. by iApply "HΦ".
    - destruct Hl as [? [-> _]]. wp_pures. by iApply "HΦ".
  Qed.

  Lemma is_list_eq lM :
    ∀ l1 l2, is_list lM l1 → is_list lM l2 → l1 = l2.
  Proof. induction lM; intros []; naive_solver eauto with f_equal. Qed.

  Lemma is_list_inv_l l:
    ∀ lM1 lM2, is_list lM1 l → lM1 = lM2 → is_list lM2 l.
  Proof. by intros ? ? ? <-. Qed.

  Lemma is_list_snoc lM x : ∃ lv, is_list (lM ++ [x]) lv.
  Proof. induction lM; naive_solver eauto. Qed.

  Definition str_val (l : list string) : list val :=
    map (λ (str : string), #str) l.

  Lemma wp_list_filter (l : list A) (P : A -> bool) (f lv : val) ip :
    {{{ (∀ (x : A),
            {{{ True }}}
              f $x @[ip]
            {{{ w, RET w; ⌜w = $(P x)⌝ }}} ) ∗
        ⌜is_list l lv⌝ }}}
       list_filter f lv @[ip]
     {{{ rv, RET rv; ⌜is_list (List.filter P l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil.
    - subst.
      rewrite /list_filter; wp_pures.
      iApply "HΦ"; done.
    - destruct Hil as (lv' & -> & Hil).
      rewrite /list_filter.
      do 7 (wp_pure _).
      fold list_filter.
      wp_apply ("IH" $! lv'); [done |].
      iIntros (rv) "%Hilp"; wp_pures.
      wp_apply "Hf"; [done |].
      iIntros (w) "->".
      destruct (P h) eqn:HP; wp_pures.
      + wp_apply wp_list_cons; [by eauto |].
        iIntros (v) "%Hil'".
        iApply "HΦ"; iPureIntro.
        simpl; rewrite HP; simpl.
        simpl in Hil'; done.
      + iApply "HΦ"; iPureIntro.
        simpl. rewrite HP. done.
  Qed.
End list_specs.

Global Arguments wp_list_nil : clear implicits.
Global Arguments wp_list_nil {_ _ _} _ {_}.

(* Start a new section because some of the specs below (e.g. wp_list_map) need
   access to the type parameter in e.g. is_list, since they operate on more than one
   list type. *)
Section list_specs_extra.
  Context `{dG : anerisG Mdl Σ}.
  Context `[!Inject A val].

  Lemma wp_list_map `{!Inject B val} (l : list A) (f : A -> B) (fv lv : val) ip :
    {{{ (∀ (x : A),
          {{{ True }}}
            fv $x @[ip]
          {{{ fr, RET fr; ⌜fr = $(f x)⌝ }}}) ∗
          ⌜is_list l lv⌝ }}}
      list_map fv lv @[ip]
    {{{ rv, RET rv; ⌜is_list (List.map f l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[#Hf %Hil] HΦ".
    iInduction l as [ | h t] "IH" forall (lv Hil Φ); simpl in Hil; try subst; rewrite /list_map.
    - wp_pures.
      iApply "HΦ"; iPureIntro.
      rewrite /is_list; done.
    - wp_pures.
      destruct Hil as (lv' & -> & Hil').
      do 4 wp_pure _.
      fold list_map.
      wp_apply "IH"; [done |].
      iIntros (rv) "%Hil_rv"; wp_pures.
      wp_apply "Hf"; [done |].
      iIntros (fr) "->".
      wp_apply wp_list_cons; [done |].
      iIntros (v) "%Hilf".
      iApply "HΦ"; auto.
  Qed.

  (* TODO: is this in some Coq library? *)
  Fixpoint mapi_loop {B : Type} (f : nat -> A -> B) (k : nat) (l : list A) : list B :=
    match l with
    | h :: t => (f k h) :: (mapi_loop f (S k) t)
    | [] => []
    end.

  Lemma mapi_loop_i {B : Type} (f : nat -> A -> B) (l : list A) (i k : nat) :
    (i < length l)%nat ->
    exists v w, l !! i = Some v ∧
           (mapi_loop f k l) !! i = Some w ∧
           w = f (k + i)%nat v.
  Proof.
    generalize dependent i.
    generalize dependent k.
    induction l as [ | h t IH]; intros k i Hlt; simpl in *.
    - exfalso; lia.
    - destruct i as [ | i']; simpl.
      { exists h, (f k h).
        replace (k + 0)%nat with k; auto. }
      apply Nat.succ_lt_mono in Hlt.
      pose proof (IH (S k) i' Hlt) as (v & w & -> & -> & Heq).
      replace (k + S i')%nat with (S k + i')%nat by lia.
      eauto.
  Qed.

  Definition mapi {B : Type} (f : nat -> A -> B) (l : list A) : list B :=
    mapi_loop f 0 l.

  Lemma mapi_i {B : Type} (f : nat -> A -> B) (l : list A) (i : nat) :
    (i < length l)%nat ->
    exists v w, l !! i = Some v ∧
           (mapi f l) !! i = Some w ∧
           w = f i v.
  Proof.
    intros Hlt.
    pose proof (mapi_loop_i f l i O Hlt) as (v & w & H1 & H2 & H3).
    eauto.
  Qed.

  (* TODO: clean up *)
  Lemma wp_list_mapi_loop `{!Inject B val}
        (f : nat -> A -> B) (k : nat) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) ip :
    {{{ □ (∀ (i : nat) (x : A),
              {{{ γ (k + i)%nat x }}}
                fv $(k + i)%nat $x @[ip]
                {{{ fr, RET fr;
                    let r := f (k + i)%nat x in
                    ⌜fr = $r⌝ ∗ ψ (k + i)%nat r }}}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ (k + i)%nat a)
    }}}
      list_mapi_loop fv #k lv @[ip]
    {{{ rv, RET rv;
        let l' := mapi_loop f k l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ (k + i)%nat a)}}}.
  Proof.
    iInduction l as [ | h l'] "IH" forall (lv k);
      iIntros (Φ) "[#Hf [%Hil Hown]] HΦ"; simpl in Hil;
      rewrite /list_mapi_loop.
    - subst.
      wp_pures.
      iApply "HΦ".
      iSplitL ""; done.
    - destruct Hil as [lv' [-> Hil']].
      do 10 wp_pure _.
      fold list_mapi_loop.
      wp_bind (list_mapi_loop _ _ _).
      iAssert (⌜#(k + 1) = #(k + 1)%nat⌝%I) as "->".
      { iPureIntro.
        do 2 apply f_equal; lia. }
      iDestruct (big_sepL_cons with "Hown") as "[Hhead Hown]".
      iApply ("IH" with "[Hown]").
      + iSplitL "".
        * iModIntro.
          iIntros (i x).
          iPoseProof ("Hf"  $! (1 + i)%nat x) as "Hf'".
          iAssert (⌜(k + (1 + i))%nat = (k + 1 + i)%nat⌝%I) as %<-.
          {  iPureIntro; by lia. }
          iApply "Hf".
        * iSplitL ""; [done |].
          iApply (big_sepL_impl with "Hown").
          iModIntro.
          iIntros (k' x) "_ Hpre".
          iAssert (⌜(k + 1 + k')%nat = (k + S k')%nat⌝%I) as %->.
          { iPureIntro; lia. }
          done.
      + iModIntro.
        iIntros (rv) "[%Hil'' Hown]".
        wp_pures.
        iAssert (⌜#k = $ (k + 0)%nat⌝%I) as %->.
        { simpl.
          iPureIntro.
          do 2 f_equal.
          lia. }
        wp_apply ("Hf" with "Hhead").
        iIntros (fr) "[-> HΨ]".
        wp_apply wp_list_cons; [done | ].
        iIntros (v) "%Hil'''".
        iApply "HΦ".
        iSplitL ""; [iPureIntro |].
        { assert (f (k + 0)%nat h :: mapi_loop f (k + 1) l' = mapi_loop f k (h :: l')) as <-.
          { simpl.
            assert ((k + 0)%nat = k) as -> by lia.
            assert (k + 1 = S k)%nat as -> by lia.
            reflexivity. }
          done. }
        simpl.
        iSplitL "HΨ".
        { assert (f k h = f (k + 0)%nat h) as ->.
          { assert (k = (k + 0))%nat as <- by lia; done. }
          done. }
        iAssert (⌜(k + 1)%nat = S k⌝%I) as %->.
        { iPureIntro.
          do 2 f_equal.
          lia. }
        iApply (big_sepL_impl with "Hown").
        iModIntro.
        iIntros (k' x) "_ HΨ".
        iAssert (⌜(S k + k')%nat = (k + S k')%nat⌝%I) as %->.
        { iPureIntro.
          lia. }
        done.
  Qed.

  Lemma wp_list_mapi `{!Inject B val}
        (f : nat -> A -> B) (l : list A) (fv lv : val)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) ip :
    {{{ □ (∀ (i : nat) (x : A),
              {{{ γ i x }}}
                fv #i $x @[ip]
                {{{ fr, RET fr;
                    let r := f i x in
                    ⌜fr = $r⌝ ∗ ψ i r }}}) ∗
        ⌜is_list l lv⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ i a)
    }}}
      list_mapi fv lv @[ip]
    {{{ rv, RET rv;
        let l' := mapi f l in
        ⌜is_list l' rv⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ i a)}}}.
  Proof.
    iIntros (Φ) "[#Hf [%Hil Hown]] HΦ".
    rewrite /list_mapi.
    do 3 wp_pure _.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (wp_list_mapi_loop with "[Hown]").
    - iSplitL ""; last first.
      + iFrame; done.
      + iModIntro.
        iIntros (i x).
        iAssert (⌜(0 + i)%nat = i⌝%I) as %->; [done |].
        iApply "Hf".
    - iModIntro.
      assert (mapi f l = mapi_loop f 0 l) as <-; [done |].
      iFrame.
  Qed.

  (* TODO: is there a standard library lemma for this? *)
  Lemma list_lookup_succ (h : A) (l : list A) (i : nat) :
    (h :: l) !! (S i) = l !! i.
  Proof. auto. Qed.

End list_specs_extra.
