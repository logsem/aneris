From iris.base_logic.lib Require Export invariants.
From aneris.aneris_lang Require Import lang proofmode notation.
From aneris.aneris_lang.lib Require Import util.
Set Default Proof Using "Type".

Import Network.

Definition list_nil : expr := NONE.
Definition list_nilV : val := NONEV.

Definition list_cons : val :=
  λ: "elem" "list", SOME (Pair "elem" "list").

Definition list_head : val :=
  λ: "l", match: "l" with
            SOME "a" => SOME (Fst "a")
          | NONE => NONE
          end.

Definition list_tail : val :=
  λ: "l", match: "l" with
            SOME "a" => (Snd "a")
          | NONE => NONE
          end.

Definition list_fold : val :=
  rec: "fold" "handler" "acc" "l" :=
    match: "l" with
      SOME "a" => let: "fst" := Fst "a" in
                  let: "snd" := Snd "a" in
                  let: "acc'" := ("handler" "acc" "fst") in
                  "fold" "handler" "acc'" "snd"
    | NONE => "acc"
    end.

Definition list_iter : val :=
  rec: "iter" "handler" "l" :=
    match: "l" with
      SOME "a" =>
      let: "tail" := Snd "a" in
      "handler" (Fst "a");;
      "iter" "handler" "tail"
    | NONE => #()
    end.

Definition list_length : val :=
  rec: "length" "l" :=
    match: "l" with
      SOME "a" => #1 + "length" (Snd "a")
    | NONE => #0
    end.

Definition list_nth : val :=
  (rec: "nth" "l" "i" :=
     match: "l" with
       SOME "a" =>
       if: "i" = #0 then SOME (Fst "a")
       else "nth" (Snd "a") ("i" - #1)
     | NONE => NONE
     end)%V.

Definition list_mem : val :=
  (rec: "find" "x" "l" :=
     match: "l" with
       SOME "a" =>
         let: "head" := Fst "a" in
         let: "tail" := Snd "a" in
         ("x" = "head") || "find" "x" "tail"
     | NONE => #false
     end).

Definition list_find_remove : val :=
  (rec: "find_remove" "f" "l" :=
     match: "l" with
       SOME "a" =>
       let: "head" := Fst "a" in
       let: "tail" := Snd "a" in
       if: "f" "head" then SOME ("head", "tail")
       else
         let: "r" := "find_remove" "f" "tail" in
         match: "r" with
           SOME "b" =>
           let: "head'" := Fst "b" in
           let: "tail'" := Snd "b" in
           SOME ("head'", list_cons "head" "tail'")
         | NONE => NONE
         end
     | NONE => NONE
     end).

Definition list_sub : val :=
  rec: "sub" "i" "l" :=
    if: "i" = #0 then NONEV
    else
      match: "l" with
        SOME "a" => list_cons (Fst "a") ("sub" ("i" - #1) (Snd "a"))
      | NONE => NONEV
      end.

Definition list_rev_aux : val :=
  rec: "rev_aux" "l" "acc" :=
    match: "l" with
      NONE => "acc"
    | SOME "p" =>
      let: "h" := Fst "p" in
      let: "t" := Snd "p" in
      let: "acc'" := list_cons "h" "acc" in
      "rev_aux" "t" "acc'"
    end.

Definition list_rev : val :=
  λ: "l", list_rev_aux "l" NONE.

Definition list_append : val :=
  rec: "append" "l" "r" :=
    match: "l" with
      NONE => "r"
    | SOME "p" =>
      let: "h" := Fst "p" in
      let: "t" := Snd "p" in
      list_cons "h" ("append" "t" "r")
    end.

Definition list_is_empty : val :=
  λ: "l", match: "l" with
            NONE => #true
          | SOME "x" => #false
          end.

Definition list_forall : val :=
  rec: "forall" "test" "l" :=
    match: "l" with
      NONE => #true
    | SOME "p" =>
      let: "h" := Fst "p" in
      let: "t" := Snd "p" in
      "test" "h" && "forall" "test" "t"
    end.

Section list_specs.
  Context `{dG : anerisG Mdl Σ}.

  Fixpoint is_list l v :=
    match l with
    | [] => v = NONEV
    | a::l' => ∃ lv : val, v = SOMEV (a,lv) ∧ is_list l' lv
  end.

  Lemma wp_list_nil ip :
    {{{ True }}}
      list_nil @[ip]
    {{{ v, RET v; ⌜is_list [] v⌝}}}.
  Proof. iIntros (Φ) "_ HΦ". wp_pures. by iApply "HΦ". Qed.

  Lemma wp_list_cons l lv ip a :
    {{{ ⌜is_list l lv⌝ }}}
      list_cons (Val a) (Val lv) @[ip]
    {{{ v, RET v; ⌜is_list (a::l) v⌝}}}.
  Proof.
    iIntros (Φ) "% HΦ". wp_lam. wp_pures.
    iApply "HΦ". iPureIntro; by eexists.
  Qed.

  Lemma wp_list_singleton ip a :
    {{{ True }}}
      list_cons (Val a) list_nilV @[ip]
    {{{ v, RET v; ⌜is_list [a] v⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_list_cons []); [done|].
    iIntros (v' Hv').
    by iApply "HΦ".
  Qed.

  Lemma wp_list_head ip lv l :
    {{{ ⌜is_list l lv⌝ }}}
      list_head (Val lv) @[ip]
    {{{ v, RET v;
        ⌜(l = [] ∧ v = NONEV) ∨ (∃ v' l', l = v' :: l' ∧ v = SOMEV v')⌝ }}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_lam. destruct l; simpl in *; subst.
    - wp_pures. iApply "HΦ". iPureIntro. by left.
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      wp_pures. iApply "HΦ". iPureIntro. right. by exists v,l.
  Qed.

  Lemma wp_list_tail ip lv l :
    {{{ ⌜is_list l lv⌝ }}}
      list_tail (Val lv) @[ip]
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
      list_length (Val lv) @[ip]
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

  Lemma wp_list_iter_invariant' {A} Φ1 Φ2 (Ψ: list A -> iProp Σ) P ip (l : list A) lv handler
        (toval : A -> val) lrest:
    (∀ (a : A) l',
        {{{ ⌜exists b, lrest++l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}}
          (Val handler) (toval a) @[ip]
        {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}}) -∗
    {{{ ⌜is_list (map toval l) lv⌝ ∗ P ∗ Ψ lrest ∗ [∗ list] a∈l, Φ1 a}}}
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

  Lemma wp_list_iter_invariant {A} Φ1 Φ2 (Ψ: list A -> iProp Σ) P ip (l : list A) lv handler
        (toval : A -> val):
    (∀ (a : A) l',
        {{{ ⌜exists b, l = l' ++ a :: b⌝ ∗ P ∗ Ψ l' ∗ Φ1 a }}}
          (Val handler) (toval a) @[ip]
        {{{v, RET v; P ∗ Ψ (l' ++ [a]) ∗ Φ2 a }}}) -∗
    {{{ ⌜is_list (map toval l) lv⌝ ∗ P ∗ Ψ [] ∗ [∗ list] a∈l, Φ1 a}}}
      list_iter (Val handler) lv @[ip]
    {{{ RET #(); P ∗ Ψ l ∗ [∗ list] a∈l, Φ2 a}}}.
  Proof.
    replace l with ([]++l); last by apply app_nil_l.
    iApply wp_list_iter_invariant'.
  Qed.

  Lemma wp_list_iter {A} Φ Ψ P ip (l : list A) lv handler
        (toval : A -> val) :
    (∀ (a : A),
        {{{ ⌜a ∈ l⌝ ∗ P ∗ Φ a }}}
          (Val handler) (toval a) @[ip]
        {{{v, RET v; P ∗ Ψ a }}}) -∗
    {{{ ⌜is_list (map toval l) lv⌝ ∗ P ∗ [∗ list] a∈l, Φ a }}}
      list_iter (Val handler) lv @[ip]
    {{{ RET #(); P ∗ [∗ list] a ∈ l, Ψ a }}}.
  Proof.
    rewrite /list_iter.
    iInduction l as [|a l'] "IH" forall (lv);
    iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl) HΦ";
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
    - iApply "HΦ"; eauto.
    - assert (Helemof: a ∈ a :: l').
      { constructor. }
      destruct Ha as [lv' [Hlv Hlcoh]]; subst.
      wp_pures.
      iDestruct (big_sepL_cons with "Hl") as "[Ha Hl']".
      wp_apply ("Helem" with "[HP Ha]"); iFrame; eauto.
      iIntros (v) "[HP Ha]". simpl. wp_seq.
      iApply ("IH" with "[] [$HP $Hl']"); eauto.
      { iIntros (a' HΦ'') "!# (% & HP & Ha) HΦ''".
        wp_apply ("Helem" with "[HP Ha]"); iFrame.
        iPureIntro. by constructor. }
    iNext. iIntros "(HP & Hl)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_list_fold {A} P Φ Ψ ip handler (l : list A) acc lv
        (toval : A -> val) :
    (∀ (a : A) acc lacc lrem,
        {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
          (Val handler) (Val acc) (toval a) @[ip]
        {{{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
    {{{ ⌜is_list (map toval l) lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
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

  Lemma wp_list_fold_generalized' {A} ip handler (l lp : list A) acc lv P Φ Ψ
        (toval : A -> val) :
    □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
      (∀ (a : A) acc lacc lrem,
          {{{ ⌜lp ++ l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
            (Val handler) (Val acc) (toval a) @[ip]
          {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
    {{{ ⌜is_list (map toval l) lv⌝ ∗ P lp acc None l ∗ [∗ list] a∈l, Φ a }}}
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

  Lemma wp_list_fold' {A} ip handler (l : list A) acc lv P Φ Ψ
        (toval : A -> val) :
    □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
      (∀ (a : A) acc lacc lrem,
          {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
            (Val handler) (Val acc) (toval a) @[ip]
          {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
    {{{ ⌜is_list (map toval l) lv⌝ ∗ P [] acc None l ∗ [∗ list] a∈l, Φ a }}}
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
              ⌜∃ r, v = SOMEV r ∧ nth_error l i = Some r⌝ }}}.
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
    {{{ v, RET v; ⌜∃ r, v = SOMEV r ∧ nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Φ (Hcoh & Hi)) "HΦ".
    iApply (wp_list_nth $! Hcoh).
    iIntros (v [H | H]); first eauto with lia.
    by iApply "HΦ".
  Qed.

  Lemma wp_list_mem `{!EqDecision A} ip (l : list A) lv (av : val) a
        (toval : A → val) `{!Inj (=) (=) toval}:
    av = toval a →
    {{{ ⌜is_list (map toval l) lv⌝ }}}
      list_mem av lv @[ip]
    {{{ (b : bool), RET #b; if b then ⌜a ∈ l⌝ else ⌜a ∉ l ∨ l = nil⌝ }}}.
  Proof.
    iIntros (Htval Φ).
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
      apply inj_neq in Heq; [|apply _].
      destruct Ha; set_solver.
  Qed.

  Lemma wp_find_remove {A} ip (l : list A) lv (Ψ : A → iProp Σ)
        (fv : val) (toval : A → val) :
    (∀ (a : A) av,
        {{{ ⌜av = toval a⌝ }}}
          fv av @[ip]
        {{{ (b : bool), RET #b; if b then Ψ a else True }}}) -∗
    {{{ ⌜is_list (map toval l) lv⌝ }}}
      list_find_remove fv lv @[ip]
    {{{ v, RET v; ⌜v = NONEV⌝ ∨
                       ∃ e lv' l1 l2,
                         ⌜l = l1 ++ e :: l2 ∧
                         v = SOMEV (toval e, lv') ∧
                         is_list (map toval (l1 ++ l2)) lv'⌝
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
    wp_bind (list_cons _ _). iApply wp_list_cons; first done.
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
      wp_apply wp_list_cons; first done.
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
      wp_bind (((rec: "append" _ _:= _)%V _ _)).
      iApply "IH"; [done..|].
      iIntros "!>" (v Hv).
      by wp_apply wp_list_cons.
  Qed.

  Lemma wp_list_forall {A} Φ Ψ ip (l : list A) lv (fv : val) (toval : A → val) :
    (∀ (a : A) av,
        {{{ ⌜av = toval a⌝ }}}
          fv av @[ip]
        {{{ (b : bool), RET #b; if b then Φ a else Ψ a }}}) -∗
    {{{ ⌜is_list (map toval l) lv⌝ }}}
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

End list_specs.

Notation "[ ]" := (list_nil) (format "[ ]") : expr_scope.
Notation "[ ]" := (list_nilV) (format "[ ]") : val_scope.
Notation "[ x ]" := (list_cons x (list_nilV)) (format "[ x ]") : expr_scope.
Infix "::" := list_cons (at level 60, right associativity) : expr_scope.
Notation "[ x ; y ; .. ; z ]" := (list_cons x (list_cons y .. (list_cons z list_nil) ..)) : expr_scope.
