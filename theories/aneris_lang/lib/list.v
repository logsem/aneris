From iris Require Import invariants.
From iris.algebra Require Import gmap frac agree frac_auth.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export own saved_prop.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics coq_tactics.
From aneris.aneris_lang Require Import lang proofmode notation.
From stdpp Require Import base.

Set Default Proof Using "Type".

Import Network.
Import String.
Import uPred.

Section list_code.

  Definition list_make : base_lang.val :=
    λ: <>, NONE.

  Definition list_cons : base_lang.val :=
    λ: "elem" "list", SOME (Pair "elem" "list").

  Definition list_head : base_lang.val :=
    λ: "l", match: "l" with
              SOME "a" => SOME (Fst "a")
            | NONE => NONE
            end.

  Definition list_tail : base_lang.val :=
    λ: "l", match: "l" with
              SOME "a" => (Snd "a")
            | NONE => NONE
            end.

  Definition list_fold : base_lang.val :=
    rec: "fold" "handler" "acc" "l" :=
      match: "l" with
        SOME "a" => let: "fst" := Fst "a" in
                   let: "snd" := Snd "a" in
                   let: "acc'" := ("handler" "acc" "fst") in
                   "fold" "handler" "acc'" "snd"
      | NONE => "acc"
      end.

  Definition list_iter : base_lang.val :=
    rec: "iter" "handler" "l" :=
      match: "l" with
        SOME "a" =>
        let: "tail" := Snd "a" in
        "handler" (Fst "a");;
                  "iter" "handler" "tail"
      | NONE => #()
      end.

  Definition list_length : base_lang.val :=
    rec: "length" "l" :=
      match: "l" with
        SOME "a" => #1 + "length" (Snd "a")
      | NONE => #0
      end.

  Definition list_nth : base_lang.val :=
    (rec: "nth" "l" "i" :=
      match: "l" with
        SOME "a" =>
        if: "i" = #0 then SOME (Fst "a")
        else "nth" (Snd "a") ("i" - #1)
      | NONE => NONE
      end)%V.

  Definition list_find_remove : base_lang.val :=
    (rec: "find" "f" "l" :=
       match: "l" with
         SOME "a" =>
           let: "head" := Fst "a" in
           let: "tail" := Snd "a" in
           if: "f" "head" then SOME ("head", "tail")
           else
             let: "r" := "find" "f" "tail" in
             match: "r" with
               SOME "b" =>
                 let: "head'" := Fst "b" in
                 let: "tail'" := Snd "b" in
                 SOME ("head'", list_cons "head" "tail'")
             | NONE => NONE
             end
       | NONE => NONE
       end).

  Definition list_sub : base_lang.val :=
    rec: "sub" "i" "l" :=
      if: "i" = #0 then NONEV
      else
        match: "l" with
          SOME "a" => list_cons (Fst "a") ("sub" ("i" - #1) (Snd "a"))
        | NONE => NONEV
        end.

  Definition list_rev_aux : base_lang.val :=
  rec: "rev_aux" "l" "acc" :=
    match: "l" with
      NONE => "acc"
    | SOME "p" =>
       let: "h" := Fst "p" in
       let: "t" := Snd "p" in
       let: "acc'" := list_cons "h" "acc" in
       "rev_aux" "t" "acc'"
    end.

  Definition list_rev : base_lang.val :=
    λ: "l", list_rev_aux "l" NONE.

  Definition list_append : base_lang.val :=
    (rec: "append" "l" "r" :=
      match: "l" with
      NONE => "r"
    | SOME "p" =>
       let: "h" := Fst "p" in
       let: "t" := Snd "p" in
       list_cons "h" ("append" "t" "r")
    end)%V.

  Definition list_is_empty : base_lang.val :=
    λ: "l", match: "l" with
              NONE => #true
            | SOME "x" => #false
            end.

  Fixpoint list_coh l v :=
    match l with
    | [] => v = NONEV
    | a::l' => ∃ lv : base_lang.val, v = SOMEV (a,lv) ∧ list_coh l' lv
  end.

End list_code.

(* ---------------------------------------------------------------------- *)

Section list_spec.
  Context `{dG : anerisG Σ}.


  Lemma list_make_spec ip :
    {{{ True }}}
      list_make #() @[ip]
    {{{ v, RET v; ⌜list_coh [] v⌝}}}.
  Proof.
    iIntros (Φ) "H HΦ". rewrite /list_make /=.
    wp_pures. by iApply "HΦ".
  Qed.

  Lemma list_cons_spec ip a lv l :
    {{{ ⌜list_coh l lv⌝ }}}
      list_cons (Val a) (Val lv) @[ip]
    {{{ v, RET v; ⌜list_coh (a::l) v⌝}}}.
  Proof.
    iIntros (Φ) "% HΦ".
    wp_lam. wp_pures. iApply "HΦ".
    iPureIntro. by exists lv.
  Qed.

  Lemma list_head_spec ip lv l :
    {{{ ⌜list_coh l lv⌝ }}}
      list_head (Val lv) @[ip]
    {{{ v, RET v; ⌜(l = [] ∧ v = NONEV) ∨
                          (∃ v' l', l = v' :: l' ∧ v = SOMEV v')⌝}}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_lam. destruct l; simpl in *; subst.
    - wp_pures. iApply "HΦ". iPureIntro. by left.
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      wp_pures. iApply "HΦ". iPureIntro. right. by exists v,l.
  Qed.

  Lemma list_tail_spec ip lv l :
    {{{ ⌜list_coh l lv⌝ }}}
      list_tail (Val lv) @[ip]
    {{{ v, RET v; ⌜list_coh (tail l) v⌝}}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_lam. destruct l; simpl in *; subst.
    - wp_match. wp_inj. by iApply "HΦ".
    - destruct a as [lv' [Hhead Htail]] eqn:Heq; subst.
      wp_match. wp_proj. by iApply "HΦ".
  Qed.

Lemma list_length_spec ip l lv :
  {{{ ⌜list_coh l lv⌝ }}}
    list_length (Val lv) @[ip]
  {{{ v, RET #v; ⌜v = List.length l⌝ }}}.
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

Lemma list_iter_spec {A} ip (l : list A) lv handler P Φ Ψ
      (toval : A -> base_lang.val) :
  (∀ (a : A),
  {{{ ⌜a ∈ l⌝ ∗ P ∗ Φ a }}}
     (Val handler) (toval a) @[ip]
  {{{v, RET v; P ∗ Ψ a }}}) -∗
  {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ ∗ P ∗ [∗ list] a∈l, Φ a }}}
    list_iter (Val handler) lv @[ip]
  {{{ RET #(); P ∗ [∗ list] a∈l, Ψ a }}}.
Proof.
  rewrite /list_iter.
  iInduction l as [|a l'] "IH" forall (lv);
  iIntros "#Helem"; iIntros (Φ') "!# (Ha & HP & Hl) HΦ";
  iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_pures.
  - iApply "HΦ"; eauto.
  - assert (Helemof: a ∈ a :: l').
    { apply elem_of_list_here. }
    destruct Ha as [lv' [Hlv Hlcoh]]; subst.
    wp_pures.
    iDestruct (big_sepL_cons with "Hl") as "[Ha Hl']".
    wp_apply ("Helem" with "[HP Ha]"); iFrame; eauto.
    iIntros (v) "[HP Ha]". simpl. wp_seq.
    iApply ("IH" with "[] [$HP $Hl']"); eauto.
    { iIntros (a' HΦ'') "!# (% & HP & Ha) HΦ''".
      wp_apply ("Helem" with "[HP Ha]"); iFrame.
      iPureIntro. by apply elem_of_list_further.
    }
    iNext. iIntros "(HP & Hl)". iApply "HΦ". iFrame.
Qed.

Lemma list_fold_spec {A} ip handler (l : list A)  acc lv P Φ Ψ
      (toval : A -> base_lang.val) :
  (∀ (a : A) acc lacc lrem,
  {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc ∗ Φ a }}}
     (Val handler) (Val acc) (toval a) @[ip]
  {{{v, RET v; P (lacc ++ [a]) v ∗ Ψ a }}}) -∗
  {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ ∗ P [] acc ∗ [∗ list] a∈l, Φ a }}}
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

Lemma list_fold_spec'_generalized {A} ip handler (l lp : list A) acc lv P Φ Ψ
      (toval : A -> base_lang.val) :
  □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
  (∀ (a : A) acc lacc lrem,
  {{{ ⌜lp ++ l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
     (Val handler) (Val acc) (toval a) @[ip]
  {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
  {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ ∗ P lp acc None l ∗ [∗ list] a∈l, Φ a }}}
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

Lemma list_fold_spec' {A} ip handler (l : list A) acc lv P Φ Ψ
      (toval : A -> base_lang.val) :
  □ (∀ (a : A) acc lacc lrem, (P lacc acc None (a::lrem) -∗ P lacc acc (Some a) lrem))%I -∗
  (∀ (a : A) acc lacc lrem,
  {{{ ⌜l = lacc ++ a :: lrem⌝ ∗ P lacc acc (Some a) lrem ∗ Φ a }}}
     (Val handler) (Val acc) (toval a) @[ip]
  {{{v, RET v; P (lacc ++ [a]) v None lrem ∗ Ψ a }}}) -∗
  {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ ∗ P [] acc None l ∗ [∗ list] a∈l, Φ a }}}
    list_fold (Val handler) (Val acc) lv @[ip]
  {{{v, RET v; P l v None [] ∗ [∗ list] a∈l, Ψ a }}}.
Proof.
  iIntros "#Hvs #Hcl".
  iApply (list_fold_spec'_generalized _ handler l [] with "[-]"); eauto.
Qed.

 Lemma list_sub_spec ip k l lv  :
     {{{ ⌜list_coh l lv⌝ }}}
       list_sub #k lv @[ip]
     {{{ v, RET v; ⌜list_coh (take k l) v ⌝}}}.
 Proof.
   iIntros (Φ) "Hcoh HΦ".
   iInduction l as [|a l'] "IH" forall (k lv Φ);
   iDestruct "Hcoh" as %Hcoh; simpl in Hcoh; subst; wp_rec;
   wp_pures; case_bool_decide; wp_if; wp_pures.
   - iApply "HΦ"; by rewrite take_nil.
   - iApply "HΦ"; by rewrite take_nil.
   - iApply "HΦ". assert (k = O) as H1 by lia. by rewrite H1 firstn_O.
   -  destruct Hcoh as [lv' [Hlv Hlcoh]]; subst.
      wp_match. wp_proj. wp_bind (list_sub _ _). wp_op.
      destruct k as [|k]; first done.
      assert (((Z.of_nat (S k)) - 1)%Z = Z.of_nat k) as -> by lia.
      iApply ("IH" $! k _ _ Hlcoh). iIntros (tl Hcoh_tl).
      iNext. wp_pures. rewrite firstn_cons.
      by wp_apply (list_cons_spec).
 Qed.

 Lemma list_nth_spec ip (i: nat) l lv  :
  {{{ ⌜list_coh l lv⌝ }}}
    list_nth (Val lv) #i @[ip]
  {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜List.length l <= i⌝) ∨
                     ⌜∃ r, v = SOMEV r ∧ List.nth_error l i = Some r⌝ }}}.
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

  Lemma list_nth_spec_some ip (i: nat) l lv  :
  {{{  ⌜list_coh l lv ∧ i < List.length l⌝  }}}
    list_nth (Val lv) #i @[ip]
  {{{ v, RET v; ⌜∃ r, v = SOMEV r ∧ List.nth_error l i = Some r⌝ }}}.
  Proof.
    iIntros (Φ (Hcoh & Hi)) "HΦ".
    iApply (list_nth_spec $! Hcoh).
    iIntros (v [H | H]); first eauto with lia.
    by iApply "HΦ".
  Qed.

  Lemma list_find_remove_spec {A} ip (l : list A) lv (Ψ : A → iProp Σ)
        (fv : base_lang.val) (toval : A → base_lang.val) :
    (∀ (a : A) av,
      {{{ ⌜av = toval a⌝ }}}
        fv av @[ip]
      {{{ (b : bool), RET #b; if b then Ψ a else True }}}) -∗
    {{{ ⌜list_coh (map (λ a, toval a) l) lv⌝ }}}
      list_find_remove fv lv @[ip]
    {{{ v, RET v; ⌜v = NONEV⌝ ∨
                       ∃ e lv' l1 l2,
                         ⌜l = l1 ++ e :: l2 ∧
                         v = SOMEV (toval e, lv') ∧
                         list_coh (map (λ a, toval a) (l1 ++ l2)) lv'⌝
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
    wp_bind (list_cons _ _). iApply list_cons_spec; first done.
    iIntros "!>" (v Hcoh) "/=". wp_pures.
    iApply "HΦ". iRight.
    iExists _, _, (_ :: _), _; eauto.
  Qed.

 Lemma list_rev_aux_spec ip l lM r rM:
  {{{ ⌜list_coh lM l ∧ list_coh rM r⌝ }}}
    list_rev_aux (Val l) (Val r) @[ip]
  {{{ v, RET v; ⌜list_coh (rev_append lM rM) v⌝ }}}.
 Proof.
   iIntros (? [Hl Hr]) "H".
   iInduction lM as [|a lM] "IH" forall (l r rM Hl Hr).
   - simpl in *; subst.
     rewrite /list_rev_aux.
     wp_pures.
     by iApply "H".
   - destruct Hl as [l' [Hl'eq Hl']]; subst.
     wp_rec; wp_pures.
     wp_apply list_cons_spec; first done.
     iIntros (w Hw).
     wp_pures.
     by iApply "IH".
 Qed.

 Lemma list_rev_spec ip l lM :
  {{{ ⌜list_coh lM l⌝ }}}
    list_rev (Val l) @[ip]
  {{{ v, RET v; ⌜list_coh (reverse lM) v⌝ }}}.
 Proof.
   iIntros (??) "H". rewrite /list_rev. wp_pures.
     by iApply (list_rev_aux_spec _ _ _ NONEV []).
 Qed.

 Lemma list_is_empty_spec ip l v :
  {{{ ⌜list_coh l v⌝ }}}
    list_is_empty v @[ip]
  {{{ v, RET #v;
        ⌜v = match l with [] => true | _ => false end⌝ }}}.
 Proof.
   iIntros (Φ Hl) "HΦ". wp_rec. destruct l.
   - rewrite Hl. wp_pures. by iApply "HΦ".
   - destruct Hl as [? [-> _]]. wp_pures. by iApply "HΦ".
 Qed.

 Lemma nth_error_lookup {A} (l : list A) (i : nat) x :
    nth_error l i  = Some x → l !! i = Some x.
 Proof.
   revert i. induction l as [|?? IHl]; destruct i; auto.
   by apply IHl.
 Qed.

 Lemma take_S_r_nth `{A : Type}:
   ∀  (l : list A) (n : nat) (x : A),
     nth_error l n = Some x →  take (n + 1) l = take n l ++ [x].
 Proof. induction l; intros []; naive_solver eauto with f_equal. Qed.

 Lemma map_nth_error_inv { A B}: forall n (l: list A) d (f: A → B),
     (∀ x y, f x = f y → x = y) →
     nth_error (map f l) n = Some (f d) → nth_error l n = Some d.
 Proof.
   induction n; intros [|] ??? H; simpl in *; inversion H; eauto using f_equal.
 Qed.

 Lemma map_lookup_Some {A B} (f : A → B) (l : list A) (i : nat) (k : B) :
   map f l !! i = Some k →
   ∃ a, k = f a ∧ l !! i = Some a.
 Proof.
   revert i. induction l; [done|].
   intros [] Hmap.
   - eexists. by inversion Hmap.
   - by apply IHl in Hmap.
 Qed.

 Lemma list_coh_eq lM :
   ∀ l1 l2, list_coh lM l1 → list_coh lM l2 → l1 = l2.
 Proof. induction lM; intros []; naive_solver eauto with f_equal. Qed.

 Lemma list_coh_inv_l l:
   ∀ lM1 lM2, list_coh lM1 l → lM1 = lM2 → list_coh lM2 l.
 Proof. by intros ? ? ? <-. Qed.

 Lemma list_coh_app lM x : ∃ lv, list_coh (lM ++ [x]) lv.
 Proof.  induction lM; naive_solver eauto. Qed.

 Definition list_str_val (l : list string) : list base_lang.val :=
   map (λ (str : string), #str) l.

End list_spec.

Section list_string_spec.

  Fixpoint list_str_coh (l: list string) v :=
    match l with
    | [] => v = NONEV
    | a::l' => ∃ lv : base_lang.val, v = SOMEV (#a,lv) ∧ list_str_coh l' lv
  end.

  Lemma list_str_coh_spec (l: list string) (v: base_lang.val) :
    list_str_coh l v → list_coh (map (λ (s: string), #s) l) v.
  Proof.
    revert v; induction l as [|]; intros []; try naive_solver eauto with f_equal.
  Qed.

  Lemma list_str_coh_spec_inv (l: list string) (v: base_lang.val) :
    list_coh (map (λ (s: string), #s) l) v → list_str_coh l v.
  Proof.
    revert v; induction l as [|]; intros []; try naive_solver eauto with f_equal.
  Qed.

End list_string_spec.
