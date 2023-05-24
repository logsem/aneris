From aneris.aneris_lang Require Import lang proofmode.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.aneris_lang.lib Require Export queue_code.

Section queue_specs.

  Context `{!anerisG Mdl Σ}.
  Context `{!Inject A val}.

  Definition is_queue (l : list A) (q : val) : Prop :=
    ∃ f b lf lb,
      q = (PairV f b) /\
      is_list lf f /\
      is_list lb b /\
      l = lf ++ (reverse lb).

  Lemma wp_queue_empty ip :
    {{{ True }}}
      queue_empty #() @[ip]
    {{{ v, RET v; ⌜is_queue [] v⌝ }}}.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /queue_empty.
    wp_pures.
    iApply "HΦ"; iPureIntro.
    eexists _, _, [], [].
    repeat split; eauto.
  Qed.

  Lemma wp_queue_is_empty ip q qv :
    {{{ ⌜is_queue q qv⌝ }}}
      queue_is_empty qv @[ip]
    {{{ (b:bool), RET #b; ⌜if b then q = [] else q ≠ []⌝ }}}.
  Proof.
    iIntros (Φ Hq) "HΦ".
    destruct Hq as (f & b & lf & lb & -> & Hil1 & Hil2 & ->).
    wp_lam. wp_pures.
    destruct lf, lb; simpl in *.
    { rewrite Hil1 Hil2. wp_pures. by iApply "HΦ". }
    { rewrite Hil1. destruct Hil2 as (lv & -> & Hil2). wp_pures. iApply "HΦ".
      iPureIntro. intros Heq. rewrite reverse_cons in Heq.
      apply app_eq_nil in Heq. destruct Heq as [_ Heq]. done. }
    { destruct Hil1 as (lv & -> & Hil1). rewrite Hil2. wp_pures. iApply "HΦ".
      iPureIntro. done. }
    destruct Hil1 as (lv1 & -> & Hil1).
    destruct Hil2 as (lv2 & -> & Hil2).
    wp_pures. iApply "HΦ". iPureIntro. done.
  Qed.

  Lemma wp_queue_add (q : list A) (qv : val) (e : A) ip :
    {{{ ⌜is_queue q qv⌝ }}}
      queue_add $e qv @[ip]
      {{{ rv, RET rv; ⌜is_queue (q ++ [e]) rv⌝ }}}.
  Proof.
    iIntros (Φ) "%Hiq HΦ".
    destruct Hiq as (f & b & lf & lb & -> & Hil1 & Hil2 & ->).
    rewrite /queue_add; wp_pures.
    wp_apply wp_list_cons; [by iPureIntro; eauto | ].
    iIntros (v) "%Hilv"; wp_pures.
    iApply "HΦ"; iPureIntro.
    eexists _, _, lf, (e :: lb).
    repeat split; eauto.
    assert (e :: lb = [e] ++ lb) as -> by auto.
    by rewrite reverse_app app_assoc.
  Qed.

  Lemma reverse_rev_eq (l : list A) : reverse l = rev l.
  Proof. by rewrite rev_alt. Qed.

  Ltac rewrite_reverse_to_rev :=
    match goal with
    | [ H : context[reverse _] |- _  ] => rewrite reverse_rev_eq in H
    | [ |- context[reverse _] ] => rewrite reverse_rev_eq
    end.

  Hint Extern 1 => rewrite_reverse_to_rev : core.

  Lemma wp_queue_norm_internal (q : list A) (qv : val) ip :
    {{{ ⌜is_queue q qv⌝ }}}
      queue_norm qv @[ip]
    {{{ rv, RET rv; ⌜is_queue q rv /\
                    (∃ rv1 rv2, rv = PairV rv1 rv2 /\
                                (is_list [] rv1 -> q = []))⌝ }}}.
  Proof.
    iIntros (Φ) "%Hiq HΦ".
    destruct Hiq as (f & b & lf & lb & -> & Hil1 & Hil2 & ->).
    rewrite /queue_norm; wp_pures; simpl in *.
    destruct lf as [ | fh ft]; simpl in Hil1; subst; wp_pures.
    - wp_apply wp_list_rev; [ by eauto | ].
      iIntros (v) "%Hilr"; wp_pures.
      iApply "HΦ"; simpl; iPureIntro.
      split.
      + eexists _, _, (reverse lb), [].
        repeat split; eauto; simpl.
        rewrite -app_nil_end; done.
      + eexists _, _.
        split; eauto.
        intros ->.
        destruct lb as [ | h t]; [done |].
        rewrite reverse_cons in Hilr.
        rewrite_reverse_to_rev.
        assert (H: ∃ (h' : A) (t' : list A), (rev t ++ [h]) = h' :: t').
        { pose proof (app_cons_not_nil (rev t) nil h) as Hne.
          remember (rev t ++ [h]) as lst.
          destruct lst as [ | h' t']; by eauto. }
        exfalso.
        destruct H as (h' & t' & Heq).
        rewrite Heq in Hilr.
        simpl in Hilr.
        destruct Hilr as (lv & [Heq' _]).
        inversion Heq'.
    - destruct Hil1 as (lv & -> & Hil1).
      wp_pures.
      iApply "HΦ". iPureIntro.
      simpl.
      split.
      + eexists _, _, (fh :: ft), lb.
        repeat split; auto.
        simpl; eauto.
      + eexists _, _.
        repeat split.
        intros Hcontra; inversion Hcontra.
  Qed.

  Lemma wp_queue_norm (q : list A) (qv : val) ip :
    {{{ ⌜is_queue q qv⌝ }}}
      queue_norm qv @[ip]
    {{{ rv, RET rv; ⌜is_queue q rv⌝ }}}.
  Proof.
    iIntros (Φ) "%Hiq HΦ".
    wp_apply wp_queue_norm_internal; [by eauto |].
    iIntros (rv) "[%Hiq' _]".
    iApply "HΦ"; done.
  Qed.

  Lemma wp_queue_peek_opt (l : list A) (q : val) ip :
    {{{ ⌜is_queue l q⌝ }}}
      queue_peek_opt q @[ip]
    {{{ v, RET v; ⌜(l = [] /\ v = NONEV) \/
                   (∃ a t, l = a :: t /\ v = SOMEV $a)⌝ }}}.
  Proof.
    iIntros (Φ Hiq) "HΦ".
    rewrite /queue_peek_opt; wp_pures.
    wp_apply wp_queue_norm_internal; [by eauto |].
    iIntros (rv (Hiqrv & (hv & tv & -> & Himpl))).
    wp_pures.
    destruct Hiqrv as (v1 & v2 & l1 & l2 & Heq & Hil1 & Hil2 & ->).
    simplify_eq.
    destruct l1 as [ | lh1 lt1]; simpl in *; subst.
    - wp_pures.
      iApply "HΦ"; iPureIntro.
      left. split; [|done]. apply Himpl. reflexivity.
    - destruct Hil1 as (lv & -> & Hil1).
      wp_pures.
      iApply "HΦ"; iPureIntro.
      right. eexists _, _. split. reflexivity. done.
  Qed.

  Lemma wp_queue_take_opt (l : list A) (q : val) ip :
    {{{ ⌜is_queue l q⌝ }}}
      queue_take_opt q @[ip]
    {{{ rv, RET rv; ⌜(l = [] /\ rv = NONEV) ∨
                     (∃ h t tv, l = h :: t /\
                                rv = SOMEV (PairV $h tv) /\
                                is_queue t tv)⌝ }}}.
  Proof.
    iIntros (Φ) "%Hiq HΦ".
    rewrite /queue_take_opt.
    wp_pures.
    wp_apply wp_queue_norm_internal; [done |].
    iIntros (rv (Hiq' & rv1 & rv2 & -> & Hilst)).
    wp_pures.
    destruct Hiq' as (f & b & lf & lb & Heq & Hilf & Hilb & ->).
    inversion Heq as [[Heq1 Heq2]]; subst.
    destruct lf as [ | h1 t1]; simpl in *.
    - subst; wp_pures.
      iApply "HΦ". auto.
    - destruct Hilf as (lv & -> & Hillv).
      wp_pures. iApply "HΦ"; iPureIntro.
      right.
      eexists _, _, _; repeat split; eauto.
      eexists _, _, _, _; eauto.
  Qed.

  Lemma wp_queue_filter (l : list A) (P : A -> bool) (f qv : val) ip :
    {{{ (∀ (x : A),
            {{{ True }}}
              f $x @[ip]
            {{{ w, RET w; ⌜w = $(P x)⌝ }}} ) ∗
        ⌜is_queue l qv⌝ }}}
       queue_filter f qv @[ip]
    {{{ rv, RET rv; ⌜is_queue (List.filter P l) rv⌝ }}}.
  Proof.
    iIntros (Φ) "[Hf %Hiq] HΦ".
    destruct Hiq as (f' & b & lf & lb & Heq & Hil1 & Hil2 & Hl).
    rewrite /queue_filter; subst; wp_pures.
    wp_apply wp_list_rev; [done |].
    iIntros (v) "%Hil_rev".
    wp_apply wp_list_append; [done |].
    iIntros (v') "%Hilv'".
    wp_pures.
    wp_apply (wp_list_filter (lf ++ reverse lb) with "[Hf]"); [by auto |].
    iIntros (rv) "%Hilrv"; wp_pures.
    iApply "HΦ".
    iPureIntro.
    eexists _, _, _, _; repeat split; eauto.
    { assert (is_list [] (InjLV #())) as H; done. }
    simpl.
    by rewrite app_nil_r.
  Qed.

  Lemma wp_queue_drop ip q qv n :
    {{{ ⌜is_queue q qv⌝ }}}
      queue_drop qv #n @[ip]
    {{{ rv, RET rv; ⌜is_queue (drop n q) rv⌝ }}}.
  Proof.
    iIntros (Φ Hq) "HΦ".
    rewrite /queue_drop.
    iInduction n as [|n] "IHn" forall (q qv Hq).
    { wp_pures. by iApply "HΦ". }
    wp_pures. wp_apply (wp_queue_norm_internal); [done|].
    iIntros (rv Hrv).
    destruct Hrv as [Hrv (rv1 & rv2 & -> & Hrv1)].
    destruct Hrv as (h & t & tv & tr & Heq & Hrv').
    destruct Hrv' as (Htv & Htr & ->).
    inversion Heq. subst.
    wp_pures.
    destruct tv as [|x tv]; simpl in *.
    (* Case 1: left is empty. *)
    { rewrite Htv. wp_pures. iApply "HΦ".
      rewrite Hrv1; [|done].
      assert (tr = []) as ->.
      { specialize (Hrv1 Htv). rewrite -(reverse_involutive tr).
        by rewrite Hrv1. }
      simpl. iPureIntro. eexists _, _, [], []. done. }
    (* Case 2 : left list is not empty *)
    destruct Htv as (lv & -> & Hlv).
    clear Hrv1 Heq.
    do 7 wp_pure _.
    rewrite -(Z2Nat.id 1); [|lia].
    rewrite -Nat2Z.inj_sub; [|lia].
    simpl. rewrite Nat.sub_0_r.
    iApply "IHn".
    { iPureIntro. eexists _, _, _, _. done. }
    iApply "HΦ".
  Qed.

  Lemma wp_queue_iter_idx Φ Ψ P ip q qv handler :
    (∀ i (a : A),
        {{{ P ∗ Φ i a }}}
          (Val handler) (Val $ a) @[ip]
        {{{v, RET v; P ∗ Ψ i a }}}) -∗
    {{{ ⌜is_queue q qv⌝ ∗ P ∗ [∗ list] i↦a ∈ q, Φ i a }}}
      queue_iter (Val handler) qv @[ip]
    {{{ RET #(); P ∗ [∗ list] i↦a ∈ q, Ψ i a }}}.
  Proof.
    iIntros "#Hq" (Φ') "!> (%Hq & HP & Hqs) HΦ" .
    destruct Hq as (f & b & lf & lb & [Heq (Hlf & Hlb & Hq')]).
    simplify_eq.
    wp_lam. wp_pures.
    iDestruct (big_sepL_app with "Hqs") as "[Hlf Hlb]".
    wp_apply (wp_list_iter_idx with "Hq [$HP $Hlf]"); [done|].
    iIntros "[HP Hlf]". wp_pures.
    wp_apply (wp_list_rev); [done|].
    iIntros (rb Hrlb).
    wp_apply (wp_list_iter_idx_aux with "Hq [$HP $Hlb]"); [done|].
    iIntros "[HP Hlb]". wp_pures.
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_queue_iter Φ Ψ P ip q qv handler :
    (∀ (a : A),
        {{{ P ∗ Φ a }}}
          (Val handler) (Val $ a) @[ip]
        {{{v, RET v; P ∗ Ψ a }}}) -∗
    {{{ ⌜is_queue q qv⌝ ∗ P ∗ [∗ list] a ∈ q, Φ a }}}
      queue_iter (Val handler) qv @[ip]
    {{{ RET #(); P ∗ [∗ list] a ∈ q, Ψ a }}}.
  Proof.
    iIntros "#Hq" (Φ') "!> (%Hq & HP & Hqs) HΦ".
    iApply (wp_queue_iter_idx with "[Hq] [HP $Hqs] HΦ").
    { iIntros (i a). iApply "Hq". }
    by iFrame.
  Qed.

  Lemma wp_queue_iteri Φ Ψ P ip q qv (fv : val) :
    is_queue q qv →
    (∀ (i : nat) (a : A),
        {{{ P ∗ Φ i a }}} fv #i (Val $ a) @[ip] {{{ v, RET v; P ∗ Ψ i a }}}) -∗
    {{{ P ∗ [∗ list] i↦a ∈ q, Φ i a }}}
      queue_iteri fv qv @[ip]
    {{{ RET #(); P ∗ [∗ list] i↦a ∈ q, Ψ i a }}}.
  Proof.
    iIntros (Hq) "#Hq".
    iIntros (Φ') "!> (HP & Hqs) HΦ".
    wp_lam. destruct Hq as (f & b & lf & lb & [-> (Hlf & Hlb & ->)]).
    wp_pures.
    rewrite big_sepL_app. iDestruct "Hqs" as "[Hqs1 Hqs2]".
    wp_smart_apply (wp_list_iteri with "Hq [$HP $Hqs1]"); [done|].
    iIntros "[HP Hqs1]".
    wp_smart_apply (wp_list_rev with "[//]"). iIntros (v Hrev).
    wp_smart_apply (wp_list_length); [done|]. iIntros (n ->).
    iApply (wp_list_iteri_loop with "Hq [$HP $Hqs2]"); [done|].
    iIntros "!> [HP Hqs]".
    iApply "HΦ". by iFrame.
  Qed.

End queue_specs.

Global Arguments is_queue {A} {_} _ _.
