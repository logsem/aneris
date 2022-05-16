From aneris.prelude Require Import misc.
From aneris.aneris_lang Require Import lang proofmode.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang.lib Require Export list_proof queue_proof.

Set Default Proof Using "Type".

Section list_proof_alt.
  Context `{dG : anerisG Mdl Σ}.

  Fixpoint is_listP {A} (l : list A) (lv : val) (P : A -> val -> Prop) :=
    match l with
    | [] => lv = NONEV
    | h :: l' => ∃ hv lv',
        lv = SOMEV (hv, lv') ∧ (P h hv) ∧ is_listP l' lv' P
  end.

  Lemma wp_list_nilP {A} (P : A -> val -> Prop) ip :
    {{{ True }}}
      [] @[ip]
    {{{ v, RET v; ⌜is_listP [] v P⌝}}}.
  Proof. iIntros (Φ) "_ HΦ". wp_pures. by iApply "HΦ". Qed.

  Lemma wp_list_consP A h (l : list A) hv lv P ip :
    {{{ ⌜is_listP l lv P⌝ ∗ ⌜P h hv⌝ }}}
      hv :: lv @[ip]
    {{{ v, RET v; ⌜is_listP (h :: l) v P⌝ }}}.
  Proof.
    iIntros (Φ) "[% %] HΦ". wp_lam. wp_pures.
    iApply "HΦ". iPureIntro.
    rewrite /is_listP. eauto.
  Qed.

  Lemma wp_list_tailP {A} ip lv (l : list A) P :
    {{{ ⌜is_listP l lv P⌝ }}}
      list_tail lv @[ip]
    {{{ v, RET v; ⌜is_listP (tail l) v P⌝}}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_lam. destruct l; simpl in *; subst.
    - wp_match. wp_inj. by iApply "HΦ".
    - destruct a as [lv' [Hhead [-> [HP Htail]]]] eqn:Heq; subst.
      wp_match. wp_proj. by iApply "HΦ".
  Qed.

  Lemma wp_list_nthP A ip (i: nat) (l : list A) lv P  :
   {{{ ⌜is_listP l lv P⌝ }}}
      list_nth (Val lv) #i @[ip]
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ ⌜length l <= i⌝) ∨
              ⌜∃ wv w, v = SOMEV wv ∧ P w wv ∧ nth_error l i = Some w⌝ }}}.
  Proof.
    iIntros (Φ) "Ha HΦ".
    iInduction l as [|a l'] "IH" forall (i lv Φ);
    iDestruct "Ha" as %Ha; simpl in Ha; subst; wp_rec; wp_let.
    - wp_match. wp_pures.
      iApply ("HΦ" $! (InjLV #())). iLeft. simpl. eauto with lia.
    - destruct Ha as [lv' [Hlv [-> [HP Hlcoh]]]].
      wp_match. wp_pures. case_bool_decide; wp_pures.
      + iApply "HΦ". iRight. simpl. iExists _, a. by destruct i.
      + destruct i; first done.
        assert ((S i - 1)%Z = i) as -> by lia.
        iApply ("IH" $! i Hlv _  Hlcoh).
        iNext. iIntros (v [ (Hv & Hs) | Hps]); simpl.
        * iApply "HΦ"; try eauto with lia.
        * iApply "HΦ"; try eauto with lia.
  Qed.

  Lemma wp_list_makeP {A} ip len (init : A) (initV : val) P :
    {{{ ⌜P init initV⌝ }}}
      list_make #len initV @[ip]
    {{{ v, RET v; ⌜is_listP (replicate len init) v P⌝ }}}.
  Proof.
    revert len. iLöb as "IH". iIntros (len Φ) "%HP HΦ".
    wp_rec. wp_pures. case_bool_decide; wp_if.
    - iApply (wp_list_nilP _); [done|].
      iNext; iIntros (v) "%".
      iApply "HΦ".
      assert (len = 0%nat) by lia; simplify_eq. done.
    - wp_pures. wp_bind ((list_make _ _)).
      assert (((Z.of_nat len) - 1)%Z = Z.of_nat (len - 1)) as -> by lia.
      iApply "IH"; first done.
      iNext. iIntros (? Hcoh) "/=".
      wp_apply (wp_list_consP); [eauto |].
      iIntros (w) "%".
      iApply "HΦ". iPureIntro.
      assert (∃ n, len = S n) as [m Hlen'].
      { exists (len - 1)%nat; lia. }
      rewrite Hlen' replicate_S.
      by assert (m = (len - 1)%nat) as -> by lia.
  Qed.

  Lemma wp_list_mapi_loopP {A B}
        (f : nat -> A -> B) (k : nat) (l : list A) (fv lv : val)
        (P : A -> val -> Prop) (Q : B -> val -> Prop)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) ip :
    {{{ □ (∀ (i : nat) (x : A) (xv : val),
              {{{ γ (k + i)%nat x ∗ ⌜P x xv⌝ }}}
                fv $(k + i)%nat xv @[ip]
              {{{ rv, RET rv;
                    let r := f (k + i)%nat x in
                    ⌜Q r rv⌝ ∗ ψ (k + i)%nat r }}}) ∗
        ⌜is_listP l lv P⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ (k + i)%nat a)
    }}}
      list_mapi_loop fv #k lv @[ip]
    {{{ rv, RET rv;
        let l' := mapi_loop f k l in
        ⌜is_listP l' rv Q⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ (k + i)%nat a)}}}.
  Proof.
    iInduction l as [ | h l'] "IH" forall (lv k);
      iIntros (Φ) "[#Hf [%Hil Hown]] HΦ"; simpl in Hil;
      rewrite /list_mapi_loop.
    - subst.
      wp_pures.
      iApply "HΦ".
      iSplitL ""; done.
    - destruct Hil as [hv [lv' [-> [HP Hil']]]].
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
        wp_apply ("Hf" with "[Hhead]"); [by iFrame |].
        iIntros (fr) "[%HQ HΨ]".
        wp_apply wp_list_consP; [ done | ].
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

  Lemma wp_list_mapiP {A B}
        (f : nat -> A -> B) (l : list A) (fv lv : val)
        (P : A -> val -> Prop) (Q : B -> val -> Prop)
        (γ : nat -> A -> iProp Σ) (ψ : nat -> B -> iProp Σ) ip :
    {{{ □ (∀ (i : nat) (x : A) (xv : val),
              {{{ γ i x ∗ ⌜P x xv⌝ }}}
                fv #i xv @[ip]
                {{{ rv, RET rv;
                    let r := f i x in
                    ⌜Q r rv⌝ ∗ ψ i r }}}) ∗
        ⌜is_listP l lv P⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ i a)
    }}}
      list_mapi fv lv @[ip]
    {{{ rv, RET rv;
        let l' := mapi f l in
        ⌜is_listP l' rv Q⌝ ∗
        ([∗ list] i ↦ a ∈ l', ψ i a)}}}.
  Proof.
    iIntros (Φ) "[#Hf [%Hil Hown]] HΦ".
    rewrite /list_mapi.
    do 3 wp_pure _.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (wp_list_mapi_loopP with "[Hown]").
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

  (* TODO: does this lemma already exist somewhere else? *)
  Lemma app_cons {A} (l1 l2 : list A) a : l1 ++ (a :: l2) = (l1 ++ [a]) ++ l2.
  Proof.
    generalize dependent l2.
    generalize dependent a.
    induction l1 as [ | x l1' IH]; intros a l2; simpl; [done |].
    apply f_equal.
    apply IH.
  Qed.

  Lemma wp_list_iteri_loopP {A}
        (k : nat) (l l1 l2 : list A) (fv lv : val)
        (P : A -> val -> Prop) (γ ψ : nat -> A -> iProp Σ) ip :
    {{{  □ (∀ (i : nat) (x : A) (xv : val),
              {{{ ⌜P x xv⌝ ∗ ⌜(i < length l)%nat⌝ ∗ γ i x }}}
                fv #i xv @[ip]
              {{{ RET #(); ψ i x }}} ) ∗
         ⌜l = l1 ++ l2⌝ ∗
         ⌜length l1 = k⌝ ∗
         ⌜is_listP l2 lv P⌝ ∗
         ([∗ list] i ↦ a ∈ l2, γ (k + i)%nat a)
    }}}
      list_iteri_loop fv #k lv @[ip]
    {{{ RET #(); [∗ list] i ↦ a ∈ l2, ψ (k + i)%nat a }}}.
  Proof.
    iInduction l2 as [ | h l2'] "IH" forall (lv k l1);
      iIntros (Φ) "[#Hf [%Hl [%Hlen [%Hil Hown]]]] HΦ"; simpl in Hil;
      rewrite /list_iteri_loop.
    - rewrite Hil.
      wp_pures.
      by iApply "HΦ".
    - destruct Hil as [hv [lv' [-> [HP Hil']]]].
      do 1 wp_pure _.
      fold list_iteri_loop.
      wp_pures.
      wp_bind (fv _ _).
      iDestruct (big_sepL_cons with "Hown") as "[Hhead Hown]".
      assert ((k + 0)%nat = k%nat) as -> by lia.
      assert (length l1 < length l).
      { rewrite Hl.
        rewrite app_length.
        simpl.
        lia. }
      iApply ("Hf" with "[$Hhead]").
      { eauto with lia. }
      iModIntro.
      iIntros "Hψ".
      wp_pures.
      iAssert (⌜#(k + 1) = #(k + 1)%nat⌝%I) as %->.
      { iPureIntro.
        do 2 apply f_equal; lia. }
      iApply ("IH" with "[Hown]").
      + iSplitL "".
        * iModIntro.
          iIntros (i x xv).
          iModIntro.
          iIntros (ϕ) "(#?&%Hlt&Hγ) Hϕ".
          iApply ("Hf" with "[Hγ]").
          { iFrame; iFrame "#"; done. }
          done.
        * rewrite app_cons in Hl.
          iSplitL ""; [done |].
          iSplitL "".
          { iPureIntro.
            rewrite app_length; simpl.
            lia. }
          iSplitL ""; [done |].
          iApply (big_sepL_impl with "Hown").
          iModIntro.
          iIntros (k' x) "_ Hpre".
          iAssert (⌜(k + 1 + k')%nat = (k + S k')%nat⌝%I) as %->.
          { iPureIntro; lia. }
          done.
      + iModIntro.
        iIntros "Hown".
        iApply "HΦ".
        iApply big_sepL_cons.
        assert ((k + 0)%nat = k) as -> by lia.
        iFrame.
        iAssert (⌜(k + 1)%nat = S k⌝%I) as %->.
        { iPureIntro. do 2 f_equal. lia. }
        iApply (big_sepL_impl with "Hown").
        iModIntro.
        iIntros (k' x) "_ HΨ".
        iAssert (⌜(S k + k')%nat = (k + S k')%nat⌝%I) as %->.
        { iPureIntro. lia. }
        done.
  Qed.

  Lemma wp_list_iteriP {A}
        (l : list A) (fv lv : val)
        (P : A -> val -> Prop) (γ ψ : nat -> A -> iProp Σ) ip :
    {{{  □ (∀ (i : nat) (x : A) (xv : val),
              {{{ ⌜P x xv⌝ ∗ ⌜(i < length l)%nat⌝ ∗ γ i x }}}
                fv #i xv @[ip]
              {{{ RET #(); ψ i x }}} ) ∗
        ⌜is_listP l lv P⌝ ∗
        ([∗ list] i ↦ a ∈ l, γ i a)
    }}}
      list_iteri fv lv @[ip]
      {{{ RET #(); [∗ list] i ↦ a ∈ l, ψ i a }}}.
  Proof.
    iIntros (Φ) "[#Hf [%Hil Hown]] HΦ".
    rewrite /list_iteri.
    do 3 wp_pure _.
    iAssert (⌜#0 = #(0%nat)⌝%I) as %->; [done |].
    iApply (wp_list_iteri_loopP 0 l [] l with "[Hown]").
    - iSplitL ""; last first; [ iFrame; done | ].
      iModIntro.
      iIntros (i x).
      iApply "Hf".
    - by iFrame.
  Qed.

  Lemma wp_list_updateP {A} (l : list A) lv (i : nat) (e : A) ev P ip :
    i < length l →
    {{{ ⌜is_listP l lv P⌝ ∗
        ⌜P e ev⌝ }}}
      list_update lv #i ev @[ip]
    {{{ lv', RET lv'; ⌜is_listP (<[i := e]> l) lv' P⌝ }}}.
  Proof.
    iLöb as "IH" forall (lv l i).
    iIntros (Hi Φ [Hil Hcoh]) "HΦ".
    wp_rec; wp_let; wp_let. destruct l as [|x t].
    - simpl in Hil. rewrite Hil. wp_pures. by iApply "HΦ".
    - rewrite /is_listP in Hil.
      destruct Hil as [hv [tv [-> [HP Hil']]]].
      wp_pures. case_bool_decide; wp_pures.
      + wp_bind (list_tail _).
        iApply (wp_list_tailP _ _ (x :: t)).
        { iPureIntro. eexists; eauto. }
        iNext. iIntros (tm Htm) "/=".
        simpl in Htm.
        iApply wp_list_consP; [done |].
        iNext. iIntros (u Hu) "/=".
        iApply "HΦ"; iPureIntro.
        assert (i = 0)%nat as -> by lia.
        repeat split; auto.
      + wp_bind (list_update _ _ _).
        assert (((Z.of_nat i) - 1)%Z = Z.of_nat (i - 1)) as -> by lia.
        iApply ("IH" $! _ t).
        { iPureIntro; simpl in *; lia. }
        { iPureIntro; done. }
        destruct i; first done; simpl.
        rewrite !Nat.sub_0_r.
        iNext; iIntros (tm Htm) "/=". wp_pures.
        iApply wp_list_consP; [done |].
        iNext; iIntros (? ?).
        by iApply "HΦ".
  Qed.

  (* TODO: this belongs in `list_proof.v` in `vendor/aneris` *)
  Lemma mapi_loop_length {A B} (f : nat -> A -> B) l k : length (mapi_loop f k l) = length l.
  Proof.
    generalize dependent k.
    generalize dependent l.
    induction l as [ | h t IH ]; [done | simpl].
    intros k.
    rewrite (IH (S k)).
    done.
  Qed.

  Lemma mapi_length {A B} (f : nat -> A -> B) l : length (mapi f l) = length l.
  Proof.
    rewrite /mapi.
    apply mapi_loop_length.
  Qed.

End list_proof_alt.
