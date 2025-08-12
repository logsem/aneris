From iris.proofmode Require Import tactics.
From iris.base_logic Require Import iprop. 
From trillium.program_logic Require Import adequacy_utils. 
From heap_lang Require Import lang locales_helpers_hl.
From fairness Require Import locales_helpers.

Close Scope Z.


Section WptpGen.
  Context {Σ: gFunctors}.
  Context (W: expr -> locale heap_lang -> (val → iPropI Σ) -> iProp Σ).
  
  Definition wptp_from_gen 
    (t0 t: list expr) (Φs : list (val → iPropI Σ)) :=
    ([∗ list] tp1_e;Φ ∈ (prefixes_from t0 t);Φs,
       W tp1_e.2 (locale_of tp1_e.1 tp1_e.2) Φ)%I.

  Lemma wptp_from_gen_app' t0 t1 Φs1 t2 Φs2
    (MATCH1: length t1 = length Φs1):
    wptp_from_gen t0 (t1 ++ t2) (Φs1 ++ Φs2) ⊢ wptp_from_gen t0 t1 Φs1 ∗ wptp_from_gen (t0 ++ t1) t2 Φs2. 
  Proof using.
    iIntros.
    rewrite {1}/wptp_from_gen. rewrite prefixes_from_app. 
    iDestruct (big_sepL2_app_inv with "[$]") as "(?&?)".
    2: { iFrame. }
    rewrite prefixes_from_length. tauto.  
  Qed.

  Lemma wptp_from_gen_app t0 t1 Φs1 t2 Φs2:
    wptp_from_gen t0 t1 Φs1 ∗ wptp_from_gen (t0 ++ t1) t2 Φs2 ⊢
      wptp_from_gen t0 (t1 ++ t2) (Φs1 ++ Φs2). 
  Proof using.
    iIntros "[WPS1 WPS2]".
    rewrite {3}/wptp_from_gen. rewrite prefixes_from_app.
    iDestruct (big_sepL2_length with "WPS1") as "%".
    iApply big_sepL2_app_same_length; [tauto| ].
    iFrame. 
  Qed.

  Lemma wptp_gen_split_1 t0 t1 t2 Φs:
    wptp_from_gen t0 (t1 ++ t2) Φs ⊢
      ⌜ exists Φs1 Φs2, Φs1 ++ Φs2 = Φs /\ length Φs1 = length t1 /\ length Φs2 = length t2 ⌝.
  Proof using.
    clear. 
    iIntros "WPS".
    iDestruct (big_sepL2_length with "[$]") as "%LENS".
    rewrite adequacy_utils.prefixes_from_length in LENS.
    iPureIntro.
    do 2 eexists. split.
    { apply (take_drop (length t1)). }
    rewrite length_take. rewrite length_skipn.
    rewrite length_app in LENS. lia.
  Qed.

  Lemma wptp_gen_singleton t0 e Φ:
    wptp_from_gen t0 [e] [Φ] ⊣⊢ W e (locale_of t0 e) Φ. 
  Proof using.
    rewrite /wptp_from_gen. simpl.
    by rewrite bi.sep_emp.
  Qed.

  Lemma new_threads_wptp_from_gen `{!irisG heap_lang M Σ} t efs:
    ([∗ list] i ↦ ef ∈ efs, 
      W ef (locale_of (t ++ take i efs) ef) (fork_post (locale_of (t ++ take i efs) ef))
    )
      ⊣⊢ wptp_from_gen t efs (newposts t (t ++ efs)).
  Proof.
    rewrite  /wptp_from_gen. 
    rewrite big_sepL2_alt; iSplit.
    - iIntros "H". iSplit.
      { rewrite /newposts. rewrite map_length.
        rewrite /newelems. rewrite drop_app_length // map_length !prefixes_from_length //. }
      iInduction efs as [|ef efs] "IH" forall (t); first done.
      rewrite /newposts /newelems.
      rewrite /= !drop_app_length //=.
      iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
      replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                 (prefixes_from (t ++ [ef]) efs))
        with (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
      + iApply "IH". iApply (big_sepL_impl with "H").
        iIntros "!>" (k e Hin) "H". by list_simplifier.
      + list_simplifier.
        replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
        rewrite /newposts /newelems.
        rewrite drop_app_length //.
    - iIntros "[_ H]".
      iInduction efs as [|ef efs] "IH" forall (t); first done.
      rewrite /newposts /newelems.
      rewrite /= !drop_app_length //=.
      iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
      replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                 (prefixes_from (t ++ [ef]) efs))
          with (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
      + iSpecialize ("IH" with "H"). iApply (big_sepL_impl with "IH").
        iIntros "!>" (k e Hin) "H". by list_simplifier.
      + list_simplifier.
        replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
        rewrite /newposts /newelems.
        rewrite drop_app_length //.
  Qed.

  Lemma wptp_from_gen_cons t0 e efs Φ Φs:
    wptp_from_gen t0 (e :: efs) (Φ :: Φs) ⊣⊢ W e (locale_of t0 e) Φ ∗ wptp_from_gen (t0 ++ [e]) efs Φs.
  Proof using. done. Qed. 

  (* TODO: do we need anything stronger (e.g. matching indices for e and Φ) ? *)
  Lemma wptp_from_gen_take_2 t efs Φs τ
    (IN: τ ∈ locales_of_list_from t efs):
    let WPS := wptp_from_gen t efs Φs in
    WPS ⊣⊢ ∃ Φ e, ⌜ Φ ∈ Φs ⌝ ∗ ⌜ from_locale_from t efs τ = Some e ⌝ ∗ W e τ Φ ∗ (W e τ Φ -∗ WPS).
  Proof using.
    simpl. iSplit. 
    2: { iIntros "(%&%&?&?&?&CLOS)". by iApply "CLOS". }
    iIntros "WPS".

    pose proof IN as [e X]%locales_of_list_from_locale_from'.
    apply from_locale_from_lookup in X. apply proj1 in X.
    (* rewrite Nat.sub_0_r /= in X. *)
    pose proof X as (t1 & t2 & -> & LEN)%elem_of_list_split_length. 

    iDestruct (wptp_gen_split_1 with "[$]") as %(?&?&<-&?&?).
    iDestruct (wptp_from_gen_app' with "[$]") as "[? WPS]"; eauto.
    destruct x0; [done| ].
    rewrite wptp_from_gen_cons. iDestruct "WPS" as "[WP ?]".

    assert (length t ≤ τ).
    { rewrite locales_of_list_from_indexes /= in IN.
      apply elem_of_lookup_imap in IN as (?&?&?&?).
      subst τ. clear.
      simpl. lia. }

    assert (from_locale_from t (t1 ++ e :: t2) τ = Some e) as E.
    { eapply from_locale_from_lookup.
      split; eauto. }
    
    do 2 iExists _. iSplit; [| iSplit].
    2: done. 
    { iPureIntro. Unshelve. 2: exact b. set_solver. }
    assert (τ = locale_of (t ++ t1) e) as EQ.
    2: { rewrite -EQ. iFrame.
         iIntros. iApply wptp_from_gen_app. iFrame. simpl.
         by rewrite -EQ. }
    rewrite /locale_of. rewrite length_app.

    (* lia.  *)
    rewrite -LEN. by apply Nat.le_add_sub.     
  Qed.

  (* TODO: try to unify with wptp_from_gen_take_2 *)
  (* TODO: do we need anything stronger (e.g. matching indices for e and Φ) ? *)
  Lemma wptp_from_gen_take_1 t efs Φs e
    (IN: e ∈ efs):
    let WPS := wptp_from_gen t efs Φs in
    WPS ⊣⊢ ∃ Φ t1 t2, let τ := locale_of (t ++ t1) e in
       ⌜ Φ ∈ Φs ⌝ ∗ ⌜ efs = t1 ++ e :: t2 ⌝ ∗ W e τ Φ ∗ (W e τ Φ -∗ WPS).
  Proof using.
    simpl. iSplit.
    2: { iIntros "(%&%&%&?&?&?&CLOS)". by iApply "CLOS". }
    iIntros "WPS".    
    apply elem_of_list_split in IN as (?&?&->).
    iDestruct (wptp_gen_split_1 with "[$]") as %(?&?&<-&?&?).
    iDestruct (wptp_from_gen_app' with "[$]") as "[? WPS]"; eauto.
    destruct x2; [done| ].
    rewrite wptp_from_gen_cons. iDestruct "WPS" as "[WP ?]".
    do 3 iExists _. iSplit; [| iSplit].
    2: { eauto. }
    2: iFrame.
    { iPureIntro. set_solver. }
    iIntros "WP".
    iApply wptp_from_gen_app. iFrame.
  Qed.

  (* EQUIV : locales_equiv t0 t0' *)

  (* Lemma wptp_from_gen_locales_equiv_1_impl t0 t0' efs efs' Φs *)
  (*   (EQUIV: locales_equiv_from t0 t0' efs efs'): *)
  (*   wptp_from_gen t0 efs Φs -∗ wptp_from_gen t0' efs' Φs. *)
  (* Proof using. *)
  (*   iIntros "WPS".  *)
  (*   (* rewrite /wptp_from_gen. *) *)
  (*   (* iApply big_sepL2_proper_2. *) *)
  (*   (* 4: by iFrame.  *) *)
  (*   clear -EQUIV. *)
  (*   Unset Printing Notations. *)
    
  (*   Disable Notation locales_equiv.  *)
  (*   eapply EQUIV.  *)
        
  Lemma wptp_from_gen_locales_equiv_1 t0 t0' efs Φs
    (EQUIV: locales_equiv t0 t0'):
    wptp_from_gen t0 efs Φs ⊣⊢ wptp_from_gen t0' efs Φs.
  Proof using.
    generalize dependent Φs. generalize dependent t0. generalize dependent t0'.
    induction efs.
    { intros. simpl. set_solver. }
    destruct Φs.
    { set_solver. }
    rewrite !wptp_from_gen_cons.
    iApply bi.sep_proper.
    2: { iApply IHefs.
         clear -EQUIV.
         rewrite !prefixes_from_app.
         eapply Forall2_app; try done.
         simpl. constructor; try done.
         (* TODO: specific to heap_lang, can it be generalized? *)
         rewrite /locale_of.
         eapply adequacy_utils.locales_equiv_from_length; eauto. }
    rewrite /locale_of.
    eapply adequacy_utils.locales_equiv_from_length in EQUIV; eauto.
    by rewrite EQUIV.
  Qed.

End WptpGen.


  Lemma wptp_from_gen_upd_2 {Σ: gFunctors}
    (W1 W2: expr -> locale heap_lang -> (val → iPropI Σ) -> iProp Σ) t efs Φs
    (τs: gset (locale heap_lang))
    (IN: τs ⊆ list_to_set $ locales_of_list_from t efs):
    wptp_from_gen W1 t efs Φs -∗                  
    (□ ∀ τ Φ e, ⌜ τ ∈ locales_of_list_from t efs /\ τ ∉ τs ⌝ -∗ W1 e τ Φ -∗ W2 e τ Φ) -∗
    ∃ (M: gmap (locale heap_lang) (expr * (val → iPropI Σ))),
    ⌜ dom M = τs ⌝ ∗
    ([∗ map] τ ↦ '(e, Φ) ∈ M, (* ⌜ Φ ∈ Φs ⌝ ∗  *)⌜ from_locale_from t efs τ = Some e ⌝ ∗ W1 e τ Φ) ∗
    (([∗ map] τ ↦ '(e, Φ) ∈ M, (* ⌜ Φ ∈ Φs ⌝ ∗  *)⌜ from_locale_from t efs τ = Some e ⌝ ∗ W2 e τ Φ) -∗ wptp_from_gen W2 t efs Φs).
  Proof using.
     iInduction efs as [|e efs] "IH" forall (Φs τs t IN). 
     { simpl. iIntros "**".
       apply equiv_empty_L in IN as ->.
       iExists ∅. set_solver. }
     iIntros "WPS #UPD".
     assert (τs ∖ {[ locale_of t e ]} ⊆ list_to_set (locales_of_list_from (t ++ [e]) efs)).
     { simpl in IN. set_solver. }

     destruct Φs as [| Φ Φs]; [done| ].
     rewrite wptp_from_gen_cons. iDestruct "WPS" as "[WP WPS]". 
     
     iSpecialize ("IH" with "[//] [$] []").
     { iModIntro. iIntros "**". iApply ("UPD" with "[] [$]").
       iPureIntro.
       destruct H0.
       rewrite locales_of_list_from_locales. simpl.
       rewrite locales_of_list_from_locales in H0.
       split; [set_solver| ].
       apply not_elem_of_difference in H1 as [? | EQ]; [done| ].
       apply elem_of_singleton in EQ.
       apply elem_of_list_fmap in H0 as ((?&?)&?&?).
       apply elem_of_list_lookup_1 in H1 as (?&?).
       apply prefixes_from_ith_length in H1. simpl in H1.
       rewrite /locale_of in EQ, H0.
       rewrite length_app /= in H1. lia. }

     iDestruct "IH" as (Ts) "(%DOM & WPS & CLOS)".
     iExists (if decide (locale_of t e ∈ τs) then <[ locale_of t e := (e, Φ) ]> Ts else Ts).
     iSplitR.
     { iPureIntro. destruct decide.
       - rewrite dom_insert_L. rewrite DOM.
         rewrite union_comm_L. rewrite difference_union_L. set_solver.
       - set_solver. }
     destruct decide.
     - iSplitL "WP WPS".
       + rewrite big_sepM_insert.
         2: { apply not_elem_of_dom. set_solver. }
         iFrame. iSplitR.
         { iPureIntro.
           pose proof (from_locale_from_locale_of t [] efs e).
           by rewrite app_nil_l app_nil_r in H0. }
         iApply (big_sepM_impl with "[$]").
         iModIntro. iIntros (k (e', Φ')) "%KTH".
         simpl. rewrite decide_False; [set_solver| ].
         intros <-. apply mk_is_Some, elem_of_dom in KTH. set_solver.
       + iIntros "CLOS'".
         rewrite big_sepM_insert.
         2: { apply not_elem_of_dom. set_solver. }
         iDestruct "CLOS'" as "((%EQ & WP2) & WPS2)".
         rewrite wptp_from_gen_cons. iFrame.
         iApply "CLOS". simpl.
         iApply (big_sepM_impl with "[$]").
         iModIntro. iIntros (k (e', Φ')) "%KTH".
         rewrite decide_False; [set_solver| ].
         intros <-. apply mk_is_Some, elem_of_dom in KTH. set_solver.
     - iSplitL "WPS".
       + simpl.
         iApply (big_sepM_impl with "[$]").
         iModIntro. iIntros (k (e', Φ')) "%KTH".
         simpl. rewrite decide_False; [set_solver| ].
         intros <-. apply mk_is_Some, elem_of_dom in KTH. set_solver.
       + iIntros "CLOS'".
         rewrite wptp_from_gen_cons. iSplitL "WP".
         { iApply ("UPD" with "[] [$]").
           iPureIntro. split; [| done].
           rewrite locales_of_list_from_locales. simpl. set_solver. }
         iApply "CLOS". simpl.
         iApply (big_sepM_impl with "[$]").
         iModIntro. iIntros (k (e', Φ')) "%KTH".
         rewrite decide_False; [set_solver| ].
         intros <-. apply mk_is_Some, elem_of_dom in KTH. set_solver.
  Qed.


Definition wptp_gen {Σ} W t Φs := (@wptp_from_gen Σ W [] t Φs).
