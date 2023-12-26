From iris.proofmode Require Import tactics.
From trillium.prelude Require Import finitary.

(* TODO: move *)
(* TODO: rename definitions inside? *)
Section GroupRolesInstantiation.  
  Context {Gl: Type} `{Countable Gl}.
  Context (get_Gls: forall n, { gls: gset Gl | size gls = n}).
  Let get_Gls' n := elements (proj1_sig (get_Gls n)). 

  Instance Gl_inhabited: Inhabited Gl.
  Proof. 
    pose proof (get_Gls 1) as [gls SPEC].
    destruct (decide (gls = ∅)).
    { subst. set_solver. }
    apply finitary.set_choose_L' in n as [g IN].
    econstructor. apply g. 
  Qed.

  Let g0 := @inhabitant _ Gl_inhabited.

  Definition gls' n: list Gl := 
    let gls_Sn := get_Gls' (S n) in
    if (decide (g0 ∈ gls_Sn)) 
    then remove EqDecision0 g0 gls_Sn
    else drop 1 gls_Sn. 
      
  Definition ρlg_i (n i: nat) := nth i (gls' n) g0.

  (* TODO: move *)
  Lemma nth_error_seq n i (DOM: i < n):
    nth_error (seq 0 n) i = Some i.
  Proof.
    erewrite nth_error_nth' with (d := 0).
    - f_equal. by apply seq_nth.
    - by rewrite seq_length. 
  Qed. 

  (* TODO: move *)
  Lemma length_remove_NoDup `{ED: EqDecision A} (l: list A) (a: A)
                            (ND: NoDup l)
    :
    length (remove ED a l) = length l - (if (decide (a ∈ l)) then 1 else 0).
  Proof.
    destruct (decide (a ∈ l)) as [IN| ].
    2: { rewrite notin_remove; [lia| ].
         by intros ?%elem_of_list_In. }
    apply elem_of_list_In, In_nth_error in IN as [i ITH].
    pose proof ITH as (l1 & l2 & -> & LEN)%nth_error_split.
    rewrite remove_app. rewrite notin_remove.
    2: { apply NoDup_app in ND as (?&NIN&?).
         intros IN1. apply (NIN a); [| set_solver]. by apply elem_of_list_In. }
    simpl. rewrite decide_True; [| done].
    rewrite notin_remove.
    2: { rewrite cons_middle app_assoc in ND. 
         apply NoDup_app in ND as (?&NIN&?).
         intros ?%elem_of_list_In. apply (NIN a); set_solver. }
    rewrite !app_length. simpl. lia.
  Qed. 


  Lemma get_Gls'_len n: length (get_Gls' n) = n. 
  Proof.
    rewrite /get_Gls'. 
    destruct (get_Gls n) as [gls SPEC]; simpl in *.
    rewrite -(list_to_set_elements_L gls) in SPEC.
    rewrite size_list_to_set in SPEC; [lia| ].
    apply NoDup_elements.
  Qed. 

  Lemma gls'_len n: length (gls' n) = n.
  Proof. 
    rewrite /gls'. destruct decide.
    - rewrite length_remove_NoDup.
      2: { rewrite /get_Gls'. apply NoDup_elements. }
      rewrite decide_True; [| done].
      rewrite get_Gls'_len. lia. 
    - rewrite skipn_length.
      rewrite get_Gls'_len. lia. 
  Qed. 

  Lemma gls'_ρlg n:
    gls' n = map (ρlg_i n) (seq 0 n). 
  Proof.
    pose proof (gls'_len n) as LEN'. 
    apply nth_ext with (d := g0) (d' := g0).
    { by rewrite fmap_length seq_length. }

    intros i DOM.    
    eapply Some_inj.
    rewrite -nth_error_nth'; [| done].
    rewrite -nth_error_nth'. 
    2: { rewrite fmap_length seq_length. congruence. }
    rewrite nth_error_map.
    rewrite nth_error_seq; [| congruence].
    simpl. rewrite /ρlg_i.
    by apply nth_error_nth'.
  Qed.

  Definition gls n: gset Gl := list_to_set (gls' n). 

  Lemma gls_ρlg n:
    gls n = list_to_set (map (ρlg_i n) (seq 0 n)).
  Proof. 
    rewrite /gls. f_equal. apply gls'_ρlg.
  Qed. 

  Lemma get_Gls'_NoDup n: NoDup (get_Gls' n).
  Proof. 
    rewrite /get_Gls'. apply NoDup_elements.
  Qed.

  (* TODO: move *)
  Lemma NoDup_remove {A: Type} (l: list A)
    (ND: NoDup l):
    forall a EQ, NoDup (remove EQ a l).
  Proof. 
    intros a ?. revert a. induction l.
    { done. }
    intros. simpl. destruct EQ.
    { subst. apply IHl. by inversion ND. }
    econstructor.
    2: { apply IHl. by inversion ND. }
    inversion ND. subst.
    intros IN%elem_of_list_In%in_remove.
    apply H2. apply elem_of_list_In, IN. 
  Qed. 

  Lemma gls'_NoDup n: NoDup (gls' n).
  Proof. 
    rewrite /gls'. destruct decide.
    - apply NoDup_remove. apply get_Gls'_NoDup.
    - apply NoDup_ListNoDup.
      eapply NoDup_app_remove_l.
      erewrite take_drop.
      apply NoDup_ListNoDup. apply get_Gls'_NoDup.
  Qed. 

  Lemma ρlg_i_dom_inj n:
    forall i j, i < n -> j < n -> ρlg_i n i = ρlg_i n j -> i = j. 
  Proof.
    rewrite /ρlg_i.
    rewrite -{1 2}(gls'_len n). apply NoDup_nth.
    apply NoDup_ListNoDup. apply gls'_NoDup. 
  Qed.

End GroupRolesInstantiation.
