From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl excl_auth.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer Require Import sub_action_em.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_logic obligations_em.

Section SignalMap.

  Class SigMapPreG Σ := {
      sm_sig_map :> inG Σ (authUR (gmapUR nat (agreeR SignalId)));
  }.
  
  Class SigMapG Σ := {
      sm_PreG :> SigMapPreG Σ;
      sm_γ__smap: gname;
  }.


  Context `{DISCR__d: OfeDiscrete DegO} `{DISCR__l: OfeDiscrete LevelO}.
  Context {LEQUIV__l: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.   
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  Context `{OP': ObligationsParamsPre Degree Level LIM_STEPS}.
  Let EO_OP := LocaleOP (Locale := locale heap_lang). 
  Existing Instance EO_OP. 

  Context {Σ: gFunctors} {oGS: ObligationsGS Σ}.

  Context (L: nat -> Level). 

  Definition ex_ith_sig B (i: nat) (s: SignalId): iProp Σ :=
    sgn s (L i) (Some $ B i).

  Definition smap_auth `{SigMapG Σ} smap := 
    own sm_γ__smap (● (to_agree <$> smap: gmapUR nat (agreeR SignalId))).
  
  Definition smap_repr `{SigMapG Σ} B D: iProp Σ :=
    ∃ (smap: gmap nat SignalId),
    smap_auth smap ∗ ([∗ map] i ↦ s ∈ smap, ex_ith_sig B i s) ∗
    ⌜ dom smap = D ⌝.

  Definition ith_sig `{SigMapG Σ} (i: nat) (s: SignalId): iProp Σ :=
    own sm_γ__smap (◯ {[ i := to_agree s ]}).

  (* TODO: move, remove duplicates *)
  Lemma map_nat_agree_valid {A: ofe} (m: gmap nat A):
    ✓ ((to_agree <$> m): gmapUR nat (agreeR A)).
  Proof using.
    red. intros k.
    destruct lookup eqn:LL; [| done].
    apply lookup_fmap_Some in LL. 
    destruct LL as (a&<-&?). 
    done.
  Qed.

  Lemma init_smap_repr `{SigMapPreG Σ, invGS_gen HasNoLc Σ} τ R B (D: gset nat):
    obls τ R -∗ BOU ∅ (2 * size D) (∃ (smap: gmap nat SignalId) (SMG: SigMapG Σ), 
          smap_repr B D ∗ ⌜ dom smap = D ⌝ ∗ obls τ (R ∪ map_img (filter (fun '(i, _) => B i = false) smap)) ∗ ([∗ map] i ↦ s ∈ smap, ith_sig i s)).
  Proof using LEQUIV__l DISCR__l.
    clear DISCR__d.
    iIntros "OB".
    iAssert (BOU ∅ (2 * size D) (∃ smap, ⌜ dom smap = D ⌝ ∗ obls τ (R ∪ map_img (filter (fun '(i, _) => B i = false) smap)) ∗ [∗ map] i ↦ s ∈ smap, ex_ith_sig B i s))%I with "[OB]" as "SIGS".
    { iInduction D as [| i D FRESH] "IH" using set_ind_L forall (R). 
      { iApply BOU_intro. iExists ∅.
        rewrite big_opM_empty. iSplit; [iPureIntro; set_solver| ].
        rewrite map_img_empty_L union_empty_r_L. set_solver. }
      rewrite size_union; [| set_solver].
      rewrite Nat.mul_add_distr_l. rewrite size_singleton. simpl. 
      iApply OU_BOU. iApply (OU_wand with "[-OB]").
      2: { iApply (OU_create_sig _ _ (L i) with "OB"). }
      iIntros "(%sid & SIG & OB & %FRESH_SID)".
      iAssert (BOU ∅ 1 (sgn sid (L i) (Some $ B i) ∗ obls τ (R ∪ if B i then ∅ else {[sid]})))%I with "[-]" as "SET".
      { destruct (B i).
        2: { iApply BOU_intro. iFrame. }
        iApply OU_BOU. iApply (OU_wand with "[]").
        2: { iApply (OU_set_sig with "[$] [$]"). set_solver. }
        iIntros "[SIG OB]". iApply BOU_intro. iFrame.
        iApply obls_proper; [| by iFrame].
        set_solver. }
      iApply (BOU_split _ _ 1). iApply (BOU_wand with "[-SET] [$]").
      iIntros "[SIG OB]".

      rewrite Nat.add_0_r.
      iSpecialize ("IH" with "[$]").
      iApply (BOU_wand with "[-IH] [$]").
      iIntros "(%smap & %DOM & OB & SIGS)". 
      iExists (<[ i := sid ]> smap).
      iSplit.
      { iPureIntro. set_solver. }
      iSplitL "OB".
      { iApply obls_proper; [| by iFrame].
        rewrite -union_assoc. eapply sets.union_proper; [done| ].
        destruct (B i) eqn:Bi.
        - rewrite map_filter_insert_not; [| by rewrite Bi].
          set_solver.
        - rewrite map_filter_insert_True; [| done].
          rewrite map_img_insert_L. rewrite delete_notin; [done| ].
          apply map_filter_lookup_None_2. left.
          apply not_elem_of_dom. congruence. }
      rewrite big_opM_insert; [| apply not_elem_of_dom; congruence].
      iFrame. }

    rewrite {2}(plus_n_O (2 * _)). iApply BOU_split.
    iApply (BOU_wand with "[] [$]"). iIntros "(%smap & %DOM & OB & SIGS)".
    iMod (own_alloc (● ((to_agree <$> smap): gmapUR nat (agreeR SignalId)) ⋅ ◯ _)) as (γ) "[A F]".
    { apply auth_both_valid_2; [| reflexivity]. apply map_nat_agree_valid. }
    iApply BOU_intro.
    iExists _, {| sm_γ__smap := γ |}. iFrame.
    iSplitL "SIGS A".
    { iExists _. by iFrame. }
    rewrite /ith_sig.
    destruct (decide (smap = ∅)).
    { subst. set_solver. }
    rewrite -big_opM_own; [| done].
    iSplit; [done| ]. 
    simpl. iApply own_proper; [| by iFrame]. 
    rewrite -big_opM_auth_frag. f_equiv.
    rewrite -(big_opM_singletons (_ <$> _)).
    by rewrite big_opM_fmap.
  Qed.

  Context {SM_G: SigMapG Σ}.

  Lemma ith_sig_in i s smap:
    ⊢ ith_sig i s -∗ smap_auth smap -∗ ⌜ smap !! i = Some s ⌝.
  Proof using.
    iIntros "S SM". iCombine "SM S" as "SM".
    iDestruct (own_valid with "SM") as %V.
    apply auth_both_valid_discrete in V as [V ?].
    apply singleton_included_l in V. destruct V as (x & ITH & LE).
    iPureIntro.
    rewrite Some_included_total in LE.
    destruct (to_agree_uninj x) as [y X].
    { eapply lookup_valid_Some; eauto. done. }
    rewrite -X in LE. apply to_agree_included in LE.
    rewrite -X in ITH.
    
    eapply leibniz_equiv.       
    rewrite lookup_fmap in ITH.
    rewrite -LE in ITH.
    
    apply fmap_Some_equiv in ITH as (?&ITH&EQ).
    rewrite ITH. apply to_agree_inj in EQ. by rewrite EQ.
  Qed.

  (* Lemma ith_sig_retrieve i s B (smap: gmap nat SignalId): *)
  (*   ⊢ ⌜ smap !! i = Some s ⌝ -∗ smap_repr B smap ==∗ ith_sig i s ∗ smap_repr B smap.  *)
  (* Proof using. *)
  (*   clear LEQUIV__l DISCR__l DISCR__d.     *)
  (*   iIntros "%ITH [S SR]". *)
  (*   rewrite /smap_repr. iFrame "SR". *)
  (*   rewrite /ith_sig -own_op cmra_comm.  *)
  (*   iApply own_update.  *)
  (*   1: eapply auth_update_alloc. *)
  (*   2: by iFrame. *)
  (*   etrans.  *)
  (*   - eapply core_id_local_update. *)
  (*     2: { apply singleton_included_l with (i := i). *)
  (*          eexists. split; [| reflexivity]. *)
  (*          rewrite lookup_fmap ITH. *)
  (*          simpl. reflexivity. } *)
  (*     apply _. *)
  (*   - rewrite gmap_disj_op_union. *)
  (*     { rewrite map_empty_union. reflexivity. } *)
  (*     apply map_disjoint_dom. simpl. set_solver. *)
  (* Qed. *)

  Lemma ith_sig_sgn i s B D:
    ⊢ ith_sig i s -∗ smap_repr B D -∗ sgn s (L i) None.
  Proof using.
    iIntros "S (%&?&?&?)".
    iDestruct (ith_sig_in with "[$] [$]") as "%ITH". 
    iDestruct (big_sepM_lookup with "[$]") as "ITH"; eauto.
    rewrite /ex_ith_sig.     
    by iDestruct (sgn_get_ex with "[$]") as "[??]". 
  Qed.

  Lemma smap_repr_split B D i s:
    ⊢ ith_sig i s -∗ smap_repr B D -∗
      ex_ith_sig B i s ∗ (ex_ith_sig B i s -∗ smap_repr B D).
  Proof using.
    iIntros "#ITH (%&SM&SR&%)".
    iDestruct (ith_sig_in with "[$] [$]") as "%ITH".
    rewrite /smap_repr /smap_auth. 
    rewrite {2}(map_split smap i) ITH /=.
    rewrite !big_sepM_union.
    2: apply map_disjoint_singleton_l_2; by apply lookup_delete.
    iDestruct "SR" as "[S SR]". rewrite big_sepM_singleton.
    iFrame. iIntros. iExists _. iFrame "SM".
    iSplitL; [| done]. 
    rewrite {2}(map_split smap i) ITH /=.
    rewrite !big_sepM_union.
    2: apply map_disjoint_singleton_l_2; by apply lookup_delete.
    iFrame. by rewrite big_sepM_singleton.    
  Qed.

  Lemma smap_repr_split_upd B B' D i s
    (OTHER_PRES: forall j, j ≠ i -> j ∈ D -> B' j = B j):
    ⊢ ith_sig i s -∗ smap_repr B D -∗
      ex_ith_sig B i s ∗ (ex_ith_sig B' i s -∗ smap_repr B' D).
  Proof using.
    clear LEQUIV__l DISCR__l DISCR__d.
    iIntros "#ITH (%&SM&SR&%)".
    iDestruct (ith_sig_in with "[$] [$]") as "%ITH".
    rewrite /smap_repr.
    rewrite {2}(map_split smap i) ITH /=.
    rewrite !big_sepM_union.
    2: apply map_disjoint_singleton_l_2; by apply lookup_delete.
    iDestruct "SR" as "[S SR]". rewrite !big_sepM_singleton.
    iFrame.
    iIntros. iExists _. iFrame. iSplitL; [| done].
    rewrite {2}(map_split smap i) ITH /=.
    rewrite !big_sepM_union.
    2: apply map_disjoint_singleton_l_2; by apply lookup_delete.
    rewrite !big_sepM_singleton. iFrame. 
    iApply (big_sepM_impl with "[$]"). iIntros "!> %% %OTHER".
    apply lookup_delete_Some in OTHER as [? ?%mk_is_Some%elem_of_dom]. 
    rewrite /ex_ith_sig. rewrite OTHER_PRES; [by iIntros; iFrame| ..].
    all: set_solver.
  Qed.

  Lemma smap_set_sig i s B B' D τ R
    (SET': B' i = true)
    (Rs: s ∈ R)
    (OTHER_PRES: forall j, j ≠ i -> j ∈ D -> B' j = B j):
    ⊢ smap_repr B D -∗ 
      ith_sig i s -∗
      obls τ R -∗
      OU (smap_repr B' D ∗ obls τ (R ∖ {[ s ]})).
  Proof using LEQUIV__l DISCR__l.
    iIntros "SR #ITH OB".
    iDestruct (smap_repr_split_upd with "[$] [$]") as "[SIGi SR']"; [done| ].
    rewrite {1}/ex_ith_sig.
    iApply (OU_wand with "[SR']").
    2: { iApply (OU_set_sig with "[$] [$]"). done. }
    iIntros "[SIGi OB]". iFrame. 
    iApply "SR'". by rewrite /ex_ith_sig SET'.
  Qed. 

  (* TODO: use bupd in definition of OU *)
  (* TODO: get rid of this version*)
  Lemma smap_create_ep' i B D π q τ d__h d__l
    (* (PH_LE: phase_le π__cp π) *)
    (LT: i ∈ D)
    (DEG_LT: deg_lt d__l d__h):
    ⊢ smap_repr B D -∗ cp π d__h -∗ th_phase_frag τ π q -∗
      OU (|==> ∃ s, ith_sig i s ∗ ep s π d__l ∗ smap_repr B D ∗ th_phase_frag τ π q).
  Proof using DISCR__d DISCR__l LEQUIV__l.
    iIntros "SR CP PH".
    rewrite /smap_repr. iDestruct "SR" as "(% & AUTH & SIGS & %DOM)".
    rewrite -DOM in LT. apply elem_of_dom in LT as [s ITH].
    rewrite {2}(map_split smap i) ITH /=.
    setoid_rewrite big_sepM_union.
    2: { apply map_disjoint_singleton_l_2. by apply lookup_delete. }
    iDestruct "SIGS" as "[SIG SIGS]". setoid_rewrite big_sepM_singleton.
    rewrite {1}/ex_ith_sig. 
    iDestruct (create_ep_upd with "CP [$] [PH]") as "OU".
    { done. }
    { done. }
    iMod (own_update with "AUTH") as "X". 
    { apply auth_update_dfrac_alloc. 
      2: { apply singleton_included_l with (i := i).
           rewrite lookup_fmap ITH. eexists. split; [| reflexivity].
           simpl. reflexivity. }
      apply _. }
    iApply (OU_wand with "[-OU]"); [| by iFrame].
    iIntros "(EP & SIG & PH)".
    iDestruct "X" as "[? ITH]". 
    iExists _. iFrame. iModIntro.
    iExists _. iFrame. iSplitL; [| done].
    rewrite {2}(map_split smap i) ITH /=.
    setoid_rewrite big_sepM_union.
    2: { apply map_disjoint_singleton_l_2. by apply lookup_delete. }
    rewrite big_sepM_singleton. iFrame.  
  Qed.

  (* Lemma ith_sig_agree i s s': *)
  (*   ith_sig i s -∗ ith_sig i s' -∗ ⌜ s' = s ⌝. *)
  (* Proof using. *)
  (*   iIntros "S1 S2". iCombine "S1 S2" as "S". *)    

  Lemma smap_create_ep i s B D π q τ d__h d__l
    (DEG_LT: deg_lt d__l d__h):
    ⊢ ith_sig i s -∗ smap_repr B D -∗ cp π d__h -∗ th_phase_frag τ π q -∗
      OU (|==> ep s π d__l ∗ smap_repr B D ∗ th_phase_frag τ π q).
  Proof using DISCR__d DISCR__l LEQUIV__l.
    iIntros "ITH SR CP PH".
    rewrite /smap_repr. iDestruct "SR" as "(% & AUTH & SIGS & %DOM)".
    iDestruct (ith_sig_in with "[$] [$]") as %ITH.
    rewrite {2}(map_split smap i) ITH /=.
    setoid_rewrite big_sepM_union.
    2: { apply map_disjoint_singleton_l_2. by apply lookup_delete. }
    iDestruct "SIGS" as "[SIG SIGS]". setoid_rewrite big_sepM_singleton.
    rewrite {1}/ex_ith_sig. 
    iDestruct (create_ep_upd with "CP [$] [PH]") as "OU".
    { done. }
    { done. }
    iMod (own_update with "AUTH") as "X". 
    { apply auth_update_dfrac_alloc. 
      2: { apply singleton_included_l with (i := i).
           rewrite lookup_fmap ITH. eexists. split; [| reflexivity].
           simpl. reflexivity. }
      apply _. }
    iApply (OU_wand with "[-OU]"); [| by iFrame].
    iIntros "(EP & SIG & PH)". iFrame. 
    iDestruct "X" as "[? ITH_]". 
    iExists _. iFrame. iModIntro. iSplit; [| done].
    rewrite {2}(map_split smap i) ITH /=.
    setoid_rewrite big_sepM_union.
    2: { apply map_disjoint_singleton_l_2. by apply lookup_delete. }
    rewrite big_sepM_singleton. iFrame.
  Qed.
  
  Lemma lookup_delete_ne' `{Countable K} {V: Type} (k: K) (m: gmap K V)
    (NOk: k ∉ dom m):
    delete k m = m.
  Proof using.
    apply delete_notin. by apply not_elem_of_dom.
  Qed.

  Lemma smap_sgns_extend (B B': nat -> bool)
    (smap: gmap nat SignalId) (s : SignalId) (m : nat) (* lm *)
    (FRESH: m ∉ dom smap)
    (PRES: forall i, i ∈ dom smap -> B' i = B i)
    :
    ⊢ ([∗ map] k↦y ∈ smap, sgn y (L k) (Some (B k))) -∗
       sgn s (L m) (Some (B' m)) -∗
       [∗ map] i↦s0 ∈ <[m := s]> smap, sgn s0 (L i) (Some $ B' i).
  Proof using.
    iIntros "SIGS SG".
    rewrite big_opM_insert_delete. 
    iSplitL "SG"; [done| ].
    rewrite lookup_delete_ne'; [| done].
    iApply (big_sepM_impl with "[$]"). iModIntro.
    iIntros (??) "% ?".
    rewrite PRES; [done| ].
    eapply elem_of_dom; eauto. 
  Qed.

  Lemma BOU_smap_extend `{invGS_gen HasNoLc Σ} τ m D R
    (B B': nat -> bool)
    (PRES: forall i, i ∈ D -> B' i = B i)
    (FRESH_UNSET: B' m = false)
    (FRESH: m ∉ D)
    :
    ⊢ obls τ R -∗ smap_repr B D -∗
      BOU ∅ 1 (
        |==> (∃ s',
             smap_repr B' (D ∪ {[ m ]}) ∗
             ith_sig m s' ∗ obls τ (R ∪ {[s']}) ∗
             ⌜ s' ∉ R ⌝ ∗ sgn s' (L m) None)).
    Proof using LEQUIV__l DISCR__l DISCR__d.
      iIntros "OBLS SM".
      iApply OU_BOU.
      iDestruct (OU_create_sig with "OBLS") as "FOO".
      iApply (OU_wand with "[-FOO]"); [| by iFrame].
      iIntros "(%s' & SG & OBLS & %NEW)".
      iApply BOU_intro.
      rewrite /smap_repr. iDestruct "SM" as "(% & SM & SIGS & %DOM)".
      iMod (own_update with "SM") as "SM".
      { apply auth_update_alloc. eapply (alloc_singleton_local_update _ m (to_agree s')).
        2: done.
        apply not_elem_of_dom. set_solver. }
      iModIntro. iDestruct "SM" as "[SM S']".
      iDestruct (sgn_get_ex with "[$]") as "[SG #SG0]".
      iExists s'.
      rewrite -fmap_insert. iFrame "#∗". iSplit; [| done].
      iExists _. iFrame. iSplitL.
      2: { iPureIntro. set_solver. }
      iApply (smap_sgns_extend with "[$]"); try done.
      1, 2: set_solver.
      rewrite FRESH_UNSET. iFrame.
    Qed.
      
    Lemma ith_sig_expect i sw τ π q D R d B
      (UNSETi: B i = false):
      ⊢ ep sw π d -∗ th_phase_frag τ π q -∗
         smap_repr B D -∗ ith_sig i sw -∗
         obls τ R -∗ sgns_level_gt R (L i) -∗ 
         OU (cp π d ∗ smap_repr B D ∗ th_phase_frag τ π q ∗ obls τ R).
    Proof using LEQUIV__l DISCR__l.
      iIntros "#EP PH SM #SW OBLS #OBLS_LT". 
      iDestruct (smap_repr_split with "SW [$]") as "[SGw SR]".
      rewrite {1}/ex_ith_sig. rewrite UNSETi. 
      iDestruct (expect_sig_upd with "EP [$] [$] [$] [$]") as "OU".
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "(CP1 & SIGW & OBLS & PH)".
      iFrame. iApply "SR". rewrite /ex_ith_sig. by rewrite UNSETi.
    Qed.

End SignalMap.


Section SignalsBlock.

  Definition sigs_block (smap: gmap nat SignalId) from len: list SignalId :=
    map (fun k => default 0 (smap !! k)) (seq from len).

  Lemma sigs_block_in smap from len:
    forall s i, smap !! i = Some s -> i ∈ seq from len -> s ∈ sigs_block smap from len.
  Proof using.
    intros ?? ITH DOM. rewrite /sigs_block.
    apply elem_of_list_In. apply in_map_iff. setoid_rewrite <- elem_of_list_In. 
    eexists. split; eauto. by rewrite ITH.
  Qed.

  Lemma sigs_block_len smap from len: length $ sigs_block smap from len = len.
  Proof using.
    rewrite /sigs_block. by rewrite map_length seq_length.
  Qed.

  Lemma sigs_block_is_Some smap from len:
    forall k, is_Some (sigs_block smap from len !! k) <-> k < len.
  Proof using.
    intros. 
    rewrite lookup_lt_is_Some. by rewrite sigs_block_len.
  Qed.

  Lemma sigs_block_lookup_eq smap from len:
    forall k, k < len -> from + k ∈ dom smap -> sigs_block smap from len !! k = smap !! (from + k). 
  Proof using.
    intros ? DOMsb DOMm.
    rewrite /sigs_block.
    rewrite list_lookup_fmap.
    rewrite lookup_seq_lt; [| done]. simpl.
    apply elem_of_dom in DOMm as [? DOMm]. by rewrite DOMm.
  Qed. 

End SignalsBlock.
