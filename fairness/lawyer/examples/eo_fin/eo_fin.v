From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.base_logic.lib Require Import invariants.
From trillium.fairness Require Import locales_helpers utils.
From trillium.fairness.lawyer Require Import program_logic sub_action_em.
From trillium.fairness.lawyer.obligations Require Import obligations_model obls_utils obligations_resources obligations_logic obligations_em.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.
From trillium.fairness.lawyer.examples Require Import bounded_nat.


Close Scope Z.

Definition EODegree n := bounded_nat n. 
Definition EOLevel n := bounded_nat n.


Section SignalMap.

  Class SigMapPreG Σ := {
      sm_sig_map :> inG Σ (authUR (gmapUR nat (agreeR SignalId)));
  }.
  
  Class SigMapG Σ := {
      sm_PreG :> SigMapPreG Σ;
      sm_γ__smap: gname;
  }.

  Context `{SigMapG Σ}.

  Context `{DISCR__d: OfeDiscrete DegO} `{DISCR__l: OfeDiscrete LevelO}.
  Context {LEQUIV__l: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.   
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.
  (* Context `{OP: ObligationsParams Degree Level Locale LIM_STEPS}. *)
  Context `{OP': ObligationsParamsPre Degree Level LIM_STEPS}.
  Let EO_OP := LocaleOP (Locale := locale heap_lang). 
  Existing Instance EO_OP. 

  Context {oGS: ObligationsGS Σ}.

  Context (L: nat -> Level). 

  Definition ex_ith_sig B (i: nat) (s: SignalId): iProp Σ :=
    sgn s (L i) (Some $ B i) (oGS := oGS). 
  
  Definition smap_repr B K (smap: gmap nat SignalId): iProp Σ :=
    own sm_γ__smap (● (to_agree <$> smap: gmapUR nat (agreeR SignalId))) ∗
    ⌜ dom smap = set_seq 0 K ⌝ ∗
    ([∗ map] i ↦ s ∈ smap, ex_ith_sig B i s).

  Definition ith_sig (i: nat) (s: SignalId): iProp Σ :=
    own sm_γ__smap (◯ {[ i := to_agree s ]}).

  Lemma ith_sig_in i s B K (smap: gmap nat SignalId):
    ⊢ ith_sig i s -∗ smap_repr B K smap -∗ ⌜ smap !! i = Some s ⌝.
  Proof using.
    iIntros "S (SM & ? & ?)". iCombine "SM S" as "SM".
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

  Lemma ith_sig_sgn i s B K (smap: gmap nat SignalId):
    ⊢ ith_sig i s -∗ smap_repr B K smap -∗ sgn s (L i) None (oGS := oGS).
  Proof using.
    iIntros "S SR".
    iDestruct (ith_sig_in with "[$] [$]") as "%ITH". 
    iDestruct "SR" as "(SM & % & ?)".
    iDestruct (big_sepM_lookup with "[$]") as "ITH"; eauto.
    rewrite /ex_ith_sig.     
    by iDestruct (sgn_get_ex with "[$]") as "[??]". 
  Qed.

  Lemma smap_repr_split B K smap i s:
    ⊢ ith_sig i s -∗ smap_repr B K smap -∗
      ex_ith_sig B i s ∗ (ex_ith_sig B i s -∗ smap_repr B K smap).
  Proof using.
    iIntros "#ITH SR".
    iDestruct (ith_sig_in with "[$] [$]") as "%ITH".
    rewrite /smap_repr. iDestruct "SR" as "(SM & % & SR)".
    rewrite {2 5}(map_split smap i) ITH /=.
    rewrite !big_sepM_union.
    2: apply map_disjoint_singleton_l_2; by apply lookup_delete.
    iDestruct "SR" as "[S SR]". rewrite big_sepM_singleton.
    iFrame. iIntros. iFrame. done.
  Qed.

  Lemma smap_repr_split_upd B B' m smap i s
    (OTHER_PRES: forall j, j ≠ i -> j ∈ dom smap -> B' j = B j):
    ⊢ ith_sig i s -∗ smap_repr B m smap -∗
      ex_ith_sig B i s ∗ (ex_ith_sig B' i s -∗ smap_repr B' m smap).
  Proof using LEQUIV__l DISCR__l DISCR__d.
    iIntros "#ITH SR".
    iDestruct (ith_sig_in with "[$] [$]") as "%ITH".
    rewrite /smap_repr. iDestruct "SR" as "(SM & % & SR)".
    rewrite {2 5}(map_split smap i) ITH /=.
    rewrite !big_sepM_union.
    2: apply map_disjoint_singleton_l_2; by apply lookup_delete.
    iDestruct "SR" as "[S SR]". rewrite !big_sepM_singleton.
    iFrame.
    2: { apply map_disjoint_dom. set_solver. }
    iIntros. iSplitR; [done| ]. iFrame.
    iApply (big_sepM_impl with "[$]"). iIntros "!> %% %OTHER".
    apply lookup_delete_Some in OTHER as [? ?%mk_is_Some%elem_of_dom]. 
    rewrite /ex_ith_sig. rewrite OTHER_PRES; [by iIntros; iFrame| ..]; done. 
  Qed.

  (* TODO: use bupd in definition of OU *)
  Lemma smap_create_ep i B K smap π π__cp τ d__h d__l
    (PH_LE: phase_le π__cp π)
    (LT: i < K)
    (DEG_LT: deg_lt d__l d__h):
    ⊢ smap_repr B K smap -∗ 
      cp π__cp d__h (oGS := oGS) -∗
      th_phase_ge τ π (oGS := oGS) -∗
      |==> OU (∃ s, ith_sig i s ∗
                    ep s π__cp d__l (oGS := oGS) ∗ smap_repr B K smap ∗
                    th_phase_ge τ π (oGS := oGS)) (oGS := oGS).
  Proof using DISCR__d DISCR__l LEQUIV__l.
    iIntros "SR CP PH".
    rewrite /smap_repr. iDestruct "SR" as "(AUTH & %DOM & SIGS)".
    assert (i ∈ dom smap) as [s ITH]%elem_of_dom.
    { rewrite DOM. apply elem_of_set_seq. lia. }
    rewrite {2 5}(map_split smap i) ITH /=.
    setoid_rewrite big_sepM_union.
    2, 3: apply map_disjoint_singleton_l_2; by apply lookup_delete.
    iDestruct "SIGS" as "[SIG SIGS]". setoid_rewrite big_sepM_singleton.
    rewrite {1}/ex_ith_sig. 
    iDestruct (create_ep_upd with "CP [$] [PH]") as "OU".
    { eauto. }
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
    iExists _. iFrame. done.
  Qed.

  (* TODO: move, find existing? *)
  Lemma lookup_delete_ne' `{Countable K} {V: Type} (k: K) (m: gmap K V)
    (NOk: k ∉ dom m):
    delete k m = m.
  Proof using.
    apply map_eq. intros.
    destruct (decide (i = k)) as [-> | ?].
    - rewrite lookup_delete. symmetry.
      by apply not_elem_of_dom.
    - by apply lookup_delete_ne.
  Qed.                          

  Lemma smap_sgns_extend (B0: nat -> nat -> bool)
    (smap: gmap nat SignalId) (s : SignalId) (m : nat) (* lm *)
    (DOM: dom smap = set_seq 0 m)
    (PRES: forall i, i ∈ dom smap -> B0 (m + 1) i = B0 m i)
    (* (LVL: lvl2nat lm = m) *)
    :
    ⊢ ([∗ map] k↦y ∈ smap, sgn y (L k) (Some (B0 m k)) (oGS := oGS)) -∗
       sgn s (L m) (Some (B0 (m + 1) m)) (oGS := oGS) -∗
       [∗ map] i↦s0 ∈ <[m := s]> smap, sgn s0 (L i) (Some $ B0 (m + 1) i) (oGS := oGS).
  Proof using.
    iIntros "SIGS SG".
    rewrite big_opM_insert_delete. 
    iSplitL "SG"; [done| ].
    rewrite lookup_delete_ne'.
    2: { rewrite DOM. intros ?%elem_of_set_seq. lia. }
    iApply (big_sepM_impl with "[$]"). iModIntro.
    iIntros (??) "% ?".
    rewrite PRES; [done| ].
    eapply elem_of_dom; eauto. 
    (* apply lookup_delete_Some in H0 as [??]. *)
    (* apply mk_is_Some, elem_of_dom in H1. *)
    (* rewrite DOM in H1. apply elem_of_set_seq in H1. *)
    (* assert ((k <? m) = (k <? m + 1) \/ k = m). *)
    (* { destruct (decide (k = m)); [tauto| ]. left. *)
    (*   destruct (k <? m) eqn:LT. *)
    (*   - rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [done | ]. *)
    (*     apply PeanoNat.Nat.ltb_lt in LT. lia. *)
    (*   - rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [done | ]. *)
    (*     apply PeanoNat.Nat.ltb_ge in LT. lia. } *)
    (* destruct H2; [| done]. rewrite H2. done. *)
  Qed.

  Lemma BMU_smap_extend `{invGS_gen HasNoLc Σ} τ m smap R B0
    (PRES: forall i, i ∈ dom smap -> B0 (m + 1) i = B0 m i)
    (FRESH_UNSET: B0 (m + 1) m = false):
    ⊢ obls τ R (oGS := oGS) -∗ smap_repr (B0 m) m smap -∗
      BMU ∅ 1 (
        |==> (∃ s',
             smap_repr (B0 (m + 1)) (m + 1) (<[m := s']> smap) ∗
             ith_sig m s' ∗ obls τ (R ∪ {[s']}) (oGS := oGS) ∗
             ⌜ s' ∉ R ⌝)) (oGS := oGS).
    Proof using LEQUIV__l DISCR__l DISCR__d.
      iIntros "OBLS SM".
      iApply OU_BMU.
      iDestruct (OU_create_sig with "OBLS") as "FOO".
      iApply (OU_wand with "[-FOO]"); [| by iFrame].
      iIntros "(%s' & SG & OBLS & %NEW)".
      iApply BMU_intro.
      rewrite /smap_repr. iDestruct "SM" as "(SM & %DOM & SIGS)". 
      iMod (own_update with "SM") as "SM".
      { apply auth_update_alloc. eapply (alloc_singleton_local_update _ m (to_agree s')).
        2: done.
        apply not_elem_of_dom. rewrite dom_fmap. rewrite DOM.
        intros ?%elem_of_set_seq. lia. }
      iModIntro. iDestruct "SM" as "[SM S']".
      iExists s'.
      rewrite -fmap_insert. iFrame. iSplit; [| done].
      iSplitR.
      { iPureIntro. rewrite dom_insert_L.
        rewrite set_seq_add_L. rewrite -DOM. set_solver. }
      iApply (smap_sgns_extend with "[$]"); try done.
      rewrite FRESH_UNSET. iFrame.
    Qed.
      
  (*   Lemma BMU_smap_restore τ s m smap *)
  (*     (DOM : dom smap = set_seq 0 (B `min` (m + 2))) *)
  (*     (IN : smap !! m = Some s) *)
  (*     (lm : sigO (λ i : nat, i < LIM)) *)
  (*     (LVL : lvl2nat lm = m): *)
  (*       ⊢ *)
  (* obls τ ∅ (oGS := oGS) -∗ *)
  (* ([∗ map] k↦y ∈ delete m smap, ∃ l0 : sigO (λ i : nat, i < LIM), *)
  (*                                         sgn y l0 (Some (k <? m)) (oGS := oGS) ∗ *)
  (*                                         ⌜lvl2nat l0 = k⌝) -∗ *)
  (* (sgn s lm (Some true) (oGS := oGS)) -∗ *)
  (* own eofin_smap (● ((to_agree <$> smap): gmap _ _)) -∗ *)
  (* BMU (⊤ ∖ ↑nroot.@"eofin") 1 *)
  (*   (⌜B ≤ m + 2⌝ ∗ obls τ ∅ (oGS := oGS) ∗ smap_repr_eo (B `min` (m + 2)) (m + 1) smap *)
  (*    ∨ (|==> ⌜m + 2 < B⌝ ∗ *)
  (*         (∃ (s' : SignalId) (lm': EOLevel B), *)
  (*            smap_repr_eo (B `min` (m + 3)) (m + 1) (<[m + 2:=s']> smap) ∗ *)
  (*            ith_sig (m + 2) s' ∗ obls τ {[s']} (oGS := oGS) ∗ *)
  (*            ⌜lvl2nat lm' = (m + 2)%nat⌝))) (oGS := oGS). *)
  (*   Proof using. *)
  (*     iIntros "OBLS SIGS SIG SM". *)
  (*     destruct (Nat.le_gt_cases B (m + 2)). *)
  (*     { rewrite PeanoNat.Nat.min_l in DOM; [| done].  *)
  (*       iApply BMU_intro. iLeft. iFrame. *)
  (*       iSplitR; [done| ]. iSplitR. *)
  (*       { iPureIntro. rewrite PeanoNat.Nat.min_l; auto. } *)
  (*       iApply (restore_map with "[$] [$]"); eauto. *)
  (*       rewrite DOM. f_equal. symmetry. by apply Nat.min_l. } *)
      
  (*     iApply OU_BMU. *)
  (*     assert {lm' : EOLevel B | lvl2nat lm' = m + 2} as [lm' LVL']. *)
  (*     { set (lm' := exist _ (m + 2) H0: EOLevel B). *)
  (*       exists lm'. done. } *)
  (*     iDestruct (OU_create_sig with "OBLS") as "FOO". *)
  (*     iApply (OU_wand with "[-FOO]"); [| by iFrame]. *)
  (*     iIntros "(%s' & SG & OBLS & %NEW)". rewrite union_empty_l_L. *)
  (*     iApply BMU_intro. iRight. iSplitR; [done| ]. *)
  (*     rewrite PeanoNat.Nat.min_r in DOM; [| lia]. *)
  (*     iMod (own_update with "SM") as "SM". *)
  (*     { apply auth_update_alloc. eapply (alloc_singleton_local_update _ (m + 2) (to_agree s')). *)
  (*       2: done.  *)
  (*       apply not_elem_of_dom. rewrite dom_fmap. rewrite DOM. *)
  (*       intros ?%elem_of_set_seq. lia. } *)
  (*     iModIntro. iDestruct "SM" as "[SM S']". *)
  (*     iExists s', lm'.  *)
  (*     iSplitL "SIGS SG SIG SM". *)
  (*     2: { iFrame. eauto. } *)
  (*     rewrite PeanoNat.Nat.min_r; [| lia]. rewrite /smap_repr_eo. *)
  (*     rewrite -fmap_insert. iFrame. iSplitR. *)
  (*     { iPureIntro. rewrite dom_insert_L DOM. *)
  (*       apply set_eq. intros ?. rewrite elem_of_union elem_of_singleton. *)
  (*       rewrite !elem_of_set_seq. lia. } *)
  (*     rewrite big_sepM_insert_delete. iSplitL "SG". *)
  (*     { iExists _. rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [ | lia]. *)
  (*       iFrame. iPureIntro. *)
  (*       Unshelve. *)
  (*       2: { assert (m + 2 < LIM) by lia.  *)
  (*            esplit. apply H1. } *)
  (*       done. } *)
  (*     rewrite (delete_notin _ (m + 2)). *)
  (*     2: { apply not_elem_of_dom. rewrite DOM. intros ?%elem_of_set_seq. lia. } *)
  (*     iApply (restore_map with "[$] [$]"); eauto. *)
  (*     rewrite DOM. f_equal. symmetry. lia. *)
  (*   Qed. *)

    Lemma ith_sig_expect i sw m τ π π__e smap R d B
      (PH_EXP: phase_le π__e π)
      (GE: m <= i)
      (UNSETi: B i = false):
      ⊢ ep sw π__e d (oGS := oGS) -∗ th_phase_ge τ π (oGS := oGS) -∗
         smap_repr B m smap -∗ ith_sig i sw -∗
         obls τ R (oGS := oGS) -∗ sgns_level_gt R (L i) (oGS := oGS) -∗ 
         OU (∃ π', cp π' d (oGS := oGS) ∗ smap_repr B m smap ∗ th_phase_ge τ π' (oGS := oGS) ∗ obls τ R (oGS := oGS) ∗ ⌜ phase_le π π' /\ phase_le π__e π' ⌝) (oGS := oGS).
    Proof using LEQUIV__l DISCR__l.
      iIntros "#EP PH SR #SW OBLS #OBLS_LT". 
      iDestruct (ith_sig_in with "[$] [$]") as "%ITH".
      iDestruct (smap_repr_split with "SW [$]") as "[SGw SR]".
      rewrite {1}/ex_ith_sig. rewrite UNSETi. 
      iDestruct (expect_sig_upd with "EP [$] [$] [$] [$]") as "OU"; [done| ..].
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "(%π' & CP1 & SIGW & OBLS & PH & [%PH_LE' %PH_LE''])".
      iExists _. iFrame. iSplitL; [| done].
      iApply "SR". rewrite /ex_ith_sig. by rewrite UNSETi.
    Qed.

    Lemma smap_expose_dom B m smap:
      ⊢ smap_repr B m smap -∗ ⌜ dom smap = set_seq 0 m ⌝.
    Proof using. by iIntros "(?&?&?)". Qed.

End SignalMap.

Section EoFin.
  Context (B: nat).
  Let LIM := B + 1. 
  Let MAX_OBL_STEPS := 10.
  Let NUM_DEG := 5.
  
  (* Instance EO_OP: ObligationsParams (EODegree NUM_DEG) (EOLevel LIM) (locale heap_lang) MAX_OBL_STEPS. *)
  Instance EO_OP': ObligationsParamsPre (EODegree NUM_DEG) (EOLevel LIM) MAX_OBL_STEPS.
  Proof using.
    esplit; try by apply _.
    - apply nat_bounded_PO. 
    - apply nat_bounded_PO. 
  Defined.
  Definition EO_OP := LocaleOP (Locale := locale heap_lang). 
  Existing Instance EO_OP. 

  Let OM := ObligationsModel.

  Let EOLevelOfe := BNOfe LIM. 
  Let EODegreeOfe := BNOfe NUM_DEG.

  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{hGS: @heapGS Σ _ EM}.

  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}. 
  
  Let thread_prog: val :=
    rec: "thread_prog" "l" "n" "M" :=
      if: ("M" ≤ "n")%V then #()
      else                           
        if: CAS "l" "n" ("n"+#1)
        then "thread_prog" "l" ("n" + #2) "M"
        else "thread_prog" "l" "n" "M"
  .

  Definition start: val :=
    λ: "i" "M",
      (let: "l" := Alloc "i" in
      (Fork (thread_prog "l" "i" "M" ) ;;
       Fork (thread_prog "l" ("i" + #1) "M")))
  .

  Class EoFinPreG Σ := {
      eofin_threads_PreG :> inG Σ (excl_authR natO);
      eofin_sigs :> SigMapPreG Σ;
        (* inG Σ (authUR (gmapUR nat (agreeR SignalId))); *)                 
  }.
  
  Class EoFinG Σ := {
      eofin_PreG :> EoFinPreG Σ;
      eofin_even: gname; eofin_odd: gname;
      (* eofin_smap: gname; *)
      eofin_sm :> SigMapG Σ;
  }.

  Definition lvl2nat {X} (l: EOLevel X) := bn2nat _ l. 

  Definition d0 := ith_bn NUM_DEG 0 ltac:(lia).
  Definition d1 := ith_bn NUM_DEG 1 ltac:(lia). 
  Definition d2 := ith_bn NUM_DEG 2 ltac:(lia). 
  Lemma d12_lt: strict (bounded_nat_le _) d1 d2.
  Proof using. apply ith_bn_lt. lia. Qed. 
  Lemma d01_lt: strict (bounded_nat_le _) d0 d1.
  Proof using. apply ith_bn_lt. lia. Qed.
  
  Ltac BMU_burn_cp :=
    iApply BMU_intro;
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]";
    iSplitR "CP";
    [| do 2 iExists _; iFrame; iPureIntro; done]. 
  
  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS _ EM _ (↑ nroot)}.
  
  Ltac MU_by_BMU :=
    iApply OBLS_AMU; [by rewrite nclose_nroot| ];
    iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH". 
  
  Ltac MU_by_burn_cp := MU_by_BMU; BMU_burn_cp.
  
  Ltac pure_step_hl := 
    iApply sswp_MU_wp; [done| ];
    iApply sswp_pure_step; [done| ]; simpl;
    iNext.
  
  Ltac pure_step := pure_step_hl; MU_by_burn_cp.   
  Ltac pure_step_cases := pure_step || (iApply wp_value; []) || wp_bind (RecV _ _ _ _)%V.
  Ltac pure_steps := repeat (pure_step_cases; []).


  Section ThreadResources.
    Context {PRE: EoFinPreG Σ}.

    Definition thread_auth γ (n: nat): iProp Σ := own γ (●E n).
    Definition thread_frag γ (n: nat): iProp Σ := own γ (◯E n).

    Lemma thread_res_alloc n:
      ⊢ |==> ∃ γ, thread_auth γ n ∗ thread_frag γ n.
    Proof using.
      iMod (own_alloc (●E n ⋅  ◯E n)) as (?) "[A F]".
      { by apply auth_both_valid_2. }
      iExists _. by iFrame.
    Qed.       

    Lemma thread_agree γ n1 n2:
      thread_auth γ n1-∗ thread_frag γ n2 -∗ ⌜ n1 = n2 ⌝. 
    Proof using.
      rewrite /thread_frag /thread_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".      
      iDestruct (own_valid with "H") as "%Hval".
      iPureIntro. apply excl_auth_agree_L in Hval. set_solver. 
    Qed.

    Lemma thread_update γ n1 n2 n':
      thread_auth γ n1 -∗ thread_frag γ n2 ==∗
      thread_auth γ n' ∗ thread_frag γ n'. 
    Proof using.
      rewrite /thread_frag /thread_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".
      rewrite -!own_op. iApply own_update; [| by iFrame].
      apply excl_auth_update.
    Qed.

  End ThreadResources.

  Section Threads.
    Context `{EoFinG Σ}.
    
    Definition threads_auth n: iProp Σ := 
      thread_auth eofin_even (if Nat.even n then n else n + 1) ∗
      thread_auth eofin_odd (if Nat.odd n then n else n + 1).

    Definition B__eo (i: nat): EOLevel LIM :=
      match (le_lt_dec LIM i) with
      | left GE => ith_bn LIM 0 ltac:(lia)                                      
      | right LT => ith_bn LIM i LT
      end.

    Definition smap_repr_eo n := smap_repr B__eo (flip Nat.ltb n) (oGS := oGS). 

    Definition eofin_inv_inner l: iProp Σ :=
      ∃ (n: nat) (smap: gmap nat SignalId), 
          l ↦ #n ∗ threads_auth n ∗ smap_repr_eo n (min B (n + 2)) smap.

    Definition eofin_inv l: iProp Σ :=
      inv (nroot .@ "eofin") (eofin_inv_inner l).

    (* Lemma restore_map (smap: gmap nat SignalId) (s : SignalId) (m : nat) lm *)
    (*   (DOM: dom smap = set_seq 0 (B `min` (m + 2))) *)
    (*   (IN: smap !! m = Some s) *)
    (*   (LVL: lvl2nat lm = m) *)
    (*   : *)
    (*   ⊢ (([∗ map] k↦y ∈ delete m smap, *)
    (*        ∃ l0, sgn y l0 (Some (k <? m)) (oGS := oGS) ∗ ⌜lvl2nat l0 = k⌝) -∗ *)
    (*       sgn s lm (Some true) (oGS := oGS)-∗ *)
    (*       [∗ map] i↦s0 ∈ smap, *)
    (*        ∃ l0, sgn s0 l0 (Some (i <? m + 1)) (oGS := oGS) ∗ ⌜ lvl2nat l0 = i⌝)%I. *)
    (* Proof using. *)
    (*   iIntros "SIGS SG". *)
    (*   rewrite (big_sepM_delete _ smap); eauto. *)
    (*   iSplitL "SG". *)
    (*   { iExists _. rewrite (proj2 (Nat.ltb_lt _ _)); [| lia]. *)
    (*     iFrame. done. } *)
    (*   iApply (big_sepM_impl with "[$]"). iModIntro. *)
    (*   iIntros (???) "(%&?&?)". iExists _. iFrame. *)
    (*   apply lookup_delete_Some in H0 as [??]. *)
    (*   apply mk_is_Some, elem_of_dom in H1. *)
    (*   rewrite DOM in H1. apply elem_of_set_seq in H1. *)
    (*   assert ((k <? m) = (k <? m + 1) \/ k = m). *)
    (*   { destruct (decide (k = m)); [tauto| ]. left. *)
    (*     destruct (k <? m) eqn:LT. *)
    (*     - rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [done | ]. *)
    (*       apply PeanoNat.Nat.ltb_lt in LT. lia. *)
    (*     - rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [done | ]. *)
    (*       apply PeanoNat.Nat.ltb_ge in LT. lia. } *)
    (*   destruct H2; [| done]. rewrite H2. done. *)
    (* Qed. *)

    (* TODO: generalize, move *)
    Lemma lvl_lt_equiv (l1 l2: EOLevel LIM):
      lvl_lt l1 l2 <-> bn2nat _ l1 < bn2nat _ l2.
    Proof using.
      destruct l1, l2; simpl in *.
      rewrite /lvl_lt. rewrite strict_spec_alt. simpl.
      rewrite /bounded_nat_le. simpl. split.
      - intros [? ?]. apply PeanoNat.Nat.le_neq. split; auto.
        intros ->. destruct H1. f_equal. apply Nat.lt_pi.
      - intros ?. split; [lia| ]. intros ?. inversion H1. subst. lia.
    Qed.
    
    Record ThreadResource (th_res: nat -> iProp Σ) (cond: nat -> bool) := {
        tr_agree (n1 n2: nat): threads_auth n1-∗ th_res n2 -∗
                              ⌜ n2 = if (cond n1) then n1 else (n1 + 1)%nat ⌝;
        tr_update (n: nat) (Cn: cond n):
          threads_auth n-∗ th_res n ==∗ threads_auth (n + 1) ∗ th_res (n + 2);
        tr_cond_neg n: cond (S n) = negb (cond n); 
    }.

    Lemma lt_B_LIM: B < LIM. lia. Qed. 

    Lemma thread_spec_holds τ l (π π2: Phase) n
      (PH_LE2: phase_le π2 π)
      `(ThreadResource th_res cond)
      :
      {{{ eofin_inv l ∗ exc_lb 20 (oGS := oGS) ∗
           (* even_res n ∗ *)
           th_res n ∗
           cp_mul π2 d2 (B - n) (oGS := oGS) ∗
           cp_mul π d0 20 (oGS := oGS) ∗
           (cp π2 d2 (oGS := oGS) ∨ ∃ sw π__e, ith_sig (n - 1) sw ∗ ep sw π__e d1 (oGS := oGS) ∗ ⌜ phase_le π__e π ⌝) ∗
           th_phase_ge τ π (oGS := oGS) ∗
           (if n <? B
            then ∃ s, ith_sig n s ∗ obls τ {[s]} (oGS := oGS)
            else obls τ ∅ (oGS := oGS)) }}}
        thread_prog #l #n #B @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) }}}.       
    Proof using OBLS_AMU. 
      iIntros (Φ). iLöb as "IH" forall (π π2 n PH_LE2). 
      iIntros "(#INV & #EB & TH & CPS2 & CPS & EXTRA & PH & SN_OB) POST".
      rewrite {2}/thread_prog.
      
      pure_steps.
      wp_bind (_ ≤ _)%E. pure_step.

      fold thread_prog. 

      destruct (Nat.le_gt_cases B n).
      { rewrite bool_decide_true; [| lia].
        pure_steps. iApply "POST".
        rewrite (proj2 (Nat.ltb_ge _ _)); done. }
      
      rewrite bool_decide_false; [| lia].
      rewrite (proj2 (Nat.ltb_lt _ _)); [| done].
      iDestruct "SN_OB" as (s) "[#SN OB]". 
      pure_steps.
      wp_bind (_ + _)%E. pure_steps.

      wp_bind (CmpXchg _ _ _)%E.
      iApply wp_atomic. 
      iInv "INV" as ">inv" "CLOS". iModIntro. 
      rewrite {1}/eofin_inv_inner.
      iDestruct "inv" as (m smap) "(L & AUTH & SR)".
      iDestruct (tr_agree with "[$] TH") as %EQ; eauto. subst n. 
      destruct (cond m) eqn:Cm. 
      - 
        iClear "EXTRA". 
        
        iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_suc with "[$]"); try done.
        { econstructor. done. }
        iNext. iIntros "L".
        
        (* iDestruct (ith_sig_in with "[$] [$]") as %IN. *)
        (* iDestruct "SR" as "(SM & %DOM & SIGS)". *)
        
        (* iDestruct (big_sepM_delete with "SIGS") as "[SG SIGS]"; eauto. *)
        (* iDestruct "SG" as (lm) "(SG & %LVL)". *)
        iDestruct (smap_expose_dom with "[$]") as "%SM_DOM". 
        rewrite /smap_repr_eo. 
        
        iPoseProof (smap_repr_split_upd B__eo _ (flip Nat.ltb (m + 1)) with "[$] [$]") as "[SG SR_CLOS]".
        { intros ?. rewrite SM_DOM elem_of_set_seq. simpl.
          intros NEQ [? [??]%Nat.min_glb_lt_iff].
          assert (j < m \/ j = m + 1) as [? | ->] by lia.
          - rewrite !(proj2 (PeanoNat.Nat.ltb_lt _ _)); lia.
          - rewrite !(proj2 (PeanoNat.Nat.ltb_ge _ _)); lia. }        
        
        MU_by_BMU. iApply OU_BMU.
        iDestruct (OU_set_sig with "OB [SG]") as "OU".
        { apply elem_of_singleton. reflexivity. }
        { rewrite /ex_ith_sig. simpl. rewrite Nat.ltb_irrefl. iFrame. }
        iApply (OU_wand with "[-OU]"); [| done]. iIntros "(SIG & OBLS)".
        rewrite (subseteq_empty_difference_L {[ s ]}); [| done].
        
        (* iPoseProof (BMU_smap_restore with "OBLS [$] [$] [$]") as "BMU"; eauto. *)
        iSpecialize ("SR_CLOS" with "[SIG]").
        { rewrite /ex_ith_sig. simpl.
          rewrite !(proj2 (PeanoNat.Nat.ltb_lt _ _)); [iFrame | lia]. }
        iApply (BMU_lower _ 1); [lia| ].
        Unshelve. 2: by apply _.
        (* iApply (BMU_wand with "[-BMU] [$]"). iIntros "COND". *)
        iApply BMU_intro. 
        iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
        iSplitR "CP".
        2: { do 2 iExists _. iFrame. done. }
        iApply wp_value.
        
        iMod (tr_update with "[$] TH") as "[AUTH TH]"; eauto. 

        destruct (Nat.le_gt_cases B (m + 2)). 
        + iDestruct "COND" as "[COND | CC]".
          2: { iMod "CC" as "[% ?]". lia. }
          iDestruct "COND" as "(% & OBLS & SM)".
          
          iMod ("CLOS" with "[AUTH SM L]") as "?".
          { rewrite /eofin_inv_inner. iNext. iExists (m + 1), smap.
            (* rewrite even_plus1_negb odd_plus1_negb E -O. simpl.  *)
            rewrite -Nat.add_assoc. rewrite Nat2Z.inj_add. 
            iFrame.
            rewrite Nat.min_l; [| done]. rewrite Nat.min_l; [| lia]. done. }
          
          iModIntro.
          wp_bind (Snd _)%E.           
          pure_steps.
          
          wp_bind (_ + _)%E. pure_step. iApply wp_value.
          
          replace (Z.add (Z.of_nat m) 2) with (Z.of_nat (m + 2)) by lia.

          (* TODO: refine the precondition and do this early in the proof *)
          iClear "IH". rewrite /thread_prog.
          pure_steps.
          wp_bind (_ ≤ _)%E. pure_step.
          rewrite bool_decide_true; [| lia].
          pure_steps. by iApply "POST". 
        + iDestruct "COND" as "[CC | COND]".
          { iDestruct "CC" as "(% & ? & ?)". lia. }
          iClear "SN".  
          iMod "COND" as "[% (%s' & %lm' & SM & SN & OBLS & %LVL')]". 
          iMod ("CLOS" with "[AUTH SM L]") as "?".
          { rewrite /eofin_inv_inner. iNext. iExists (m + 1), _.
            (* rewrite even_plus1_negb odd_plus1_negb E -O. simpl.  *)
            rewrite -Nat.add_assoc. rewrite Nat2Z.inj_add. 
            iFrame. }
          
          iModIntro.
          wp_bind (Snd _)%E.           
          pure_steps.
          
          wp_bind (_ + _)%E.

          red in H2. apply Nat.le_sum in H2 as [? LE].
          rewrite {4}LE.
          rewrite -plus_n_Sm. 
          rewrite !plus_Sn_m. rewrite !PeanoNat.Nat.sub_succ_l; try lia.
          iDestruct (cp_mul_take with "CPS2") as "[CPS2 CP2']".
          iDestruct (cp_mul_take with "CPS2") as "[CPS2 CP2'']".
          replace (B - S (m + 1)) with (m + 1 + x - m) by lia.

          pure_step_hl. 
          MU_by_BMU. iApply OU_BMU.
          iDestruct (exchange_cp_upd with "CP2'' [PH] [$]") as "OU".
          { reflexivity. }
          { etrans; [apply d01_lt| apply d12_lt]. }
          { by rewrite <- PH_LE2. } 
          iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "[CPS' PH]".
          BMU_burn_cp.

          iApply wp_value.
          
          replace (Z.add (Z.of_nat m) 2) with (Z.of_nat (m + 2)) by lia. 
          iApply ("IH" with "[] [-POST]"); [..| by iFrame].
          { iPureIntro. reflexivity. } 
          rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
          
          iFrame "#∗".
          replace (B - (m + 2)) with (m + 1 + x - m) by lia.
          replace (m + 2) with (S (m + 1)) by lia.
          iFrame. 
          iExists _. iFrame. 
      - 

        iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_fail with "[$]"); try done.
        { intros [=]. lia. }
        { econstructor. done. }
        iNext. iIntros "L".

        assert (B - (m + 1) = S (B - (m + 2))) as LE by lia. 
        rewrite LE.

        iDestruct "EXTRA" as "[CP2' | EXP]". 
        + MU_by_BMU. 
          (* TODO: avoid unfolding BMU *)
          iMod (smap_create_ep m with "[$] [$] [$]") as "OU"; eauto.
          { lia. }
          iApply OU_BMU.
          iApply (OU_wand with "[-OU]"); [| done]. iIntros "(%sw & #SW & #EP & SR & PH)".
          (* rewrite -E in H0. *)
          rewrite Nat.min_r; [| lia].
          
          iDestruct (ith_sig_expect with "[$] [$] [$] [$] [$] [$]") as "OU".
          { done. }
          { reflexivity. }
          iApply OU_BMU.
          iApply (OU_wand with "[-OU]"); [| done].
          iIntros "(%π' & CP1 & SR & PH & OBLS & [%PH_LE' %])".

          iApply OU_BMU.
          iDestruct (exchange_cp_upd with "[$] [$] [$]") as "OU".
          { reflexivity. }
          { apply d01_lt. }
          iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "[CPS' PH]".
          BMU_burn_cp.
 
          iApply wp_value.

          iMod ("CLOS" with "[AUTH SR L]") as "?".
          { rewrite /eofin_inv_inner. iNext. iExists m, smap.
            rewrite Nat.min_r; [| lia]. iFrame. }
          iModIntro.
          wp_bind (Snd _)%E.

          pure_step_hl.
          MU_by_BMU. BMU_burn_cp.
          
          do 2 pure_step_cases. 
          iApply ("IH" $! π' π2 with "[] [-POST]"); [..| by iFrame]. 
          { iPureIntro. etrans; [apply PH_LE2 | apply PH_LE']. }
          replace (B - (m + 1)) with (S (B - (m + 2))) by lia. 
          iFrame "#∗". 
          iSplitR "OBLS".
          2: { rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
               iExists _. iFrame "#∗". }
          iRight. rewrite Nat.add_sub.
          do 2 iExists _. iFrame "#∗". done.
        + MU_by_BMU. 
          iDestruct "EXP" as "(%sw & %π__e & #SW & #EP & %PH_EXP)".
          rewrite Nat.add_sub.
          iDestruct (ith_sig_expect with "[$] [$] [$] [$] [$] [$]") as "OU".
          { apply PH_EXP. }
          { reflexivity. }
          iApply OU_BMU.
          iApply (OU_wand with "[-OU]"); [| done].
          iIntros "(%π' & CP1 & SR & PH & OBLS & [%PH_LE' %PH_LE''])".

          iApply OU_BMU.
          iDestruct (exchange_cp_upd with "[$] [$] [$]") as "OU". 
          { reflexivity. }
          { apply d01_lt. }
          iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "[CPS' PH]".
          BMU_burn_cp.
 
          iApply wp_value.

          iMod ("CLOS" with "[AUTH SR L]") as "?".
          { rewrite /eofin_inv_inner. iNext. iExists m, smap.
            rewrite Nat.min_r; [| lia]. iFrame. }
          iModIntro.
          wp_bind (Snd _)%E.
          do 3 pure_step_cases. 
          iApply ("IH" $! π' with "[] [-POST]"); [..| by iFrame]. 
          { iPureIntro. etrans; [apply PH_LE2 | apply PH_LE']. }
          replace (B - (m + 1)) with (S (B - (m + 2))) by lia. 
          iFrame "#∗". 
          iSplitR "OBLS".
          2: { rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
               iExists _. iFrame "#∗". }
          iRight. rewrite Nat.add_sub.
          do 2 iExists _. iFrame "#∗". done.
    Time Qed. 

    Lemma thread_spec_wrapper τ l (π π2: Phase) n
      (PH_LE2: phase_le π2 π)
      `(ThreadResource th_res cond)

      :
      {{{ eofin_inv l ∗ exc_lb 20 (oGS := oGS) ∗
           th_res n ∗
           cp_mul π2 d2 (S (B - n)) (oGS := oGS) ∗
           cp_mul π d0 20 (oGS := oGS) ∗           
           th_phase_ge τ π (oGS := oGS) ∗
           (if n <? B
            then ∃ s, ith_sig n s ∗ obls τ {[s]} (oGS := oGS)
            else obls τ ∅ (oGS := oGS)) }}}
        thread_prog #l #n #B @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) }}}.       
    Proof using OBLS_AMU.
      iIntros (Φ). iIntros "(#INV & #EB & TH & CPS2 & CPS & PH & SN_OB) POST".
      iDestruct (cp_mul_take with "CPS2") as "[??]".
      iApply (thread_spec_holds with "[-POST] [$]"); eauto.
      iFrame "#∗".
    Qed. 

    Definition even_res n: iProp Σ := thread_frag eofin_even n.
    Definition odd_res n: iProp Σ := thread_frag eofin_odd n.

    Lemma even_thread_resource: ThreadResource even_res Nat.even.
    Proof using.
      split.
      - iIntros (??) "[E ?] TH".
        by iDestruct (thread_agree with "E TH") as "%".
      - iIntros (??) "[E ?] TH".        
        iMod (thread_update with "E TH") as "[E TH]". iFrame.
        apply Is_true_true_1 in Cn. rewrite -Nat.negb_even Cn. simpl.
        iModIntro. rewrite /threads_auth.
        rewrite -Nat.negb_even !Nat.even_add Cn. simpl.
        rewrite -Nat.add_assoc. iFrame.
      - intros. by rewrite even_succ_negb.
    Qed.

    Lemma odd_thread_resource: ThreadResource odd_res Nat.odd.
    Proof using.
      split.
      - iIntros (??) "[? O] TH".
        by iDestruct (thread_agree with "O TH") as "%".
      - iIntros (??) "[? O] TH".        
        iMod (thread_update with "O TH") as "[O TH]". iFrame.
        apply Is_true_true_1 in Cn. rewrite -Nat.negb_odd Cn. simpl.
        iModIntro. rewrite /threads_auth.
        rewrite -Nat.negb_odd !Nat.odd_add Cn. simpl.
        rewrite -Nat.add_assoc. iFrame.
      - intros. by rewrite odd_succ_negb.
    Qed.    

  End Threads.

  Section MainProof.
    Context {PRE: EoFinPreG Σ}.

    (* TODO: move *)
    Lemma map_nat_agree_valid {A: ofe} (m: gmap nat A):
      ✓ ((to_agree <$> m): gmapUR nat (agreeR A)).
    Proof using.
      red. intros k.
      destruct lookup eqn:L; [| done].
      apply lookup_fmap_Some in L. 
      destruct L as (a&<-&?). 
      done.
    Qed.

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

    (* TODO: parametrize smap_repr_eo with the lower bound *)
    Lemma alloc_inv l (* (i: nat) *) τ
      (* (i := 0) *)
      :
      obls τ ∅ (oGS := oGS) -∗ l ↦ #0 -∗ 
        BMU ⊤ 2 (|={∅}=> ∃ (eoG: EoFinG Σ) (sigs: list SignalId),
                       even_res 0 (H := eoG)∗
                       odd_res 1 (H := eoG) ∗
                       eofin_inv l (H := eoG) ∗
                       obls τ (list_to_set sigs) (oGS := oGS) ∗
                       ⌜ length sigs = min B 2 ⌝ ∗
                       ⌜ NoDup sigs ⌝ ∗
                       ([∗ list] k ↦ s ∈ sigs, ith_sig k s)
        ) (oGS := oGS).
    Proof using OBLS_AMU PRE.
      iIntros "OB L".
      iMod (thread_res_alloc 0) as "(%γ & AUTH & FRAG)".
      iMod (thread_res_alloc 1) as "(%γ' & AUTH' & FRAG')".
      
      set (m := min B 2).
      iAssert (BMU ⊤ 2 
                 (|==> ∃ γ smap, smap_repr_eo' γ m 0 smap ∗
                                 (* let sigs := map_img smap in *)
                                 let sigs := sigs_block smap 0 m in
                                 obls τ (list_to_set sigs) (oGS := oGS) ∗
                                 (* ⌜ size sigs = m ⌝ ∗ *)
                                  ⌜ NoDup sigs ⌝ ∗ 
                                 own γ (◯ ((to_agree <$> smap): gmapUR nat _))
              ))%I with "[OB]" as "-#SR".
      {
        
        assert (m <= 0 \/ m = 0 + 1 \/ m = 0 + 2) as [LE | [EQ | EQ]] by lia; revgoals.
        - iApply OU_BMU.
          assert (0 < LIM) as Di by lia. 
          unshelve iDestruct (OU_create_sig with "[$]") as "OU".
          { eexists. apply Di. }
          iApply (OU_wand with "[-OU] [$]"). iIntros "(%si & SGi & OBLS & _)". 

          iApply OU_BMU.
          assert (0 + 1 < LIM) as Di' by lia. 
          unshelve iDestruct (OU_create_sig with "[$]") as "OU".
          { eexists. apply Di'. }
          iApply (OU_wand with "[-OU] [$]"). iIntros "(%si' & SGi' & OBLS & %NEW)".

          iApply BMU_intro.
          set (smap0 := {[ 0 := si; 0 + 1 := si']}: gmap nat SignalId).
          iMod (own_alloc (● ((to_agree <$> smap0): gmapUR nat (agreeR SignalId)) ⋅ ◯ _)) as (?) "[A F]".
          { apply auth_both_valid_2; [| reflexivity]. apply map_nat_agree_valid. }
          iModIntro. iExists _, _. iFrame. 
          replace (sigs_block smap0 0 m) with ([ si; si' ]).
          2: { subst smap0 m. rewrite EQ. rewrite /sigs_block. simpl. done. } 

          rewrite !bi.sep_assoc. iSplitL.
          2: { iPureIntro. econstructor; try set_solver. apply NoDup_singleton. }
          
          iSplitR "OBLS".
          2: { iApply obls_proper; [| by iFrame]. set_solver. }

          iSplitR.
          { subst smap0. iPureIntro. rewrite !dom_insert_L.
            subst m.
            (* subst i.  *)
            rewrite EQ. simpl. set_solver. }
          subst smap0. rewrite !big_sepM_insert; try set_solver.
          rewrite big_sepM_empty. rewrite /ex_ith_sig.
          rewrite bi.sep_assoc. iSplitL; [| done]. iSplitL "SGi".
          + iExists _. rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
            iFrame. done. 
          + iExists _. rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
            iFrame. done.
        - iApply OU_BMU.
          assert (0 < LIM) as Di by lia. 
          unshelve iDestruct (OU_create_sig with "[$]") as "OU".
          { eexists. apply Di. }
          iApply (OU_wand with "[-OU] [$]"). iIntros "(%si & SGi & OBLS & _)".

          iApply BMU_intro.
          set (smap0 := {[ 0 := si]}: gmap nat SignalId).
          iMod (own_alloc (● ((to_agree <$> smap0): gmapUR nat (agreeR SignalId)) ⋅ ◯ _)) as (?) "[A F]".
          { apply auth_both_valid_2; [| reflexivity]. apply map_nat_agree_valid. }
          iModIntro. iExists _, _. iFrame.
          replace (sigs_block smap0 0 m) with [si].
          2: { subst smap0 m. rewrite EQ. rewrite /sigs_block. simpl. done. }
          iSplitR "OBLS".
          2: { iSplitL; [| iPureIntro; by apply NoDup_singleton]. 
               iApply obls_proper; [| by iFrame]. set_solver. }

          iSplitR.
          { subst smap0. iPureIntro. rewrite !dom_insert_L.
            subst m. (* subst i.  *)
            rewrite EQ. simpl. set_solver. }
          subst smap0. rewrite !big_sepM_insert; try set_solver.
          rewrite big_sepM_empty. rewrite /ex_ith_sig.
          iSplitL; [| done].
          iExists _. rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
          iFrame. done.
        - iApply BMU_intro.
          set (smap0 := ∅: gmap nat SignalId).
          iMod (own_alloc (● ((to_agree <$> smap0): gmapUR nat (agreeR SignalId)) ⋅ ◯ _)) as (?) "[A F]".
          { apply auth_both_valid_2; [| reflexivity]. apply map_nat_agree_valid. }
          iModIntro. iExists _, _. iFrame.
          assert (B = 0) by lia. simpl.  
          replace (sigs_block smap0 0 m) with (nil: list SignalId).
          2: { subst smap0 m. simpl. rewrite H. done. }

          iSplitR "OB".
          2: { iFrame. iPureIntro; constructor. }
          rewrite /smap_repr_eo'. iFrame.
          iSplitR.
          { subst smap0. iPureIntro. 
            subst m. (* subst i. *)
            rewrite H. set_solver. }
          subst smap0. rewrite big_sepM_empty. done. }

      iApply (BMU_wand with "[-SR] [$]"). 
      iIntros "X". iMod "X" as "(%γ__sr & %smap & SR & OB & %SIZE & #F)".
      
      set (eoG := {| 
          (* eofin_even := (if Nat.even i then γ else γ'); *)
          (* eofin_odd := (if Nat.even i then γ' else γ); *)
          eofin_even := (if Nat.even 0 then γ else γ');
          eofin_odd := (if Nat.even 0 then γ' else γ);
          eofin_smap := γ__sr
      |}).
      
      iExists eoG, _. iFrame.
      iApply fupd_frame_r.
      iSplit. 
      { iApply inv_alloc. iNext. 
        rewrite /eofin_inv_inner. iExists 0, smap. iFrame. }
      rewrite bi.sep_assoc. iSplit.
      { iPureIntro. split; try done. apply sigs_block_len. } 
      iDestruct "SR" as "(?&%DOM&SIGS)".
      iApply big_sepL_forall. iIntros (k s IN).
      pose proof IN as DOMk%mk_is_Some%sigs_block_is_Some.
      rewrite sigs_block_lookup_eq in IN; try done.
      2: { simpl. rewrite DOM. apply elem_of_set_seq. lia. }
      simpl in IN.       
      rewrite /ith_sig.
      iApply (own_mono with "F").
      apply auth_frag_mono.
      apply singleton_included_l. eexists.
      rewrite lookup_fmap IN. simpl. split; [reflexivity| ]. done.
    Qed.

    Close Scope Z. 

    Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS _ EM _ ⊤}.
    Context {NO_OBS_POST: ∀ τ v, obls τ ∅ (oGS := oGS) -∗ fork_post τ v}. 

    Theorem main_spec τ π
      :
      {{{ exc_lb 20 (oGS := oGS) ∗
           cp_mul π d2 (S (2 * (S B))) (oGS := oGS) ∗
           cp_mul π d0 40 (oGS := oGS) ∗
           th_phase_ge τ π (oGS := oGS) ∗
           obls τ ∅ (oGS := oGS) }}}
      start #(0%nat) #B @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) }}}.
    Proof using PRE OBLS_AMU__f OBLS_AMU NO_OBS_POST.
      iIntros (Φ). iIntros "(#EB & CPS2 & CPS_FORK & PH & OB) POST". rewrite /start.
      iDestruct (cp_mul_take with "CPS2") as "[CPS2 CP]". 

      wp_bind (RecV _ _ _ _)%V.
      pure_step_hl.
      MU_by_BMU.
      iApply OU_BMU.
      iDestruct (exchange_cp_upd with "[$] [$] [$]") as "OU". 
      { reflexivity. }
      { etrans; [apply d01_lt| apply d12_lt]. }
      iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "[CPS PH]".
      BMU_burn_cp.
      
      pure_steps.
      wp_bind (ref _)%E.
      (* iApply wp_atomic.       *)
      iApply sswp_MU_wp_fupd; [done| ]. iApply wp_alloc.
      iModIntro.
      iNext. iIntros "%l L _".
      iPoseProof (alloc_inv _ _  with "[$] [$]") as "BMU". 
      MU_by_BMU. iApply (BMU_weaken with "[-BMU] [$]"); [lia| done| ]. iIntros "INV".
      (* TODO: make a tactic, remove duplication *)
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iSplitR "CP".
      2: { do 2 iExists _. iFrame. done. }
      iApply wp_value.
      iApply fupd_mask_mono; [apply empty_subseteq| ].
      iMod "INV" as "(% & %sigs & RE & RO & #INV & OB & %SIGS_LEN & %SIGS_UNIQ & #SIGS)".
      clear PRE. 
      iModIntro.

      wp_bind (Rec _ _ _)%V. pure_steps.

      (* iAssert (∃ γ γ', thread_frag γ i ∗ thread_frag γ' (i + 1))%I with "[RE RO]" as "(%γ & %γ' & RES & RES')". *)
      (* { destruct (Nat.even i); do 2 iExists _; iFrame. } *)

      rewrite Nat.add_0_r.
      rewrite -Nat.add_succ_l. iDestruct (cp_mul_split with "CPS2") as "[CPS2 CPS2']".
      replace 40 with (20 + 20) by lia. iDestruct (cp_mul_split with "CPS_FORK") as "[CPS_FORK CPS_FORK']". 
      wp_bind (Fork _)%E. 

      assert (B = 0 \/ B = 1 \/ 2 <= B) as [B0 | [B1 | LE2]] by lia; revgoals.
      - rewrite Nat.min_r in SIGS_LEN; [| done].
        destruct sigs as [| si [| si' [|]]]; try by (simpl in SIGS_LEN; lia).

        rewrite !big_sepL_cons. simpl. rewrite union_empty_r_L.  
        iDestruct "SIGS" as "(ITH & ITH' & _)". 

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[-CP PH OB]").
        2: { iApply OBLS_AMU__f; [done| ]. 
             iApply (BMU_AMU__f with "[-PH]"); [reflexivity| ..].
             2: by iFrame. 
             
             iIntros "PH".
             (* TODO: change BMU_burn_cp*)
             iApply BMU_intro. iFrame "PH OB".
             iSplitR "CP".
             2: { do 2 iExists _. iFrame. done. }
             iAccu. }

        iIntros "[? (%π1 & %π2 & PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])]".
        Unshelve. 2: exact {[ si ]}.
        assert (si ≠ si') as NEQ.
        { intros <-. apply NoDup_cons in SIGS_UNIQ. set_solver. }
        replace (({[si; si']} ∖ {[si]})) with ({[si']}: gset _) by set_solver.
        replace ({[si; si']} ∩ {[si]}) with ({[si]}: gset _) by set_solver.
        iSplitL "RE CPS2 CPS_FORK PH3 OB2".
        { iApply (thread_spec_wrapper with "[-]").
          { reflexivity. }
          { apply even_thread_resource. }
          2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
          rewrite Nat.sub_0_r. iFrame "CPS2". iFrame "#∗".
          iSplitL "PH3".
          { apply strict_include in LT2. by erewrite <- LT2. }
          rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
          iExists _. by iFrame. }

        apply strict_include in LT1. iRename "PH1" into "PH".
        wp_bind (Rec _ _ _)%V. pure_step.
        iApply wp_value. pure_step.

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ''). iApply (MU__f_wand with "[-CP PH OB1]").
        2: { iApply OBLS_AMU__f; [done| ]. 
             iApply (BMU_AMU__f with "[-PH]"); [reflexivity| ..].
             2: by iFrame. 
             
             iIntros "PH".
             (* TODO: change BMU_burn_cp*)
             iApply BMU_intro. iFrame "PH OB1".
             iSplitR "CP".
             2: { do 2 iExists _. iFrame. done. }
             iAccu. }

        iIntros "[? (%π3 & %π4 & PH1 & OB1 & PH3 & OB2 & [%LT3 %LT4])]".
        Unshelve. 2: exact {[ si' ]}.        
        rewrite difference_diag_L. rewrite intersection_idemp_L.

        iSplitR "POST OB1".
        2: { by iApply "POST". }
        
        apply strict_include in LT4. iRename "PH3" into "PH".
        wp_bind (_ + _)%E. rewrite Nat2Z.inj_0.
        assert (phase_le π π4) as LT' by (by etrans). 
        do 2 pure_step_cases.
        replace (0 + 1)%Z with 1%Z; [| done].
        replace 1%Z with (Z.of_nat 1%nat); [| done].         
        iApply (thread_spec_wrapper with "[-]").
        { reflexivity. }
        { apply odd_thread_resource. }
        2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
        rewrite -PeanoNat.Nat.sub_succ_l; [| lia]. simpl. rewrite Nat.sub_0_r.
        iDestruct (cp_mul_take with "CPS2'") as "[CPS2 ?]". 
        iFrame "CPS2". iFrame "#∗".
        Unshelve. 2: exact #(). 
        iSplitL "PH".
        { by erewrite <- LT'. }
        rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
        iExists _. by iFrame.
      - 
        simpl in SIGS_LEN. 
        destruct sigs as [| si [|]]; try by (simpl in SIGS_LEN; lia).

        rewrite !big_sepL_cons. simpl. rewrite union_empty_r_L.  
        iDestruct "SIGS" as "(ITH & _)". 

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[-CP PH OB]").
        2: { iApply OBLS_AMU__f; [done| ]. 
             iApply (BMU_AMU__f with "[-PH]"); [reflexivity| ..].
             2: by iFrame. 
             
             iIntros "PH".
             (* TODO: change BMU_burn_cp*)
             iApply BMU_intro. iFrame "PH OB".
             iSplitR "CP".
             2: { do 2 iExists _. iFrame. done. }
             iAccu. }

        iIntros "[? (%π1 & %π2 & PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])]".
        Unshelve. 2: exact {[ si ]}.

        rewrite difference_diag_L. rewrite intersection_idemp_L.
        iSplitL "RE CPS2 CPS_FORK PH3 OB2".
        { iApply (thread_spec_wrapper with "[-]").
          { reflexivity. }
          { apply even_thread_resource. }
          2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
          rewrite Nat.sub_0_r. iFrame "CPS2". iFrame "#∗".
          iSplitL "PH3".
          { apply strict_include in LT2. by erewrite <- LT2. }
          rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
          iExists _. by iFrame. }

        apply strict_include in LT1. iRename "PH1" into "PH".
        wp_bind (Rec _ _ _)%V. pure_step.
        iApply wp_value. pure_step.

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ''). iApply (MU__f_wand with "[-CP PH OB1]").
        2: { iApply OBLS_AMU__f; [done| ]. 
             iApply (BMU_AMU__f with "[-PH]"); [reflexivity| ..].
             2: by iFrame. 
             
             iIntros "PH".
             (* TODO: change BMU_burn_cp*)
             iApply BMU_intro. iFrame "PH OB1".
             iSplitR "CP".
             2: { do 2 iExists _. iFrame. done. }
             iAccu. }

        iIntros "[? (%π3 & %π4 & PH1 & OB1 & PH3 & OB2 & [%LT3 %LT4])]".
        Unshelve. 2: exact ∅.
        rewrite difference_diag_L. rewrite intersection_idemp_L.

        iSplitR "POST OB1".
        2: { by iApply "POST". }
        
        apply strict_include in LT4. iRename "PH3" into "PH".
        wp_bind (_ + _)%E. rewrite Nat2Z.inj_0.
        assert (phase_le π π4) as LT' by (by etrans). 
        do 2 pure_step_cases.
        replace (0 + 1)%Z with 1%Z; [| done].
        replace 1%Z with (Z.of_nat 1%nat); [| done].         
        iApply (thread_spec_wrapper with "[-]").
        { reflexivity. }
        { apply odd_thread_resource. }
        2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
        simpl. 
        iDestruct (cp_mul_take with "CPS2'") as "[CPS2 ?]".
        rewrite {1 3}B1. simpl.
        rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
        iFrame "CPS2". iFrame "#∗".
        by erewrite <- LT'.
        Unshelve. exact #(). 
      - simpl in SIGS_LEN. 
        destruct sigs as [| ]; try by (simpl in SIGS_LEN; lia).

        simpl. 

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[-CP PH OB]").
        2: { iApply OBLS_AMU__f; [done| ]. 
             iApply (BMU_AMU__f with "[-PH]"); [reflexivity| ..].
             2: by iFrame. 
             
             iIntros "PH".
             (* TODO: change BMU_burn_cp*)
             iApply BMU_intro. iFrame "PH OB".
             iSplitR "CP".
             2: { do 2 iExists _. iFrame. done. }
             iAccu. }

        iIntros "[? (%π1 & %π2 & PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])]".
        Unshelve. 2: exact ∅.


        rewrite difference_diag_L. rewrite intersection_idemp_L.
        iSplitL "RE CPS2 CPS_FORK PH3 OB2".
        { iApply (thread_spec_wrapper with "[-]").
          { reflexivity. }
          { apply even_thread_resource. }
          2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
          rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
          rewrite Nat.sub_0_r. iFrame "CPS2". iFrame "#∗".
          apply strict_include in LT2. by erewrite <- LT2. }

        apply strict_include in LT1. iRename "PH1" into "PH".
        wp_bind (Rec _ _ _)%V. pure_step.
        iApply wp_value. pure_step.

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ''). iApply (MU__f_wand with "[-CP PH OB1]").
        2: { iApply OBLS_AMU__f; [done| ]. 
             iApply (BMU_AMU__f with "[-PH]"); [reflexivity| ..].
             2: by iFrame. 
             
             iIntros "PH".
             (* TODO: change BMU_burn_cp*)
             iApply BMU_intro. iFrame "PH OB1".
             iSplitR "CP".
             2: { do 2 iExists _. iFrame. done. }
             iAccu. }

        iIntros "[? (%π3 & %π4 & PH1 & OB1 & PH3 & OB2 & [%LT3 %LT4])]".
        Unshelve. 2: exact ∅.
        rewrite difference_diag_L. rewrite intersection_idemp_L.

        iSplitR "POST OB1".
        2: { by iApply "POST". }
        
        apply strict_include in LT4. iRename "PH3" into "PH".
        wp_bind (_ + _)%E. rewrite Nat2Z.inj_0.
        assert (phase_le π π4) as LT' by (by etrans). 
        do 2 pure_step_cases.
        replace (0 + 1)%Z with 1%Z; [| done].
        replace 1%Z with (Z.of_nat 1%nat); [| done].         
        replace 0%Z with (Z.of_nat 0%nat); [| done].         
        iApply (thread_spec_wrapper with "[-]").
        { reflexivity. }
        { apply odd_thread_resource. }
        2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
        simpl. 
        (* iDestruct (cp_mul_take with "CPS2'") as "[CPS2 ?]".  *)        
        rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
        rewrite {1 3}B0. simpl.  
        iFrame "CPS2'". iFrame "#∗".
        by erewrite <- LT'.
        Unshelve. exact #().
    Qed.
      
  End MainProof.

End EoFin.
