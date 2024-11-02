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


Section EoFin.
  Context (LIM: nat).
  Let MAX_OBL_STEPS := 10.
  Let NUM_DEG := 5.
  
  Instance EO_OP: ObligationsParams (EODegree NUM_DEG) (EOLevel LIM) (locale heap_lang) MAX_OBL_STEPS.
  Proof using.
    esplit; try by apply _.
    - apply nat_bounded_PO. 
    - apply nat_bounded_PO. 
  Defined.

  Let OM := ObligationsModel EO_OP.

  Let EOLevelOfe := BNOfe LIM. 
  Let EODegreeOfe := BNOfe NUM_DEG. 

  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{hGS: @heapGS Σ _ EM}.

  Let ASEM := ObligationsASEM EO_OP.
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
      eofin_sigs :> inG Σ (authUR (gmapUR nat (agreeR SignalId)));
  }.
  
  Class EoFinG Σ := {
      eofin_PreG :> EoFinPreG Σ;
      eofin_even: gname; eofin_odd: gname;
      eofin_smap: gname;
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

  Definition ex_ith_sig (n i: nat) (s: SignalId): iProp Σ :=
    ∃ l, sgn EO_OP s l (Some $ Nat.ltb i n) (H3 := oGS) ∗ ⌜ lvl2nat l = i ⌝. 
  
  Definition smap_repr' {PRE: EoFinPreG Σ} γ K n (smap: gmap nat SignalId): iProp Σ :=
    own γ (● (to_agree <$> smap: gmapUR nat (agreeR SignalId))) ∗
    ⌜ dom smap = set_seq 0 K ⌝ ∗
    ([∗ map] i ↦ s ∈ smap, ex_ith_sig n i s).

  Section Threads.
    Context `{EoFinG Σ}.

    Definition smap_repr := smap_repr' eofin_smap. 
    
    Definition threads_auth n: iProp Σ := 
      thread_auth eofin_even (if Nat.even n then n else n + 1) ∗
      thread_auth eofin_odd (if Nat.odd n then n else n + 1). 

    Definition eofin_inv_inner l M (BOUND: M < LIM) : iProp Σ :=
      ∃ (n: nat) (smap: gmap nat SignalId), 
          l ↦ #n ∗ threads_auth n ∗ smap_repr (min M (n + 2)) n smap.

    Definition eofin_inv l M BOUND: iProp Σ :=
      inv (nroot .@ "eofin") (eofin_inv_inner l M BOUND).

    Definition ith_sig (i: nat) (s: SignalId): iProp Σ :=
      own eofin_smap (◯ {[ i := to_agree s ]}).

    Definition ith_sig_in i s K n (smap: gmap nat SignalId):
      ⊢ ith_sig i s -∗ smap_repr K n smap -∗ ⌜ smap !! i = Some s ⌝.
    Proof.
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

      apply fmap_Some_equiv in ITH as (?&?&?).
      rewrite H1. apply to_agree_inj in H2. by rewrite H2.
    Qed.

    Definition ith_sig_sgn i s K n (smap: gmap nat SignalId):
      ⊢ ith_sig i s -∗ smap_repr K n smap -∗ ∃ l, sgn _ s l None (H3 := oGS) ∗ ⌜ lvl2nat l = i ⌝. 
    Proof.
      iIntros "S SR".
      iDestruct (ith_sig_in with "[$] [$]") as "%ITH". 
      iDestruct "SR" as "(SM & % & ?)".
      iDestruct (big_sepM_lookup with "[$]") as "ITH"; eauto.
      rewrite /ex_ith_sig. iDestruct "ITH" as "(%l & SG & %LVL)".
      iExists _. iSplitL; [| done].
      by iDestruct (sgn_get_ex with "[$]") as "[??]". 
    Qed.

    Lemma smap_repr_split K n smap i s:
      ⊢ ith_sig i s -∗ smap_repr K n smap -∗
         ex_ith_sig n i s ∗ (ex_ith_sig n i s -∗ smap_repr K n smap).
    Proof using.
      iIntros "#ITH SR".
      iDestruct (ith_sig_in with "[$] [$]") as "%ITH".
      rewrite /smap_repr /smap_repr'. iDestruct "SR" as "(SM & % & SR)".
      rewrite {2 5}(map_split smap i) ITH /=.
      rewrite !big_sepM_union.
      2: apply map_disjoint_singleton_l_2; by apply lookup_delete.
      iDestruct "SR" as "[S SR]". rewrite big_sepM_singleton.
      iFrame. iIntros. iFrame. done.
    Qed.

    (* TODO: use bupd in definition of OU *)
    Lemma smap_create_ep i K n smap π π__cp τ
      (PH_LE: phase_le π__cp π)
      (LT: i < K):
      ⊢ smap_repr K n smap -∗ 
         cp EO_OP π__cp d2 (H3 := oGS) -∗
         th_phase_ge EO_OP τ π (H3 := oGS) -∗
         |==> OU EO_OP τ
           (∃ s, ith_sig i s ∗
             ep EO_OP s π__cp d1 (H3 := oGS) ∗ smap_repr K n smap ∗
            th_phase_ge EO_OP τ π (H3 := oGS)) (H3 := oGS).
    Proof using.
      iIntros "SR CP PH".
      rewrite /smap_repr /smap_repr'. iDestruct "SR" as "(AUTH & %DOM & SIGS)".
      assert (i ∈ dom smap) as [s ITH]%elem_of_dom.
      { rewrite DOM. apply elem_of_set_seq. lia. }
      rewrite {2 5}(map_split smap i) ITH /=.
      setoid_rewrite big_sepM_union.
      2, 3: apply map_disjoint_singleton_l_2; by apply lookup_delete.
      iDestruct "SIGS" as "[SIG SIGS]". setoid_rewrite big_sepM_singleton.
      rewrite {1}/ex_ith_sig. iDestruct "SIG" as "(%l & SIG & %LVLi)".
      iDestruct (create_ep_upd with "[$] [$] [PH]") as "OU".
      { apply (ith_bn_lt _ 1). lia. }
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
      iExists _. iFrame. iSplitR; [done| ].
      iExists _. by iFrame.
    Qed.

    Lemma restore_map (smap: gmap nat SignalId) (s : SignalId) (m : nat) lm B
      (DOM: dom smap = set_seq 0 (B `min` (m + 2)))
      (IN: smap !! m = Some s)
      (LVL: lvl2nat lm = m)
      :
      ⊢ (([∗ map] k↦y ∈ delete m smap,
           ∃ l0, sgn EO_OP y l0 (Some (k <? m)) (H3 := oGS) ∗ ⌜lvl2nat l0 = k⌝) -∗
          sgn EO_OP s lm (Some true) (H3 := oGS)-∗
          [∗ map] i↦s0 ∈ smap,
           ∃ l0, sgn EO_OP s0 l0 (Some (i <? m + 1)) (H3 := oGS) ∗ ⌜ lvl2nat l0 = i⌝)%I.
    Proof using.
      iIntros "SIGS SG".
      rewrite (big_sepM_delete _ smap); eauto.
      iSplitL "SG".
      { iExists _. rewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
        iFrame. done. }
      iApply (big_sepM_impl with "[$]"). iModIntro.
      iIntros (???) "(%&?&?)". iExists _. iFrame.
      apply lookup_delete_Some in H0 as [??].
      apply mk_is_Some, elem_of_dom in H1.
      rewrite DOM in H1. apply elem_of_set_seq in H1.
      assert ((k <? m) = (k <? m + 1) \/ k = m).
      { destruct (decide (k = m)); [tauto| ]. left.
        destruct (k <? m) eqn:LT.
        - rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [done | ].
          apply PeanoNat.Nat.ltb_lt in LT. lia.
        - rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [done | ].
          apply PeanoNat.Nat.ltb_ge in LT. lia. }
      destruct H2; [| done]. rewrite H2. done.
    Qed.

    Lemma BMU_smap_restore τ B (BOUND: B < LIM) s m smap
      (DOM : dom smap = set_seq 0 (B `min` (m + 2)))
      (IN : smap !! m = Some s)
      (lm : sigO (λ i : nat, i < LIM))
      (LVL : lvl2nat lm = m):
        ⊢
  obls EO_OP τ ∅ (H3 := oGS) -∗
  ([∗ map] k↦y ∈ delete m smap, ∃ l0 : sigO (λ i : nat, i < LIM),
                                          sgn EO_OP y l0 (Some (k <? m)) (H3 := oGS) ∗
                                          ⌜lvl2nat l0 = k⌝) -∗
  (sgn EO_OP s lm (Some true) (H3 := oGS)) -∗
  own eofin_smap (● ((to_agree <$> smap): gmap _ _)) -∗
  BMU EO_OP (⊤ ∖ ↑nroot.@"eofin") τ 1
    (⌜B ≤ m + 2⌝ ∗ obls EO_OP τ ∅ (H3 := oGS) ∗ smap_repr (B `min` (m + 2)) (m + 1) smap
     ∨ (|==> ⌜m + 2 < B⌝ ∗
          (∃ (s' : SignalId) (lm': EOLevel B),
             smap_repr (B `min` (m + 3)) (m + 1) (<[m + 2:=s']> smap) ∗
             ith_sig (m + 2) s' ∗ obls EO_OP τ {[s']} (H3 := oGS) ∗
             ⌜lvl2nat lm' = (m + 2)%nat⌝))) (oGS := oGS).
    Proof using.
      iIntros "OBLS SIGS SIG SM".
      destruct (Nat.le_gt_cases B (m + 2)).
      { rewrite PeanoNat.Nat.min_l in DOM; [| done]. 
        iApply BMU_intro. iLeft. iFrame.
        iSplitR; [done| ]. iSplitR.
        { iPureIntro. rewrite PeanoNat.Nat.min_l; auto. }
        iApply (restore_map with "[$] [$]"); eauto.
        rewrite DOM. f_equal. symmetry. by apply Nat.min_l. }
      
      iApply OU_BMU.
      assert {lm' : EOLevel B | lvl2nat lm' = m + 2} as [lm' LVL'].
      { set (lm' := exist _ (m + 2) H0: EOLevel B).
        exists lm'. done. }
      iDestruct (OU_create_sig with "OBLS") as "FOO".
      iApply (OU_wand with "[-FOO]"); [| by iFrame].
      iIntros "(%s' & SG & OBLS & %NEW)". rewrite union_empty_l_L.
      iApply BMU_intro. iRight. iSplitR; [done| ].
      rewrite PeanoNat.Nat.min_r in DOM; [| lia].
      iMod (own_update with "SM") as "SM".
      { apply auth_update_alloc. eapply (alloc_singleton_local_update _ (m + 2) (to_agree s')).
        2: done. 
        apply not_elem_of_dom. rewrite dom_fmap. rewrite DOM.
        intros ?%elem_of_set_seq. lia. }
      iModIntro. iDestruct "SM" as "[SM S']".
      iExists s', lm'. 
      iSplitL "SIGS SG SIG SM".
      2: { iFrame. eauto. }
      rewrite PeanoNat.Nat.min_r; [| lia]. rewrite /smap_repr.
      rewrite -fmap_insert. iFrame. iSplitR.
      { iPureIntro. rewrite dom_insert_L DOM.
        apply set_eq. intros ?. rewrite elem_of_union elem_of_singleton.
        rewrite !elem_of_set_seq. lia. }
      rewrite big_sepM_insert_delete. iSplitL "SG".
      { iExists _. rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [ | lia].
        iFrame. iPureIntro.
        Unshelve.
        2: { assert (m + 2 < LIM) by lia. 
             esplit. apply H1. }
        done. }
      rewrite (delete_notin _ (m + 2)).
      2: { apply not_elem_of_dom. rewrite DOM. intros ?%elem_of_set_seq. lia. }
      iApply (restore_map with "[$] [$]"); eauto.
      rewrite DOM. f_equal. symmetry. by apply Nat.min_l.
    Qed.

    (* TODO: generalize, move *)
    Lemma lvl_lt_equiv (l1 l2: EOLevel LIM):
      lvl_lt EO_OP l1 l2 <-> bn2nat _ l1 < bn2nat _ l2.
    Proof using.
      destruct l1, l2; simpl in *.
      rewrite /lvl_lt. rewrite strict_spec_alt. simpl.
      rewrite /bounded_nat_le. simpl. split.
      - intros [? ?]. apply PeanoNat.Nat.le_neq. split; auto.
        intros ->. destruct H1. f_equal. apply Nat.lt_pi.
      - intros ?. split; [lia| ]. intros ?. inversion H1. subst. lia.
    Qed.
    
    Lemma ith_sig_expect i sw m τ π π__e N smap s
      (PH_EXP: phase_le π__e π)
      (GE: m <= i):
      ⊢ ep _ sw π__e d1 (H3 := oGS) -∗ th_phase_ge _ τ π (H3 := oGS) -∗
         smap_repr N m smap -∗ ith_sig i sw -∗
         ith_sig (i + 1) s -∗ obls _ τ {[ s ]} (H3 := oGS) -∗
         OU _ τ (∃ π', cp _ π' d1 (H3 := oGS) ∗ smap_repr N m smap ∗ th_phase_ge _ τ π' (H3 := oGS) ∗ obls _ τ {[ s ]} (H3 := oGS) ∗ ⌜ phase_le π π' /\ phase_le π__e π' ⌝) (H3 := oGS).
    Proof using.
      iIntros "#EP PH SR #SW #S OBLS". 
      iDestruct (ith_sig_in with "[$] [$]") as "%ITH".
      iDestruct (ith_sig_sgn with "S [$]") as "#OWN".
      iDestruct (smap_repr_split with "SW [$]") as "[SGw SR]".
      rewrite {1}/ex_ith_sig. rewrite (proj2 (Nat.ltb_ge _ _)); [| done].
      iDestruct "SGw" as "(%lw & SGw & %LW)".
      iDestruct (expect_sig_upd with "[$] [$] [$] [] [$]") as "OU"; [done| ..].
      { rewrite /sgns_level_gt. rewrite big_sepS_singleton.
        iDestruct "OWN" as "(%lo & SGo & %LO)".
        iExists _. iFrame "SGo". iPureIntro.
        apply lvl_lt_equiv. rewrite /lvl2nat in LW, LO. lia. }
      iApply (OU_wand with "[-OU]"); [| done].
      iIntros "(%π' & CP1 & SIGW & OBLS & PH & [%PH_LE' %PH_LE''])".
      iExists _. iFrame. iSplitL; [| done].
      iApply "SR". iExists _.
      rewrite (proj2 (Nat.ltb_ge _ _)); [| done]. by iFrame.
    Qed.

    Record ThreadResource (th_res: nat -> iProp Σ) (cond: nat -> bool) := {
        tr_agree (n1 n2: nat): threads_auth n1-∗ th_res n2 -∗
                              ⌜ n2 = if (cond n1) then n1 else (n1 + 1)%nat ⌝;
        tr_update (n: nat) (Cn: cond n):
          threads_auth n-∗ th_res n ==∗ threads_auth (n + 1) ∗ th_res (n + 2);
        tr_cond_neg n: cond (S n) = negb (cond n); 
    }.

    Lemma thread_spec_holds τ l B (BOUND: B < LIM) (π π2: Phase) n
      (PH_LE2: phase_le π2 π)
      `(ThreadResource th_res cond)
      :
      {{{ eofin_inv l B BOUND ∗ exc_lb EO_OP 20 (H3 := oGS) ∗
           (* even_res n ∗ *)
           th_res n ∗
           cp_mul _ π2 d2 (B - n) (H3 := oGS) ∗
           cp_mul _ π d0 20 (H3 := oGS) ∗
           (cp _ π2 d2 (H3 := oGS) ∨ ∃ sw π__e, ith_sig (n - 1) sw ∗ ep _ sw π__e d1 (H3 := oGS) ∗ ⌜ phase_le π__e π ⌝) ∗
           th_phase_ge EO_OP τ π (H3 := oGS) ∗
           (if n <? B
            then ∃ s, ith_sig n s ∗ obls EO_OP τ {[s]} (H3 := oGS)
            else obls EO_OP τ ∅ (H3 := oGS)) }}}
        thread_prog #l #n #B @ τ
      {{{ v, RET v; obls EO_OP τ ∅ (H3 := oGS) }}}.       
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
        (* pose proof (Is_true_true_1 _ EVEN) as E. *)
        (* rewrite E. *)
        (* pose proof (Nat.negb_even m) as O. rewrite E in O. simpl in O. rewrite -O.  *)
        
        iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_suc with "[$]"); try done.
        { econstructor. done. }
        iNext. iIntros "L".
        
        iDestruct (ith_sig_in with "[$] [$]") as %IN.
        iDestruct "SR" as "(SM & %DOM & SIGS)".
        
        iDestruct (big_sepM_delete with "SIGS") as "[SG SIGS]"; eauto.
        iDestruct "SG" as (lm) "(SG & %LVL)".
        rewrite Nat.ltb_irrefl. 
        
        MU_by_BMU. iApply OU_BMU.
        iDestruct (OU_set_sig with "OB [SG]") as "OU".
        { apply elem_of_singleton. reflexivity. }
        { by iFrame. }
        iApply (OU_wand with "[-OU]"); [| done]. iIntros "(SIG & OBLS)".
        rewrite (subseteq_empty_difference_L {[ s ]}); [| done].        
        
        iPoseProof (BMU_smap_restore with "[$] [$] [$] [$]") as "BMU"; eauto.
        iApply (BMU_lower _ _ _ 1); [lia| ].
        iApply (BMU_wand with "[-BMU] [$]"). iIntros "COND".
        
        iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
        iSplitR "CP".
        2: { do 2 iExists _. iFrame. done. }
        iApply wp_value.
        
        iMod (tr_update with "[$] TH") as "[AUTH TH]"; eauto. 

        (* rewrite E in H0. *)

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
          iClear "IH EXTRA". rewrite /thread_prog.
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

          red in H2. apply Nat.le_sum in H2 as [? LE]. rewrite {6}LE.
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
        (* pose proof (Is_true_true_1 _ ODD) as O. *)
        (* rewrite O. *)
        (* pose proof (Nat.negb_odd m) as E. rewrite O in E. simpl in E. rewrite -E.  *)

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

    Lemma thread_spec_wrapper τ l B (BOUND: B < LIM) (π π2: Phase) n
      (PH_LE2: phase_le π2 π)
      `(ThreadResource th_res cond)

      :
      {{{ eofin_inv l B BOUND ∗ exc_lb EO_OP 20 (H3 := oGS) ∗
           th_res n ∗
           cp_mul _ π2 d2 (S (B - n)) (H3 := oGS) ∗
           cp_mul _ π d0 20 (H3 := oGS) ∗           
           th_phase_ge EO_OP τ π (H3 := oGS) ∗
           (if n <? B
            then ∃ s, ith_sig n s ∗ obls EO_OP τ {[s]} (H3 := oGS)
            else obls EO_OP τ ∅ (H3 := oGS)) }}}
        thread_prog #l #n #B @ τ
      {{{ v, RET v; obls EO_OP τ ∅ (H3 := oGS) }}}.       
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

    (* TODO: parametrize smap_repr with the lower bound *)
    Lemma alloc_inv l (* (i: nat) *) B (LT: B < LIM) τ
      (* (i := 0) *)
      :
      obls _ τ ∅ (H3 := oGS) -∗ l ↦ #0 -∗ 
        BMU _ ⊤ τ 2 (|={∅}=> ∃ (eoG: EoFinG Σ) (sigs: gset SignalId),
                       even_res 0 (H := eoG)∗
                       odd_res 1 (H := eoG) ∗
                       eofin_inv l B LT (H := eoG) ∗
                       obls _ τ sigs (H3 := oGS) ∗
                       ⌜ size sigs = min B 2 ⌝ ∗
                       ([∗ set] k ∈ set_seq 0 (min B 2), ∃ s, ith_sig k s ∗ ⌜ s ∈ sigs ⌝)
        ) (oGS := oGS).
    Proof using OBLS_AMU PRE.
      iIntros "OB L".
      iMod (thread_res_alloc 0) as "(%γ & AUTH & FRAG)".
      iMod (thread_res_alloc 1) as "(%γ' & AUTH' & FRAG')".
      
      set (m := min B 2).
      iAssert (BMU EO_OP ⊤ τ 2 
                 (|==> ∃ γ smap, smap_repr' γ m 0 smap ∗
                                 let sigs := map_img smap in
                                 obls _ τ sigs (H3 := oGS) ∗
                                 ⌜ size sigs = m ⌝ ∗
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
          replace (map_img smap0) with ({[ si; si' ]}: gset SignalId).
          2: { subst smap0.
               rewrite map_img_insert_L. rewrite delete_notin; set_solver. }

          rewrite /smap_repr'. iFrame.
          (* rewrite !bi.sep_assoc. iSplitL.  *)
          (* 2: { subst smap0. simpl.. *)
          (*      iApply big_sepS_impl.  *)
          
          iSplitR "OBLS".
          2: { 
               iSplitL "OBLS".
               { iApply obls_proper; [| by iFrame]. set_solver. }
               rewrite size_union.
               2: { set_solver. }
               rewrite !size_singleton. iPureIntro. lia. }
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
          iModIntro. iExists _, _. iFrame. iSplitR "OBLS".
          2: { replace (map_img smap0) with ({[ si ]}: gset SignalId).
               2: { set_solver. }
               iSplitL. 
               { iApply obls_proper; [| by iFrame]. set_solver. }
               iPureIntro. rewrite size_singleton. lia. }
          rewrite /smap_repr'. iFrame.
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
          iModIntro. iExists _, _. iFrame. iSplitR "OB".
          2: { subst smap0. rewrite map_img_empty_L size_empty.
               iSplitL; [set_solver| ]. iPureIntro. lia. }
          rewrite /smap_repr'. iFrame.
          iSplitR.
          { subst smap0. iPureIntro. 
            subst m. (* subst i. *)
            assert (B = 0) as -> by lia. simpl.  
            set_solver. }
          subst smap0. rewrite big_sepM_empty. done. }

      (* iMod "SR" as (γ__sr smap) "BMU". iModIntro. *)
      iApply (BMU_wand with "[-SR] [$]"). 
      iIntros "X". iMod "X" as "(%γ__sr & %smap & SR & OB & %SIZE & #F)".
      
      set (eoG := {| 
          (* eofin_even := (if Nat.even i then γ else γ'); *)
          (* eofin_odd := (if Nat.even i then γ' else γ); *)
          eofin_even := (if Nat.even 0 then γ else γ');
          eofin_odd := (if Nat.even 0 then γ' else γ);
          eofin_smap := γ__sr
      |}).
      iExists eoG, _. iFrame. iApply fupd_frame_r.
      rewrite bi.sep_comm. rewrite -bi.sep_assoc. 
      iSplit; [done| ]. 
      iSplit. 
      2: { iApply inv_alloc. iNext. 
           rewrite /eofin_inv_inner. iExists 0, smap. iFrame. }
      rewrite /smap_repr'. iDestruct "SR" as "(?&%DOM&SIGS)".

      (* subst i. *)
      (* rewrite PeanoNat.Nat.sub_0_r. rewrite PeanoNat.Nat.sub_0_r in SIZE. *)
      iApply big_sepS_forall. iIntros (k IN).
      rewrite -DOM in IN. apply elem_of_dom in IN as [s IN]. 
      rewrite /ith_sig. iExists _. iSplit.
      2: { iPureIntro. eapply elem_of_map_img; eauto. }
      iApply (own_mono with "F").
      apply auth_frag_mono.
      apply singleton_included_l. eexists.
      rewrite lookup_fmap IN. simpl. split; [reflexivity| ]. done.
    Qed.

    Close Scope Z. 

    Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS _ EM _ ⊤}.
    Context {NO_OBS_POST: ∀ τ v, obls EO_OP τ ∅ (H3 := oGS) -∗ fork_post τ v}. 

    Theorem main_spec τ π (B: nat) (LT: B < LIM)
      (* (i := 0) *)
      :
      {{{ exc_lb EO_OP 20 (H3 := oGS) ∗
           cp_mul _ π d2 (S (2 * (S B))) (H3 := oGS) ∗
           cp_mul _ π d0 40 (H3 := oGS) ∗
           th_phase_ge EO_OP τ π (H3 := oGS) ∗
           obls EO_OP τ ∅ (H3 := oGS) }}}
      start #(0%nat) #B @ τ
      {{{ v, RET v; obls EO_OP τ ∅ (H3 := oGS) }}}.
    Proof using.
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
      iPoseProof (alloc_inv _ _ LT with "[$] [$]") as "BMU". 
      MU_by_BMU. iApply (BMU_weaken with "[-BMU] [$]"); [lia| done| ]. iIntros "INV".
      (* TODO: make a tactic, remove duplication *)
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
      iSplitR "CP".
      2: { do 2 iExists _. iFrame. done. }
      iApply wp_value.
      iApply fupd_mask_mono; [apply empty_subseteq| ].
      iMod "INV" as "(% & %sigs & RE & RO & #INV & OB & %SIG_LEN & #SIGS)".
      clear PRE. 
      iModIntro.

      (* assert (0 = i) as II by done. rewrite {2 5 6 7 8 10 11 13}II. *)
      (* rewrite {2}II in SIG_LEN. *)
      (* revert SIG_LEN. *)
      (* clear II. generalize i. clear i. intros i SIG_LEN.  *)

      wp_bind (Rec _ _ _)%V. pure_steps.

      (* iAssert (∃ γ γ', thread_frag γ i ∗ thread_frag γ' (i + 1))%I with "[RE RO]" as "(%γ & %γ' & RES & RES')". *)
      (* { destruct (Nat.even i); do 2 iExists _; iFrame. } *)

      rewrite Nat.add_0_r.
      rewrite -Nat.add_succ_l. iDestruct (cp_mul_split with "CPS2") as "[CPS2 CPS2']".
      replace 40 with (20 + 20) by lia. iDestruct (cp_mul_split with "CPS_FORK") as "[CPS_FORK CPS_FORK']". 
      wp_bind (Fork _)%E. 

      assert (B = 0 \/ B = 1 \/ 2 <= B) as [-> | [-> | LE2]] by lia; revgoals.
      - rewrite Nat.min_r in SIG_LEN; [| done]. rewrite Nat.min_r; [| done].
        simpl. rewrite union_empty_r_L. 
        rewrite big_sepS_union; [| set_solver]. rewrite !big_sepS_singleton.
        iDestruct "SIGS" as "[(%si & ITH & %INi) (%si' & ITH' & %INi')]". 

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
        assert (sigs = {[ si ; si' ]} /\ si ≠ si') as [SIG_EQ II'] by admit.
        Unshelve. 2: exact {[ si ]}.
        rewrite SIG_EQ.
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
        iSplitL "PH".
        { by erewrite <- LT'. }
        rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
        iExists _. by iFrame.
      - 

      
      
  End MainProof.



End EoFin.
