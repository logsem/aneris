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

  Instance EO_lvl_LeibnizEquiv: LeibnizEquiv EOLevelOfe.
  Admitted. 

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

  Section Threads.
    Context `{EoFinG Σ}.
    
    Definition thread_auth γ (n: nat): iProp Σ := own γ (●E n).

    Definition thread_frag γ (n: nat): iProp Σ := own γ (◯E n).

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

    Ltac MU_by_burn_cp :=
      iApply OBLS_AMU; [by rewrite nclose_nroot| ];
      iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH";
      BMU_burn_cp.

    Ltac pure_step_hl := 
      iApply sswp_MU_wp; [done| ];
      iApply sswp_pure_step; [done| ]; simpl;
      iNext.

    Ltac pure_step := pure_step_hl; MU_by_burn_cp. 

    Ltac pure_step_cases := pure_step || (iApply wp_value; []) || wp_bind (RecV _ _ _ _)%V.
    Ltac pure_steps := repeat (pure_step_cases; []).

    Definition ex_ith_sig (n i: nat) (s: SignalId): iProp Σ :=
      ∃ l, sgn EO_OP s l (Some $ Nat.ltb i n) (H3 := oGS) ∗ ⌜ lvl2nat l = i ⌝. 

    Definition smap_repr K n (smap: gmap nat SignalId): iProp Σ :=
      own eofin_smap (● (to_agree <$> smap: gmapUR nat (agreeR SignalId))) ∗
      ⌜ dom smap = set_seq 0 K ⌝ ∗
      ([∗ map] i ↦ s ∈ smap, ex_ith_sig n i s).

    Definition eofin_inv_inner l M (BOUND: M < LIM) : iProp Σ :=
      ∃ (n: nat) (smap: gmap nat SignalId), 
          l ↦ #n ∗
          thread_auth eofin_even (if Nat.even n then n else n + 1) ∗
          thread_auth eofin_odd (if Nat.odd n then n else n + 1) ∗
          smap_repr (min M (n + 2)) n smap
    .

    Definition eofin_inv l M BOUND: iProp Σ :=
      inv (nroot .@ "eofin") (eofin_inv_inner l M BOUND).

    Lemma add1_helper {x y: nat}: x < y -> x + 1 <= y.
    Proof. lia. Qed.

    Definition even_res n: iProp Σ :=
      thread_frag eofin_even n.

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
      rewrite /smap_repr. iDestruct "SR" as "(SM & % & SR)".
      rewrite {2 5}(map_split smap i) ITH /=.
      rewrite !big_sepM_union.
      2: apply map_disjoint_singleton_l_2; by apply lookup_delete.
      iDestruct "SR" as "[S SR]". rewrite big_sepM_singleton.
      iFrame. iIntros. iFrame. done.
    Qed.  

    Lemma smap_create_ep i K n smap π τ
      (LT: i < K):
      ⊢ smap_repr K n smap -∗ 
         cp EO_OP π d2 (H3 := oGS) -∗
         th_phase_ge EO_OP τ π (H3 := oGS) -∗
         BMU EO_OP ∅ τ 1 
           (∃ s, ith_sig i s ∗
             ep EO_OP s π d1 (H3 := oGS) ∗ smap_repr K n smap ∗
            th_phase_ge EO_OP τ π (H3 := oGS)) (oGS := oGS).
    Proof using.
      iIntros "SR CP PH".
      rewrite /smap_repr. iDestruct "SR" as "(AUTH & %DOM & SIGS)".
      assert (i ∈ dom smap) as [s ITH]%elem_of_dom.
      { rewrite DOM. apply elem_of_set_seq. lia. }
      rewrite {2 5}(map_split smap i) ITH /=.
      setoid_rewrite big_sepM_union.
      2, 3: apply map_disjoint_singleton_l_2; by apply lookup_delete.
      iDestruct "SIGS" as "[SIG SIGS]". setoid_rewrite big_sepM_singleton.
      rewrite {1}/ex_ith_sig. iDestruct "SIG" as "(%l & SIG & %LVLi)".
      iApply OU_BMU.
      iDestruct (create_ep_upd with "[$] [$] [$]") as "OU".
      { apply (ith_bn_lt _ 1). lia. }
      iApply (OU_wand with "[-OU]"); [| by iFrame].
      iIntros "(EP & SIG & PH)".
      iMod (own_update with "AUTH") as "X". 
      { apply auth_update_dfrac_alloc. 
        2: { apply singleton_included_l with (i := i).
             rewrite lookup_fmap ITH. eexists. split; [| reflexivity].
             simpl. reflexivity. }
        apply _. }
      iApply BMU_intro. iDestruct "X" as "[? ITH]". 
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
      iIntros "(%s' & SG & OBLS)". rewrite union_empty_l_L.
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

    Definition thread_spec τ l B π Φ: iProp Σ :=
      ∀ a,
           even_res a ∗ cp_mul EO_OP π d2 (S (B - a)) (H3 := oGS) ∗ 
           th_phase_ge EO_OP τ π (H3 := oGS) ∗
           (if a <? B
            then ∃ s0 : SignalId, ith_sig a s0 ∗ obls EO_OP τ {[s0]} (H3 := oGS)
            else obls EO_OP τ ∅ (H3 := oGS)) -∗
           ▷ (∀ x : base_lit, obls EO_OP τ ∅ (H3 := oGS) -∗ Φ #x) -∗
           WP thread_prog #l #a #B @τ {{ v, Φ v }}. 

    Lemma thread_advance τ (l: loc) B (BOUND : B < LIM) π Φ m
      (H0 : (if Nat.even m then m else m + 1) < B)
      (s : SignalId)
      (smap : gmap nat SignalId)
      (EVEN : Nat.even m)
      :
        (□ thread_spec τ l B π Φ) -∗
        even_res (if Nat.even m then m else m + 1) -∗
        ith_sig (if Nat.even m then m else m + 1) s -∗
        obls EO_OP τ {[s]} (H3 := oGS) -∗
        (∀ x, obls EO_OP τ ∅ (H3 := oGS) -∗ Φ #x) -∗
        cp_mul EO_OP π d2 (B - (if Nat.even m then m else m + 1)) (H3 := oGS) -∗
        th_phase_ge EO_OP τ π (H3 := oGS)-∗
        cp_mul EO_OP π d0 12 (H3 := oGS)-∗
        l ↦ #m -∗
        thread_auth eofin_even (if Nat.even m then m else m + 1) -∗
        thread_auth eofin_odd (if Nat.odd m then m else m + 1) -∗
        smap_repr (B `min` (m + 2)) m smap -∗
        (▷ eofin_inv_inner l B BOUND ={⊤ ∖ ↑nroot.@"eofin",⊤}=∗ emp) -∗
  WP CmpXchg #l #(if Nat.even m then m else (m + 1)%nat)
       #((if Nat.even m then m else (m + 1)%nat) + 1)
  @ τ; ⊤ ∖ ↑nroot.@"eofin" {{ v, |={⊤ ∖ ↑nroot.@"eofin",⊤}=>
                                   WP if: Snd v
                                      then thread_prog #l
                                             (#(if Nat.even m
                                                then m
                                                else (m + 1)%nat) + #2) #B
                                      else thread_prog #l
                                             #(if Nat.even m
                                               then m
                                               else (m + 1)%nat) #B @τ
                                   {{ v, Φ v }} }}.
    Proof using OBLS_AMU.
      iIntros "#IH TH SN OB POST CPS1 PH CPS L EVEN ODD SR CLOS".
      
      pose proof (Is_true_true_1 _ EVEN) as E.
      rewrite E.
      pose proof (Nat.negb_even m) as O. rewrite E in O. simpl in O. rewrite -O. 
      
      iApply sswp_MU_wp; [done| ]. 
      iApply (wp_cmpxchg_suc with "[$]"); try done.
      { econstructor. done. }
      iNext. iIntros "L".
      
      iDestruct (ith_sig_in with "[$] [$]") as %IN.
      iDestruct "SR" as "(SM & %DOM & SIGS)".
      iDestruct (big_sepM_delete with "SIGS") as "[SG SIGS]"; eauto.
      iDestruct "SG" as (lm) "(SG & %LVL)".
      rewrite Nat.ltb_irrefl. 
      
      iApply OBLS_AMU; [by rewrite nclose_nroot| ]. 
      iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH". 
      
      iApply OU_BMU.
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
      
      iMod (thread_update _ _ _ (m + 2) with "EVEN [$]") as "[EVEN TH]". 
      
      assert (S (B - (m + 2)) <= B - m) as LE.
      { destruct (Nat.even m); lia. }
      apply Nat.le_sum in LE as [? LE].
      rewrite LE.
      iDestruct (cp_mul_split with "CPS1") as "[? ?]". 
      
      destruct (Nat.le_gt_cases B (m + 2)).
      - iDestruct "COND" as "[COND | CC]".
        2: { iMod "CC" as "[% ?]". lia. }
        iDestruct "COND" as "(% & OBLS & SM)".
        
        iMod ("CLOS" with "[EVEN ODD SM L]") as "?".
        { rewrite /eofin_inv_inner. iNext. iExists (m + 1), smap.
          rewrite even_plus1_negb odd_plus1_negb E -O. simpl. 
          rewrite -Nat.add_assoc. rewrite Nat2Z.inj_add. 
          iFrame.
          rewrite Nat.min_l; [| done]. rewrite Nat.min_l; [| lia]. done. }
        
        iModIntro.
        wp_bind (Snd _)%E.           
        pure_steps.
        
        wp_bind (_ + _)%E. pure_step. iApply wp_value.
        
        replace (Z.add (Z.of_nat m) 2) with (Z.of_nat (m + 2)) by lia.
        iApply ("IH" with "[-POST]"). 
        2: by iFrame. 
        iFrame.
        rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [ | lia]. 
        iFrame "#∗".
      - iDestruct "COND" as "[CC | COND]".
        { iDestruct "CC" as "(% & ? & ?)". lia. }
        iClear "SN". 
        iMod "COND" as "[% (%s' & %lm' & SM & SN & OBLS & %LVL')]".
        iMod ("CLOS" with "[EVEN ODD SM L]") as "?".
        { rewrite /eofin_inv_inner. iNext. iExists (m + 1), _.
          rewrite even_plus1_negb odd_plus1_negb E -O. simpl. 
          rewrite -Nat.add_assoc. rewrite Nat2Z.inj_add. 
          iFrame. rewrite -Nat.add_assoc. simpl. iFrame. }
        
        iModIntro.
        wp_bind (Snd _)%E.           
        pure_steps.
        
        wp_bind (_ + _)%E. pure_step. iApply wp_value.
        
        replace (Z.add (Z.of_nat m) 2) with (Z.of_nat (m + 2)) by lia. 
        iApply ("IH" with "[-POST]"); [| by iFrame].
        rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
        iFrame "#∗".
        iExists _. iFrame. 
    Qed.
    
    Lemma wait_iter τ l (n B: nat) π π__e sw R
      (LT: n < B)
      (BOUND: B < LIM)
      (PHASE_EXP: phase_le π__e π):
      {{{ eofin_inv l B BOUND ∗ 
          cp _ π d1 (H3 := oGS) ∗ th_phase_ge _ τ π (H3 := oGS) ∗
          ith_sig (n - 1) sw ∗ obls _ τ R (H3 := oGS) ∗
          (∃ l, ⌜ lvl2nat l = n - 1 ⌝ ∗ sgns_level_gt _ R l (H3 := oGS)) ∗
          ep _ sw π__e d1 (H3 := oGS) ∗ exc_lb _ 20 (H3 := oGS) ∗ 
          even_res n
      }}}
        thread_prog #l #n #B @τ
      {{{ v, RET v; ⌜ False ⌝ }}}.
    Proof using.
      iIntros (Φ). iLöb as "IH" forall (π PHASE_EXP).
      iIntros "(#INV & CP1 & PH & #SW & OBLS & (%lw & %LW & #OBLS_LT) & #EXP & #EB & EV) POST".
      rewrite /thread_prog.

      wp_bind (RecV _ _ _ _)%V.
      iApply sswp_MU_wp; [done| ]. 
      iApply sswp_pure_step; [done| ]; simpl. 
      iNext.
      iApply OBLS_AMU; [by rewrite nclose_nroot| ]. 
      iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH".
      iApply OU_BMU.
      iDestruct (exchange_cp_upd with "CP1 [$] [$]") as "OU".
      { reflexivity. }
      { apply (ith_bn_lt _ 0). lia. } 
      iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "[CPS PH]". 
      BMU_burn_cp.
      pure_steps. 

      wp_bind (_ ≤ _)%E. pure_steps.
      rewrite bool_decide_false; [| lia]. pure_steps.
      fold thread_prog.
      wp_bind (_ + _)%E. pure_steps.

      wp_bind (CmpXchg _ _ _)%E.
      iApply wp_atomic. 
      iInv "INV" as ">inv" "CLOS". iModIntro.
      rewrite {1}/eofin_inv_inner.
      iDestruct "inv" as (m smap) "(L & EVEN & ODD & SR)".
      iDestruct (thread_agree with "EVEN [$]") as %<-.
      destruct (even_or_odd m) as [EVEN | ODD].
      - pose proof (Is_true_true_1 _ EVEN) as E. rewrite E.
        iApply sswp_MU_wp; [done| ].
        iApply (wp_cmpxchg_suc with "[$]"); try done.
        { econstructor. done. }
        iNext. iIntros "L".
        MU_by_burn_cp. 
        pure_steps.

        admit.
      - pose proof (Is_true_true_1 _ ODD) as O.
        rewrite O.
        pose proof (Nat.negb_odd m) as E. rewrite O in E. simpl in E. rewrite -E. 
        rewrite -E in LW LT. 

        iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_fail with "[$]"); try done.
        { intros [=]. lia. }
        { econstructor. done. }
        iNext. iIntros "L".
        rewrite Nat.min_r; [| lia].

        iApply OBLS_AMU; [by rewrite nclose_nroot| ]. 
        iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH".

        iApply OU_BMU.
        rewrite Nat.add_sub. 
        iDestruct (smap_repr_split with "[$] [$]") as "[SIGW SR]".
        rewrite {1}/ex_ith_sig. iDestruct "SIGW" as "(%lw' & SIGW & %LW')".
        rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
        assert (lw' = lw) as ->.
        { rewrite Nat.add_sub in LW. rewrite -LW' in LW.
          set_solver. }
        iDestruct (expect_sig_upd with "[$] [$] [$] [$] [$]") as "OU".
        { done. }
        iApply (OU_wand with "[-OU]"); [| by iFrame].
        iIntros "(%π' & CP1 & SIGW & OBLS & PH & [%PH_LE' %PH_LE''])".
        
        iSpecialize ("SR" with "[SIGW]").
        { rewrite /ex_ith_sig.
          rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
          iExists _. iFrame. done. }
        BMU_burn_cp.

        iApply wp_value.
        iMod ("CLOS" with "[EVEN ODD SR L]") as "?".
        { rewrite /eofin_inv_inner. iNext. iExists m, smap.
          rewrite Nat.min_r; [| lia].
          rewrite -E O. iFrame. }
        iModIntro.

        wp_bind (Snd _)%E. pure_step. iApply wp_value. pure_step.
        iApply ("IH" $! π' with "[] [-POST] [$]"); [done| ]. 
        iFrame "#∗". iExists _. iSplit; [| iApply "OBLS_LT"].
    Admitted.

    Lemma thread_spec_holds τ l B (BOUND: B < LIM) π Φ:
      eofin_inv l B BOUND -∗ exc_lb EO_OP 20 (H3 := oGS) -∗
      □ thread_spec τ l B π Φ. 
    Proof.
      iIntros "#INV #EB". iModIntro. 
      iLöb as "IH". 

      rewrite {2}/thread_spec. iIntros (n) "(TH & CPS1 & PH & SN_OB) POST".
      rewrite /thread_prog.
      
      wp_bind (RecV _ _ _ _)%V.
      iApply sswp_MU_wp; [done| ]. 
      iApply sswp_pure_step; [done| ]; simpl. 
      iNext.
      iApply OBLS_AMU; [by rewrite nclose_nroot| ]. 
      iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH".
      iDestruct (cp_mul_take with "CPS1") as "[CPS1 CP1]".
      iApply OU_BMU.
      iDestruct (exchange_cp_upd with "[$] [$] [$]") as "OU".
      { reflexivity. }
      { etrans; [apply d01_lt| apply d12_lt]. }
      iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "[CPS PH]". 
      BMU_burn_cp. 
      
      pure_steps.
      wp_bind (_ ≤ _)%E.
      pure_step.

      fold thread_prog. 

      destruct (Nat.le_gt_cases B n).
      { rewrite bool_decide_true; [| lia].
        pure_steps. iApply "POST".
        rewrite (proj2 (Nat.ltb_ge _ _)); done. }
      
      rewrite bool_decide_false; [| lia].
      rewrite (proj2 (Nat.ltb_lt _ _)); [| done].
      iDestruct "SN_OB" as (s) "[SN OB]". 
      pure_steps.
      wp_bind (_ + _)%E. pure_steps.  
      wp_bind (CmpXchg _ _ _)%E.

      iApply wp_atomic. 
      iInv "INV" as ">inv" "CLOS". iModIntro.
      rewrite {1}/eofin_inv_inner.
      iDestruct "inv" as (m smap) "(L & EVEN & ODD & SR)".
      iDestruct (thread_agree with "EVEN [$]") as %<-.
      destruct (even_or_odd m) as [EVEN | ODD].
      -
        (* TODO: why iApply doesn't work? *)
        iPoseProof (thread_advance with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "FOO".
        1, 2: eauto.
        
        pose proof (Is_true_true_1 _ EVEN) as E. rewrite E.
        iApply (wp_wand with "[$]"). set_solver.         
      - pose proof (Is_true_true_1 _ ODD) as O.
        rewrite O.
        pose proof (Nat.negb_odd m) as E. rewrite O in E. simpl in E. rewrite -E. 

        iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_fail with "[$]"); try done.
        { intros [=]. lia. }
        { econstructor. done. }
        iNext. iIntros "L".

        iApply OBLS_AMU; [by rewrite nclose_nroot| ]. 
        iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH".
        assert (B - (m + 1) = S (B - (m + 2))) as LE.
        { destruct (Nat.even m); lia. }
        rewrite LE.
        iDestruct (cp_mul_take with "CPS1") as "[CPS1 CP1]".
        iPoseProof (smap_create_ep m with "[$] [$] [$]") as "BMU"; eauto.
        { lia. }
        iApply (BMU_weaken with "[-BMU] [$]"); [lia| set_solver| ].
        iIntros "(%sw & SW & EP & SR & PH)".
        iDestruct (ith_sig_sgn with "[$] [$]") as "(%lw & #SGW & %LVLw)". 

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
        iSplitR "CP".
        2: { do 2 iExists _. iFrame. done. }
        iApply wp_value.

        iMod ("CLOS" with "[EVEN ODD SR L]") as "?".
        { rewrite /eofin_inv_inner. iNext. iExists m, smap.
          rewrite -E O. iFrame. }
        iModIntro.

        wp_bind (Snd _)%E. pure_steps.

        admit.
    Admitted. 

  End Threads.

End EoFin.
