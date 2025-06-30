From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl excl_auth.
From iris.base_logic.lib Require Import invariants.
From fairness Require Import locales_helpers utils.
From lawyer Require Import program_logic sub_action_em.
From lawyer.obligations Require Import obligations_model obls_utils obligations_resources obligations_logic obligations_em env_helpers.
From lawyer.examples Require Import orders_lib signal_map obls_tactics.
From heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


Close Scope Z.

Definition EODegree n := bounded_nat n. 
Definition EOLevel n := bounded_nat n.


Section EoFin.
  Context (B: nat).
  Let LIM := B + 1. 
  Let MAX_OBL_STEPS := 10.
  Let NUM_DEG := 5.
  
  Instance EO_OP': ObligationsParamsPre (EODegree NUM_DEG) (EOLevel LIM) MAX_OBL_STEPS.
  Proof using.
    esplit; try by apply _.
    - apply nat_bounded_PO. 
    - apply nat_bounded_PO. 
  Defined.
  Definition EO_OP := LocaleOP (Locale := locale heap_lang). 
  Existing Instance EO_OP. 

  Let EOLevelOfe := BNOfe LIM. 
  Let EODegreeOfe := BNOfe NUM_DEG.

  Instance EOFin_OP_HL: OP_HL EODegreeOfe EOLevelOfe MAX_OBL_STEPS.
  Proof. esplit; by apply _. Defined.
  Existing Instance EOFin_OP_HL. 

  Context `{EM: ExecutionModel heap_lang M}.
  Context {Σ} {OHE: OM_HL_Env EOFin_OP_HL EM Σ}. 
  
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
      eofin_threads_PreG :: inG Σ (excl_authR natO);
      eofin_sigs :: SigMapPreG Σ;
  }.
  
  Class EoFinG Σ := {
      eofin_PreG :: EoFinPreG Σ;
      eofin_even: gname; eofin_odd: gname;
      eofin_sm :: SigMapG Σ;
  }.

  Definition d0 := ith_bn NUM_DEG 0 ltac:(lia).
  Definition d1 := ith_bn NUM_DEG 1 ltac:(lia). 
  Definition d2 := ith_bn NUM_DEG 2 ltac:(lia). 
  Lemma d12_lt: strict (bounded_nat_le _) d1 d2.
  Proof using. apply ith_bn_lt. lia. Qed. 
  Lemma d01_lt: strict (bounded_nat_le _) d0 d1.
  Proof using. apply ith_bn_lt. lia. Qed.
    
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

    Definition smap_repr_eo n K: iProp Σ :=
      smap_repr B__eo (flip Nat.ltb n) (set_seq 0 K).

    Definition eofin_inv_inner l: iProp Σ :=
      ∃ (n: nat), 
          l ↦ #n ∗ threads_auth n ∗
          smap_repr_eo n (min B (n + 2)).

    Definition eofin_inv l: iProp Σ :=
      inv (nroot .@ "eofin") (eofin_inv_inner l).

    Record ThreadResource (th_res: nat -> iProp Σ) (cond: nat -> bool) := {
        tr_agree (n1 n2: nat): threads_auth n1-∗ th_res n2 -∗
                              ⌜ n2 = if (cond n1) then n1 else (n1 + 1)%nat ⌝;
        tr_update (n: nat) (Cn: cond n):
          threads_auth n-∗ th_res n ==∗ threads_auth (n + 1) ∗ th_res (n + 2);
        tr_cond_neg n: cond (S n) = negb (cond n); 
    }.

    Lemma lt_B_LIM: B < LIM. lia. Qed. 

    Lemma BOU_update_SR τ m:
  obls τ ∅ -∗
  smap_repr_eo (m + 1) (B `min` (m + 2)) -∗
      BOU ∅ 1 (
        |==> ∃ R', smap_repr_eo (m + 1) (B `min` (m + 3)) ∗
                         obls τ R' ∗
          (⌜ B <= m + 2 /\ R' = ∅ ⌝ ∨
           ∃ s', ith_sig (m + 2) s' ∗ ⌜ m + 2 < B /\ R' = {[ s' ]} ⌝)).
    Proof using.
      iIntros "OBLS SR".
      destruct (Nat.le_gt_cases B (m + 2)).
      { rewrite !PeanoNat.Nat.min_l; try lia.
        iApply BOU_intro. iModIntro. do 1 iExists _. iFrame.
        iLeft. done. }

      iApply BOU_wand.
      2: { rewrite /smap_repr_eo. simpl.
           iPoseProof (BOU_smap_extend B__eo τ (m + 2) _ ∅
(flip Nat.ltb (m + 1)) (flip Nat.ltb (m + 1)) with "[$] [$]") as "foo".
           4: by iFrame.
           { done. }
           { simpl. apply Nat.ltb_ge. lia. }
           intros ?%elem_of_set_seq. lia. }

      iIntros "UPD". iMod "UPD" as (?) "(SR & SIG & OB & % & #LVL)".
      iModIntro. repeat rewrite Nat.min_r; try lia. 
      do 1 iExists _. iFrame. iSplit.
      { rewrite /smap_repr_eo. 
        rewrite (Nat.add_succ_r _ 2).        
        rewrite set_seq_S_end_union_L. rewrite union_comm_L. iFrame. }
      iRight. iExists _. iFrame. iPureIntro.
      eexists. repeat split; eauto. set_solver.
    Qed.

    Lemma B__eo_simpl i (DOM: i < LIM):
      B__eo i = ith_bn LIM i DOM.
    Proof.      
      rewrite /B__eo. destruct le_lt_dec; [lia| ].
      f_equal. eapply Nat.lt_pi.
    Qed.

    Lemma thread_spec_holds τ l π n
      `(ThreadResource th_res cond)
      :
      {{{ eofin_inv l ∗ exc_lb 20 ∗
           th_res n ∗
           cp_mul π d2 (B - n) ∗
           cp_mul π d0 20 ∗
           (cp π d2 ∨ ∃ sw, ith_sig (n - 1) sw ∗ ep sw π d1) ∗
           th_phase_eq τ π ∗
           (if n <? B
            then ∃ s, ith_sig n s ∗ obls τ {[s]}
            else obls τ ∅) }}}
        thread_prog #l #n #B @ τ
      {{{ v, RET v; obls τ ∅ }}}.       
    Proof using. 
      iIntros (Φ). iLöb as "IH" forall (n).
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
      iDestruct "inv" as (m) "(L & AUTH & SR)".
      iDestruct (tr_agree with "[$] TH") as %EQ; eauto. subst n. 
      destruct (cond m) eqn:Cm.
      - 
        iClear "EXTRA". 
        
        iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_suc with "[$]"); try done.
        { econstructor. done. }
        iNext. iIntros "L".
       
        MU_by_BOU. iFrame "PH". 
        iApply OU_BOU.
        iApply (OU_wand with "[-OB SR]").
        2: { iApply (smap_set_sig B__eo with "[$] [$] [$]").
             { Unshelve. 2: exact (flip Nat.ltb (S m)).
               simpl. apply Nat.ltb_lt. lia. }
             { set_solver. }
             intros. simpl.
             apply elem_of_set_seq in H2.
             destruct (Nat.lt_trichotomy j (S m)) as [LT | [-> | LT]]; revgoals.
             1,2: rewrite !(proj2 (Nat.ltb_ge _ _)); lia.
             rewrite !(proj2 (Nat.ltb_lt _ _)); try lia. }
        
        iIntros "(SR & OBLS)".
        rewrite (subseteq_empty_difference_L {[ s ]}); [| done].
                
        iApply (BOU_weaken ∅ _ 1 _ _ _); [lia| set_solver|iIntros "X"; iApply "X"|].
                
        iApply (BOU_wand with "[-OBLS SR]").
        2: { iApply (BOU_update_SR with "[$] [SR]").
             rewrite /smap_repr_eo. rewrite Nat.add_1_r. iFrame. }
        iIntros "UPD".
        burn_cp_after_BOU.
        iMod "UPD" as (R') "(SR & OB & COND)". 
        iApply wp_value.
        
        iMod (tr_update with "[$] TH") as "[AUTH TH]"; eauto. 

        destruct (Nat.le_gt_cases B (m + 2)). 
        + iDestruct "COND" as "[COND | CC]".
          2: { iDestruct "CC" as "(%&?&%&?)". lia. }
          iDestruct "COND" as "(_ & ->)".
          
          iMod ("CLOS" with "[AUTH SR L]") as "?".
          { rewrite /eofin_inv_inner. iNext. iExists (m + 1).
            rewrite -Nat.add_assoc. rewrite Nat2Z.inj_add. 
            iFrame. }
          
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
          { iDestruct "CC" as "(% & %)". lia. }
          iClear "SN".  
          iDestruct "COND" as "(%s' & SN & (%LT & ->))".
          iMod ("CLOS" with "[AUTH SR L]") as "?".
          { rewrite /eofin_inv_inner. iNext. iExists (m + 1).
            rewrite -Nat.add_assoc. rewrite Nat2Z.inj_add. 
            iFrame. }
          
          iModIntro.
          wp_bind (Snd _)%E.           
          pure_steps.
          
          wp_bind (_ + _)%E.

          red in LT. apply Nat.le_sum in LT as [? LE].
          rewrite {4}LE.
          rewrite -plus_n_Sm. 
          rewrite !plus_Sn_m. rewrite !PeanoNat.Nat.sub_succ_l; try lia.
          iDestruct (cp_mul_take with "CPS2") as "[CPS2 CP2']".
          iDestruct (cp_mul_take with "CPS2") as "[CPS2 CP2'']".
          replace (B - S (m + 1)) with (m + 1 + x - m) by lia.

          pure_step_hl. 
          MU_by_BOU. iApply OU_BOU.
          iDestruct (exchange_cp_upd with "CP2'' [$]") as "OU".
          { reflexivity. }
          { etrans; [apply d01_lt| apply d12_lt]. }
          iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "CPS'".
          BOU_burn_cp.

          iApply wp_value.
          
          replace (Z.add (Z.of_nat m) 2) with (Z.of_nat (m + 2)) by lia. 
          iApply ("IH" with "[-POST]"); [..| done].
          rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
          
          iFrame "#∗".
          replace (B - (m + 2)) with (m + 1 + x - m) by lia.
          replace (m + 2) with (S (m + 1)) by lia.
          iFrame. 
      - iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_fail with "[$]"); try done.
        { intros [=]. lia. }
        { econstructor. done. }
        iNext. iIntros "L".

        assert (B - (m + 1) = S (B - (m + 2))) as LE by lia. 
        rewrite LE.

        iDestruct "EXTRA" as "[CP2' | EXP]". 
        + MU_by_BOU. 
          (* TODO: avoid unfolding BOU *)
          rewrite /smap_repr_eo. 
          iPoseProof (smap_create_ep' B__eo m with "[$] [$] [$]") as "OU"; eauto.
          { apply elem_of_set_seq. lia. } 
          { apply d12_lt. }
          iApply OU_BOU.
          iApply (OU_wand with "[-OU]"); [| done].
          iIntros "X". iMod "X" as "(%sw & #SW & #EP & SR & PH)".
          iDestruct (ith_sig_sgn with "SN [$]") as "#EX". 
          iDestruct (ith_sig_expect B__eo with "[$] [$] [$] SW [$] []") as "OU".
          { apply Nat.ltb_irrefl. }
          { rewrite /sgns_level_gt.
            iApply big_opS_singleton. iExists _. iFrame "EX".
            iPureIntro. apply set_Forall_singleton. 
            rewrite !B__eo_simpl; try lia. intros.
            apply ith_bn_lt. lia. }
            
          iApply OU_BOU.
          iApply (OU_wand with "[-OU]"); [| done].
          iIntros "(CP1 & SR & PH & OBLS)".

          iApply OU_BOU.
          iDestruct (exchange_cp_upd with "[$] [$]") as "OU".
          { reflexivity. }
          { apply d01_lt. }
          iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "CPS'".
          BOU_burn_cp.
 
          iApply wp_value.

          iMod ("CLOS" with "[AUTH SR L]") as "?".
          { rewrite /eofin_inv_inner. iNext. iExists m.
            rewrite Nat.min_r; [| lia]. iFrame. }
          iModIntro.
          wp_bind (Snd _)%E.

          pure_step_hl.
          MU_by_BOU. BOU_burn_cp.
          
          do 2 pure_step_cases. 
          iApply ("IH" $! _ with "[-POST]"); [..| by iFrame].
          replace (B - (m + 1)) with (S (B - (m + 2))) by lia.
          rewrite Nat.add_sub.
          iFrame "#∗". 
          rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
          iExists _. iFrame "#∗".
        + MU_by_BOU. 
          iDestruct "EXP" as "(%sw & #SW & #EP)".
          rewrite Nat.add_sub.
          iDestruct (ith_sig_sgn with "SN [$]") as "#EX".
          iDestruct (ith_sig_expect B__eo with "[$] [$] [$] [$] [$] []") as "OU".
          { apply Nat.ltb_irrefl. }
          { rewrite /sgns_level_gt.
            iApply big_opS_singleton. 
            iExists _. iFrame "EX". iPureIntro.
            apply set_Forall_singleton.
            rewrite !B__eo_simpl; try lia. intros.
            apply ith_bn_lt. lia. }
          iApply OU_BOU.
          iApply (OU_wand with "[-OU]"); [| done].
          iIntros "(CP1 & SR & PH & OBLS)".

          iApply OU_BOU.
          iDestruct (exchange_cp_upd with "[$] [$]") as "OU". 
          { done. }
          { apply d01_lt. }
          iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "CPS'".
          BOU_burn_cp.
 
          iApply wp_value.

          iMod ("CLOS" with "[AUTH SR L]") as "?".
          { rewrite /eofin_inv_inner. iNext. iExists m.
            rewrite Nat.min_r; [| lia]. iFrame. }
          iModIntro.
          wp_bind (Snd _)%E.
          do 3 pure_step_cases. 
          iApply ("IH" $! _ with "[-POST]"); [..| by iFrame]. 
          replace (B - (m + 1)) with (S (B - (m + 2))) by lia. 
          iFrame "#∗". 
          iSplitR "OBLS".
          2: { rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
               iExists _. iFrame "#∗". }
          iRight. rewrite Nat.add_sub.
          done. 
    Time Qed.

    Lemma thread_spec_wrapper τ l π n `(ThreadResource th_res cond):
      {{{ eofin_inv l ∗ exc_lb 20 ∗
           th_res n ∗
           cp_mul π d2 (S (B - n)) ∗
           cp_mul π d0 20 ∗           
           th_phase_eq τ π ∗
           (if n <? B
            then ∃ s, ith_sig n s ∗ obls τ {[s]}
            else obls τ ∅) }}}
        thread_prog #l #n #B @ τ
      {{{ v, RET v; obls τ ∅ }}}.
    Proof using.
      iIntros (Φ). iIntros "(#INV & #EB & TH & CPS2 & CPS & PH & SN_OB) POST".
      iDestruct (cp_mul_take with "CPS2") as "[??]".
      iApply (thread_spec_holds with "[-POST] [$]").
      { eauto. }
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

    Lemma alloc_inv l τ:
      obls τ ∅ -∗ l ↦ #0 -∗ 
        BOU ⊤ 2 (|={∅}=> ∃ (eoG: EoFinG Σ) (sigs: list SignalId),
                       even_res 0 (H := eoG)∗
                       odd_res 1 (H := eoG) ∗
                       eofin_inv l (H := eoG) ∗
                       obls τ (list_to_set sigs) ∗
                       ⌜ length sigs = min B 2 ⌝ ∗
                       ⌜ NoDup sigs ⌝ ∗
                       ([∗ list] k ↦ s ∈ sigs, ith_sig k s)
        ).
    Proof using PRE.
      iIntros "OB L".
      iMod (thread_res_alloc 0) as "(%γ & AUTH & FRAG)".
      iMod (thread_res_alloc 1) as "(%γ' & AUTH' & FRAG')".
      
      set (m := min B 2).
      iAssert (BOU ⊤ 2 
                 (|==> ∃ smap (smG: SigMapG Σ),
                              smap_repr B__eo (flip Nat.ltb 0) (set_seq 0 m) ∗
                              ⌜ dom smap = set_seq 0 m ⌝ ∗
                               let sigs := sigs_block smap 0 m in
                               obls τ (list_to_set sigs) ∗
                               ⌜ NoDup sigs ⌝ ∗ 
                               own sm_γ__smap (◯ ((to_agree <$> smap): gmapUR nat _)) ∗
                               ⌜ @sm_PreG _ smG = @eofin_sigs _ PRE ⌝
              ))%I with "[OB]" as "-#SR".
      { assert (m <= 0 \/ m = 0 + 1 \/ m = 0 + 2) as [LE | [EQ | EQ]] by lia; revgoals.
        - iApply OU_BOU.
          assert (0 < LIM) as Di by lia. 
          unshelve iDestruct (OU_create_sig with "[$]") as "OU".
          { eexists. apply Di. }
          iApply (OU_wand with "[-OU] [$]"). iIntros "(%si & SGi & OBLS & _)". 

          iApply OU_BOU.
          assert (0 + 1 < LIM) as Di' by lia. 
          unshelve iDestruct (OU_create_sig with "[$]") as "OU".
          { eexists. apply Di'. }
          iApply (OU_wand with "[-OU] [$]"). iIntros "(%si' & SGi' & OBLS & %NEW)".

          iApply BOU_intro.
          set (smap0 := {[ 0 := si; 0 + 1 := si']}: gmap nat SignalId).
          iMod (own_alloc (● ((to_agree <$> smap0): gmapUR nat (agreeR SignalId)) ⋅ ◯ _)) as (?) "[A F]".
          { apply auth_both_valid_2; [| reflexivity]. apply map_nat_agree_valid. }
          iModIntro.
          iExists _, {| sm_γ__smap := γ0|}. iFrame. 
          replace (sigs_block smap0 0 m) with ([ si; si' ]).
          2: { subst smap0 m. rewrite EQ. rewrite /sigs_block. simpl. done. } 

          rewrite !bi.sep_assoc.
          iSplitL; [| done]. iSplitL. 
          2: { iPureIntro. econstructor; try set_solver. apply NoDup_singleton. }
          
          iSplitR "OBLS".
          2: { iApply obls_proper; [| by iFrame]. set_solver. }

          iSplit.
          2: { subst smap0. iPureIntro. rewrite !dom_insert_L.
               subst m. rewrite EQ. simpl. set_solver. }
          subst smap0. rewrite /smap_repr. iFrame.
          rewrite !big_sepM_insert. 2, 3: set_solver. rewrite big_sepM_empty. 
          rewrite /ex_ith_sig. rewrite !B__eo_simpl. iFrame.
          iPureIntro. subst m. rewrite EQ. set_solver. 
        - iApply OU_BOU.
          assert (0 < LIM) as Di by lia. 
          unshelve iDestruct (OU_create_sig with "[$]") as "OU".
          { eexists. apply Di. }
          iApply (OU_wand with "[-OU] [$]"). iIntros "(%si & SGi & OBLS & _)".

          iApply BOU_intro.
          set (smap0 := {[ 0 := si]}: gmap nat SignalId).
          iMod (own_alloc (● ((to_agree <$> smap0): gmapUR nat (agreeR SignalId)) ⋅ ◯ _)) as (?) "[A F]".
          { apply auth_both_valid_2; [| reflexivity]. apply map_nat_agree_valid. }
          iModIntro. iExists _, {| sm_γ__smap := γ0 |}. iFrame.
          replace (sigs_block smap0 0 m) with [si].
          2: { subst smap0 m. rewrite EQ. rewrite /sigs_block. simpl. done. }
          iSplitR "OBLS".
          2: { simpl. rewrite union_empty_l_L union_empty_r_L. iFrame.
               iPureIntro. repeat split; try done.
               - subst smap0 m. rewrite EQ. rewrite /sigs_block. set_solver.
               - by apply NoDup_singleton. }

          subst smap0. rewrite /smap_repr. 
          rewrite !big_sepM_insert; [| set_solver]. rewrite big_sepM_empty.
          rewrite /ex_ith_sig. simpl. subst m. rewrite EQ.
          rewrite !(proj2 (PeanoNat.Nat.ltb_ge _ _)); try lia.
          rewrite !B__eo_simpl. iFrame. iPureIntro. set_solver. 
        - iApply BOU_intro.
          set (smap0 := ∅: gmap nat SignalId).
          iMod (own_alloc (● ((to_agree <$> smap0): gmapUR nat (agreeR SignalId)) ⋅ ◯ _)) as (?) "[A F]".
          { apply auth_both_valid_2; [| reflexivity]. apply map_nat_agree_valid. }
          iModIntro. iExists _, {| sm_γ__smap := γ0 |}. iFrame.
          assert (B = 0) by lia. simpl.  
          replace (sigs_block smap0 0 m) with (nil: list SignalId).
          2: { subst smap0 m. simpl. rewrite H. done. }

          iSplitR "OB".
          2: { iFrame. iPureIntro. repeat split; try (done || constructor).
               subst smap0 m. rewrite dom_empty_L H. done. }
          subst smap0. rewrite big_sepM_empty.
          subst m. rewrite H. iPureIntro. set_solver. } 

      iApply (BOU_wand with "[-SR] [$]"). 
      iIntros "X". iMod "X" as "(%smap & %SMG & SR & %DOM & OB & %SIZE & #F & %EQ_PRE)".
      
      set (eoG := {| 
          eofin_even := (if Nat.even 0 then γ else γ');
          eofin_odd := (if Nat.even 0 then γ' else γ);
          eofin_sm := SMG;
      |}).
      
      iExists eoG, _. iFrame.
      iApply fupd_frame_r.
      iSplit. 
      { iApply inv_alloc. iNext.
        rewrite /eofin_inv_inner. iExists 0. iFrame. }
      rewrite bi.sep_assoc. iSplit.
      { iPureIntro. split; try done. apply sigs_block_len. } 
      iDestruct "SR" as "SIGS".
      iApply big_sepL_forall. iIntros (k s IN).
      pose proof IN as DOMk%mk_is_Some%sigs_block_is_Some.
      rewrite sigs_block_lookup_eq in IN; try done.
      2: { simpl. rewrite DOM. apply elem_of_set_seq. lia. }
      simpl in IN.       
      rewrite /ith_sig.
      rewrite EQ_PRE. 
      iApply (own_mono with "F").
      apply auth_frag_mono.
      apply singleton_included_l. eexists.
      rewrite lookup_fmap IN. simpl. split; [reflexivity| ]. done.
    Qed.

    Close Scope Z. 

    Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}. 

    Theorem main_spec τ π:
      {{{ exc_lb 20 ∗
           cp_mul π d2 (S (2 * (S B))) ∗
           cp_mul π d0 40 ∗
           th_phase_eq τ π ∗
           obls τ ∅ }}}
      start #(0%nat) #B @ τ
      {{{ v, RET v; obls τ ∅ }}}.
    Proof using PRE NO_OBS_POST.
      iIntros (Φ). iIntros "(#EB & CPS2 & CPS_FORK & PH & OB) POST". rewrite /start.
      iDestruct (cp_mul_take with "CPS2") as "[CPS2 CP]". 

      wp_bind (RecV _ _ _ _)%V.
      pure_step_hl.
      MU_by_BOU.
      iApply OU_BOU.
      iDestruct (exchange_cp_upd with "[$] [$]") as "OU". 
      { done. }
      { etrans; [apply d01_lt| apply d12_lt]. }
      iApply (OU_wand with "[-OU]"); [| by iFrame]. iIntros "CPS".
      BOU_burn_cp.
      
      pure_steps.
      wp_bind (ref _)%E.
      iApply sswp_MU_wp_fupd; [done| ]. iApply wp_alloc.
      iModIntro.
      iNext. iIntros "%l L _".
      iPoseProof (alloc_inv _ _  with "[$] [$]") as "BOU". 
      MU_by_BOU. iApply (BOU_weaken with "[-BOU] [$]"); [lia| done| ]. iIntros "INV".
      burn_cp_after_BOU. 
      iApply wp_value.
      iApply fupd_mask_mono; [apply empty_subseteq| ].
      iMod "INV" as "(% & %sigs & RE & RO & #INV & OB & %SIGS_LEN & %SIGS_UNIQ & #SIGS)".
      clear PRE. 
      iModIntro.

      wp_bind (Rec _ _ _)%V. pure_steps.

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
        2: { iApply ohe_obls_AMU__f; [done| ].
             iApply BOU_AMU__f.
             iApply BOU_intro. iFrame "PH OB".
             iSplitR "CP".
             2: { iExists _. iFrame. }
             iNext. iAccu. }

        iIntros "[? (%π1 & %π2 & PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])]".
        Unshelve. 2: exact {[ si ]}.
        assert (si ≠ si') as NEQ.
        { intros <-. apply NoDup_cons in SIGS_UNIQ. set_solver. }
        replace (({[si; si']} ∖ {[si]})) with ({[si']}: gset _) by set_solver.
        replace ({[si; si']} ∩ {[si]}) with ({[si]}: gset _) by set_solver.
        iSplitL "RE CPS2 CPS_FORK PH3 OB2".
        { iApply (thread_spec_wrapper with "[-]").
          { apply even_thread_resource. }
          2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
          rewrite Nat.sub_0_r. iFrame "#∗".
          rewrite bi.sep_assoc. iSplitR "OB2".
          2: { rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
               iExists _. by iFrame. }
          iSplitL "CPS2"; (iApply cp_mul_weaken; [| reflexivity| by iFrame]); apply LT2. }

        iRename "PH1" into "PH".
        apply strict_include in LT1.
        iDestruct (cp_mul_weaken with "CPS") as "CPS"; [apply LT1| reflexivity| ].
        wp_bind (Rec _ _ _)%E. pure_steps.

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ''). iApply (MU__f_wand with "[-CP PH OB1]").
        2: { iApply ohe_obls_AMU__f; [done| ].
             iApply BOU_AMU__f. 
             iApply BOU_intro. iFrame "PH OB1".
             iSplitR "CP".
             2: { iExists _. iFrame. }
             iNext. iAccu. }

        iIntros "[? (%π3 & %π4 & PH1 & OB1 & PH3 & OB2 & [%LT3 %LT4])]".
        Unshelve. 2: exact {[ si' ]}.        
        rewrite difference_diag_L. rewrite intersection_idemp_L.

        iSplitR "POST OB1".
        2: { by iApply "POST". }
        
        apply strict_include in LT4. iRename "PH3" into "PH".
        wp_bind (_ + _)%E. rewrite Nat2Z.inj_0.
        iDestruct (cp_mul_weaken with "CPS") as "CPS"; [apply LT4| reflexivity| ].
        do 2 pure_step_cases.
        replace (0 + 1)%Z with 1%Z; [| done].
        replace 1%Z with (Z.of_nat 1%nat); [| done].
        iApply (thread_spec_wrapper with "[-]").
        { apply odd_thread_resource. }
        2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
        rewrite -PeanoNat.Nat.sub_succ_l; [| lia]. simpl. rewrite Nat.sub_0_r.
        iDestruct (cp_mul_take with "CPS2'") as "[CPS2 ?]". 
        iFrame "PH". iFrame "#∗".
        rewrite bi.sep_assoc. iSplitR "OB2".
        2: { rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
             iExists _. by iFrame. }
        iSplitL "CPS2"; (iApply cp_mul_weaken; [| reflexivity| by iFrame]).
        all: etrans; eauto.
        Unshelve. exact #(). 
      - simpl in SIGS_LEN. 
        destruct sigs as [| si [|]]; try by (simpl in SIGS_LEN; lia).

        rewrite !big_sepL_cons. simpl. rewrite union_empty_r_L.  
        iDestruct "SIGS" as "(ITH & _)". 

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
        iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[-CP PH OB]").
        2: { iApply ohe_obls_AMU__f; [done| ].
             iApply BOU_AMU__f. 
             iApply BOU_intro. iFrame "PH OB".
             iSplitR "CP".
             2: { iExists _. iFrame. }
             iNext. iAccu. }

        iIntros "[? (%π1 & %π2 & PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])]".
        Unshelve. 2: exact {[ si ]}.

        rewrite difference_diag_L. rewrite intersection_idemp_L.
        iSplitL "RE CPS2 CPS_FORK PH3 OB2".
        { iApply (thread_spec_wrapper with "[-]").
          { apply even_thread_resource. }
          2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
          rewrite Nat.sub_0_r. iFrame "PH3 #∗".
          rewrite bi.sep_assoc. iSplitR "OB2".
          2: { rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)); [ | lia].
               iExists _. by iFrame. }
          iSplitL "CPS2"; (iApply cp_mul_weaken; [| reflexivity| by iFrame]).
          all: apply LT2. }

        apply strict_include in LT1. iRename "PH1" into "PH".
        iDestruct (cp_mul_weaken with "CPS") as "CPS"; [apply LT1| reflexivity| ].
        wp_bind (Rec _ _ _)%V. pure_step.
        iApply wp_value. pure_step.

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ''). iApply (MU__f_wand with "[-CP PH OB1]").
        2: { iApply ohe_obls_AMU__f; [done| ].
             iApply BOU_AMU__f.
             iApply BOU_intro. iFrame "PH OB1".
             iSplitR "CP".
             2: { iExists _. iFrame. }
             iNext. iAccu. }

        iIntros "[? (%π3 & %π4 & PH1 & OB1 & PH3 & OB2 & [%LT3 %LT4])]".
        Unshelve. 2: exact ∅.
        rewrite difference_diag_L. rewrite intersection_idemp_L.

        iSplitR "POST OB1".
        2: { by iApply "POST". }
        
        apply strict_include in LT4. iRename "PH3" into "PH".
        wp_bind (_ + _)%E. rewrite Nat2Z.inj_0.
        iDestruct (cp_mul_weaken with "CPS") as "CPS"; [apply LT4| reflexivity| ].
        do 2 pure_step_cases.
        replace (0 + 1)%Z with 1%Z; [| done].
        replace 1%Z with (Z.of_nat 1%nat); [| done].         
        iApply (thread_spec_wrapper with "[-]").
        { apply odd_thread_resource. }
        2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
        simpl. 
        iDestruct (cp_mul_take with "CPS2'") as "[CPS2 ?]".
        rewrite {1 3}B1. simpl.
        rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
        iFrame "PH #∗".
        iSplitL "CPS2"; (iApply cp_mul_weaken; [| reflexivity| by iFrame]).
        all: etrans; eauto. 
        Unshelve. exact #().
      - simpl in SIGS_LEN. 
        destruct sigs as [| ]; try by (simpl in SIGS_LEN; lia).

        simpl. 

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ'). iApply (MU__f_wand with "[-CP PH OB]").
        2: { iApply ohe_obls_AMU__f; [done| ].
             iApply BOU_AMU__f.
             iApply BOU_intro. iFrame "PH OB".
             iSplitR "CP".
             2: { iExists _. iFrame. }
             iNext. iAccu. }

        iIntros "[? (%π1 & %π2 & PH1 & OB1 & PH3 & OB2 & [%LT1 %LT2])]".
        Unshelve. 2: exact ∅.

        rewrite difference_diag_L. rewrite intersection_idemp_L.
        iSplitL "RE CPS2 CPS_FORK PH3 OB2".
        { iApply (thread_spec_wrapper with "[-]").
          { apply even_thread_resource. }
          2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
          rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
          rewrite Nat.sub_0_r. iFrame "PH3 #∗".
          iSplitL "CPS2"; (iApply cp_mul_weaken; [| reflexivity| by iFrame]); apply LT2. }

        apply strict_include in LT1. iRename "PH1" into "PH".
        iDestruct (cp_mul_weaken with "CPS") as "CPS"; [apply LT1| reflexivity| ].
        wp_bind (Rec _ _ _)%V. pure_step.
        iApply wp_value. pure_step.

        iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
        iApply sswp_MUf_wp. iIntros (τ''). iApply (MU__f_wand with "[-CP PH OB1]").
        2: { iApply ohe_obls_AMU__f; [done| ].
             iApply BOU_AMU__f. 
             iApply BOU_intro. iFrame "PH OB1".
             iSplitR "CP".
             2: { iExists _. iFrame. }
             iNext. iAccu. }

        iIntros "[? (%π3 & %π4 & PH1 & OB1 & PH3 & OB2 & [%LT3 %LT4])]".
        Unshelve. 2: exact ∅.
        rewrite difference_diag_L. rewrite intersection_idemp_L.

        iSplitR "POST OB1".
        2: { by iApply "POST". }
        
        apply strict_include in LT4. iRename "PH3" into "PH".
        wp_bind (_ + _)%E. rewrite Nat2Z.inj_0.
        iDestruct (cp_mul_weaken with "CPS") as "CPS"; [apply LT4| reflexivity| ].
        do 2 pure_step_cases.
        replace (0 + 1)%Z with 1%Z; [| done].
        replace 1%Z with (Z.of_nat 1%nat); [| done].         
        replace 0%Z with (Z.of_nat 0%nat); [| done].         
        iApply (thread_spec_wrapper with "[-]").
        { apply odd_thread_resource. }
        2: { iNext. iIntros (v) "OB". by iApply NO_OBS_POST. }
        simpl. 
        rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _)); [| lia].
        rewrite {1 3}B0. simpl.  
        iFrame "PH #∗".
        iSplitL "CPS2'"; (iApply cp_mul_weaken; [| reflexivity| by iFrame]).
        all: etrans; eauto.
        Unshelve. exact #().
    Qed.
      
  End MainProof.

End EoFin.
