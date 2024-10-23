From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl excl_auth.
(* From iris.base_logic Require Export gen_heap. *)
(* From trillium.program_logic Require Export weakestpre adequacy ectx_lifting. *)
From iris.base_logic.lib Require Import invariants.
From trillium.fairness Require Import locales_helpers utils.
From trillium.fairness.lawyer Require Import program_logic sub_action_em.
From trillium.fairness.lawyer.obligations Require Import obligations_model obls_utils obligations_resources obligations_logic obligations_em.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


Close Scope Z.

(* Definition EODegree n := Fin.t (S n). *)
(* Definition EOLevel n := Fin.t (S n). *)
Definition EODegree n := { i | i < n }. 
Definition EOLevel n := { i | i < n }.


Definition bounded_nat_le n (x y: { i | i < n }) := `x <= `y. 

(* TODO: move? *)
Instance nat_bounded_PO n: PartialOrder (bounded_nat_le n).
Proof using.
  split.
  - split.
    + red. intros. red. reflexivity.
    + red. intros [??] [??] [??]. rewrite /bounded_nat_le. simpl. lia.
  - red. intros [??] [??]. rewrite /bounded_nat_le. simpl.
    intros. assert (x = x0) by lia. subst.
    assert (l0 = l) by apply Nat.lt_pi. congruence.
Qed. 


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

  Let EOLevelOfe := sigO (fun i => i < LIM).
  Let EODegreeOfe := sigO (fun i => i < NUM_DEG).

  Instance EO_lvl_LeibnizEquiv: LeibnizEquiv EOLevelOfe.
  Admitted. 

  (* Definition EO_EM := @ObligationsEM EODegreeOfe EOLevelOfe _ _ _ heap_lang _ _ _ EO_OP.  *)
  (* Context `{hGS: @heapGS Σ _ EO_EM}. *)
  (* Let oGS : ObligationsGS EO_OP Σ := heap_fairnessGS (heapGS := hGS). *)

  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{hGS: @heapGS Σ _ EM}.

  (* Let OAM := ObligationsAM OP.  *)
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
      (* (* TODO: abstract over signal id type? *) *)
      (* eofin_sigs :> inG Σ (excl_authR natO); *)
      (* eofin_toks :> inG Σ (exclR unitO); *)
      eofin_sigs :> inG Σ (authUR (gmapUR nat (agreeR SignalId)));
  }.
  
  Class EoFinG Σ := {
      eofin_PreG :> EoFinPreG Σ;
      eofin_even: gname; eofin_odd: gname;
      eofin_smap: gname;
  }.

  Section Threads.
    Context `{EoFinG Σ}.
    
    Definition thread_auth γ (n: nat): iProp Σ :=
      own γ (●E n).

    Definition thread_frag γ (n: nat): iProp Σ :=
      own γ (◯E n).

    Lemma thread_agree γ n1 n2:
      thread_auth γ n1-∗ thread_frag γ n2 -∗ ⌜ n1 = n2 ⌝. 
    Proof.
      rewrite /thread_frag /thread_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".      
      iDestruct (own_valid with "H") as "%Hval".
      iPureIntro. apply excl_auth_agree_L in Hval. set_solver. 
    Qed.

    Lemma thread_update γ n1 n2 n':
      thread_auth γ n1 -∗ thread_frag γ n2 ==∗
      thread_auth γ n' ∗ thread_frag γ n'. 
    Proof.
      rewrite /thread_frag /thread_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".
      rewrite -!own_op. iApply own_update; [| by iFrame].
      apply excl_auth_update.
    Qed.

    Definition lvl2nat {X} (l: EOLevel X): nat := proj1_sig l. 

    (* Definition nth_lvl (n: nat) {M: nat} (BOUND: M < LIM) (LE: n <= M): EOLevel LIM := *)
    (*   exist _ n (Nat.le_lt_trans _ _ _ LE BOUND). *)

    (* Definition nth_lvl' (n: nat) {M: nat} (BOUND: M < LIM) (LE: n < M): EOLevel LIM := *)
    (*   (* exist _ n (Nat.lt_trans _ _ _ LE BOUND). *) *)
    (*   nth_lvl n BOUND (Nat.lt_le_incl _ _ LE).  *)

    Definition nth_deg (n: nat) (LT: n < NUM_DEG): EODegree NUM_DEG :=
      exist _ n LT. 

    Let d0 := nth_deg 0 (Nat.lt_0_succ _). 
    Let d1 := nth_deg 1 (proj1 (Nat.succ_lt_mono _ _) (Nat.lt_0_succ _)).

    Lemma d01_lt: deg_lt _ d0 d1.
    Proof.
      red. apply strict_spec_alt. split; try done.
      subst d0 d1. simpl. red. simpl. lia. 
    Qed.

    Ltac BMU_burn_cp :=
      iApply BMU_intro;
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]";
      iSplitR "CP";
      [| do 2 iExists _; iFrame; iPureIntro; reflexivity]. 

    Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS _ EM _ (↑ nroot)}.

    Ltac pure_step :=
      iApply sswp_MU_wp; [done| ];
      iApply sswp_pure_step; [done| ]; simpl;
      iNext;
      iApply OBLS_AMU; [by rewrite nclose_nroot| ];
      iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH";
      BMU_burn_cp
    . 

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
          thread_auth eofin_even
            (if Nat.even n then n else n + 1) ∗
          thread_auth eofin_odd
            (if Nat.odd n then n else n + 1) ∗
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

    Definition ith_sig_in i s (smap: gmap nat SignalId):
      ⊢ ith_sig i s -∗ own eofin_smap (● (to_agree <$> smap: gmapUR nat (agreeR SignalId))) -∗ 
         ⌜ smap !! i = Some s ⌝.
    Proof.
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

      apply fmap_Some_equiv in ITH as (?&?&?).
      rewrite H1. apply to_agree_inj in H2. by rewrite H2.
    Qed.

    (* TODO: move *)
    Global Instance BMU_proper:
      Proper (equiv ==> eq ==> eq ==> equiv ==> equiv) (BMU EO_OP (oGS := oGS)).
    Proof using. solve_proper. Qed. 

    Lemma smap_create_ep i K n s smap π τ:
      ⊢ ith_sig i s -∗ 
         smap_repr K n smap -∗ 
         cp EO_OP π d1 (H3 := oGS) -∗
         th_phase_ge EO_OP τ π (H3 := oGS) -∗
         BMU EO_OP ∅ τ 1 
           (ep EO_OP s π d0 (H3 := oGS) ∗ smap_repr K n smap ∗
            th_phase_ge EO_OP τ π (H3 := oGS) ∗ ith_sig i s) (oGS := oGS).
    Proof using.
      iIntros "ITH SR CP PH".
      rewrite /smap_repr. iDestruct "SR" as "(AUTH & %DOM & SIGS)".
      iDestruct (ith_sig_in with "[$] [$]") as "%ITH".
      rewrite {2 5}(map_split smap i) ITH. simpl. rewrite big_sepM_union.
      2: { apply map_disjoint_singleton_l_2. apply lookup_delete. }
      iDestruct "SIGS" as "[SIG SIGS]". rewrite big_sepM_singleton.
      rewrite {1}/ex_ith_sig. iDestruct "SIG" as "(%l & SIG & %LVLi)".
      iApply OU_BMU.
      iDestruct (create_ep_upd with "[$] [$] [$]") as "OU"; [apply d01_lt| ].
      iApply (OU_wand with "[-OU]"); [| by iFrame].
      iIntros "(EP & SIG & PH)".
      iApply BMU_intro. iFrame. iSplitR; [done| ].
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

    Lemma BMU_smap_restore
  (τ : locale heap_lang)
  (B : nat)
  (BOUND : B < LIM)
  (s : SignalId)
  (m : nat)
  (smap : gmap nat SignalId)
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
           even_res a ∗ cp_mul EO_OP π d1 (S (B - a)) (H3 := oGS) ∗ 
           th_phase_ge EO_OP τ π (H3 := oGS) ∗
           (if a <? B
            then ∃ s0 : SignalId, ith_sig a s0 ∗ obls EO_OP τ {[s0]} (H3 := oGS)
            else obls EO_OP τ ∅ (H3 := oGS)) -∗
           ▷ (∀ x : base_lit, obls EO_OP τ ∅ (H3 := oGS) -∗ Φ #x) -∗
           WP thread_prog #l #a #B @τ {{ v, Φ v }}. 

    Lemma thread_advance τ (l: loc) B (BOUND : B < LIM) π
      (Φ: val → iPropI Σ)
      (m: nat)
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
        cp_mul EO_OP π d1 (B - (if Nat.even m then m else m + 1)) (H3 := oGS) -∗
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
      
      iDestruct "SR" as "(SM & %DOM & SIGS)". 
      iDestruct (ith_sig_in with "[$] [$]") as %IN. 
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
      { apply d01_lt. }
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
        iPoseProof (smap_create_ep with "[$] [$] [$] [$]") as "BMU"; eauto.
        iApply (BMU_weaken with "[-BMU] [$]"); [lia| set_solver| ].
        iIntros "(EP & SR & PH & SN)". 

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
