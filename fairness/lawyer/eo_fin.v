From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl excl_auth.
(* From iris.base_logic Require Export gen_heap. *)
(* From trillium.program_logic Require Export weakestpre adequacy ectx_lifting. *)
From iris.base_logic.lib Require Import invariants.
From trillium.fairness Require Import locales_helpers utils.
From trillium.fairness.lawyer Require Import obligations_model obls_utils obligations_resources program_logic.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


Close Scope Z.
Open Scope nat. 

(* TODO: move *)
Section Arithmetic.

  Lemma even_succ_negb n: Nat.even (S n) = negb $ Nat.even n.
  Proof.
    rewrite Nat.even_succ.
    rewrite -Nat.negb_even.
    done. 
  Qed.

  (* Lemma odd_succ_negb n: Nat.odd (S n) = negb $ Nat.odd n. *)
  (* Proof. by rewrite Nat.odd_succ Nat.negb_odd. Qed. *)

  (* Lemma even_plus1_negb n: Nat.even (n + 1) = negb $ Nat.even n. *)
  (* Proof. by rewrite Nat.add_1_r even_succ_negb. Qed.  *)

  (* Lemma odd_plus1_negb n: Nat.odd (n + 1) = negb $ Nat.odd n. *)
  (* Proof. by rewrite Nat.add_1_r odd_succ_negb. Qed. *)

  (* Lemma even_odd_False n : Nat.even n → Nat.odd n → False. *)
  (* Proof. *)
  (*   intros Heven Hodd. rewrite -Nat.negb_odd in Heven. *)
  (*   apply Is_true_true_1 in Heven. *)
  (*   apply Is_true_true_1 in Hodd. *)
  (*   by rewrite Hodd in Heven. *)
  (* Qed. *)
  
  (* Lemma even_not_odd n : Nat.even n → ¬ Nat.odd n. *)
  (* Proof. intros Heven Hodd. by eapply even_odd_False. Qed. *)
  
  (* Lemma odd_not_even n : Nat.odd n → ¬ Nat.even n. *)
  (* Proof. intros Heven Hodd. by eapply even_odd_False. Qed. *)
  
  Lemma even_or_odd n: Nat.even n \/ Nat.odd n.
  Proof. 
    destruct (decide (Nat.even n)) as [| O]; auto.
    apply negb_prop_intro in O. rewrite Nat.negb_even in O. tauto.
  Qed.

End Arithmetic.

(* Definition EODegree n := Fin.t (S n). *)
(* Definition EOLevel n := Fin.t (S n). *)
Definition EODegree n := { i | i < n }. 
Definition EOLevel n := { i | i < n }. 

Section EoFin.
  Context (LIM: nat).
  Let MAX_OBL_STEPS := 10.
  Let NUM_DEG := 5.
  
  Instance EO_OP: ObligationsParams (EODegree NUM_DEG) (EOLevel LIM) (locale heap_lang) MAX_OBL_STEPS.
  Proof using.
    esplit; try by apply _.
    - rewrite /EODegree.
      exact (fun d1 d2 => proj1_sig d1 < proj1_sig d2).
    - exact (fun d1 d2 => proj1_sig d1 < proj1_sig d2).
  Defined.

  Let OM := ObligationsModel EO_OP.

  Let EOLevelOfe := sigO (fun i => i < LIM).
  Let EODegreeOfe := sigO (fun i => i < NUM_DEG). 

  Instance foo: LeibnizEquiv EOLevelOfe.
  Admitted. 
  
  Let EM := @ObligationsEM EODegreeOfe EOLevelOfe _ _ _ heap_lang _ _ _ EO_OP. 

  Context `{hGS: @heapGS Σ _ EM}.
  Let oGS : ObligationsGS EO_OP Σ := heap_fairnessGS (heapGS := hGS).

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

    Ltac MU_burn_cp :=
      iApply (BMU_MU with "[-PH] [$]"); [by eauto| ]; iIntros "PH";
      iApply BMU_intro;
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]";
      iSplitR "CP";
      [| do 2 iExists _; iFrame; iPureIntro; reflexivity]. 

    Ltac pure_step :=
      iApply sswp_MU_wp; [done| ];
      iApply sswp_pure_step; [done| ]; simpl;
      iNext;
      MU_burn_cp
    . 

    Ltac pure_step_cases := pure_step || (iApply wp_value; []) || wp_bind (RecV _ _ _ _)%V.
    Ltac pure_steps := repeat (pure_step_cases; []).

    Definition smap_repr K n (smap: gmap nat SignalId): iProp Σ :=
      own eofin_smap (● (to_agree <$> smap: gmapUR nat (agreeR SignalId))) ∗
      ⌜ dom smap = set_seq 0 K ⌝ ∗
      ([∗ map] i ↦ s ∈ smap, ∃ l, sgn EO_OP s l (Some $ Nat.ltb i n) (H3 := oGS) ∗ ⌜ lvl2nat l = i ⌝). 


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
 
    Lemma thread_spec τ n l M (BOUND: M < LIM) π s:
      {{{ eofin_inv l M BOUND ∗ even_res n ∗
          cp_mul EO_OP π d0 100 (H3 := oGS) ∗ th_phase_ge EO_OP τ π (H3 := oGS) ∗
          ith_sig n s ∗ 
          obls EO_OP τ (if (Nat.ltb n M) then {[ s ]} else ∅) (H3 := oGS) }}}
        thread_prog #l #n #M @ τ
      {{{ x, RET #x; obls EO_OP τ ∅ (H3 := oGS) }}}.
    Proof.
      iIntros (Φ). iIntros "(#INV & TH & CPS & PH & SN & OB) POST".
      rewrite /thread_prog.

      wp_bind (RecV _ _ _ _)%V.
      pure_steps.
      wp_bind (_ ≤ _)%E.
      pure_step.

      fold thread_prog. 

      destruct (Nat.le_gt_cases M n).
      { rewrite bool_decide_true; [| lia].
        pure_steps. iApply "POST".
        rewrite (proj2 (Nat.ltb_ge _ _)); done. }
      
      rewrite bool_decide_false; [| lia].
      rewrite (proj2 (Nat.ltb_lt _ _)); [| done]. 
      pure_steps.
      wp_bind (_ + _)%E. pure_steps.  
      wp_bind (CmpXchg _ _ _)%E.

      iApply wp_atomic. 
      iInv "INV" as ">inv" "CLOS". iModIntro.
      rewrite {1}/eofin_inv_inner.
      iDestruct "inv" as (m smap) "(L & EVEN & ODD & SM & %DOM & SIGS)".
      iDestruct (thread_agree with "EVEN [$]") as %<-.
      destruct (even_or_odd m) as [EVEN | ODD].
      - pose proof (Is_true_true_1 _ EVEN) as E.
        rewrite E.
        assert (Nat.odd m = false) as O by admit.
        rewrite O. 

        iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_suc with "[$]"); try done.
        { econstructor. done. }
        iNext. iIntros "L".

        iDestruct (ith_sig_in with "[$] [$]") as %IN. 
        iDestruct (big_sepM_delete with "SIGS") as "[SG SIGS]"; eauto.
        iDestruct "SG" as (lm) "(SG & %LVL)".
        rewrite Nat.ltb_irrefl. 

        iApply (BMU_MU with "[-PH] [$]"); [by eauto| ]; iIntros "PH". 

        iApply OU_BMU.
        iDestruct (OU_set_sig with "OB [SG]") as "OU".
        { apply elem_of_singleton. reflexivity. }
        { by iFrame. }
        iApply (OU_wand with "[-OU]"); [| done]. iIntros "(SIG & OBLS)".
        rewrite (subseteq_empty_difference_L {[ s ]}); [| done].

        (* iDestruct (cp_mul_take with "CPS") as "[CPS CP]".  *)
        iAssert (BMU EO_OP (⊤ ∖ ↑nroot.@"eofin") τ 1
                   (⌜ M <= m + 2 ⌝ ∗ obls EO_OP τ ∅ ∗ smap_repr (min M (m + 2)) (m + 1) smap ∨
                    ⌜ m + 2 < M ⌝ ∗ smap_repr (min M (m + 2)) (m + 1) smap ∗ ∃ s' lm', ith_sig (m + 2) s' ∗ obls EO_OP τ {[ s' ]} ∗ sgn EO_OP s' lm' (Some false) ∗ ⌜ lvl2nat lm' = (m + 2)%nat ⌝))%I with "[OBLS SIGS SIG SM]" as "BMU".
        { destruct (Nat.le_gt_cases M (m + 2)).
          { rewrite PeanoNat.Nat.min_l in DOM; [| done]. 
            iApply BMU_intro. iLeft. iFrame.
            iSplitR; [done| ]. iSplitR.
            { iPureIntro. rewrite PeanoNat.Nat.min_l; auto. }
            rewrite (big_sepM_delete _ smap); eauto.
            iSplitL "SIG".
            { iExists _. rewrite (proj2 (Nat.ltb_lt _ _)); [| lia]. 
              iFrame. done. }
            iApply (big_sepM_impl with "[$]"). iModIntro.
            iIntros (???) "(%&?&?)". iExists _. iFrame.
            assert ((k <? m) = (k <? m + 1) \/ k = m).
            { destruct (decide (k = m)); [tauto| ]. left.
              destruct (k <? m).
              - rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _)). ; [| lia]. 
              split. 
            
          iApply OU_BMU.
          set (lm' := exist _ (m + 2) H1: EOLevel M).
          iDestruct (OU_create_sig with "OBLS") as "FOO".
          iApply (OU_wand with "[-FOO]"); [| by iFrame].
          iIntros "(%s' & SG & OBLS)". rewrite union_empty_l_L.
          iApply BMU_intro. iRight. iSplitR; [done| ].
          

        
                  
        

        iMod ("CLOS" with "P2 EVEN ODD") as "_"

      
        iMod (thread_update _ _ _ (m + 2) with "EVEN [$]") as "[EVEN TH]". 

      



  End Threads.

End EoFin.
