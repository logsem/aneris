From iris.proofmode Require Import tactics coq_tactics.
From iris.algebra Require Import auth gmap gset excl excl_auth.
(* From iris.base_logic Require Export gen_heap. *)
(* From trillium.program_logic Require Export weakestpre adequacy ectx_lifting. *)
From iris.base_logic.lib Require Import invariants.
From trillium.fairness Require Import locales_helpers utils.
From trillium.fairness.lawyer Require Import obligations_model obls_utils obligations_resources program_logic.
From trillium.fairness.heap_lang Require Export heap_lang_defs tactics notation sswp_logic locales_helpers_hl.


Close Scope Z.

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
      eofin_threads_PreG :> inG Σ (excl_authR (prodR natO positiveO));
      (* TODO: abstract over signal id type? *)
      eofin_sigs :> inG Σ (excl_authR natO);
      eofin_toks :> inG Σ (exclR unitO);
  }.
  
  Class EoFinG Σ := {
      eofin_PreG :> EoFinPreG Σ;
      eofin_even: gname; eofin_odd: gname; 
      eofin_p1: gname; eofin_p2: gname;
      eofin_tok_p1: gname; eofin_tok_p2: gname;
  }.

  Section Threads.
    Context `{EoFinG Σ}.
    
    Definition thread_auth γ (n: nat) (g: gname): iProp Σ :=
      own γ (●E (n, g)).

    Definition thread_frag γ (n: nat) (g: gname): iProp Σ :=
      own γ (◯E (n, g)).

    Lemma thread_agree γ n1 g1 n2 g2:
      thread_auth γ n1 g1 -∗ thread_frag γ n2 g2 -∗ ⌜ n1 = n2 /\ g1 = g2 ⌝. 
    Proof.
      rewrite /thread_frag /thread_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".      
      iDestruct (own_valid with "H") as "%Hval".
      iPureIntro. apply excl_auth_agree_L in Hval. set_solver. 
    Qed.

    Lemma thread_update γ n1 g1 n2 g2 n' g':
      thread_auth γ n1 g1 -∗ thread_frag γ n2 g2 ==∗
      thread_auth γ n' g' ∗ thread_frag γ n' g'. 
    Proof.
      rewrite /thread_frag /thread_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".
      rewrite -!own_op. iApply own_update; [| by iFrame].
      apply excl_auth_update.
    Qed.

    Definition nth_lvl (n: nat) {M: nat} (BOUND: M < LIM) (LE: n <= M): EOLevel LIM :=
      exist _ n (Nat.le_lt_trans _ _ _ LE BOUND).

    Definition nth_lvl' (n: nat) {M: nat} (BOUND: M < LIM) (LE: n < M): EOLevel LIM :=
      (* exist _ n (Nat.lt_trans _ _ _ LE BOUND). *)
      nth_lvl n BOUND (Nat.lt_le_incl _ _ LE). 

    Definition nth_deg (n: nat) (LT: n < NUM_DEG): EODegree NUM_DEG :=
      exist _ n LT. 

    Definition sgn_p_auth γ g: iProp Σ := own γ (●E g).
    Definition sgn_p_frag γ g: iProp Σ := own γ (◯E g).

    Definition thread_tok γ := own γ (Excl ()). 

    Definition eofin_inv_inner l M (BOUND: M < LIM) : iProp Σ :=
      ∃ (n: nat), 
          l ↦ #n ∗
          thread_auth eofin_even
            (if Nat.even n then n else n + 1)
            (if Nat.even n then eofin_p1 else eofin_p2) ∗
          thread_auth eofin_odd
            (if Nat.odd n then n else n + 1)
            (if Nat.odd n then eofin_p1 else eofin_p2) ∗
          (∀ (LE: n + 1 <= M), ∃ sid, sgn EO_OP sid (nth_lvl (n + 1) BOUND LE) (Some false) (H3 := oGS) ∗ (∃ c, sgn_p_auth eofin_p1 c ∗ (sgn_p_frag eofin_p1 c ∨ ⌜ c = sid ⌝ ∗ thread_tok eofin_tok_p1))) ∗
          (∀ (LE: n + 2 <= M), ∃ sid, sgn EO_OP sid (nth_lvl (n + 2) BOUND LE) (Some false) (H3 := oGS) ∗ (∃ c, sgn_p_auth eofin_p2 c ∗ (sgn_p_frag eofin_p2 c ∨ ⌜ c = sid ⌝ ∗ thread_tok eofin_tok_p2)))
    .

    Definition eofin_inv l M BOUND: iProp Σ :=
      inv (nroot .@ "eofin") (eofin_inv_inner l M BOUND).

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

    Lemma add1_helper {x y: nat}: x < y -> x + 1 <= y.
    Proof. lia. Qed.

    Definition even_res n: iProp Σ :=
      ∃ g, thread_frag eofin_even n g ∗ thread_tok g. 

    Lemma thread_spec τ n l M (BOUND: M < LIM) π:
      {{{ eofin_inv l M BOUND ∗ even_res n ∗
          cp_mul EO_OP π d0 100 (H3 := oGS) ∗ th_phase_ge EO_OP τ π (H3 := oGS) ∗
          ((∀ (LT: n < M), ∃ s, obls EO_OP τ {[ s ]} (H3 := oGS) ∗ sgn EO_OP s (nth_lvl (n + 1) BOUND (add1_helper LT)) None (H3 := oGS)) ∧
           (⌜ n >= M⌝ -∗ obls EO_OP τ ∅ (H3 := oGS)))
      }}}
        thread_prog #l #n #M @ τ
      {{{ x, RET #x; obls EO_OP τ ∅ (H3 := oGS) }}}.
    Proof.
      iIntros (Φ). iIntros "(#INV & TH & CPS & PH & OB) POST".
      rewrite /thread_prog.

      wp_bind (RecV _ _ _ _)%V.
      pure_steps.
      wp_bind (_ ≤ _)%E.
      pure_step. 

      destruct (Nat.le_gt_cases M n).
      { rewrite bool_decide_true; [| lia].
        pure_steps. iApply "POST".
        iApply "OB". done. }
      
      rewrite bool_decide_false; [| lia].
      iDestruct (bi.and_elim_l with "OB") as "OB".
      iSpecialize ("OB" $! ltac:(done)). iDestruct "OB" as (s) "[OB SIG]".
      pure_steps.
      wp_bind (_ + _)%E. pure_steps.  
      wp_bind (CmpXchg _ _ _)%E.

      iApply wp_atomic. 
      iInv "INV" as ">inv" "CLOS". iModIntro.
      rewrite {1}/eofin_inv_inner.
      iDestruct "inv" as (m) "(L & EVEN & ODD & P1 & P2)".
      iDestruct "TH" as (g) "[EV TOK]". 
      iDestruct (thread_agree with "EVEN [$]") as %[<- <-].
      destruct (even_or_odd m) as [EVEN | ODD].
      - pose proof (Is_true_true_1 _ EVEN) as E.
        rewrite {1 2 3 6 7 8 9 10 11}E.

        iApply sswp_MU_wp; [done| ]. 
        iApply (wp_cmpxchg_suc with "[$]"); try done.
        { econstructor. done. }
        iNext. iIntros "L".

        iApply (BMU_MU with "[-PH] [$]"); [by eauto| ]; iIntros "PH". 

        iApply OU_BMU.
        iDestruct (OU_set_sig with "OB [SIG]") as "OU".
        { apply elem_of_singleton. reflexivity. }
        { iApply "SIG". 
        iApply (OU_wand with "[-OU]"); [| done].
        iIntros "(SIG & OBLS)".

        iMod ("CLOS" with "P2 EVEN ODD") as "_"

      

      



  End Threads.

End EoFin.
