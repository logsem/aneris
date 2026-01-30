From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From lawyer.examples.ticketlock Require Import obls_atomic releasing_lock.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


(** With the current proof, we don't require anything from Σ before OM is instantiated.
    However, we keep this preG/G pattern for uniformness. *)
Class ClientPreG (Σ: gFunctors) := { }.

Class ClientG Σ := {
    cl_PreG :: ClientPreG Σ;
}.

Section MotivatingClient.
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}. 

  Context (RFL: ReleasingFairLock).

  Context (l__f: Level).
  Hypothesis
    (LVL_ORDf: forall l, l ∈ rfl_lvls RFL -> lvl_lt l l__f)
  .

  Definition left_thread: val :=
    λ: "lk" "flag",
      (rfl_acquire RFL) "lk" ;;
      "flag" <- #true ;;
      (rfl_release RFL) "lk"
    .

    Definition right_thread_iter: val :=
      λ: "lk" "flag" "c",
        (rfl_acquire RFL) "lk" ;;
        "c" <- !"flag" ;;
        (rfl_release RFL) "lk"
    .

    Definition right_thread_rep: val :=
      rec: "right" "lk" "flag" "c" :=
        right_thread_iter "lk" "flag" "c" ;;
        if: (!"c" = #true) then #() else "right" "lk" "flag" "c"
    .

    Definition right_thread: val :=
      λ: "lk" "flag",
        let: "c" := ref #false in
        right_thread_rep "lk" "flag" "c"
    .

  Definition client_prog: val :=
    λ: <>,
      let: "flag" := ref #false in
      let: "lk" := rfl_newlock RFL #() in
      (Fork (left_thread "lk" "flag") ;;
       Fork (right_thread "lk" "flag")).

  Context (d0 d__r: Degree).
  Hypothesis (LThm: deg_lt (rfl_d RFL) d__r).
  Hypothesis (LT0m: deg_lt d0 (rfl_d RFL)).

  Definition c__cl: nat := 4.
  Definition MAX_EXC := 70.
  Definition client_LB := max_list [MAX_EXC + 2; rfl_sb_fun RFL c__cl].  
  Hypothesis (LS_LB: client_LB <= LIM_STEPS).

  Definition P__lock' flag s__f (b: bool): iProp Σ :=
      flag ↦ #b ∗ sgn s__f l__f (Some b).

  Section AfterInit.
    Context {CL: ClientG Σ}.
    Context {RFLG: rfl_G RFL Σ}.

    Definition P__lock flag s__f (b: bool): iProp Σ := P__lock' flag s__f b. 

    Definition client_inv lk flag sf: iProp Σ :=
      rfl_is_lock RFL lk c__cl (∃ b, P__lock flag sf b) (rfl_G0 := RFLG).

    Global Instance client_inv_pers lk flag sf: Persistent (client_inv lk flag sf).
    Proof using. apply rfl_is_lock_pers. Qed. 

    Lemma acquire_left τ (lk: val) flag s__f π:
      {{{ client_inv lk flag s__f ∗
          obls τ {[ s__f ]} ∗ th_phase_eq τ π ∗
          cp π (rfl_d RFL) ∗
          sgn s__f l__f None
      }}}
        rfl_acquire RFL lk @ τ
      {{{ v, RET v; ∃ s__o l__o b, obls τ {[ s__f; s__o ]} ∗
                          th_phase_eq τ π ∗
                          P__lock flag s__f b ∗ rfl_locked RFL s__o (rfl_G0 := RFLG) ∗ 
                          ⌜ s__o ≠ s__f ⌝ ∗ ⌜ l__o ∈ rfl_lvls RFL ⌝ }}}.
    Proof using All.
      iIntros (Φ).
      iIntros "(#INV & OB & PH & CPm & #SF') POST".

      iApply (rfl_acquire_spec with "[-POST]").
      { iFrame "#∗". 
        iApply big_opS_singleton. iExists _. iFrame "SF'".
        iPureIntro. set_solver. }
      all: try by eauto.
      
      iNext. iIntros (?) "(%s__o & %l__o & OB & SGNo & %ADD & %LVLo & PH & (%f & P) & LOCKED)".
      
      rewrite /P__lock. iDestruct "P" as "[FLAG ?]". 
      iApply "POST". do 3 iExists _. iFrame.
      iPureIntro. split; [set_solver| ]. apply LVLo. 
    Qed.

    Lemma release_left (lk: val) τ s__o flag s__f π
      :
      {{{ client_inv lk flag s__f ∗
          obls τ {[ s__o ]} ∗
          th_phase_eq τ π ∗ cp π (rfl_d RFL) ∗
          flag ↦ #true ∗ sgn s__f l__f (Some true) ∗
          rfl_locked RFL s__o (rfl_G0 := RFLG) }}}
        (rfl_release RFL) lk @ τ
      {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π }}}.
    Proof using All.
      iIntros (Φ).
      iIntros "(#INV & OB & PH & CPm & FLAG & SGNf & LOCKED) POST".
      iDestruct (sgn_get_ex with "[$]") as "[SGNf #SGNf']".
      
      rewrite -(union_empty_l_L {[ _ ]}). iApply (rfl_release_spec with "[-POST]").
      2: iFrame "OB".
      3: by iApply "POST".
      all: try by eauto. 
      iFrame "#∗".

      iIntros (?) "%QQ PH OB".
      iApply BOU_intro. simpl.

      iSplitL "FLAG SGNf".
      { iExists _. iFrame. } 

      iIntros "PH'". simpl.
      iDestruct (th_phase_frag_combine' with "[$PH $PH']") as "foo"; [done| by iFrame].      
    Qed.

    Lemma first_step e1 τ π R n d d'
      (BOUND: n + 2 <= LIM_STEPS)
      (NVAL: language.to_val e1 = None)
      (DEG_LT: deg_lt d' d):
      th_phase_eq τ π -∗ cp π d -∗
      sswp NotStuck ⊤ e1 (fun e2 => cp_mul π d' n -∗ exc_lb (S n) -∗ th_phase_eq τ π -∗ WP e2 @τ {{ v, R v }}) -∗
      WP e1 @ τ {{ R }}.
    Proof using.
      clear -BOUND DEG_LT NVAL.
      iIntros "PH CP FIN".
      iApply sswp_MU_wp; [done| ].
      iApply (sswp_wand with "[-FIN]"); [| by iFrame].
      simpl. iIntros (e2) "FIN".
      MU_by_BOU.
      iApply (BOU_wand with "[FIN PH]").
      2: { simpl. iApply (BOU_lower _ (S (S n))); [lia| ].
           iApply (first_BOU with "[$]"). 
           apply DEG_LT. }
      iIntros "(CPS & #EXC)".
      burn_cp_after_BOU.
      iApply ("FIN" with "[$] [$] [$]").
    Qed.

    Theorem left_thread_spec (lk: val) τ flag s__f π:
      {{{ client_inv lk flag s__f ∗ 
          obls τ {[ s__f ]} ∗ th_phase_eq τ π ∗
          cp_mul π (rfl_d RFL) 3 ∗
          sgn s__f l__f None
      }}}
        left_thread lk #flag @ τ
      {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π }}}.
    Proof using All.
      iIntros (Φ).
      iIntros "(#LOCK & ?&PH&CPSm&?) POST".
      rewrite /left_thread.

      pure_step_cases.
      split_cps "CPSm" 1. rewrite -cp_mul_1.
      iApply (first_step with "[$] [$]").
      { try_solve_bounds. use_rfl_fl_sb. }
      { done. }
      { eauto. }
      iApply sswp_pure_step; [done| ].
      iIntros "!> CPS #EXC PH". simpl.
      pure_steps.

      split_cps "CPSm" 1.
      wp_bind (rfl_acquire _ _)%E.
      iApply (acquire_left with "[-CPS CPSm POST]").
      { iFrame "#∗". by rewrite cp_mul_1. }
      iNext. iIntros (v) "(% & % & % & OB & PH & P & LOCKED & % & %LVLo)".
      rewrite /P__lock. iDestruct "P" as "[FLAG SGNf]".

      wp_bind (Rec _ _ _)%E. pure_steps.
      wp_bind (_ <- _)%E.
      iApply sswp_MU_wp.
      { done. }
      iApply (wp_store with "[$]"). iIntros "!> FLAG".
      MU_by_BOU. iMod (OU_set_sig with "OB SGNf") as "[SGNf OB]".
      { set_solver. }
      { try_solve_bounds. }
      BOU_burn_cp.
      pure_steps.

      wp_bind (Rec _ _ _)%E. pure_steps.
      replace ({[s__f; s__o]} ∖ {[s__f]}) with ({[ s__o ]}: gset _) by set_solver. 
      iApply (release_left with "[-POST]").
      { iFrame "#∗". 
        iDestruct (cp_mul_take with "CPS") as "[??]".
        by iApply cp_mul_1. }
      iNext. done.
    Qed.

    Lemma acquire_right τ (lk: val) flag s__f π:
      {{{ client_inv lk flag s__f ∗
          obls τ ∅ ∗ th_phase_eq τ π ∗
          cp π (rfl_d RFL)
      }}}
        rfl_acquire RFL lk @ τ
      {{{ v, RET v; ∃ s__o f, obls τ {[ s__o ]} ∗ th_phase_eq τ π ∗
                          P__lock flag s__f f ∗ rfl_locked RFL s__o (rfl_G0 := RFLG)
      }}}.
    Proof using All.
      iIntros (Φ).
      iIntros "(#INV & OB & PH & CPm) POST".

      iApply (rfl_acquire_spec with "[-POST]").
      1: iFrame "#∗"; by iApply empty_sgns_levels_rel.
      all: try by eauto.

      iNext. iIntros (?) "(%s__o & % & OB & PH & % & % & ? & (%f & P) & LOCKED)".
      rewrite union_empty_l_L. iApply "POST". do 2 iExists _.
      iFrame. 
    Qed.

    Lemma release_right (lk: val) τ s__o flag s__f π f:
      {{{ client_inv lk flag s__f ∗
          ep s__f π (rfl_d RFL) ∗
          obls τ {[ s__o ]} ∗
          th_phase_eq τ π ∗ cp π (rfl_d RFL) ∗
          P__lock flag s__f f ∗          
          rfl_locked RFL s__o (rfl_G0 := RFLG) }}}
        rfl_release RFL lk @ τ
      {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π ∗ 
                         (⌜ f = true ⌝ ∨ ⌜ f = false ⌝ ∗ cp_mul π (rfl_d RFL) 4) }}}.
    Proof using All.
      iIntros (Φ).
      iIntros "(#INV & #EPf & OB & PH & CPm & P & LOCKED) POST".

      iAssert (∀ q', obls τ ∅ -∗ th_phase_frag τ π q' -∗ BOU ∅ 4 ((⌜f = true⌝ ∨ ⌜f = false⌝ ∗ cp_mul π (rfl_d RFL) 4) ∗ P__lock flag s__f f ∗ obls τ ∅ ∗ th_phase_frag τ π q'))%I with "[P]" as "FIN".
      { iIntros (q') "OB PH". rewrite /P__lock. destruct f.
        { iDestruct "P" as "[? SGNf]".          
          iApply BOU_intro. iFrame. by iLeft. }
        iDestruct "P" as "[FLAG SGNf]".
        iApply OU_BOU_rep. iApply (OU_rep_wand with "[FLAG]").
        2: { iApply (expect_sig_upd_rep with "EPf [$] [$] [] [$]").
             iApply empty_sgns_levels_rel. }
        iIntros "(CPSm & UNSET & OB & PH)". iFrame.
        iRight. by iFrame. }
      
      rewrite -(union_empty_l_L {[ _ ]}).
      iApply (rfl_release_spec with "[-POST] [$]").
      2: iFrame "#∗".
      all: try by eauto.

      iIntros (q QQ) "PH OB".
      iMod ("FIN" with "[$] [$]") as "(C&P&?&PH)".
      iModIntro.
      iSplitL "P"; [by iExists _| ].
      iIntros "PH'".
      iDestruct (th_phase_frag_combine' with "[$PH $PH']") as "foo"; [done| iFrame].
    Qed.
    
    Lemma right_thread_iter_spec (lk: val) τ π flag s__f (c: loc):
      {{{ client_inv lk flag s__f ∗ 
          obls τ ∅ ∗ th_phase_eq τ π ∗
          sgn s__f l__f None ∗
          ep s__f π (rfl_d RFL) ∗
          cp_mul π (rfl_d RFL) 3 ∗
          c ↦ #false
      }}}
        right_thread_iter lk #flag #c @ τ
      {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π ∗
                    ∃ (v: bool), c ↦ #v ∗ (⌜ v = true ⌝  ∨ ⌜ v = false ⌝ ∗ cp_mul π (rfl_d RFL) 4)
                     }}}.
    Proof using All.
      iIntros (Φ).
      iIntros "(#INV & OB & PH & #SGNf & #EPf & CPSm & C) POST".
      rewrite /right_thread_iter.

      pure_step_cases.
      split_cps "CPSm" 1. rewrite -cp_mul_1.
      iApply (first_step with "[$] [$]").
      { try_solve_bounds. use_rfl_fl_sb. }
      { done. }
      { apply LT0m. }
      iApply sswp_pure_step; [done| ].
      iIntros "!> CPS #EXC PH". simpl.
      pure_steps.

      pure_steps.
      wp_bind (rfl_acquire _ _)%E.
      split_cps "CPSm" 1. rewrite -!cp_mul_1. 
      iApply (acquire_right with "[PH OB CPSm]").
      { by iFrame "#∗". }

      iNext. iIntros (v) "(%s__o & %f & OB & PH & P & LOCKED)".
      wp_bind (Rec _ _ _)%E. pure_steps.
      wp_bind (! _)%E. rewrite /P__lock. iDestruct "P" as "[FLAG P]".
      iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> FLAG".
      MU_by_burn_cp. pure_steps.
      wp_bind (_ <- _)%E.
      iApply sswp_MU_wp; [done| ]. iApply (wp_store with "[C]"); [by iFrame| ].
      iIntros "!> C". MU_by_burn_cp. pure_steps.
      wp_bind (Rec _ _ _)%E. pure_steps.
      
      iApply (release_right with "[OB PH P LOCKED FLAG CPSm']").
      { iFrame "#∗". }
      iNext. iIntros (?) "(OB & PH & FIN)".
      iApply "POST". iFrame. 
    Qed.

    Lemma right_thread_rep_spec (lk: val) τ π (flag c: loc) s__f:
      {{{ client_inv lk flag s__f ∗ 
          obls τ ∅ ∗ th_phase_eq τ π ∗
          sgn s__f l__f None ∗
          ep s__f π (rfl_d RFL) ∗
          cp_mul π (rfl_d RFL) 4 ∗
          c ↦ #false
      }}}
        right_thread_rep lk #flag #c @ τ
      {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π ∗
                    c ↦ #true }}}.
    Proof using All.
      iIntros (Φ).
      iLöb as "IH".
      iIntros "(#INV & OB & PH & #SGNf & #EPf & CPSh & C) POST".
      rewrite /right_thread_rep.

      pure_step_cases.
      split_cps "CPSh" 1. rewrite -cp_mul_1.
      iApply (first_step with "[$] [$]").
      { try_solve_bounds. use_rfl_fl_sb. }
      { done. }
      { apply LT0m. }
      iApply sswp_pure_step; [done| ].
      iIntros "!> CPS #EB PH". simpl.

      wp_bind (Rec _ _ _)%E.
      do 7 pure_step_cases.
      wp_bind (right_thread_iter _ _ _)%E.

      split_cps "CPS" 20. 
      iApply (right_thread_iter_spec with "[-POST CPS]").
      { iFrame "#∗". }
      iIntros "!> %r (OB & PH & (%f & C & ITER))".
      wp_bind (Rec _ _ _)%E. pure_steps.      
      wp_bind (! _)%E.
      iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> C".
      MU_by_burn_cp. pure_steps.
      wp_bind (_ = _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step.
      { simpl. tauto. }
      MU_by_burn_cp. pure_steps.
      
      iDestruct "ITER" as "[-> | [-> CPh]]".
      - rewrite bool_decide_eq_true_2; [| tauto].
        pure_steps. iApply "POST". iFrame.
      - rewrite bool_decide_eq_false_2; [| done].
        pure_step. iApply ("IH" with "[-POST]"); [| done]. iFrame "#∗".
    Qed.

    Theorem right_thread_spec (lk: val) τ π (flag: loc) s__f:
      {{{ client_inv lk flag s__f ∗ 
          obls τ ∅ ∗ th_phase_eq τ π ∗
          sgn s__f l__f None ∗
          cp_mul π d__r 2
      }}}
        right_thread lk #flag @ τ
      {{{ v, RET v; obls τ ∅ ∗ th_phase_eq τ π}}}.
    Proof using All.
      iIntros (Φ).
      iIntros "(#INV & OB & PH & #SGNf & CPSm) POST".
      rewrite /right_thread.

      pure_step_cases.
      split_cps "CPSm" 1. rewrite -cp_mul_1.
      iApply (first_step with "[$] [$]").
      { try_solve_bounds. use_rfl_fl_sb. }
      { done. }
      { apply LThm. }
      iApply sswp_pure_step; [done| ].
      iIntros "!> CPS #EXC PH". simpl.
      pure_steps.

      wp_bind (ref _)%E.
      iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %c C _".
      MU_by_BOU.
      iApply BOU_lower.
      { try_solve_bounds. use_rfl_fl_sb. }
      iApply OU_BOU.

      iApply (OU_wand with "[-CPSm' PH]").
      2: { iApply (@create_ep_upd with "[$] [$] [$]").
           apply LThm. } 
      iIntros "(EPf & _ & PH)".
      
      BOU_burn_cp.

      do 1 pure_step_cases.

      wp_bind (Rec _ _ _)%E.
      do 1 pure_step_cases. iApply wp_value.
      do 1 pure_step_cases. 

      split_cps "CPS" 10. simpl.
      iApply (right_thread_rep_spec with "[-POST]").
      2: { iNext. iIntros (?) "(?&?&?&?)". iApply "POST". iFrame. }
      iFrame "#∗".
      iApply cp_mul_weaken; [reflexivity| | by iFrame].
      lia.
    Qed.

  End AfterInit.

  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}. 

  Context {CL_PRE: ClientPreG Σ} {FL_PRE: rfl_preG RFL Σ}.

  Theorem client_spec τ π:
    {{{ obls τ ∅ ∗ th_phase_eq τ π ∗ cp_mul π d__r 3 }}}
      client_prog #() @ τ
    {{{ v, RET v; obls τ ∅ }}}.
  Proof using All.
    iIntros (Φ) "(OB & PH & CPSr) POST". rewrite /client_prog.

    pure_step_hl. MU_by_BOU.
    iApply BOU_lower.
    { try_solve_bounds. use_rfl_fl_sb. } 
    iApply BOU_split.
    split_cps "CPSr" 1. rewrite -cp_mul_1.
    iApply (BOU_wand with "[-CPSr']").
    2: { iApply (first_BOU with "[$]").
         apply LThm. }
    iIntros "(CPS & #EXC)".

    iApply OU_BOU. iApply (OU_wand with "[-OB]").
    2: { iApply (OU_create_sig _ _ l__f with "OB"). }
    iIntros "(%s__f & SGNf & OB & _)". rewrite union_empty_l_L.
    iDestruct (sgn_get_ex with "[$]") as "[SGNf #SGNf']".
    BOU_burn_cp.

    split_cps "CPS" 1. rewrite -cp_mul_1.

    wp_bind (ref _)%E. iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply wp_alloc. iIntros "!> %flag FLAG _".
    iNext. MU_by_burn_cp. iModIntro.

    iApply wp_value. wp_bind (Rec _ _ _)%E. pure_steps.
  
    wp_bind (rfl_newlock _ _)%E.
    iApply (rfl_newlock_spec RFL _ _ c__cl (∃ b, P__lock flag s__f b) with "[$CPS' $PH FLAG SGNf]").
    all: try by eauto.
    { try_solve_bounds. }
    { iExists _. iFrame. }

    set (cG := {| cl_PreG := CL_PRE |}). 
    
    iIntros "!> %lk (%RFLG & RFL_INV & PH)".
    iAssert (client_inv lk flag s__f)%I with "RFL_INV" as "#INV".
    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (Fork _)%E. 
    split_cps "CPS" 3.
    iApply sswp_MUf_wp. iIntros "%τ' !>".
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iApply (MU__f_wand with "[-CP PH OB]").
    2: { iApply ohe_obls_AMU__f; [done| ].
         iApply BOU_AMU__f.
         iApply BOU_intro. iFrame.
         iAccu. }
    iIntros "(_ & (%π1 & %π2 & PH1 & OB1 & PH2 & OB2 & [%PH_LT1 %PH_LT2]))".

    iSplitL "CPS' OB2 PH2".
    { iApply (left_thread_spec with "[-]").
      2: { iIntros "!> % [OB PH]". by iApply NO_OBS_POST. }
      iFrame "#∗". iSplitL "OB2".
      { iApply obls_proper; [| done]. symmetry. apply intersection_idemp. }
      apply strict_include in PH_LT2.
      iApply cp_mul_weaken; [| reflexivity| by iFrame]. done. }

    iRename "PH1" into "PH". rewrite difference_diag_L.
    apply strict_include in PH_LT1. 
    wp_bind (Rec _ _ _)%E.
    iDestruct (cp_mul_weaken with "CPS") as "CPS".
    { apply PH_LT1. }
    { reflexivity. }
    pure_steps.

    iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
    iApply sswp_MUf_wp. iIntros "%τ2 !>". 
    iApply (MU__f_wand with "[-CP PH OB1]").
    2: { iApply ohe_obls_AMU__f; [done| ].
         iApply BOU_AMU__f. 
         iApply BOU_intro. iFrame.
         iAccu. }
    iIntros "(_ & (%π11 & %π12 & PH1 & OB1 & PH2 & OB2 & [%PH_LT11 %PH_LT12]))".

    iSplitR "POST OB1".
    2: { iApply "POST". iApply obls_proper; [| done].
         symmetry. apply difference_diag. }

    split_cps "CPS" 3.
    iApply (right_thread_spec with "[-PH1]").
    2: { iIntros "!> % [OB PH]". by iApply NO_OBS_POST. }
    rewrite intersection_idemp_L. iFrame "#∗".
    apply strict_include in PH_LT12.
    iApply cp_mul_weaken; [| reflexivity| by iFrame]. 
    etrans; done.

    Unshelve. all: by eauto. 
  Qed.
    
End MotivatingClient.
