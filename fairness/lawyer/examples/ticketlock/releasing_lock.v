From trillium.fairness.lawyer.examples Require Import obls_atomic.
From trillium.fairness.lawyer.obligations Require Import obligations_model  obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From trillium.fairness.lawyer.obligations Require Import obligations_resources.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From trillium.fairness.lawyer.examples Require Import signal_map obls_tactics.
From trillium.fairness.lawyer.examples.ticketlock Require Import fair_lock.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.


Section ReleasingLockSpec.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  
  
  Record ReleasingFairLock := {
      rfl_newlock: val;
      rfl_acquire: val;
      rfl_release: val;
      rfl_preG: gFunctors -> Set;
      rfl_G: gFunctors -> Set;
      rfl_is_lock `{rfl_G Σ} {OHE: OM_HL_Env OP EM Σ}
      : val -> nat -> iProp Σ -> iProp Σ;
      rfl_sb_fun: nat -> nat;
      rfl_d: Degree;
      rfl_lvls: gset Level;
      rfl_locked `{rfl_G Σ} {OHE: OM_HL_Env OP EM Σ}: SignalId -> iProp Σ;
      
      rfl_newlock_spec {Σ} {PRE: rfl_preG Σ} {OHE: OM_HL_Env OP EM Σ}        
        τ π u P
        (LB_SB': rfl_sb_fun u <= LIM_STEPS):
        {{{ cp π rfl_d ∗ th_phase_eq τ π ∗ P }}}
            rfl_newlock #() @ τ
        {{{ lk, RET lk; ∃ RFLG: rfl_G Σ, rfl_is_lock lk u P (rfl_G0 := RFLG) ∗ th_phase_eq τ π }}};

      rfl_acquire_spec `{RFLG: rfl_G Σ} {OHE: OM_HL_Env OP EM Σ}
        τ lk (π: Phase) (Ob: gset SignalId) u (P: iProp Σ):
      {{{
          rfl_is_lock lk u P (rfl_G0 := RFLG)  ∗
          obls τ Ob ∗
          th_phase_eq τ π ∗
          cp π rfl_d ∗
          sgns_levels_gt' Ob (rfl_lvls: gset LvlO)
      }}}
        rfl_acquire lk @ τ
      {{{ v, RET v; ∃ s__o l__o,
              obls τ (Ob ∪ {[ s__o ]}) ∗ sgn s__o l__o None ∗
              ⌜ s__o ∉ Ob ⌝ ∗ ⌜ l__o ∈ rfl_lvls ⌝ ∗
              th_phase_eq τ π ∗ P ∗ rfl_locked s__o (rfl_G0 := RFLG) }}};

      rfl_release_spec {Σ} {RFLG: rfl_G Σ} {OHE: OM_HL_Env OP EM Σ}
        τ lk (π: Phase) (Ob: gset SignalId) (u: nat) (P: iProp Σ) s__o Q
        (ADD: s__o ∉ Ob):
      {{{ rfl_is_lock lk u P (rfl_G0 := RFLG) ∗
          sgns_levels_gt' Ob rfl_lvls ∗
          obls τ (Ob ∪ {[ s__o ]}) ∗ 
          th_phase_eq τ π ∗ cp π rfl_d ∗
          rfl_locked s__o (rfl_G0 := RFLG) ∗
          (∀ q, ⌜ Qp.le q 1 ⌝ -∗ th_phase_frag τ π q -∗ obls τ Ob -∗
           BOU ∅ u (P ∗ ((Qp.sub 1%Qp q ≫= Some ∘ th_phase_frag τ π) -∗? Q)))
      }}}
        rfl_release lk @ τ
      {{{ v, RET v; Q }}} ;

      rfl_is_lock_pers `{PRE: rfl_G Σ} {OHE: OM_HL_Env OP EM Σ}
        lk u P: Persistent (rfl_is_lock lk u P (rfl_G0 := PRE));
  }.
  
End ReleasingLockSpec.


Section RFLFromFL.

  Class RelOblPreG Σ := {
      ro_ow_sig_pre :> inG Σ (excl_authUR (optionUR SignalId));
      ro_sig_map_pre :> SigMapPreG Σ;
  }.
  
  Class RelOblG Σ := {
      ro_PreG :> RelOblPreG Σ;
      ro_γ__ow: gname;
      ro_sig_map :> SigMapG Σ;
  }.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}. 

  Context
    {FLP: FairLockPre}
    (FL: FairLock (FLP := FLP)).

  Context (l__o: Level).
  Context (P__lock: iProp Σ).  
  Hypothesis (LVL_ORDo: forall l, l ∈ fl_acq_lvls FLP -> lvl_lt l__o l). 
  
  Section AfterInit.

  Context {ROG: RelOblG Σ}.
  Context {FLG: fl_GS FLP Σ}.
    
  Definition RR__L π (r': option nat): iProp Σ :=
    match r' with
    | None => ⌜ True ⌝
    | Some r => ∃ s, ith_sig r s ∗ ep s π (fl_d__l FLP)
  end.

  Definition smap_repr_cl r (b: bool): iProp Σ :=
    smap_repr (fun _ => l__o) (flip Nat.ltb r) (set_seq 0 (r + (if b then 1 else 0))).
  
  Definition lock_owner_auth (oo: option SignalId) :=
    own ro_γ__ow (● Excl' oo).
  Definition lock_owner_frag (oo: option SignalId) :=
    own ro_γ__ow (◯ Excl' oo).
    
  Definition lock_inv_inner lk: iProp Σ :=
    ∃ r b oo, fl_LK FLP (lk, r, b) (FLG := FLG) ∗ lock_owner_auth oo ∗
                (⌜ b = true ⌝ ∗ (∃ s__o, ⌜ oo = Some s__o ⌝ ∗ ith_sig r s__o)
                 ∨ ⌜ b = false ⌝ ∗ lock_owner_frag None ∗ P__lock) ∗ smap_repr_cl r b.

  Definition lock_ns := nroot .@ "lock".
  Definition lock_inv lk: iProp Σ :=
    inv lock_ns (lock_inv_inner lk).

  Definition sb_add := 3.
  (* Definition rfl_fl_sb := max (fl_c__cr FLP) 10. *)
  Definition rfl_fl_sb_fun :=
    fun i => max_list [10; fl_c__cr FLP; fl_B FLP i + sb_add; fl_B FLP (i + sb_add)].

  Definition rfl_fl_is_lock lk u: iProp Σ :=
    lock_inv lk ∗ fl_is_lock FL lk (u + sb_add) (FLG := FLG) ∗
    ⌜ rfl_fl_sb_fun u <= LIM_STEPS ⌝.

  (* need to assume at least one FL level *)
  (* TODO: can we change either TAU or levels order? *)
  Context (l__fl: Level).
  Hypothesis (L__FL: l__fl ∈ fl_acq_lvls FLP).

  Lemma BOU_wait_owner τ π q O r:
      obls τ O ∗ sgns_levels_ge' O (fl_acq_lvls FLP)∗
      th_phase_frag τ π q ∗ RR__L π (Some r) ∗ smap_repr_cl r true ⊢
      BOU ∅ 1 (cp π (fl_d__l FLP) ∗ th_phase_frag τ π q ∗
                obls τ O ∗ smap_repr_cl r true).
    Proof using L__FL LVL_ORDo. 
      iIntros "(OBLS & #LVLS & PH & #RR & SR)".
      rewrite /RR__L. iDestruct "RR" as (s) "(#ITH & #EP)".  (* & %PH__e *)
      iApply OU_BOU.
      iApply (OU_wand with "[]").
      2: { rewrite /smap_repr_cl.
           iApply (ith_sig_expect (λ _, l__o) with "[$] [$] [$] [$] [$] []").
           { simpl. apply Nat.ltb_nlt. lia. }
           rewrite /sgns_levels_ge'.
           (* iDestruct (big_sepS_forall with "LVLS") as "LVLS'". *)
           (* iSpecialize ("LVLS'" $! l__fl with "[//]"). *)
           rewrite /sgns_level_gt /sgns_levels_gt'. rewrite /sgns_levels_rel. 
           iApply big_sepS_impl; [by iFrame| ].
           iModIntro. iIntros (??) "(%l & ? & %LE)".
           iExists _. iFrame. iPureIntro.
           apply set_Forall_singleton.
           simpl in *. rewrite /flip in LE. 
           eapply strict_transitive_l; [| apply LE].
           1: apply LVL_ORDo.
           all: apply L__FL. }
      iIntros "(?&?&?&?)". iApply BOU_intro. iFrame.
    Qed.

    Lemma BOU_create_wait_owner τ π q r s:
      th_phase_frag τ π q ∗ cp π (fl_d__h FLP) ∗ smap_repr_cl r true ∗ ith_sig r s ⊢
      BOU ∅ 1 (th_phase_frag τ π q ∗ RR__L π (Some r) ∗ smap_repr_cl r true).
    Proof using LVL_ORDo L__FL.
      iIntros "(PH & CP & SR & #ITH)".
      rewrite /RR__L.
      iApply OU_BOU.
      iApply (OU_wand with "[]").
      2: { iApply (smap_create_ep (λ _, l__o) r with "[$] [$] [$] [$]").
           apply fl_degs_lh. }
      iIntros "X". iMod "X" as "(?&?&?)". iApply BOU_intro.
      iFrame. iExists _. iFrame "#∗".
    Qed.

    Lemma lock_owner_agree n1 n2:
      lock_owner_auth n1-∗ lock_owner_frag n2 -∗ ⌜ n1 = n2 ⌝.
    Proof using.
      rewrite /lock_owner_frag /lock_owner_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".
      iDestruct (own_valid with "H") as "%Hval".
      iPureIntro. apply excl_auth_agree_L in Hval. set_solver.
    Qed.

    Lemma lock_owner_update n1 n2 n':
      lock_owner_auth n1 -∗ lock_owner_frag n2 ==∗
      lock_owner_auth n' ∗ lock_owner_frag n'.
    Proof using.
      rewrite /lock_owner_frag /lock_owner_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".
      rewrite -!own_op. iApply own_update; [| by iFrame].
      apply excl_auth_update.
    Qed.  

    Lemma BOU_smap_cl_extend τ R r:
    ⊢ obls τ R -∗ smap_repr_cl r false -∗
      BOU ∅ 1 (|==> (∃ s', smap_repr_cl r true ∗ obls τ (R ∪ {[s']}) ∗ ⌜ s' ∉ R ⌝ ∗ sgn s' l__o None ∗ ith_sig r s')).
    Proof using.
      iIntros "OB SR".
      iApply (BOU_wand with "[]").
      2: { iApply (BOU_smap_extend (λ _, l__o) _ r with "[$] [$]").
             { intros. reflexivity. }
             { simpl. apply Nat.ltb_irrefl. }
             intros ?%elem_of_set_seq. lia. }
      iIntros "XX". iMod "XX" as "(%s' & SR & #ITH & OB & %FRESH & #SGN)".
      iExists _. iFrame "#∗".
      iModIntro. iSplit; [| done].
      rewrite /smap_repr_cl. rewrite Nat.add_0_r. rewrite set_seq_add_L.
      simpl. by rewrite union_empty_r_L. 
    Qed.

    Definition rfl_fl_locked (s__o: SignalId): iProp Σ :=
      lock_owner_frag (Some s__o) ∗ sgn s__o l__o None ∗
      fl_release_token FL (FLG := FLG).

    Existing Instance fl_is_lock_pers. 

    Definition rfl_fl_lvls := fl_acq_lvls FLP ∪ {[ l__o ]}. 

    Context (d__m': Degree).
    Hypothesis (LTmm': deg_lt (fl_d__m FLP) d__m').

    Definition rfl_acquire_spec_gen (e: expr) (R: iProp Σ) (d: Degree) :=
                                
      forall (τ : locale heap_lang) (lk : val) (π : Phase) (Ob : gset SignalId) 
      (u : nat) (P : iProp Σ),
      {{{ rfl_fl_is_lock lk u ∗ obls τ Ob ∗
          th_phase_eq τ π ∗ cp π d ∗
          sgns_levels_gt' Ob rfl_fl_lvls }}}
        e lk @ τ
      {{{ v, RET v; ∃ s__o,
              obls τ (Ob ∪ {[ s__o ]}) ∗ rfl_fl_locked s__o ∗
              th_phase_eq τ π ∗ R }}}. 


    Ltac remember_goal :=
  match goal with | |- envs_entails _ ?P =>
    iAssert (P -∗ P)%I as "GOAL"; [iIntros "X"; by iApply "X"| ]
  end.

    Lemma rfl_acquire_spec_later:
      rfl_acquire_spec_gen (fl_acquire FLP) (▷ P__lock) (fl_d__m FLP).
    Proof using L__FL LVL_ORDo.
      clear LTmm'.
      rewrite /rfl_acquire_spec_gen. intros τ lk π Ob u R.
      iIntros (Φ).
      iIntros "(#(INV & LOCK & %BOUND) & OB & PH & CPm & #OB_GT) POST".

      iApply (wp_step_fupd _ _ ⊤ _ _ with "[POST]").
      { done. }
      { iModIntro. iNext. iModIntro.
        iApply "POST". }

      iPoseProof (fl_acquire_spec FL _ _ τ with "[$]") as "ACQ".
      rewrite /TLAT_FL_RR /TLAT_RR.

      iApply ("ACQ" $! _ _ _ _ (RR__L π) with "[] [OB PH CPm]").
      { try_solve_bounds. }
      { rewrite /TLAT_pre. iFrame "#∗".
        iApply (sgns_levels_rel'_impl with "[$]").
        1, 2: done.
        set_solver. }

      iApply (TAU_intro with "[]").
      3: { iSplit; [| iAccu].
           iCombine "INV" as "X". iApply "X". }
      { by apply _. }
      iIntros "(#INV & _)".
      rewrite /TAU_acc.
      iInv "INV" as "inv" "CLOS".
      iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'".
      rewrite {1}/lock_inv_inner.
      
      iDestruct "inv" as (r b oo) "(LK & LOCK_OW & ST & SR)".
      iExists (lk, r, b).
      iFrame "LK". iSplit; [done| ].
      
      iSplit; [| iSplit].
      
      3: { iIntros "[LK %]".
           iMod "CLOS'" as "_". iFrame.
           iMod ("CLOS" with "[-]") as "_".
           2: { by iFrame "#∗". }
           iNext. rewrite /lock_inv_inner. do 3 iExists _. iFrame. }

      { iIntros (O' q') "(OB & #LVLS' & PH & %Q' & (-> & CASES))". simpl.

        (* TODO: don't unfold BOU *)
        remember_goal.
        iDestruct "ST" as "[>(_ & (%s__o & [-> #SMAP__o])) | [>% ?]]"; [| done].
        iMod "LOCK_OW". iMod "SR".
        iApply "GOAL". iClear "GOAL".

        iAssert (BOU ∅ 1 (RR__L π (Some r) ∗ th_phase_frag τ π q' ∗
                           smap_repr_cl r true))%I with "[CASES PH SR]" as "EXP".
        { iDestruct "CASES" as "[RR | CP]".
          { iApply BOU_intro. iFrame "#∗". }
          iApply (BOU_wand with "[]").
          2: { iApply BOU_create_wait_owner; [..| iFrame "#∗"]. }
          iIntros "(?&?&?)". iFrame. }

        rewrite /sb_add. iMod "EXP" as "(#RR & PH & SR)"; [lia| ].

        iMod (BOU_wait_owner with "[OB PH SR]") as "WAIT".
        { iFrame "#∗". }
        { lia. }
        iDestruct "WAIT" as "(CP & PH & OB & SR)".
        iFrame "#∗". iModIntro. iIntros "[LK %]".
        iMod "CLOS'" as "_".
        iMod ("CLOS" with "[-]") as "_"; [| done].
        iNext. rewrite /lock_inv_inner. do 3 iExists _. iFrame.
        iLeft. iSplit; [done| ]. iExists _. iFrame "#∗". done. }

      { iIntros "%q' (OB & PH & %Q') %st [LK (%X & %Y & %Z)]".
        destruct st as ((?&?)&?). simpl in X, Y, Z. inversion_clear X. subst.
        remember_goal. 

        iDestruct "ST" as "[XX | YY]".
        { iDestruct "XX" as "[#YY VV]".
          iModIntro. by iMod "YY" as %?. }

        iDestruct "YY" as "(_& >LOCKED & P)".
        iMod "LOCK_OW".
        iMod "SR".
        iApply "GOAL". iClear "GOAL".

        simpl. rewrite /acquire_at_post. simpl.
        
        iMod (BOU_smap_cl_extend with "[$] [$]") as "X".
        { rewrite /sb_add. lia. }
        iMod "X" as "(%s' & SR & OB & %FRESH' & [#SGNo #RTH])".
        iApply BOU_intro. iFrame. 

        simpl in *. 
        iMod "CLOS'" as "_".
        iMod (lock_owner_update _ _ (Some s') with "[$] [$]") as "[LOCK_OW LOCKED]".
        iMod ("CLOS" with "[LK SR LOCK_OW]").
        { iNext. rewrite /lock_inv_inner.
          do 3 iExists _. iFrame.
          iLeft. iSplit; [done| ].
          iExists _. by iFrame "#∗". }
        
        iModIntro. iIntros "PH_CLOS RT POST !>". iApply "POST".
        do 1 iExists _. iFrame "#∗".
        iDestruct (th_phase_frag_combine' with "[$PH PH_CLOS]") as "foo".
        { done. }
        2: by iFrame.
        destruct (1 - q')%Qp; done. }
    Qed.

    Definition acquire_aux: val :=
      λ: "lk", fl_acquire FLP "lk" ;; Skip
    .

    (* leading lambda to exchange fuel, trailing Skip to strip later *)
    (* TODO: change the definition of (our counterpart of) atomic_wp,
       so that it allows showing postcondition under later *)
    Lemma acquire_usage:
      rfl_acquire_spec_gen acquire_aux P__lock d__m'.
    Proof using L__FL LVL_ORDo LTmm'.
      rewrite /rfl_acquire_spec_gen /acquire_aux. intros τ lk π Ob c__cl ?.
      iIntros (Φ).
      iIntros "(#(INV & LOCK & %BOUND) & OB & PH & CPm & #OB_GT) POST".

      pure_step_hl. MU_by_BOU.
      iMod (first_BOU with "[$]") as "[CPS #EB]". 
      { apply LTmm'. }
      { try_solve_bounds. use_rfl_fl_sb. }
      BOU_burn_cp.

      pure_steps.
      split_cps "CPS" 1. rewrite -cp_mul_1. 
      wp_bind (fl_acquire _ _)%E. iApply (rfl_acquire_spec_later with "[-POST CPS]"); eauto.
      { iFrame "#∗". done. }
      iIntros "!> %v (% & ?&?&PH&?)".

      wp_bind (Rec _ _ _)%E. pure_steps.
      iApply "POST". iExists _. iFrame.
    Qed.
  
    Lemma BOU_set_sig τ r s R:
      ⊢ smap_repr_cl r true -∗ ith_sig r s -∗ obls τ (R ∪ {[ s ]}) -∗
         BOU ∅ 1 (smap_repr_cl (r + 1) false ∗ obls τ (R ∖ {[ s ]})).
    Proof using.
      clear. 
      iIntros "SR #SIG OB".
      iApply OU_BOU.
      iApply (OU_wand with "[-OB SR]").
      2: { iApply (smap_set_sig (λ _, l__o) with "[$] [$] [$]").
           { Unshelve. 2: exact (flip Nat.ltb (S r)).
             simpl. apply Nat.ltb_lt. lia. }
           { set_solver. }
           (* TODO: extract lemma, use in eo_fin *)
           intros. simpl.
           apply elem_of_set_seq in H0.
           destruct (Nat.lt_trichotomy j (S r)) as [LT | [-> | LT]]; revgoals.
           1,2: rewrite !(proj2 (Nat.ltb_ge _ _)); lia.
           rewrite !(proj2 (Nat.ltb_lt _ _)); lia. }
      iIntros "[SR OB]". iApply BOU_intro.
      iSplitR "OB".
      2: { iApply obls_proper; [..| by iFrame]. set_solver. }
      rewrite /smap_repr_cl. rewrite Nat.add_1_r Nat.add_0_r.
      iFrame.
    Qed.

    (* TODO: remove sgns_levels_gt' restriction; probably need to change obls def *)
    Lemma release_usage u (lk: val) τ s__o Ob π Q
      (ADD: s__o ∉ Ob)
      :
      {{{ rfl_fl_is_lock lk u ∗
          sgns_levels_gt' Ob (fl_acq_lvls FLP) ∗ obls τ (Ob ∪ {[ s__o ]}) ∗ 
          th_phase_eq τ π ∗ cp π (fl_d__m FLP) ∗
          rfl_fl_locked s__o ∗ 
          (∀ q, ⌜ Qp.le q 1 ⌝ -∗ th_phase_frag τ π q -∗ obls τ Ob -∗
           BOU ∅ u (P__lock ∗ (((Qp.sub 1%Qp q) ≫= Some ∘ th_phase_frag τ π) -∗? Q)))
      }}}
        (fl_release FLP) lk @ τ
      {{{ v, RET v; Q }}}.
    Proof using All.
      iIntros (Φ).
      iIntros "(#(INV & LOCK & %BOUND) & #SGT & OB & PH & CPm & LOCKED & FIN_BOU) POST".

      iApply (wp_step_fupd _ _ ⊤ _ _ with "[POST]").
      { done. }
      { iModIntro. iNext. iModIntro. iApply "POST". }

      iDestruct "LOCKED" as "(OW & #SGNo & RT)".
      iPoseProof (fl_release_spec FL lk _ τ with "[$]") as "REL".
      rewrite /TLAT_FL /TLAT.
      iApply ("REL" with "[] [OB PH CPm]").
      { try_solve_bounds. }
      { iFrame.
        (* TODO: make a lemma *)
        rewrite /sgns_levels_gt'.

        rewrite /sgns_levels_rel. rewrite big_sepS_union; [| set_solver].
        iSplit. 
        - iApply (big_sepS_impl with "[$]").
          iModIntro. iIntros (??) "(%l & ? & %LE)".
          iExists _. iFrame. done.
        - iApply big_sepS_singleton. iExists _. by iFrame "SGNo". }

      iApply (TAU_intro with "[-]").
      3: { iSplit; [| iAccu].
           iCombine "INV" as "X". iApply "X". }
      { by apply _. }
      iIntros "(#INV & LOCKED & FIN_BOU)".
      iInv "INV" as "inv" "CLOS". rewrite {1}/lock_inv_inner.
      iDestruct "inv" as (r b oo) "(LK & >LOCK_OW & ST & >SR)".

      iDestruct "ST" as "[>[-> ST]| [? [>UNLOCKED ?]]]".
      2: { iExFalso. iCombine "LOCKED UNLOCKED" as "X".
           iDestruct (own_valid with "X") as %V%auth_frag_valid_1.
           rewrite Some_valid in V. done. }

      iDestruct "ST" as "[%so_ [-> #SM__o]]".
      iExists _.
      iFrame "LK".
      iDestruct (lock_owner_agree with "[$] [$]") as "%EQ".
      inversion EQ. subst.

      iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'".
      iSplit; [done| ].
      iSplit; [| iSplit].
      3: { iIntros "[LK %]".
           iMod "CLOS'" as "_". iFrame.
           iMod ("CLOS" with "[-]") as "_".
           2: { by iFrame "#∗". }
           iNext. rewrite /lock_inv_inner. do 3 iExists _. iFrame.
           iLeft. iSplit; [done| ]. eauto. }
      { iIntros (??) "(?&?&?&?&?)". done. }
      { iIntros "% (OB & PH & %Q') %st [LK (%X & %Y & %Z)]".
        destruct st as ((?&?)&?). simpl in X, Y, Z. inversion_clear X. subst.
        iMod (BOU_set_sig with "[$SR] [$] [$]") as "[SR OB]".
        { rewrite /sb_add. lia. }
                                                                            
        rewrite (difference_disjoint_L Ob); [| set_solver].

        iMod ("FIN_BOU" with "[//] [$] [$]") as "[P FIN]".
        { rewrite /sb_add. lia. }
        iModIntro. 
        
        rewrite /release_at_post. simpl.
        iMod (lock_owner_update _ _ None with "[$] [$]") as "[UNL' UNL]".
        iMod "CLOS'" as "_".
        iMod ("CLOS" with "[-FIN]") as "_".
        2: { iModIntro. iIntros "PH_CLOS POST". iApply "POST".
             iFrame. iModIntro.
             iApply "FIN".
             destruct (1 - q')%Qp; simpl; done. }
        iNext. rewrite /lock_inv_inner. do 3 iExists _. iFrame.
        iRight. iSplit; [done| ]. iFrame. }
     Qed.

    End AfterInit.

  Lemma alloc_client_inv {FLG: fl_GS FLP Σ} {PRE: RelOblPreG Σ}
    lk:
    fl_LK FLP (lk, 0, false) (FLG := FLG) -∗
    P__lock ={∅}=∗
    ∃ (cG: RelOblG Σ), lock_inv lk (ROG := cG) (FLG := FLG).
  Proof using.
    iIntros "LK P".
    rewrite -(plus_O_n 0).
    iMod (own_alloc (● Excl' None ⋅ ◯ _: excl_authUR (optionUR SignalId))) as (?) "[OW_A OW_F]".
    { apply auth_both_valid_2; [| reflexivity]. done. }

    iMod (init_smap_repr_empty (fun _ => l__o) ∅) as (SMG) "SR".

    set (CG := {| ro_γ__ow := γ; ro_sig_map := SMG |}).
    iMod (inv_alloc lock_ns _ (lock_inv_inner lk) with "[LK OW_A OW_F SR P]") as "#INV".
    { iNext. rewrite /lock_inv_inner.
      do 3 iExists _. iFrame.
      iSplitR "SR".
      2: { rewrite /smap_repr_cl. done. }
      iRight. by iFrame. }
    iModIntro. by iExists _.   
  Qed.

End RFLFromFL.


Section RFL2FL.

  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree).
  Notation "'Level'" := (om_hl_Level).

  Context
    {FLP: FairLockPre}
    (FL: FairLock (FLP := FLP)).

  Class RFL_FL_preG Σ := {
      rfl_fl_pre_impl :: RelOblPreG Σ;
      rfl_fl_pre_fl :: fl_GpreS FLP Σ;
  }.

  Class RFL_FL_G Σ := {      
      rfl_fl_impl :: RelOblG Σ;
      rfl_fl_fl :: fl_GS FLP Σ;
  }.

  Context (l__o: Level).
  Hypothesis (LVL_ORDo: forall l, l ∈ fl_acq_lvls FLP -> lvl_lt l__o l). 
  Context (l__fl: Level).
  Hypothesis (L__FL: l__fl ∈ fl_acq_lvls FLP).

  Context (d__m': Degree).
  Hypothesis (LTmm': deg_lt (fl_d__m FLP) d__m').

  (* extra steps to exchange fuel that has to align with that of acquire_aux*)
  Definition release_aux: val :=
    λ: "lk", (fl_release FLP) "lk". 
  Definition newlock_aux: val :=
    λ: <>, (fl_create FLP) #().

  Program Definition RFL_FL: ReleasingFairLock := {|
      rfl_newlock := newlock_aux;
      rfl_acquire := acquire_aux (FLP := FLP);
      rfl_release := release_aux;
      rfl_preG := RFL_FL_preG;
      rfl_G := RFL_FL_G;
  
      rfl_sb_fun := rfl_fl_sb_fun (FLP := FLP);
      rfl_d := d__m';
      rfl_lvls := rfl_fl_lvls l__o (FLP := FLP);
  |}.
  Next Obligation.
    intros ??? lk u P. unshelve eapply (rfl_fl_is_lock FL l__o P lk u); auto.
    apply rfl_G0.
  Defined.
  Next Obligation.
    intros ????. unshelve eapply (rfl_fl_locked FL l__o); auto.
    apply rfl_G0.
  Defined.
  Next Obligation.
    intros **.
    iIntros "(CP & PH & P) POST".
    rewrite /newlock_aux. pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS _]".
    { apply LTmm'. }
    { try_solve_bounds. use_rfl_fl_sb. }
    iModIntro. burn_cp_after_BOU.

    iApply wp_fupd. 
        
    unshelve epose proof (fl_create_spec FL) as spec.
    { apply PRE. }
    simpl in spec. iApply (spec with "[] [-POST P]").
    { try_solve_bounds. }
    { iDestruct (cp_mul_take with "CPS") as "[??]". iFrame. }
    iNext. iIntros (lk) "(%FLG & LK & #LOCK & PH)".
    iApply "POST".

    Unshelve. 2: exact (u + sb_add).
    iApply fupd_mask_mono; [by apply empty_subseteq| ].
    iMod (alloc_client_inv l__o with "LK P") as "(%CG & #INV)".

    iModIntro.
    iExists {| rfl_fl_impl := CG ; rfl_fl_fl := FLG |}.
    iFrame "#∗".
    try_solve_bounds. 
  Qed.
  Next Obligation.
    intros **. simpl. 
    iIntros "(#[INV LOCK] & ?&?&?&#SGT) POST".
    iApply (acquire_usage with "[-POST]").
    5: iFrame "#∗".
    all: try by eauto.
    iNext. iIntros "% (%&?&LOCKED&?&?)". iApply "POST".
    rewrite /rfl_fl_locked. iDestruct "LOCKED" as "(?&#SGNo&?)".
    do 2 iExists _. iFrame "#∗".
    iSplit.
    2: { iPureIntro. set_solver. }
    iIntros "%IN".
    rewrite /sgns_levels_gt' /sgns_levels_rel.
    iDestruct (big_sepS_elem_of with "SGT") as "(%l'&SGN'&%GT)"; eauto.
    iDestruct (sgn_level_agree with "SGN' SGNo") as %->.
    specialize (GT l__o ltac:(set_solver)).
    by apply strict_ne in GT.
  Qed.
  Next Obligation.
    intros **. simpl.
    iIntros "(#(INV & LOCK & %BOUND) & #SGT & OB & PH & CP & LOCKED & BOU) POST".
    rewrite /release_aux. pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS _]".
    { apply LTmm'. }
    { try_solve_bounds. use_rfl_fl_sb. }
    iModIntro. burn_cp_after_BOU.

    iApply (release_usage with "[-POST] [$]").
    5: iFrame "#∗".
    all: try by eauto.
    rewrite bi.sep_assoc. iSplitR.
    2: { rewrite cp_mul_1. iApply (cp_mul_weaken with "[$]"); done || lia. }
    iSplit. 
    - try_solve_bounds. 
    - iApply (sgns_levels_rel'_impl with "[$]"); set_solver.
  Qed.
  Next Obligation.
    intros. simpl. apply _.
  Qed.
  Fail Next Obligation.

End RFL2FL.
