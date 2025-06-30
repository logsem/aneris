From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fixpoint.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From iris.base_logic.lib Require Import saved_prop. 
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From fairness Require Import utils.
From lawyer.examples Require Import obls_tactics.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From lawyer Require Import sub_action_em program_logic.
From lawyer.examples.ticketlock Require Import obls_atomic fair_lock.


Section Ticketlock.
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Context {FLP: FairLockPre}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).

  Definition Tid := locale heap_lang.

  Local Infix "*'" := prod (at level 10, left associativity).

  Definition tau_codom Σ: Type :=
    Tid *' Phase *' Qp *'
    (gset SignalId) *' (gset Level) *'
    (val -> (iProp Σ)) *' ((option nat) -> (iProp Σ)).

  Definition tau_codom_gn: Type := 
    Tid *' Phase *' Qp *'
    (gset SignalId) *' (gset Level) *'
    gname *' gname.
                                       
  Local Infix "**" := prodO (at level 10, left associativity).

  Class TicketlockPreG Σ := {
      tl_tau_map_pre :: inG Σ (authUR (gmapUR nat (exclR $ tau_codom_gn)));
      tl_tau_sp_post :: savedPredG Σ val;
      tl_tau_sp_rr :: savedPredG Σ (option nat);
      tl_tokens_pre :: inG Σ (authUR (gset_disjUR natO));
      tl_held_pre :: inG Σ (excl_authUR boolO);
      tl_ow_lb_pre :: inG Σ mono_natUR;
      tl_rel_tok_pre :: inG Σ (exclR unitO);
  }.

  Class TicketlockG Σ := {
      tl_pre :: TicketlockPreG Σ;
      tl_γ_tau_map: gname; tl_γ_tokens: gname; tl_γ_held: gname;
      tl_γ_ow_lb: gname; tl_γ_rel_tok: gname;
  }.

  Definition ticket_tau `{TicketlockG Σ} (n: nat) (cd: tau_codom Σ): iProp Σ :=
    ∃ (γ__p γ__r: gname),
      let cd_gn: tau_codom_gn := (cd.1.1, γ__p, γ__r) in
      own tl_γ_tau_map ((◯ {[ n := Excl cd_gn ]}): authUR (gmapUR nat _)) ∗
      saved_pred_own γ__p DfracDiscarded cd.1.2 ∗ saved_pred_own γ__r DfracDiscarded cd.2.

  Definition tokens_auth `{TicketlockG Σ} (N: nat) :=
    own tl_γ_tokens ((● (GSet $ set_seq 0 N)): authUR (gset_disjUR natO)).
  Definition ticket_token `{TicketlockG Σ} (i: nat) :=
    own tl_γ_tokens ((◯ (GSet {[ i ]})): authUR (gset_disjUR natO)).

  Definition held_auth `{TicketlockG Σ} (b: bool) :=
    own tl_γ_held ((● Excl' b): (excl_authUR boolO)).
  Definition held_frag `{TicketlockG Σ} (b: bool) :=
    own tl_γ_held ((◯ Excl' b): (excl_authUR boolO)).

  Definition ow_exact `{TicketlockG Σ} (n: nat) :=
    own tl_γ_ow_lb ((●MN n): mono_natUR).
  Definition ow_lb `{TicketlockG Σ} (n: nat) :=
    own tl_γ_ow_lb (mono_nat_lb n).

  Definition rel_tok `{TicketlockG Σ} := own tl_γ_rel_tok (Excl ()).

  Lemma ticket_token_excl `{TicketlockG Σ} i:
    ticket_token i -∗ ticket_token i -∗ False.
  Proof using.
    iApply bi.wand_curry. rewrite -own_op -auth_frag_op.
    iIntros "X". iDestruct (own_valid with "X") as %V.
    rewrite auth_frag_valid in V. apply gset_disj_valid_op in V. set_solver.
  Qed.

  Lemma ticket_token_bound `{TicketlockG Σ} i N:
    ticket_token i -∗ tokens_auth N -∗ ⌜ i < N ⌝.
  Proof using.
    iApply bi.wand_curry. rewrite bi.sep_comm -own_op.
    iIntros "X". iDestruct (own_valid with "X") as %V.
    apply auth_both_valid_discrete in V as [IN V].
    apply gset_disj_included, elem_of_subseteq_singleton in IN.
    apply elem_of_set_seq in IN. iPureIntro. lia.
  Qed.

  Lemma held_agree `{TicketlockG Σ} b1 b2:
    held_auth b1-∗ held_frag b2 -∗ ⌜ b1 = b2 ⌝.
  Proof using.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. apply excl_auth_agree_L in Hval. set_solver.
  Qed.

  Lemma held_update `{TicketlockG Σ} b1 b2 b':
    held_auth b1 -∗ held_frag b2 ==∗
    held_auth b' ∗ held_frag b'.
  Proof using.
    iIntros "HA HB". iCombine "HB HA" as "H".
    rewrite -!own_op. iApply own_update; [| by iFrame].
    apply excl_auth_update.
  Qed.

  Ltac destruct_cd cd :=
    destruct cd as [[[[[[?τ ?π] ?q] ?Ob] ?L] ?Post] ?RR].

  Lemma ow_exact_lb `{TicketlockG Σ} n:
    ow_exact n -∗ ow_exact n ∗ ow_lb n.
  Proof using.
    iIntros "EX".
    rewrite /ow_exact. rewrite mono_nat_auth_lb_op.
    rewrite /ow_lb -own_op.
    erewrite (mono_nat_lb_op_le_l n) at 1; [| reflexivity].
    by rewrite cmra_assoc.
  Qed.

  Lemma ow_exact_increase `{TicketlockG Σ} n m
    (LE: n <= m):
    ow_exact n ==∗ ow_exact m ∗ ow_lb m.
  Proof using.
    iIntros "EX".
    rewrite /ow_exact.
    rewrite /ow_lb -!own_op.
    iApply (own_update with "[$]").
    etrans.
    { apply mono_nat_update, LE. }
    by rewrite {1}mono_nat_auth_lb_op.
  Qed.

  Lemma ow_lb_le_exact `{TicketlockG Σ} i n:
    ow_lb i -∗ ow_exact n -∗ ⌜ i <= n ⌝.
  Proof using.
    iApply bi.wand_curry. rewrite bi.sep_comm -own_op. iIntros "X".
    iDestruct (own_valid with "X") as %V%mono_nat_both_valid. done.
  Qed.

  Definition tl_LK `{TicketlockG Σ} `{gen_heapGS loc val Σ}
    (st: FL_st): iProp Σ :=
    let '(lk, r, b) := st in
    ∃ (l__ow l__tk: loc),
      ⌜ lk = (#l__ow, #l__tk)%V ⌝ ∗ l__ow ↦{/ 2} #r ∗
      held_frag b.

  (** Assume that the resulting OM has all needed degrees and levels *)
  Context (d__w d__l0 d__h0 d__e d__m0: Degree).
  Hypothesis
    (fl_degs_wl0: deg_lt d__w d__l0)
    (fl_degs_lh0: deg_lt d__l0 d__h0)
    (fl_degs_he: deg_lt d__h0 d__e)
    (fl_degs_em: deg_lt d__e d__m0)
  .

  Definition tl_exc := 20.

  Hypothesis (LS_LB: S tl_exc ≤ LIM_STEPS). 

  (** we need to have a non-empty set of "acquire levels" 
      to eventually verify the sequential lock spec. *)
  (* TODO: seemingly it's possible to get rid of this restriction 
     by having an extra "lower bound" of levels in the definition of TLAT. 
     clarify if it's possible *)
  Context (lvl_acq: Level).

  Definition lvls_acq: gset Level := {[ lvl_acq ]}. 
  
  Definition tl_newlock: val :=
    λ: <>,
       let: "ow" := ref #(0%nat) in
       let: "tk" := ref #(0%nat) in
       ("ow", "tk").

  Definition get_ticket: val :=
    λ: "lk", FAA (Snd "lk") #1.

  Definition wait: val :=
    rec: "wait" "lk" "t" :=
      let: "o" := !(Fst "lk") in
      if: "t" = "o"
      then #()
      else "wait" "lk" "t"
  .

  Definition tl_acquire : val :=
    λ: "lk",
      let: "t" := get_ticket "lk" in
      wait "lk" "t"
  .

  Definition tl_release: val :=
      λ: "lk", FAA (Fst "lk") #1
  .

  Definition tl_c__cr := 2 + tl_exc.
  Definition tl_fl_B c := 2 * c + 3 + tl_exc.

  Program Definition TLPre: FairLockPre := {|    
    fl_c__cr := tl_c__cr;
    fl_B := tl_fl_B;
    fl_GpreS := TicketlockPreG;
    fl_GS := TicketlockG;
    fl_LK := fun Σ FLG HEAP => tl_LK;
    fl_degs_lh := fl_degs_lh0;
    fl_d__m := d__m0;
    fl_acq_lvls := lvls_acq;
    fl_create := tl_newlock;
    fl_acquire := tl_acquire;
    fl_release := tl_release;
  |}.
  Next Obligation.
    etrans; eauto.
  Defined.

  Section Proofs.

  Context {Σ: gFunctors}.
  Context {OHE: OM_HL_Env OP EM Σ}.

  Definition TAU_stored `{TLG: TicketlockG Σ} (lk: val) (c: nat) (cd: tau_codom Σ): iProp Σ :=
    let '(τ, π, q, Ob, L, Φ, RR) := cd in
    obls τ Ob ∗ sgns_levels_gt' Ob L ∗
    th_phase_frag τ π (q /2) ∗
    TAU τ (acquire_at_pre lk (FLP := TLPre) (FLG := TLG)) (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        L
        c
        (⊤ ∖ ↑fl_ι)
        π
        q
        (fun _ _ => Φ #())
        Ob
        (acq_FG_RR RR π (FLP := TLPre))
        (oGS' := ohe_oGS')
        . 

  Definition tau_interp `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) (i: nat) (cd: tau_codom Σ): iProp Σ :=
      let '((((((τ, π), q), _), _), Φ), _) := cd in
      (TAU_stored lk c cd ∗ ⌜ ow < i ⌝ ∨
       (((th_phase_frag τ π (q /2) -∗ Φ #()) ∗ rel_tok ∨ ticket_token i) ∗ ⌜ ow = i ⌝) ∨
       ticket_token i ∗ ⌜ i < ow ⌝).

  Arguments tau_interp _ _ _ _ _ cd: simpl nomatch. 

  Definition tau_map_interp `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) (TM: gmap nat tau_codom_gn): iProp Σ :=
    own tl_γ_tau_map ((● (Excl <$> TM)): authUR (gmapUR nat (exclR $ tau_codom_gn))) ∗
    [∗ map] i ↦ cd_gn ∈ TM,
      ∃ (Φ: val -> iProp Σ) (RR: option nat -> iProp Σ), saved_pred_own cd_gn.1.2 DfracDiscarded Φ ∗ saved_pred_own cd_gn.2 DfracDiscarded RR ∗
      let cd: tau_codom Σ := (cd_gn.1.1, Φ, RR) in
      tau_interp lk c ow i cd.
  
  Definition tl_inv_inner `{TicketlockG Σ} (tl: val) (c: nat): iProp Σ :=
    ∃ (l__ow l__tk: loc) (ow tk: nat) TM,
      ⌜ tl = (#l__ow, #l__tk)%V ⌝ ∗ ⌜ ow <= tk ⌝ ∗ exc_lb (tk - ow + 2) ∗
      l__ow ↦{/ 2} #ow ∗ l__tk ↦ #tk ∗ ow_exact ow ∗ held_auth (negb (ow =? tk)) ∗
      tokens_auth tk ∗
      ⌜ dom TM = set_seq 0 tk ⌝ ∗ tau_map_interp tl c ow TM ∗
      (⌜ ow = tk ⌝ → rel_tok).

  Lemma ticket_tau_alloc `{TicketlockG Σ} lk c ow TM n cd
    (FRESH: n ∉ dom TM):    
    tau_map_interp lk c ow TM -∗
    tau_interp lk c ow n cd
    ==∗ ∃ cd_gn, tau_map_interp lk c ow (<[ n := cd_gn ]> TM) ∗ ticket_tau n cd.
  Proof using.
    clear fl_degs_wl0 d__w LS_LB.
    iIntros "TMA TI". destruct_cd cd. 
    iMod (saved_pred_alloc Post DfracDiscarded) as (γ__p) "#POST"; [done| ].
    iMod (saved_pred_alloc RR DfracDiscarded) as (γ__r) "#RR"; [done| ].

    rewrite /tau_map_interp. iDestruct "TMA" as "[TMA PREDS]".
    iExists (τ, π, q, Ob, L, γ__p, γ__r).
    rewrite big_opM_insert. iFrame "PREDS". 
    2: { by apply not_elem_of_dom. }
    rewrite bi.sep_comm bi.sep_assoc. 
    iApply bupd_frame_r. iSplitL "TMA".
    2: { do 2 iExists _. iFrame "#∗". }
    rewrite /ticket_tau. do 2 (setoid_rewrite bi.sep_exist_r).
    do 2 iExists _. simpl. iFrame "#∗".  
    rewrite bi.sep_comm.
    rewrite -own_op. iApply own_update; [| by iFrame].
    apply auth_update_alloc.
    rewrite fmap_insert. apply alloc_singleton_local_update.
    2: done.
    apply not_elem_of_dom. set_solver.
  Qed.

  Lemma tau_map_ticket `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) TM i cd:
    tau_map_interp lk c ow TM -∗ ticket_tau i cd -∗
    ∃ cd_gn, ⌜ TM !! i = Some cd_gn ⌝ ∗ ⌜ cd_gn.1.1 = cd.1.1 ⌝ ∗
             saved_pred_own cd_gn.1.2 DfracDiscarded cd.1.2 ∗ saved_pred_own cd_gn.2 DfracDiscarded cd.2.
  Proof using.
    iIntros "TM TK". rewrite /tau_map_interp /ticket_tau.
    iDestruct "TM" as "[TMA SP]". iDestruct "TK" as (??) "(TK & SP1 & SP2)".
    destruct_cd cd. simpl.
    iExists (_, _, _, _, _, _, _).
    iFrame. simpl. iSplit; [| done].
    iCombine "TMA TK" as "TK". 
    iDestruct (own_valid with "TK") as %V%auth_both_valid_discrete.
    iPureIntro. destruct V as [IN V]. 
    apply singleton_included_exclusive_l in IN.
    2, 3: apply _ || done.
    apply leibniz_equiv_iff in IN.
    apply lookup_fmap_Some in IN as (?&IN&?).
    inversion IN. by subst.
  Qed.

  Lemma tau_map_ticket_interp `{TicketlockG Σ} TM i cd lk c ow:
    ticket_tau i cd -∗ tau_map_interp lk c ow TM -∗
    ∃ Φ' RR',
      let cd' := (cd.1.1, Φ', RR') in
      tau_interp lk c ow i cd' ∗ ticket_tau i cd ∗
      (tau_interp lk c ow i cd' -∗ tau_map_interp lk c ow TM) ∗
      (∀ v, ▷ (cd.1.2 v ≡ Φ' v)) ∗ (∀ r, ▷ (cd.2 r ≡ RR' r)). 
  Proof using.
    clear fl_degs_wl0 d__w LS_LB.
    iIntros "T TMI".
    rewrite /tau_map_interp. iDestruct "TMI" as "[AUTH TMI]". 
    iDestruct (tau_map_ticket with "[$] [$]") as (? ITH EQ) "(#SP1 & #SP2)".
    destruct_cd cd. 
    destruct cd_gn as [[]]. simpl in EQ. subst p.
    
    remember (τ, π, q, Ob, L, Post, RR) as cd. simpl.
    rewrite {2}(map_split TM i).
    rewrite big_opM_union.
    2: { apply map_disjoint_dom. destruct lookup; set_solver. }
    iDestruct "TMI" as "[TKI CLOS]".
    rewrite ITH. simpl. rewrite big_sepM_singleton.
    
    iFrame "T AUTH".
    iDestruct "TKI" as (Φ' RR') "(#SP1' & #SP2' & TI')". simpl.    
    do 2 iExists _. iSplitL "TI'".
    { subst cd. simpl. iFrame. }
    iSplitL.
    2: { iSplit; iIntros.
         - iDestruct (saved_pred_agree with "SP1 SP1'") as "foo".
           iApply "foo".
         - iDestruct (saved_pred_agree with "SP2 SP2'") as "foo".
           iApply "foo". }
    iIntros "TKI".
    iDestruct (big_sepM_insert_delete with "[CLOS TKI]") as "TMI".
    2: { rewrite insert_id; [| done]. iFrame. }
    simpl. 
    iFrame.  do 2 iExists _. iFrame "#∗".
    subst cd. iFrame. 
  Qed.

  Lemma TMI_extend_acquire `{TicketlockG Σ} lk c ow TM (cd: tau_codom Σ)
    (DOM: dom TM = set_seq 0 ow):
    let '((((((τ, π), q), _), _), Φ), _) := cd in   
    tau_map_interp lk c ow TM -∗ rel_tok -∗
    (th_phase_frag τ π (q /2) -∗ cd.1.2 #()) ==∗
    ∃ cd_gn, tau_map_interp lk c ow (<[ ow := cd_gn ]> TM) ∗ ticket_tau ow cd.
  Proof using.
    clear fl_degs_wl0 d__w LS_LB.
    destruct_cd cd. simpl. 
    iIntros "TMI RTOK TAU".    
    iMod (ticket_tau_alloc with "[$] [RTOK TAU]") as "FOO".
    3: { by iFrame. }
    { rewrite DOM elem_of_set_seq. lia. }
    rewrite /tau_interp. iRight. iLeft. iSplit; [| done].
    iLeft. iFrame. 
  Qed.

  Lemma tokens_alloc `{TicketlockG Σ} (N: nat):
    tokens_auth N ==∗ tokens_auth (S N) ∗ ticket_token N.
  Proof using.
    clear LS_LB.
    iIntros. rewrite /tokens_auth /ticket_token.
    rewrite -own_op. iApply own_update; [| by iFrame].
    apply auth_update_alloc.
    rewrite set_seq_S_end_union_L. simpl.
    etrans.
    1: eapply gset_disj_alloc_empty_local_update.
    2: { reflexivity. }
    apply disjoint_singleton_l. by (intros ?%elem_of_set_seq; lia).
  Qed.

  Definition tl_is_lock `{TicketlockG Σ} lk c := inv fl_ι (tl_inv_inner lk c).

  Lemma tl_newlock_spec `{TicketlockPreG Σ} τ π c
    (BOUND: fl_c__cr TLPre <= LIM_STEPS):
      {{{ cp π d__m0 ∗ th_phase_eq τ π }}}
        tl_newlock #() @ τ
      {{{ lk, RET lk; ∃ TLG: TicketlockG Σ, tl_LK (lk, 0, false) ∗ tl_is_lock lk c ∗ th_phase_eq τ π }}}.
  Proof using LS_LB.
    clear fl_degs_wl0 d__w.
    iIntros (Φ) "(CP & PH) POST". rewrite /tl_newlock.
    pure_step_hl.

    MU_by_BOU.

    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { apply fl_degs_em. }
    iModIntro. burn_cp_after_BOU. 
    
    wp_bind (ref _)%E. iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iIntros "!> %l__ow OW _". MU_by_burn_cp.
    pure_steps. wp_bind (Rec _ _ _)%E. pure_steps. 
    
    wp_bind (ref _)%E. iApply sswp_MU_wp; [done| ].
    iApply wp_alloc. iIntros "!> %l__tk TK _". MU_by_burn_cp. pure_steps.
    
    iMod (own_alloc (● ∅ ⋅ ◯ _: authUR (gmapUR nat (exclR $ tau_codom_gn)))) as (γ__tm) "[TM_AUTH TM_FRAG]".
    { apply auth_both_valid_2; [| reflexivity]. done. }
    iMod (@own_alloc _ _ _ (● (GSet ∅) ⋅ _: authUR (gset_disjUR natO))) as (γ__toks) "[TOKS_AUTH TOKS_FRAG]".
    { apply auth_both_valid_2; [| reflexivity]. done. }
    iMod (own_alloc (● Excl' false ⋅ ◯ _: (excl_authUR boolO))) as (γ__h) "[HELD_AUTH HELD_FRAG]".
    { apply auth_both_valid_2; [| reflexivity]. done. }
    iMod (own_alloc (●MN 0: mono_natUR)) as (γ__lb) "LB_AUTH".
    { apply mono_nat_auth_valid. }
    iMod (own_alloc (Excl ())) as (γ__rt) "RT".
    { done. }
    rewrite -{1}Qp.inv_half_half. iDestruct "OW" as "[OW OW']".

    eset (TLG := Build_TicketlockG _ _ γ__tm γ__toks γ__h γ__lb γ__rt).
    iApply fupd_wp.
    iMod (inv_alloc fl_ι _ (tl_inv_inner _ c) with "[-POST OW' HELD_FRAG CPS PH]") as "#INV".
    { rewrite /tl_inv_inner. iNext. do 5 iExists _. iFrame.
      do 2 (iSplit; [done| ]). iSplit.
      { simpl. iApply exc_lb_le; [| done]. unfold tl_exc. lia. }
      rewrite Nat.eqb_refl. iFrame.
      iSplit.
      { iPureIntro. apply dom_empty_L. }
      iSplit; [| done].
      rewrite /tau_map_interp. rewrite fmap_empty. iFrame. set_solver. }

    iModIntro. pure_steps.
    wp_bind (Rec _ _ _)%V. pure_steps.
    iApply "POST". iExists _. iFrame "#∗".
    iExists _. done.
  Qed.

  Section AfterInit.
        
  Context {TLG: TicketlockG Σ}.
    
  (* TODO: find existing *)
  Lemma fupd_frame_all E1 E2 P:
    ((|==> P) ∗ |={E1, E2}=> emp: iProp Σ) ⊢ |={E1, E2}=> P.
  Proof using.
    iIntros "[P ?]". iMod "P". by iFrame.
  Qed.

  Definition wait_res o' t τ π q Ob Φ RR: iProp Σ :=
    ⌜ o' <= t ⌝ ∗
    ow_lb o' ∗ cp_mul π d__h0 (t - o') ∗
    (RR (Some o') ∨ cp π d__h0) ∗
    cp_mul π d__w 10 ∗
    let cd: tau_codom Σ := (τ, π, q, Ob, lvls_acq, Φ, RR) in
    ticket_token t ∗ ticket_tau t cd
    ∗ th_phase_frag τ π (q / 2)
  .

  Lemma get_ticket_spec s (lk: val) c (τ: locale heap_lang) (π: Phase) (q: Qp)
    Φ
    (Ob: gset SignalId)
    RR
    (LIM_STEPS': fl_B TLPre c <= LIM_STEPS):
    tl_is_lock lk c ∗ exc_lb 20 ⊢
        TAU_FL τ
        (acquire_at_pre lk (FLP := TLPre) (FLG := TLG))
        (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        {[lvl_acq]}
        c π q (fun _ _ => Φ #())
        Ob
        (acq_FG_RR RR π (FLP := TLPre))        
        -∗
        TLAT_pre τ {[lvl_acq]} d__e π q Ob (oGS' := ohe_oGS') -∗
        cp_mul π d__w 10 -∗
        WP (get_ticket lk) @ s; τ; ⊤ {{ tv, ∃ (t o': nat), ⌜ tv = #t ⌝ ∗ wait_res o' t τ π q Ob Φ RR }}.
  Proof using fl_degs_wl0 LS_LB.
    iIntros "[#INV #EB]". rewrite /TLAT_FL /TLAT.
    iIntros "TAU PRE CPS".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(OB & #SGT & PH & CPe)".
    rewrite /get_ticket.

    pure_steps.

    (* TODO: ??? worked fine when get_ticket was inlined into tl_acquire:
       wp_bind (Snd _)%E. *)
    assert (FAA (Snd lk) #1 = fill_item (FaaLCtx #(LitInt 1)) (Snd lk)) as CTX by done.
    iApply (wp_bind [(FaaLCtx #1)] s ⊤ τ (Snd lk) (Λ := heap_lang)). simpl.
    
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & #EBd & >OW & >TK & >EXACT & >HELD & >TOKS & >%DOM__TM & TAUS & RTOK)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    rewrite /TAU_FL. rewrite TAU_elim. iMod "TAU" as (st) "[[ST %ST__lk] TAU]".
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_faa with "TK").
    iIntros "!> TK'". iNext. MU_by_BOU.

    simpl.
    apply Nat.le_sum in LEot as [d ->].

    iMod (exchange_cp_upd with "CPe [$]") as "CPSh".
    { apply (reflexive_eq (S (S d))). lia. }
    { apply fl_degs_he. }
    { simpl in LIM_STEPS'. lia. }
    iDestruct (cp_mul_take with "CPSh") as "[CPSh CPh]".

    iMod (exchange_cp_upd _ _ _ _ 10 with "[$] EB") as "CPS'".
    { lia. }
    { etrans; [apply fl_degs_wl0 | apply fl_degs_lh0]. }
    { try_solve_bounds. use_rfl_fl_sb. }

    iMod (increase_eb_upd with "EBd") as "#EBd'".
    { try_solve_bounds. use_rfl_fl_sb. }
    iClear "EBd".

    iDestruct (ow_exact_lb with "[$]") as "[EXACT LB]".
    iMod (tokens_alloc with "[$]") as "[TOKS TOK]".

    iDestruct (th_phase_frag_halve with "PH") as "[PH PH']".
    destruct (Nat.eq_0_gt_0_cases d) as [-> | QUEUE].
    2: { BOU_burn_cp.
         rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. simpl.
         iModIntro.
         pure_steps.
         do 2 iExists _.
         iRevert "PH". iFrame. iIntros "PH". rewrite Nat.add_sub'.
         rewrite {1}cp_mul_take. iDestruct "CPSh" as "[CPSh CPh]".
         iFrame.

         iDestruct "TAU" as "[_ [_ AB]]".
         iMod ("AB" with "[ST]") as "TAU"; [by iFrame| ].
         iMod (ticket_tau_alloc _ c ow TM (ow + d) with "[$] [TAU PH OB]") as (cd_gn) "[TMI TK]".
         { rewrite DOM__TM. intros ?%elem_of_set_seq. lia. }
         { Unshelve. 2: repeat eapply pair.
           simpl. iLeft. iFrame "OB PH SGT". iSplit; [| iPureIntro; lia]. 
           iApply "TAU". }

         iFrame "TK". 
         iApply fupd_frame_all.
         iSplitR. 
         { iModIntro. iSplit; [done| ]. iPureIntro; lia. }

         iClear "RTOK".
         iMod ("CLOS" with "[HELD TK' OW EXACT TOKS TMI]") as "_"; [| done].
         iNext. rewrite /tl_inv_inner.
         do 5 iExists _. iFrame.

         rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
         replace (((ow + d)%nat + 1)%Z) with (Z.of_nat $ S (ow + d)) by lia.
         iFrame. rewrite !bi.sep_assoc. iSplit.
         2: { iIntros "%". lia. }
         replace ((S (ow + d) - ow + 2)) with (S (d + 2)) by lia. iFrame "#∗".
         iPureIntro. split.
         { split; [done| lia]. }
         rewrite dom_insert_L DOM__TM.
         by rewrite set_seq_S_end_union_L. }

    rewrite (proj2 (Nat.eqb_eq _ _)); [| done]. simpl.

    rewrite /tl_LK. destruct st as [[]]. iDestruct "ST" as (??) "(-> & OW' & HELD')".
    rewrite !Nat.add_0_r. rewrite Nat.add_0_r in DOM__TM.
    iDestruct "TAU" as "[_ [COMM _]]".
    iDestruct (held_agree with "[$] [$]") as "<-".
    rewrite /tl_LK.

    iMod (held_update _ _ true with "[$] [$]") as "[HELD HELD']".

    iMod ("COMM" with "[OB PH'] [HELD' OW']") as "COMM". 
    { iFrame. iPureIntro. by apply Qp.div_le. }
    { Unshelve. 2: eapply (pair (pair _ _ ) _). 
      rewrite /acquire_at_post. simpl. rewrite /tl_LK.
      iFrame. iSplit; [| done]. iExists _. done. }
    { try_solve_bounds. use_rfl_fl_sb. }

    BOU_burn_cp. iModIntro. iApply wp_value.
    iMod "COMM" as "Φ".
    rewrite -{1}(Qp.div_2 q). rewrite Qp.add_sub. simpl.

    iSpecialize ("RTOK" with "[//]"). 
    iMod (TMI_extend_acquire _ _ _ _ (((((((_), _), _), _), _), _), _) with "[$] [$] [$]") as (?) "[TMI TK]"; eauto.

    do 2 iExists _. iFrame. iApply fupd_frame_all.
    iSplitL "CPSh".
    { rewrite Nat.sub_diag.
      iModIntro.
      iSplit; [done| ]. iSplit; [done| ].
      rewrite bi.sep_or_l. iRight.
      by rewrite -cp_mul_take. }
    
    iApply "CLOS". iNext. rewrite /tl_inv_inner.
    rewrite -(Nat.add_1_r ow).
    replace (Z.of_nat ow + 1)%Z with (Z.of_nat (ow + 1)) by lia.
    do 5 iExists _. iFrame.
    rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. iFrame.
    iFrame. rewrite !bi.sep_assoc. iSplit.
    2: { iIntros "%". lia. }
    rewrite Nat.sub_diag Nat.add_sub'. iFrame "#∗".
    iPureIntro. split.
    { split; [done| lia]. }
    rewrite dom_insert_L DOM__TM.
    rewrite set_seq_add_L. simpl.
    set_solver.
  Qed.

  Lemma wait_spec (lk: val) c o' (t: nat) τ π q Ob Φ RR
    (LIM_STEPS': fl_B TLPre c <= LIM_STEPS):
    tl_is_lock lk c ∗ exc_lb 20 ∗ wait_res o' t τ π q Ob Φ RR 
    ⊢ WP (wait lk #t) @ τ {{ v, Φ v ∗ rel_tok }}.
  Proof using fl_degs_wl0.
    clear LS_LB.
    iLöb as "IH" forall (o').
    rewrite {2}/wait_res. iIntros "(#INV & #EXC & %LEo't & OW_LB & CPSh & RR & CPS & TOK & TAU & PH)".
    rewrite {2}/wait.
    pure_steps.

    wp_bind (Fst _)%E.
    (* TODO: make a lemma? and remove duplicates *)
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    wp_bind (! _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & #EBd & >OW & >Ltk & >EXACT & >HELD & >TOKS & >%DOM__TM & TAUS & RTOK)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_load with "[OW]"); [done| ]. iIntros "!> OW".
    
    iDestruct (ticket_token_bound with "[$] [$]") as %LTttk.
    destruct (decide (ow = t)) as [-> | QUEUE].
    { rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
      iDestruct (tau_map_ticket_interp with "[$] [$]") as (??) "(TAUtk & TK & TMI_CLOS & #EQ1 & #EQ2)".
      rewrite {1}/tau_interp. iDestruct "TAUtk" as "[[? %] | [[TAUtk _] | [? %]]]".
      1, 3: lia.
      simpl. iDestruct "TAUtk" as "[[Φ RTOK'] | TOK']".
      2: { by iDestruct (ticket_token_excl with "[$] [$]") as %?. }
      iSpecialize ("TMI_CLOS" with "[TOK]").
      { rewrite /tau_interp. iRight. iLeft. iSplit; [| done]. iFrame. }

      MU_by_burn_cp. 
      
      iModIntro. pure_steps.
      iMod ("CLOS" with "[TMI_CLOS OW TOKS HELD EXACT Ltk]") as "_".
      { rewrite /tl_inv_inner. iNext. do 5 iExists _. iFrame "#∗".
        rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
        rewrite !bi.sep_assoc. iSplitL; [by iFrame| ].
        iIntros "%". lia. }
      iModIntro.

      wp_bind (Rec _ _ _)%V. pure_steps.
      wp_bind (_ = _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step.
      { simpl. tauto. }
      iNext. MU_by_burn_cp. rewrite bool_decide_eq_true_2; [| tauto].
      pure_steps. iFrame.
      iRewrite ("EQ1" $! #()). by iApply "Φ". }

    iDestruct (tau_map_ticket_interp with "[$] [$]")  as (??) "(TAUtk & TK & TMI_CLOS & #EQ1 & #EQ2)".
    rewrite {1}/tau_interp.
    apply Nat.le_lteq in LEot as [LTot | EQ].
    2: { subst tk. iDestruct "TAUtk" as "[[? %] | [[? %] | [? %]]]".
         all: try lia.
         by iDestruct (ticket_token_excl with "[$] [$]") as %?. }

    iDestruct "TAUtk" as "[[TAUs %] | [[? %] | [? %]]]".
    all: try lia.
    2: { by iDestruct (ticket_token_excl with "[$] [$]") as %?. }
    rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
    rewrite /TAU_stored. iDestruct "TAUs" as "(OB & #SLT & PH' & TAUs)".
    rewrite TAU_elim.
    rewrite /TAU_acc. iNext. MU_by_BOU.
    iApply BOU_invs. simpl.
    iMod "TAUs" as ([[lk_ r] b]) "[PRE [WAIT _]]".
    rewrite /acquire_at_pre. simpl. iDestruct "PRE" as "[>(%&%&%EQ&OW'&HELD') ->]".
    inversion EQ. subst l__ow0 l__tk0. clear EQ.
    iDestruct (held_agree with "[$] [$]") as %<-.
    iDestruct (pointsto_agree with "[$] [$]") as %EQ. inversion EQ as [EQ'].
    apply Nat2Z.inj' in EQ'. subst r. clear EQ.
    iDestruct (ow_lb_le_exact with "[$] [$]") as %LBow.
    replace (t - o') with (t - ow + (ow - o')) by lia.
    rewrite cp_mul_split. iDestruct "CPSh" as "[CPSh CPSh']".
    iSpecialize ("WAIT" with "[OB PH RR CPSh']").
    { iFrame. iSplitR.
      { by iApply sgns_levels_gt'_ge'. }
      iSplit.
      { iPureIntro. by apply Qp.div_le. }
      iSplit; [done| ].
      iRewrite ("EQ2" $! (Some o')) in "RR".
      apply Nat.le_sum in LBow as [d ->]. rewrite Nat.add_sub'.
      destruct d.
      - by rewrite Nat.add_0_r. 
      - rewrite cp_mul_take. iDestruct "CPSh'" as "[??]". iFrame. }
    iModIntro.
    
    iMod "WAIT" as "((RR & CP) & PH & OB & CLOS')".
    { try_solve_bounds. use_rfl_fl_sb. }
    iSpecialize ("CLOS'" with "[OW' HELD']").
    { iFrame. iSplit; [| done]. iNext. iExists _. eauto. }

    iMod (exchange_cp_upd with "[$] EXC") as "CPS'". 
    { reflexivity. }
    { apply fl_degs_wl0. }
    { try_solve_bounds. use_rfl_fl_sb. }

    iDestruct (cp_mul_split with "[CPS CPS']") as "CPS"; [iFrame| ]. simpl.
    iModIntro. iMod "CLOS'" as "TAUs". iModIntro. burn_cp_after_BOU.
    iModIntro. pure_steps.
    iSpecialize ("TMI_CLOS" with "[TAUs SLT OB PH']").
    { rewrite /tau_interp. iLeft. iSplit; [| done].
      rewrite /TAU_stored. by iFrame. }
    
    iClear "OW_LB". iDestruct (ow_exact_lb with "[$]") as "[EXACT OW_LB]".
    iMod ("CLOS" with "[TMI_CLOS OW TOKS HELD EXACT Ltk]") as "_".
    { rewrite /tl_inv_inner. iNext. do 5 iExists _. iFrame.
      rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. iFrame "#∗".
      rewrite !bi.sep_assoc. iSplit.
      { iPureIntro. repeat split; eauto. lia. }
      iIntros "->". lia. }
    iModIntro.
    wp_bind (Rec _ _ _)%V. pure_steps.
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { simpl. tauto. }
    iNext. MU_by_burn_cp. rewrite bool_decide_eq_false_2.
    2: { intros [=EQ%Nat2Z.inj']. lia. }
    do 2 pure_step_cases.

    iApply ("IH" $! ow).
    iFrame "#∗". iSplit; [iPureIntro; lia| ]. iSplitL "RR".
    { iRewrite -("EQ2" $! (Some ow)) in "RR". iFrame. }
    replace 21 with (10 + 11) by lia. rewrite cp_mul_split.
    iDestruct "CPS" as "[??]". iFrame.
  Qed.

  Lemma rel_tok_excl: rel_tok -∗ rel_tok -∗ ⌜ False ⌝.
  Proof using.
    iStartProof. rewrite bi.wand_curry -own_op.
    iIntros "X". by iDestruct (own_valid with "[$]") as %V.
  Qed.

  Lemma tau_map_interp_update (TM: gmap nat tau_codom_gn) (l__ow l__tk: loc) c (ow: nat)
    (lk := (#l__ow, #l__tk)%V)
    (next := bool_decide (ow + 1 ∈ dom TM)):
    tau_map_interp lk c ow TM -∗ held_auth false -∗
    l__ow ↦{/ 2} #(ow + 1)%nat -∗ rel_tok -∗
    BOU (⊤ ∖ ↑fl_ι) c (held_auth next ∗ l__ow ↦{/ 2} #(ow + 1)%nat ∗
                        (⌜ next = false ⌝ → rel_tok) ∗
                        tau_map_interp lk c (ow + 1) TM).
  Proof using.
    clear fl_degs_wl0 d__w LS_LB.
    iIntros "TMI AUTH LOW RTOK". rewrite /tau_map_interp.

    rewrite {2 4}(map_split TM ow).
    rewrite !big_opM_union.
    2, 3: apply map_disjoint_dom; destruct lookup; set_solver.
    iDestruct "TMI" as "(TM & OW & TMI)".

    rewrite (map_split (delete _ _ ) (ow + 1)).
    rewrite !big_opM_union.
    2, 3: apply map_disjoint_dom; destruct lookup; set_solver.
    iDestruct "TMI" as "[OW' TMI]".
    rewrite !bi.sep_assoc. iApply (BOU_frame_r with "[TMI]").
    { iApply (big_sepM_impl with "[$]").
      iIntros "!>" (i cd ITH) "TI".
      apply lookup_delete_Some in ITH as [? [? ITH]%lookup_delete_Some].
      rewrite /tau_interp. destruct cd as [[[[[[]]]]]].
      iDestruct "TI" as (??) "(#SP1 & #SP2 & [[? %] | [[? %] | [? %]]])"; try lia.
      all: do 2 iExists _; iFrame "SP1 SP2". 
      - iLeft. iFrame. iPureIntro. lia.
      - do 2 iRight. iFrame. iPureIntro. lia. }
    rewrite -bi.sep_assoc bi.sep_comm -bi.sep_assoc.
    iPoseProof BOU_frame_l as "foo". rewrite bi.wand_curry. iApplyHyp "foo".

    iApply (bi.wand_frame_l with "[-RTOK OW]").
    2: { destruct (TM !! ow) as [cd| ] eqn:OW.
         2: { iSplitR "RTOK"; [| iAccu]. set_solver. }
         simpl. rewrite !big_sepM_singleton.
         rewrite /tau_interp. destruct cd as [[[[[[]]]]]].
         iDestruct "OW" as (??) "(#SP1 & #SP2 & [[? %] | [[OW %] | [? %]]])"; try lia.
         iDestruct "OW" as "[CD | TT]".
         { iDestruct "CD" as "[_ RT]".
           by iDestruct (rel_tok_excl with "[$] [$]") as "?". }
         iFrame. do 2 iExists _. iFrame "SP1 SP2".
         do 2 iRight. iFrame. iPureIntro. lia. }
    iIntros "RTOK".
    rewrite !lookup_delete_ne; [| lia].
    destruct (TM !! (ow + 1)) as [[[[[[[]]]]]]| ] eqn:OW'; simpl; subst next.
    2: { rewrite bool_decide_eq_false_2; [| by apply not_elem_of_dom].
         iModIntro. iFrame. set_solver. }
    simpl. rewrite bool_decide_eq_true_2; [| by apply elem_of_dom].
    rewrite !big_sepM_singleton.
    rewrite {1}/tau_interp.
    iDestruct "OW'" as (??) "(#SP1 & #SP2 & [[TAU %] | [[? %] | [? %]]])"; try lia.
    rewrite /TAU_stored.
    simpl. iDestruct "TAU" as "(OB' & #SLT' & PH' & TAUs')". simpl.
    rewrite TAU_elim. simpl. rewrite /TAU_acc.
    
    iApply BOU_invs.
    iMod "TAUs'" as ([[lk_ r] b]) "[PRE [_ [COMM _]]]". iModIntro.

    rewrite /acquire_at_pre. simpl.

    iDestruct "PRE" as "[foo ->]".
    iApply (class_instances_later.elim_modal_timeless false). 
    2: done.
    2: iSplitL "foo"; [iApply "foo"| ].
    { apply _. }
    iIntros "(%&%&%EQ&LOW'&HELD')".

    subst lk. inversion_clear EQ.
    iDestruct (held_agree with "[$] [$]") as %<-.
    iDestruct (pointsto_agree with "LOW LOW'") as %EQ.
    inversion EQ as [EQ'']. assert (r = ow + 1) as -> by lia. clear EQ'' EQ.

    iMod (held_update _ _ true with "[$] [$]") as "[HELD HELD']".
    iMod ("COMM" with "[$OB' $PH'] [HELD' LOW']") as "CLOS'".
    { iPureIntro. by apply Qp.div_le. }
    { rewrite /acquire_at_post. simpl.
      Unshelve. 2: eapply (pair (pair _ _) _). iFrame.  
      iSplit; [| done].
      iExists _. eauto. }
    iModIntro. 

    iFrame "HELD LOW TM".
    iMod "CLOS'". iModIntro.
    rewrite /tau_interp. iSplitL.
    2: { by iIntros "%". }
    do 2 iExists _. iFrame "SP1 SP2". 
    iRight. iLeft.
    rewrite -{1}(Qp.div_2 q). rewrite Qp.add_sub. simpl.
    iSplit; [| done]. iLeft. iFrame.
  Qed.

  Lemma tl_release_spec (lk: val) c τ:
    tl_is_lock lk c ∗ rel_tok ⊢
        TLAT_FL τ
        (release_at_pre lk (FLP := TLPre) (FLG := TLG))
        (release_at_post lk (FLP := TLPre) (FLG := TLG))
        ∅
        AC_none
        (fun _ _ => None)
        (fun _ '(_, r, _) => #r)
         c
         (tl_release lk)        
        (FLP := TLPre).
  Proof using fl_degs_wl0 LS_LB.
    iIntros "(#INV & RT)". rewrite /TLAT_FL /TLAT.
    iIntros (Φ q π Ob) "%LIM_STEPS' PRE TAU".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(OB & _ & PH & CP)".
    rewrite /tl_release.

    pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "[CPS #EB]".
    { trans d__e; [trans d__h0| ]; [trans d__l0|..]; eauto. }
    BOU_burn_cp.
    
    assert (FAA (Fst lk) #1 = fill_item (FaaLCtx #(LitInt 1)) (Fst lk)) as CTX by done.
    iApply (wp_bind [(FaaLCtx #1)] NotStuck ⊤ τ (Fst lk) (Λ := heap_lang)). simpl.
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & >#EBD & >OW & >Ltk & >EXACT & >HELD & >TOKS & >%DOM__TM & TAUS & _)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ].
    rewrite TAU_elim.
    iMod "TAU" as ([[]]) "[ST TAU]". iModIntro.
    rewrite /release_at_pre. simpl.

    (* TODO: fix later elimination *)
    match goal with | |- envs_entails _ ?P => iAssert (P -∗ P)%I as "GOAL"; [iIntros "X"; by iApply "X"| ] end.
    iDestruct "ST" as "(>(%&%&%&OW'&HELD')&[% %EQ])". subst.
    iApplyHyp "GOAL".
    inversion EQ. subst. clear EQ.
    iDestruct (pointsto_agree with "OW OW'") as %EQ. inversion EQ as [EQ'].
    apply Nat2Z.inj' in EQ'. subst n. clear EQ.
    iCombine "OW OW'" as "OW". rewrite Qp.inv_half_half.
    iDestruct (held_agree with "[$] [$]") as %EQ.
    destruct Nat.eqb eqn:EQ'; [done| ]. apply PeanoNat.Nat.eqb_neq in EQ'. clear EQ.
    iApply (wp_faa with "[$]"). iIntros "!> OW".
    iDestruct "TAU" as "[_ [TAU _]]".
    iNext. MU_by_BOU.

    iDestruct (th_phase_frag_halve with "PH") as "[PH PH']".    

    iMod (held_update _ _ false with "[$] [$]") as "[HELD HELD']".
    iMod (ow_exact_increase _ (ow + 1) with "[$]") as "[EXACT OW_LB]"; [lia| ].    
    rewrite -{2}Qp.inv_half_half. rewrite pointsto_fractional. iDestruct "OW" as "[OW OW']".

    iSpecialize ("TAU" with "[$OB $PH']"). 
    { iPureIntro. apply Qp.div_le. done. }

    iMod ("TAU" $! (_, _, _) with "[HELD' OW']") as "CLOS'".
    { rewrite /release_at_post. iFrame.
      iSplit; [| by eauto].
      do 2 iExists _. iSplitR; [by eauto| ]. iFrame.
      Set Printing Coercions.
      by rewrite Nat2Z.inj_add. }
    { try_solve_bounds. use_rfl_fl_sb. }
   
    iApply BOU_proper.
    1, 2: reflexivity.
    { apply bi.sep_comm. }
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]".

    iApply (BOU_frame_l with "[CP PH]").
    { iExists _. by iFrame. }
    iApply (BOU_mask_comm' with "[-CLOS'] [$]"); [set_solver| ].
    iIntros "Φ". simpl.

    iMod (tau_map_interp_update with "[$] [$] [OW] [$]") as "UPD".
    { by rewrite Nat2Z.inj_add. }
    { try_solve_bounds. use_rfl_fl_sb. }
    iDestruct "UPD" as "(HELD & OW & RTOK & TMI)". 
    iModIntro. iIntros "PH".
    rewrite -{1}(Qp.div_2 q). rewrite Qp.add_sub. simpl. iSpecialize ("Φ" with "[$]").
    
    pure_steps.
    iMod ("CLOS" with "[-Φ CPS OW_LB]") as "_".
    2: { iModIntro. by iApply "Φ". }
    iNext. rewrite /tl_inv_inner. do 5 iExists _.
    iRevert "EBD". iFrame. iIntros "#EBd".
    iSplit; [done| ]. iSplit; [iPureIntro; lia| ].
    erewrite bool_decide_ext with (Q := ow + 1 ≠ tk). 
    2: { rewrite DOM__TM elem_of_set_seq. simpl. lia. }
    iSplitR.
    { iApply (exc_lb_le with "EBd"). lia. }
    rewrite bi.sep_assoc. iSplitR "RTOK".
    2: { iApply bi.impl_proper; [..| done | by iFrame].
         rewrite bool_decide_eq_false. iPureIntro. tauto. }
    iSplit; [| done].
    rewrite /held_auth. erewrite Excl_proper; [by iFrame| ].
    destruct Nat.eqb eqn:OW'.
    - apply Nat.eqb_eq in OW'. apply bool_decide_eq_false. lia.
    - apply Nat.eqb_neq in OW'. apply bool_decide_eq_true. lia.
  Qed.

  Lemma tl_acquire_spec (lk: val) c τ:
    tl_is_lock lk c ⊢
        TLAT_FL_RR τ 
        (acquire_at_pre lk (FLP := TLPre) (FLG := TLG))
        (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        (fl_acq_lvls TLPre)
        (fun '(_, _, b) => ⌜ b = true ⌝)
        (fun _ _ => Some $ rel_tok)
        (fun _ _ => #())
        c (fl_acquire TLPre lk)
        (FLP := TLPre)
        .
  Proof using fl_degs_wl0 d__w LS_LB.
    iIntros "#INV". rewrite /TLAT_FL /TLAT.
    iIntros (Φ q π Ob RR) "%LIM_STEPS' PRE TAU".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(OB & #SGT & PH & CP)".

    rewrite /tl_acquire. pure_step_hl. MU_by_BOU.
    iMod (first_BOU with "[$]") as "(CPSe & #EB)".
    { apply fl_degs_em. }
    iDestruct (cp_mul_take with "CPSe") as "[CPSe CPe]".
    iMod (exchange_cp_upd with "[$] [$]") as "CPSh".
    { reflexivity. }
    { apply fl_degs_he. }
    { try_solve_bounds. simpl.
      rewrite /tl_fl_B. rewrite /tl_exc. lia. }
    iDestruct (cp_mul_take with "CPSh") as "[CPSh CPh]".
    iMod (exchange_cp_upd _ _ d__w with "[CPh] [$]") as "CPS".
    { reflexivity. }
    { do 2 (etrans; eauto). }
    { done. }
    { try_solve_bounds. simpl. 
      rewrite /tl_fl_B. rewrite /tl_exc. lia. }
    BOU_burn_cp.
    replace 19 with (10 + 9) at 3 by lia.
    iDestruct (cp_mul_split with "CPS") as "[CPS1 CPS]".

    set (post := (fun x => bi_wand rel_tok (Φ x))). 
    
    pure_steps.
    rewrite cp_mul_take. iDestruct "CPSe" as "[CPSe CPe]".
    iApply (wp_wand with "[TAU OB PH CPe CPS1]").
    { iApply (get_ticket_spec with "[$] [TAU] [OB PH CPe] [$]").
      { done. }
      { simpl. rewrite /TAU_FL. simpl.
        iApply (TAU_Proper with "[$]").
        all: try reflexivity.
        Unshelve. 3: exact post. all: done. }
      rewrite /TLAT_pre. iFrame "#∗". }
    simpl. iIntros (?) "(%&%&->&WR)".
    rewrite /wait_res.

    do 6 rewrite bi.sep_assoc.    
    iDestruct "WR" as "[WR_ PH]".

    wp_bind (Rec _ _ _)%V.
    do 3 pure_step_cases.
    iApply (wp_wand with "[WR_ PH]").
    { iApply wait_spec; eauto.
      do 5 rewrite -bi.sep_assoc. iDestruct "WR_" as "(?&?&?&?&?&?&?)".
      iFrame "#∗". }

    subst post. simpl. iIntros (?) "[POST ?]". by iApply "POST".
  Qed.

  End AfterInit.

  End Proofs.


  Program Definition TL_FL: FairLock (FLP := TLPre) := {|
    fl_is_lock {Σ} {TLG: TicketlockG Σ} {FLG: OM_HL_Env OP EM Σ} := @tl_is_lock _ FLG TLG;
    fl_release_token _ FLG := @rel_tok _ FLG;
  |}. 
  Next Obligation.
    iIntros "%%% %%%% % !> (CP & PH) POST".
    unshelve iApply (tl_newlock_spec with "[-POST] [$]").
    { eauto. }
    { done. }
    iFrame.
  Qed.
  Next Obligation.
    iIntros "%%% %%% #LOCK".
    iApply (tl_acquire_spec with "[$]").
  Qed.
  Next Obligation.
    iIntros "%%% %%% (#LOCK & RT)".
    iApply (tl_release_spec with "[$]").
  Qed.
  Fail Next Obligation. 

End Ticketlock.
