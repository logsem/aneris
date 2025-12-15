From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len trace_utils. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context om_wfree_inst wptp_gen pwp wfree_traces calls.
From lawyer.nonblocking.tokens Require Import pwp_ext om_wfree_inst_tokens.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From lawyer Require Import action_model sub_action_em.
From heap_lang Require Import lang.


Close Scope Z.


Section WaitFreePR.

  Let OP := om_hl_OP (OP_HL := OP_HL_WF). 
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} _ _ => ⌜ True ⌝%I).

  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let tc := tctx_tpctx ic. 
  Let Ki := tpctx_ctx tc.
  Let τi := tpctx_tid tc. 

  Context `(WFST: WaitFreeSpecToken m).
  Let F := wfst_F _ WFST. 
  
  Open Scope WFR_scope. 

  Local Definition OHE {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}:
    OM_HL_Env OP_HL_WF EM Σ.
  esplit. 
  - apply AMU_lift_top.
  - intros.
    iIntros. iApply AMU_lift_top; [(try rewrite nclose_nroot); done| ].
    iFrame.
  Unshelve.
  exact {| heap_iemgs := Hinv |}.
  Defined.

  Lemma get_call_wp {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} {UT: UnitToken Σ}
    (a: val) π:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv _ WFST) -∗
    cp_mul π0 d0 F -∗ th_phase_frag τi π (1 / 2)%Qp -∗ unit_tok -∗
    WP m a @ τi {{ _, ⌜ True ⌝ }}.
  Proof using.
    simpl. iIntros "#INV CPS PH TOK".
    pose proof (@wfst_spec _ WFST _ EM Σ OHE) as SPEC. 
    iApply (SPEC with "[-]").
    2: { by iIntros "!> **". } 
    iSplitL "CPS"; [| by iFrame].
    iApply (cp_mul_weaken with "[$]"); [| done].
    apply phase_le_init.
  Qed.

  Definition no_extra_obls (_: cfg heap_lang) (δ: mstate M) :=
    forall τ', default ∅ (ps_obls δ !! τ') ≠ ∅ -> τ' = τi.

  Definition obls_sim_rel_wfree extr omtr :=
    obls_sim_rel extr omtr /\ no_extra_obls (trace_last extr) (trace_last omtr).

  Definition wfree_trace_inv `{Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (extr: execution_trace heap_lang) (omtr: auxiliary_trace M): iProp Σ :=
    ⌜ no_extra_obls (trace_last extr) (trace_last omtr) /\
      from_option (fun e => to_val e = None) True (from_locale (trace_last extr).1 τi) ⌝ ∗
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv _ WFST). 
  
  Context (ai: val).

  Class PrWfreeTok Σ := {
      pwt_Hinv :: @IEMGS _ _ HeapLangEM EM Σ;
      pwt_CT :: CallTracker Σ;
      pwt_UT :: UnitToken Σ;
  }.

  Definition ct_interp_tok `{PWT: PrWfreeTok Σ} (etr: execution_trace heap_lang): iProp Σ
    := ct_interp m τi unit_tok etr.

  Definition cti_cond `{PWT: PrWfreeTok Σ} (etr: execution_trace heap_lang): iProp Σ
    :=
    ⌜ trace_length etr <= ii ⌝ -∗ ct_interp_tok etr.

  Definition pwp0 `{PWT: PrWfreeTok Σ} :=
    let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) si_add_none in pwp. 

  Definition pwp_ext `{PWT: PrWfreeTok Σ} :=
    let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) ct_interp_tok in pwp.

  Definition wp_tc {Σ} {PWT: PrWfreeTok Σ}                   
    (s: stuckness) (e: expr) (b: bool) Φ :=
    if b then pwp_ext s ⊤ τi e Φ
    else
      let e' := default (Val #false) (under_ctx Ki e) in
      (* from now on, we forget about the original postcondition *)
      wp s ⊤ τi e' (fun _ => ⌜ True ⌝%I).

  Definition thread_pr {Σ} {PWT: PrWfreeTok Σ} s N :=
    (fun e τ Φ => if decide (τi = τ) then wp_tc s e (N <=? ii) Φ
                 else pwp0 s ⊤ τ e Φ).

  Definition wptp_wfree {Σ} {PWT: PrWfreeTok Σ}
    (s: stuckness) (etr: execution_trace heap_lang) (Φs : list (val → iPropI Σ)):
    iProp Σ :=
    wptp_gen (thread_pr s (trace_length etr)) (trace_last etr).1 Φs.

  Lemma wptp_wfre_not_stuck {Σ} {PWT: PrWfreeTok Σ}
    ex atr σ tp trest s Φs :
    valid_exec ex →
    trace_ends_in ex (tp ++ trest, σ) →
    fits_inf_call ic m ai ex ->
    state_interp ex atr -∗ wptp_wfree s ex Φs -∗ cti_cond ex ={⊤}=∗
    state_interp ex atr ∗ wptp_wfree s ex Φs ∗ cti_cond ex ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (Hexvalid Hex FIT) "HSI Ht CTI".
    do 2 rewrite assoc.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "((HSI & Ht) & CTI)".
    iIntros (e He).
    rewrite /wptp_wfree.
    rewrite Hex. iEval (simpl) in "Ht".

    iDestruct (wptp_gen_split_1 with "[$]") as %(?&?&<-&?&?).
    iDestruct (wptp_from_gen_app' with "[$]") as "[WPS _]"; eauto.
    erewrite wptp_from_gen_take_1; eauto.
    iDestruct "WPS" as "(%Φ & %t1 & %t2 & %IN & -> & W & _)".
    iSimpl in "W". 
    rewrite /thread_pr.
    apply elem_of_list_split in He as (?&?&->).
    rewrite -app_assoc -app_comm_cons in Hex. 
    destruct decide; [rewrite /wp_tc; destruct Nat.leb eqn:LEN| ].
    - iMod (wp_not_stuck _ _ ectx_emp with "[HSI CTI] W") as "(_ & _ & ?)";
      [done| rewrite ectx_fill_emp // | .. ].
      { done. }
      { simpl. rewrite /phys_SI. simpl.
        rewrite /cti_cond. iSpecialize ("CTI" with "[]").
        { iPureIntro. by apply leb_complete. }
        iDestruct "HSI" as "(?&?&?)". by iFrame. }
      simpl. by rewrite Hex.
    - apply fits_inf_call_last_or_short in FIT as [NVAL | SHORT].
      2: { apply Nat.leb_gt in LEN. 
           exfalso. clear -LEN SHORT.
           (* TODO: why lia doesn't work? *)
           by apply Nat.lt_nge in LEN. }
      rewrite Hex in NVAL.

      (* red in NVAL. rewrite /expr_at in NVAL.  *)
      eapply runs_call_helper in NVAL; eauto.
      destruct NVAL as (ec & CUR & NVAL).

      rewrite CUR.
      pose proof CUR as <-%under_ctx_spec. 
      iSimpl in "W". 
      iMod (wp_not_stuck _ _ Ki with "[$] W") as "(_ & _ & %NS)";
      [done|  | .. ].
      { simpl. erewrite (proj1 (under_ctx_spec _ _ _)); eauto. }
      { done. }      
      iPureIntro. simpl in *. intros.
      specialize (NS ltac:(done)).
      rewrite Hex in NS. simpl in NS.
      eapply not_stuck_fill; eauto.
    - 
      iMod (wp_not_stuck _ _ ectx_emp with "[HSI CTI] W") as "(_ & _ & %NS)";
      [done| rewrite ectx_fill_emp // | .. ].
      { done. }
      { simpl. rewrite /phys_SI. simpl.
        iDestruct "HSI" as "(?&?&?)". iFrame. }
      simpl. by rewrite Hex in NS.
    (* TODO: get rid of this? *)
    Unshelve. all: by apply trace_singleton. 
  Qed. 

  Definition extra_fuel `{!ObligationsGS Σ} (etr: execution_trace heap_lang) :=
    let len := trace_length etr in
    if len <=? ii then (cp_mul π0 d0 (S ii - len) ∗ cp_mul π0 d0 F)%I else ⌜ True ⌝%I.

  Definition cur_phases `{!ObligationsGS Σ} (etr: execution_trace heap_lang): iProp Σ :=
    let c := trace_last etr in
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, ∃ π, th_phase_eq τ π) ∗
    let ph_res := let q := if (trace_length etr <=? ii) then 1%Qp else (/2)%Qp in
                  (∃ π, th_phase_frag τi π q)%I in
    ⌜ τi ∈ locales_of_cfg c ⌝ → ph_res.

  Definition obls_τi `{!ObligationsGS Σ}: iProp Σ :=
    ∃ s, obls τi {[ s ]} ∗ sgn s l0 (Some false) ∗ ep s π0 d0. 

  Definition obls_τi' `{!ObligationsGS Σ} (c: cfg heap_lang): iProp Σ :=
    if decide (τi ∈ locales_of_cfg c) then obls_τi else cp π0 d1.

  Definition cur_obls_sigs `{!ObligationsGS Σ} (etr: execution_trace heap_lang): iProp Σ :=
    let c := trace_last etr in
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, obls τ ∅) ∗
    obls_τi' c. 

  Definition pr_pr_wfree {Σ} {PWT: PrWfreeTok Σ}
    (s: stuckness) (etr: execution_trace heap_lang) (Φs: list (val → iProp Σ)): iProp Σ :=
    let oGS: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ (@pwt_Hinv _ PWT) in
    wptp_wfree s etr Φs ∗ extra_fuel etr ∗ cur_phases etr ∗
    cur_obls_sigs etr ∗ cti_cond etr. 

  (* TODO: remove? *)
  Lemma cur_phases_take `{!ObligationsGS Σ} etr τ
    (IN: τ ∈ locales_of_cfg (trace_last etr)):
    let ph π := th_phase_frag τ π (/2)%Qp in
    cur_phases etr ⊣⊢ ∃ π, ph π ∗ (ph π -∗ cur_phases etr).
  Proof using.
    simpl. rewrite /cur_phases.
    destruct (decide (τ = τi)) as [-> | NEQ]. 
    - iSplit.
      2: { iIntros "(%π & PH & CLOS)".
           by iApply "CLOS". }
      iIntros "[PHS' PH]". iDestruct ("PH" with "[//]") as (π) "PH".
      erewrite th_phase_frag_combine' with (p := (/ 2)%Qp).
      2: { by destruct Nat.leb. }
      iDestruct "PH" as "[PH PH']".
      iExists π. iFrame.
      iIntros "PH _".
      iExists _. iApply th_phase_frag_combine'; [| by iFrame].
      by destruct Nat.leb.
    - iSplit.
      2: { iIntros "(%π & PH & CLOS)".
           by iApply "CLOS". }
      iIntros "[PHS' PH]". iFrame "PH".
      iDestruct (big_sepS_elem_of_acc with "[$]") as "[PH PHS]".
      { apply elem_of_difference. split; eauto. set_solver. }
      iDestruct "PH" as "(%π & PH)".
      rewrite {1}/th_phase_eq. rewrite -Qp.inv_half_half. 
      iDestruct (th_phase_frag_combine with "PH") as "[PH1 PH2]".
      iExists _. iFrame.
      iIntros "PH". iApply "PHS".
      iExists _. iEval (rewrite /th_phase_eq).
      rewrite -Qp.inv_half_half. iApply th_phase_frag_combine. iFrame.
  Qed.

  (* TODO: refactor *)
  Lemma same_phase_no_fork {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr mtr
    (e : expr)
    (σ σ' : state)
    (efs t1 t2 : list expr)
    (FIN : trace_last etr = (t1 ++ e :: t2, σ))
    (ec : expr)
    (π : Phase)
    (PH : ps_phases (trace_last mtr) !! τi = Some π)
    (CORR : obls_cfg_corr (trace_last etr) (trace_last mtr))
    (x : expr)
    (H2 : prim_step ec σ x σ' efs)
    (δ' : AM2M ObligationsAM)
    (ℓ : mlabel (AM2M ObligationsAM)):
   ⊢ @th_phase_frag _ _ _ WF_SB OP Σ
           (@iem_fairnessGS heap_lang _ HeapLangEM EM Σ Hinv)
           τi π (/ 2) -∗
  ⌜@obls_ves_wrapper _ _ _ WF_SB
             OP Nat.inhabited (@trace_last (cfg heap_lang) (option nat) etr)
             (@Some nat τi)
             (t1 ++ @fill _ Ki x :: t2 ++ efs, σ')
             (trace_last mtr)
             ℓ δ'⌝ ∗
          @gen_heap_interp loc loc_eq_decision loc_countable (option val) Σ
            (@heap_gen_heapGS Σ (@iem_phys heap_lang _ HeapLangEM EM Σ Hinv))
            (heap σ') ∗
          @obls_asem_mti _ _ _ WF_SB OP
            Nat.inhabited Σ
            (@iem_fairnessGS heap_lang _ HeapLangEM EM Σ Hinv)
            (etr :tr[ @Some nat τi]: (t1 ++ @fill _ Ki x :: t2 ++ efs, σ'))
            (mtr :tr[ ℓ ]: δ') -∗
  ⌜efs = [] /\ locales_of_cfg (trace_last etr) = locales_of_cfg (t1 ++ @fill _ Ki x :: t2 ++ efs, σ')⌝.
  Proof using.
    clear m WFST F.
    iIntros "PH HSI".
    iAssert (⌜ ps_phases δ'  !! τi = Some π ⌝)%I as "%PH'".
    { iApply (th_phase_msi_frag with "[-PH] [$]").
      by iDestruct "HSI" as "(?&?&(?&?&?))". }
    iDestruct "HSI" as "(%EVOL&_&CORR')".
    rewrite /obls_asem_mti. simpl. 
    red in EVOL. destruct ℓ as [? [|]].
    2: { tauto. } 
    destruct EVOL as [MSTEP ->]. simpl in MSTEP.
    red in MSTEP. destruct MSTEP as (_ & MSTEP & [=<-] & CORR').
    simpl in MSTEP.
    
    (* TODO: make a lemma *)
    assert (ps_phases (trace_last mtr) = ps_phases δ') as PH_EQ.
    { destruct MSTEP as (δ2 & PSTEP & OFORK).
      destruct PSTEP as (? & ? & δ1 & STEPS & BURN).
      assert (ps_phases (trace_last mtr) = ps_phases δ2) as EQ2. 
      { rewrite (lse_rep_phases_eq_helper _ _ _ STEPS).
        destruct BURN as (?&?&BURN).
        eapply lse_rep_phases_eq_helper.
        apply nsteps_once. red. left.
        eexists. red. eauto. }
      inversion OFORK.
      2: { by subst. }
      subst y. red in H0. destruct H0 as (?&?&FORK).
      inversion FORK. subst.
      subst ps'. rewrite phases_update_phases in PH'.
      subst new_phases0.
      rewrite lookup_insert_ne in PH'.
      2: { intros ->. destruct FRESH'. by eapply elem_of_dom. }
      rewrite lookup_insert in PH'. inversion PH'.
      rewrite -EQ2 PH in LOC_PHASE. inversion LOC_PHASE. subst π0.
      pose proof (phase_lt_fork π 0) as NEQ. red in NEQ.
      apply strict_ne in NEQ. done. }
    
    red in CORR'. destruct CORR' as (CORR' & DPO').

    rewrite (proj1 CORR) (CORR'). 

    red in DPO'. apply (@f_equal _ _ dom) in PH_EQ. 
    rewrite DPO' in PH_EQ.
    red in CORR'. rewrite -PH_EQ in CORR'.
    red in CORR. rewrite (proj2 CORR) -(proj1 CORR) in CORR'.
    rewrite FIN in CORR'. simpl in CORR.
    rewrite !locales_of_cfg_simpl in CORR'.
    repeat (rewrite !length_app /= in CORR').

     iPureIntro. split.
     2: { set_solver. }
    
    destruct efs; [done| ].
    simpl in CORR'. apply set_seq_uniq2 in CORR'. lia.
  Qed.

  Lemma reestablish_wfree_inv {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr mtr
    (FIT: fits_inf_call ic m ai etr)
    :
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv _ WFST) -∗
    cur_obls_sigs etr -∗ state_interp etr mtr -∗
    wfree_trace_inv etr mtr.
  Proof using.
    simpl. iIntros "#INV OB TI".
    clear -FIT. 
    rewrite /wfree_trace_inv. iFrame "INV". simpl.
    rewrite /no_extra_obls. simpl.
    iDestruct "TI" as "(_&_&MSI)". rewrite /obls_asem_mti. simpl.
    rewrite /obls_si. iDestruct "MSI" as "(MSI & %CORR')".
    iSplit. 
    - iIntros (τ' OBS).
      rewrite /cur_obls_sigs.
      destruct (decide (τ' = τi)); [done| ].
      simpl. 
      iDestruct "OB" as "(OB & _)".
      iDestruct (big_sepS_elem_of with "[$]") as "OB".
      { apply elem_of_difference. rewrite not_elem_of_singleton. split; [| done].
        rewrite (proj1 CORR').
        destruct (ps_obls (trace_last mtr) !! τ') eqn:TT; rewrite TT in OBS; [| done]. 
        eapply elem_of_dom; eauto. }
      iDestruct (obls_msi_exact with "[$] [$]") as %NOOBS.
      by rewrite NOOBS in OBS.
    - iPureIntro.
      destruct FIT. 
      ospecialize (fic_never_val (trace_length etr - 1)).
      erewrite (trace_lookup_last etr) in fic_never_val. 
      2: { simpl. rewrite -Nat.sub_succ_l; [lia| ].
           destruct etr; simpl; lia. }
      done. 
  Qed.

  Lemma split_trace_fuel {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr c' τ
    (BEFORE: trace_length etr <= ii):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    let fuel_pre := cp_mul π0 d0 F in
    ⊢ extra_fuel etr -∗ cp π0 d0 ∗ fuel_pre ∗
      ((⌜ trace_length etr < ii ⌝ → fuel_pre) -∗ extra_fuel (etr :tr[ Some τ]: c')).
  Proof using.
    simpl. iIntros "CPS". 
    rewrite /extra_fuel.
    rewrite leb_correct; [| done]. 
    rewrite Nat.sub_succ_l; [| done]. rewrite cp_mul_take.
    iDestruct "CPS" as "((CPS & CP) & CPP)". iFrame.
    iIntros "CPP".
    destruct leb eqn:LEN; [| done]. iFrame.
    iApply "CPP". iPureIntro. 
    apply leb_complete in LEN. simpl in LEN. lia.
  Qed.

  Lemma reestablish_fuel {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr c' τ:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ extra_fuel etr -∗ extra_fuel (etr :tr[ Some τ]: c').
  Proof using.
    simpl. iIntros "CPS". 
    rewrite /extra_fuel.
    destruct (trace_length (_ :tr[ _ ]: _) <=? _) eqn:LE; [| done].
    rewrite leb_correct.
    2: { apply leb_complete in LE. simpl in *. lia. }
    simpl. iDestruct "CPS" as "(? & $)".
    iApply (cp_mul_weaken with "[$]"); [done| lia].
  Qed.

  Lemma reestablish_phases {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr τ c'
    (EQ_CFG: locales_of_cfg (trace_last etr) = locales_of_cfg c')
    (AFTER: ii < trace_length etr)
    :
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    cur_phases etr -∗ cur_phases (etr :tr[ Some τ ]: c').
  Proof using.
    clear m WFST F.
    simpl. iIntros "PHS".
    rewrite /cur_phases.
    rewrite -EQ_CFG.    
    rewrite leb_correct_conv; [| done].
    rewrite leb_correct_conv; [done| ].
    simpl.
    remember (trace_length etr) as X. rewrite -HeqX. lia.
  Qed.

  Lemma reestablish_obls_sigs {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr t1 t2 x σ'
    (EQ_CFG: locales_of_cfg (trace_last etr) = locales_of_cfg (t1 ++ fill Ki x :: t2, σ')):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    cur_obls_sigs etr -∗ cur_obls_sigs (etr :tr[ Some τi ]: (t1 ++ fill Ki x :: t2, σ')).
  Proof using.
    simpl. iIntros "(OBS & OBτi)". 
    rewrite /cur_obls_sigs. simpl.
    rewrite /obls_τi'. 
    rewrite -EQ_CFG. iFrame. 
  Qed.

  From lawyer Require Import program_logic.  

  Lemma MU_burn_cp_nofork {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} τ π d q P:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ BOU ∅ WF_SB (cp π d ∗ th_phase_frag τ π q ∗ P) -∗ 
      let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
      @MU _ EM Σ hGS ⊤ τ (th_phase_frag τ π q ∗ P).
  Proof using.
    simpl. iIntros "BOU".
    iApply AMU_lift_top; [(try rewrite nclose_nroot); done| ].
    iApply BOU_AMU. iApply (BOU_weaken with "[] [$]"); try done.
    iIntros "(CP & PH & P)".
    iSplitL "P".
    { by iIntros "$". }
    iFrame.
  Qed.

  Lemma MU_burn_cp_fork {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} τ π0 d τ' Q:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ BOU ∅ WF_SB (∃ R1 R2, cp π0 d ∗ th_phase_eq τ π0 ∗ obls τ (R1 ∪ R2) ∗ Q R1 R2 ∗ ⌜ R1 ## R2 ⌝) -∗
      let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
      @MU__f _ EM Σ hGS ⊤ τ τ'
        (∃ π π' R1 R2, th_phase_eq τ π ∗ th_phase_eq τ' π' ∗ obls τ R1 ∗ obls τ' R2 ∗ Q R1 R2 ∗ ⌜ R1 ## R2 ⌝).
  Proof using.
    simpl. iIntros "BOU".
    iApply AMU_lift_top; [(try rewrite nclose_nroot); done| ].
    iApply (BOU_AMU__f'_strong _ _ _ _ Q). iApply (BOU_weaken with "[] [$]"); try done. 
    iIntros "(%R1 & %R2 & CP & PH & OB & Q &?)".
    iFrame. 
    iIntros "(%&%&%&%&?&?&?&?&?&?)".
    iFrame. 
  Qed.

  Lemma MU_burn_cp {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} τ π0 d oτ' Q:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ BOU ∅ WF_SB (∃ R1 R2, cp π0 d ∗ th_phase_eq τ π0 ∗ obls τ (R1 ∪ R2) ∗ Q R1 R2 ∗ ⌜ R1 ## R2 ⌝) -∗
      let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
      @MU_impl _ EM Σ hGS oτ' ⊤ τ
        (∃ π R1 R2, th_phase_eq τ π ∗ Q R1 R2 ∗ ⌜ R1 ## R2 ⌝ ∗
         from_option (fun τ' => ∃ π', th_phase_eq τ' π' ∗ obls τ R1 ∗ obls τ' R2) (obls τ (R1 ∪ R2)) oτ').
  Proof using.
    simpl. iIntros "BOU".
    destruct oτ'.
    - iPoseProof (MU_burn_cp_fork with "[$]") as "foo".
      iApply (MU__f_wand with "[] [$]"). simpl.
      iIntros "(%&%&%&%&?&?&?&?&?)". by iFrame.
    - simpl.
      iApply (MU_wand with "[-BOU]").
      2: { iApply MU_burn_cp_nofork. iMod "BOU".
           repeat setoid_rewrite <- bi.sep_exist_l. 
           iModIntro. iFrame. }
      iIntros "[$ X]". by iDestruct "X" as "(%&%&$&?)". 
  Qed.

  Lemma cur_obls_sigs_τi_step `{!ObligationsGS Σ} etr c'
    (STEP: locale_step (trace_last etr) (Some τi) c'):
    cur_obls_sigs etr -∗ obls_τi ∗
      let oτ' := step_fork (trace_last etr) c' in
      (obls_τi -∗ from_option (fun τ' => obls τ' ∅) ⌜ True ⌝ oτ' -∗ cur_obls_sigs (etr :tr[ Some τi ]: c')).
  Proof using.
    simpl. iIntros "(OBLS & OB)".
    rewrite /cur_obls_sigs /obls_τi'. simpl.
    rewrite decide_True.
    2: { eapply locales_of_cfg_step; eauto. }
    iFrame. iIntros "OB OB'". 
    rewrite decide_True.
    2: { eapply locale_step_sub; eauto. eapply locales_of_cfg_step; eauto. }
    iFrame.
    pose proof STEP as ->%locale_step_step_fork_exact. 
    rewrite difference_union_distr_l_L big_sepS_union.
    2: { destruct step_fork eqn:SF; [| set_solver].
         simpl. apply elem_of_disjoint.
         intros ? [??]%elem_of_difference [->%elem_of_singleton ?]%elem_of_difference.
         apply step_fork_difference in SF. set_solver. }
    iFrame. destruct step_fork eqn:SF; simpl. 
    2: { rewrite subseteq_empty_difference_L; set_solver. }
    rewrite difference_disjoint_L.
    2: { apply step_fork_difference in SF.
         apply locales_of_cfg_step in STEP.
         set_solver. }
    by rewrite big_sepS_singleton.
  Qed.

  Lemma cur_phases_τi_step `{!ObligationsGS Σ} etr c'
    (STEP: locale_step (trace_last etr) (Some τi) c'):
    cur_phases etr -∗
    let oτ' := step_fork (trace_last etr) c' in
    let ph ex := ∃ π, th_phase_frag τi π (if (trace_length ex <=? ii) then 1%Qp else (/2)%Qp) in
    let etr' := etr :tr[ Some τi ]: c' in
    ph etr ∗ (ph etr' -∗ from_option (fun τ' => ∃ π', th_phase_eq τ' π') ⌜ True ⌝ oτ' -∗ cur_phases etr').
  Proof using.
    #[local] Arguments Nat.leb _ _ : simpl nomatch.
    rewrite /cur_phases. simpl. iIntros "(PHS & PH)".
    iSpecialize ("PH" with "[]").
    { iPureIntro. eapply locales_of_cfg_step; eauto. }
    iFrame.
    iIntros "PH PH'".
    pose proof STEP as ->%locale_step_step_fork_exact. 
    rewrite difference_union_distr_l_L big_sepS_union.
    2: { destruct step_fork eqn:SF; [| set_solver].
         simpl. apply elem_of_disjoint.
         intros ? [??]%elem_of_difference [->%elem_of_singleton ?]%elem_of_difference.
         apply step_fork_difference in SF. set_solver. }
    iFrame "PHS".

    iSplitL "PH'".
    { destruct step_fork eqn:SF.
      2: { simpl. rewrite subseteq_empty_difference_L; set_solver. }
      simpl. rewrite difference_disjoint_L.
      { by rewrite big_sepS_singleton. }
      apply elem_of_disjoint. intros ? ?%elem_of_singleton ?%elem_of_singleton. 
      subst.
      apply step_fork_difference in SF.
      apply locales_of_cfg_step in STEP. set_solver. }
    iFrame. done. 
  Qed.

  Lemma cur_obls_sigs_other_step `{!ObligationsGS Σ}
    etr c' τ
    (STEP: locale_step (trace_last etr) (Some τ) c')
    (OTHER: τ ≠ τi)
    :
    cur_obls_sigs etr -∗
      obls τ ∅ ∗ obls_τi' (trace_last etr) ∗
      let oτ' := step_fork (trace_last etr) c' in
      (obls τ ∅ -∗ obls_τi' c' -∗ (∀ τ', ⌜ oτ' = Some τ' /\ τ' ≠ τi ⌝ → obls τ' ∅) -∗
       cur_obls_sigs (etr :tr[ Some τi ]: c')).
  Proof using.
    simpl. iIntros "(OBLS & OBτi)". iFrame "OBτi". 
    rewrite /cur_obls_sigs. simpl.
    iDestruct (big_sepS_elem_of_acc with "[$]") as "(OB & OBLS)".
    { apply elem_of_difference. split; [| apply not_elem_of_singleton]; eauto.
      eapply locales_of_cfg_step; eauto. }
    iFrame "OB". iIntros "OB OBτi OB'".
    iSpecialize ("OBLS" with "[$]").     
    pose proof STEP as ->%locale_step_step_fork_exact.    
    rewrite difference_union_distr_l_L big_sepS_union.
    2: { destruct step_fork eqn:SF; [| set_solver].
         simpl. apply elem_of_disjoint.
         intros ? [??]%elem_of_difference [->%elem_of_singleton ?]%elem_of_difference.
         apply step_fork_difference in SF. set_solver. }
    iFrame.
    destruct step_fork eqn:SF; simpl. 
    2: { rewrite subseteq_empty_difference_L; set_solver. }
    destruct (decide (l = τi)).
    { rewrite subseteq_empty_difference_L; set_solver. } 
    rewrite difference_disjoint_L; [| set_solver].
    rewrite big_sepS_singleton. by iApply "OB'". 
  Qed.

  (* TODO: refactor *)
  Lemma cur_phases_other_step `{!ObligationsGS Σ} etr c' τ
    (STEP: locale_step (trace_last etr) (Some τ) c')
    (* (etr' := etr :tr[ Some τi ]: c') *)
    (etr' := etr :tr[ Some τ ]: c')
    (FITS: fits_inf_call ic m ai etr')
    (OTHER: τ ≠ τi):
    cur_phases etr -∗
    let oτ' := step_fork (trace_last etr) c' in
    let ph := ∃ π, th_phase_eq τ π in
    ph ∗ (ph -∗ from_option (fun τ' => ∃ π', th_phase_eq τ' π') ⌜ True ⌝ oτ' -∗
          cur_phases etr' ∗
          (⌜ trace_length etr = ii ⌝ → ∃ π, th_phase_frag τi π (/2)%Qp)).
  Proof using.
    clear WFST F.
    rewrite /cur_phases. simpl. iIntros "(PHS & PHτi)".
    iDestruct (big_sepS_elem_of_acc with "[$]") as "(PH & PHS)".
    { apply elem_of_difference. split; [| apply not_elem_of_singleton]; eauto.
      eapply locales_of_cfg_step; eauto. }
    iFrame "PH". iIntros "PH PH'".
    iSpecialize ("PHS" with "[$]"). 
    pose proof STEP as ->%locale_step_step_fork_exact. 
    rewrite difference_union_distr_l_L big_sepS_union.
    2: { destruct step_fork eqn:SF; [| set_solver].
         simpl. apply elem_of_disjoint.
         intros ? [??]%elem_of_difference [->%elem_of_singleton ?]%elem_of_difference.
         apply step_fork_difference in SF. set_solver. }
    iFrame "PHS". rewrite -bi.sep_assoc. 
    
    destruct step_fork eqn:SF.
    2: { simpl. iSplitR.
         { rewrite subseteq_empty_difference_L; [| done]. set_solver. }
         rewrite union_empty_r_L. 
         destruct (decide (trace_length etr = ii)).
         - destruct FITS. 
           rewrite trace_lookup_last in fic_call .
           2: { simpl in *. lia. }
           simpl in fic_call. 
           iSpecialize ("PHτi" with "[]").
           { iPureIntro. red in fic_call. 
             pose proof STEP as EQ%locale_step_step_fork_exact.
             rewrite SF /= union_empty_r_L in EQ. rewrite -EQ.
             eapply expr_at_in_locales; eauto. }
           iDestruct "PHτi" as (?) "PH".
           rewrite leb_correct; [| simpl in *; lia].
           iDestruct (th_phase_frag_halve with "PH") as "[PH PH_]".
           rewrite leb_correct_conv; [| simpl in *; lia].
           rewrite half_inv2. iSplitL "PH".
           + iIntros "_". iFrame.
           + iIntros "_". iFrame.
         - iSplitL.
           2: { by iIntros (?). }
           simpl. 
           assert (S (trace_length etr) <=? ii = (trace_length etr <=? ii)) as X. 
           2: { rewrite X. iFrame. }
           simpl in *.
           destruct (decide (trace_length etr <= ii)) as [LE | GT]. 
           + by do 2 (rewrite leb_correct; [| lia]).
           + by do 2 (rewrite leb_correct_conv; [| lia]). }

    simpl. 
    destruct (decide (l = τi)) as [-> | ?]. 
    { rewrite subseteq_empty_difference_L; [| set_solver]. iSplitR; [set_solver| ].
      iDestruct "PH'" as (?) "PH".
      destruct (decide (trace_length etr = ii)).
      - rewrite leb_correct; [| simpl in *; lia].
        iDestruct (th_phase_frag_halve with "PH") as "[PH PH_]".
        rewrite leb_correct_conv; [| simpl in *; lia].
        rewrite half_inv2. iSplitL "PH".
        + iIntros "_". iFrame.
        + iIntros "_". iFrame.
      - iSplitL.
        2: { by iIntros (?). }
        simpl.
        iClear "PHτi". iIntros "_".
        rewrite leb_correct; [iFrame| ].
        enough ((trace_length etr) ≤ ii).
        { simpl in *. lia. }
        destruct (Nat.le_gt_cases (trace_length etr) ii); [done| ].
        eapply fic_has_τi in H. 
        2: { eapply fits_inf_call_prev; eauto. }
        apply step_fork_difference in SF. set_solver. }

    simpl. rewrite difference_disjoint_L.
    2: { set_solver. }
    rewrite big_opS_singleton. iFrame "PH'".

    destruct (decide (trace_length etr = ii)).
    - destruct FITS. subst etr'.
      rewrite trace_lookup_last in fic_call.
      2: { simpl in *. lia. }
      simpl in fic_call.
      iSpecialize ("PHτi" with "[]").
      { iPureIntro. red in fic_call. 
        pose proof STEP as EQ%locale_step_step_fork_exact.
        rewrite SF /= in EQ.
        apply expr_at_in_locales in fic_call. rewrite EQ in fic_call.
        apply elem_of_union in fic_call as [|]; eauto.
        set_solver. }
      iDestruct "PHτi" as (?) "PH".
      rewrite leb_correct; [| simpl in *; lia].
      iDestruct (th_phase_frag_halve with "PH") as "[PH PH_]".
      rewrite leb_correct_conv; [| simpl in *; lia].
      rewrite half_inv2. iSplitL "PH".
      + iIntros "_". iFrame.
      + iIntros "_". iFrame.
    - iSplitL. 
      2: { by iIntros (?). }
      simpl. 
      assert (S (trace_length etr) <=? ii = (trace_length etr <=? ii)) as X. 
      2: { rewrite X.
           iIntros (?). iApply "PHτi".
           iPureIntro. set_solver. }
      simpl in *.
      destruct (decide (trace_length etr <= ii)) as [LE | GT]. 
      + by do 2 (rewrite leb_correct; [| lia]).
      + by do 2 (rewrite leb_correct_conv; [| lia]).
  Qed.

  Lemma obls_τi'_next `{!ObligationsGS Σ} c c'
    (SAME: locales_of_cfg c' = locales_of_cfg c):
    obls_τi' c ⊣⊢ obls_τi' c'.
  Proof using.
    rewrite /obls_τi'. by rewrite SAME.
  Qed.

  Lemma BOU_wait_τi `{!ObligationsGS Σ} `{invGS_gen HasNoLc Σ} τ π:
    obls τ ∅ -∗ th_phase_eq τ π -∗ obls_τi -∗
      BOU ∅ WF_SB (cp π d0 ∗ th_phase_eq τ π ∗ obls τ ∅ ∗ obls_τi). 
  Proof using.
    clear m WFST F. 
    iIntros "OB PH OBτi".
    rewrite /obls_τi. iDestruct "OBτi" as "(%s & OBτi & SGN & #EP)".    
    iMod (expect_sig_upd with "[] [$] OB [] [$]") as "(?&?&?&?)".
    { iApply (ep_weaken with "[$]"). apply (phase_le_init π). } 
    { (* TODO: Make a lemma *)
      rewrite /sgns_level_gt. rewrite /sgns_levels_gt'.
      iApply empty_sgns_levels_rel. }
    { rewrite /WF_SB. lia. }
    iModIntro. iFrame "#∗".
  Qed.

  Lemma wptp_wfree_other_simpl {Σ} {PWT: PrWfreeTok Σ}
    s (etr: execution_trace heap_lang) tp0 tp Φs
    (OTHER: τi ∉ locales_of_list_from tp0 tp):
    wptp_from_gen (thread_pr s (trace_length etr)) tp0 tp Φs ⊣⊢
    let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) si_add_none in 
    wptp_from tp0 s tp Φs.
  Proof using.
    rewrite /wptp_from_gen.
    iApply big_sepL2_proper; try done.
    intros ? [??] ? IN IN'. rewrite /thread_pr. simpl.
    rewrite decide_False; [done| ]. 
    intros ->. apply OTHER.
    rewrite /locale_of. rewrite locales_of_list_from_indexes.
    pose proof IN as ITH%prefixes_lookup_orig. 
    apply prefixes_from_ith_length in IN. simpl in IN.
    apply elem_of_lookup_imap. eauto.
  Qed.

  Lemma wptp_wfree_posts {Σ: gFunctors} {PWT: PrWfreeTok Σ}
    (s : stuckness) (etr: execution_trace heap_lang) mtr (Φs : list (val → iProp Σ))
    (FIT: fits_inf_call ic m ai etr):
    let Ps := adequacy_utils.posts_of (trace_last etr).1 Φs in
    (* pr_pr_wfree s etr Φs -∗ |~~| Ps ∗ (Ps -∗ pr_pr_wfree s etr Φs). *)
    pr_pr_wfree s etr Φs -∗ state_interp etr mtr ={⊤}=∗ Ps ∗ state_interp etr mtr ∗ (Ps -∗ pr_pr_wfree s etr Φs). 
  Proof using.
    simpl.
    set (Ps := adequacy_utils.posts_of (trace_last etr).1 Φs). simpl.
    iUnfold pr_pr_wfree.
    iIntros "(WPS & CPS & PH & OB & CTI) TI".

    iFrame "CPS PH OB".
    iDestruct "TI" as "(EV & PHYS & MOD)". iFrame "EV MOD".  

    (** We'll establish pre_step for postconditions of all threads except τi.
        It can be ignored, since fits_inf_call implies τi doesn't terminate.
        Ignoring τi allows to operate with simpler TI. *)
    iFrame "CTI". 
    
    iAssert (pre_step top top (Ps ∗ (Ps -∗ wptp_wfree s etr Φs)) 
               (irisG0 := IEMGS_into_Looping (@pwt_Hinv _ PWT) si_add_none))%I
      with "[WPS]" as "CLOS".
    2: { iMod (pre_step_elim with "[PHYS] CLOS") as "((?&?)&?&?)"; by iFrame.
         Unshelve. exact looping_trace. }

    rewrite /wptp_wfree.
    iDestruct (big_sepL2_length with "[$]") as "%LENS".
    rewrite adequacy_utils.prefixes_from_length in LENS.

    destruct (trace_last etr) as [tp σ] eqn:LAST. simpl.

    pose proof (thread_pool_split tp τi) as (tp1 & tp2 & tp' & -> & TP' & NO1 & NO2).

    iDestruct (wptp_gen_split_1 with "WPS") as %X.
    destruct X as (Φs1 & Φs' & <- & LEN1 & LEN').
    iDestruct (wptp_from_gen_app' with "[$]") as "[WPS1 WPS'] /="; [done| ].

    rewrite wptp_wfree_other_simpl; [| done]. simpl.
    iPoseProof (wptp_of_val_post with "WPS1") as "foo".

    iDestruct (wptp_gen_split_1 with "WPS'") as %X.
    destruct X as (Φs_ & Φs2 & <- & LEN2 & LEN'').
    iDestruct (wptp_from_gen_app' with "WPS'") as "[WPS' WPS2]"; [done| ].
    
    erewrite wptp_wfree_other_simpl with (tp0 := tp1 ++ tp'); [| done].
    iPoseProof (wptp_of_val_post with "WPS2") as "bar".

    iAssert (pre_step top top (adequacy_utils.posts_of tp' Φs_ ∗ (adequacy_utils.posts_of tp' Φs_ -∗ wptp_from_gen (thread_pr s (trace_length etr)) tp1 tp' Φs_)) (irisG0 := IEMGS_into_Looping (@pwt_Hinv _ PWT) si_add_none))%I with "[WPS']" as "WPS'".
    { destruct TP' as [-> | (e & -> & EQ)].
      { iModIntro. rewrite /adequacy_utils.posts_of. simpl. set_solver. }
      destruct Φs_ as [ | ? [|] ].
      1, 3: simpl in LEN2; lia.
      rewrite wptp_gen_singleton.
      rewrite /adequacy_utils.posts_of. simpl.

      destruct FIT as [_ _ NVAL _]. specialize (NVAL (trace_length etr - 1)).
      rewrite trace_lookup_last /= in NVAL.
      2: { rewrite -Nat.sub_succ_l.
           2: { apply trace_length_at_least. }
           simpl. (* lia. *)
           by rewrite Nat.sub_0_r. }
      fold tc τi in NVAL. 
      rewrite LAST EQ /= in NVAL.
      rewrite /from_locale (from_locale_from_locale_of []) /= in NVAL.
      rewrite NVAL /=. 
      iFrame. iModIntro. set_solver. }

    iMod "foo" as "[P1 WPS1]". 
    iMod "bar" as "[P2 WPS2]". 
    iMod "WPS'" as "[P' WPS']".

    iModIntro. subst Ps. iSimpl.
    rewrite -!posts_of_app; try done. iFrame "P1 P2 P'".
    iIntros "(P1 & P' & P2)".
    iSpecialize ("WPS1" with "P1"). iSpecialize ("WPS2" with "P2"). iSpecialize ("WPS'" with "P'").
    iApply wptp_from_gen_app. iSplitL "WPS1".
    { by rewrite wptp_wfree_other_simpl. }
    simpl. iApply wptp_from_gen_app. iFrame.
    by rewrite wptp_wfree_other_simpl.
  Qed.

  Lemma wptp_wfree_not_stuck {Σ : gFunctors} {PWT: PrWfreeTok Σ}
    (s : stuckness) (ex : execution_trace heap_lang) 
    (Φs : list (val → iProp Σ)) 
    (σ : state) (atr : auxiliary_trace M) 
    (tp trest : list expr)
    (VALID: valid_exec ex)
    (LAST: trace_ends_in ex (tp ++ trest, σ))
    (FIT: fits_inf_call ic m ai ex):
    state_interp ex atr -∗ pr_pr_wfree s ex Φs ={⊤}=∗
    state_interp ex atr ∗ pr_pr_wfree s ex Φs ∗
    ⌜∀ e: expr, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝ .
  Proof using.
    iIntros "SI PR".
    rewrite /pr_pr_wfree. iDestruct "PR" as "(WPS &X&Y&Z&CTI)".
    iFrame "X Y Z".
    rewrite -bi.sep_assoc. 
    iApply (wptp_wfre_not_stuck with "[$] [$] [$]"); eauto.
  Qed.

  Lemma wptp_wfree_upd_other `{PWT: PrWfreeTok Σ} s N tp0 tp Φs
    (OTHER: τi ∉ locales_of_list_from tp0 tp):
    wptp_from_gen (thread_pr s N) tp0 tp Φs -∗
    wptp_from_gen (thread_pr s (S N)) tp0 tp Φs.
  Proof using.
    iIntros "WPS". iApply (big_sepL2_impl with "[$]").
    iModIntro. iIntros (i pfi Φi PFith Φith).
    rewrite /thread_pr.
    destruct decide; [| set_solver].
    destruct OTHER.
    rewrite locales_of_list_from_locales.
    apply elem_of_list_In, in_map_iff.
    eexists (_, _). split; eauto.
    rewrite -surjective_pairing.
    apply elem_of_list_In. eapply elem_of_list_lookup; eauto.
  Qed.

  Local Lemma ic_helper:
    tctx_tpctx ic = {| tpctx_ctx := Ki; tpctx_tid := τi |}.
  Proof using. by destruct ic as [? []]. Qed.

  Section TakeStep.
  Context {Σ} {PWT: PrWfreeTok Σ}.

  Let Hinv: IEMGS HeapLangEM EM Σ := @pwt_Hinv _ PWT.
  
  Context (s : stuckness).
  Context (etr : execution_trace heap_lang) (Φs : list (val → iProp Σ)) 
    (c : cfg heap_lang) (oτ : olocale heap_lang) (c' : cfg heap_lang).
  Context (mtr : auxiliary_trace M).
  Context 
    (VALID: valid_exec etr)
    (FIN: trace_ends_in etr c)
    (* (STEP: locale_step c oτ c') *)
    (* (FIT: fits_inf_call ic m ai (etr :tr[ oτ ]: c')) *)
  .

  Lemma locale_tp_split
    (e e' : expr) (σ' : state) (efs t1 t2 : list expr)
    (Heqc': (t1 ++ e' :: t2 ++ efs, σ') = c')
    (τ := locale_of t1 e):
    (locale_of t1 e ∉ locales_of_list t1) ∧
    (locale_of t1 e ∉ locales_of_list_from (t1 ++ [e']) t2) ∧
    locale_of t1 e ∉ locales_of_list_from (t1 ++ [e'] ++ t2) efs.
  Proof using.
    clear FIN VALID. 
    pose proof (thread_pool_split c'.1 τ) as SPLIT.
    rewrite -Heqc' /= in SPLIT. destruct SPLIT as (tp1 & tp2 & tp' & EQ & TP' & NO1 & NO2).
    destruct TP' as [-> | (e_ & -> & LOC)].
    { simpl in EQ.
      assert (τ ∈ locales_of_list c'.1) as IN. 
      { rewrite -Heqc' /=.
        rewrite locales_of_list_from_app /=. rewrite locales_of_list_from_cons.
        set_solver. }
      rewrite -Heqc' /= EQ in IN.
      rewrite locales_of_list_from_app /= in IN.
      rewrite app_nil_r in NO2.
      exfalso. 
      apply elem_of_app in IN as [?|?]; eauto. }
    rewrite -/τ /locale_of in LOC.
    apply app_inj_1 in EQ as [EQ1 EQ2]; eauto.
    simpl in EQ2. inversion EQ2. subst.
    split; eauto.
    apply Decidable.not_or. intros IN. destruct NO2.
    rewrite locales_of_list_from_app. apply elem_of_app.
    by rewrite -app_assoc.
  Qed.

  (* Lemma get_MU_impl *)
  (* (e : expr) *)
  (* (σ : state) *)
  (* (e' : expr) *)
  (* (σ' : state) *)
  (* (efs t1 t2 : list expr) *)
  (* (FIN : trace_last etr = (t1 ++ e :: t2, σ)) *)
  (* (H : (t1 ++ e :: t2, σ) = c) *)
  (* (τ : nat) *)
  (* (H1 : (t1 ++ e' :: t2 ++ efs, σ') = c') *)
  (* (STEP : locale_step (t1 ++ e :: t2, σ) (Some τ) (t1 ++ e' :: t2 ++ efs, σ')) *)
  (* (π : Phase) *)
  (* (sf : olocale heap_lang) *)
  (* (Heqsf : sf = step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ')) *)
  (* (upd := fun (R1 R2: gset SignalId) => let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in *)
  (*                       (⌜ R1 = ∅ ⌝ ∗  *)
  (*                       if (decide (sf = Some τi)) *)
  (*                       then (∃ s, ⌜ R2 = {[ s ]} ⌝ ∗ sgn s l0 (Some false) ∗ ep s π0 d0)%I *)
  (*                       else (⌜ R2 = ∅ ⌝ ∗ obls_τi' (t1 ++ e' :: t2 ++ efs, σ')))%I) *)
  (* (* "INV" : wfree_trace_inv etr mtr *) *)
  (* (* cp π0 d0 -∗ th_phase_eq τ π -∗ obls τ ∅ -∗ obls_τi' (trace_last etr) -∗  *) *)

  (* : *)
  
  (* ⊢ *)
  (*   (* MU_impl *) *)
  (*   let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in *)
  (*   @MU_impl _ EM Σ hGS sf ⊤ τ *)
  (*   (∃ R1 R2 : gset SignalId, cp π0 d0 ∗ th_phase_eq τ π0 ∗  *)
  (*      obls τ (R1 ∪ R2) ∗ upd R1 R2 ∗ ⌜R1 ## R2⌝).  *)
  (* Proof using. *)
  (*   iIntros "CP PH OB OBτi". *)

  Lemma τi_not_in e σ e' σ'
  (efs t1 t2 : list expr)
  (FIN' : trace_last etr = (t1 ++ e :: t2, σ))
  (τ := locale_of t1 e : nat)
  (STEP : locale_step (t1 ++ e :: t2, σ) (Some τ) (t1 ++ e' :: t2 ++ efs, σ'))
  (NO : step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ') ≠ Some τi)
  (FIT : from_locale (t1 ++ e' :: t2 ++ efs) τi = Some (fill Ki (m ai)))
  (sf := step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ')):
  τi ∉ locales_of_list_from (t1 ++ e' :: t2) efs.
  Proof using.
    clear WFST F. 
    rewrite locales_of_list_from_locales.
    intros [[??] IN]%elem_of_list_In%in_map_iff.
    destruct IN as (LOC & IN).
    apply elem_of_list_In, elem_of_list_lookup in IN as [i IN].
    pose proof IN as X.
    apply prefixes_from_ith_length in IN. 
    rewrite !length_app /= in IN. rewrite /locale_of in LOC.
    
    apply from_locale_lookup in FIT.
    apply lookup_lt_Some in FIT. simpl in FIT.
    rewrite /τi in LOC.
    rewrite /τi -LOC IN in FIT. 
    repeat rewrite !length_app /= in FIT.
    simpl in FIT.
    
    apply step_fork_hl in STEP as [[? ->] | (?&->&?)].
    { simpl. simpl in FIT. lia. }
    simpl in FIT. destruct i; [| lia].
    simpl in X. inversion X.
    subst. simpl in e0.
    rewrite app_comm_cons app_assoc in NO.
    rewrite FIN' in NO.
    rewrite step_fork_fork in NO.
    { rewrite /τi in NO. 
      rewrite -LOC in NO. 
      rewrite /locale_of !length_app in NO. done. }
    apply locales_equiv_middle. done.
  Qed.    

  Lemma unfold_helper (STEP: locale_step c oτ c'):
    wptp_wfree s etr Φs -∗
    ∃ e t1 t2 efs e' Φs1 Φ Φs2,
      let τ := locale_of t1 e in
      ⌜ oτ = Some τ /\ c.1 = t1 ++ e :: t2 /\ c'.1 = t1 ++ e' :: t2 ++ efs /\
        ectx_language.prim_step e c.2 e' c'.2 efs /\ 
        τ ∉ locales_of_list t1 /\ τ ∉ locales_of_list_from (t1 ++ [e']) t2 /\ τ ∉ locales_of_list_from (t1 ++ [e'] ++ t2) efs /\
        Φs = Φs1 ++ [Φ] ++ Φs2 /\
        length Φs1 = length t1 /\ length Φs2 = length t2 ⌝ ∗ 
  wptp_from_gen (thread_pr s (trace_length etr)) [] t1 Φs1 ∗ 
  thread_pr s (trace_length etr) e (locale_of t1 e) Φ ∗ 
  wptp_from_gen (thread_pr s (trace_length etr)) (t1 ++ [e]) t2 Φs2.
  Proof using FIN.
    clear mtr WFST VALID F. 
    iIntros "WPS".
    simpl.
    inversion STEP as
        [?? e σ e' σ' efs t1 t2 -> -> PSTEP | ].
    2: { done. }
    simpl in *. 
    destruct oτ as [τ| ]; [| done]. inversion H0. clear H0.
    rewrite H3 in STEP. rewrite H3.

    assert (τ ∉ locales_of_list_from [] t1 /\ τ ∉ locales_of_list_from (t1 ++ [e']) t2 /\ τ ∉ locales_of_list_from (t1 ++ [e'] ++ t2) efs) as (NO1 & NO2 & NO').
    { subst τ. eapply locale_tp_split; eauto. }

    iUnfold wptp_wfree in "WPS".

    red in FIN. iEval (rewrite FIN; simpl) in "WPS".
    iDestruct (wptp_gen_split_1 with "WPS") as %X.
    destruct X as (Φs1 & Φs' & EQ & LEN1 & LEN').
    iEval (rewrite -EQ) in "WPS".
    iDestruct (wptp_from_gen_app' with "[$]") as "[WPS1 WPS'] /="; [done| ].
    replace (e :: t2) with ([e] ++ t2) at 1 by done.
    iDestruct (wptp_gen_split_1 with "WPS'") as %X.
    destruct X as (Φ_ & Φs2 & EQ' & LEN_ & LEN2).
    iEval (rewrite -EQ') in "WPS'".
    iDestruct (wptp_from_gen_app' with "WPS'") as "[WP WPS2] /="; [done| ].
    destruct Φ_ as [ | Φ [|]].
    1, 3: simpl in LEN_; lia.
    rewrite wptp_gen_singleton.

    iFrame. iPureIntro. simpl. do 2 eexists. repeat split; eauto.
    all: try by rewrite H3.
    by subst.
  Qed.
    
  (* (* H3: *) *)
  (* H3 : locale_of t1 e = τ *)
  (* H : (t1 ++ e :: t2, σ) = c *)
  (* H1 : (t1 ++ e' :: t2 ++ efs, σ') = c' *)
  (* EQ :  Φs1 ++ Φs' = Φs /\ *)
  (* LEN1 : length Φs1 = length t1 *)
  (* LEN' : length Φs' = length (e :: t2) *)
  (* Φ : val → iPropI Σ *)
  (* Φs2 : list (val → iPropI Σ) *)
  (* EQ' : [Φ] ++ Φs2 = Φs' *)

  Lemma no_ongoing_call
    (e': expr) (K : ectx heap_lang) (s0 : nat) τ c''
    (FIT : fits_inf_call ic m ai (etr :tr[ τ ]: c''))
    (H : trace_length etr = ii)
    (CALL : inside_call m τi K s0 (etr :tr[ τ ]: c'') e'):
  False.
  Proof using.
    clear WFST F. 
    red in CALL. simpl in CALL.
    rewrite Nat.sub_0_r in CALL. 
    destruct CALL as (a & CALL & PREV & NORET & ?).
    destruct FIT as [_ _ _ PREVS_RET]. move PREVS_RET at bottom.
    destruct CALL as (?&?&?). 
    ospecialize * PREVS_RET.
    { simpl. rewrite H. lia. }
    { rewrite /ii in H. rewrite -H. apply PREV. }
    { rewrite H1 /=. eauto. }
    
    destruct PREVS_RET as (r&RET_PREV&RET).
    edestruct (_ !! r) eqn:RTH; [| done]. simpl in RET.
    ospecialize * (NORET r).
    { rewrite H. lia. }
    rewrite RTH /= in NORET.
    destruct RET. 
    edestruct not_return_nval; eauto. 
    red. eauto.
  Qed.

  Lemma extract_token τ c''
    (FIT : fits_inf_call ic m ai (etr :tr[ τ ]: c''))
    (H : trace_length etr = ii):
    ct_interp_tok (etr :tr[ τ ]: c'') -∗ unit_tok.
  Proof using.
    rewrite /ct_interp_tok /ct_interp.
    iIntros "(%&?&[($ & %) | (%&%&%&%CONTRA)])".
    exfalso. destruct CONTRA as [-> ?].
    eapply no_ongoing_call; eauto.
  Qed.    

  Lemma locales_equiv_app1 t (e1 e2: expr):
    locales_equiv (t ++ [e1]) (t ++ [e2]).
  Proof using.
    rewrite !prefixes_from_app.
    eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
    simpl. by constructor.
  Qed.

  Lemma wptp_wfree_take_step_τi
    (EQ_TID: oτ = Some τi)
    (STEP: locale_step c oτ c')
    (FIT: fits_inf_call ic m ai (etr :tr[ oτ ]: c')):
    state_interp etr mtr -∗ wfree_trace_inv etr mtr -∗
    pr_pr_wfree s etr Φs 
    ={⊤,∅}=∗ |={∅}▷=>^(S (trace_length etr)) |={∅,⊤}=>
    ∃ (δ' : M) (ℓ : mlabel M),
      state_interp (etr :tr[ oτ ]: c') (mtr :tr[ ℓ ]: δ') ∗
      pr_pr_wfree s (etr :tr[ oτ ]: c') (Φs ++ newposts c.1 c'.1).
  Proof using VALID FIN.
    iIntros "TI #INV PR".
    rewrite /pr_pr_wfree. 
    iDestruct "PR" as "(WPS & CPS & PH & OB & CTI)".

    iDestruct (unfold_helper with "[$]") as "(%&%&%&%&%&%&%&% & %PROPS & WPS1 & WP & WPS2)"; eauto.
    subst oτ. 
    destruct c as [tp σ], c' as [tp' σ'].
    simpl in PROPS. 
    destruct PROPS as ([=EQ_TID'] & -> & -> & PSTEP & NO1 & NO' & NO2 & EQ_Φs & LEN1 & LEN2).

    iEval (rewrite /thread_pr) in "WP".
    rewrite decide_True.
    2: congruence. 

    rewrite /wp_tc.

    iDestruct (cur_phases_τi_step with "[$]") as "(PH & PHS)".
    { by rewrite FIN. }
    iDestruct "PH" as "(%π & PH)". 

    iAssert (⌜ ps_phases (trace_last mtr) !! τi = Some π ⌝)%I as "%PH".
    { iApply (th_phase_msi_frag with "[-PH] [$]").
      by iDestruct "TI" as "(?&?&(?&?&?))". }
    iAssert (⌜ obls_cfg_corr (trace_last etr) (trace_last mtr) ⌝)%I as "%CORR".
    { iDestruct "TI" as "(_&_&CORR)".
      rewrite /obls_asem_mti /obls_si.
      iDestruct "CORR" as "(_&%CORR)". done. }

    destruct Nat.leb eqn:LEN.
    +
      rewrite /cti_cond. iSpecialize ("CTI" with "[]").
      { iPureIntro. by apply leb_complete. }
  
      apply Nat.leb_le in LEN.
      simpl. 

      iDestruct (split_trace_fuel with "[$]") as "(CP & CPP & CPS)"; [done| ].
      iDestruct (cur_obls_sigs_τi_step with "[$]" ) as "(OB & OBLS)".
      { by rewrite FIN. }

      rewrite {1}/obls_τi. iDestruct "OB" as "(%si & OB & SGN & EP)".

      assert (τi = length Φs1) as EQ_TID''. 
      { rewrite /locale_of in EQ_TID'. by rewrite LEN1 -EQ_TID'. } 

      iDestruct (@pwp_MU_ctx_take_step _ _ _ (@pwt_Hinv _ PWT) ct_interp_tok with "TI [CTI] [CP PH OB] [WP]") as "STEP".
      1-2: by eauto. 
      { red. rewrite FIN. erewrite ectx_fill_emp. reflexivity. }
      { done. }
      { by iFrame. }
      { rewrite -EQ_TID''. 
        rewrite (cp_weaken _ π); [| by apply phase_le_init].        
        iApply (MU_burn_cp _ _ _ _ (fun R1 R2 => (⌜ R1 = {[ si ]} /\ R2 = ∅ ⌝)%I) with "[$CP $PH OB]").
        iModIntro. do 2 iExists _. iSplit.
        2: { iPureIntro. split; [split| ]; try reflexivity. done. }
        by rewrite union_empty_r_L. }
      { by rewrite -EQ_TID''. }
          
      rewrite -EQ_TID''. 
      
      iMod "STEP". iModIntro.
      iMod "STEP". iModIntro. iNext. 
      iMod "STEP". iModIntro.
      iApply (step_fupdN_wand with "[STEP]"); first by iApply "STEP".
      iIntros "STEP".
      iMod "STEP" as (δ' ℓ) "(HSI & CTI & He2 & WPS' & MOD) /=".

      iDestruct "MOD" as (π' ??) "(PH & [->->] & _ & MOD')".
      rewrite union_empty_r_L. 

      iAssert (@state_interp _ M _ _ (etr :tr[ Some τi ]: (t1 ++ e' :: t2 ++ efs, σ')) _)%I with "[HSI]" as "TI".
      { simpl. iDestruct "HSI" as "(?&?&?)". iFrame. }

      iModIntro.
      do 2 iExists _.
      iSplitL "TI".
      { iFrame. }

      (* Set Printing Implicit. *)

      iAssert (wp_tc s e' (S (trace_length etr) <=? ii) Φ -∗
               wptp_wfree s
               (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ'))
               (Φs ++

                  (* newposts (t1 ++ e :: t2) (t1 ++ e' :: t2 ++ efs) (irisG0 := (@IEM_irisG heap_lang _ HeapLangEM EM Σ (@pwt_Hinv Σ PWT))) *)
                   (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) cti_cond
                    in newposts (t1 ++ e :: t2) (t1 ++ e' :: t2 ++ efs))

              ))%I
        with "[WPS1 WPS2 WPS']" as "WPS". 
      { iIntros "WP".
        rewrite app_comm_cons app_assoc.
        iApply wptp_from_gen_app. iSplitR "WPS'".
        2: { simpl. rewrite /newposts.
             rewrite newelems_app_drop.
             2: { rewrite !length_app. simpl. lia. }
             rewrite EQ_TID' in STEP. 
             apply step_fork_hl in STEP as [[? ->] | (?&->&?)].
             { simpl. set_solver. }

             (** in case of tokens, there must be no forks, at least for τi *)
             (* TODO: try to unify the proof with no-tokens case *)
             admit. }
          
        rewrite EQ_Φs. iApply wptp_from_gen_app. iSplitL "WPS1".
        { iApply (wptp_wfree_upd_other with "[$]").
          by rewrite EQ_TID'. }

        simpl. iApply wptp_from_gen_cons.
        iSplitL "WP".
        2: { erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [e'])).
             2: by apply locales_equiv_app1. 
             iApply (wptp_wfree_upd_other with "[$]").
             by rewrite EQ_TID'. }
        
        rewrite /thread_pr. rewrite decide_True; done. }

      (* pr is reestablished differently depending on whether we reach ii.
         TODO: try to unify it *)
      apply Nat.le_lteq in LEN as [LT | <-].
      * iSpecialize ("CPS" with "[$CPP]"); [done| ]. 
        iSpecialize ("WPS" with "[He2]").
        { rewrite /wp_tc. rewrite leb_correct.
          2: { simpl in *. lia. }
          done. }
          
        iFrame "CPS WPS".
        rewrite leb_correct; [| simpl in *; lia].
        iSpecialize ("PHS" with "[PH]"); [by eauto| ].
                    
        iAssert (cur_phases (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')) ∗
                   cur_obls_sigs (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')))%I with "[-CTI]" as "[PHS OBS]".
        { destruct step_fork eqn:SF; simpl. 
          - iDestruct "MOD'" as (?) "(PH' & OB & OB')".
            iSplitL "PH' PHS".
            + iApply "PHS". eauto.
            + iApply ("OBLS" with "[-OB'] [$]"). iFrame.
          - iSplitL "PHS".
            + by iApply "PHS".
            + iApply ("OBLS" with "[-] [//]"). by iFrame. }
        by iFrame.
      * iClear "He2".

        iDestruct (extract_token with "CTI") as "TOK"; eauto. 
        
        iDestruct (th_phase_frag_halve with "PH") as "[PH PH']". 
        iSpecialize ("WPS" with "[CPP PH' TOK]").
        { iPoseProof (get_call_wp with "[] [$] [$] [$]") as "WP".
          { iDestruct "INV" as "[??]". done. }
          (* TODO: extract lemma *)
          clear LEN2 PH CORR.
          clear STEP VALID FIN.
          clear (* H H1 *) NO' NO2 NO1.
          clear dependent Φs1.
          Unshelve. 2: exact ai. 
          rewrite /wp_tc. rewrite leb_correct_conv.
          2: { simpl. lia. }
          destruct FIT. 
          rewrite trace_lookup_extend in fic_call; [| done].
          simpl in fic_call. do 2 red in fic_call. rewrite ic_helper /= in fic_call.
          rewrite EQ_TID' /= in fic_call.
          rewrite (locale_of_hl_expr_irrel _ e e') in fic_call. 
          rewrite /from_locale from_locale_from_locale_of in fic_call.
          inversion fic_call. subst e'. 
          erewrite (proj2 (under_ctx_spec _ _ _)). 
          { simpl. iApply (wp_stuck_mono with "[$]"). done. }
          reflexivity. }

        iFrame "WPS".
        iSpecialize ("CPS" with "[]").
        { iIntros (?). simpl in H0. lia. }
        iFrame "CPS".
        rewrite leb_correct_conv; [| simpl in *; lia].
        iSpecialize ("PHS" with "[PH]").
        { rewrite half_inv2. iFrame. }

        iAssert (cur_phases (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')) ∗
                   cur_obls_sigs (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')))%I with "[-]" as "[PHS OBS]".
        { destruct step_fork eqn:SF; simpl. 
          - iDestruct "MOD'" as (?) "(PH' & OB & OB')".
            iSplitL "PH' PHS".
            + iApply "PHS". eauto.
            + iApply ("OBLS" with "[-OB'] [$]"). iFrame. 
          - iSplitL "PHS".
            + by iApply "PHS".
            + iApply ("OBLS" with "[-] [//]"). iFrame. }
        iFrame.
        simpl. iIntros (?). lia.  
    + apply Nat.leb_gt in LEN. 
      apply fits_inf_call_prev in FIT.
      apply fits_inf_call_last_or_short in FIT as [NVAL | SHORT].
      2: { simpl in *. lia. }

      rewrite leb_correct_conv; [| simpl in *; lia].  
      
      rewrite FIN in NVAL. apply runs_call_helper in NVAL; eauto.
      destruct NVAL as (e_ & CUR & NVAL).

      rewrite CUR. simpl.
      apply under_ctx_spec in CUR.

      rewrite -CUR in PSTEP. eapply fill_step_inv in PSTEP as (?&?&?).
      2: done. 

      iDestruct (wp_ctx_take_step with "[TI] WP") as "He".
      1, 2: by eauto. 
      { red. rewrite FIN. rewrite -CUR. eauto. }
      { subst. done. }
      { iFrame. }

      iMod "He" as "He". iModIntro.
      iMod "He" as "He". iModIntro. iNext.
      iMod "He" as "He". iModIntro.
      iApply (step_fupdN_wand with "[He]"); first by iApply "He".
      iIntros "He".
      iMod "He" as (δ' ℓ) "(HSI & He2 & Hefs) /=".

      iDestruct (same_phase_no_fork with "[$] [$]") as %(-> & EQ_CFG); eauto.

      simpl. rewrite !app_nil_r.
      iDestruct "HSI" as "(%MSTEP & HEAP & MSI)".

      iSpecialize ("PHS" with "[PH]"); [by eauto| ].

      iAssert (wptp_wfree s (etr :tr[ Some τi ]: (t1 ++ fill Ki x :: t2, σ')) Φs)%I with "[WPS1 WPS2 He2]" as "WPS".    
      { rewrite /wptp_wfree. simpl.
        rewrite EQ_Φs. 
        iApply wptp_from_gen_app. iSplitL "WPS1".
        { simpl. iApply (wptp_wfree_upd_other with "[$]").
          by rewrite EQ_TID'. }
        simpl. 
        iApply (wptp_from_gen_app _ _ [_] [_]).
        iSplitL "He2".
        { simpl. iApply wptp_gen_singleton.
          rewrite /thread_pr. rewrite decide_True; [| done].
          rewrite /wp_tc. rewrite leb_correct_conv.
          2: { simpl in *; lia. }
          rewrite under_ctx_fill. done. }

        erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [fill Ki x])).
        2: by apply locales_equiv_app1. 

        simpl. iApply (wptp_wfree_upd_other with "[$]").
        erewrite (proj1 (locales_equiv_from_of_list_from _ _ _ _)).
        { rewrite EQ_TID'. apply NO'. }
        apply adequacy_utils.locales_equiv_from_refl.
        apply locales_equiv_from_middle with (t2 := []). done. }
        
      iAssert (@state_interp _ M _ _ (etr :tr[ Some τi ]: (t1 ++ fill Ki x :: t2, σ')) _)%I with "[HEAP MSI]" as "TI".
      { simpl. by iFrame. }

      rewrite -{6}(app_nil_r (t1 ++ e' :: t2)).
      rewrite /newposts. rewrite newelems_app_drop.
      2: { rewrite !length_app. simpl. lia. }
      simpl. rewrite app_nil_r. 

      iDestruct (reestablish_obls_sigs with "[$]") as "OBS".
      { by rewrite EQ_CFG app_nil_r. }
        
      iDestruct (reestablish_fuel with "[$]") as "CPS". 
      iSpecialize ("PHS" with "[]"). 
      { destruct step_fork eqn:SF; [| done]. simpl.
        rewrite app_nil_r in EQ_CFG. 
        rewrite /step_fork EQ_CFG in SF.
        subst e'. simpl in SF. rewrite difference_diag_L in SF.
        set_solver. }

      subst e'.
      rewrite EQ_TID'. do 2 iExists _.
      iFrame. iModIntro. iIntros (?). simpl in *. lia.  
  Admitted.

  Lemma bump_cti τ c''
    (OTHER: τ ≠ τi)
    (STEP: locale_step (trace_last etr) (Some τ) c''):
    ct_interp_tok etr -∗ ct_interp_tok (etr :tr[ Some τ ]: c'').
  Proof using.
    clear WFST F.
    rewrite /ct_interp_tok /ct_interp.
    iIntros "(%&?&[(? & %) | (%&%&%&->&%)])".
    { iExists _. iFrame. iLeft. eauto. }
    iExists _. iFrame. iRight.
    do 3 iExists _. iPureIntro. split; eauto.
    apply bump_inside_call; eauto.
  Qed.

  Lemma bump_cti_cond τ c''
    (OTHER: τ ≠ τi)
    (STEP: locale_step (trace_last etr) (Some τ) c''):
    cti_cond etr -∗ cti_cond (etr :tr[ Some τ ]: c'').
  Proof using.
    clear WFST F.
    rewrite /cti_cond. simpl.
    iIntros "CTI" (LEN).
    iSpecialize ("CTI" with "[]").
    { iPureIntro. simpl in *. lia. }
    by iApply (bump_cti with "[$]"). 
  Qed.

  (* TODO: this doesn't rely on (oτ ≠ Some τi)? can it be reused?*)
  Lemma take_model_step t1 e' t2 efs σ' π e
    (oτ' := step_fork c (t1 ++ ectx_fill ectx_emp e' :: t2 ++ efs, σ'))
    (τ := locale_of t1 e)
    (FIN': trace_ends_in etr c)
    (STEP: locale_step c (Some τ) (t1 ++ ectx_fill ectx_emp e' :: t2 ++ efs, σ'))
:
    let oGS: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ (@pwt_Hinv _ PWT) in
    cp π0 d0 -∗ th_phase_eq τ π -∗ obls (locale_of t1 e) ∅ -∗ obls_τi' (trace_last etr) -∗     
    @MU_impl _
          EM Σ {| heap_iemgs := @pwt_Hinv Σ PWT |} oτ' ⊤
          τ
          (∃ (π0 : Phase) (R1 R2 : @gset SignalId Nat.eq_dec nat_countable),
             @th_phase_eq Degree Level (locale heap_lang) WF_SB OP Σ
               _
               τ π0 ∗
             (λ R0 R3 : @gset SignalId Nat.eq_dec nat_countable,
                let H :=
                  @iem_fairnessGS heap_lang
                    (AM2M
                       (@ObligationsAM Degree Level (locale heap_lang) WF_SB OP
                          Nat.inhabited))
                    HeapLangEM EM Σ Hinv
                  in
                ⌜R0 = ∅⌝ ∗
                (if
                  decide (oτ' = @Some (locale heap_lang) τi)                    
                 then
                  ∃ s0, ⌜R3 = {[s0]}⌝ ∗
                    @sgn Degree unitO (locale heap_lang) WF_SB OP Σ H s0 l0
                      (@Some bool false) ∗
                    @ep (@sigO natO (λ i : nat, i < 2)) Level
                      (locale heap_lang) WF_SB OP Σ H s0 obligations_model.π0 d0
                 else ⌜R3 = ∅⌝ ∗ @obls_τi' Σ H (t1 ++ e' :: t2 ++ efs, σ')))
               R1 R2 ∗
             ⌜R1 ## R2⌝ ∗
             @from_option (locale heap_lang) (iPropI Σ)
               (λ τ' : locale heap_lang,
                  ∃ π' : Phase,
                    @th_phase_eq Degree Level (locale heap_lang) WF_SB OP Σ
                      _
                      τ' π' ∗
                    @obls Degree Level (locale heap_lang) WF_SB OP Σ _ τ R1 ∗
                    @obls Degree Level (locale heap_lang) WF_SB OP Σ _ τ' R2)
               (@obls Degree Level (locale heap_lang) WF_SB OP Σ _ τ (R1 ∪ R2))
               oτ').
  Proof using.
    clear m WFST VALID FIN F. 
    simpl. iIntros "CP PH OB OBτi".
    rewrite (cp_weaken _ π); [| by apply phase_le_init].
    rewrite /obls_τi' /obls_τi.
    
    iApply (MU_burn_cp with "[-]").
    iFrame "CP PH". simpl.
    rewrite -FIN' in STEP.

    assert (exists sf, sf = oτ') as (sf & Heqsf) by eauto. subst oτ'.
    rewrite FIN' in STEP.
    rewrite -Heqsf. 

    destruct sf; simpl.
    2: { iModIntro. do 2 iExists _.
         iSplitL "OB".
         { erewrite union_empty_r_L. iFrame. }
         repeat (iSplit; try done).
         iApply obls_τi'_next; [| done].
         apply locale_step_step_fork_exact in STEP.
         rewrite -Heqsf /= in STEP.
         rewrite STEP. rewrite FIN'. set_solver. }
    destruct (decide (l = τi)) as [-> | NEQ].
    - rewrite decide_False.
      2: { eapply locale_step_fork_Some in STEP; eauto.
           rewrite FIN'. tauto. }
      iMod (OU_create_sig with "[$]") as "(%sg & SGN & OB & _)".
      { rewrite /WF_SB. lia. }
      iDestruct (sgn_get_ex with "[$]") as "(SGN & #SGN0)".
      iMod (create_ep_upd with "[OBτi] SGN0") as "(#EP & _)".
      { apply (orders_lib.ith_bn_lt 2 0 1). lia. }
      { iFrame. }
      iModIntro. do 2 iExists _. rewrite decide_True; [| done].
      iFrame. iFrame "#∗". iPureIntro. set_solver.
    - iModIntro. iFrame.
      setoid_rewrite (@decide_False _ (Some l = _)); [| congruence].
      do 2 iExists _. erewrite union_empty_r_L. iFrame.
      repeat iSplit; try done.
      rewrite /obls_τi'.
      apply locale_step_step_fork_exact in STEP. rewrite STEP.
      erewrite decide_ext; [by iFrame| ].
      rewrite -Heqsf. simpl.
      rewrite FIN'. set_solver.
  Qed.

  Lemma wptp_wfree_take_step'_other
    (STEP: locale_step c oτ c')
    (OTHER: oτ ≠ Some τi)
    (FIT: fits_inf_call ic m ai (etr :tr[ oτ ]: c')):
    state_interp etr mtr -∗ wfree_trace_inv etr mtr -∗
    pr_pr_wfree s etr Φs 
    ={⊤,∅}=∗ |={∅}▷=>^(S (trace_length etr)) |={∅,⊤}=>
    ∃ (δ' : M) (ℓ : mlabel M),
      state_interp (etr :tr[ oτ ]: c') (mtr :tr[ ℓ ]: δ') ∗
      pr_pr_wfree s (etr :tr[ oτ ]: c') (Φs ++ newposts c.1 c'.1).
  Proof using VALID FIN.
    iIntros "TI #INV PR".
    rewrite /pr_pr_wfree. 
    iDestruct "PR" as "(WPS & CPS & PH & OB & CTI)".

    iDestruct (unfold_helper with "[$]") as "(%&%&%&%&%&%&%&% & %PROPS & WPS1 & WP & WPS2)"; eauto.
    destruct c as [tp σ] eqn:CC, c' as [tp' σ'].
    simpl in PROPS. 
    destruct PROPS as (-> & -> & -> & PSTEP & NO1 & NO' & NO2 & EQ_Φs & LEN1 & LEN2).
    set (τ := locale_of t1 e). 

    iEval (rewrite /thread_pr) in "WP".
    assert (τi ≠ locale_of t1 e) as OTHER'.
    { by intros ->. }
    clear OTHER. 
    
    rewrite decide_False; [| done]. 
    destruct (trace_length etr <=? ii) eqn:LEN.
    + apply Nat.leb_le in LEN.
      simpl.

      iDestruct (split_trace_fuel with "[$]") as "(CP & CPP & CPS)"; [done| ].
      iDestruct (cur_obls_sigs_other_step with "[$]") as "(OB & OBτi & OBLS)".
      { by rewrite FIN. }
      { congruence. }
      iDestruct (cur_phases_other_step _ _ τ with "[$]") as "(PH & PHS)".
      { rewrite FIN. subst τ. eauto. }
      { eauto. }
      { subst τ. congruence. }
      iDestruct "PH" as (π) "PH". 

      remember (step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ')) as sf.

      iDestruct (@pwp_MU_ctx_take_step _ _ _ (@pwt_Hinv _ PWT) si_add_none with "TI [] [CP PH OB OBτi] WP") as "STEP".
      1-2: by eauto.
      { red. rewrite FIN. erewrite ectx_fill_emp. reflexivity. }
      { done. }
      { done. }
      { iPoseProof (take_model_step with "[$] [$] [$] [$]") as "foo".
        { congruence. }
        { rewrite ectx_fill_emp. subst c. eauto. }
        rewrite ectx_fill_emp.
        rewrite FIN. subst τ c.  
        iApply "foo". }

      iMod "STEP". iModIntro.
      iMod "STEP". iModIntro. iNext. 
      iMod "STEP". iModIntro.
      iApply (step_fupdN_wand with "[STEP]"); first by iApply "STEP".
      iIntros "STEP".
      iMod "STEP" as (δ' ℓ) "(HSI & _ & He2 & WPS' & MOD) /=".

      iDestruct "MOD" as (π' R1 R2) "(PH & (-> & MOD) & %DISJ12 & MOD')".        
      rewrite union_empty_l_L. 
        
      iAssert (@state_interp _ M _ _ (etr :tr[ Some τ ]: (t1 ++ e' :: t2 ++ efs, σ')) _)%I with "[HSI]" as "TI".
      { simpl. iDestruct "HSI" as "(?&?&?)". iFrame. }

      iSpecialize ("PHS" with "[$PH]"). 

      iModIntro.
      do 2 iExists _.
      iFrame "TI".

      (** first close the wptp for the _current_ trace length *)
      iAssert (wptp_gen (thread_pr s (trace_length etr)) (t1 ++ e' :: t2 ++ efs) (Φs ++ newposts (t1 ++ e :: t2) (t1 ++ e' :: t2 ++ efs)))%I with "[WPS1 WPS2 WPS' He2]" as "WPS_PRE". 
      { rewrite app_comm_cons app_assoc.
        iApply wptp_from_gen_app. iSplitR "WPS'".
        2: { simpl. rewrite /newposts.
             rewrite newelems_app_drop.
             2: { rewrite !length_app. simpl. lia. }

             subst τ.
             apply step_fork_hl in STEP as [[? ->] | (?&->&?)].
             { simpl. set_solver. }
             rewrite wptp_gen_singleton. rewrite /thread_pr.
             rewrite /wp_tc. rewrite leb_correct; [| done].
             rewrite big_sepL_singleton. simpl. rewrite app_nil_r.
             replace (locale_of (t1 ++ e' :: t2) x) with (locale_of (t1 ++ e :: t2) x).
             2: { rewrite /locale_of. rewrite !length_app. simpl. lia. }
             destruct decide as [-> | ?]; try done.
             (** the case when the target thread is forked off *)
             (* TODO: just prohibit all forking if tokens are used *)
             admit. }
          
        rewrite EQ_Φs. iApply wptp_from_gen_app. iFrame "WPS1". 

        simpl. iApply wptp_from_gen_cons.          
        iSplitL "He2".
        2: { erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [e'])).
             { done. }
             apply locales_equiv_app1. }
               
        rewrite /thread_pr.
        rewrite /wp_tc. rewrite leb_correct; [| done].
        subst τ. 
        destruct decide as [-> | ?]; done. }
      
      destruct (decide (sf = Some τi)) as [-> | NO].
      * (** again, the case with the target thread forked off *)
        admit. 
      * subst c.        
        rewrite decide_False.
        2: { rewrite -FIN. by rewrite -Heqsf. } 
        iDestruct "MOD" as "(-> & OBτi)".

        rewrite FIN in Heqsf.
        rewrite -Heqsf. 

        iAssert (let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
                 obls τ ∅ ∗
                 from_option (λ τ', obls τ' ∅) ⌜ True ⌝ sf ∗
                 from_option (λ τ', ∃ π'0, th_phase_eq τ' π'0) ⌜ True ⌝ sf)%I with "[MOD']" as "(OB & OB' & PH')".
        { destruct sf; simpl. 
          - iDestruct "MOD'" as (?) "(?&?&?)". iFrame.
          - by iFrame. }
             
        iSpecialize ("OBLS" with "OB OBτi [OB']").
        { iIntros (? [EQ ?]). rewrite FIN -Heqsf in EQ. subst.
          simpl. by rewrite EQ. }
            
        iFrame "OBLS".

        (* rewrite -Heqsf. *)
        rewrite FIN. rewrite -Heqsf. 
        iDestruct ("PHS" with "[$]") as "[PHS PHτi]". iFrame "PHS". 

        (* pr is reestablished differently depending on whether we reach ii.
           TODO: try to unify it *)
        (* TODO: the case analysis above is very similar to this one *)
        apply Nat.le_lteq in LEN as [LT | <-].
        ** iClear "PHτi". 
           iSpecialize ("CPS" with "[$CPP]"); [done| ].

           iDestruct (bump_cti_cond with "CTI") as "CTI". 
           { symmetry. apply OTHER'. }
           { rewrite FIN. eauto. }

           iFrame "CPS CTI".

           rewrite /wptp_wfree /wptp_gen /wptp_from_gen.
           simpl. iApply (big_sepL2_impl with "[$]").
           iModIntro. 
           iIntros (k0 [tp0 e0] Φ0 KTH KTH'). simpl.
           rewrite /thread_pr.
           rewrite !leb_correct.
           2, 3: simpl in *; lia.
           by iIntros "$".
        ** iSpecialize ("CPS" with "[]").
           { iIntros (?). simpl in *. lia. }
           iFrame "CPS".
           iDestruct ("PHτi" with "[//]") as (π_) "PHτi".
           rewrite half_inv2.

           iSpecialize ("CTI" with "[]").
           { iPureIntro. lia. }
           iDestruct (bump_cti with "CTI") as "CTI".
           { symmetry. apply OTHER'. }
           { rewrite FIN. eauto. }
           iDestruct (extract_token with "CTI") as "TOK"; eauto. 

           iPoseProof (get_call_wp ai with "[] [$] [$] [$]") as "WP".
           { iDestruct "INV" as "[??]". done. }

           rewrite /newposts. 
           rewrite app_comm_cons app_assoc.  
           rewrite newelems_app_drop.
           2: { rewrite !length_app. simpl. lia. }

           iDestruct (wptp_from_gen_app' with "[$]") as "[WPS WPS']".
           { rewrite EQ_Φs. rewrite !length_app. simpl.
             symmetry in LEN1, LEN2. simpl in *.
             rewrite LEN1 LEN2.
             reflexivity. }

           destruct FIT. 
           rewrite trace_lookup_last in fic_call.
           2: { simpl in *. lia. }
           simpl in fic_call. red in fic_call.
           red in fic_call. rewrite ic_helper /= in fic_call. 

           assert (τi ∉ locales_of_list_from (t1 ++ e' :: t2) efs) as NONEW.
           { subst τ. eapply τi_not_in; eauto. by rewrite FIN -Heqsf. }

           assert (from_locale (t1 ++ e' :: t2) τi = Some (fill Ki (m ai))) as CUR.
           { apply from_locale_from_lookup. split; [| simpl; lia].
             simpl. rewrite Nat.sub_0_r.
             simpl in fic_call. apply from_locale_from_lookup, proj1 in fic_call.
             rewrite /= Nat.sub_0_r in fic_call.
             rewrite app_comm_cons app_assoc in fic_call.
             apply lookup_app_Some in fic_call. destruct fic_call as [? | [OVER ?]].
             { done. }
             destruct NONEW. rewrite locales_of_list_from_indexes.
             apply elem_of_lookup_imap.
            eexists (τi - length (t1 ++ e' :: t2)), _. split; [lia| done]. }
           clear fic_call.

           iSplitL.
           2: { iIntros (?). simpl in *. lia. }

           iApply wptp_from_gen_app. iSplitR "WPS'".
           2: { simpl. iApply (wptp_wfree_upd_other with "[$]"). done. }

           (*****)
           (* TODO: extract a lemma *)
           remember (t1 ++ e' :: t2) as tp'.
           generalize τ. clear τ. intros τ. 
           clear dependent Φs1 Φs2  t1 t2 e.
           pose proof CUR as X%from_locale_lookup%elem_of_list_split_length.
           destruct X as (t1 & t2 & -> & ->).
           iDestruct (wptp_gen_split_1 with "[$]") as %X.
           destruct X as (Φs1 & Φs2 & <- & LEN1 & LEN2).
           iDestruct (wptp_from_gen_app' with "[$]") as "[WPS1 WPS]"; [done| ].
           iApply wptp_from_gen_app. iSplitL "WPS1".
           { iApply (wptp_wfree_upd_other with "[$]").
             rewrite H0. 
             rewrite locales_of_list_from_indexes.
             intros (?&?&?&?)%elem_of_lookup_imap.
             apply lookup_lt_Some in H2. simpl in *. lia. }
           simpl. destruct Φs2; [done| ].
           (* drop the existing pwp for τi *)
           rewrite wptp_from_gen_cons. iDestruct "WPS"  as "[_ WPS2]". 
           iApply wptp_from_gen_cons. iSplitR "WPS2".
           2: { iApply (wptp_wfree_upd_other with "[$]").
                rewrite H0. 
                rewrite locales_of_list_from_indexes.
                intros (?&?&?&?)%elem_of_lookup_imap.
                apply lookup_lt_Some in H2.
                rewrite length_app /= in H1. 
                lia. }
                  
           rewrite /thread_pr. rewrite !decide_True; try done.
           rewrite /wp_tc. rewrite leb_correct_conv; [| simpl in *; lia].
           rewrite under_ctx_fill /= -H0. 
           iApply (wp_stuck_mono with "[$]"). done.
    + apply leb_complete_conv in LEN. simpl in LEN.

      iClear "CPS".
      iAssert (extra_fuel (etr :tr[ Some τ ]: (t1 ++ e' :: t2 ++ efs, σ'))) as "CPS'".
      { rewrite /extra_fuel. rewrite leb_correct_conv; [done| ].
        simpl. lia. }
        
      iDestruct (cur_obls_sigs_other_step with "[$]") as "(OB & OBτi & OBLS)".
      { by rewrite FIN. }
      { congruence. }
      iDestruct (cur_phases_other_step with "[$]") as "(PH & PHS)"; eauto.
      { rewrite FIN. subst τ. eauto. }
      iDestruct "PH" as (π) "PH". 

      rewrite {1}/obls_τi'.
      rewrite decide_True.
      2: { eapply fic_has_τi; eauto. eapply fits_inf_call_prev; eauto. }

      remember (step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ')) as sf.

      iDestruct (@pwp_MU_ctx_take_step _ _ _ Hinv with "TI [] [OB PH OBτi] WP") as "STEP".
      1-2: by eauto.
      { red. rewrite FIN. erewrite ectx_fill_emp. reflexivity. }
      { done. }
      { done. }
      { rewrite -Heqsf. 
        iApply (MU_burn_cp _ _ _ _ (fun (R1 R2: gset SignalId) => (⌜ R1 = ∅ /\ R2 = ∅⌝ ∗ obls_τi)%I) with "[-]").
        iMod (BOU_wait_τi with "[$] [$] [$]") as "(?&?&OB&?)".
        iModIntro. do 2 iExists _. iFrame.  
        iSplitL "OB".
        { by erewrite union_empty_l_L. }
        iFrame. iPureIntro. set_solver. }          
          
      iMod "STEP". iModIntro.
      iMod "STEP". iModIntro. iNext. 
      iMod "STEP". iModIntro.
      iApply (step_fupdN_wand with "[STEP]"); first by iApply "STEP".
      iIntros "STEP".
      iMod "STEP" as (δ' ℓ) "(HSI & _ & He2 & WPS' & MOD) /=".

      iDestruct "MOD" as (π' R1 R2) "(PH & ((-> & ->) & OBτi) & %DISJ12 & MOD')".
      rewrite union_empty_l_L. 

      iAssert (@state_interp _ M _ _ (etr :tr[ Some τ ]: (t1 ++ e' :: t2 ++ efs, σ')) _)%I with "[HSI]" as "TI".
      { simpl. iDestruct "HSI" as "(?&?&?)". iFrame. }

      iFrame "TI". iFrame "CPS'". iClear "CPS'".

      iAssert (let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
               obls τ ∅ ∗
               from_option (λ τ', obls τ' ∅) ⌜ True ⌝ sf ∗
               from_option (λ τ', ∃ π'0, th_phase_eq τ' π'0) ⌜ True ⌝ sf)%I with "[MOD']" as "(OB & OB' & PH')".
      { destruct sf; simpl. 
        - iDestruct "MOD'" as (?) "(?&?&?)". iFrame.
        - by iFrame. }

      iSpecialize ("OBLS" with "[$] [OBτi] [OB']").
      { rewrite /obls_τi'. rewrite decide_True; [done| ].
        apply fic_has_τi in FIT; [done| ].
        simpl. lia. }
      { rewrite -Heqsf. by iIntros (? [-> ?]). }
      iFrame "OBLS".

      rewrite -Heqsf. 
      iDestruct ("PHS" with "[$PH] [$]") as "[PHS _]". iFrame "PHS".
      iModIntro.
      rewrite app_comm_cons app_assoc.
      iSplitL.
      2: { iIntros (?). simpl in *. lia. }
 
      iApply wptp_from_gen_app. iSplitR "WPS'".
      2: { simpl.
           replace (newposts (t1 ++ e :: t2) ((t1 ++ e' :: t2) ++ efs)) with
             (newposts (t1 ++ e' :: t2) ((t1 ++ e' :: t2) ++ efs)).
           2: { apply adequacy_utils.newposts_locales_equiv.
                apply locales_equiv_middle. done. }
           rewrite -new_threads_wptp_from_gen.
           iApply (big_sepL_impl with "[$]").
           iModIntro. 
           iIntros (i x ITH).
           rewrite /thread_pr.
           destruct decide.
           2: { simpl. list_simplifier.
                rewrite /locale_of. rewrite !length_app /=.
                by iIntros "$". }

           apply fits_inf_call_prev, fits_inf_call_last_or_short in FIT.
           destruct FIT as [NVAL | SHORT].
           2: { simpl in SHORT. lia. }
           (* red in FIT. destruct FIT as (?& IN & ?&?). *)
           move NVAL at bottom.
           rewrite /τi in e0.
           red in NVAL. destruct NVAL as (?&EXPR&NVAL).
           red in EXPR. rewrite ic_helper in EXPR. 
           rewrite FIN /= in EXPR.
           rewrite /τi e0 in EXPR. 
           apply from_locale_lookup in EXPR. 
           apply lookup_lt_Some in EXPR.
           rewrite /locale_of !length_app /= in EXPR. lia. }

      simpl.
      iAssert (wptp_from_gen (thread_pr s (trace_length etr)) [] (t1 ++ e' :: t2) Φs)%I with "[-]" as "WPS".
      { rewrite EQ_Φs. iApply wptp_from_gen_app. iSplitL "WPS1"; [done| ].
        simpl. iApply wptp_from_gen_cons. iSplitR "WPS2".
        { rewrite /thread_pr. rewrite decide_False; done. }
        iApply (wptp_from_gen_locales_equiv_1 with "[$]").
        apply locales_equiv_app1. }
          
      (* TODO: Make a lemma *)
      iApply (big_sepL2_impl with "[$]").
      iModIntro. 
      iIntros (i pfi Φi PFith Φith).
      rewrite /thread_pr.
      erewrite (proj2 (leb_eq_equiv _ _ _ _)).
      { by iIntros "$". }
      simpl in *. lia. 
  Admitted.
  
  (* our PR instance in fact implies the not-stuck property *)
  (* TODO: ? move this property to definition of PR? *)
  Lemma wptp_wfree_take_step 
    (STEP: locale_step c oτ c')
    (FIT: fits_inf_call ic m ai (etr :tr[ oτ ]: c')):
    state_interp etr mtr -∗ wfree_trace_inv etr mtr -∗
    pr_pr_wfree s etr Φs 
    ={⊤,∅}=∗ |={∅}▷=>^(S (trace_length etr)) |={∅,⊤}=>
    ⌜∀ e2: expr, s = NotStuck → e2 ∈ c'.1 → not_stuck e2 c'.2⌝ ∗
    ∃ (δ' : M) (ℓ : mlabel M),
      state_interp (etr :tr[ oτ ]: c') (mtr :tr[ ℓ ]: δ') ∗
      wfree_trace_inv (etr :tr[ oτ ]: c') (mtr :tr[ ℓ ]: δ') ∗
      pr_pr_wfree s (etr :tr[ oτ ]: c') (Φs ++ newposts c.1 c'.1).
  Proof using VALID FIN.
    iIntros "? #INV ?".
    
    iAssert (|={⊤,∅}=> |={∅}▷=>^(S (trace_length etr)) |={∅,⊤}=> 
    ∃ (δ' : M) (ℓ : mlabel M),
      state_interp (etr :tr[ oτ ]: c') (mtr :tr[ ℓ ]: δ') ∗
      pr_pr_wfree s (etr :tr[ oτ ]: c') (Φs ++ newposts c.1 c'.1))%I with "[-]" as "X".
    { destruct (decide (oτ = Some τi)).
      - by iApply (wptp_wfree_take_step_τi with "[$] [$] [$]"). 
      - by iApply (wptp_wfree_take_step'_other with "[$] [$] [$]"). } 

    iMod "X". iModIntro.
    iApply (step_fupdN_wand with "X").
    iIntros "X". iMod "X" as (??) "(TI & PR)".
    rewrite /pr_pr_wfree. iDestruct "PR" as "(WPS & ? & ? & OBS & CTI)".
    iMod (wptp_wfre_not_stuck with "TI WPS CTI") as "(TI & WPS & CTI & %NSTUCK')"; eauto.
    { econstructor; eauto. }
    { erewrite app_nil_r. red. simpl. apply surjective_pairing. }
    iDestruct (reestablish_wfree_inv with "[] [$] [$]") as "#INV'".
    2: { iDestruct "INV" as "[??]". done. }
    { done. }
    iModIntro. iFrame. iSplit; [| done].
    iPureIntro. intros. by apply NSTUCK'.
  Qed.

  End TakeStep.

  Program Definition PR_wfree {Σ} {PWT: PrWfreeTok Σ}:
    @ProgressResource heap_lang M Σ (@iem_invGS _ _ _ _ _ (@pwt_Hinv _ PWT))
      state_interp wfree_trace_inv

      (* fork_post *)
      (fun _ _ =>
         let _ := IEM_irisG HeapLangEM EM in
         ⌜ True ⌝%I: iProp Σ) (* because upon forks we only obtain pwp .. { True } *)

      (fits_inf_call ic m ai) :=
    {| pr_pr := pr_pr_wfree |}.
  Next Obligation.
    apply @wptp_wfree_posts.
  Qed.
  Next Obligation.
    apply @wptp_wfree_not_stuck.
  Qed.
  Final Obligation.
    intros ??? etr Φs c oτ c' mtr VALID FIN STEP.
    iIntros "_ TI #INV PR %FIT". (* cwp is not needed*)
    iApply (wptp_wfree_take_step with "[$] [$] [$]"); eauto.
  Qed.

End WaitFreePR.
