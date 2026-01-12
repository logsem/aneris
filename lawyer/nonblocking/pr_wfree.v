From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context om_wfree_inst wptp_gen pwp wfree_traces calls pr_wfree_lib.
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

  Context (s': stuckness). 
  Context `(WFS: WaitFreeSpec s' Pred m).
  Let F := wfs_F _ _ _ WFS. 
  
  Open Scope WFR_scope. 

  Lemma get_call_wp {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (a: val) π
    (Pa: Pred a):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfs_mod_inv _ _ _ WFS) -∗
    cp_mul π0 d0 (F a) -∗ th_phase_frag τi π (1 / 2)%Qp -∗
    WP m a @ s' ; τi ; ⊤ {{ _, ⌜ True ⌝ }}.
  Proof using.
    simpl. iIntros "#INV CPS PH".
    pose proof (@wfs_spec _ _ _ WFS _ EM Σ OHE) as SPEC. 
    iApply (SPEC with "[] [-]").
    { done. }
    2: { by iIntros "!> **". } 
    iSplitL "CPS"; [| by iFrame].
    iApply (cp_mul_weaken with "[$]"); [| done].
    apply phase_le_init.
  Qed.

  (* TODO: add this to tokens version *)
  Definition call_progresses (etr: execution_trace heap_lang) := 
    s' = NotStuck -> ii < trace_length etr -> 
    not_stuck_tid τi (trace_last etr).

  Definition wfree_trace_inv `{Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (extr: execution_trace heap_lang) (omtr: auxiliary_trace M): iProp Σ :=
    ⌜ no_extra_obls ic (trace_last extr) (trace_last omtr) /\
      from_option (fun e => to_val e = None) True (from_locale (trace_last extr).1 τi) /\
      call_progresses extr ⌝ ∗
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfs_mod_inv _ _ _ WFS). 
  
  Context (ai: val) (Pai: Pred ai).

  Definition wp_tc {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness) (e: expr) (b: bool) Φ :=
    if b then
      let _ := IEMGS_into_Looping Hinv si_add_none in
      pwp s ⊤ τi e Φ
    else
      let e' := default (Val #false) (under_ctx Ki e) in
      (* from now on, we forget about the original postcondition *)
      wp s' ⊤ τi e' (fun _ => ⌜ True ⌝%I).

  Definition thread_pr {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} s N :=
    (fun e τ Φ => if decide (τi = τ) then wp_tc s e (N <=? ii) Φ
                 else let _ := IEMGS_into_Looping Hinv si_add_none in pwp s ⊤ τ e Φ).

  Definition wptp_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness) (etr: execution_trace heap_lang) (Φs : list (val → iPropI Σ)):
    iProp Σ :=
    wptp_gen (thread_pr s (trace_length etr)) (trace_last etr).1 Φs.

  Lemma wptp_wfre_not_stuck {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}    
    ex atr σ tp trest s Φs 
    (S'_LE: stuckness_le s' s)
    :
    valid_exec ex →
    trace_ends_in ex (tp ++ trest, σ) →
    fits_inf_call ic m ai ex ->
    state_interp ex atr -∗ wptp_wfree s ex Φs ={⊤}=∗
    state_interp ex atr ∗ wptp_wfree s ex Φs ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (Hexvalid Hex FIT) "HSI Ht".
    rewrite assoc.
    iApply fupd_plain_keep_r; iFrame.
    iIntros "[HSI Ht]".
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
    - iMod (wp_not_stuck _ _ ectx_emp with "[HSI] W") as "(_ & _ & ?)";
      [done| rewrite ectx_fill_emp // | .. ].
      { done. }
      { simpl. rewrite /phys_SI. simpl.
        iSplit; [| done]. 
        by iDestruct "HSI" as "(?&?&?)". }
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
      subst s. simpl in S'_LE. destruct s'; try done.
      specialize (NS ltac:(done)).
      rewrite Hex in NS. simpl in NS.
      eapply not_stuck_fill; eauto.
    - iMod (wp_not_stuck _ _ ectx_emp with "[HSI] W") as "(_ & _ & %NS)";
      [done| rewrite ectx_fill_emp // | .. ].
      { done. }
      { simpl. rewrite /phys_SI. simpl.
        iSplit; [| done]. 
        by iDestruct "HSI" as "(?&?&?)". }
      simpl. by rewrite Hex in NS.
    (* TODO: get rid of this? *)
    Unshelve. all: by apply trace_singleton. 
  Qed. 

  Definition pr_pr_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness) (etr: execution_trace heap_lang) (Φs: list (val → iProp Σ)): iProp Σ :=
    let oGS: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    wptp_wfree s etr Φs ∗ extra_fuel ic (F ai) etr ∗ cur_phases ic etr ∗ cur_obls_sigs ic etr ∗
    ⌜ stuckness_le s' s ⌝
  . 
  
  Lemma reestablish_wfree_inv {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr mtr s Φs
    (VALID: valid_exec etr)
    (FIT: fits_inf_call ic m ai etr)
    :
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    let RES := (cur_obls_sigs ic etr ∗ wptp_wfree s etr Φs ∗ state_interp etr mtr)%I in
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfs_mod_inv _ _ _ WFS) -∗
    RES
    ={⊤}=∗ wfree_trace_inv etr mtr ∗ RES. 
  Proof using.
    simpl. iIntros "#INV (OB & WPS & TI)".
    clear -FIT VALID. 
    rewrite /wfree_trace_inv. iFrame "INV". simpl.
    rewrite /no_extra_obls. simpl.
    rewrite and_assoc. rewrite bi.pure_and.
    (* rewrite -!bi.sep_assoc. *)
    rewrite pure_and_sep. rewrite -bi.sep_assoc. 
    iApply fupd_frame_l.
    iSplit. 
    - iSplit. 
      + iDestruct "TI" as "(_&_&MSI)". rewrite /obls_asem_mti. simpl.
        rewrite /obls_si. iDestruct "MSI" as "(MSI & %CORR')".
        iIntros (τ' OBS).
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
      + iPureIntro.
        destruct FIT. 
        ospecialize (fic_never_val (trace_length etr - 1)).
        erewrite (trace_lookup_last etr) in fic_never_val.
        { done. }
        simpl. rewrite -Nat.sub_succ_l; [lia| ].
        destruct etr; simpl; lia.
    - iFrame "OB". iClear "INV".

      (* TODO: extract lemma, unify with similar proof in wptp_wfre_not_stuck *)
      rewrite /call_progresses. 

      destruct (decide (ii < trace_length etr)) as [LONG | SHORT].
      2: { iFrame. iModIntro. iIntros (??). lia. }

      pose proof LONG as IN. eapply fic_has_τi in IN; eauto.
      destruct (trace_last etr) as [tp ?] eqn:LAST.
      pose proof IN as IN'.
      apply locales_of_cfg_Some in IN' as [e TI].
      pose proof TI as TI'%from_locale_lookup.
      apply elem_of_list_split_length in TI' as (?&?&->&?).

      apply fits_inf_call_last_or_short in FIT as [NVAL | SHORT].
      2: lia. 
      rewrite LAST in NVAL.
      eapply runs_call_helper in NVAL; eauto.
      destruct NVAL as (ec & CUR & NVAL).

        iDestruct (wptp_from_gen_take_2 _ _ _ _ τi with "WPS") as "X".
        { rewrite /locales_of_cfg in IN.
          eapply elem_of_list_to_set; eauto.
          simpl in IN. rewrite LAST /=. set_solver. }
        
        rewrite LAST. simpl. 
        iDestruct "X" as "(%&%&%&%TI'&WP&CLOS)".
        rewrite /from_locale in TI. rewrite TI in TI'. inversion TI'. subst e0. 
        rewrite {1}/thread_pr. rewrite decide_True; [| done].
        rewrite /wp_tc. rewrite leb_correct_conv; [| done]. 

      rewrite CUR.
      pose proof CUR as <-%under_ctx_spec. 
      iSimpl in "WP".
      
      iMod (wp_not_stuck _ _ Ki with "[TI] WP") as "(? & WP & %NS)";
      [done|  | .. ].
      { simpl. erewrite (proj1 (under_ctx_spec _ _ _)); eauto. }
      { done. }
      { simpl. rewrite LAST. iFrame. }

      iModIntro. iSplit.
      { iPureIntro. intros. rewrite -LAST.
        red. eexists. split.
        { rewrite LAST. eauto. }
        eapply not_stuck_fill; eauto. }

      iSpecialize ("CLOS" with "[WP]").
      { rewrite /thread_pr. rewrite decide_True; [| done]. 
        rewrite /wp_tc.
        rewrite leb_correct_conv; [| done]. 
        rewrite CUR. done. }
      simpl. rewrite /wptp_wfree LAST. iFrame.
      Unshelve. apply _. 
  Qed.

  Lemma wptp_wfree_other_simpl {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    s (etr: execution_trace heap_lang) tp0 tp Φs
    (OTHER: τi ∉ locales_of_list_from tp0 tp):
    wptp_from_gen (thread_pr s (trace_length etr)) tp0 tp Φs ⊣⊢
    let _ := IEMGS_into_Looping _ si_add_none (EM := EM) in
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

  Lemma wptp_wfree_posts {Σ: gFunctors} (Hinv : IEMGS HeapLangEM EM Σ)
    (s : stuckness) (etr: execution_trace heap_lang) (Φs : list (val → iProp Σ))
    (FIT: fits_inf_call ic m ai etr):
    let Ps := adequacy_utils.posts_of (trace_last etr).1 Φs in
    pr_pr_wfree s etr Φs -∗ |~~| Ps ∗ (Ps -∗ pr_pr_wfree s etr Φs).
  Proof using.
    clear Pai.
    simpl. 
    set (Ps := adequacy_utils.posts_of (trace_last etr).1 Φs). simpl. 
    iUnfold pr_pr_wfree.
    iIntros "(WPS & CPS & PH & OB)".

    iAssert (pre_step top top (Ps ∗ (Ps -∗ wptp_wfree s etr Φs)) (irisG0 := {|
      iris_invGS :=
        @iem_invGS heap_lang (AM2M _) HeapLangEM EM Σ Hinv;
      state_interp :=
        @state_interp heap_lang M Σ _;
      fork_post := λ (_ : locale heap_lang) (_ : val), True        
    |}))%I with "[WPS]" as "CLOS".
    2: { iMod "CLOS". iModIntro. by iFrame. }
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

    iAssert (|~~| adequacy_utils.posts_of tp' Φs_ ∗ (adequacy_utils.posts_of tp' Φs_ -∗ wptp_from_gen (thread_pr s (trace_length etr)) tp1 tp' Φs_))%I with "[WPS']" as "WPS'".
    { destruct TP' as [-> | (e & -> & EQ)].
      { iModIntro. rewrite /adequacy_utils.posts_of. simpl. set_solver. }
      destruct Φs_ as [ | ? [|] ].
      1, 3: simpl in LEN2; lia.
      rewrite wptp_gen_singleton.
      rewrite /adequacy_utils.posts_of. simpl.
      destruct (to_val e) eqn:VAL; simpl.
      2: { iFrame. iModIntro. set_solver. }
      rewrite /thread_pr. rewrite decide_True; [| done].
      pose proof (of_to_val e _ VAL) as EV. rewrite -EV.        
      rewrite /wp_tc. destruct leb eqn:LEN.
      - iPoseProof (wp_value_inv' with "WPS'") as "foo".
        iMod (pre_step_looping_wfree_elim with "foo") as "foo".
        iModIntro. iFrame. iIntros "(? & _)".
        by iApply @wp_value'.
      - apply fits_inf_call_last_or_short in FIT. destruct FIT as [RUNS | SHORT].
        2: { apply leb_complete_conv in LEN. simpl in SHORT. lia. }

        rewrite LAST /= in RUNS. apply runs_call_helper in RUNS; eauto.  
        destruct RUNS as (e_ & CTX & NVAL).
        apply under_ctx_val_Some_inv in CTX as [? ->]; eauto.
        congruence. }
      
    iMod (pre_step_looping_wfree_elim with "foo") as "[P1 WPS1]". 
    iMod (pre_step_looping_wfree_elim with "bar") as "[P2 WPS2]".
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

  Lemma wptp_wfree_not_stuck {Σ : gFunctors} (Hinv : IEMGS HeapLangEM EM Σ) 
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
    rewrite /pr_pr_wfree. iDestruct "PR" as "(WPS &X&Y&Z&%S'_LE)".
    iFrame "X Y Z".
    iFrame (S'_LE). 
    iApply (wptp_wfre_not_stuck with "[$] [$]"); eauto.
  Qed.

  Lemma wptp_wfree_upd_other `{Hinv : @IEMGS _ _ HeapLangEM EM Σ} s N tp0 tp Φs
    (OTHER: τi ∉ locales_of_list_from tp0 tp):
    wptp_from_gen (thread_pr s N) tp0 tp Φs -∗
    wptp_from_gen (thread_pr s (S N)) tp0 tp Φs.
  Proof using.
    clear m ai WFS F Pai.
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
  Context {Σ} (Hinv : IEMGS HeapLangEM EM Σ).
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
    clear mtr m WFS VALID F. 
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
    
  #[local] Arguments Nat.leb _ _ : simpl nomatch.

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
  Proof using VALID FIN Pai.
    iIntros "TI #INV PR".
    rewrite /pr_pr_wfree. 
    iDestruct "PR" as "(WPS & CPS & PH & OB & %S'_LE)".

    iDestruct (unfold_helper with "[$]") as "(%&%&%&%&%&%&%&% & %PROPS & WPS1 & WP & WPS2)"; eauto.
    subst oτ. 
    destruct c as [tp σ], c' as [tp' σ'].
    simpl in PROPS. 
    destruct PROPS as ([=EQ_TID'] & -> & -> & PSTEP & NO1 & NO' & NO2 & EQ_Φs & LEN1 & LEN2).
    (* set (τ := locale_of t1 e).  *)

    iEval (rewrite /thread_pr) in "WP".
    rewrite decide_True.
    2: congruence. 
 
    rewrite EQ_TID'. 
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
    + apply Nat.leb_le in LEN.
      simpl. 

      iDestruct (split_trace_fuel with "[$]") as "(CP & CPP & CPS)"; [done| ].
      iDestruct (cur_obls_sigs_τi_step with "[$]" ) as "(OB & OBLS)".
      { by rewrite FIN. }

      rewrite {1}/obls_τi. iDestruct "OB" as "(%si & OB & SGN & EP)".

      iDestruct (@pwp_MU_ctx_take_step _ _ _ Hinv with "TI [] [CP PH OB] WP") as "STEP".
      1-2: by eauto. 
      { red. rewrite FIN. erewrite ectx_fill_emp. reflexivity. }
      { done. }
      { done. }
      { rewrite (cp_weaken _ π); [| by apply phase_le_init].
        iApply (MU_burn_cp _ _ _ _ (fun R1 R2 => (⌜ R1 = {[ si ]} /\ R2 = ∅ ⌝)%I) with "[$CP $PH OB]").
        iModIntro. do 2 iExists _. iSplit.
        2: { iPureIntro. split; [split| ]; try reflexivity. done. }
        by rewrite union_empty_r_L. }
          
      iMod "STEP". iModIntro.
      iMod "STEP". iModIntro. iNext. 
      iMod "STEP". iModIntro.
      iApply (step_fupdN_wand with "[STEP]"); first by iApply "STEP".
      iIntros "STEP".
      iMod "STEP" as (δ' ℓ) "(HSI & _ & He2 & WPS' & MOD) /=".

      iDestruct "MOD" as (π' ??) "(PH & [->->] & _ & MOD')".
      rewrite union_empty_r_L. 

      iAssert (@state_interp _ M _ _ (etr :tr[ Some τi ]: (t1 ++ e' :: t2 ++ efs, σ')) _)%I with "[HSI]" as "TI".
      { simpl. iDestruct "HSI" as "(?&?&?)". iFrame. }

      iModIntro.
      do 2 iExists _.
      iSplitL "TI".
      { simpl. rewrite EQ_TID'. iFrame. }

      iAssert (wp_tc s e' (S (trace_length etr) <=? ii) Φ -∗
               wptp_wfree s
               (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ'))
               (Φs ++ newposts (t1 ++ e :: t2) (t1 ++ e' :: t2 ++ efs) (irisG0 := {|
    iris_invGS :=
      @iem_invGS heap_lang
        (AM2M
           (@ObligationsAM (@sigO natO (λ i : nat, i < 2)) unitO
              (locale heap_lang) WF_SB OP Nat.inhabited))
        HeapLangEM EM Σ Hinv;
    state_interp :=
      @state_interp heap_lang M Σ (@IEM_irisG heap_lang M HeapLangEM EM Σ Hinv);
    fork_post := λ (_ : locale heap_lang) (_ : val), True        
  |})))%I with "[WPS1 WPS2 WPS']" as "WPS". 
      { iIntros "WP".
        rewrite app_comm_cons app_assoc.
        iApply wptp_from_gen_app. iSplitR "WPS'".
        2: { simpl. rewrite /newposts.
             rewrite newelems_app_drop.
             2: { rewrite !length_app. simpl. lia. }
             rewrite EQ_TID' in STEP. 
             apply step_fork_hl in STEP as [[? ->] | (?&->&?)].
             - simpl. set_solver.
             - rewrite wptp_gen_singleton. rewrite /thread_pr.
               rewrite decide_False.
               2: { intros ->. rewrite /locale_of in EQ_TID'. 
                    rewrite !length_app /= in EQ_TID'. lia. }
               rewrite big_sepL_singleton. simpl.
               rewrite app_nil_r.
             replace (locale_of (t1 ++ e' :: t2) x) with (locale_of (t1 ++ e :: t2) x); [done| ].
             rewrite /locale_of. rewrite !length_app. simpl. lia. } 
          
      rewrite EQ_Φs. iApply wptp_from_gen_app. iSplitL "WPS1".
      { iApply (wptp_wfree_upd_other with "[$]").
        by rewrite EQ_TID'. }

      simpl. iApply wptp_from_gen_cons.
      iSplitL "WP".
      2: { erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [e'])).
           2: { rewrite !prefixes_from_app.
                eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
                simpl. by constructor. }
           iApply (wptp_wfree_upd_other with "[$]").
           by rewrite EQ_TID'. }
             
      rewrite /thread_pr. rewrite decide_True; [done| ]. 
      done. }

      (* pr is reestablished differently depending on whether we reach ii.
         TODO: try to unify it *)
      apply Nat.le_lteq in LEN as [LT | <-].
      * iSpecialize ("CPS" with "[$CPP]"); [done| ]. 
        iSpecialize ("WPS" with "[He2]").
        { rewrite /wp_tc. rewrite leb_correct.
          2: { simpl in *. lia. }
          done. }
          
        iFrame "CPS WPS".
        (* rewrite leb_correct; [| simpl in *; lia]. *)
        iSpecialize ("PHS" with "[PH]").
        { destruct ii eqn:II; [lia| ].
          unfold ii in II. rewrite II.
          rewrite leb_correct; [| simpl in *; lia]. eauto. }
                    
        iAssert (cur_phases ic (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')) ∗
                   cur_obls_sigs ic (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')))%I with "[-]" as "[PHS OBS]".
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
        iDestruct (th_phase_frag_halve with "PH") as "[PH PH']". 
        iSpecialize ("WPS" with "[CPP PH']").
        { iPoseProof (get_call_wp with "[] [$] [$]") as "WP".
          { done. }
          { iDestruct "INV" as "[??]". done. }
          (* TODO: extract lemma *)
          clear LEN2 PH CORR.
          clear STEP VALID FIN.
          clear (* H H1 *) NO' NO2 NO1.
          clear dependent Φs1.
          rewrite /wp_tc. rewrite leb_correct_conv.
          2: { simpl. lia. }
          destruct FIT. 
          rewrite trace_lookup_extend in fic_call; [| done].
          simpl in fic_call. do 2 red in fic_call. rewrite ic_helper /= in fic_call.
          rewrite EQ_TID' /= in fic_call.
          replace (locale_of t1 e) with (locale_of t1 e') in fic_call.
          2: { done. }
          rewrite /from_locale from_locale_from_locale_of in fic_call.
          inversion fic_call. subst e'. 
          erewrite (proj2 (under_ctx_spec _ _ _)). 
          { simpl. iApply (wp_stuck_mono with "[$]"). done. }
          reflexivity. }

        iFrame "WPS".
        iSpecialize ("CPS" with "[]").
        { iIntros (?). simpl in *. lia. }
        iFrame "CPS".
        
        iSpecialize ("PHS" with "[PH]").
        { rewrite half_inv2.
          unfold ii in H. rewrite -H.
          rewrite leb_correct_conv; [| simpl in *; lia].
          iFrame. }

        iAssert (cur_phases ic (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')) ∗
                   cur_obls_sigs ic (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')))%I with "[-]" as "[PHS OBS]".
        { destruct step_fork eqn:SF; simpl. 
          - iDestruct "MOD'" as (?) "(PH' & OB & OB')".
            iSplitL "PH' PHS".
            + iApply "PHS". eauto.
            + iApply ("OBLS" with "[-OB'] [$]"). iFrame. 
          - iSplitL "PHS".
            + by iApply "PHS".
            + iApply ("OBLS" with "[-] [//]"). iFrame. }
        by iFrame.            
    + apply Nat.leb_gt in LEN. 
      apply fits_inf_call_prev in FIT.
      apply fits_inf_call_last_or_short in FIT as [NVAL | SHORT].
      2: { simpl in *. lia. }
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

      iSpecialize ("PHS" with "[PH]").
      { rewrite leb_correct_conv; [| simpl in *; lia]. eauto. }

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
        2: { rewrite !prefixes_from_app.
             eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
             simpl. by constructor. }
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
      by iFrame.
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
  Proof using VALID FIN Pai.
    iIntros "TI #INV PR".
    rewrite /pr_pr_wfree. 
    iDestruct "PR" as "(WPS & CPS & PH & OB & %S'_LE)".

    iDestruct (unfold_helper with "[$]") as "(%&%&%&%&%&%&%&% & %PROPS & WPS1 & WP & WPS2)"; eauto.
    destruct c as [tp σ], c' as [tp' σ'].
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
      { set_solver. }
      iDestruct (cur_phases_other_step _ _ _ τ with "[$]") as "(PH & PHS)".
      { rewrite FIN. subst τ. eauto. }
      { eauto. }
      { subst τ. set_solver. }
      iDestruct "PH" as (π) "PH". 

      remember (step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ')) as sf.

      iDestruct (@pwp_MU_ctx_take_step _ _ _ Hinv with "TI [] [CP PH OB OBτi] WP") as "STEP".
      1-2: by eauto.
      { red. rewrite FIN. erewrite ectx_fill_emp. reflexivity. }
      { done. }
      { done. }
      { iPoseProof (take_model_step with "[$] [$] [$] [$]") as "foo".
        { apply trace_ends_in_last. }
        { rewrite ectx_fill_emp.
          by rewrite FIN. }
        rewrite ectx_fill_emp.
        rewrite FIN. 
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
      (* iSpecialize ("OBLS" with "[$]"). *)

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
             - simpl. set_solver.
             - rewrite wptp_gen_singleton. rewrite /thread_pr.
               rewrite /wp_tc. rewrite leb_correct; [| done].
               rewrite big_sepL_singleton. simpl. rewrite app_nil_r.
               replace (locale_of (t1 ++ e' :: t2) x) with (locale_of (t1 ++ e :: t2) x).
               2: { rewrite /locale_of. rewrite !length_app. simpl. lia. } 
               destruct decide as [-> | ?]; done. }
          
        rewrite EQ_Φs. iApply wptp_from_gen_app. iFrame "WPS1". 

        simpl. iApply wptp_from_gen_cons.          
        iSplitL "He2".
        2: { erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [e'])).
             { done. }
             rewrite !prefixes_from_app.
             eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
             simpl. by constructor. }
               
        rewrite /thread_pr.
        rewrite /wp_tc. rewrite leb_correct; [| done].
        subst τ. 
        destruct decide as [-> | ?]; done. }

      destruct (decide (sf = Some τi)) as [-> | NO].
      * simpl. symmetry in Heqsf.
        rewrite decide_True //.
        2: { rewrite -FIN Heqsf. set_solver. }
        iDestruct "MOD" as "(% & -> & SGN & #EP)".
        rewrite -FIN Heqsf. 
        iDestruct "MOD'" as "(% & PHτi & OB & OBτi)". 

        iSpecialize ("OBLS" with "[$] [SGN OBτi] []").
        { rewrite /obls_τi'. rewrite decide_True.
          { iFrame "#∗". }
          apply locale_step_step_fork_exact in STEP. rewrite STEP.
          rewrite -FIN Heqsf. set_solver. }
        { iIntros (? (?&?)). set_solver. }
        iFrame "OBLS".          

        iDestruct ("PHS" with "[$PHτi]") as "[PHS PHτi]".
        iFrame "PHS".

        iFrame (S'_LE). 
          
        (* pr is reestablished differently depending on whether we reach ii.
           TODO: try to unify it *)
        apply Nat.le_lteq in LEN as [LT | <-].
        ** iClear "PHτi". 
           iSpecialize ("CPS" with "[$CPP]"); [done| ].
           iFrame "CPS".

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

           iPoseProof (get_call_wp ai with "[] [$] [$]") as "WP".
           { done. }
           { iDestruct "INV" as "[??]". done. }

           destruct FIT.
           rewrite trace_lookup_last in fic_call. 
           2: { simpl in *. lia. }
           simpl in fic_call. red in fic_call.

           subst τ. apply step_fork_hl in STEP as [[? ->] | (?&->&?)].
           { simpl. by rewrite FIN H0 in Heqsf. }
           rewrite FIN H0 in Heqsf. inversion Heqsf. clear Heqsf. 

           rewrite app_comm_cons app_assoc. 
           iApply wptp_from_gen_app. iSplitL "WPS_PRE".
           { (** just drop the pwp for the newly forked τi *)
             iDestruct (wptp_from_gen_app' with "[$]") as "[WPS _]".
             { rewrite EQ_Φs. rewrite !length_app. simpl in *.
               (* lia.  - ??? *)
               f_equal.
               { by symmetry. }
               f_equal. by symmetry. }
             simpl. iApply (wptp_wfree_upd_other with "[$]").
             rewrite locales_of_list_from_indexes.
             intros (?&?&->&?)%elem_of_lookup_imap.
             rewrite /locale_of /= in H2. rewrite -H2 in H1.
             apply lookup_lt_Some in H1.
             rewrite !length_app /= in H1. lia. }

           rewrite /newposts.
           rewrite newelems_app_drop.
           2: { rewrite !length_app. simpl. lia. }
           simpl. iApply wptp_gen_singleton. rewrite /thread_pr.
           rewrite decide_True.
           2: { rewrite -H2. rewrite /locale_of !length_app. done. }
           rewrite leb_correct_conv.
           2: { simpl in *. lia. }
           simpl.

           red in fic_call. rewrite ic_helper /= in fic_call.
           rewrite /τi /= in H2. 
           rewrite /τi -H2 /= in fic_call. 
           rewrite app_comm_cons app_assoc in fic_call. 
           assert (locale_of (t1 ++ e :: t2) x = locale_of (t1 ++ e' :: t2) x) as RR. 
           { rewrite /locale_of !length_app. done. }
           rewrite /= RR in fic_call. 
           rewrite /from_locale from_locale_from_locale_of in fic_call.
           inversion fic_call. subst x. clear fic_call.
           rewrite under_ctx_fill. simpl. rewrite H2.
           iApply (wp_stuck_mono with "[$]"). done.

      * rewrite FIN in Heqsf.
        rewrite -Heqsf. 
        rewrite decide_False; [| done]. iDestruct "MOD" as "(-> & OBτi)".

        iAssert (let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
                 obls τ ∅ ∗
                 from_option (λ τ', obls τ' ∅) ⌜ True ⌝ sf ∗
                 from_option (λ τ', ∃ π'0, th_phase_eq τ' π'0) ⌜ True ⌝ sf)%I with "[MOD']" as "(OB & OB' & PH')".
        { destruct sf; simpl. 
          - iDestruct "MOD'" as (?) "(?&?&?)". iFrame.
          - by iFrame. } 
             
        iSpecialize ("OBLS" with "OB OBτi [OB']").
        { iIntros (? [EQ ?]).
          by rewrite Heqsf -FIN EQ /=. }
            
        iFrame "OBLS".
        iFrame (S'_LE). 

        rewrite FIN -Heqsf.
        iDestruct ("PHS" with "[$]") as "[PHS PHτi]". iFrame "PHS". 

        (* pr is reestablished differently depending on whether we reach ii.
           TODO: try to unify it *)
        (* TODO: the case analysis above is very similar to this one *)
        apply Nat.le_lteq in LEN as [LT | <-].
        ** iClear "PHτi". 
           iSpecialize ("CPS" with "[$CPP]"); [done| ].
           iFrame "CPS".

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

           iPoseProof (get_call_wp ai with "[] [$] [$]") as "WP".
           { done. }
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
           { subst τ. eapply τi_not_in; eauto.
             by rewrite FIN -Heqsf. }

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
      iAssert (extra_fuel ic (F ai) (etr :tr[ Some τ ]: (t1 ++ e' :: t2 ++ efs, σ'))) as "CPS'".
      { rewrite /extra_fuel. rewrite leb_correct_conv; [done| ].
        simpl. lia. }
        
      iDestruct (cur_obls_sigs_other_step with "[$]") as "(OB & OBτi & OBLS)".
      { by rewrite FIN. }
      { set_solver. }
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
        iApply (MU_burn_cp _ _ _ _ (fun (R1 R2: gset SignalId) => (⌜ R1 = ∅ /\ R2 = ∅⌝ ∗ (obls_τi ic))%I) with "[-]").
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
      iFrame (S'_LE). 

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
        (* TODO: make a lemma and use it above *)
        rewrite !prefixes_from_app.
        eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
        simpl. by constructor. }
          
      (* TODO: Make a lemma *)
      iApply (big_sepL2_impl with "[$]").
      iModIntro. 
      iIntros (i pfi Φi PFith Φith).
      rewrite /thread_pr.
      erewrite (proj2 (leb_eq_equiv _ _ _ _)).
      { by iIntros "$". }
      simpl in *. lia. 
  Qed.
  
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
  Proof using VALID FIN Pai.
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
    rewrite /pr_pr_wfree. iDestruct "PR" as "(WPS & ? & ? & OBS & %S'_LE)".
    iMod (wptp_wfre_not_stuck with "TI WPS") as "(TI & WPS & %NSTUCK')"; eauto.
    { econstructor; eauto. }
    { erewrite app_nil_r. red. simpl. apply surjective_pairing. }
    iMod (reestablish_wfree_inv with "[] [$OBS $TI $WPS]") as "(#INV'&?&?&?)"; eauto.
    { econstructor; eauto. } 
    { iDestruct "INV" as "[??]". done. }
    
    iModIntro. iFrame. iFrame (S'_LE). iSplit; [| done].
    iPureIntro. intros. by apply NSTUCK'.
  Qed.

  End TakeStep.

  Program Definition PR_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}:
    @ProgressResource heap_lang M Σ (@iem_invGS _ _ _ _ _ Hinv)
      state_interp wfree_trace_inv

      (* fork_post *)
      (fun _ _ =>
         let _ := IEM_irisG HeapLangEM EM in
         ⌜ True ⌝%I: iProp Σ) (* because upon forks we only obtain pwp .. { True } *)

      (fits_inf_call ic m ai) :=
    {| pr_pr := pr_pr_wfree |}.
  Next Obligation.
    intros.
    iIntros "PR SI".
    iPoseProof (wptp_wfree_posts with "PR") as "W"; [done| ].
    iMod (pre_step_elim with "SI W") as "(SI & POSTS & CLOS)". 
    by iFrame. 
  Qed.
  Next Obligation.
    (* iApply @wptp_wfree_not_stuck. *)
    iIntros "**".
    iMod (wptp_wfree_not_stuck with "[$] [$]") as "foo"; eauto. 
  Qed.
  Final Obligation.
    intros ??? etr Φs c oτ c' mtr VALID FIN STEP.
    iIntros "_ TI #INV PR %FIT". (* cwp is not needed*)
    iApply (wptp_wfree_take_step with "[$] [$] [$]"); eauto.  
  Qed.

End WaitFreePR.
