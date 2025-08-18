From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
(* From lawyer.examples Require Import orders_lib obls_tactics. *)
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context om_wfree_inst wptp_gen pwp.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From lawyer Require Import action_model sub_action_em.
From heap_lang Require Import lang.


Close Scope Z.


(* TODO: move *)
Lemma phases_update_phases πs δ:
  ps_phases (update_phases πs δ) = πs.
Proof using. by destruct δ. Qed.


(* TODO: move, generalize *)
Lemma set_seq_uniq2 s l1 l2:
  (set_seq s l1: gset nat) = set_seq s l2 <-> l1 = l2.
Proof using.
  split; [| congruence]. 
  intros EQ. rewrite set_eq in EQ.
  repeat setoid_rewrite elem_of_set_seq in EQ.
  destruct (Nat.lt_trichotomy l1 l2) as [LT | [? | LT]]; try done.
  - specialize (EQ (s + l1)). lia.
  - specialize (EQ (s + l2)). lia.
Qed.


Section WaitFreePR.

  (* Let OP := LocaleOP (OPRE := OPP_WF) (Locale := locale heap_lang).  *)
  Let OP := om_hl_OP (OP_HL := OP_HL_WF). 
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  (* Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ _ => obls τ ∅ (oGS := aGS)). *)
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} _ _ => ⌜ True ⌝%I).

  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let Ki := tctx_ctx ic.
  Let τi := tctx_tid ic.

  Context `(WFS: WaitFreeSpec m).
  Let F := wfs_F _ WFS. 
  
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

  (* TODO: move *)
  Lemma phase_le_init π: phase_le π0 π.
  Proof using.
    red. rewrite /π0. apply suffix_nil.
  Qed.

  Lemma get_call_wp {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (a: val) π:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    cp_mul π0 d0 F -∗ th_phase_frag τi π (1 / 2)%Qp -∗ WP m a @ τi {{ _, ⌜ True ⌝ }}.
  Proof using.
    simpl. iIntros "CPS PH".
    pose proof (@wfs_spec _ WFS _ EM Σ OHE) as SPEC. 
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
    ⌜ no_extra_obls (trace_last extr) (trace_last omtr) ⌝.

  (* TODO: move *)
  Definition under_ctx (K: ectx heap_lang) (e: expr): option expr.
  Admitted.

  Lemma under_ctx_spec K e e':
    under_ctx K e = Some e' <-> ectx_fill K e' = e.
  Proof using. Admitted.

  Lemma under_ctx_fill K e:
    under_ctx K (ectx_fill K e) = Some e.
  Proof using. Admitted. 

  Definition runs_call (ec: expr) (c: cfg heap_lang): Prop :=
    exists e, from_locale c.1 τi = Some e /\ under_ctx Ki e = Some ec /\ to_val ec = None.

  Context (ai: val). 

  Definition fits_inf_call (etr: execution_trace heap_lang): Prop :=
    from_option (runs_call (m ai)) True (etr !! ii) /\
    forall j, ii <= j -> from_option (fun c => exists ec, runs_call ec c) True (etr !! j).

  Lemma fits_inf_call_last_or_short etr
    (FITS: fits_inf_call etr):
    (exists ec, runs_call ec (trace_last etr)) \/ trace_length etr <= ii. 
  Proof using.
    edestruct Nat.lt_ge_cases as [LT| ]; [| by eauto].
    red in FITS. apply proj2 in FITS. red in LT.
    ospecialize * (FITS (trace_length etr - 1)).
    { lia. }
    rewrite trace_lookup_last in FITS.
    2: { lia. }
    simpl in FITS. by left.
  Qed.

  Lemma fits_inf_call_prev etr τ c
    (FITS: fits_inf_call (etr :tr[τ]: c)):
    fits_inf_call etr.
  Proof using.
    assert (forall j cj, etr !! j = Some cj -> (etr :tr[ τ ]: c) !! j = Some cj) as LOOKUP.
    { intros. simpl.
      rewrite trace_lookup_extend_lt; [done| ]. 
      by apply trace_lookup_lt_Some. }
    red.
    destruct FITS as [II FITS]. split.
    { destruct (etr !! ii) eqn:ITH; rewrite ITH; [| done].
      apply LOOKUP in ITH.
      by rewrite ITH in II. }
    intros ? LE.
    specialize (FITS _ LE).
    destruct (etr !! j) eqn:JTH; rewrite JTH; [| by eauto]. simpl.
    apply LOOKUP in JTH.
    by rewrite JTH in FITS. 
  Qed.

  Definition wp_tc {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness) (e: expr) (b: bool) Φ :=
    if b then
      let _ := iris_OM_into_Looping (EM := EM) in
      pwp s ⊤ τi e Φ
    else
      let e' := default (Val #false) (under_ctx Ki e) in
      (* from now on, we forget about the original postcondition *)
      wp s ⊤ τi e' (fun _ => ⌜ True ⌝%I).

  Definition thread_pr {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} s N :=
    (fun e τ Φ => if decide (τi = τ) then wp_tc s e (N <=? ii) Φ
                 else let _ := iris_OM_into_Looping (EM := EM) in pwp s ⊤ τ e Φ).

  (* Definition wptp_wfree_ {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} *)
  (*   (s: stuckness) *)
  (*   (* (tp: list expr) *) *)
  (*   (etr: execution_trace heap_lang) *)
  (*   (Φs : list (val → iPropI Σ)): *)
  (*   iProp Σ := *)
  (*   wptp_gen (thread_pr s (trace_length etr)) (trace_last etr).1 Φs. *)

  Definition wptp_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness)
    (* (tp: list expr) *)
    (etr: execution_trace heap_lang)
    (Φs : list (val → iPropI Σ)):
    iProp Σ :=
    wptp_gen (thread_pr s (trace_length etr)) (trace_last etr).1 Φs.

  (* TODO: move; isn't it already proven somewhere? *)
  Lemma not_stuck_fill (ec: expr) K σ
    (NS: not_stuck ec σ)
    (NV: to_val ec = None):
  not_stuck (fill K ec) σ.
  Proof using.
    destruct NS as [VAL | RED]. 
    { simpl in VAL. rewrite NV in VAL. red in VAL. set_solver. }
    red. right. eapply reducible_fill; eauto.
  Qed.

  Lemma runs_call_helper t1 t2 e ec σ
    (EQ: τi = locale_of t1 e)
    (RUNS: runs_call ec (t1 ++ e :: t2, σ)):
    under_ctx Ki e = Some ec /\ to_val ec = None.
  Proof using.
    red in RUNS. destruct RUNS as (e_ & TIth & CUR & NVAL).
    simpl in TIth.
    pose proof (from_locale_from_Some [] (t1 ++ e :: t2) t1 e) as X.
    ospecialize (X _).
    { apply prefixes_from_spec. eauto. }
    simpl in X. rewrite EQ /from_locale in TIth. 
    rewrite TIth in X. inversion X. subst. eauto.
  Qed.

  (* Lemma from_locale_from_locale_tp t1 t2 τ e: *)
  (*   from_locale t1 τ = Some e <-> locale_of t1 e = τ /\ e *)
  (* Proof using. *)
  (*   rewrite /from_locale. rewrite /locale_of. *)
  (*   rewrite /from_locale_from. *)
  (*   [] tp ?Goal0 = Some e0 *)

  Lemma wptp_wfre_not_stuck {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    ex atr σ tp trest s Φs :
    (* Forall2 (λ '(t, e) '(t', e'), locale_of t e = locale_of t' e') (prefixes t0) (prefixes t0') -> *)
    valid_exec ex →
    trace_ends_in ex (tp ++ trest, σ) →
    state_interp ex atr -∗ wptp_wfree s ex Φs ={⊤}=∗
    state_interp ex atr ∗ wptp_wfree s ex Φs ∗
    ⌜∀ e, e ∈ tp → s = NotStuck → not_stuck e (trace_last ex).2⌝.
  Proof.
    iIntros (Hexvalid Hex) "HSI Ht".
    rewrite assoc.
    (* iDestruct (wptp_from_same_locales t0' with "Ht") as "Ht"; first done. *)
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
        by iDestruct "HSI" as "(?&?&?)". }
      simpl. by rewrite Hex.
    - assert (fits_inf_call ex) as FITS.
      { admit. }
      apply fits_inf_call_last_or_short in FITS as [(ec & FITS) | SHORT].
      2: { apply Nat.leb_gt in LEN. 
           exfalso. clear -LEN SHORT.
           (* TODO: why lia doesn't work? *)
           by apply Nat.lt_nge in LEN. }
      rewrite Hex in FITS.

      eapply runs_call_helper in FITS; eauto. destruct FITS as (CUR & NVAL).

      rewrite CUR.
      pose proof CUR as <-%under_ctx_spec. 
      iSimpl in "W". 
      iMod (wp_not_stuck _ _ Ki with "[$] W") as "(_ & _ & %NS)";
      [done|  | .. ].
      { erewrite (proj1 (under_ctx_spec _ _ _)); eauto. }
      { done. }      
      iPureIntro. simpl in *. intros.
      specialize (NS ltac:(done)).
      rewrite Hex in NS. simpl in NS.
      eapply not_stuck_fill; eauto.
    - 
      iMod (wp_not_stuck _ _ ectx_emp with "[HSI] W") as "(_ & _ & %NS)";
      [done| rewrite ectx_fill_emp // | .. ].
      { done. }
      { simpl. rewrite /phys_SI. simpl.
        by iDestruct "HSI" as "(?&?&?)". }
      simpl. by rewrite Hex in NS.
    (* TODO: get rid of this? *)
    Unshelve. all: by apply trace_singleton. 
  Admitted.

  Definition extra_fuel `{!ObligationsGS Σ} (etr: execution_trace heap_lang) :=
    let len := trace_length etr in
    if len <=? ii then (cp_mul π0 d0 (S ii - len) ∗ cp_mul π0 d0 F)%I else ⌜ True ⌝%I.

  Definition cur_phases `{!ObligationsGS Σ} (etr: execution_trace heap_lang): iProp Σ :=
    let c := trace_last etr in
    (* ([∗ map] τ' ↦ π' ∈ delete τ (ps_phases δ), th_phase_eq τ' π') ∗ *)
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

  (* Lemma foo {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}: ObligationsGS Σ. *)
  (*   apply Hinv. *)
  (*   Show Proof.  *)
  (*   apply _.  *)
  
  Definition pr_pr_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness) (etr: execution_trace heap_lang) (Φs: list (val → iProp Σ)): iProp Σ :=
    let oGS: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    wptp_wfree s etr Φs ∗ extra_fuel etr ∗ cur_phases etr ∗ cur_obls_sigs etr. 

(*   Definition obls_wfree_ti `{!ObligationsGS Σ} *)
(*     (etr: execution_trace Λ) (omtr: auxiliary_trace OM): iProp Σ := *)
(*     obls_ti etr omtr ∗ extra_fuel omtr ∗ cur_phases omtr ∗ cur_obls_sigs omtr. *)

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
          @gen_heap_interp loc loc_eq_decision loc_countable val Σ
            (@heap_gen_heapGS Σ (@iem_phys heap_lang _ HeapLangEM EM Σ Hinv))
            (heap σ') ∗
          @obls_asem_mti _ _ _ WF_SB OP
            Nat.inhabited Σ
            (@iem_fairnessGS heap_lang _ HeapLangEM EM Σ Hinv)
            (etr :tr[ @Some nat τi]: (t1 ++ @fill _ Ki x :: t2 ++ efs, σ'))
            (mtr :tr[ ℓ ]: δ') -∗
  ⌜efs = [] /\ locales_of_cfg (trace_last etr) = locales_of_cfg (t1 ++ @fill _ Ki x :: t2 ++ efs, σ')⌝.
  Proof using.
    clear m WFS F.
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

  (* Lemma prefixes_from_ith_length (t: list expr) pf i *)
  (*   (ITH: prefixes_from t0 t !! i = Some pf): *)
  (*   length pf.1 = i.  *)
  (* Proof using. *)

  Lemma reestablish_wfree_inv {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr mtr:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    cur_obls_sigs etr -∗ state_interp etr mtr -∗ wfree_trace_inv etr mtr.
  Proof using.
    simpl. iIntros "OB TI".
    clear. 
    rewrite /wfree_trace_inv. simpl.
    rewrite /no_extra_obls. simpl.
    iDestruct "TI" as "(_&_&MSI)". rewrite /obls_asem_mti. simpl.
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
    2: { apply leb_complete in LE. simpl in LE.
         clear -LE.
         (* TODO: why lia doesn't solve it as is? *)
         remember (trace_length etr).
         rewrite -Heqn in LE. lia. }
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
    clear m WFS F.
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

  Lemma MU_burn_cp_fork {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} τ π0 d τ' R' Q:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ BOU ∅ WF_SB (∃ R0, cp π0 d ∗ th_phase_eq τ π0 ∗ obls τ R0 ∗ Q R0) -∗
      let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
      @MU__f _ EM Σ hGS ⊤ τ τ'
        (∃ π π' R0, th_phase_eq τ π ∗ th_phase_eq τ' π' ∗ obls τ (R0 ∖ R') ∗ obls τ' (R0 ∩ R') ∗ Q R0).
  Proof using.
    simpl. iIntros "BOU".
    iApply AMU_lift_top; [(try rewrite nclose_nroot); done| ].
    iApply (BOU_AMU__f'_strong _ _ _ _ Q). iApply (BOU_weaken with "[] [$]"); try done. 
    iIntros "(%R0 & CP & PH & OB & Q)".
    iFrame. 
    iIntros "(%&%&%&?&?&?&?&?&?)".
    iFrame. 
  Qed.

  Lemma MU_burn_cp {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} τ π0 d R' oτ' Q:
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
    ⊢ BOU ∅ WF_SB (∃ R0, cp π0 d ∗ th_phase_eq τ π0 ∗ obls τ R0 ∗ Q R0) -∗
      let hGS: @heapGS Σ M EM := {| heap_iemgs := Hinv |} in
      @MU_impl _ EM Σ hGS oτ' ⊤ τ
        (∃ π R0, th_phase_eq τ π ∗ Q R0 ∗
         from_option (fun τ' => ∃ π', th_phase_eq τ' π' ∗ obls τ (R0 ∖ R') ∗ obls τ' (R0 ∩ R')) (obls τ R0) oτ').
  Proof using.
    simpl. iIntros "BOU".
    destruct oτ'.
    - iPoseProof (MU_burn_cp_fork with "[$]") as "foo".
      iApply (MU__f_wand with "[] [$]"). simpl.
      iIntros "(%&%&%&?&?&?&?&?)". by iFrame.
    - simpl.
      iApply (MU_wand with "[-BOU]").
      2: { iApply MU_burn_cp_nofork. iMod "BOU".
           rewrite -!bi.sep_exist_l. 
           iModIntro. iFrame. }
      iIntros "[$ X]". by iDestruct "X" as "(%&$&?)". 
  Qed.

  (* TODO: move *)
  Lemma locales_of_cfg_step c1 τ c2
    (STEP: locale_step c1 (Some τ) c2):
  τ ∈ locales_of_cfg c1.
  Proof using.
    apply locale_step_from_locale_src in STEP.
    eapply locales_of_cfg_Some; eauto.
    Unshelve. apply inhabitant. 
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


  (* Lemma cur_phases_τi_step `{!ObligationsGS Σ} etr c' *)
  (*   (STEP: locale_step (trace_last etr) (Some τi) c'): *)
  (*   cur_phases etr -∗ *)
  (*   let oτ' := step_fork (trace_last etr) c' in *)
  (*   let ph ex := ∃ π, th_phase_frag τi π (if (trace_length ex <=? ii) then 1%Qp else (/2)%Qp) in *)
  (*   let etr' := etr :tr[ Some τi ]: c' in *)
  (*   ph etr ∗ (ph etr' -∗ from_option (fun τ' => ∃ π', th_phase_eq τ' π') ⌜ True ⌝ oτ' -∗ cur_phases etr' ∗ (⌜ trace_length etr = ii ⌝ → ∃ π, th_phase_frag τi π (/2)%Qp)). *)
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

  (* TODO: move, refactor? *)
  Lemma newelems_app_drop {A: Type} (t1 t1' t2: list A)
    (LEN: length t1' = length t1)
    :
    newelems t1 (t1' ++ t2) = t2.
  Proof using.
    rewrite /newelems. by list_simplifier.
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

  (* TODO: any simpler way? *)
  (* TODO: move *)
  Lemma half_inv2: (/2)%Qp = (1/2)%Qp.
  Proof using. 
    apply (Qp.mul_inj_r 2%Qp).
    by rewrite Qp.mul_div_r Qp.mul_inv_r.
  Qed.

  Lemma fic_has_τi etr
    (FITS : fits_inf_call etr)
    (LEN: ii < trace_length etr):
    τi ∈ locales_of_cfg (trace_last etr).
  Proof using.
    red in FITS. 
    destruct FITS as [_ NEXT].
    ospecialize (NEXT (trace_length etr - 1) _).
    { lia. }
    rewrite trace_lookup_last in NEXT.
    2: { lia. }
    simpl in NEXT. rewrite /runs_call in NEXT.
    destruct NEXT as (?&?&IN&?).
    eapply locales_of_cfg_Some; eauto.
    Unshelve. exact inhabitant.
  Qed.

  (* TODO: refactor *)
  Lemma cur_phases_other_step `{!ObligationsGS Σ} etr c' τ
    (STEP: locale_step (trace_last etr) (Some τ) c')
    (etr' := etr :tr[ Some τi ]: c')
    (FITS: fits_inf_call etr')
    (OTHER: τ ≠ τi):
    cur_phases etr -∗
    let oτ' := step_fork (trace_last etr) c' in
    let ph := ∃ π, th_phase_eq τ π in
    ph ∗ (ph -∗ from_option (fun τ' => ∃ π', th_phase_eq τ' π') ⌜ True ⌝ oτ' -∗
          cur_phases etr' ∗
          (⌜ trace_length etr = ii ⌝ → ∃ π, th_phase_frag τi π (/2)%Qp)).
  Proof using.
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
         - apply proj1 in FITS. subst etr'.
           rewrite trace_lookup_last in FITS.
           2: { simpl in *. lia. }
           simpl in FITS.
           iSpecialize ("PHτi" with "[]").
           { iPureIntro. red in FITS. destruct FITS as (?&IN&_).
             pose proof STEP as EQ%locale_step_step_fork_exact.
             rewrite SF /= union_empty_r_L in EQ. rewrite -EQ. 
             eapply locales_of_cfg_Some; eauto. }
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
        apply fic_has_τi in H. 
        2: { eapply fits_inf_call_prev; eauto. }
        apply step_fork_difference in SF. set_solver. }

    simpl. rewrite difference_disjoint_L.
    2: { set_solver. }
    rewrite big_opS_singleton. iFrame "PH'".

    destruct (decide (trace_length etr = ii)).
    - apply proj1 in FITS. subst etr'.
      rewrite trace_lookup_last in FITS.
      2: { simpl in *. lia. }
      simpl in FITS.
      iSpecialize ("PHτi" with "[]").
      { iPureIntro. red in FITS. destruct FITS as (?&IN&_).
        pose proof STEP as EQ%locale_step_step_fork_exact.
        rewrite SF /= in EQ. 
        apply mk_is_Some in IN.
        eapply locales_of_cfg_Some in IN.
        rewrite <- surjective_pairing in IN.
        rewrite EQ in IN. set_solver. }
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
   Unshelve. exact inhabitant. 
  Qed.

  Lemma obls_τi'_next `{!ObligationsGS Σ} c c'
    (SAME: locales_of_cfg c' = locales_of_cfg c):
    obls_τi' c ⊣⊢ obls_τi' c'.
  Proof using.
    rewrite /obls_τi'. by rewrite SAME.
  Qed.

  Program Definition PR_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}:
    @ProgressResource heap_lang M Σ (@iem_invGS _ _ _ _ _ Hinv)
      state_interp wfree_trace_inv

      (* fork_post *)
      (fun _ _ =>
         let _ := IEM_irisG HeapLangEM EM in
         ⌜ True ⌝%I: iProp Σ) (* because upon forks we only obtain pwp .. { True } *)

      fits_inf_call :=
    {| pr_pr := pr_pr_wfree |}.
  Next Obligation.
    intros.
    iUnfold pr_pr_wfree.
    iIntros "(WPS & CPS & PH & OB)".

    iAssert (pre_step top top (Ps ∗ (Ps -∗ wptp_wfree s ex Φs)) (irisG0 := {|
      iris_invGS :=
        @iem_invGS heap_lang
          (AM2M
             (@ObligationsAM (@sigO natO (λ i : nat, i < 2)) unitO
                (locale heap_lang) WF_SB OP Nat.inhabited))
          HeapLangEM EM Σ Hinv;
      state_interp :=
        @state_interp heap_lang M Σ (@IEM_irisG heap_lang M HeapLangEM EM Σ Hinv);
      fork_post := λ (_ : locale heap_lang) (_ : language.val heap_lang), True        
    |}))%I with "[WPS]" as "CLOS".
    2: { iMod "CLOS". iModIntro. by iFrame. }
    rewrite /wptp_wfree.
    iDestruct (big_sepL2_length with "[$]") as "%LENS".
    rewrite adequacy_utils.prefixes_from_length in LENS.
(*    (* split thread pool into three parts, 
       "frame" the outer two using wptp_of_val_post,
       prove the remaining wp/pwp part for τi *) *)
    (* now it's trivial, due to True postconditions? *)
    admit.
  Admitted.
  Next Obligation.
    iIntros "* %VALID %END SI PR".
    rewrite /pr_pr_wfree. iDestruct "PR" as "(WPS &X&Y&Z)".
    iFrame "X Y Z".
    (* TODO: we can probably weaken this obligation,
       since t0 is never used? *)
    assert (t0 = []) as -> by admit. simpl in END.
    iApply (wptp_wfre_not_stuck with "[$] [$]"); eauto.
  Admitted. 
  Final Obligation.
    intros ??? etr Φs c oτ c' mtr VALID FIN STEP.
    (* Set Printing Implicit. *)
    iIntros "_ TI #INV PR %FIT". (* cwp is not needed*)

    (* our PR instance in fact implies this not-stuck property *)
    (* TODO: ? move this property to definition of PR? *)
    iAssert (|={⊤,∅}=>
               |={∅}▷=>^(S (trace_length etr))
                 |={∅,⊤}=>
                 ∃ (δ' : M) (ℓ : mlabel M),
               state_interp (etr :tr[ oτ ]: c') (mtr :tr[ ℓ ]: δ') ∗
               (* wfree_trace_inv (etr :tr[ oτ ]: c') (mtr :tr[ ℓ ]: δ') ∗ *)
               pr_pr_wfree s (etr :tr[ oτ ]: c') (Φs ++ newposts c.1 c'.1))%I
        with "[-]" as "X".
    2: { iMod "X". iModIntro.
         iApply (step_fupdN_wand with "X").
         iIntros "X". iMod "X" as (??) "(TI & PR)".
         rewrite /pr_pr_wfree. iDestruct "PR" as "(WPS & ? & ? & OBS)".
         iMod (wptp_wfre_not_stuck with "TI WPS") as "(TI & WPS & %NSTUCK')"; eauto.
         { econstructor; eauto. }
         { erewrite app_nil_r. red. simpl. apply surjective_pairing. }
         iDestruct (reestablish_wfree_inv with "[$] [$]") as "#INV'". 
         iModIntro. iFrame. iSplit; [| done].
         iPureIntro. intros. by apply NSTUCK'. }

    simpl.
    (* rewrite /obls_asem_mti. *)
    (* iDestruct "TI" as "(%EV & PHYS & MSI)". *)
    inversion STEP as
        [?? e σ e' σ' efs t1 t2 -> -> PSTEP | ].
    2: { done. }
    simpl in *. 
    destruct oτ as [τ| ]; [| done]. inversion H0. clear H0.
    rewrite H3 in STEP, FIT. rewrite H3.

    rewrite /pr_pr_wfree. iDestruct "PR" as "(WPS & CPS & PH & OB)".

    iUnfold wptp_wfree in "WPS".

    (* iDestruct (wptp_from_gen_upd_2 _ *)
    
    (* iDestruct (wptp_from_gen_take_2 _ _ _ _ τ with "WPS") as "WPS". *)
    (* { rewrite FIN. simpl. rewrite -H3. *)
    (*   rewrite locales_of_list_locales. *)
    (*   eapply elem_of_fmap. eexists (_, _). split; eauto. *)
    (*   apply prefixes_from_spec. eauto. } *)

    (* simpl. iDestruct "WPS" as (Φ e_) "(%Φ_IN & %FIN_ & WP & WPS)". *)
    (* rewrite FIN in FIN_. rewrite -H3 /= in FIN_. *)
    (* rewrite from_locale_from_locale_of in FIN_. inversion FIN_. subst e_. clear FIN_. *)

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

    iEval (rewrite /thread_pr) in "WP".
    destruct decide.
    - subst τ.
      rewrite /wp_tc.

      (* iDestruct (cur_phases_take _ τi with "PH") as "(%π & PH & PHS)". *)
      (* { eapply locales_of_cfg_Some. *)
      (*   rewrite FIN. rewrite e0. *)
      (*   by apply locale_step_from_locale_src in STEP. } *)
      iDestruct (cur_phases_τi_step with "[$]") as "(PH & PHS)".
      { by rewrite e0 FIN. }
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
        { by rewrite e0 FIN. }

        rewrite {1}/obls_τi. iDestruct "OB" as "(%si & OB & SGN & EP)".

        iDestruct (@pwp_MU_ctx_take_step _ _ _ Hinv with "TI [CP PH OB] WP") as "STEP".
        1-2: by eauto. 
        { red. rewrite FIN. erewrite ectx_fill_emp. reflexivity. }
        { done. }
        { rewrite (cp_weaken _ π); [| by apply phase_le_init].
          iApply (MU_burn_cp _ _ _ ∅ _ (fun R => (⌜ R = {[ si ]} ⌝)%I) with "[$CP $PH OB]").
          iModIntro. iFrame. done. }
          
        iMod "STEP". iModIntro.
        iMod "STEP". iModIntro. iNext. 
        iMod "STEP". iModIntro.
        iApply (step_fupdN_wand with "[STEP]"); first by iApply "STEP".
        iIntros "STEP".
        iMod "STEP" as (δ' ℓ) "(HSI & He2 & WPS' & MOD) /=".

        iDestruct "MOD" as (π' ?) "(PH & -> & MOD')".
        rewrite difference_empty_L intersection_empty_r_L.

        iAssert (@state_interp _ M _ _ (etr :tr[ Some τi ]: (t1 ++ e' :: t2 ++ efs, σ')) _)%I with "[HSI]" as "TI".
        { simpl. iDestruct "HSI" as "(?&?&?)". iFrame. }

        (* iSpecialize ("OBLS" with "[OB SGN EP]"); [by iFrame| ]. *)

        iModIntro.
        do 2 iExists _.
        (* rewrite bi.sep_comm. rewrite -bi.sep_assoc. *)
        iSplitL "TI".
        { simpl. rewrite e0. iFrame. }

        (* iAssert (wp_tc s e' (S (trace_length etr) <=? ii) Φ -∗ *)
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
      fork_post := λ (_ : locale heap_lang) (_ : language.val heap_lang), True        
    |})))%I with "[WPS1 WPS2 WPS']" as "WPS". 
        { iIntros "WP".
          rewrite app_comm_cons app_assoc.
          iApply wptp_from_gen_app. iSplitR "WPS'".
          2: { simpl. rewrite /newposts.
               rewrite newelems_app_drop.
               2: { rewrite !length_app. simpl. lia. }

               apply step_fork_hl in STEP as [[? ->] | (?&->&?)].
               - simpl. set_solver.
               - rewrite wptp_gen_singleton. rewrite /thread_pr.
                 rewrite decide_False.
                 2: { intros ->. rewrite /locale_of in e0.
                      rewrite !length_app in e0. simpl in e0. lia. }
                 rewrite big_sepL_singleton. simpl.
                 rewrite app_nil_r.
                 replace (locale_of (t1 ++ e' :: t2) x) with (locale_of (t1 ++ e :: t2) x); [done| ].
                 rewrite /locale_of. rewrite !length_app. simpl. lia. } 
          
          rewrite -EQ. iApply wptp_from_gen_app. iSplitL "WPS1".
          { iApply (big_sepL2_impl with "[$]").
            iModIntro. iIntros (i pfi Φi PFith Φith).
            rewrite /thread_pr.
            destruct decide.
            2: { set_solver. }

            rewrite e1 in e0.
            simpl in e0.
            rewrite /locale_of in e0.

            pose proof PFith as ?%prefixes_from_ith_length.
            simpl in H0. rewrite H0 in e0. subst.
            apply lookup_lt_Some in PFith.
            rewrite adequacy_utils.prefixes_from_length in PFith. lia. }

          simpl. rewrite -EQ'. iApply wptp_from_gen_cons.
          iSplitL "WP".
          2: { erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [e'])).
               2: { rewrite !prefixes_from_app.
                    eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
                    simpl. by constructor. }
               iApply (big_sepL2_impl with "[$]").
               iModIntro. iIntros (i pfi Φi PFith Φith).
               rewrite /thread_pr.
               destruct decide.
               2: { set_solver. }
               
               rewrite e1 in e0.
               simpl in e0.
               rewrite /locale_of in e0.
               
               pose proof PFith as ?%prefixes_from_ith_length.
               simpl in H0. rewrite H0 in e0. subst.
               apply lookup_lt_Some in PFith.
               rewrite adequacy_utils.prefixes_from_length in PFith.
               rewrite !length_app /= in e0. lia. }
               
          rewrite /thread_pr. rewrite decide_True.
          2: { rewrite e0. done. }
          
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
          rewrite leb_correct; [| simpl in *; lia].
          iSpecialize ("PHS" with "[PH]"); [by eauto| ].
                    
          iAssert (cur_phases (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')) ∗
                     cur_obls_sigs (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')))%I with "[-]" as "[PHS OBS]".
          { destruct step_fork eqn:SF; simpl. 
            - iDestruct "MOD'" as (?) "(PH' & OB & OB')".
              rewrite e0. iSplitL "PH' PHS".
              + iApply "PHS". eauto.
              + iApply ("OBLS" with "[-OB'] [$]"). iFrame.
                by rewrite e0.
            - iSplitL "PHS".
              + by iApply "PHS".
              + iApply ("OBLS" with "[-] [//]"). by iFrame. }
          iFrame.
        * iClear "He2".
          iDestruct (th_phase_frag_halve with "PH") as "[PH PH']". 
          iSpecialize ("WPS" with "[CPP PH']").
          { rewrite /wp_tc. rewrite leb_correct_conv.
            2: { simpl. lia. }
            iPoseProof (get_call_wp with "[$] [$]") as "WP".
            red in FIT. apply proj1 in FIT.
            rewrite trace_lookup_extend in FIT; [| done].
            simpl in FIT. red in FIT.
            destruct FIT as (e_ & CUR_ & CTX & ?).
            rewrite e0 /= in CUR_.
            replace (locale_of t1 e) with (locale_of t1 e') in CUR_.
            2: { done. }
            rewrite /from_locale from_locale_from_locale_of in CUR_.
            inversion CUR_. subst e_. clear CUR_.
            rewrite CTX. simpl.
            iApply (wp_stuck_mono with "[$]"). done. }

          iFrame "WPS".
          iSpecialize ("CPS" with "[]").
          { iIntros (?). lia. }
          iFrame "CPS".
          rewrite leb_correct_conv; [| lia].
          iSpecialize ("PHS" with "[PH]").
          { rewrite half_inv2. iFrame. }

          iAssert (cur_phases (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')) ∗
                     cur_obls_sigs (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')))%I with "[-]" as "[PHS OBS]".
          { destruct step_fork eqn:SF; simpl. 
            - iDestruct "MOD'" as (?) "(PH' & OB & OB')".
              rewrite e0. iSplitL "PH' PHS".
              + iApply "PHS". eauto.
              + iApply ("OBLS" with "[-OB'] [$]"). iFrame. by rewrite e0. 
            - iSplitL "PHS".
              + by iApply "PHS".
              + iApply ("OBLS" with "[-] [//]"). iFrame. }
          iFrame.            
      + apply Nat.leb_gt in LEN. 
        apply fits_inf_call_prev in FIT.
        apply fits_inf_call_last_or_short in FIT as [(ec & FIT) | SHORT].
        2: { simpl in SHORT. lia. }
        rewrite FIN in FIT. eapply runs_call_helper in FIT; eauto.
        destruct FIT as (CUR & NVAL).

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
        { rewrite leb_correct_conv; [| lia]. eauto. }

        iAssert (wptp_wfree s (etr :tr[ Some τi ]: (t1 ++ fill Ki x :: t2, σ')) Φs)%I with "[WPS1 WPS2 He2]" as "WPS". 
        {
          rewrite /wptp_wfree. 
          rewrite -EQ. iApply wptp_from_gen_app. iSplitL "WPS1".
          { simpl.
            rewrite /wptp_from_gen.
            iApply (big_sepL2_impl with "[$]").
            iModIntro. iIntros (i pfi Φi PFith Φith).
            rewrite /thread_pr.
            destruct decide.
            2: { set_solver. }
            rewrite leb_correct_conv; [| lia].
            rewrite leb_correct_conv; [| lia].
            set_solver. }
          simpl. rewrite -EQ'.
          iApply (wptp_from_gen_app _ _ [_] [_]).
          iSplitL "He2".
          { simpl. iApply wptp_gen_singleton.
            rewrite /thread_pr. rewrite decide_True; [| done].
            rewrite /wp_tc. rewrite leb_correct_conv.
            2: { lia. }
            rewrite under_ctx_fill. rewrite e0. done. }
          (* TODO: make a lemma, use it above too *)
          { simpl.
            erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [fill Ki x])).
            2: { rewrite !prefixes_from_app.
                 eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
                 simpl. by constructor. }
            rewrite /wptp_from_gen.
            iApply (big_sepL2_impl with "[$]").
            iModIntro. iIntros (i pfi Φi PFith Φith).
            rewrite /thread_pr.
            destruct decide.
            2: { set_solver. }
            rewrite e1 in e0.
            simpl in e0.
            rewrite /locale_of in e0.

            pose proof PFith as ?%prefixes_from_ith_length.
            rewrite length_app in H3. simpl in H3. lia. }
        }
        
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
        rewrite e0. do 2 iExists _.
        by iFrame.
    - (* other threads' steps *)
      destruct (trace_length etr <=? ii) eqn:LEN.
      + apply Nat.leb_le in LEN.
        simpl.

        iDestruct (split_trace_fuel with "[$]") as "(CP & CPP & CPS)"; [done| ].
        iDestruct (cur_obls_sigs_other_step with "[$]") as "(OB & OBτi & OBLS)".
        { by rewrite FIN. }
        { congruence. }
        iDestruct (cur_phases_other_step with "[$]") as "(PH & PHS)"; eauto.
        { rewrite FIN. subst τ. eauto. }
        iDestruct "PH" as (π) "PH". rewrite H3. 

        remember (step_fork (trace_last etr) (t1 ++ e' :: t2 ++ efs, σ')) as sf.
        (* rewrite -Heqsf. *)

        iDestruct (@pwp_MU_ctx_take_step _ _ _ Hinv with "TI [CP PH OB OBτi] WP") as "STEP".
        1-2: by eauto.
        { red. rewrite FIN. erewrite ectx_fill_emp. reflexivity. }
        { done. }
        { rewrite -Heqsf. 
          rewrite (cp_weaken _ π); [| by apply phase_le_init].
          rewrite /obls_τi' /obls_τi. 

          set (upd := fun (R: gset SignalId) => let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
                        if (decide (sf = Some τi))
                        then (∃ s, ⌜ R = {[ s ]} ⌝ ∗ sgn s l0 (Some false) ∗ ep s π0 d0)%I
                        else (⌜ R = ∅ ⌝ ∗ obls_τi' (t1 ++ e' :: t2 ++ efs, σ'))%I). 
          iApply (MU_burn_cp _ _ _ ⊤ _ upd with "[-]").
          iFrame "CP PH". subst upd. simpl.
          rewrite -FIN in STEP.
          destruct sf; simpl. 
          2: { iFrame. iModIntro. iSplit; [done| ].
               iApply obls_τi'_next; [| done].
               apply locale_step_step_fork_exact in STEP.
               rewrite -Heqsf in STEP. set_solver. }
          destruct (decide (l = τi)) as [-> | NEQ].
          - rewrite decide_False.
            2: { eapply locale_step_fork_Some in STEP; eauto. tauto. }
            iMod (OU_create_sig with "[$]") as "(%sg & SGN & OB & _)".
            { rewrite /WF_SB. lia. }
            iDestruct (sgn_get_ex with "[$]") as "(SGN & #SGN0)". 
            iMod (create_ep_upd with "[OBτi] SGN0") as "(#EP & _)".
            { apply (orders_lib.ith_bn_lt 2 0 1). lia. }
            { iFrame. }
            iModIntro. iExists _. rewrite decide_True; [| done].
            iFrame. iSplit; [iPureIntro; set_solver| ].
            iApply "EP". 
          - iModIntro. iFrame. rewrite (@decide_False _ (_ = _)); [| congruence].
            iSplit; [done| ].
            (* TODO: refactor *)
            rewrite /obls_τi'.
            apply locale_step_step_fork_exact in STEP. rewrite STEP.
            erewrite decide_ext; [by iFrame| ].
            rewrite -Heqsf. simpl. set_solver. }

        iMod "STEP". iModIntro.
        iMod "STEP". iModIntro. iNext. 
        iMod "STEP". iModIntro.
        iApply (step_fupdN_wand with "[STEP]"); first by iApply "STEP".
        iIntros "STEP".
        iMod "STEP" as (δ' ℓ) "(HSI & He2 & WPS' & MOD) /=".

        iDestruct "MOD" as (π' R) "(PH & MOD & MOD')".

        iAssert (@state_interp _ M _ _ (etr :tr[ Some τ ]: (t1 ++ e' :: t2 ++ efs, σ')) _)%I with "[HSI]" as "TI".
        { simpl. iDestruct "HSI" as "(?&?&?)". iFrame. }

        iSpecialize ("PHS" with "[$PH]"). 
        (* iSpecialize ("OBLS" with "[$]"). *)

        iModIntro.
        do 2 iExists _.
        iFrame "TI".

        (** first close the wptp for the _current_ trace length *)
        iAssert (wptp_gen (thread_pr s (trace_length etr)) (t1 ++ e' :: t2 ++ efs) (Φs ++ newposts (t1 ++ e :: t2) (t1 ++ e' :: t2 ++ efs)))%I with "[WPS1 WPS2 WPS' He2]" as "WPS_PRE". 
        { 
          rewrite app_comm_cons app_assoc.
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
          
          rewrite -EQ. iApply wptp_from_gen_app. iFrame "WPS1". 

          simpl. rewrite -EQ'. iApply wptp_from_gen_cons.          
          iSplitL "He2".
          2: { erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [e'])).
               2: { rewrite !prefixes_from_app.
                    eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
                    simpl. by constructor. }
               done. }
               
          rewrite /thread_pr.
          rewrite /wp_tc. rewrite leb_correct; [| done].
          subst τ. 
          destruct decide as [-> | ?]; done. }

        destruct (decide (sf = Some τi)) as [-> | NO].
        * simpl. symmetry in Heqsf.   
        
        
        (* pr is reestablished differently depending on whether we reach ii.
           TODO: try to unify it *)
        apply Nat.le_lteq in LEN as [LT | <-].
        * iSpecialize ("CPS" with "[$CPP]"); [done| ].
          iFrame "CPS".  
          iSpecialize ("WPS" with "[He2]").
          { rewrite /wp_tc. rewrite leb_correct.
            2: { simpl in *. lia. }
            done. }
          
          iFrame "CPS WPS".
          rewrite leb_correct; [| simpl in *; lia].
          iSpecialize ("PHS" with "[PH]"); [by eauto| ].
                    
          iAssert (cur_phases (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')) ∗
                     cur_obls_sigs (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')))%I with "[-]" as "[PHS OBS]".
          { destruct step_fork eqn:SF; simpl. 
            - iDestruct "MOD'" as (?) "(PH' & OB')".
              rewrite e0. iSplitL "PH' PHS".
              + iApply "PHS". eauto.
              + iApply "OBLS". eauto.
            - iSplitL "PHS".
              + by iApply "PHS".
              + by iApply "OBLS". }
          iFrame.
        * iClear "He2".
          iDestruct (th_phase_frag_halve with "PH") as "[PH PH']". 
          iSpecialize ("WPS" with "[CPP PH']").
          { rewrite /wp_tc. rewrite leb_correct_conv.
            2: { simpl. lia. }
            iPoseProof (get_call_wp with "[$] [$]") as "WP".
            red in FIT. apply proj1 in FIT.
            rewrite trace_lookup_extend in FIT; [| done].
            simpl in FIT. red in FIT.
            destruct FIT as (e_ & CUR_ & CTX & ?).
            rewrite e0 /= in CUR_.
            replace (locale_of t1 e) with (locale_of t1 e') in CUR_.
            2: { done. }
            rewrite /from_locale from_locale_from_locale_of in CUR_.
            inversion CUR_. subst e_. clear CUR_.
            rewrite CTX. simpl.
            iApply (wp_stuck_mono with "[$]"). done. }

          iFrame "WPS".
          iSpecialize ("CPS" with "[]").
          { iIntros (?). lia. }
          iFrame "CPS".
          rewrite leb_correct_conv; [| lia].
          iSpecialize ("PHS" with "[PH]").
          { iExists _.
            replace (/ 2)%Qp with (1 / 2)%Qp; try done.
            (* TODO: any simpler way? *)
            apply (Qp.mul_inj_r 2%Qp).
            by rewrite Qp.mul_div_r Qp.mul_inv_r. }

          iAssert (cur_phases (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')) ∗
                     cur_obls_sigs (etr :tr[ Some (locale_of t1 e) ]: (t1 ++ e' :: t2 ++ efs, σ')))%I with "[-]" as "[PHS OBS]".
          { destruct step_fork eqn:SF; simpl. 
            - iDestruct "MOD'" as (?) "(PH' & OB')".
              rewrite e0. iSplitL "PH' PHS".
              + iApply "PHS". eauto.
              + iApply "OBLS". eauto.
            - iSplitL "PHS".
              + by iApply "PHS".
              + by iApply "OBLS". }
          iFrame.            
      + apply Nat.leb_gt in LEN. 
        apply fits_inf_call_prev in FIT.
        apply fits_inf_call_last_or_short in FIT as [(ec & FIT) | SHORT].
        2: { simpl in SHORT. lia. }
        rewrite FIN in FIT. eapply runs_call_helper in FIT; eauto.
        destruct FIT as (CUR & NVAL).

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
        { rewrite leb_correct_conv; [| lia]. eauto. }

        iAssert (wptp_wfree s (etr :tr[ Some τi ]: (t1 ++ fill Ki x :: t2, σ')) Φs)%I with "[WPS1 WPS2 He2]" as "WPS". 
        {
          rewrite /wptp_wfree. 
          rewrite -EQ. iApply wptp_from_gen_app. iSplitL "WPS1".
          { simpl.
            rewrite /wptp_from_gen.
            iApply (big_sepL2_impl with "[$]").
            iModIntro. iIntros (i pfi Φi PFith Φith).
            rewrite /thread_pr.
            destruct decide.
            2: { set_solver. }
            rewrite leb_correct_conv; [| lia].
            rewrite leb_correct_conv; [| lia].
            set_solver. }
          simpl. rewrite -EQ'.
          iApply (wptp_from_gen_app _ _ [_] [_]).
          iSplitL "He2".
          { simpl. iApply wptp_gen_singleton.
            rewrite /thread_pr. rewrite decide_True; [| done].
            rewrite /wp_tc. rewrite leb_correct_conv.
            2: { lia. }
            rewrite under_ctx_fill. rewrite e0. done. }
          (* TODO: make a lemma, use it above too *)
          { simpl.
            erewrite wptp_from_gen_locales_equiv_1 with (t0' := (t1 ++ [fill Ki x])).
            2: { rewrite !prefixes_from_app.
                 eapply Forall2_app; [apply adequacy_utils.locales_equiv_refl| ].
                 simpl. by constructor. }
            rewrite /wptp_from_gen.
            iApply (big_sepL2_impl with "[$]").
            iModIntro. iIntros (i pfi Φi PFith Φith).
            rewrite /thread_pr.
            destruct decide.
            2: { set_solver. }
            rewrite e1 in e0.
            simpl in e0.
            rewrite /locale_of in e0.

            pose proof PFith as ?%prefixes_from_ith_length.
            rewrite length_app in H3. simpl in H3. lia. }
        }
        
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
        rewrite e0. do 2 iExists _.
        by iFrame.


  Admitted. 
  
End WaitFreePR.
