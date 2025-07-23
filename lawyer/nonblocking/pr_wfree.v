From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From fairness Require Import fairness locales_helpers.
From lawyer Require Import program_logic sub_action_em action_model.
(* From lawyer.examples Require Import orders_lib obls_tactics. *)
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am.
From heap_lang Require Import lang.
From lawyer.nonblocking Require Import trace_context om_wfree_inst.


Close Scope Z.


Section Pwp.

  Definition LoopingModel: Model :=
    {| mstate := unit; mlabel := unit; mtrans := fun _ _ _ => True |}.

  (* Class LoopIrisG {Λ: language} Σ := { *)
  (*   lig_inner :: irisG Λ LoopingModel Σ *)
  (* }. *)

  (* Definition pwp {Λ: language} {Σ: gFunctors} := @wp Λ (iProp Σ) LoopingModel. *)
  (* Definition pwp := @wp (A := LoopingModel). *)
  (* Definition pwp {Λ: language} {PROP} := @wp Λ PROP LoopingModel. *)
  (* Global Arguments pwp {_ _ _}.  wp *)
  Definition pwp `{!irisG Λ LoopingModel Σ} :=
    @wp Λ (iProp Σ) stuckness _. 

End Pwp. 


Section WaitFreePR.

  Let OP := LocaleOP (OPRE := OPP_WF) (Locale := locale heap_lang). 
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} τ _ => obls τ ∅ (oGS := aGS)).

  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let Ki := tctx_ctx ic.
  Let τi := tctx_tid ic.

  Context (m: val).
  Context (F: nat). (** amount of fuel required for the call (currently at d0) *)

  Definition no_extra_obls (_: cfg heap_lang) (δ: mstate M) :=
    forall τ', default ∅ (ps_obls δ !! τ') ≠ ∅ -> τ' = τi.

  Definition obls_sim_rel_wfree extr omtr :=
    obls_sim_rel extr omtr /\ no_extra_obls (trace_last extr) (trace_last omtr).

  Definition wfree_trace_inv `{Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (extr: execution_trace heap_lang) (omtr: auxiliary_trace M): iProp Σ :=
    ⌜ no_extra_obls (trace_last extr) (trace_last omtr) ⌝.

  Definition fits_inf_call: execution_trace heap_lang → Prop.
  Admitted.

  Definition phys_SI {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (etr: execution_trace heap_lang) (_: auxiliary_trace LoopingModel): iProp Σ :=
    lgem_si (trace_last etr).2 (lgem_GS0 := (iem_phys HeapLangEM EM)).

  Section WptpGen.
    Context {Σ: gFunctors}.
    Context (W: expr -> locale heap_lang -> (val → iPropI Σ) -> iProp Σ).
    
    (* TODO: move *)
    Definition wptp_from_gen 
      (t0 t: list expr) (Φs : list (val → iPropI Σ)) :=
      ([∗ list] tp1_e;Φ ∈ (prefixes_from t0 t);Φs,
         W tp1_e.2 (locale_of tp1_e.1 tp1_e.2) Φ)%I.

    Lemma wptp_from_gen_app' t0 t1 Φs1 t2 Φs2
      (MATCH1: length t1 = length Φs1):
      wptp_from_gen t0 (t1 ++ t2) (Φs1 ++ Φs2) ⊢ wptp_from_gen t0 t1 Φs1 ∗ wptp_from_gen (t0 ++ t1) t2 Φs2. 
    Proof using.
      iIntros.
      rewrite {1}/wptp_from_gen. rewrite prefixes_from_app. 
      iDestruct (big_sepL2_app_inv with "[$]") as "(?&?)".
      2: { iFrame. }
      rewrite prefixes_from_length. tauto.  
    Qed.

    Lemma wptp_gen_split_1 t0 t1 t2 Φs:
      wptp_from_gen t0 (t1 ++ t2) Φs ⊢
      ⌜ exists Φs1 Φs2, Φs1 ++ Φs2 = Φs /\ length Φs1 = length t1 /\ length Φs2 = length t2 ⌝.
    Proof using.
      clear. 
      iIntros "WPS".
      iDestruct (big_sepL2_length with "[$]") as "%LENS".
      rewrite adequacy_utils.prefixes_from_length in LENS.
      iPureIntro.
      do 2 eexists. split.
      { apply (take_drop (length t1)). }
      rewrite length_take. rewrite length_skipn.
      rewrite length_app in LENS. lia.
    Qed.

    Lemma wptp_gen_singleton t0 e Φ:
      wptp_from_gen t0 [e] [Φ] ⊣⊢ W e (locale_of t0 e) Φ. 
    Proof using.
      rewrite /wptp_from_gen. simpl.
      by rewrite bi.sep_emp.
    Qed.

  End WptpGen.

  Definition wptp_gen {Σ} W t Φs := (@wptp_from_gen Σ W [] t Φs).

  (** not making it an instance to avoid incorrect Iris instantiations *)
  Definition iris_OM_into_Looping {Σ} (Hinv: @IEMGS _ _ HeapLangEM EM Σ):
    irisG heap_lang LoopingModel Σ.
  Proof using.
    exact {| state_interp := phys_SI; fork_post := fun _ _ => (⌜ True ⌝)%I |}.
  Defined.

  (* TODO: move *)
  Definition under_ctx (K: ectx heap_lang) (e: expr): option expr.
  Admitted.

  Lemma under_ctx_spec K e e':
    under_ctx K e = Some e' <-> ectx_fill K e' = e.
  Proof using. Admitted.

  (* Definition empty_post {Σ: gFunctors}: val -> iProp Σ := (fun _ => ⌜ True ⌝%I).  *)

  Definition wp_tc {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness) (e: expr) (b: bool) Φ :=
    if b then
      let e' := default (Val #false) (under_ctx Ki e) in
      wp s ⊤ τi e' Φ
    else
      let _ := iris_OM_into_Looping in
      pwp s ⊤ τi e Φ.

  Definition thread_pr {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} s N :=
    (fun e τ Φ => if decide (τi = τ) then wp_tc s e (ii <? N) Φ
                 else let _ := iris_OM_into_Looping in pwp s ⊤ τ e Φ).

  Definition wptp_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness)
    (* (tp: list expr) *)
    (etr: execution_trace heap_lang)
    (Φs : list (val → iPropI Σ)):
    iProp Σ :=
    wptp_gen (thread_pr s (trace_length etr)) (trace_last etr).1 Φs.

  Open Scope WFR_scope. 

  Definition extra_fuel `{!ObligationsGS Σ} (etr: execution_trace heap_lang) :=
    let len := trace_length etr in
    if len <? ii then (cp_mul π0 d0 (ii - len) ∗ cp_mul π0 d0 F)%I else ⌜ True ⌝%I.

  Definition cur_phases `{!ObligationsGS Σ} (etr: execution_trace heap_lang): iProp Σ :=
    let c := trace_last etr in
    (* ([∗ map] τ' ↦ π' ∈ delete τ (ps_phases δ), th_phase_eq τ' π') ∗ *)
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, ∃ π, th_phase_eq τ π) ∗
    let ph_res := let q := if (trace_length etr <? ii) then 1%Qp else (/2)%Qp in
                  (∃ π, th_phase_frag τi π q)%I in
    ⌜ τi ∈ locales_of_cfg c ⌝ → ph_res.

  Definition cur_obls_sigs `{!ObligationsGS Σ} (etr: execution_trace heap_lang): iProp Σ :=
    let c := trace_last etr in
    ([∗ set] τ ∈ locales_of_cfg c ∖ {[ τi ]}, obls τ ∅) ∗
    if decide (τi ∈ locales_of_cfg c)
    then (∃ s, obls τi {[ s ]} ∗ sgn s l0 (Some false) ∗ ep s π0 d0)%I
    else cp π0 d1.

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

  Program Definition PR_wfree {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}:
    @ProgressResource heap_lang M Σ (@iem_invGS _ _ _ _ _ Hinv)
      state_interp wfree_trace_inv fork_post fits_inf_call :=
    {| pr_pr := pr_pr_wfree |}.
  Next Obligation.
    intros.
    (* rewrite /pr_pr_wfree. *)
    iUnfold pr_pr_wfree.
    iIntros "(WPS & CPS & PH & OB)".
    iAssert (|~~| (Ps ∗ (Ps -∗ wptp_wfree s ex Φs)))%I with "[WPS]" as "CLOS".
    2: { iMod "CLOS". iModIntro. by iFrame. }
    rewrite /wptp_wfree.
    iDestruct (big_sepL2_length with "[$]") as "%LENS".
    rewrite adequacy_utils.prefixes_from_length in LENS.
    (* split thread pool into three parts, 
       "frame" the outer two using wptp_of_val_post,
       prove the remaining wp/pwp part for τi *)
    admit.
  Admitted.
  Next Obligation.
  Admitted. 
  Final Obligation.
    intros ??? etr Φs c oτ c' mtr VALID FIN STEP.
    iIntros "#CWP TI #INV PR %FIT".
    simpl. rewrite /obls_asem_mti. iDestruct "TI" as "(%EV & PHYS & MSI)".
    inversion STEP as
        [?? e σ e' σ' efs t1 t2 -> -> PSTEP | ].
    2: { done. }
    simpl in *. 
    destruct oτ as [τ| ]; [| done]. inversion H0. clear H0.
    rewrite H3 in STEP, FIT. rewrite H3.

    rewrite /pr_pr_wfree. iDestruct "PR" as "(WPS & CPS & PH & OB)".
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
    iDestruct (wptp_from_gen_app' with "WPS'") as "[WPS_ WPS2] /="; [done| ].
    destruct Φ_ as [ | Φ [|]].
    1, 3: simpl in LEN_; lia.
    rewrite wptp_gen_singleton.

    
    
  
  Admitted. 
  
End WaitFreePR.
