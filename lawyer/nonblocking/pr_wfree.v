From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
(* From lawyer.examples Require Import orders_lib obls_tactics. *)
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context om_wfree_inst.
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


  (* TODO: move *)
  Definition under_ctx (K: ectx heap_lang) (e: expr): option expr.
  Admitted.

  Lemma under_ctx_spec K e e':
    under_ctx K e = Some e' <-> ectx_fill K e' = e.
  Proof using. Admitted.

  Lemma under_ctx_fill K e:
    under_ctx K (ectx_fill K e) = Some e.
  Proof using. Admitted. 

  Definition runs_call (c: cfg heap_lang): Prop :=
    exists e ec, from_locale c.1 τi = Some e /\ under_ctx Ki e = Some ec /\ to_val ec = None. 

  Definition fits_inf_call (etr: execution_trace heap_lang): Prop :=
    forall j, ii <= j -> from_option runs_call True (etr !! j).

  Lemma fits_inf_call_last_or_short etr
    (FITS: fits_inf_call etr):
    runs_call (trace_last etr) \/ trace_length etr <= ii. 
  Proof using.
    edestruct Nat.lt_ge_cases as [LT| ]; [| by eauto].
    red in FITS. red in LT.
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
    red. intros ? LE.
    red in FITS. specialize (FITS _ LE).
    destruct (etr !! j) eqn:JTH; rewrite JTH; [| done]. simpl.
    rewrite trace_lookup_extend_lt in FITS.
    2: { by apply trace_lookup_lt_Some. }
    by rewrite JTH in FITS.
  Qed.    
  
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

    Lemma wptp_from_gen_app t0 t1 Φs1 t2 Φs2:
      wptp_from_gen t0 t1 Φs1 ∗ wptp_from_gen (t0 ++ t1) t2 Φs2 ⊢
      wptp_from_gen t0 (t1 ++ t2) (Φs1 ++ Φs2). 
    Proof using.
      iIntros "[WPS1 WPS2]".
      rewrite {3}/wptp_from_gen. rewrite prefixes_from_app.
      iDestruct (big_sepL2_length with "WPS1") as "%".
      iApply big_sepL2_app_same_length; [tauto| ].
      iFrame. 
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

    Lemma new_threads_wptp_from_gen `{!irisG heap_lang M Σ} t efs:
      ([∗ list] i ↦ ef ∈ efs, 
         W ef (locale_of (t ++ take i efs) ef) (fork_post (locale_of (t ++ take i efs) ef))
       )
         ⊣⊢ wptp_from_gen t efs (newposts t (t ++ efs)).
    Proof.
      rewrite  /wptp_from_gen. 
      rewrite big_sepL2_alt; iSplit.
      - iIntros "H". iSplit.
        { rewrite /newposts. rewrite map_length.
          rewrite /newelems. rewrite drop_app_length // map_length !prefixes_from_length //. }
        iInduction efs as [|ef efs] "IH" forall (t); first done.
        rewrite /newposts /newelems.
        rewrite /= !drop_app_length //=.
        iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
        replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                   (prefixes_from (t ++ [ef]) efs))
          with (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
        + iApply "IH". iApply (big_sepL_impl with "H").
          iIntros "!>" (k e Hin) "H". by list_simplifier.
        + list_simplifier.
          replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
          rewrite /newposts /newelems.
          rewrite drop_app_length //.
      - iIntros "[_ H]".
        iInduction efs as [|ef efs] "IH" forall (t); first done.
        rewrite /newposts /newelems.
        rewrite /= !drop_app_length //=.
        iDestruct "H" as "[H1 H]". rewrite (right_id [] (++)). iFrame.
        replace (map (λ '(tnew, e), fork_post (locale_of tnew e))
                   (prefixes_from (t ++ [ef]) efs))
          with (newposts (t ++[ef]) ((t ++ [ef]) ++ efs)).
        + iSpecialize ("IH" with "H"). iApply (big_sepL_impl with "IH").
          iIntros "!>" (k e Hin) "H". by list_simplifier.
        + list_simplifier.
          replace (t ++ ef :: efs) with ((t ++ [ef]) ++ efs); last by list_simplifier.
          rewrite /newposts /newelems.
          rewrite drop_app_length //.
  Qed.

  Lemma wptp_from_gen_cons t0 e efs Φ Φs:
    wptp_from_gen t0 (e :: efs) (Φ :: Φs) ⊣⊢ W e (locale_of t0 e) Φ ∗ wptp_from_gen (t0 ++ [e]) efs Φs.
  Proof using. done. Qed. 

  (* TODO: do we need anything stronger (e.g. matching indices for e and Φ) ? *)
  Lemma wptp_from_gen_take_1 t efs Φs e
    (IN: e ∈ efs):
    let WPS := wptp_from_gen t efs Φs in
    WPS ⊣⊢ ∃ Φ t1 t2, let τ := locale_of (t ++ t1) e in
       ⌜ Φ ∈ Φs ⌝ ∗ ⌜ efs = t1 ++ e :: t2 ⌝ ∗ W e τ Φ ∗ (W e τ Φ -∗ WPS).
  Proof using.
    clear F. clear dependent ic.
    simpl. iSplit. 
    2: { iIntros "(%&%&%&?&?&?&CLOS)". by iApply "CLOS". }
    iIntros "WPS".
    apply elem_of_list_split in IN as (?&?&->).
    iDestruct (wptp_gen_split_1 with "[$]") as %(?&?&<-&?&?).
    iDestruct (wptp_from_gen_app' with "[$]") as "[? WPS]"; eauto.
    destruct x2; [done| ].
    rewrite wptp_from_gen_cons. iDestruct "WPS" as "[WP ?]".
    do 3 iExists _. iSplit; [| iSplit].
    2: { eauto. }
    2: iFrame.
    { iPureIntro. set_solver. } 
    iIntros "WP".
    iApply wptp_from_gen_app. iFrame.
  Qed.

  (* EQUIV : locales_equiv t0 t0' *)

  (* Lemma wptp_from_gen_locales_equiv_1_impl t0 t0' efs efs' Φs *)
  (*   (EQUIV: locales_equiv_from t0 t0' efs efs'): *)
  (*   wptp_from_gen t0 efs Φs -∗ wptp_from_gen t0' efs' Φs. *)
  (* Proof using. *)
  (*   iIntros "WPS".  *)
  (*   (* rewrite /wptp_from_gen. *) *)
  (*   (* iApply big_sepL2_proper_2. *) *)
  (*   (* 4: by iFrame.  *) *)
  (*   clear -EQUIV. *)
  (*   Unset Printing Notations. *)
    
  (*   Disable Notation locales_equiv.  *)
  (*   eapply EQUIV.  *)
    
    
  Lemma wptp_from_gen_locales_equiv_1 t0 t0' efs Φs
    (EQUIV: locales_equiv t0 t0'):
    wptp_from_gen t0 efs Φs ⊣⊢ wptp_from_gen t0' efs Φs.
  Proof using.
    generalize dependent Φs. generalize dependent t0. generalize dependent t0'.
    induction efs.
    { intros. simpl. set_solver. }
    destruct Φs.
    { set_solver. }
    rewrite !wptp_from_gen_cons.
    iApply bi.sep_proper.
    2: { iApply IHefs.
         clear -EQUIV.
         rewrite !prefixes_from_app.
         eapply Forall2_app; try done.
         simpl. constructor; try done.
         (* TODO: specific to heap_lang, can it be generalized? *)
         rewrite /locale_of.
         eapply adequacy_utils.locales_equiv_from_length; eauto. }
    rewrite /locale_of.
    eapply adequacy_utils.locales_equiv_from_length in EQUIV; eauto.
    by rewrite EQUIV.
  Qed.

  End WptpGen.

  Definition wptp_gen {Σ} W t Φs := (@wptp_from_gen Σ W [] t Φs).

  (** not making it an instance to avoid incorrect Iris instantiations *)
  Definition iris_OM_into_Looping {Σ} (Hinv: @IEMGS _ _ HeapLangEM EM Σ):
    irisG heap_lang LoopingModel Σ.
  Proof using.
    exact {| state_interp := phys_SI; fork_post := fun _ _ => (⌜ True ⌝)%I |}.
  Defined.
  (* Definition empty_post {Σ: gFunctors}: val -> iProp Σ := (fun _ => ⌜ True ⌝%I).  *)

  Definition wp_tc {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    (s: stuckness) (e: expr) (b: bool) Φ :=
    if b then
      let _ := iris_OM_into_Looping in
      pwp s ⊤ τi e Φ
    else
      let e' := default (Val #false) (under_ctx Ki e) in
      wp s ⊤ τi e' Φ.

  Definition thread_pr {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ} s N :=
    (fun e τ Φ => if decide (τi = τ) then wp_tc s e (N <=? ii) Φ
                 else let _ := iris_OM_into_Looping in pwp s ⊤ τ e Φ).

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

  Lemma runs_call_helper t1 t2 e σ
    (EQ: τi = locale_of t1 e)
    (RUNS: runs_call (t1 ++ e :: t2, σ)):
    exists ec, under_ctx Ki e = Some ec /\ to_val ec = None.
  Proof using.
    red in RUNS. destruct RUNS as (e_ & ec & TIth & CUR & NVAL).
    simpl in TIth.
    pose proof (from_locale_from_Some [] (t1 ++ e :: t2) t1 e) as X.
    ospecialize (X _).
    { apply prefixes_from_spec. eauto. }
    simpl in X. rewrite EQ /from_locale in TIth. 
    rewrite TIth in X. inversion X. subst. eauto.
  Qed.

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
      apply fits_inf_call_last_or_short in FITS as [FITS | SHORT].
      2: { apply Nat.leb_gt in LEN. 
           exfalso. clear -LEN SHORT.
           (* TODO: why lia doesn't work? *)
           by apply Nat.lt_nge in LEN. }
      rewrite Hex in FITS.

      eapply runs_call_helper in FITS; eauto. destruct FITS as (ec & CUR & NVAL).

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

  Open Scope WFR_scope. 

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

  (* TODO: move *)
  Lemma prefixes_from_ith_length (t0 t: list expr) pf i
    (ITH: prefixes_from t0 t !! i = Some pf):
    length pf.1 = length t0 + i.
  Proof using.
    clear -ITH. 
    generalize dependent t0. generalize dependent i. generalize dependent pf.
    induction t.
    { intros. simpl. destruct t0; done. }
    intros. destruct i.
    { simpl in ITH. inversion ITH. subst. simpl. lia. }
    simpl in ITH. apply IHt in ITH.
    rewrite length_app /= in ITH. lia.
  Qed.

  Lemma prefixes_ith_length (t: list expr) pf i
    (ITH: prefixes t !! i = Some pf):
    length pf.1 = i. 
  Proof using.
    apply prefixes_from_ith_length in ITH. by rewrite ITH.
  Qed.

  Lemma reestablish_wfree_inv {Σ} {Hinv : @IEMGS _ _ HeapLangEM EM Σ}
    etr mtr
    (σ' : state)
    (t1 t2 : list expr)
    e' e''
    (δ' : AM2M ObligationsAM)
    (ℓ : mlabel (AM2M ObligationsAM)):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ Hinv in
  cur_obls_sigs (etr :tr[ Some τi ]: (t1 ++ e' :: t2, σ')) -∗
  state_interp (etr :tr[ Some τi ]: (t1 ++ e' :: t2, σ'))
           (mtr :tr[ ℓ ]: δ') -∗
  wfree_trace_inv
    (etr :tr[ Some (locale_of t1 e'')
     ]: (t1 ++ e'' :: t2, σ'))
    (mtr :tr[ ℓ ]: δ').
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
      destruct (ps_obls δ' !! τ') eqn:TT; rewrite TT in OBS; [| done]. 
      eapply elem_of_dom; eauto. }
    iDestruct (obls_msi_exact with "[$] [$]") as %NOOBS.
    by rewrite NOOBS in OBS.
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
    simpl. iIntros "PHS".
    rewrite /cur_phases.
    rewrite -EQ_CFG.    
    rewrite leb_correct_conv; [| done].
    rewrite leb_correct_conv; [done| ].
    simpl.
    remember (trace_length etr) as X. rewrite -HeqX. lia.
  Qed.

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
    - rewrite H3 in e0.
      subst τ.
      rewrite /wp_tc.
      destruct Nat.leb eqn:LEN.
      + admit.
      + 
        apply fits_inf_call_prev in FIT.
        apply fits_inf_call_last_or_short in FIT as [FIT | SHORT].
        2: { apply Nat.leb_gt in LEN. 
             clear -LEN SHORT.
             simpl in SHORT. lia. }
        rewrite FIN in FIT. eapply runs_call_helper in FIT; eauto.
        destruct FIT as (ec & CUR & NVAL).

        rewrite CUR. simpl.
        apply under_ctx_spec in CUR.

        iDestruct (cur_phases_take _ τi with "PH") as "(%π & PH & PHS)".
        { eapply locales_of_cfg_Some.
          rewrite FIN. rewrite e0.
          by apply locale_step_from_locale_src in STEP. }
        iAssert (⌜ ps_phases (trace_last mtr) !! τi = Some π ⌝)%I as "%PH".
        { iApply (th_phase_msi_frag with "[-PH] [$]").
          by iDestruct "TI" as "(?&?&(?&?&?))". }
        iAssert (⌜ obls_cfg_corr (trace_last etr) (trace_last mtr) ⌝)%I as "%CORR".
        { iDestruct "TI" as "(_&_&CORR)".
          rewrite /obls_asem_mti /obls_si.
          iDestruct "CORR" as "(_&%CORR)". done. }

        rewrite -CUR in PSTEP. eapply fill_step_inv in PSTEP as (?&?&?).
        2: done. 
        iDestruct (wp_ctx_take_step with "[TI] WP") as "He"; eauto.
        { red. rewrite FIN. rewrite -CUR. eauto. }
        { subst. done. }

        iMod "He" as "He". iModIntro.
        iMod "He" as "He". iModIntro. iNext.
        iMod "He" as "He". iModIntro.
        iApply (step_fupdN_wand with "[He]"); first by iApply "He".
        iIntros "He".
        iMod "He" as (δ' ℓ) "(HSI & He2 & Hefs) /=".

        iDestruct (same_phase_no_fork with "[$] [$]") as %(-> & EQ_CFG); eauto.

        simpl. rewrite !app_nil_r.
        iDestruct "HSI" as "(%MSTEP & HEAP & MSI)".

        iSpecialize ("PHS" with "[$]").

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
            rewrite LEN.
            rewrite leb_correct_conv; [set_solver| ].
            apply leb_complete_conv in LEN. lia. } 
          simpl. rewrite -EQ'.
          iApply (wptp_from_gen_app _ _ [_] [_]).
          iSplitL "He2".
          { simpl. iApply wptp_gen_singleton.
            rewrite /thread_pr. rewrite decide_True; [| done].
            rewrite /wp_tc. rewrite leb_correct_conv.
            2: { apply leb_complete_conv in LEN. lia. }
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

        iMod (wptp_wfre_not_stuck with "TI WPS") as "(TI & WPS & %NSTUCK')". 
        { econstructor; eauto. move STEP at bottom.
          rewrite app_nil_r in STEP. rewrite <- e0 in STEP.
          by rewrite H0 in STEP. }
        { red. simpl.
          rewrite -(app_nil_r (_ ++ _)). reflexivity. }
        simpl in NSTUCK'. rewrite -H0 in NSTUCK'.
        iApply fupd_frame_l. iSplit.
        { iPureIntro. intros. by apply NSTUCK'. }

        assert (newposts (t1 ++ ectx_fill Ki ec :: t2) (t1 ++ ectx_fill Ki x :: t2) = []) as NONEW.
        { erewrite adequacy_utils.newposts_locales_equiv.
          { apply adequacy_utils.newposts_same_empty. }
          apply locales_equiv_from_middle. done. }
        subst. rewrite NONEW. rewrite app_nil_r.

        iAssert (cur_obls_sigs (etr :tr[ Some τi ]: (t1 ++ fill Ki x :: t2, σ')))%I with "[OB]" as "OB".
        { rewrite /cur_obls_sigs. simpl.
          rewrite app_nil_r in EQ_CFG. rewrite -EQ_CFG. done. }  

        iAssert (wfree_trace_inv
          (etr :tr[ Some (locale_of t1 (ectx_fill Ki ec))
                  ]: (t1 ++ ectx_fill Ki x :: t2, σ'))
            (mtr :tr[ ℓ ]: δ'))%I with "[OB TI]" as "#INV'".
        { iApply (reestablish_wfree_inv with "[$] [$]"). }
        
        iAssert (extra_fuel
    (etr :tr[ Some (locale_of t1 (ectx_fill Ki ec))
     ]: (t1 ++ ectx_fill Ki x :: t2, σ')))%I with "[CPS]" as "CPS".
        { iApply (reestablish_fuel with "[$]"). }

        iAssert (cur_phases
          (etr :tr[ Some (locale_of t1 (ectx_fill Ki ec))
                  ]: (t1 ++ ectx_fill Ki x :: t2, σ')))%I with "[PHS]" as "PHS".
        { iApply (reestablish_phases with "[$]").
          - rewrite EQ_CFG. by rewrite app_nil_r.
          - apply Nat.leb_gt in LEN. done. }

        rewrite e0. do 2 iExists _. by iFrame "#∗".
    - 
    
  
  Admitted. 
  
End WaitFreePR.
