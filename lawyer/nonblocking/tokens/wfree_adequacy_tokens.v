From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat gmap_view.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len trace_utils. 
From trillium.program_logic Require Import execution_model weakestpre adequacy simulation_adequacy_em_cond. 
From trillium.prelude Require Import classical.
From fairness Require Import fairness locales_helpers utils.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.examples Require Import orders_lib obls_tactics.
From lawyer.nonblocking Require Import trace_context om_wfree_inst pr_wfree_lib (* pr_wfree *) wfree_traces wptp_gen pwp calls wfree_adequacy_lib pwp_ext.
(* From lawyer.nonblocking.logrel Require Import fundamental.  *)
From lawyer.nonblocking.logrel Require Import valid_client.
From lawyer.nonblocking.tokens Require Import om_wfree_inst_tokens pr_wfree_tokens tokens_ra fundamental_tok op_spec_lifting.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination.
From heap_lang Require Import lang simulation_adequacy.

Close Scope Z. 

(* TODO: use in other file *)
Definition is_fun (v: val) := exists f x b, v = RecV f x b. 


Section WFAdequacy.

  Let OP := LocaleOP (OPRE := OPP_WF) (Locale := locale heap_lang). 
  Existing Instance OP.
  Let OM := ObligationsModel.

  Let M := AM2M ObligationsAM.
  Let ASEM := ObligationsASEM.
  Let EM := TopAM_EM ASEM (fun {Σ} {aGS: asem_GS Σ} _ _ => ⌜ True ⌝%I).

  Context (ic: @trace_ctx heap_lang).
  Let ii := tctx_index ic.
  Let tpc := tctx_tpctx ic. 
  Let Ki := tpctx_ctx tpc.
  Let τi := tpctx_tid tpc. 

  Context (s': stuckness).
  
  Context `(SPEC: WaitFreeSpecToken MS).
  Context (m: val) (* (MSm: m ∈ MS) *)
  .
  (* Local Definition m: val := default #()  *)
  
  Let F := wfst_F _ SPEC.
  
  Context ((* m *) ai: val).

  Let fic := fits_inf_call ic m ai.

  (* TODO: unify with non-tokens version *)
  Definition is_init_tpool (tp: list expr) :=
    valid_init_tpool_restr tp MS /\
    (** the operation under consideration is determined by the thread id,
        acccording to how the operations are assigned in valid_init_tpool_restr *)
    elements MS !! τi = Some m /\ 
    (ii = 0 -> exists e, from_locale tp τi = Some e /\ under_ctx Ki e = Some (m ai)) /\
    (forall e, from_locale tp τi = Some e -> to_val e = None).

  Definition wfreeΣ: gFunctors := iemΣ HeapLangEM EM. 

  Instance wfree_pre: @heapGpreS wfreeΣ M EM.
  Proof. 
    unshelve esplit. 
  Qed. 

  (* TODO: move *)
  Lemma ct_init `{CallTrackerPre Σ}:
    ⊢ |==> ∃ (CT: CallTracker Σ), ct_auth None ∗ ct_frag None.
  Proof using.
    From iris.algebra Require Import excl_auth.
    iMod (own_alloc (● (Some $ Excl $ None) ⋅ ◯ _:  excl_authUR (option expr))) as "(%γ & ? & ?)".
    { by apply auth_both_valid_2. }
    iExists {| ct_γ := γ |}. by iFrame.
  Qed.

  (* TODO: move to lib and remove duplicate? *)
  Lemma rah_wfree_inv {Σ} {Hinv : IEMGS HeapLangEM EM Σ}
    c:
  ⊢ adequacy_cond.rel_always_holds_with_trace_inv MaybeStuck
    (wfree_trace_inv ic s' SPEC)
    (map (λ (_ : nat) (_ : val), True) (adequacy_utils.locales_of_list c.1))
    (obls_sim_rel_wfree ic s') c (init_om_wfree_state F ic c).
  Proof using.
    rewrite /adequacy_cond.rel_always_holds_with_trace_inv.
    
    iIntros (extr omtr [tp σ] EXTRA FIN NSTUCK).
    
    simpl. iIntros "(%VALID_STEP & HEAP & MSI & [%TH_OWN %OBLS]) POSTS #INV".
    red in EXTRA. destruct EXTRA as (VALID & EX0 & OM0 & CONT_SIM). 
    iApply fupd_mask_intro_discard; [done| ].
    
    rewrite /wfree_trace_inv. iDestruct "INV" as "((%NOOBS' & %NVAL & %PROGRESS) & _)".
    iPureIntro. 
    
    rewrite /obls_sim_rel_wfree. split; [|done].
    
    destruct extr.
    { simpl in VALID_STEP.
      inversion VALID. subst.
      red in EX0, OM0. simpl in EX0, OM0. subst.
      rewrite /obls_sim_rel_wfree /obls_sim_rel /obls_sim_rel_gen.
      simpl.
      
      split; [done| ]. simpl. red.
      red. simpl. eapply @obls_τi_enabled; eauto. }
    
    simpl in VALID_STEP. inversion VALID. subst. simpl in *.
    rewrite /obls_sim_rel.
    red. split. 
    { simpl. by destruct a. }
    simpl. rewrite /obls_st_rel.
    red. simpl.
    eapply @obls_τi_enabled; eauto.
  Qed.

  (* TODO: unify with non-tokens version if invariants are unified *)
  Lemma init_wfree_inv  {Σ} {Hinv : IEMGS HeapLangEM EM Σ} c
    (ETR0: is_init_tpool c.1)
    (MOD_INIT: wfst_is_init_st _ SPEC c)
    (M_FUN: is_fun m):
  @wfst_mod_inv _ SPEC Σ
            (@iem_phys heap_lang _ HeapLangEM EM Σ Hinv)
            (@iris_invGS heap_lang _ Σ (@IEM_irisG heap_lang _ HeapLangEM EM Σ Hinv)) -∗
  wfree_trace_inv ic s' SPEC {tr[ c ]}{tr[ init_om_wfree_state F ic c ]}.
  Proof using.
    (* clear MSm. *)
    iIntros "#INV". 
    rewrite /wfree_trace_inv. iFrame "INV". 
    iPureIntro. repeat split.
    - simpl. red. rewrite /init_om_wfree_state. simpl.
      intros τ NEMPTY. destruct decide.
      2: { rewrite lookup_gset_to_gmap option_guard_decide in NEMPTY.
           destruct decide; simpl in NEMPTY; done. }
      destruct lookup eqn:L; try done. 
      apply lookup_insert_Some in L. destruct L as [| [? L]]; [set_solver| ].
      apply lookup_gset_to_gmap_Some in L. set_solver.
    - simpl.
      destruct (from_locale c.1 τi) eqn:IN; rewrite IN; [| done].
      destruct ETR0 as (_&_&NVAL0).
      by apply NVAL0 in IN.
    - red. simpl.
      intros _ TI0.
      destruct ETR0 as (?&?&CALL0&?).
      destruct (CALL0 ltac:(lia)) as (?&?&?).           
      eapply RecV_App_not_stuck; eauto.
  Qed.

  Open Scope WFR_scope. 

  Local Lemma locale_in_helper R (tks: list val) (tp: list expr) τ e
    (TP: Forall2 R tks tp)
    (IN: tks !! τ = Some e):
    τ ∈ locales_of_list tp.
  Proof using.
    clear -TP IN. 
    rewrite locales_of_list_indexes.
    apply Forall2_length in TP.
    rewrite indexes_seq. apply elem_of_seq.
    apply lookup_lt_Some in IN. lia.
  Qed.

  (* TODO: move *)
  Lemma gmultiset_disj_union_difference_r `{Countable K} (X Y Z: gmultiset K):
    Z ⊆ Y -> (X ⊎ Y) ∖ Z = X ⊎ Y ∖ Z.
  Proof using. clear. multiset_solver. Qed.

  Lemma init_τi_pwp_ext {Σ} {PWT: @PrWfreeTok MS Σ} e
    (VALID_CL: valid_op_client m e)
    (NOFORKS: no_forks e)
    (TI: elements MS !! τi = Some m)
    (M_FUN: is_fun m):
    ⊢ □ ( (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv _ SPEC) -∗
         ct_frag None -∗ pwp_ext ic m MaybeStuck ⊤ τi e (λ _, True)).
  Proof using.
    simpl.

    red in VALID_CL. destruct VALID_CL as (e0 & -> & VALID_CL). 
    opose proof * (fundamental _ _ _ e0) as FTLR; eauto.
    { apply (cti_interp_tok_add_pres m τi). }  
    { admit. }
    Unshelve.
    2, 3: by apply PWT.
    2: exact (method_tok m).

    iStartProof. 
    iPoseProof (FTLR) as "FF".
    rewrite /logrel /interp_expr. 
    rewrite -subst_env_singleton.

    iModIntro. 
    iIntros "#INV CTF".
    rewrite /pwp_ext.

    iSpecialize ("FF" $! {["m" := m]} τi with "[] [$]").
    2: iApply (@wp_wand with "FF"); set_solver.

    rewrite -insert_empty. iApply interp_env_cons; [done| ].
    iSplitL; [| by iApply interp_env_nil].
    change (tpctx_tid (tctx_tpctx ic)) with τi.

    red in M_FUN. destruct M_FUN as (?&?&?&EQ).
    iEval (rewrite EQ). rewrite interp_unfold /=.

    iIntros (τ a).
    iPoseProof (lift_spec m ic MaybeStuck ⊤ a
                  ⌜ True ⌝ (bi_pure ∘ is_ground_val)
                 with "[]") as "LIFT". 
    { pose proof (@wfst_safety_spec _ SPEC) as SAFE.
      iPoseProof (SAFE with "[$]") as "SAFE".
      iDestruct (big_sepS_elem_of_acc _ (dom MS) m with "[$]") as "[#SPEC _]".
      { admit. }
      rewrite {3}EQ. 
      iModIntro. iIntros "TOK _".
      rewrite -EQ.
      setoid_rewrite bi.sep_comm at 2. iApply ("SPEC" with "TOK"). }
    rewrite -EQ. iIntros "!> #LRa CTF".
    (** we assume that the method doesn't use LR for its argument *)
    iClear "LRa".
    iSpecialize ("LIFT" with "[$] [//]").
    rewrite /pwp. iApply (@wp_wand with "[LIFT]").
    { replace (tpctx_tid (tctx_tpctx ic)) with τ by admit.  
      iClear "INV".
      Unset Printing Notations.
      Set Printing Implicit.
      iApply "LIFT". 
      clear. 
      Set Printing All. 
      
      
      

    

  Lemma init_wptp_wfree {Σ} {PWT: @PrWfreeTok MS Σ} c
    (ETR0: is_init_tpool c.1):
    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ (@pwt_Hinv _ _ PWT) in
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv _ SPEC) -∗
    (⌜ ii = 0 ⌝ → ∃ π, cp_mul π0 d0 F ∗ th_phase_frag τi π (/2)%Qp) -∗
    methods_toks (MS ∖ {[+ m +]}) -∗
    (⌜ ii = 0 ⌝ → method_tok m) -∗
    ct_frag None -∗
    wptp_wfree ic s' m MaybeStuck {tr[ c ]}
      (map (λ _ _, True) (adequacy_utils.locales_of_list c.1)).
  Proof using.
    simpl. iIntros "#INV T TOKS TOKm CTF".
    rewrite /wptp_wfree. simpl.
    destruct (thread_pool_split c.1 τi) as (tp1 & tp2 & tp' & EQ & TP' & NO1 & NO2).
    rewrite EQ. rewrite !locales_of_list_from_app'. rewrite !map_app /=.
    destruct ETR0 as (TP & M_TI & II0 & NVAL0).
    rewrite EQ in TP.

    red in TP. apply List.Forall2_app_inv_r in TP as (tks1 & tks2 & TP1 & TP2 & EQ_MS).

    rewrite EQ_MS in M_TI. apply lookup_app_Some in M_TI as [IN1 | [LEN1 M_TI]].
    { destruct NO1. by eapply locale_in_helper. }

    destruct TP' as [-> | (e & -> & LOC)].
    { destruct NO2. rewrite app_nil_r.
      rewrite locales_of_list_from_indexes.
      apply elem_of_lookup_imap.
      apply Nat.le_sum in LEN1 as [d ->].
      apply Forall2_length in TP1. rewrite TP1.
      simpl in *. apply Forall2_length in TP2.
      rewrite Nat.add_sub' in M_TI.
      apply lookup_lt_Some in M_TI. rewrite TP2 in M_TI.
      apply lookup_lt_is_Some_2 in M_TI as [??].
      eauto. }
    simpl in TP2.
    apply Forall2_cons_inv_r in TP2 as (m_ & tks2_ & MTI & TP2 & ->).
    assert (m_ = m) as ->.
    { apply Forall2_length in TP1. rewrite TP1 in M_TI.
      rewrite LOC Nat.sub_diag /= in M_TI. congruence. }
    clear M_TI.

    iEval (rewrite -{3}(list_to_set_disj_elements MS)) in "TOKS".
    rewrite EQ_MS list_to_set_disj_app.
    rewrite gmultiset_disj_union_difference_r.
    2: multiset_solver.
    iDestruct (methods_toks_split with "TOKS") as "[TOKS1 TOKS]". 
   
    iApply wptp_from_gen_app. iSplitL "TOKS1".
    {
      (* iApply init_wptp_wfree_pwps. *)
      (* - done. *)
      (* - by apply Forall_app, proj1 in TP. *)
      (* - done. *)
      admit. 
    }

    simpl. rewrite gmultiset_cancel_l2.
    iApply wptp_from_gen_cons. iSplitR "TOKS".
    2: {
         (* iApply init_wptp_wfree_pwps. *)
         (* - done. *)
         (* - by do 2 (apply Forall_app, proj2 in TP). *)
         (* - done. *)
      admit. 
    }
       
    rewrite /thread_pr. rewrite decide_True; [| done].
    rewrite /wp_tc.
    destruct ii eqn:TI.
    2: { 
         rewrite leb_correct; [| lia].
         (* apply Forall_app, proj2 in TP. *)
         (* apply Forall_app, proj1 in TP. *)
         (* inversion TP as [| ?? (? & -> & ?)]. subst. *)
         (* by iApply init_pwp. *)
      (** get pwp_ext with SI extended with ct_frag token *)
      admit. 
    }

    (** get Trillium wp immediately *)
    rewrite leb_correct_conv; [| lia].
    iDestruct ("T" with "[//]") as (π) "[CPS PH]".
    iSpecialize ("TOKm" with "[//]"). 
    rewrite half_inv2.
    unshelve iPoseProof (get_call_wp ic SPEC m _ ai with "[$] [$] [$] [$]") as "WP".
    { apply gmultiset_elem_of_elements. rewrite EQ_MS. set_solver. }
    destruct (II0 eq_refl) as (e_ & IN & CTX).
    rewrite LOC EQ /= in IN.
    rewrite /from_locale in IN. rewrite from_locale_from_locale_of in IN.
    inversion IN. subst e_.
    rewrite CTX. simpl.
    iApply (wp_stuck_mono with "[$]"). done.
  Admitted.

  Lemma init_pr_pr_wfree {Σ} {PWT: @PrWfreeTok MS Σ}
    c
    (ETR0: is_init_tpool c.1):
  (let _: heap1GS Σ := iem_phys HeapLangEM EM in wfst_mod_inv _ SPEC) -∗
  @obls_init_resource _ _ _ _ _ _
            (@iem_fairnessGS heap_lang _ HeapLangEM EM Σ (@pwt_Hinv _ _ PWT))
            (init_om_wfree_state F ic c) () -∗
  methods_toks MS -∗
  ct_auth None -∗ ct_frag None -∗
  pr_pr_wfree ic s' SPEC m MaybeStuck {tr[ c ]}
    (map (λ _ _, True) (adequacy_utils.locales_of_list c.1)).
  Proof using.
    iIntros "#INV MOD TOKS CTA CTF".
    rewrite /pr_pr_wfree. simpl.

    iDestruct (init_wfree_resources_weak with "[$]") as "(CPS & OB' & OBLS & PHS)".
    iFrame.
    
    rewrite -{2}(difference_union_intersection_L (locales_of_cfg c) {[ τi ]}).    
    rewrite big_sepS_union.
    2: { set_solver. }
    iDestruct "PHS" as "[$ PH]".
    #[local] Arguments Nat.leb _ _ : simpl nomatch.
    rewrite /extra_fuel. simpl.
    iDestruct "CPS" as "(CPS_PRE & CPS0 & CP1)".
    iDestruct (cp_mul_split with "CPS_PRE") as "[CPS_PRE CPS_PRE']". rewrite Nat.add_0_r.
    rewrite Nat.sub_0_r. fold ii.
    rewrite bi.sep_comm. rewrite -bi.sep_assoc. iSplitL "CPS0 CPS_PRE".
    { destruct leb; [| done]. iFrame. }
    rewrite /obls_τi'.

    rewrite -bi.sep_assoc. 
    iAssert (_%I ∗ (⌜ ii = 0 ⌝ →
                    let _: ObligationsGS Σ := @iem_fairnessGS _ _ _ _ _ (@pwt_Hinv _ _ PWT) in
                    ∃ π, th_phase_frag τi π (/ 2)%Qp))%I with "[PH]" as "[X PHτi]".
    2: iSplitL "X"; [by iApply "X"| ].
    { destruct (decide (τi ∈ locales_of_cfg c)).
      2: { iSplitL.
           - by iIntros (?).
           - iIntros (II0). destruct ETR0 as (?&?&IN&?).
             destruct (IN II0) as (?&E&?). destruct n.
             eapply locales_of_cfg_Some; eauto.
             Unshelve. apply c. }
      rewrite intersection_comm_L subseteq_intersection_1_L.
      2: set_solver.
      rewrite big_sepS_singleton.
      fold τi.
      destruct ii eqn:II.
      - rewrite leb_correct_conv; [| lia].
        setoid_rewrite th_phase_frag_halve at 1. iDestruct "PH" as (?) "(PH&?)".
        rewrite half_inv2. 
        iSplitL "PH"; iIntros (?); iExists _; iFrame.
      - iSplitL.
        2: { iIntros (?). lia. }
        iIntros (?). iFrame. }

    assert (m ∈ MS) as MSm.
    { destruct ETR0 as (?&IN&?&?).
      apply gmultiset_elem_of_elements. eapply elem_of_list_lookup; eauto. } 
    iEval (rewrite {3}(gmultiset_disj_union_difference' _ _ MSm)) in "TOKS".
    iDestruct (methods_toks_split with "TOKS") as "[TOK TOKS]".

    rewrite bi.sep_comm !bi.sep_assoc. iSplit.
    2: by destruct s'.
    
    iAssert (cti_cond ic m {tr[ c ]} ∗ (⌜ ii = 0 ⌝ → method_tok m))%I with "[CTA TOK]" as "[$ TOK]". 
    { rewrite /cti_cond /=.
      fold ii. destruct ii eqn:II.
      - iSplitR; [| by iFrame]. iIntros (?). lia.
      - iSplitL; [| iIntros (?); lia].
        iIntros "%SHORT".
        iFrame. iLeft. by iFrame. }

    iSplitL "TOK CTF TOKS PHτi CPS_PRE'". 
    { iApply (init_wptp_wfree with "[$] [PHτi CPS_PRE'] [$] [$] [$]").
      { done. }
      iFrame. }
      
    destruct decide.
    - iSpecialize ("OB'" with "[//]"). iFrame.
    - iFrame.
  Qed.

  Lemma PR_premise_wfree `{hPre: @heapGpreS Σ M EM} 
    {MTPre: MethodTokenPre Σ} {CTPre: CallTrackerPre Σ} c
    (ETR0: is_init_tpool c.1)
    (MOD_INIT: wfst_is_init_st _ SPEC c)
    (M_FUN: is_fun m)
    :
  PR_premise_multiple
    (obls_sim_rel_wfree ic s')
    (λ etr, fits_inf_call ic m ai etr ∧ has_no_forks etr)
    Σ MaybeStuck c.1 c.2
    (init_om_wfree_state F ic c) ((): @em_init_param _ _ EM).
  Proof using. 
    red. iIntros (Hinv) "(PHYS & MOD)". simpl.
    iMod (@wfst_init_mod _ SPEC with "[PHYS]") as "[#INV (%MT & TOKS)]".
    2: { iFrame. }
    { by rewrite -surjective_pairing. }
         
    iMod ct_init as "(%CT & CTA & CTF)".
    set (PWT := {| pwt_UT := MT; pwt_CT := CT |}).

    iModIntro.
    iExists (wfree_trace_inv ic s' SPEC).    
    iExists (PR_wfree_tokens ic s' SPEC m MSm ai). 

    iSplitR.
    { simpl. iApply hl_config_wp. }
    iSplitL. 
    { 
      (* by iApply init_pr_pr_wfree.  *)
      admit. }
    iSplitR.
    { rewrite -surjective_pairing. by iApply init_wfree_inv. }
    by iApply rah_wfree_inv.
  Qed.

  (* TODO: rename *)
  Lemma simple_om_simulation_adequacy_terminate_multiple_waitfree_impl extr
    (MOD_INIT : wfst_is_init_st _ SPEC (trfirst extr))
    (VALID : extrace_valid extr)
    (FAIR : fair_call extr tpc ii)
    (INIT_TP : is_init_tpool (trfirst extr).1)
    (CALL: from_option (fun c => call_at tpc c m ai (APP := App)) False (extr S!! ii))
    (M_FUN: is_fun m):
    terminating_trace extr /\ int_ref_inf_one (call_progresses ic s') extr ∨
    (∃ k, ¬ fits_inf_call ic m ai (trace_take_fwd k extr)) \/
    (s' = MaybeStuck /\ gets_stuck_ae extr ic). 
  Proof using.
    clear MSm.
    opose proof (om_simulation_adequacy_model_trace_multiple_waitfree
                   ic s'
                wfreeΣ _ (trfirst extr).1 _ _ _ _ _ _ _ VALID _ _) as ADEQ.
    { apply init_om_wfree_is_init. }
    { apply surjective_pairing. }     
    { rewrite -surjective_pairing. 
      eapply PR_premise_wfree; eauto. }
    
    destruct ADEQ as [(mtr & MATCH & OM0 & IREF) | RET].
    2: { right. left. done. } 

    opose proof (obls_matching_traces_OM _ _ _ _ MATCH _) as (omtr & MATCH'' & SR & OM_WF & FIRST'').
    { intros ?? X. apply X. }
    { eapply obls_init_wf. rewrite OM0. apply init_om_wfree_is_init. }

    destruct (Classical_Prop.classic (∃ j, has_return_at extr ic j)) as [[j RET]| NORET].
    { red in RET. rewrite (ic_helper ic) in RET.
      destruct RET as (r & cj & ? & JTH & RET).
      right. left. exists j. intros [_ NVALS _]. 
      specialize (NVALS _ H).

      eapply trace_take_fwd_lookup_Some' in JTH.
      2: reflexivity.
      rewrite JTH /= in NVALS.
      edestruct not_return_nval; eauto. }

    assert (int_ref_inf_one (call_progresses ic s') extr) as IREF1.
    { eapply int_ref_inf_proj_one. eapply int_ref_inf_impl; eauto.
      by intros ?? (?&?&?). }

    destruct (extr S!! ii) as [ci | ] eqn:IITH.
    2: { left.
         pose proof (trace_has_len extr) as [??]. 
         eapply state_lookup_dom_neg in IITH; eauto.
         split; [| done].
         eapply terminating_trace_equiv; eauto.
         destruct x; try done. }

    add_case (exists N, ii <= N /\ is_Some (extr S!! N) /\ ∀ j, N ≤ j → from_option (not_stuck_tid τi) True (extr S!! j)) IF_NS. 
    { intros NS. 
    
      assert (forall τ, obls_trace_fair τ omtr) as OM_FAIR.
      { eapply om_trace_fair; eauto. }

      left. split; [| done]. 
      pose proof (traces_match_valid2 _ _ _ _ _ _ MATCH'') as OM_VALID.
      pose proof (obls_fair_trace_terminate _ OM_VALID OM_FAIR) as OM_TERM.
      
      eapply (traces_match_preserves_termination _ _ _ _ _ _ MATCH'').
      apply OM_TERM; eauto.
      + apply unit_WF.
      + apply fin_wf. }

    destruct (decide (s' = MaybeStuck)) as [S'|S']. 
    2: { apply IF_NS. 
         exists ii. split; [lia| ]. split; [done| ].
         intros.
         destruct (extr S!! j) eqn:ITH; [| done]. simpl.
         eapply ref_call_progress_last; eauto. by destruct s'. }
    
    destruct (Classical_Prop.classic (gets_stuck_ae extr ic)) as [| NS]. 
    { do 2 right. tauto. }
    apply IF_NS.

    rewrite /gets_stuck_ae in NS.
    rewrite not_all_ex_not_iff in NS. destruct NS as (N & NS).
    apply not_impl_and_not_iff in NS as ([? NTH] & NS).
    exists (max ii N). split; [lia| ].
    split.
    { pose proof (Nat.max_spec_le ii N) as [[? MAX] | [? MAX]]; rewrite MAX; eauto. }
    intros. destruct (extr S!! j) eqn:JTH; [| done]. simpl.
    
    rewrite not_ex_all_not_iff in NS.
    specialize (NS j). rewrite /ge in NS. rewrite !not_and_l in NS.
    destruct NS as [? | [? | NS]].
    { lia. }
    { set_solver. }
    rewrite /gets_stuck_at /= in NS.
    rewrite (ic_helper ic) /tpc (tc_helper ic) in NS.
    rewrite JTH in NS.
    destruct (decide (not_stuck_tid τi c)); [done| ]. destruct NS.
    eexists. repeat split.
    { lia. }
    apply stuck_tid_neg. split; eauto.
    opose proof * from_locale_trace.
    { done. }
    { apply IITH. }
    { simpl in CALL.
      move CALL at bottom. do 2 red in CALL.
      rewrite /tpc tc_helper /= in CALL.
      apply mk_is_Some in CALL. apply CALL. }
    { etrans; [| apply H]. lia. }
    by rewrite JTH in H0.
  Qed.

  Theorem simple_om_simulation_adequacy_terminate_multiple_waitfree extr
        (ETR0: valid_init_tpool_restr (trfirst extr).1 MS)
        (MOD_INIT: wfst_is_init_st _ SPEC (trfirst extr))
        (CALL: from_option (fun c => call_at tpc c m ai (APP := App)) False (extr S!! ii))
    :
    extrace_valid extr -> 
    fair_call extr tpc ii ->
    (exists f x b, m = RecV f x b) ->
    terminating_trace extr /\ int_ref_inf_one (call_progresses ic s') extr \/ 
    (exists k, ¬ fits_inf_call ic m ai (trace_take_fwd k extr)) \/
    (s' = MaybeStuck /\ gets_stuck_ae extr ic). 
  Proof.
    intros VALID FAIR M_FUN. 

    destruct (decide (ii = 0 → ∃ e,
                    from_locale (trfirst extr).1 τi = Some e ∧ under_ctx Ki e = Some (m ai))) as [II0| ].
    2: { pose proof tc_helper. 
         clear -n H.
         right. left. 
         apply Classical_Prop.imply_to_and in n as (II & NO0).
         exists 0. intros FITS. apply NO0.
         destruct FITS.
         fold ii in fic_call.
         rewrite trace_take_fwd_0_first in fic_call.
         rewrite II /= in fic_call.
         red in fic_call. simpl in fic_call. eauto.
         red in fic_call. rewrite H in fic_call.
         eexists. split; eauto. by rewrite under_ctx_fill. }

    destruct (@decide (∀ e, from_locale (trfirst extr).1 τi = Some e → to_val e = None)) as [E0| ].
    { destruct (from_locale (trfirst extr).1 τi) eqn:E.
      2: { left. set_solver. }
      destruct (to_val e) eqn:V.
      { right. set_solver. }
      left. set_solver. }
    2: { apply not_forall_exists_not in n as [e VAL].
         apply Classical_Prop.imply_to_and in VAL as [E VAL].
         right. left. exists 0. intros FITS. apply VAL.
         destruct FITS. 
         specialize (fic_never_val 0). rewrite trace_take_fwd_0_first /= in fic_never_val.
         rewrite E in fic_never_val. done. }

    assert (is_init_tpool (trfirst extr).1) as INIT_TP.
    { repeat split; eauto.
      red in ETR0.
      (* should follow from ETR0 *)
      admit. }

    by apply simple_om_simulation_adequacy_terminate_multiple_waitfree_impl.
  Admitted.

  (* TODO: rename *)
  Lemma obls_terminates_impl_multiple_waitfree
    (extr : extrace heap_lang)
    (ETR0: valid_init_tpool_restr (trfirst extr).1 MS)
    (MOD_INIT: wfst_is_init_st _ SPEC (trfirst extr))
    (VALID: extrace_valid extr)
    (FAIR: fair_call extr tpc ii)
    (MAIN: previous_calls_return_tr extr ii τi m)
    (CALL: from_option (fun c => call_at tpc c m ai (APP := App)) False (extr S!! ii))
    (M_FUN: is_fun m)
    :
    terminating_trace extr /\ int_ref_inf_one (call_progresses ic s') extr
    \/ has_return extr ic \/
    (s' = MaybeStuck /\ gets_stuck_ae extr ic). 
  Proof.
    opose proof * (simple_om_simulation_adequacy_terminate_multiple_waitfree) as ADEQ; eauto.

    destruct ADEQ as [| [[n NFIT] | STUCK]]; [tauto| | tauto]. 
    right. left. red. simpl in *.
    
    destruct (extr S!! ii) as [ci | ] eqn:ITH; rewrite ITH /= in CALL; [| done].
    by eapply not_fic_has_return.
  Qed.
    
End WFAdequacy.

Theorem wfree_token_is_wait_free_restr MS
  (SPEC: WaitFreeSpecToken MS)
  (FUNS: map_Forall (const ∘ is_fun) MS)
  :
  wait_free_restr MS (wfst_is_init_st _ SPEC) (* s' *) NotStuck any_arg.
Proof using.
  red. intros etr ETR0 MOD_INIT VALID. intros m IN.
  
  apply main_returns_reduction; try done.
  { (* TODO: prove above separately? *)
    apply elem_of_dom in IN as [??]. eapply FUNS; eauto. }
  
  red. intros [i tpc] a ci FAIR ITH MAIN CALL _.

  opose proof * (obls_terminates_impl_multiple_waitfree (TraceCtx i tpc)
                   NotStuck
                ) as ADEQ.
  3: by apply MOD_INIT. 
  all: eauto.
  { simpl. by rewrite ITH. }
  { apply elem_of_dom in IN as [??]. eapply FUNS; eauto. }
    
  destruct ADEQ as [[TERM PROGRESS]| [? | ?]].
  2, 3: tauto. 

  pose proof (trace_has_len etr) as [? LEN].
  eapply terminating_trace_equiv in TERM as [len EQ]; eauto. subst.
  opose proof (proj2 (state_lookup_dom _ _ LEN (len - 1)) _) as [c LAST].
  { apply trace_len_gt_0 in LEN. simpl in *. lia. }
  
  assert (i <= len - 1) as DOM.
  { pose proof ITH as DOM.
    eapply mk_is_Some, state_lookup_dom in DOM; eauto. simpl in DOM.
    lia. }

  add_case (not_stuck_tid (tpctx_tid tpc) c) IF_NS.
  { intros NS.
    left.
    edestruct @Classical_Prop.classic as [RET | NORET]; [by apply RET| ].

    clear PROGRESS.
        
    pose proof DOM as EE. eapply from_locale_trace in EE; eauto.
    2: { eapply locales_of_cfg_Some. eapply expr_at_in_locales.
         erewrite <- surjective_pairing. eauto. }
    rewrite LAST /= in EE. destruct EE as [e EE].
    
    destruct (decide (nval_at tpc c)) as [NVAL | VAL]. 
    + clear ITH CALL MOD_INIT VALID ETR0 SPEC MAIN.
      eapply has_return_fin_trace; eauto. 
    + eapply call_returns_if_not_continues in DOM; eauto.
      2: { eapply call_nval_at; eauto. done. }
      destruct DOM as (k & r & ck & RANGE & KTH & RETk).
      red. exists k, r, ck. split; eauto. lia. }
  
  (* destruct s'. *)
  (* 2: { destruct (decide (not_stuck_tid (tpctx_tid tpc) c)). *)
  (*      { by apply IF_NS. } *)
  (*      right. split; auto.          *)
  (*      red. intros N [? NTH]. *)
  (*      exists (len - 1). repeat split; eauto. *)
  (*      { red. eapply mk_is_Some, state_lookup_dom in NTH; eauto. *)
  (*        simpl in NTH. lia. } *)
  (*      red. destruct tpc. *)
  (*      eexists. repeat split; eauto. *)
  (*      apply stuck_tid_neg. split; auto. *)
  (*      eapply from_locale_trace in DOM; eauto. *)
  (*      by rewrite LAST in DOM. } *)
  
  apply IF_NS.
  eapply ref_call_progress_last in PROGRESS; eauto. 
Qed.
