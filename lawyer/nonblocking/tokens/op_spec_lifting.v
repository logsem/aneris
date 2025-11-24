From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context wptp_gen pwp wfree_traces calls pwp_ext pr_wfree_tokens om_wfree_inst_tokens.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From lawyer Require Import action_model sub_action_em.
From lawyer Require Import program_logic.  
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From heap_lang Require Import sswp_logic lang locales_helpers_hl.

(* TODO: reorganize imports *)

Close Scope Z. 

Section SpecLifting.
  Context `{PWT: PrWfreeTok Σ}.

  Context {M: Model} {EM: ExecutionModel heap_lang M}.

  Context (m: val) (τ: locale heap_lang). 

  (* TODO: ct_interp_tok doesn't need an entire trace_ctx *)
  Let mock_tctx := TraceCtx 99 (TpoolCtx ectx_emp τ). 

  (* TODO: move *)
  Lemma ct_auth_frag_agree c1 c2:
    ct_auth c1 -∗ ct_frag c2 -∗ ⌜ c2 = c1 ⌝. 
  Proof using.
    simpl.
    rewrite bi.wand_curry -own_op.
    iIntros "X". iDestruct (own_valid with "[$]") as %V.
    iPureIntro. symmetry. by apply excl_auth_agree_L.
  Qed.  

  (* TODO: move *)
  Lemma ct_auth_frag_update c1 c2 c':
    ct_auth c1 -∗ ct_frag c2 ==∗ ct_auth c' ∗ ct_frag c'. 
  Proof using.
    simpl. 
    rewrite bi.wand_curry -!own_op.
    iApply own_update. apply excl_auth_update. 
  Qed.

  Lemma inside_call_extend extr tp1 tp2 K e σ1
    (Hζ : locale_of tp1 (fill K e) = τ)
    (Hextr : trace_ends_in extr (tp1 ++ fill K e :: tp2, σ1))
    (s : nat)
    (CALL : inside_call m (tpctx_tid (tctx_tpctx mock_tctx)) K s extr e)
    (e2 : expr)
    (σ2 : state)
    (H : ectx_language.prim_step e σ1 e2 σ2 [])
    (V2 : to_val e2 = None):
    inside_call m τ K s (extr :tr[ Some τ ]: (tp1 ++ fill K e2 :: tp2 ++ [], σ2)) e2.
  Proof using.
    red in CALL. destruct CALL as (a & CALL & PREV & NORET & CUR).
    pose proof (trace_length_at_least extr) as LENnz. simpl in LENnz.
    remember (trace_length extr) as N.
    red. exists a. simpl. rewrite -HeqN. rewrite -HeqN in LENnz PREV.
     repeat split.
    - destruct CALL as (?&CALL&?). eexists. split; eauto.
      rewrite -CALL. apply trace_lookup_extend_lt. rewrite -HeqN. lia.
    - lia.
    - simpl. intros j DOM.
      assert (s <= j <= trace_length extr - 1 \/ j = trace_length extr) as [DOM' | ->].
      { lia. }
      + pose proof DOM' as X%NORET. 
        destruct (extr !! j) eqn:JTH; rewrite JTH /= in X; [| done].
        rewrite trace_lookup_extend_lt.
        2: { rewrite -HeqN. lia. }
        rewrite JTH. eauto.
      + rewrite trace_lookup_last.
        2: { simpl. rewrite -HeqN. lia. }
        simpl.
        red. eexists. split; [| apply V2]. 
        red.
        rewrite -Hζ. rewrite /from_locale.
        by rewrite from_locale_from_locale_of.
    - rewrite app_nil_r.
      rewrite -Hζ. rewrite /locale_of.
      rewrite list_lookup_middle; [| done].
      simpl. by apply under_ctx_spec.
  Qed. 

  Lemma lift_call e
    (NVAL: to_val e = None):
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) si_add_none in
     WP e @τ {{ _, unit_tok }}) -∗
    ct_frag (Some e) -∗
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) (@ct_interp_tok mock_tctx m _ PWT) in WP e @τ {{ _, ct_frag None }}).
  Proof using.
    simpl. 
    iIntros "WP MRK".
    iLöb as "IH" forall (e NVAL).

    repeat rewrite wp_unfold.
    rewrite /wp_pre. simpl.
    rewrite NVAL /=. 

    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "(PHYS & CTI)".

    rewrite /ct_interp_tok /ct_interp. iDestruct "CTI" as "(%&AUTH & X)".
    iDestruct (ct_auth_frag_agree with "[$] [$]") as %EQ. 
    iDestruct "X" as "[(?&%) | (%&%&%&->&%CALL)]".
    { subst. done. }
    inversion EQ. subst e0. clear EQ.

    assert (K0 = K) as ->.
    { red in CALL. destruct CALL as (?&?&?&?&CUR). revert CUR. 
      rewrite Hextr /=. 
      subst τ. rewrite /locale_of. rewrite list_lookup_middle /=; [| done].
      rewrite under_ctx_spec.
      intros EQ%ectx_fill_ctx_nval; done. }    

    iMod ("WP" $! _ looping_trace K with "[//] [] [] [PHYS]") as "[RED WP]".
    1, 2: done.
    { iFrame. }
    iModIntro. iFrame.

    iIntros "**".
    iSpecialize ("WP" with "[//]"). 
    iMod "WP". iModIntro.
    iNext. 
    iMod "WP". iModIntro.

    iApply (@step_fupdN_wand with "WP"). iIntros "ST".
    iMod "ST" as "(%&%& (PHYS & ADD) & WP & WPS)".

    destruct (to_val e2) eqn:V2.
    { apply of_to_val in V2 as <-. 
      iPoseProof (wp_value_inv with "WP") as "POST".
      iMod (pre_step_elim with "[PHYS ADD] POST") as "((PHYS & ADD) & TOK)".
      { iFrame. }
      iMod (ct_auth_frag_update _ _ None with "[$] [$]") as "[??]".      
      iModIntro. do 2 iExists _. iFrame.
      assert (efs = []) as -> by admit. repeat rewrite big_sepL_nil.
      iSplitL "TOK".
      { iLeft. by iFrame. }
      iSplit; [| done]. by iApply @wp_value.
      Unshelve. 2, 3: exact tt. exact looping_trace. }

    iMod (ct_auth_frag_update _ _ (Some e2) with "[$] [$]") as "[AUTH FRAG]". 
    iModIntro. do 2 iExists _. iFrame.
    assert (efs = []) as -> by admit. repeat rewrite big_sepL_nil.
    iSplitR.
    2: { iFrame. iApply ("IH" with "[//] [$] [$]"). }
    
    iRight. iPureIntro. simpl. 
    exists e2, K, s. split; [done| ].
    eapply inside_call_extend; eauto.
    Unshelve. all: exact tt.
  Admitted.

  Lemma start_call extr tp1 tp2 K σ1 (a: val)
    (Hζ : locale_of tp1 (fill K (m a)) = τ)
  (Hextr : trace_ends_in extr (tp1 ++ fill K (m a) :: tp2, σ1))
  (e2 : expr)
  (σ2 : state)
  (V2 : to_val e2 = None):
  inside_call m τ K (trace_length extr - 1)
    (extr :tr[ Some τ ]: (tp1 ++ fill K e2 :: tp2 ++ [], σ2)) e2.
  Proof using.
    pose proof (trace_length_at_least extr) as LENnz. simpl in LENnz. 
    red. simpl. exists a.
    remember (trace_length extr) as N.
    rewrite -HeqN. rewrite -HeqN in LENnz. 
    repeat split.
    - eexists.
      split.
      + eapply ft_lookup_old.
        eapply trace_lookup_last. rewrite -HeqN. lia.
      + rewrite Hextr. simpl.
        rewrite -Hζ. rewrite /from_locale. 
        by rewrite from_locale_from_locale_of.
    - lia.
    - intros j DOM.
      assert (j = trace_length extr - 1 \/ j = trace_length extr) as [-> | ->].
      { rewrite -HeqN. lia. }
      + rewrite trace_lookup_extend_lt.
        2: { rewrite -HeqN; lia. }
        erewrite trace_lookup_last; [| rewrite -HeqN; lia]. simpl.
        rewrite Hextr. 
        eapply (@call_nval_at _ _ App); [done| ].
        red. red.
        rewrite -Hζ. rewrite /from_locale. 
        by rewrite from_locale_from_locale_of.
      + rewrite @trace_lookup_last.
        2: done.
        simpl. 
        red. eexists. split; [| apply V2].
        red. rewrite -Hζ. rewrite /from_locale. 
        by rewrite from_locale_from_locale_of.
    - rewrite app_nil_r.
      rewrite -Hζ. rewrite /locale_of.
      rewrite list_lookup_middle; [| done].
      simpl. by apply under_ctx_spec.
  Qed.

  (* Lemma lift_spec `{Hinv : @IEMGS heap_lang M LG EM Σ} (a: val): *)
  (*   (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) si_add_none in *)
  (*    {{{ unit_tok }}} App m a @ τ {{{ v, RET v; unit_tok}}} ) ⊢ *)
  (*   (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) (@ct_interp_tok mock_tctx m _ PWT) in *)
  (*    {{{ ct_frag None }}} App m a @ τ {{{ v, RET v; ct_frag None }}} ). *)
  (* Proof using. *)
  Lemma lift_spec `{Hinv : @IEMGS heap_lang M LG EM Σ} (a: val):
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) si_add_none in
     □ (unit_tok -∗ WP (App m a) @ τ {{ v, unit_tok}} )) ⊢
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) (@ct_interp_tok mock_tctx m _ PWT) in
     □ (ct_frag None -∗ WP (App m a) @ τ {{ v, ct_frag None }} )).
  Proof using.
    simpl. iIntros "#WP".
    iIntros "!> NO".

    repeat rewrite wp_unfold.
    rewrite /wp_pre. simpl.

    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "(PHYS & CTI)".

    iAssert (ct_frag None ∗ ct_auth None ∗ unit_tok)%I with "[NO CTI]" as "(FRAG & AUTH & TOK)".
    { rewrite /ct_interp_tok /ct_interp. iDestruct "CTI" as "(%&AUTH & X)".
      iDestruct (ct_auth_frag_agree with "[$] [$]") as %EQ. 
      iDestruct "X" as "[(?&?) | (%&%&%&->&?)]". 
      { subst. iFrame. }
      congruence. }

    iSpecialize ("WP" with "TOK").
    iMod ("WP" $! _ looping_trace K with "[//] [] [] [PHYS]") as "[RED WP]".
    1, 2: done.
    { iFrame. }
    iModIntro. iFrame.

    iIntros "**".
    iSpecialize ("WP" with "[//]"). 
    iMod "WP". iModIntro.
    iNext. 
    iMod "WP". iModIntro.

    iApply (@step_fupdN_wand with "WP"). iIntros "ST".
    iMod "ST" as "(%&%& (PHYS & ADD) & WP & WPS)".

    destruct (to_val e2) eqn:V2.
    { apply of_to_val in V2 as <-. 
      iPoseProof (wp_value_inv with "WP") as "POST".
      iMod (pre_step_elim with "[PHYS ADD] POST") as "((PHYS & ADD) & TOK)".
      { iFrame. }
      iModIntro. do 2 iExists _. iFrame.
      assert (efs = []) as -> by admit. repeat rewrite big_sepL_nil.
      iSplitL "TOK".
      { iLeft. by iFrame. }
      iSplit; [| done]. by iApply @wp_value.
      Unshelve. 2, 3: exact tt. exact looping_trace. }

    iMod (ct_auth_frag_update _ _ (Some e2) with "[$] [$]") as "[AUTH FRAG]". 
    iModIntro. do 2 iExists _. iFrame.
    assert (efs = []) as -> by admit. repeat rewrite big_sepL_nil.
    iSplitR.
    2: { iFrame. by iApply (lift_call with "[$] [$]"). }  
    
    iRight. iPureIntro. simpl. 
    exists e2, K, (trace_length extr - 1). split; [done| ].
    eapply start_call; eauto. 
    Unshelve. all: exact tt.
  Qed.

End SpecLifting. 
