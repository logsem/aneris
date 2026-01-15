From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context wptp_gen pwp wfree_traces calls op_eval_helpers.
From lawyer.nonblocking.tokens Require Import pwp_ext pr_wfree_tokens om_wfree_inst_tokens tokens_ra.
From lawyer.nonblocking.logrel Require Import valid_client.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From lawyer Require Import action_model sub_action_em program_logic.  
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From heap_lang Require Import sswp_logic lang locales_helpers_hl.

(* TODO: reorganize imports *)

(* (* TODO: move *) *)
(* Lemma no_forks_fill_item e Ki *)
(*   (NOFORKS: no_forks (fill_item Ki e)): *)
(*   no_forks e.  *)
(* Proof using. destruct Ki; simpl; set_solver. Qed.  *)

(* Lemma no_forks_fill e K *)
(*   (NOFORKS: no_forks (fill K e)): *)
(*   no_forks e.  *)
(* Proof using. *)
(*   revert NOFORKS. pattern K. apply rev_ind; clear K. *)
(*   { done. } *)
(*   simpl. intros. *)
(*   rewrite -calls.fill_app /= in NOFORKS. *)
(*   apply H. eapply no_forks_fill_item; eauto. *)
(* Qed. *)

(* Lemma no_forks_fill_item_replace e e' Ki *)
(*   (NOFORKS: no_forks (fill_item Ki e)) *)
(*   (NOFORKS': no_forks e'): *)
(*   no_forks (fill_item Ki e'). *)
(* Proof using. destruct Ki; simpl; set_solver. Qed.  *)

(* Lemma no_forks_fill_replace e e' K *)
(*   (NOFORKS: no_forks (fill K e)) *)
(*   (NOFORKS': no_forks e'): *)
(*   no_forks (fill K e'). *)
(* Proof using. *)
(*   revert NOFORKS. pattern K. apply rev_ind; clear K. *)
(*   { done. } *)
(*   simpl. intros. *)
(*   rewrite -calls.fill_app /= in NOFORKS. rewrite -calls.fill_app /=. *)
(*   eapply no_forks_fill_item_replace; eauto. *)
(*   apply H. eapply no_forks_fill_item; eauto. *)
(* Qed. *)

(* Lemma no_forks_subst s v e *)
(*   (NOFORKS: no_forks e) *)
(*   (NOFORKS': val_nf v): *)
(*   no_forks (subst s v e).  *)
(* Proof using. *)
(*   induction e; try set_solver. *)
(*   - simpl. destruct decide; done. *)
(*   - simpl. destruct decide; try done. *)
(*     apply IHe. eauto. *)
(* Qed. *)

(* (* TODO: move *) *)
(* Lemma no_forks_prim_step e σ e' σ' efs *)
(*   (PSTEP: prim_step e σ e' σ' efs) *)
(*   (NOFORKS: no_forks e): *)
(*   efs = [] /\ no_forks e'. *)
(* Proof using. *)
(*   inversion PSTEP. simpl in *. subst. *)
(*   pose proof NOFORKS as NOFORKS'%no_forks_fill. *)
(*   inversion H1; subst; eauto. *)
(*   14: by inversion NOFORKS'. *)
(*   all: try by (split; [done | ]; eapply no_forks_fill_replace; eauto; simpl in *; tauto).  *)
(*   - split; [done | ]. *)
(*     inversion NOFORKS'. simpl in H.  *)
(*     destruct x, f; simpl; eapply no_forks_fill_replace; eauto. *)
(*     all: apply no_forks_subst; try done. *)
(*     by apply no_forks_subst.  *)
(*   - split; [done | eapply no_forks_fill_replace; eauto]. *)
(*     simpl in NOFORKS'. *)
(*     by inv_unop_eval H.  *)
(*   - split; [done | eapply no_forks_fill_replace; eauto]. *)
(*     by inv_binop_eval H.  *)
(*   - split; [done | eapply no_forks_fill_replace; eauto]. *)
(*     simpl in NOFORKS'. simpl. tauto.  *)


Close Scope Z. 

Section SpecLifting.
  Context `{PWT: PrWfreeTok MS Σ}.

  Context {M: Model} {EM: ExecutionModel heap_lang M}.

  Context (m: val). 

  (* TODO: ct_interp_tok doesn't need an entire trace_ctx *)
  Context (ic: @trace_ctx heap_lang).
  Let τ := tpctx_tid $ tctx_tpctx ic.   

  Context (s: stuckness). 

  Lemma lift_call E e
    (NVAL: to_val e = None)
    (Q: val -> iProp Σ)
    (* (NOFORKS: no_forks e) *)
    :
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ _ PWT) si_add_none in
     WP e @ CannotFork; s ; τ ; E {{ v, method_tok m ∗ Q v }}) -∗
    ct_frag (Some e) -∗
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ _ PWT) (@ct_interp_tok ic _ m _ PWT) in WP e @ CannotFork; s ; τ ; E {{ v, ct_frag None ∗ Q v }}).
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
    iMod "ST" as "(%&%& (PHYS & ADD) & WP & WPS & %FF)".
    specialize (FF eq_refl). subst efs. 

    destruct (to_val e2) eqn:V2.
    { apply of_to_val in V2 as <-. 
      iPoseProof (wp_value_inv with "WP") as "POST".
      iMod (pre_step_elim with "[PHYS ADD] POST") as "((PHYS & ADD) & (TOK & Q))".
      { iFrame. }
      iMod (ct_auth_frag_update _ _ None with "[$] [$]") as "[??]".      
      iModIntro. do 2 iExists _. iFrame.
      repeat rewrite big_sepL_nil.
      iSplitL "TOK".
      { iLeft. by iFrame. }
      iSplit; [| done]. by iApply @wp_value.
      Unshelve. 2, 3: exact tt. exact looping_trace. }

    iMod (ct_auth_frag_update _ _ (Some e2) with "[$] [$]") as "[AUTH FRAG]". 
    iModIntro. do 2 iExists _. iFrame.
    repeat rewrite big_sepL_nil.
    iSplitR.
    2: { iFrame. iSplit; [| done]. 
         iApply ("IH" with "[//] [$] [$]"). }
    
    iRight. iPureIntro. simpl. 
    exists e2, K, s0. split; [done| ].
    eapply inside_call_extend; eauto.
    Unshelve. all: exact tt.
  Qed.

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

  (** The original intention was to lift the entire interp_arrow 
      from "simple pwp_ext" (without extended state interpretation)
      to "cti_interp-based pwp_ext".
      interp_arrow is a triple that takes an argument in LR and returns result in LR.
      However, the two triples would operate with different LRs (since state interpretations are different), and it's not clear how to convert between the two.
      Therefore, we'd only use this lifting lemma for stronger specs that ignore the input predicate P and ensure, via pure Q, that the result is a ground value (for which we can manually establish LR).
   *)
  (* Lemma lift_spec `{Hinv : @IEMGS heap_lang M LG EM Σ} E (a: val) *)
  (*   (P: iProp Σ) (Q: val -> iProp Σ): *)
  (*   (let _ := IEMGS_into_Looping (@pwt_Hinv _ _ PWT) si_add_none in *)
  (*    □ (method_tok m -∗ P -∗ WP (App m a) @ s ; τ ; E {{ v, method_tok m ∗ Q v }} )) ⊢ *)
  (*   (let _ := IEMGS_into_Looping (@pwt_Hinv _ _ PWT) (@ct_interp_tok ic _ m _ PWT) in *)
  (*    □ (ct_frag None -∗ P -∗ WP (App m a) @ s ; τ ; E {{ v, ct_frag None ∗ Q v }} )). *)

  Lemma lift_spec `{Hinv : @IEMGS heap_lang M LG EM Σ} E (a: val)
    (P: iProp Σ) (Q: val -> iProp Σ):
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ _ PWT) si_add_none in
     □ (method_tok m -∗ P -∗ WP (App m a) @ CannotFork; s ; τ ; E {{ v, method_tok m ∗ Q v }} )) ⊢
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ _ PWT) (@ct_interp_tok ic _ m _ PWT) in
     □ (ct_frag None -∗ P -∗ WP (App m a) @ CannotFork; s ; τ ; E {{ v, ct_frag None ∗ Q v }} )).
  Proof using.
    simpl. iIntros "#WP".
    iIntros "!> NO P".

    repeat rewrite wp_unfold.
    rewrite /wp_pre. simpl.

    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "(PHYS & CTI)".

    iAssert (ct_frag None ∗ ct_auth None ∗ method_tok m)%I with "[NO CTI]" as "(FRAG & AUTH & TOK)".
    { rewrite /ct_interp_tok /ct_interp. iDestruct "CTI" as "(%&AUTH & X)".
      iDestruct (ct_auth_frag_agree with "[$] [$]") as %EQ. 
      iDestruct "X" as "[(?&?) | (%&%&%&->&?)]". 
      { subst. iFrame. }
      congruence. }

    iSpecialize ("WP" with "TOK P").
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
    iMod "ST" as "(%&%& (PHYS & ADD) & WP & WPS & %FF)".
    specialize (FF eq_refl). subst efs. 

    destruct (to_val e2) eqn:V2.
    { apply of_to_val in V2 as <-. 
      iPoseProof (wp_value_inv with "WP") as "POST".
      iMod (pre_step_elim with "[PHYS ADD] POST") as "((PHYS & ADD) & (TOK & Q))".
      { iFrame. }
      iModIntro. do 2 iExists _. iFrame.
      repeat rewrite big_sepL_nil.
      iSplitL "TOK".
      { iLeft. by iFrame. }
      iSplit; [| done]. by iApply @wp_value.
      Unshelve. 2, 3: exact tt. exact looping_trace. }

    iMod (ct_auth_frag_update _ _ (Some e2) with "[$] [$]") as "[AUTH FRAG]". 
    iModIntro. do 2 iExists _. iFrame.
    repeat rewrite big_sepL_nil.
    iSplitR.
    2: { iFrame. iSplit; [| done]. 
         by iApply (lift_call with "[$] [$]"). }
    
    iRight. iPureIntro. simpl. 
    exists e2, K, (trace_length extr - 1). split; [done| ].
    eapply start_call; eauto. 
    Unshelve. all: exact tt.
  Qed. 

End SpecLifting. 
