From iris.proofmode Require Import tactics.
From trillium.traces Require Import inftraces trace_lookup exec_traces trace_len. 
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_adequacy obligations_model obligations_em obligations_am obls_termination obligations_wf.
From lawyer.nonblocking Require Import trace_context wptp_gen pwp wfree_traces calls pwp_ext pr_wfree_tokens om_wfree_inst_tokens.
From trillium.program_logic Require Import execution_model weakestpre adequacy_utils adequacy_cond simulation_adequacy_em_cond. 
From lawyer Require Import action_model sub_action_em.
From lawyer Require Import program_logic.  
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From heap_lang Require Import sswp_logic lang.

(* TODO: reorganize imports *)

Section SpecLifting.
  Context `{PWT: PrWfreeTok Σ}.

  Context {M: Model} {EM: ExecutionModel heap_lang M}.

  Context (m: val) (τ: locale heap_lang). 

  (* TODO: ct_interp_tok doesn't need an entire trace_ctx *)
  Let mock_tctx := TraceCtx 99 (TpoolCtx ectx_emp τ). 

  Lemma lift_spec `{Hinv : @IEMGS heap_lang M LG EM Σ} (a: val):
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) si_add_none in
     {{{ unit_tok }}} App m a @ τ {{{ v, RET v; unit_tok}}} ) ⊢
    (let _ := IEMGS_into_Looping (@pwt_Hinv _ PWT) (@ct_interp_tok mock_tctx m _ PWT) in
     {{{ ct_frag None }}} App m a @ τ {{{ v, RET v; ct_frag None }}} ).
  Proof using.
    simpl. iIntros "#WP".
    iIntros (Φ) "!> NO POST".
    iSpecialize ("WP" $! Φ). 
    repeat rewrite wp_unfold.
    rewrite /wp_pre. simpl.

    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "(PHYS & CTI)".
  iMod "Hsswp" as "foo".
    destruct (to_val e1) eqn:He1.
    { erewrite val_stuck in He1; done. }
    simpl. 
    iDestruct "HSI" as "(%EV & PHYS & MSI)". simpl. 
    iMod ("Hwp" $! _ looping_trace K with "[//] [] [] [PHYS ADD]") as "[Hs Hwp]".
    1, 2: done.
    { iFrame. }
    iDestruct ("Hwp" with "[]") as "Hwp"; first done.
    iModIntro. 
    iApply (step_fupdN_wand with "Hwp").
    iIntros "!> Hwp".
    iMod "Hwp" as ([] []) "((PHYS & ADD) & WP & WPS')".
    
    rewrite /MU /MU_impl. iMod ("MU" $! (trace_extend _ _ (_, _)) with "[PHYS MSI]") as (δ ρ) "TI".
    { rewrite /trace_interp_interim.
      iFrame.
      iPureIntro. split.
      { rewrite -Hlocale. reflexivity. }
      split; [| done]. 
      rewrite -Hlocale. econstructor; eauto.
      simpl in Hstp. simpl.
      by apply fill_prim_step. }
    
    iModIntro.
    simpl.  iDestruct "TI" as "((%&?&?)&?)". 
    do 2 iExists _. subst ζ. iFrame. 
    iPureIntro. congruence. 
    
 
    setoid_rewrite wp_unfold.
    repeat 


  Context `(WFST: WaitFreeSpecToken m).
  Let F := wfst_F _ WFST. 
 

  pwp_ext
End SpecLifting. 
