From trillium.fairness.heap_lang Require Import heap_lang_defs em_lm. 
From trillium.fairness Require Import lm_fair lm_fair_traces trace_interp_corr. 
From trillium.fairness.lm_rules Require Import resources_updates. 
From iris.proofmode Require Import tactics.


Section LM_EM_HL.
  Context `{LM: LiveModel (locale heap_lang) M LSI}.
  (* Context {LF: LMFairPre LM}. *)
  Context {LF: LMFairPre LM}.

  Definition LM_EM_HL: ExecutionModel heap_lang (fair_model_model LM_Fair) :=
    LM_EM (LM := LM) 0%nat ltac:(done).

  (* TODO: how to avoid specifying instances of EqDec and Cnt? *)
  Global Instance LM_EM_fairPre {Σ} {hGS: @heapGpreS Σ _ LM_EM_HL}:
    (* fairnessGpreS LM Σ. *)
    fairnessGpreS LM Σ. 
  Proof.
    apply hGS.
  Qed.

  (* TODO: get rid of it*)
  Global Instance LM_EM_fair `{hGS: @heapGS Σ _ LM_EM_HL}:
    (* fairnessGS LM Σ. *)
    fairnessGS LM Σ.
  Proof. apply hGS. Defined.

  Section EWP_Top.
    From trillium.program_logic Require Import ewp.

    Let LMF := LM_Fair (LF := LF).
    
    Context `{hGS: @heapGS Σ _ LM_EM_HL}. 

    Definition dom_tmap_restr (δ δ': fmstate LMF) := 
      dom (ls_tmap δ') ⊆ dom (ls_tmap δ).

    Let msi: fmstate LMF -> iProp Σ := 
          model_state_interp (fG := @heap_fairnessGS _ _ _ hGS). 
    Let PI (p: state heap_lang) := gen_heap_interp p.(heap). 
    Let RTI := @restores_TI _ _ _ (@heapG_irisG _ _ _ hGS) PI
                           LMF msi dom_tmap_restr _.        

    Lemma LM_restores_TI τ: ⊢ RTI τ τ.
    Proof. 
      rewrite /RTI /restores_TI.
      simpl. rewrite /em_lm_msi. iIntros "**".
      destruct (trace_last extr) as [tp σ] eqn:LASTe. rewrite LASTe.
      iIntros "% (%EV & PI & EM & %CORR)".
      iExists _. iFrame. iIntros "* %PSTEP %MSTEP %RESTR PI MSI".
      iExists _, _. iFrame.
      apply tids_restrict_smaller' in CORR. simpl in CORR. 
      iPureIntro. split.
      { red. repeat split; eauto.
        simpl. red. intros. rewrite -update_locale_dom; eauto.
        (* TODO: remove unused parameters *)
        exact (fun _ _ => True). }
      apply tids_smaller'_restrict.
      red. intros. rewrite -update_locale_dom; eauto.
      (* TODO: remove unused parameters *)
      exact (fun _ _ => True). 
    Qed. 

End EWP_Top. 

End LM_EM_HL.
