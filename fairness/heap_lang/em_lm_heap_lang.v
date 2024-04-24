From trillium.fairness.heap_lang Require Import heap_lang_defs em_lm. 
From trillium.fairness Require Import lm_fair lm_fair_traces. 
From trillium.fairness.lm_rules Require Import resources_updates. 


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

End LM_EM_HL.
