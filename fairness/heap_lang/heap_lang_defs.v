From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Export resources fuel.
From trillium.fairness.heap_lang Require Export lang.


Class heapGpreS Σ `(LM: LiveModel heap_lang M) := HeapPreG {
  heapGpreS_inv :> invGpreS Σ;
  heapGpreS_gen_heap :> gen_heapGpreS loc val Σ;
  heapGpreS_fairness :> fairnessGpreS LM Σ;
}.

Class heapGS Σ `(LM:LiveModel heap_lang M) := HeapG {
  heap_inG :> heapGpreS Σ LM;

  heap_invGS :> invGS_gen HasNoLc Σ;
  heap_gen_heapGS :> gen_heapGS loc val Σ;

  heap_fairnessGS :> fairnessGS LM Σ;
}.

Definition heapΣ (M : FairModel) : gFunctors :=
  #[ invΣ; gen_heapΣ loc val; fairnessΣ heap_lang M ].

Global Instance subG_heapPreG {Σ} `{LM : LiveModel heap_lang M} :
  subG (heapΣ M) Σ → heapGpreS Σ LM.
Proof. solve_inG. Qed.

#[global] Instance heapG_irisG `{LM:LiveModel heap_lang M} `{!heapGS Σ LM} : irisG heap_lang LM Σ := {
    state_interp extr auxtr :=
      (⌜valid_state_evolution_fairness extr auxtr⌝ ∗
       gen_heap_interp (trace_last extr).2.(heap) ∗
       model_state_interp (trace_last extr).1 (trace_last auxtr))%I ;
    fork_post tid := λ _, tid ↦M ∅;
}.
