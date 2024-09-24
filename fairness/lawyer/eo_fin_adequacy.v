From trillium.fairness.heap_lang Require Import simulation_adequacy.
From trillium.fairness.lawyer Require Import obligations_model.


Section ObligationsAdequacy.

  Context {Λ: language}. 
  Context `(OP: ObligationsParams Degree Level (locale Λ) LIM_STEPS).
  Context `{Countable (locale Λ)}.
  Let OM := ObligationsModel OP.

  
  

End ObligationsAdequacy.
