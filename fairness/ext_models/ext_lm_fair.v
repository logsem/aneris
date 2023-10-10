From trillium.fairness.ext_models Require Import ext_models.
From trillium.fairness Require Import lm_fair fuel_ext.

Section ExtModelLM.
  Context `{EM: ExtModel M}. 
  Context `{LM: LiveModel G M LSI} `{Countable G} `{EqDecision (fmstate M)}.
  Context `{∀ s1 ρ s2, Decision (fmtrans M s1 (Some ρ) s2)}.
  Context `{Inhabited (lm_ls LM)} `{Inhabited G}. 

  Context {lmEI: Type} `{Countable lmEI}.
  (* Additional constraints on LiveStates during the external step *)
  Context {lmETs': lmEI -> relation (lm_ls LM)}. 

  Context (projEI: lmEI -> (@EI _ EM)). 

  Definition lmETs (ι: lmEI): relation (lm_ls LM) :=
    fun δ1 δ2 => (@ETs _ EM) (projEI ι) (ls_under δ1) (ls_under δ2) /\
                lmETs' ι δ1 δ2. 

  Context {lm_active_exts: lm_ls LM -> gset lmEI}. 
  Context (lm_active_exts_spec: forall δ ι, ι ∈ lm_active_exts δ <-> ∃ δ', lmETs ι δ δ').

  Let lib_fair := LM_Fair (LM := LM). 

  Instance ExtLMFair: ExtModel lib_fair := 
    Build_ExtModel lib_fair _ _ _ _ _ lm_active_exts_spec.

End ExtModelLM.
