From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.fairness.heap_lang Require Export lang heap_lang_defs.


Section adequacy.
(* Context . *)
(* Context .  *)

(* Let eGS := @heap_fairnessGS EM.  *)

Theorem strong_simulation_adequacy_general
    `{hPre: @heapGpreS Σ M EM} (s: stuckness) (e1 : expr) σ1 (s1: M)
    (R: execution_trace heap_lang → auxiliary_trace M → Prop)
    (conv_init: heapGS Σ EM -> iProp Σ)
  :
  rel_finitary R →
  em_is_init_st ([e1], σ1) s1 ->
  em_valid_state_evolution_fairness {tr[ ([e1], σ1) ]} {tr[ s1 ]} ->
  (∀ `{Hinv : @heapGS Σ M EM} ,
    ⊢ (([∗ map] l ↦ v ∈ heap σ1, mapsto l (DfracOwn 1) v) ∗
       conv_init Hinv
       ={⊤}=∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ _, em_thread_post 0%nat (em_GS0 := heap_fairnessGS)}} ∗
       rel_always_holds0 R s state_interp (fun _ => em_thread_post 0%nat (em_GS0 := heap_fairnessGS)) e1 σ1 s1) ∗
       (em_init_resource s1 (em_GS0 := heap_fairnessGS) ∗ em_msi ([e1], σ1) s1 (em_GS0 := heap_fairnessGS) ==∗ conv_init Hinv ∗ em_msi ([e1], σ1) s1 (em_GS0 := heap_fairnessGS))%I) ->
  continued_simulation R (trace_singleton ([e1], σ1)) (trace_singleton s1).
Proof.
  intros Hfin INIT VALID1 H.

  (* apply (wp_strong_adequacy heap_lang M Σ s); first by eauto. *)
  intros. apply (wp_strong_adequacy heap_lang M Σ s); [done| ]. 
  iIntros (?) "".

  iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen [Hσ _]]".  
  (* iMod (init_fairnessGS_LM _ _ s1 e1) as (fGS) "GEN".    *)
  iMod (em_initialization _ s1 ([e1], σ1)) as (fGS) "[LM_INIT MSI]"; [done| ].
  Unshelve. 2: by apply hPre. 

  set (distG := {| heap_fairnessGS := (fGS: (em_GS Σ (ExecutionModel := EM))) |}).
  (* iMod (H distG) as "Hwp". clear H. *)
  iPoseProof (H distG) as "[Hwp CONV]". clear H.
 
  iExists state_interp, (fun _ => em_thread_post 0%nat), fork_post.
  iSplitR.
  { unfold config_wp. iIntros "!>!>" (???????) "?". done. }

  (* iApply "Hwp".  *)
  iMod ("CONV" with "[LM_INIT MSI]") as "[LM_INIT' MSI]"; [by iFrame| ]. 
  
  iSpecialize ("Hwp" with "[Hσ LM_INIT']"); [by iFrame| ]. 
  iDestruct "Hwp" as ">[Hwp H]". 
  iModIntro. iFrame.
Qed.

End adequacy.
