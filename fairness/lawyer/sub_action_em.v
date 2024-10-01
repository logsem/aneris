From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From trillium Require Import language.
From trillium.program_logic Require Import traces weakestpre.
From trillium.fairness Require Import locales_helpers execution_model.
From trillium.fairness.lawyer Require Import action_model.


Class ActionSubEM (Λ: language) (AM: ActionModel) := {

    (* TODO: how to express that these two are typeclasses themselves? *)
    asem_preGS: gFunctors -> Set;
    asem_GS: gFunctors -> Set;
    asem_Σ: gFunctors;
    asem_Σ_subG: forall Σ, subG asem_Σ Σ -> asem_preGS Σ;

    asem_valid_evolution_step:
      cfg Λ -> olocale Λ → cfg Λ → 
      amSt AM → Action * option (amRole AM) → amSt AM → Prop;

    asem_msi {Σ} `{asem_GS Σ}: cfg Λ -> amSt AM -> iProp Σ;
    
    asem_init_param: Type; 
    asem_init_resource {Σ: gFunctors} `{asem_GS Σ}: 
      amSt AM → asem_init_param -> iProp Σ;
    asem_is_init_st: cfg Λ -> amSt AM -> Prop;
    
    asem_initialization Σ `{ePreGS: asem_preGS Σ}: 
    forall (s1: amSt AM) (σ: cfg Λ) (p: asem_init_param)
      (INIT_ST: asem_is_init_st σ s1),
      ⊢ (|==> ∃ eGS: asem_GS Σ, @asem_init_resource _ eGS s1 p ∗ @asem_msi _ eGS σ s1)
}.


Definition TopAM_EM {Λ AM} (ASEM: ActionSubEM Λ AM)
  (thread_post: forall Σ, asem_GS Σ -> locale Λ → iProp Σ):
  ExecutionModel Λ (AM2M AM).
  esplit. 
  - apply asem_Σ_subG.
  - apply asem_valid_evolution_step.
  - exact thread_post. 
  - by apply asem_initialization.
Defined. 
  
Section AM_UPD.

  Context `{ASEM: ActionSubEM Λ AM}. 
  Context `{aeGS: asem_GS Σ}.
  Context `{Countable (locale Λ)}.
  
  Definition AM_st_interp_interim (c c': cfg Λ)
    (δ: amSt AM) (τ: locale Λ) oτ': iProp Σ :=
    asem_msi c δ (asem_GS0 := aeGS) ∗ 
    ⌜ locale_step c (Some τ) c' ⌝ ∗
    ⌜ step_fork c c' = oτ' ⌝
  .

  Section AMU.
    Context {iGS: invGS_gen HasNoLc Σ}. 

    Definition AMU_impl
      (f: option (locale Λ)) E ζ (a: Action) (P : iProp Σ): iProp Σ :=
      ∀ c c' δ, 
        AM_st_interp_interim c c' δ ζ f ={E}=∗
        ∃ δ' oρ, asem_msi c' δ' (asem_GS0 := aeGS) ∗
                 (* ⌜ amTrans _ δ (a, oρ) δ' ⌝ ∗ P *)
                 ⌜ asem_valid_evolution_step c (Some ζ) c' δ (a, oρ) δ' ⌝ ∗
                 P
    .

    Definition AMU := AMU_impl None.
    Definition AMU__f E ζ ζ' P := AMU_impl (Some ζ') E ζ P. 

  End AMU.

End AM_UPD.


Section AMU_HL.
  From trillium.fairness.lawyer Require Import program_logic. 
    
  Context `{ASEM: ActionSubEM heap_lang AM}. 
  Context {Σ: gFunctors}. 

  Definition AMU_lift_MU_impl (f: option $ locale heap_lang) 
    `{aeGS: asem_GS Σ}
    `{EM: ExecutionModel heap_lang M} `{hGS: @heapGS Σ _ EM}
    (A: coPset) := 
    ⊢ ∀ E ζ P (a: Action) (Aa: a ∈ A), AMU_impl f E ζ a P (aeGS := aeGS) -∗ MU_impl f E ζ P.
  
  Definition AMU_lift_MU := @AMU_lift_MU_impl None. 
  Definition AMU_lift_MU__f τ := @AMU_lift_MU_impl (Some τ). 
  
  Lemma AMU_lift_top thread_post
    (EM := TopAM_EM ASEM thread_post)
    `{hGS: @heapGS Σ _ EM}
    (aeGS := heap_fairnessGS (heapGS := hGS))
    f
    :
    @AMU_lift_MU_impl f aeGS _ EM _ (↑ nroot).
  Proof using.
    red. iIntros (E ζ P ??). rewrite /AMU /AMU_impl /MU /MU_impl.
    simpl. 
    iIntros "AMU" (extr mtr) "TI'".
    simpl. destruct extr as [| extr c']; [done| ]. simpl.
    iDestruct "TI'" as "(?&MSI&->&%&%)".
    iMod ("AMU" with "[MSI]") as "AMU".
    { iFrame. iPureIntro. eauto. }
    iModIntro. iDestruct "AMU" as (??) "(?&%&?)".
    do 2 iExists _. iFrame. eauto.
  Qed. 

End AMU_HL.
