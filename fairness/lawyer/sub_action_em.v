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

    Lemma AMU_impl_wand f E ζ a P Q:
      (P -∗ Q) -∗ AMU_impl f E ζ a P -∗ AMU_impl f E ζ a Q.
    Proof using.
      rewrite /AMU_impl. iIntros "PQ AMU" (???) "?".
      iMod ("AMU" with "[$]") as (??) "(?&?&?)".
      iModIntro. do 2 iExists _. iFrame. by iApply "PQ".
    Qed.

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


Section ProdASEM.

  Context `{ASEM1: ActionSubEM Λ AM1}. 
  Context `{ASEM2: ActionSubEM Λ AM2}.

  Let PM := ProdAM AM1 AM2.

  Context
    {is_act1_dec: forall a, Decision (is_action_of AM1 a)}
    {is_act2_dec: forall a, Decision (is_action_of AM2 a)}.

  Open Scope type. 

  Definition prod_asem_valid_evolution_step:
      cfg Λ -> olocale Λ → cfg Λ →
      amSt PM → Action * option (amRole PM) → amSt PM → Prop := 
    fun c oτ c' '(δ1, δ2) aoρ '(δ1', δ2') =>
      let '(a, oρ) := aoρ in
      let A1 := is_act1_dec a in let A2 := is_act2_dec a in
      match oρ with
      | None =>
          @asem_valid_evolution_step _ _ ASEM1 c oτ c' δ1 (a, None) δ1' /\
          @asem_valid_evolution_step _ _ ASEM2 c oτ c' δ2 (a, None) δ2'
      | Some (inl ρ1) =>
          @asem_valid_evolution_step _ _ ASEM1 c oτ c' δ1 (a, Some ρ1) δ1' /\
         if (is_act2_dec a)
         then @asem_valid_evolution_step _ _ ASEM2 c oτ c' δ2 (a, None) δ2'
         else δ2' = δ2
      | Some (inr ρ2) =>
          @asem_valid_evolution_step _ _ ASEM2 c oτ c' δ2 (a, Some ρ2) δ2' /\
         if (is_act1_dec a)
         then @asem_valid_evolution_step _ _ ASEM1 c oτ c' δ1 (a, None) δ1'
         else δ1' = δ1
      end
      . 

  Let prod_asem_preGS Σ := (@asem_preGS _ _ ASEM1 Σ) * (@asem_preGS _ _ ASEM2 Σ). 
  Let prod_asem_GS Σ := (@asem_GS _ _ ASEM1 Σ) * (@asem_GS _ _ ASEM2 Σ).
  Let prod_asem_Σ := #[@asem_Σ _ _ ASEM1; @asem_Σ _ _ ASEM2]. 

  Lemma prod_asems_subG Σ:
    subG prod_asem_Σ Σ → prod_asem_preGS Σ.
  Proof using. 
    simpl. intros.
    apply subG_inv in H as [??].
    split; eapply asem_Σ_subG; solve_inG. 
  Qed. 

  Let prod_asem_init_param := @asem_init_param _ _ ASEM1 * @asem_init_param _ _ ASEM2.
  Let prod_asem_is_init c (s: amSt PM) := asem_is_init_st c s.1 /\ asem_is_init_st c s.2.

  Definition prod_asem_init_resource `{pG: prod_asem_GS Σ}
    (s: amSt PM) (p: prod_asem_init_param): iProp Σ :=
    asem_init_resource s.1 p.1 (asem_GS0 := pG.1) ∗
    asem_init_resource s.2 p.2 (asem_GS0 := pG.2)
  .

  Definition prod_asem_msi `{pG: prod_asem_GS Σ}
    (τ: cfg Λ) (p: amSt PM): iProp Σ :=
    @asem_msi _ _ ASEM1 _ pG.1 τ p.1 ∗ @asem_msi _ _ ASEM2 _ pG.2 τ p.2.

  Lemma prod_asem_initialization Σ {pG: prod_asem_preGS Σ}:
    forall (s1: amSt PM) (σ: cfg Λ) (p: prod_asem_init_param)
      (INIT_ST: prod_asem_is_init σ s1),
      ⊢ (|==> ∃ eGS: prod_asem_GS Σ,
             prod_asem_init_resource s1 p (pG := eGS) ∗ 
             prod_asem_msi σ s1 (pG := eGS)).
  Proof using.
    intros [s1 s2] σ [p1 p2] [??]. iStartProof. 
    iMod (@asem_initialization _ _ ASEM1 _ pG.1 s1 σ p1) as "(%g1&I1&M1)"; [done| ].
    iMod (@asem_initialization _ _ ASEM2 _ pG.2 s2 σ p2) as "(%g2&I2&M2)"; [done| ].
    iModIntro. iExists (g1, g2). iFrame.
  Qed.


  Program Definition ProdASEM: ActionSubEM Λ PM := {|
    asem_Σ := #[@asem_Σ _ _ ASEM1; @asem_Σ _ _ ASEM2];
    asem_valid_evolution_step := prod_asem_valid_evolution_step;
    asem_initialization := prod_asem_initialization;
  |}.
  Next Obligation.
    simpl. intros.
    apply subG_inv in H as [??].
    split; eapply asem_Σ_subG; solve_inG. 
  Qed.


End ProdASEM.
