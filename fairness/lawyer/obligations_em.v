From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat.
From trillium.fairness Require Import fairness locales_helpers execution_model.
From trillium.fairness.lawyer Require Import obligations_model obls_utils obligations_resources. 



Section ObligationsEM.

  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}
    `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}
  .

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  (* Context {Locale: Type}. *)
  Context {Λ: language}.
  Context `{Countable (locale Λ)}.
  Let Locale := locale Λ.

  Context {LIM_STEPS: nat}.
  Context (OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Let OM := ObligationsModel OP.

  Definition threads_own_obls (c: cfg Λ) (δ: mstate OM) :=
    locales_of_cfg c = dom $ ps_obls OP δ. 
    
  Lemma locale_nofork_step_obls_pres c1 c2 τ θ δ1 δ2
    (STEP: locale_step c1 (Some τ) c2)
    (TH_OWN: threads_own_obls c1 δ1)
    (TRANS: progress_step OP δ1 θ δ2)
    (NOFORK: locales_of_cfg c2 = locales_of_cfg c1)
    :
    threads_own_obls c2 δ2.
  Proof.
    destruct c1 as [tp1 σ1], c2 as [tp2 σ2].
    red. rewrite NOFORK.
    eapply progress_step_obls_pres in TRANS; [| apply obls_eq_init].
    rewrite TRANS. done. 
  Qed.
      
  Definition obls_valid_evolution_step
    (σ1: cfg Λ) (oζ: olocale Λ) (σ2: cfg Λ)
    (δ1: mstate OM) (ℓ: mlabel OM) (δ2: mstate OM) :=
      mtrans δ1 ℓ δ2 /\
      oζ = Some ℓ                
  .

  Definition obls_si `{!ObligationsGS OP Σ}
    (σ: cfg Λ) (δ: mstate OM): iProp Σ :=
      obls_msi _ δ ∗
      ⌜ threads_own_obls σ δ ⌝ ∗
      ⌜ dom_phases_obls OP δ ⌝
  . 

  Definition obls_init_resource `{!ObligationsGS OP Σ}
    (δ: mstate OM) (_: unit): iProp Σ :=
    own (obls_cps _) (◯ (cps_repr _ $ ps_cps _ δ)) ∗
    own (obls_sigs _) (◯ (sig_map_repr $ ps_sigs _ δ)) ∗
    own (obls_obls _) (◯ (obls_map_repr $ ps_obls _ δ)) ∗
    own (obls_eps _) (◯ (eps_repr _ $ ps_eps _ δ)) ∗
    own (obls_phs _) (◯ (phases_repr $ ps_phases _ δ)) ∗
    own (obls_exc_lb _) (◯MN (ps_exc_bound _ δ))
  .

  Definition obls_is_init_st (σ: cfg Λ) (δ: mstate OM) :=
    exists τ0,
      let R := {[ τ0 ]} in
      locales_of_cfg σ = R /\ dom $ ps_obls OP δ = R /\ dom $ ps_phases OP δ = R.

  Lemma obls_resources_init Σ {PRE: ObligationsPreGS OP Σ}:
    ∀ s1 σ p (INIT: obls_is_init_st σ s1),
        ⊢ |==> ∃ eGS: ObligationsGS OP Σ, obls_init_resource s1 p ∗ obls_si σ s1. 
  Proof using.
    clear H1 H0 H. 
    simpl. intros δ σ ? INIT. iStartProof.
    iMod (own_alloc (● (cps_repr _ $ ps_cps _  δ) ⋅ ◯ _)) as (?) "[CPa CPf]".
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (sig_map_repr (ps_sigs _ δ)) ⋅ ◯ _)) as (?) "[SIGSa SIGSf]".
    { apply auth_both_valid_2; [| reflexivity].
      rewrite /sig_map_repr.
      intros s. destruct lookup eqn:L; [| done].
      apply lookup_fmap_Some in L. 
      destruct L as ([l b]&<-&?).
      done. }
    iMod (own_alloc (● (obls_map_repr $ ps_obls _ δ) ⋅ ◯ _)) as (?) "[OBLSa OBLSf]". 
    { apply auth_both_valid_discrete. split; [reflexivity| ].
      intros τ. rewrite lookup_fmap. 
      by destruct lookup. }
    iMod (own_alloc (● (eps_repr _ $ ps_eps _ δ) ⋅ ◯ _)) as (?) "[EPSa EPSf]". 
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (phases_repr $ ps_phases _ δ) ⋅ ◯ _)) as (?) "[PHa PHf]". 
    { apply auth_both_valid_2; [| reflexivity].
      rewrite /phases_repr. intros τ. destruct lookup eqn:L; [| done].
      rewrite lookup_fmap_Some in L. destruct L as (? & <- & L). done. }
    iMod (own_alloc (●MN (ps_exc_bound _ δ) ⋅ mono_nat_lb _)) as (?) "[LBa LBf]".
    { apply mono_nat_both_valid. reflexivity. }
    iModIntro. iExists {| obls_pre := PRE; |}.
    iFrame.
    iPureIntro. 
    red in INIT. destruct INIT as (?&?&?&?). set_solver.  
  Qed.
    

  Definition ObligationsEM: ExecutionModel Λ OM :=
    {| 
      em_Σ := obls_Σ OP;
      em_valid_evolution_step := obls_valid_evolution_step;
      em_thread_post Σ `{!ObligationsGS OP Σ} :=
        fun τ => (obls _ τ ∅)%I;
      em_initialization := obls_resources_init;
    |}.

  From trillium.fairness.lawyer Require Import sub_action_em obligations_am action_model. 
  Context `{Inhabited Locale}. 
  Let OAM := ObligationsAM OP. 

  Definition obls_ves_wrapper:
    cfg Λ → olocale Λ → cfg Λ → 
    amSt OAM → Action * option (amRole OAM) → amSt OAM → Prop :=

    fun c1 oτ c2 δ1 (aoτ: Action * olocale Λ) δ2 =>
      let '(a, oρ) := aoτ in
      from_option (fun ρ => obls_valid_evolution_step c1 oτ c2 δ1 ρ δ2) False oρ /\
      a = obls_act. 

  Definition ObligationsASEM: ActionSubEM Λ (ObligationsAM OP) :=
    {| 
      asem_Σ := obls_Σ OP;
      asem_valid_evolution_step := obls_ves_wrapper;
      asem_initialization := obls_resources_init;
    |}.

End ObligationsEM.


