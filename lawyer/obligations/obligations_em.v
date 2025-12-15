From iris.proofmode Require Import tactics.
From stdpp Require Import namespaces.
From trillium.program_logic Require Import language execution_model.
From iris.base_logic Require Import ghost_map.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat.
From fairness Require Import fairness locales_helpers.
From lawyer.obligations Require Import obligations_model obls_utils obligations_resources obligations_wf.


Section ObligationsEM.

  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}
    `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}
  .

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context {Λ: language}.
  Let Locale := locale Λ.

  Context {LIM_STEPS: nat}.
  Context {OP: ObligationsParams Degree Level Locale LIM_STEPS}.
  Let OM := ObligationsModel.

  Definition threads_own_obls (c: cfg Λ) (δ: mstate OM) :=
    locales_of_cfg c = dom $ ps_obls δ. 
    
  Lemma locale_nofork_step_obls_pres c1 c2 τ θ δ1 δ2
    (STEP: locale_step c1 (Some τ) c2)
    (TH_OWN: threads_own_obls c1 δ1)
    (TRANS: progress_step δ1 θ δ2)
    (NOFORK: locales_of_cfg c2 = locales_of_cfg c1)
    :
    threads_own_obls c2 δ2.
  Proof.
    destruct c1 as [tp1 σ1], c2 as [tp2 σ2].
    red. rewrite NOFORK.
    symmetry. pattern δ2. eapply pres_by_loc_step_implies_progress.
    { eapply @loc_step_dom_obls_pres. }
    2: { eauto. }
    congruence. 
  Qed.
      
  Definition obls_cfg_corr (σ: cfg Λ) (δ: mstate OM) :=
      threads_own_obls σ δ /\ dom_phases_obls δ. 

  Definition obls_valid_evolution_step
    (σ1: cfg Λ) (oζ: olocale Λ) (σ2: cfg Λ)
    (δ1: mstate OM) (ℓ: mlabel OM) (δ2: mstate OM) :=
      locale_step σ1 oζ σ2 /\
      mtrans δ1 ℓ δ2 /\
      oζ = Some ℓ /\
      obls_cfg_corr σ2 δ2
  .

  Definition obls_si `{!ObligationsGS Σ} (σ: cfg Λ) (δ: mstate OM): iProp Σ :=
      obls_msi δ ∗ ⌜ obls_cfg_corr σ δ ⌝.

  Definition obls_ti `{!ObligationsGS Σ} (etr: execution_trace Λ) (omtr: auxiliary_trace OM) := 
    obls_si (trace_last etr) (trace_last omtr).

  Definition obls_init_resource `{!ObligationsGS Σ}
    (δ: mstate OM) (_: unit): iProp Σ :=
    ([∗ mset] '(π, d) ∈ (ps_cps δ), cp π d) ∗    
    own obls_sigs (◯ (sig_map_repr $ ps_sigs δ)) ∗
    own obls_obls (◯ (obls_map_repr $ ps_obls δ)) ∗
    own obls_eps (◯ (eps_repr $ ps_eps δ)) ∗
    ([∗ map] τ↦π ∈ ps_phases δ, th_phase_eq τ π) ∗
    exc_lb (ps_exc_bound δ)
  .

  Definition obls_is_init_st (σ: cfg Λ) (δ: mstate OM) :=
    (* exists τ0, *)
    (*   let R := {[ τ0 ]} in *)
    (*   locales_of_cfg σ = R /\ dom $ ps_obls δ = R /\  *)
    (*   om_st_wf δ. *)
      locales_of_cfg σ = dom (ps_obls δ) /\
      om_st_wf δ.

  Lemma obls_resources_init Σ {PRE: ObligationsPreGS Σ}:
    ∀ s1 σ p (INIT: obls_is_init_st σ s1),
        ⊢ |==> ∃ eGS: ObligationsGS Σ, obls_init_resource s1 p ∗ obls_ti {tr[ σ ]} {tr[ s1 ]}.
  Proof using.
    clear H1 H0 H. 
    simpl. intros δ σ ? INIT. iStartProof.
    iMod (own_alloc (● (cps_repr $ ps_cps  δ) ⋅ ◯ _)) as (?) "[CPa CPf]".
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (sig_map_repr (ps_sigs δ)) ⋅ ◯ _)) as (?) "[SIGSa SIGSf]".
    { apply auth_both_valid_2; [| reflexivity].
      rewrite /sig_map_repr.
      intros s. destruct lookup eqn:L; [| done].
      apply lookup_fmap_Some in L. 
      destruct L as ([l b]&<-&?).
      done. }
    iMod (own_alloc (● (obls_map_repr $ ps_obls δ) ⋅ ◯ _)) as (?) "[OBLSa OBLSf]". 
    { apply auth_both_valid_discrete. split; [reflexivity| ].
      intros τ. rewrite lookup_fmap. 
      by destruct lookup. }
    iMod (own_alloc (● (eps_repr $ ps_eps δ) ⋅ ◯ _)) as (?) "[EPSa EPSf]". 
    { by apply auth_both_valid_2. }

    iMod (ghost_map_alloc (wrap_phase <$> ps_phases δ)) as (?) "[PHa PHf]".
    iMod (own_alloc (●MN (ps_exc_bound δ) ⋅ mono_nat_lb _)) as (?) "[LBa LBf]".
    { apply mono_nat_both_valid. reflexivity. }
    iModIntro. iExists {| obls_pre := PRE; |}.
    rewrite big_sepM_fmap. iFrame.

    rewrite /cps_repr. iSplitL.
    { by iApply cps_mset. } 

    iPureIntro. 
    red in INIT. destruct INIT as (?&?).
    red. rewrite /threads_own_obls /dom_phases_obls.
    erewrite om_wf_dpo; eauto.
  Qed.
  
  Definition ObligationsEM: ExecutionModel Λ OM :=
    {| 
      em_Σ := obls_Σ;
      em_valid_evolution_step := obls_valid_evolution_step;
      em_thread_post Σ `{!ObligationsGS Σ} :=
        fun τ _ => (obls τ ∅)%I;
      em_initialization := obls_resources_init;
    |}.

  Definition init_phases (n: nat): list Phase :=
    (fun i => ext_phase π0 i) <$> seq 0 n.

  Definition init_phases_asg (c: cfg Λ) :=
    zip (elements $ locales_of_cfg c) (init_phases (size $ locales_of_cfg c)). 

  Definition init_om_state (c: cfg Λ) (degs: gmultiset Degree) (eb: nat)
    : mstate OM := {|
      ps_cps := mset_map (pair π0) degs;
      ps_sigs := ∅;
      ps_obls := gset_to_gmap ∅ (locales_of_cfg c);
      ps_eps := ∅;
      ps_phases := list_to_map $ init_phases_asg c;
      ps_exc_bound := eb;
  |}.

  Lemma init_om_thown (c: cfg Λ) ds eb:
    threads_own_obls c (init_om_state c ds eb).
  Proof.
    red. simpl. by rewrite dom_gset_to_gmap.
  Qed.

  Lemma len_init_phases_cfg c:
    length (init_phases (size (locales_of_cfg c))) = length (elements (locales_of_cfg c)).
  Proof using. 
     rewrite /init_phases. rewrite length_fmap.
     by rewrite length_size List.length_seq.
  Qed.

  Lemma dom_ipa (c: cfg Λ):
    dom (list_to_map (init_phases_asg c): gmap (locale Λ) Phase) = locales_of_cfg c.
  Proof using. 
    rewrite dom_list_to_map_L. simpl.
    rewrite fst_zip.
    { by rewrite list_to_set_elements_L. }
    by rewrite len_init_phases_cfg. 
  Qed. 

  Lemma init_phases_helper e σ:
    list_to_map $ init_phases_asg ([e], σ) = ({[locale_of [] e := ext_phase π0 0]}: gmap Locale Phase).
  Proof using.
    rewrite /init_phases_asg. 
    rewrite locales_of_cfg_singleton. rewrite size_singleton.
    rewrite elements_singleton. simpl.
    set_solver.
  Qed. 

  Lemma ipa_NoDup1 c: NoDup (init_phases_asg c).*1.
  Proof using. 
    rewrite fst_zip.
    - apply NoDup_elements.
    - by rewrite len_init_phases_cfg.
  Qed.

  Lemma ipa_NoDup2 c: NoDup (init_phases_asg c).*2. 
  Proof using.
    rewrite snd_zip.
    - rewrite /init_phases.
      apply NoDup_fmap_2; try apply _.
      apply NoDup_seq.
    - by rewrite len_init_phases_cfg.
  Qed.

  Lemma dpd_ipa c δ
    (PHS: ps_phases δ = list_to_map $ init_phases_asg c):
    dom_phases_disj δ.
  Proof using.
    red. destruct δ. simpl in *. rewrite PHS.
    destruct c as (es, σ). 
    pose proof (ipa_NoDup1 (es, σ)). pose proof (ipa_NoDup2 (es, σ)). 
    red. simpl. intros ????? X%elem_of_list_to_map Y%elem_of_list_to_map; eauto.
    apply elem_of_list_lookup_1 in X as (i&X).
    apply elem_of_list_lookup_1 in Y as (j&Y).
    apply zip_lookup_Some_1 in X as [? X].  
    apply zip_lookup_Some_1 in Y as [? Y]. 
    destruct (decide (i = j)).
    { congruence. }
    rewrite /init_phases in X, Y.
    apply list_lookup_fmap_Some in X as (?&?&->). 
    apply list_lookup_fmap_Some in Y as (?&?&->).
    apply phases_disj_forks.
    intros <-.
    pose proof (NoDup_seq 0 (size (locales_of_cfg (es, σ)))) as ND. eapply NoDup_alt in ND; eauto.
  Qed.

  Lemma cpb_init_phases_π0 c δ ds
    (PHS: ps_phases δ = list_to_map $ init_phases_asg c)
    (CPS: ps_cps δ = mset_map (pair π0) ds):
    cps_phase_bound δ.
  Proof using.
    red. destruct δ. simpl in *. rewrite PHS CPS. 
    intros (?&?&[??]& P). revert P. simpl.   
    rewrite elem_of_mset_map. simpl.
    intros (? & (?&[=]&?) & LT). subst.
    apply elem_of_list_to_map in H2.
    2: { apply ipa_NoDup1. }
    apply elem_of_zip_r in H2.
    rewrite /init_phases in H2. apply elem_of_list_fmap in H2 as (?&->&?).  
    pose proof (phase_lt_fork π0 x1) as LT'.
    apply strict_spec in LT.
    rewrite strict_spec in LT. destruct LT as [? N].
    apply N. apply LT'.
  Qed.

  Lemma init_om_st_wf c ds eb:
    om_st_wf (init_om_state c ds eb).
  Proof using.
    clear. 
    destruct c as [es σ].
    rewrite /init_om_state. split.
    - red. simpl. rewrite dom_ipa dom_gset_to_gmap. done. 
    - red. simpl.
      trans (∅: gset nat); set_solver. 
    - eapply dpd_ipa; eauto. 
    - eapply cpb_init_phases_π0; eauto. 
    - red. simpl. set_solver.
    - red. simpl.
      erewrite @flatten_gset_map_img_gtg_empty. done.  
    - red. simpl. 
      intros ???.
      destruct (_ !! τ1) eqn:X, (_ !! τ2) eqn:Y; simpl; try done.
      apply lookup_gset_to_gmap_Some in X as [? <-]. 
      apply lookup_gset_to_gmap_Some in Y as [? <-].
      done. 
  Qed. 

  Lemma init_om_state_init_multiple es σ ds eb:
    obls_is_init_st (es, σ) (init_om_state ((es, σ)) ds eb).
  Proof.
    red. 
    rewrite dom_gset_to_gmap. split; eauto. 
    apply init_om_st_wf. 
  Qed.

  Lemma init_om_state_init e σ ds eb:
    obls_is_init_st ([e], σ) (init_om_state (([e], σ)) ds eb).
  Proof.
    apply init_om_state_init_multiple.
  Qed.

  From lawyer Require Import sub_action_em obligations_am action_model. 
  Context `{Inhabited Locale}. 
  Let OAM := ObligationsAM. 

  Definition obls_ves_wrapper:
    cfg Λ → olocale Λ → cfg Λ → 
    amSt OAM → Action * option (amRole OAM) → amSt OAM → Prop :=

    fun c1 oτ c2 δ1 (aoτ: Action * olocale Λ) δ2 =>
      let '(a, oρ) := aoτ in
      from_option (fun ρ => obls_valid_evolution_step c1 oτ c2 δ1 ρ δ2) False oρ /\
      a = obls_act.

  Definition obls_asem_mti `{!ObligationsGS Σ}
    (etr: execution_trace Λ) (omtr: finite_trace (amSt OAM) (Action * option (amRole OAM))) :=
    obls_si (trace_last etr) (trace_last omtr).

  Lemma obls_asem_resources_init Σ {PRE: ObligationsPreGS Σ}:
    ∀ s1 σ p (INIT: obls_is_init_st σ s1),
        ⊢ |==> ∃ eGS: ObligationsGS Σ, obls_init_resource s1 p ∗ obls_asem_mti {tr[ σ ]} {tr[ s1 ]}.
  Proof using. by apply obls_resources_init. Qed.

  Definition ObligationsASEM: ActionSubEM Λ (ObligationsAM) :=
    {| 
      asem_Σ := obls_Σ;
      asem_valid_evolution_step := obls_ves_wrapper;
      asem_initialization := obls_asem_resources_init;
    |}.
       
End ObligationsEM.
