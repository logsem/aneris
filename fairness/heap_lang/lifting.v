From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.prelude Require Import classical_instances.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.fairness Require Export fairness resources fair_termination fairness_finiteness fuel fuel_termination.
From trillium.program_logic Require Import ectx_lifting.
From trillium.fairness.heap_lang Require Export lang.
From trillium.fairness.heap_lang Require Import tactics notation.
Set Default Proof Using "Type".

Canonical Structure ModelO (M : FairModel) := leibnizO M.
Canonical Structure RoleO (M : FairModel) := leibnizO (M.(fmrole)).

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

Section adequacy.

Lemma posts_of_empty_mapping `{heapGS Σ M} (e1 e: expr) v (tid : nat) (tp : list expr):
  tp !! tid = Some e ->
  to_val e = Some v ->
  posts_of tp ((λ (_ : val), 0%nat ↦M ∅) ::  (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) tp)))) -∗
  tid ↦M ∅.
Proof.
  intros Hsome Hval. simpl.

  rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (λ _: val, tid ↦M ∅)) _) //.
  apply elem_of_list_omap.
  exists (e, (λ _: val, tid ↦M ∅)); split; last first.
  - simpl. apply fmap_Some. exists v. split; done.
  - destruct tp as [|e1' tp]; first set_solver. simpl.
    apply elem_of_cons.
    destruct tid as [|tid]; [left|right]; first by simpl in Hsome; simplify_eq.
    apply elem_of_lookup_zip_with. eexists tid, e, _. do 2 split =>//.
    rewrite /locale_of /=.
    rewrite list_lookup_fmap fmap_Some. simpl in Hsome.
    exists (e1 :: take tid tp, e). rewrite drop_0. split.
    + erewrite prefixes_from_lookup =>//.
    + rewrite /locale_of /= take_length_le //.
      assert (tid < length tp)%nat; last lia. by eapply lookup_lt_Some.
Qed.

(* Local Hint Resolve tid_step_tp_length_heap: core. *)

Lemma from_locale_from_lookup tp0 tp tid e :
  from_locale_from tp0 tp tid = Some e <-> (tp !! (tid - length tp0)%nat = Some e ∧ (length tp0 <= tid)%nat).
Proof.
  split.
  - revert tp0 tid. induction tp as [| e1 tp1 IH]; intros tp0 tid.
    { unfold from_locale. simpl. done. }
    unfold from_locale. simpl.
    destruct (decide (locale_of tp0 e1 = tid)).
    + intros ?; simplify_eq. rewrite /locale_of /= Nat.sub_diag.
      split; [done|lia].
    + intros [H Hlen]%IH. rewrite app_length /= in H.
      rewrite app_length /= in Hlen.
      destruct tid as [|tid]; first lia.
      assert (Heq1 : (length tp0 + 1 = S (length tp0))%nat) by lia.
      rewrite Heq1 in Hlen.
      assert (length tp0 ≤ tid)%nat by lia.
      assert (Heq : (S tid - length tp0)%nat = (S ((tid - (length tp0))))%nat) by lia.
      rewrite Heq /=. split.
      * rewrite -H. f_equal. lia.
      * transitivity tid; try lia. assumption.
  - revert tp0 tid. induction tp as [|e1 tp1 IH]; intros tp0 tid.
    { set_solver. }
    destruct (decide (tid = length tp0)) as [-> | Hneq].
    + rewrite Nat.sub_diag /=. intros  [? _]. simplify_eq.
      rewrite decide_True //.
    + intros [Hlk Hlen]. assert (length tp0 < tid)%nat as Hle by lia.
      simpl. rewrite decide_False //. apply IH. split.
      * assert (tid - length tp0 = S ((tid - 1) - length tp0))%nat as Heq by lia.
        rewrite Heq /= in Hlk. rewrite -Hlk app_length /=. f_equal; lia.
      * rewrite app_length /=. apply Nat.le_succ_l in Hle. rewrite Nat.add_comm //.
Qed.

Lemma from_locale_lookup tp tid e :
  from_locale tp tid = Some e <-> tp !! tid = Some e.
Proof.
  assert (from_locale tp tid = Some e <-> (tp !! tid = Some e ∧ 0 ≤ tid)%nat) as H; last first.
  { split; intros ?; apply H; eauto. split; [done|lia]. }
  unfold from_locale. replace (tid) with (tid - length (A := expr) [])%nat at 2;
    first apply from_locale_from_lookup. simpl; lia.
Qed.

Theorem heap_lang_continued_simulation_fair_termination {FM : FairModel}
        `{FairTerminatingModel FM} {LM:LiveModel heap_lang FM} ξ a1 r1 extr :
  continued_simulation
    (sim_rel_with_user LM ξ)
    ({tr[trfirst extr]}) ({tr[initial_ls (LM := LM) a1 r1]}) →
  extrace_fairly_terminating extr.
Proof.
  apply continued_simulation_fair_termination.
  - intros ?? contra. inversion contra.
    simplify_eq. inversion H2.
  - by intros ex atr [[??]?].
  - by intros ex atr [[??]?].
Qed.

Definition rel_always_holds {Σ} `{LM:LiveModel heap_lang M} `{!heapGS Σ LM}
           (s:stuckness) (ξ : execution_trace heap_lang → finite_trace M
                  (option $ fmrole M) → Prop) (c1:cfg heap_lang)
           (c2:live_model_to_model LM) : iProp Σ :=
  ∀ ex atr c,
    ⌜valid_system_trace ex atr⌝ -∗
    ⌜trace_starts_in ex c1⌝ -∗
    ⌜trace_starts_in atr c2⌝ -∗
    ⌜trace_ends_in ex c⌝ -∗
    ⌜∀ ex' atr' oζ ℓ, trace_contract ex oζ ex' →
                      trace_contract atr ℓ atr' →
                      ξ ex' (map_underlying_trace atr')⌝ -∗
    ⌜∀ e2, s = NotStuck → e2 ∈ c.1 → not_stuck e2 c.2⌝ -∗
    state_interp ex atr -∗
    posts_of c.1 ((λ _, 0%nat ↦M ∅) :: ((λ '(tnew, e), fork_post (locale_of tnew e)) <$> (prefixes_from c1.1 (drop (length c1.1) c.1)))) -∗
    |={⊤, ∅}=> ⌜ξ ex (map_underlying_trace atr)⌝.

Theorem strong_simulation_adequacy Σ `(LM:LiveModel heap_lang M)
    `{!heapGpreS Σ LM} (s: stuckness) (e1 : expr) σ1 (s1: M) (FR: gset _)
    (ξ : execution_trace heap_lang → finite_trace M (option $ fmrole M) →
         Prop) :
  rel_finitary (sim_rel_with_user LM ξ) →
  live_roles M s1 ≠ ∅ ->
  (∀ `{Hinv : !heapGS Σ LM},
    ⊢ |={⊤}=>
       (* state_interp (trace_singleton ([e1], σ1)) (trace_singleton (initial_ls (LM := LM) s1 0%nat)) ∗ *)
       ([∗ map] l ↦ v ∈ heap σ1, mapsto l (DfracOwn 1) v) -∗
       frag_model_is s1 -∗
       frag_free_roles_are (FR ∖ live_roles _ s1) -∗
       has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1)) ={⊤}=∗
       WP e1 @ s; locale_of [] e1; ⊤ {{ v, 0%nat ↦M ∅ }} ∗
       rel_always_holds s ξ ([e1], σ1) (initial_ls (LM := LM) s1 0%nat)) ->
  continued_simulation (sim_rel_with_user LM ξ) (trace_singleton ([e1], σ1)) (trace_singleton (initial_ls (LM := LM) s1 0%nat)).
Proof.
  intros Hfin Hfevol H.
  apply (wp_strong_adequacy heap_lang LM Σ s); first by eauto.
  iIntros (?) "".
  iMod (gen_heap_init (heap σ1)) as (genheap)" [Hgen [Hσ _]]".
  iMod (model_state_init s1) as (γmod) "[Hmoda Hmodf]".
  iMod (model_mapping_init s1) as (γmap) "[Hmapa Hmapf]".
  iMod (model_fuel_init s1) as (γfuel) "[Hfuela Hfuelf]".
  iMod (model_free_roles_init s1 (FR ∖ live_roles _ s1)) as (γfr) "[HFR Hfr]".
  set (distG :=
         {|
          heap_fairnessGS := {|
                              fairness_model_name := γmod;
                              fairness_model_mapping_name := γmap;
                              fairness_model_fuel_name := γfuel;
                              fairness_model_free_roles_name := γfr;
                              |}
         |}).
  iMod (H distG) as "Hwp". clear H.
  iExists state_interp, (λ _, 0%nat ↦M ∅)%I, fork_post.
  iSplitR.
  { unfold config_wp. iIntros "!>!>" (???????) "?". done. }
  (* iAssert (state_interp with "[Hgen Hmoda Hmodf Hmapa Hfuela HFR] Hfr [Hfuelf Hmapf]"). *)
  (* { iFrame "Hmodf". unfold state_interp. simpl. iFrame. iExists {[ 0%nat := (live_roles Mdl s1) ]}, _. *)
  (*   iSplitL "Hfuela"; first by rewrite /auth_fuel_is /= fmap_gset_to_gmap //. *)
  (*   iSplitL "Hmapa"; first by rewrite /auth_mapping_is /= map_fmap_singleton //. *)
  (*   iSplit; first done. *)
  (*   iSplit; iPureIntro; [|split]. *)
  (*   - intros ρ tid. rewrite lookup_gset_to_gmap_Some. *)
  (*     setoid_rewrite lookup_singleton_Some. split; naive_solver. *)
  (*   - intros tid Hlocs. rewrite lookup_singleton_ne //. compute in Hlocs. set_solver. *)
  (*   - rewrite dom_gset_to_gmap. set_solver. } *)
  iSpecialize ("Hwp" with "Hσ Hmodf Hfr [Hfuelf Hmapf]").
  { rewrite /has_fuels /frag_mapping_is /= map_fmap_singleton. iFrame.
    iAssert ([∗ set] ρ ∈ live_roles M s1, ρ ↦F (LM.(lm_fl) s1))%I with "[Hfuelf]" as "H".
    - unfold frag_fuel_is. setoid_rewrite map_fmap_singleton.
      rewrite -big_opS_own //. iApply (own_proper with "Hfuelf").
      rewrite -big_opS_auth_frag. f_equiv. rewrite gset_to_gmap_singletons //.
    - rewrite dom_gset_to_gmap. iFrame.
      iApply (big_sepS_mono with "H"). iIntros (ρ Hin) "H".
      iExists _. iFrame. iPureIntro. apply lookup_gset_to_gmap_Some. done. }
  iDestruct "Hwp" as ">[Hwp H]".
  iModIntro. iFrame "Hwp".
  iSplitL "Hgen Hmoda Hmapa Hfuela HFR".
  { unfold state_interp. simpl. iFrame. iExists {[ 0%nat := (live_roles M s1) ]}, _.
    iSplitL "Hfuela"; first by rewrite /auth_fuel_is /= fmap_gset_to_gmap //.
    iSplitL "Hmapa"; first by rewrite /auth_mapping_is /= map_fmap_singleton //.
    iSplit; first done.
    iSplit; iPureIntro; [|split].
    - intros ρ tid. rewrite lookup_gset_to_gmap_Some.
      setoid_rewrite lookup_singleton_Some. split; naive_solver.
    - intros tid Hlocs. rewrite lookup_singleton_ne //. compute in Hlocs. set_solver.
    - rewrite dom_gset_to_gmap. set_solver. }
  iIntros (ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr Hstuck Hequiv) "Hsi Hposts".
  assert ( ∀ (ex' : finite_trace (cfg heap_lang) (olocale heap_lang)) (atr' : auxiliary_trace LM) (oζ : olocale heap_lang) (ℓ : mlabel LM),
   trace_contract ex oζ ex' → trace_contract atr ℓ atr' → ξ ex' (map_underlying_trace atr')) as Hcontr'.
  { intros ex' atr' oζ ℓ H1 H2. cut (sim_rel_with_user LM ξ ex' atr'); eauto. rewrite /sim_rel_with_user. intros [??]. done. }
  iSpecialize ("H" $! ex atr c Hvalex Hstartex Hstartatr Hendex Hcontr' Hstuck).
  unfold sim_rel_with_user.
  iAssert (|={⊤}=> ⌜ξ ex (map_underlying_trace atr)⌝ ∗ state_interp ex atr ∗ posts_of c.1
               ((λ _ : language.val heap_lang, 0%nat ↦M ∅)
                :: ((λ '(tnew, e), fork_post (language.locale_of tnew e)) <$>
                    prefixes_from [e1] (drop (length [e1]) c.1))))%I with "[Hsi H Hposts]" as "H".
  { iApply fupd_plain_keep_l. iFrame. iIntros "[Hsi Hposts]".
    iSpecialize ("H" with "Hsi Hposts").
    by iApply fupd_plain_mask_empty. }
  iMod "H" as "[H1 [Hsi Hposts]]".
  destruct ex as [c'|ex' tid (e, σ)].
  - (* We need to prove that the initial state satisfies the property *)
    destruct atr as [δ|???]; last by inversion Hvalex. simpl.
    have Heq1 := trace_singleton_ends_in_inv _ _ Hendex.
    have Heq3 := trace_singleton_starts_in_inv _ _ Hstartex.
    have Heq4 := trace_singleton_starts_in_inv _ _ Hstartex.
    pose proof (trace_singleton_starts_in_inv _ _ Hstartatr). simpl.
    simplify_eq.
    iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".
    assert (∀ (ρ : fmrole M) (tid : nat),
               ls_mapping (initial_ls (LM := LM) s1 0%nat) !! ρ = Some tid →
               is_Some (([e1], σ1).1 !! tid)) as HA.
    { simpl. intros ρ tid Hsome. apply lookup_gset_to_gmap_Some in Hsome as [??].
      simplify_eq. by eexists _. }
    iSplit; last done. iClear "H1".
    iSplit; first done.
    destruct (to_val e1) as [v1|] eqn:Heq.
    + iSplit.
      { iPureIntro. intros ρ tid Hinit.
        simpl in *. apply lookup_gset_to_gmap_Some in Hinit as [_ <-].
        rewrite /from_locale //. }
      iIntros (tid e Hsome Hnoval ρ). destruct tid; last done.
      simpl in Hsome. compute in Hsome. simplify_eq. simpl.
      iAssert (0%nat ↦M ∅) with "[Hposts]" as "Hem".
      { rewrite /= Heq /fmap /=. by iDestruct "Hposts" as "[??]". }
      iDestruct "Hsi" as "(_&_&Hsi)".
      iDestruct "Hsi" as "(%m&%FR'&Hfuela&Hmapa&HFR&%Hinvmap&%Hsmall&Hmodel&HfrFR)".
      iDestruct (frag_mapping_same 0%nat m with "[Hmapa] Hem") as "%H"; first done.
      iPureIntro. by eapply no_locale_empty.
    + iSplit; iPureIntro.
      { simpl. intros ρ tid Hsome. apply lookup_gset_to_gmap_Some in Hsome as [??].
        simplify_eq. by eexists _. }
      intros tid e Hsome Hval' ρ.
      destruct tid as [|tid]; rewrite /from_locale /= in Hsome; by simplify_eq.
  - (* We need to prove that that the property is preserved *)
    destruct atr as [|atr' ℓ δ]; first by inversion Hvalex.
    (* rewrite (trace_singleton_ends_in_inv _ _ Hendex); last exact unit. *)
    specialize (Hcontr ex' atr' tid ℓ).
    have H: trace_contract (trace_extend ex' tid (e, σ)) tid ex' by eexists.
    have H': trace_contract (trace_extend atr' ℓ δ) ℓ atr' by eexists.
    specialize (Hcontr H H') as Hvs. clear H H' Hcontr.
    (* destruct Hvalex as (Hlm & Hlt & Hts). *)
    have H: trace_ends_in ex' (trace_last ex') by eexists.
    have H': trace_ends_in atr' (trace_last atr') by eexists.
    iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".
    apply (trace_singleton_ends_in_inv (L := unit)) in Hendex.
    simpl in *. simplify_eq.
    iDestruct "Hsi" as "((%&%&%Htids)&_&Hsi)".
    iDestruct "Hsi" as "(%m&%&Hfuela&Hmapa&?&%Hinvmap&%Hsmall&Hmodel&?)".
    iSplit; [|done].
    iSplit; [done|].
    iSplit.
    + iPureIntro. intros ρ tid' Hsome. simpl. unfold tids_smaller in Htids. eapply Htids. done.
    + iIntros (tid' e' Hsome Hnoval ρ). simpl.
      iAssert (tid' ↦M ∅) with "[Hposts]" as "H".
      { destruct (to_val e') as [?|] eqn:Heq; last done.
        iApply posts_of_empty_mapping => //.
        apply from_locale_lookup =>//. }
      iDestruct (frag_mapping_same tid' m with "Hmapa H") as "%Hlk".
      { rewrite /auth_mapping_is. iPureIntro. by eapply no_locale_empty. }
Qed.

Theorem simulation_adequacy Σ `(LM:LiveModel heap_lang M) `{!heapGpreS Σ LM} (s: stuckness) (e1 : expr) σ1 (s1: M) (FR: gset _):
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles M s1 ≠ ∅ ->
  (* The initial configuration satisfies certain properties *)
  (* A big implication, and we get back a Coq proposition *)
  (* For any proper Aneris resources *)
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
        frag_free_roles_are (FR ∖ live_roles _ s1) -∗
        has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  @continued_simulation
    heap_lang
    LM
    (sim_rel LM)
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls (LM := LM) s1 0%nat)).
Proof.
  intros Hfevol Hne H.
  assert (sim_rel LM = sim_rel_with_user LM (λ _ _, True)) as Heq.
  { Require Import Coq.Logic.FunctionalExtensionality.
    Require Import Coq.Logic.PropExtensionality.
    do 2 (apply functional_extensionality_dep; intros ?).
    apply propositional_extensionality.
    unfold sim_rel_with_user. intuition. }

  rewrite Heq.
  apply (strong_simulation_adequacy Σ LM s _ _ _ FR) =>//.
  { rewrite -Heq. done. }
  iIntros (Hinv) "".
  iPoseProof (H Hinv) as ">H". iModIntro. iIntros "Hσ Hm Hfr Hf". iSplitR "".
  - iApply ("H" with "Hm Hfr Hf").
  - iIntros "!>%%%????????". iApply (fupd_mask_weaken ∅); first set_solver. by iIntros "_ !>".
Qed.

Theorem simulation_adequacy_inftraces Σ `(LM: LiveModel heap_lang M)
        `{!heapGpreS Σ LM} (s: stuckness) FR
        e1 σ1 (s1: M)
        (iex : inf_execution_trace heap_lang)
        (Hvex : valid_inf_exec (trace_singleton ([e1], σ1)) iex)
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM)  →
  live_roles M s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
     frag_model_is s1 -∗
         frag_free_roles_are (FR ∖ live_roles _ s1) -∗
         has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  exists iatr,
  @valid_inf_system_trace _ LM
    (@continued_simulation
       heap_lang
       LM
       (sim_rel LM))
    (trace_singleton ([e1], σ1))
    (trace_singleton (initial_ls (LM := LM) s1 0%nat))
    iex
    iatr.
Proof.
  intros Hfin Hlr Hwp.
  eexists.
  eapply produced_inf_aux_trace_valid_inf.
  Unshelve.
  - econstructor.
  - apply (simulation_adequacy Σ LM s _ _ _ FR) => //.
  - done.
Qed.

Definition heap_lang_extrace : Type := extrace heap_lang.

Theorem simulation_adequacy_traces Σ `(LM : LiveModel heap_lang M) `{!heapGpreS Σ LM} (s: stuckness) FR
        e1 (s1: M)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles M s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         frag_free_roles_are (FR ∖ live_roles _ s1) -∗
         has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  ∃ (auxtr : auxtrace LM), exaux_traces_match extr auxtr.
Proof.
  intros Hfin Hlr Hwp.
  have [iatr Hbig] : exists iatr,
      @valid_inf_system_trace
        heap_lang LM
        (@continued_simulation
           heap_lang
           LM
           (sim_rel LM))
        (trace_singleton ([e1], (trfirst extr).2))
        (trace_singleton (initial_ls (LM := LM) s1 0%nat))
        (from_trace extr)
        iatr.
  { apply (simulation_adequacy_inftraces _ _ s FR); eauto.
    eapply from_trace_preserves_validity; eauto; first econstructor.
    simpl. destruct (trfirst extr) eqn:Heq.
    simpl in Hexfirst. rewrite -Hexfirst Heq //. }
  exists (to_trace (initial_ls (LM := LM) s1 0%nat) iatr).
  eapply (valid_inf_system_trace_implies_traces_match (continued_simulation (sim_rel LM))); eauto.
  - by intros ? ? [? ?]%continued_simulation_rel.
  - by intros ? ? [? ?]%continued_simulation_rel.
  - apply from_trace_spec. simpl. destruct (trfirst extr) eqn:Heq. simplify_eq. f_equal.
    simpl in Hexfirst. rewrite -Hexfirst Heq //.
  - apply to_trace_spec.
Qed.

Theorem simulation_adequacy_model_trace Σ `(LM : LiveModel heap_lang M)
        `{!heapGpreS Σ LM} (s: stuckness) FR
        e1 (s1: M)
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles M s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         frag_free_roles_are (FR ∖ live_roles _ s1) -∗
         has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  ∃ (auxtr : auxtrace LM) mtr, exaux_traces_match extr auxtr ∧
                               upto_stutter ls_under Ul auxtr mtr.
Proof.
  intros Hfb Hlr Hwp.
  destruct (simulation_adequacy_traces
              Σ _ _ FR e1 s1 extr Hvex Hexfirst Hfb Hlr Hwp) as [auxtr Hmatch].
  destruct (can_destutter_auxtr extr auxtr) as [mtr Hupto] =>//.
  { intros ?? contra. inversion contra. done. }
  eauto.
Qed.

Theorem simulation_adequacy_terminate Σ `{LM:LiveModel heap_lang Mdl}
        `{!heapGpreS Σ LM} (s: stuckness)
        e1 (s1: Mdl) FR
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (∀ mtr : @mtrace Mdl, mtrace_fairly_terminating mtr) ->
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles Mdl s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
         frag_free_roles_are (FR ∖ live_roles _ s1) -∗
         has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (Mdl.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.
  intros Hterm Hfb Hlr Hwp Hvex Hfair.
  destruct (simulation_adequacy_model_trace
              Σ _ _ FR e1 s1 extr Hvex Hexfirst Hfb Hlr Hwp) as (auxtr&mtr&Hmatch&Hupto).
  destruct (infinite_or_finite extr) as [Hinf|] =>//.
  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair.
  have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.
  have Htermtr := Hterm mtr Hmtrvalid Hfairm.
  eapply exaux_preserves_termination =>//.
  eapply upto_stutter_finiteness =>//.
Qed.

Theorem simulation_adequacy_terminate_ftm Σ `{FairTerminatingModel M}
        `(LM : LiveModel heap_lang M)
        `{!heapGpreS Σ LM} (s: stuckness)
        e1 (s1: M) FR
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  (* The model has finite branching *)
  rel_finitary (sim_rel LM) →
  live_roles M s1 ≠ ∅ ->
  (∀ `{!heapGS Σ LM},
      ⊢ |={⊤}=>
        frag_model_is s1 -∗
        frag_free_roles_are (FR ∖ live_roles _ s1) -∗
        has_fuels (Σ := Σ) 0%nat (gset_to_gmap (LM.(lm_fl) s1) (M.(live_roles) s1))
        ={⊤}=∗ WP e1 @ s; 0%nat; ⊤ {{ v, 0%nat ↦M ∅ }}
  ) ->
  (* The coinductive pure coq proposition given by adequacy *)
  extrace_fairly_terminating extr.
Proof.
  eapply simulation_adequacy_terminate =>//.
  apply fair_terminating_traces_terminate.
Qed.

End adequacy.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
(* Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core. *)

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _) => apply alloc_fresh : core.
Local Hint Resolve to_of_val : core.

#[global] Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
#[global] Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

#[global] Instance rec_atomic s f x e : Atomic s (Rec f x e).
Proof. solve_atomic. Qed.
#[global] Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance injl_atomic s v : Atomic s (InjL (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance injr_atomic s v : Atomic s (InjR (Val v)).
Proof. solve_atomic. Qed.
(** The instance below is a more general version of [Skip] *)
#[global] Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
Proof. destruct f, x; solve_atomic. Qed.
#[global] Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance if_true_atomic s v1 e2 : Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
Proof. solve_atomic. Qed.
#[global] Instance if_false_atomic s e1 v2 : Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance fst_atomic s v : Atomic s (Fst (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance snd_atomic s v : Atomic s (Snd (Val v)).
Proof. solve_atomic. Qed.

#[global] Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.

#[global] Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof. solve_atomic. Qed.
#[global] Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
#[global] Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
#[global] Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

#[global] Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

#[global] Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

#[global] Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instance for [EqOp]. *)
#[global] Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

#[global] Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

#[global] Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

#[global] Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. by intros ->. Qed.

Lemma auth_fuel_is_proper `{heapGS Σ Mdl} (x y : gmap (fmrole Mdl) nat):
  x = y ->
  auth_fuel_is x -∗ auth_fuel_is y.
Proof. by intros ->. Qed.

Section lifting.
Context `{LM:LiveModel heap_lang M}.
Context `{!heapGS Σ LM}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types tid : nat.


Lemma wp_lift_pure_step_no_fork tid E E' Φ e1 e2 fs ϕ:
  fs ≠ ∅ ->
  PureExec ϕ 1 e1 e2 ->
  ϕ ->
  (|={E}[E']▷=> has_fuels_S tid fs ∗ ((has_fuels tid fs) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  intros NnO Hpe Hϕ.
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hϕ). by apply nsteps_once_inv in Hpe. }
  iIntros "H". iApply wp_lift_step; eauto.
  { destruct Hps as [Hred _]. specialize (Hred inhabitant). eapply reducible_not_val; eauto. }
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  iMod "H". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "H" as "[Hfuels Hkont]".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(%&Hgh&Hmi)".
  (* iDestruct "Hmi" as (??) "(?&?&?&?&?&?&%)". *)

  iMod (update_no_step_enough_fuel _ _ ∅ with "Hfuels Hmi") as "H"; eauto;
    [by intros X%dom_empty_inv_L | set_solver | set_solver | econstructor =>//; by apply fill_step |].
  iModIntro.
  iDestruct ("H") as (δ2 ℓ [Hlabels Hvse]) "[Hfuels Hmi]".
  iExists δ2, ℓ.
  rewrite /state_interp /=.
  rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
  repeat iSplit; last done.
  - iPureIntro. destruct ℓ =>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iApply "Hkont". iApply (has_fuels_proper with "Hfuels") =>//.
    rewrite map_filter_id //. intros ?? ?%elem_of_dom_2; set_solver.
Qed.

Lemma wp_lift_pure_step_no_fork_remove_role rem s tid E E' Φ e1 e2 fs ϕ:
  fs ≠ ∅ ->
  rem ⊆ dom fs →
  rem ∩ live_roles _ s = ∅ →
  PureExec ϕ 1 e1 e2 ->
  ϕ ->
  (|={E}[E']▷=> frag_model_is s ∗ has_fuels_S tid fs ∗
                 (frag_model_is s -∗ (has_fuels tid (fs ⇂ (dom fs ∖ rem))) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  intros NnO Hincl Hdisj Hpe Hϕ.
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hϕ). by apply nsteps_once_inv in Hpe. }
  iIntros "H". iApply wp_lift_step; eauto.
  { destruct Hps as [Hred _]. specialize (Hred inhabitant). eapply reducible_not_val; eauto. }
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  iMod "H". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "H" as "(Hmod & Hfuels & Hkont)".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(%&Hgh&Hmi)".
  iDestruct (model_agree' with "Hmi Hmod") as %Heq.

  iMod (update_no_step_enough_fuel _ _ rem with "Hfuels Hmi") as "H"; eauto;
    [by intros X%dom_empty_inv_L | set_solver | econstructor =>//; by apply fill_step |].
  iModIntro.
  iDestruct ("H") as (δ2 ℓ [Hlabels Hvse]) "[Hfuels Hmi]".
  iExists δ2, ℓ.
  rewrite /state_interp /=.
  rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
  repeat iSplit; last done.
  - iPureIntro. destruct ℓ =>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iApply ("Hkont" with "Hmod"). iApply (has_fuels_proper with "Hfuels") =>//.
Qed.

(* Lemma wp_lift_pure_step_no_fork_2 tid E E' Φ e1 e2 (fs: gmap (fmrole Mdl) nat) R ϕ: *)
(*   R ≠ ∅ -> *)
(*   PureExec ϕ 1 e1 e2 -> *)
(*   ϕ -> *)
(*   (forall (ρ: fmrole Mdl) (f: nat), fs !! ρ = Some f -> f > 0) -> *)
(*   (|={E}[E']▷=> has_fuels tid R fs ∗ ((has_fuels tid R (fmap (λ (x: nat), (x - 1)%nat) fs)) -∗ WP e2 @ tid; E {{ Φ }})) *)
(*   ⊢ WP e1 @ tid; E {{ Φ }}. *)
(* Proof. *)

Lemma wp_lift_pure_step_no_fork' fs tid E E' Φ e1 e2:
  fs ≠ ∅ ->
  PureExec True 1 e1 e2 ->
  (|={E}[E']▷=> has_fuels_S tid fs ∗ ((has_fuels tid fs) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  intros. by iApply wp_lift_pure_step_no_fork.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole tid E E' Φ e1 e2 ρ f φ:
  PureExec φ 1 e1 e2 -> φ ->
  (|={E}[E']▷=> has_fuel tid ρ (S f) ∗ ((has_fuel tid ρ f) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  iIntros (??) "H". rewrite has_fuel_fuels_S.
  iApply (wp_lift_pure_step_no_fork {[ ρ := f ]} {[ρ]}); eauto; last first.
  rewrite has_fuel_fuels //. apply map_non_empty_singleton.
Qed.

Lemma wp_lift_pure_step_no_fork_take_step s1 s2 tid E E' fs1 fs2 fr1 Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  valid_new_fuelmap (LM := LM) fs1 fs2 s1 s2 ρ ->
  live_roles M s2 ∖ live_roles M s1 ⊆ fr1 →
  M.(fmtrans) s1 (Some ρ) s2 ->
  (|={E}[E']▷=> frag_model_is s1 ∗ has_fuels tid fs1 ∗ frag_free_roles_are fr1 ∗
                 (frag_model_is s2 -∗ frag_free_roles_are (fr1 ∖ (live_roles M s2 ∖ live_roles M s1))
                  -∗ (has_fuels tid fs2 -∗ WP e2 @ tid; E {{ Φ }})))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  iIntros (Hpe Hφ Hval Hfr Htrans).
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hφ). by apply nsteps_once_inv in Hpe. }
  iIntros "Hkont".
  iApply wp_lift_step; eauto.
  { destruct (pure_step_safe _ e2 Hps inhabitant) as (?&?&?&?). by eapply val_stuck. }

  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  iMod "Hkont". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "Hkont" as "(Hmod&Hfuels&Hfr&Hkont)".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(%&Hgh&Hmi)". simpl.
  iDestruct (model_agree' with "Hmi Hmod") as %Hmeq.

  iMod (update_step_still_alive _ _ _ _ σ1 σ1 with "Hfuels Hmod Hmi Hfr") as "H"; eauto.
  { rewrite Hexend. eauto. }
  { econstructor =>//.
    - rewrite Hexend //=.
    - by apply fill_step. }
  { rewrite Hmeq. apply Hval. }
  iModIntro. iDestruct "H" as (δ2 ℓ [Hlabels Hvse]) "(Hfuels&Hmod&Hmi&Hfr)".
  iExists δ2, ℓ.
  rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
  repeat iSplit; last done.
  - iPureIntro. destruct ℓ =>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - by iSpecialize ("Hkont" with "Hmod Hfr Hfuels").
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole_take_step s1 s2 tid E E' (f1 f2: nat) fr Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (f2 ≤ LM.(lm_fl) s2)%nat -> M.(fmtrans) s1 (Some ρ) s2 ->
  (|={E}[E']▷=> frag_model_is s1 ∗ frag_free_roles_are fr ∗ has_fuel tid ρ f1 ∗
   (frag_model_is s2 -∗ frag_free_roles_are fr -∗ (if decide (ρ ∈ live_roles M s2) then has_fuel tid ρ f2 else tid ↦M ∅) -∗
                               WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  iIntros (Hpe Hφ Hroles Hfl Hmdl).
  rewrite has_fuel_fuels.
  iIntros "H".
  iApply (wp_lift_pure_step_no_fork_take_step _ _ _ _ _ {[ρ := f1]}
         (if decide (ρ ∈ live_roles M s2) then {[ρ := f2]} else ∅) fr  with "[H]"); eauto.
  - repeat split.
    + intros ?. rewrite decide_True //. rewrite lookup_singleton //=.
    + destruct (decide (ρ ∈ live_roles _ s2)); set_solver.
    + set_solver.
    + intros ρ' Hdom. destruct (decide (ρ ∈ live_roles M s2)); set_solver.
    + intros ρ' Hneq Hin. destruct (decide (ρ ∈ live_roles M s2)); set_solver.
    + destruct (decide (ρ ∈ live_roles M s2)); set_solver.
    + destruct (decide (ρ ∈ live_roles M s2)); set_solver.
  - set_solver.
  - iMod "H". do 2 iModIntro. iMod "H" as "(Hmod&Hfr&Hfuels&Hkont)". iModIntro.
    iFrame "Hmod Hfr Hfuels". iIntros "Hmod Hfr Hfuels". iApply ("Hkont" with "Hmod [Hfr] [Hfuels]").
    + replace (fr ∖ (live_roles M s2 ∖ live_roles M s1)) with fr; [done|set_solver].
    + destruct (decide (ρ ∈ live_roles M s2)).
      * rewrite -has_fuel_fuels //.
      * iDestruct "Hfuels" as "[Hf _]". rewrite dom_empty_L //.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole' tid E E' Φ e1 e2 ρ f:
  PureExec True 1 e1 e2 ->
  (|={E}[E']▷=> has_fuel tid ρ (S f) ∗ ((has_fuel tid ρ f) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof.
  iIntros (?) "H". rewrite has_fuel_fuels_S.
  iApply (wp_lift_pure_step_no_fork' {[ ρ := f ]} {[ρ]}); last first.
  rewrite has_fuel_fuels //. apply map_non_empty_singleton.
Qed.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork_nostep s tid E e Φ R1 R2 fs (Hdisj: R1 ## R2) (Hnemp: fs ≠ ∅):
  R1 ∪ R2 = dom fs ->
  (∀ tid', ▷ (has_fuels tid' (fs ⇂ R2) -∗ WP e @ s; tid'; ⊤ {{ _, tid' ↦M ∅ }})) -∗
     ▷ (has_fuels tid (fs ⇂ R1) ={E}=∗ Φ (LitV LitUnit)) -∗
     has_fuels_S tid fs -∗ WP Fork e @ s; tid; E {{ Φ }}.
Proof.
  iIntros (Hunioneq) "He HΦ Htid". iApply wp_lift_atomic_head_step; [done|].
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iMod (update_fork_split R1 R2 _
       (tp1 ++ ectx_language.fill K (Val $ LitV LitUnit) :: tp2 ++ [e]) fs _ _ _ e _ σ1 with "Htid Hmi") as
       (δ2) "(Hfuels2 & Hfuels1 & Hσ & %Hvse)" => //.
  { rewrite -Hloc. rewrite -(language.locale_fill _ _ K). econstructor 1 =>//.
    apply fill_step, head_prim_step. econstructor. }
  { list_simplifier. exists (tp1 ++ fill K #() :: tp2). split; first by list_simplifier.
    rewrite !app_length //=. }
  iModIntro. iSplit. iPureIntro; first by eauto. iNext.
  iIntros (e2 σ2 efs Hstep).
  have [-> [-> ->]] : σ2 = σ1 ∧ efs = [e] ∧ e2 = Val $ LitV LitUnit by inv_head_step.
  iMod ("HΦ" with "Hfuels1") as "HΦ". iModIntro. iExists δ2, (Silent_step tid). iFrame.
  rewrite Hexend /=. iFrame "Hsi".
  iSplit; first by iPureIntro.
  iSplit; [|done].
  iApply "He". by list_simplifier.
Qed.

(** Heap *)
(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
Lemma heap_array_to_seq_meta l vs (n : nat) :
  length vs = n →
  ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
  [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
Proof.
  iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

Lemma heap_array_to_seq_mapsto l v (n : nat) :
  ([∗ map] l' ↦ v ∈ heap_array l (replicate n v), l' ↦ v) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
Proof.
  iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
  { done. }
  rewrite big_opM_union; last first.
  { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
  rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc.
  rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
Qed.

(* TODO *)

Lemma wp_allocN_seq_nostep s tid E v n fs:
  fs ≠ ∅ ->
  0 < n →
  {{{ has_fuels_S tid fs }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; tid; E
  {{{ l, RET LitV (LitLoc l); has_fuels tid fs ∗ [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (HnO Hn Φ) "HfuelS HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iModIntro; iSplit; first by eauto.
  iIntros (e2 σ2 efs Hstep). iNext.
  inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hsi")
    as "(Hsi & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id ?Hexend; auto with lia. }
  iMod (update_no_step_enough_fuel _ _ ∅ with "HfuelS Hmi") as (δ2 ℓ) "([%Hlabel %Hvse] & Hfuel & Hmi)" =>//.
  { by intros ?%dom_empty_inv_L. }
  { set_solver. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists δ2, ℓ.
  rewrite Hexend //=. iFrame "Hmi Hsi".
  repeat iSplit =>//.
  iApply "HΦ". iSplitL "Hfuel".
  { iApply (has_fuels_proper with "Hfuel") =>//.
    rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver. }
  iApply big_sepL_sep. iSplitL "Hl".
  + by iApply heap_array_to_seq_mapsto.
  + iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma wp_alloc_nostep s tid E v fs :
  fs ≠ ∅ ->
  {{{ has_fuels_S tid fs }}} Alloc (Val v) @ s; tid; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ ∗ has_fuels tid fs }}}.
Proof.
  iIntros (? Φ) "HfuelS HΦ". iApply (wp_allocN_seq_nostep with "HfuelS"); auto with lia.
  iIntros "!>" (l) "/= (? & ? & _)". rewrite loc_add_0. by iApply "HΦ"; iFrame.
Qed.

Lemma wp_choose_nat_nostep s tid E fs :
  fs ≠ ∅ ->
  {{{ has_fuels_S tid fs }}}
    ChooseNat @ s; tid; E
  {{{ (n:nat), RET LitV (LitInt n); has_fuels tid fs }}}.
Proof.
  iIntros (? Φ) "HfuelS HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iModIntro; iSplit; eauto.
  (* TODO: Improve this so we hide the (arbitrary) choice of `n` *)
  Unshelve. 2: apply O.
  iIntros (e2 σ2 efs Hstep). iNext.
  inv_head_step.
  iMod (update_no_step_enough_fuel _ _ ∅ with "HfuelS Hmi") as (δ2 ℓ) "([%Hlabel %Hvse] & Hfuel & Hmi)" =>//.
  { by intros ?%dom_empty_inv_L. }
  { set_solver. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists δ2, ℓ.
  rewrite Hexend //=. iFrame "Hmi Hsi".
  repeat iSplit =>//.
  iApply "HΦ".
  iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.

Lemma wp_load_nostep s tid E l q v fs:
  fs ≠ ∅ ->
  {{{ ▷ l ↦{q} v ∗ has_fuels_S tid fs }}} Load (Val $ LitV $ LitLoc l) @ s; tid; E {{{ RET v; l ↦{q} v ∗ has_fuels tid fs }}}.
Proof.
  iIntros (? Φ) "[>Hl HfuelS] HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iMod (update_no_step_enough_fuel _ _ ∅ with "HfuelS Hmi") as (δ2 ℓ) "([%Hlabels %Hvse] & Hfuel & Hmod)" =>//.
  { by intros ?%dom_empty_inv_L. }
  { set_solver. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists _,_.
  rewrite Hexend //=. iFrame "Hsi Hmod".
  do 2 (iSplit=>//).
  iApply "HΦ". iFrame. iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.

Lemma wp_store_nostep s tid E l v' v fs:
  fs ≠ ∅ ->
  {{{ ▷ l ↦ v' ∗ has_fuels_S tid fs }}}
    Store (Val $ LitV (LitLoc l)) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ has_fuels tid fs }}}.
Proof.
  iIntros (? Φ) "[>Hl HfuelS] HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod (update_no_step_enough_fuel _ _ ∅ with "HfuelS Hmi") as (δ2 ℓ) "([%Hlabels %Hvse] & Hfuel & Hmod)" =>//.
  { by intros ?%dom_empty_inv_L. }
  { set_solver. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iModIntro; iExists _,_.
  rewrite Hexend //=. iFrame "Hsi Hmod".
  do 2 (iSplit=>//).
  iApply "HΦ". iFrame. iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.

Lemma wp_store_step_singlerole s tid ρ (f1 f2: nat) fr s1 s2 E l v' v :
  f2 ≤ LM.(lm_fl) s2 -> fmtrans M s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  {{{ ▷ l ↦ v' ∗ ▷ frag_model_is s1 ∗ ▷ has_fuel tid ρ f1 ∗ ▷ frag_free_roles_are fr }}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ frag_model_is s2 ∗ frag_free_roles_are fr ∗
      (if decide (ρ ∈ live_roles M s2) then has_fuel tid ρ f2 else tid ↦M ∅ ) }}}.
Proof.
  iIntros (Hfl Htrans ? Φ) "(>Hl & >Hst & >Hfuel1 & > Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto.
  iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq.
  rewrite has_fuel_fuels Hexend.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod (update_step_still_alive _ _ _ _ _ _ _ _ _
            (if decide (ρ ∈ live_roles M s2) then {[ ρ := f2 ]} else ∅)
            with "Hfuel1 Hst Hmi Hfr") as
        (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; eauto.
  - set_solver.
  - destruct (decide (ρ ∈ live_roles M s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles M s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; first (intros ρ' Hin; set_solver).
      split; set_solver.
    + repeat (split; set_solver).
  - iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame.
    iSplit; first done.
    iApply "HΦ". iFrame.
    replace (fr ∖ (live_roles M s2 ∖ live_roles M s1))
      with fr; [iFrame|set_solver].
    destruct (decide (ρ ∈ live_roles M s2)).
    + rewrite has_fuel_fuels //.
    + iDestruct "Hfuel" as "[?_]". rewrite dom_empty_L //.
Qed.

Lemma wp_cmpxchg_fail_step_singlerole s tid ρ (f1 f2: nat) fr s1 s2 E l q v' v1 v2:
  v' ≠ v1 → vals_compare_safe v' v1 → f2 ≤ LM.(lm_fl) s2 -> M.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  {{{ ▷ l ↦{q} v' ∗ ▷ frag_model_is s1 ∗ ▷ has_fuel tid ρ f1 ∗ ▷ frag_free_roles_are fr }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' ∗ frag_model_is s2 ∗ frag_free_roles_are fr ∗
      (if decide (ρ ∈ live_roles M s2) then has_fuel tid ρ f2 else tid ↦M ∅ ) }}}.
Proof.
  iIntros (?? Hfl Htrans ? Φ) "(>Hl & >Hst & >Hfuel1 & > Hfr) HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq.
  rewrite bool_decide_false //.
  rewrite has_fuel_fuels Hexend.
  iMod (update_step_still_alive _ _ _ _ _ _ _ _ _
            (if decide (ρ ∈ live_roles M s2) then {[ ρ := f2 ]} else ∅)
            with "Hfuel1 Hst Hmi Hfr") as
        (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; eauto.
  - set_solver.
  - destruct (decide (ρ ∈ live_roles M s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles M s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; first (intros ρ' Hin; set_solver).
      split; set_solver.
    + repeat (split; set_solver).
  - rewrite -> bool_decide_eq_false_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame.
    iSplit; first done. iApply "HΦ". iFrame.
    replace (fr ∖ (live_roles M s2 ∖ live_roles M s1)) with fr; [iFrame|set_solver].
    destruct (decide (ρ ∈ live_roles M s2)).
    + rewrite has_fuel_fuels //.
    + iDestruct "Hfuel" as "[?_]". rewrite dom_empty_L //.
Qed.

Lemma wp_cmpxchg_suc_step_singlerole_keep_dead  s tid ρ (f1 f2: nat) fr s1 s2 E l v' v1 v2:
  ρ ∉ live_roles _ s2 →
  v' = v1 → vals_compare_safe v' v1 → f2 < f1 -> M.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  {{{ ▷ l ↦ v' ∗ ▷ frag_model_is s1 ∗ ▷ has_fuel tid ρ f1 ∗ ▷ frag_free_roles_are fr }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 ∗ frag_model_is s2 ∗ frag_free_roles_are fr ∗
      has_fuel tid ρ f2 }}}.
Proof.
  iIntros (??? Hfl Htrans ? Φ) "(>Hl & >Hst & >Hfuel1 & >Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  rewrite has_fuel_fuels Hexend.
  iMod (update_step_still_alive _ _ _ _ _ _ _ _ _ {[ ρ := f2 ]} with "Hfuel1 Hst Hmi Hfr") as
        (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; eauto.
  - set_solver.
  - apply head_locale_step; econstructor =>//.
  - repeat (split; try done); [|set_solver|set_solver|set_solver| set_solver |].
    + intros ??. rewrite !lookup_singleton /=. lia.
    + rewrite dom_singleton singleton_subseteq_l. simplify_eq.
      destruct (decide (ρ ∈ live_roles _ (trace_last atr))); set_solver.
  - rewrite -> bool_decide_eq_true_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame. iSplit; first done. iApply "HΦ". iFrame.
    replace (fr ∖ (live_roles M s2 ∖ live_roles M s1)) with fr; [iFrame|set_solver].
    by rewrite has_fuel_fuels.
Qed.

Lemma wp_cmpxchg_suc_step_singlerole s tid ρ (f1 f2: nat) fr s1 s2 E l v' v1 v2:
  v' = v1 → vals_compare_safe v' v1 → f2 ≤ LM.(lm_fl) s2 -> M.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  {{{ ▷ l ↦ v' ∗ ▷ frag_model_is s1 ∗ ▷ has_fuel tid ρ f1 ∗ ▷ frag_free_roles_are fr }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 ∗ frag_model_is s2 ∗ frag_free_roles_are fr ∗
      (if decide (ρ ∈ live_roles M s2) then has_fuel tid ρ f2 else tid ↦M ∅ ) }}}.
Proof.
  iIntros (?? Hfl Htrans ? Φ) "(>Hl & >Hst & >Hfuel1 & >Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iDestruct (model_agree' with "Hmi Hst") as %Hmeq.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  rewrite has_fuel_fuels Hexend.
  iMod (update_step_still_alive _ _ _ _ _ _ _ _ _
            (if decide (ρ ∈ live_roles M s2) then {[ ρ := f2 ]} else ∅)
            with "Hfuel1 Hst Hmi Hfr") as
        (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; eauto.
  - set_solver.
  - destruct (decide (ρ ∈ live_roles M s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles M s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; set_solver.
    + repeat (split; set_solver).
  - rewrite -> bool_decide_eq_true_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame. iSplit; first done. iApply "HΦ". iFrame.
    replace (fr ∖ (live_roles M s2 ∖ live_roles M s1)) with fr; [iFrame|set_solver].
    destruct (decide (ρ ∈ live_roles M s2)).
    + rewrite has_fuel_fuels //.
    + iDestruct "Hfuel" as "[?_]". rewrite dom_empty_L //.
Qed.

(* Lemma wp_faa s E l i1 i2 : *)
(*   {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E *)
(*   {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}. *)
(* Proof. *)
(*   iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto. *)
(*   iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?. *)
(*   iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step. *)
(*   iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]". *)
(*   iModIntro. iSplit=>//. iFrame. by iApply "HΦ". *)
(* Qed. *)
End lifting.
