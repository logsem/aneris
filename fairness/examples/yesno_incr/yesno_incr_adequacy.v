From Paco Require Import paco1 paco2 pacotac.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness Require Import trace_utils.
From trillium.fairness.examples.yesno_incr Require Import yesno_incr3.
From stdpp Require Import finite.

(* TODO: Move prerequisites *)
Lemma infinite_trace_after'' {S T} n (tr tr' : trace S T) :
  after n tr = Some tr' → infinite_trace tr → infinite_trace tr'.
Proof.
  intros Hafter Hinf m. specialize (Hinf (n+m)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf. done.
Qed.

Lemma trace_eventually_cons {S T} s l (tr : trace S T) P :
  trace_eventually tr P → trace_eventually (s -[l]-> tr) P.
Proof. intros [n HP]. by exists (Datatypes.S n). Qed.

(* Definition yesno_aux_progress n b (auxtr : auxtrace the_model) := *)
(*   trace_eventually auxtr (ls_under ∘ (λ s _, s = (n,b))). *)
Lemma trace_eventually_stutter_preserves `(LM : LiveModel Λ FM)
      (mtr : mtrace FM)
      (auxtr : auxtrace LM) P :
  upto_stutter ls_under Ul auxtr mtr →
  trace_eventually mtr P →
  trace_eventually auxtr (λ s l, P (ls_under s) (l ≫= Ul)).
Proof.
  intros Hstutter [n Heventually].
  revert mtr auxtr Hstutter Heventually.
  induction n as [|n IHn]; intros mtr auxtr Hstutter Heventually.
  - punfold Hstutter; [|apply upto_stutter_mono].
    induction Hstutter.
    + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl in *. done.
    + destruct (IHHstutter Heventually) as [n Heventually'].
      exists (1 + n). rewrite /pred_at. rewrite after_sum'. simpl.
      done.
    + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl.
      simplify_eq. rewrite H0. done.
  - punfold Hstutter; [|apply upto_stutter_mono].
    induction Hstutter.
    + rewrite /pred_at in Heventually. simpl in *. exists 0. rewrite /pred_at. simpl in *. done.
    + destruct (IHHstutter Heventually) as [n' Heventually'].
      exists (1 + n'). rewrite /pred_at. rewrite after_sum'. simpl.
      done.
    + apply trace_eventually_cons.
      assert (pred_at str n P) as Heventually'.
      { rewrite /pred_at in Heventually.
        simpl in *. done. }
      eapply IHn; [|done].
      rewrite /upaco2 in H1. destruct H1; [done|done].
Qed.

Lemma even_odd_False n : Nat.even n → Nat.odd n → False.
Proof.
  intros Heven Hodd. rewrite -Nat.negb_odd in Heven.
  apply Is_true_true_1 in Heven.
  apply Is_true_true_1 in Hodd.
  rewrite Hodd in Heven.
  done.
Qed.

Lemma even_not_odd n : Nat.even n → ¬ Nat.odd n.
Proof. intros Heven Hodd. by eapply even_odd_False. Qed.

Lemma odd_not_even n : Nat.odd n → ¬ Nat.even n.
Proof. intros Heven Hodd. by eapply even_odd_False. Qed.

(* TODO: move to fairness.v *)
Lemma mtrace_valid_after `{M : FairModel} (mtr mtr' : mtrace M) k :
  after k mtr = Some mtr' → mtrace_valid mtr → mtrace_valid mtr'.
Proof.
  revert mtr mtr'.
  induction k; intros mtr mtr' Hafter Hvalid.
  { destruct mtr'; simpl in *; by simplify_eq. }
  punfold Hvalid.
  inversion Hvalid as [|??? Htrans Hval']; simplify_eq.
  eapply IHk; [done|].
  by inversion Hval'.
Qed.

Lemma rel_finitary_sim_rel_with_user_sim_rel `{LM:LiveModel Λ Mdl}
      `{EqDecision (mstate LM)} `{EqDecision (mlabel LM)}
      `{Countable (locale Λ)} ξ :
  rel_finitary (sim_rel LM) → rel_finitary (sim_rel_with_user LM ξ).
Proof.
  intros Hrel. eapply rel_finitary_impl; [|done]. by intros ex aux [Hsim _].
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
               ((λ _ : language.val heap_lang, 0 ↦M ∅)
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

(* The model is finitely branching *)
Definition steppable n : list (nat * option YN) :=
  n' ← [S n; n];
  ℓ ← [Some Y; Some No];
  mret (n', ℓ).

#[local] Instance proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in yntrans s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma model_finitary s:
  Finite { '(s', ℓ) | yntrans s ℓ s'}.
Proof.
  assert (H: forall A (y x: A) xs, (y = x ∨ y ∈ xs) -> y ∈ x::xs) by set_solver.
  eapply (in_list_finite (steppable s)).
  intros [n w] Htrans.
  inversion Htrans; try (repeat (rewrite ?Nat.sub_0_r; simpl;
    eapply H; try (by left); right); done).
Qed.

(** Proof that any fair execution of model guarantees progress *)
Definition yesno_mtrace : Type := mtrace the_fair_model.

Definition yesno_mdl_progress (tr : yesno_mtrace) :=
  ∀ n, ∃ m, pred_at tr m (λ s _, s = n).

Lemma yesno_mdl_always_live ρ n (mtr : yesno_mtrace) :
  infinite_trace mtr →
  pred_at mtr n
          (λ (δ : the_fair_model) (_ : option (option (fmrole the_fair_model))),
             role_enabled_model ρ δ).
Proof.
  intros Hinf.
  specialize (Hinf n) as [mtr' Hafter].
  rewrite /pred_at. rewrite Hafter.
  rewrite /role_enabled_model.
  destruct mtr'; destruct ρ; set_solver.
Qed.

Lemma yesno_mdl_always_eventually_scheduled ρ (mtr : yesno_mtrace) :
  infinite_trace mtr →
  fair_model_trace ρ mtr →
  ∀ n, ∃ m, pred_at mtr (n+m) (λ _ ℓ, ℓ = Some (Some ρ)).
Proof.
  intros Hinf Hfair n.
  apply (yesno_mdl_always_live ρ n mtr) in Hinf.
  specialize (Hfair n Hinf) as [m [Hfair | Hfair]].
  - rewrite /pred_at in Hfair.
    destruct (after (n + m) mtr); [|done].
    rewrite /role_enabled_model in Hfair. destruct t; destruct ρ; set_solver.
  - by exists m.
Qed.

Lemma yesno_mdl_noprogress_Y n m (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (trfirst mtr) = n →
  Nat.even n →
  (∀ m0 : nat,
     m0 < m → pred_at mtr m0
             (λ _ l, l ≠ Some (Some Y))) →
  pred_at mtr m (λ s _, s = n).
Proof.
  intros Hinf Hvalid Hfirst Heven Hne.
  induction m.
  { rewrite /pred_at. destruct mtr; done. }
  simpl in *.
  assert (∀ m0 : nat,
          m0 < m
          → pred_at mtr m0
              (λ _ l, l ≠ Some (Some Y)))
    as Hne'.
  { intros. apply Hne. lia. }
  specialize (IHm Hne').
  rewrite /pred_at in IHm.
  destruct (after m mtr) eqn:Hafter; rewrite Hafter in IHm; [|done].
  rewrite /pred_at. replace (S m) with (m + 1) by lia.
  rewrite after_sum'. rewrite Hafter. simpl.
  specialize (Hinf (m+1)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf.
  destruct t; [by apply is_Some_None in Hinf|].
  eapply mtrace_valid_after in Hvalid; [|done].
  assert (ℓ ≠ Some Y) as Hneq.
  { assert (m < S m) by lia. specialize (Hne m H). rewrite /pred_at in Hne.
    rewrite Hafter in Hne. intros ->. apply Hne. done. }
  pinversion Hvalid. simplify_eq. inversion H1; simplify_eq.
  - by apply even_not_odd in Heven.
  - by destruct t.
Qed.

(* Trivial *)
Lemma yesno_mdl_noprogress_No n m (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (trfirst mtr) = n →
  Nat.odd n →
  (∀ m0 : nat,
     m0 < m → pred_at mtr m0
             (λ _ (l : option (option YN)),
                l ≠ Some (Some No))) →
  pred_at mtr m (λ s _, s = n).
Proof.
  intros Hinf Hvalid Hfirst Hodd Hne.
  induction m.
  { rewrite /pred_at. destruct mtr; done. }
  simpl in *.
  assert (∀ m0 : nat,
          m0 < m
          → pred_at mtr m0
              (λ _ l, l ≠ Some (Some No)))
    as Hne'.
  { intros. apply Hne. lia. }
  specialize (IHm Hne').
  rewrite /pred_at in IHm.
  destruct (after m mtr) eqn:Hafter; rewrite Hafter in IHm; [|done].
  rewrite /pred_at. replace (S m) with (m + 1) by lia.
  rewrite after_sum'. rewrite Hafter. simpl.
  specialize (Hinf (m+1)).
  rewrite after_sum' in Hinf. rewrite Hafter in Hinf.
  destruct t; [by apply is_Some_None in Hinf|].
  eapply mtrace_valid_after in Hvalid; [|done].
  assert (ℓ ≠ Some No) as Hneq.
  { assert (m < S m) by lia. specialize (Hne m H). rewrite /pred_at in Hne.
    rewrite Hafter in Hne. intros ->. apply Hne. done. }
  pinversion Hvalid. simplify_eq. inversion H1; simplify_eq.
  - by apply odd_not_even in Hodd.
  - by destruct t.
Qed.

Theorem yesno_mdl_progresses_Y n (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = n →
  Nat.even n →
  ∃ m, pred_at mtr m (λ s _, s = S n).
Proof.
  intros Hinf Hvalid Hfair Hfirst Heven.
  specialize (Hfair Y).
  pose proof (yesno_mdl_always_eventually_scheduled Y mtr Hinf Hfair 0) as Hsched.
  simpl in *.
  apply trace_eventually_until in Hsched as [m [Hsched Hschedne]].
  rewrite /pred_at in Hsched.
  destruct (after m mtr) eqn:Hafter; last first.
  { rewrite Hafter in Hsched. done. }
  rewrite Hafter in Hsched.
  destruct t; [done|].
  simplify_eq.
  assert (s = trfirst mtr) as ->.
  { eapply yesno_mdl_noprogress_Y in Hschedne; [|done..].
    rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. }
  eapply mtrace_valid_after in Hvalid; [|done].
  pinversion Hvalid; simplify_eq. inversion H1; simplify_eq.
  - exists (m + 1).
    rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl.
    destruct t; simpl in *; simplify_eq; done.
  - by apply even_not_odd in Heven.
Qed.

Theorem yesno_mdl_progresses_No n (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = n →
  Nat.odd n →
  ∃ m, pred_at mtr m (λ s _, s = S n).
Proof.
  intros Hinf Hvalid Hfair Hfirst Hodd.
  specialize (Hfair No).
  pose proof (yesno_mdl_always_eventually_scheduled No mtr Hinf Hfair 0) as Hsched.
  simpl in *.
  apply trace_eventually_until in Hsched as [m [Hsched Hschedne]].
  rewrite /pred_at in Hsched.
  destruct (after m mtr) eqn:Hafter; last first.
  { rewrite Hafter in Hsched. done. }
  rewrite Hafter in Hsched.
  destruct t; [done|].
  simplify_eq.
  assert (s = trfirst mtr) as ->.
  { eapply yesno_mdl_noprogress_No in Hschedne; [|done..].
    rewrite /pred_at in Hschedne. rewrite Hafter in Hschedne. done. }
  eapply mtrace_valid_after in Hvalid; [|done].
  pinversion Hvalid; simplify_eq. inversion H1; simplify_eq.
  - exists (m + 1).
    rewrite /pred_at. rewrite !after_sum'. rewrite Hafter. simpl.
    destruct t; simpl in *; simplify_eq; done.
  - by apply odd_not_even in Hodd.
Qed.

Theorem yesno_mdl_progresses (mtr : yesno_mtrace) :
  infinite_trace mtr →
  mtrace_valid mtr →
  (∀ ρ, fair_model_trace ρ mtr) →
  (trfirst mtr) = 0 →
  yesno_mdl_progress mtr.
Proof.
  intros Hinf Hvalid Hfair Hfirst n.
  induction n as [|n IHn].
  { exists 0. rewrite /pred_at. rewrite /trfirst in Hfirst. simpl.
    destruct mtr; done. }
  destruct IHn as [m Hpred].
  rewrite /pred_at in Hpred.
  destruct (after m mtr) eqn:Hafter; [|done].
  eapply infinite_trace_after'' in Hinf; [|done].
  eapply mtrace_valid_after in Hvalid; [|done].
  destruct (Nat.even n) eqn:Heqn.
  - assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ t) as Hfair'.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst t = n) as Hfirst'.
    { rewrite /trfirst. destruct t; done. }
    pose proof (yesno_mdl_progresses_Y n t Hinf Hvalid Hfair' Hfirst')
      as [m' Hpred']; [by eauto|].
    exists (m + m').
    rewrite pred_at_sum. rewrite Hafter. done.
  - assert (∀ ρ : fmrole the_fair_model, fair_model_trace ρ t) as Hfair'.
    { intros. by eapply fair_model_trace_after. }
    assert (trfirst t = n) as Hfirst'.
    { rewrite /trfirst. destruct t; done. }
    pose proof (yesno_mdl_progresses_No n t Hinf Hvalid Hfair' Hfirst')
      as [m' Hpred']; [by rewrite -Nat.negb_even Heqn|].
    exists (m + m').
    rewrite pred_at_sum. rewrite Hafter. done.
Qed.

(** Proof that fair progress is preserved through auxiliary trace *)

(* TODO: Better definition *)
Definition yesno_aux_progress (auxtr : auxtrace the_model) :=
  ∀ n, ∃ m, pred_at auxtr m (λ s l, (λ s' _, s' = n) (ls_under s) (l ≫= Ul)).

Lemma yesno_mtr_aux_progress_preserved
      (mtr : mtrace the_fair_model)
      (auxtr : auxtrace the_model) :
  upto_stutter ls_under Ul auxtr mtr →
  yesno_mdl_progress mtr → yesno_aux_progress auxtr.
Proof.
  intros Hstutter Hmtr n. specialize (Hmtr n).
  by apply (trace_eventually_stutter_preserves _ mtr auxtr (λ s' _, s' = n)).
Qed.

(** Proof that progress is preserved between auxilary and execution trace,
 for a specific ξ *)

Definition yesno_ex_progress (l:loc) (tr : heap_lang_extrace) :=
  ∀ (n:nat), ∃ m, pred_at tr m (λ s _, heap s.2 !! l = Some #n).

Definition ξ_yesno_model_match (l : loc) (c : cfg heap_lang) (δ : the_fair_model) :=
  ∃ (N:nat), heap c.2 !! l = Some #N ∧ δ = N.

Definition ξ_yesno_steps (l : loc) (c : cfg heap_lang) (δ : the_fair_model) :=
  Forall (λ e, is_Some $ to_val e) c.1 → False.

Definition ξ_yesno (l : loc) (c : cfg heap_lang) (δ : the_fair_model) :=
  ξ_yesno_steps l c δ ∧ ξ_yesno_model_match l c δ.

Definition ξ_yesno_trace (l : loc) (extr : execution_trace heap_lang)
           (auxtr : finite_trace the_fair_model (option YN)) :=
  ξ_yesno l (trace_last extr) (trace_last auxtr).

Lemma yesno_aux_ex_progress_preserved l (extr : heap_lang_extrace) (auxtr : auxtrace the_model) :
  traces_match labels_match (λ c δ, live_tids c δ ∧ ξ_yesno l c δ) locale_step
  (lm_ls_trans the_model) extr auxtr →
  yesno_aux_progress auxtr → yesno_ex_progress l extr.
Proof.
  intros Hξ Hauxtr.
  intros n.
  specialize (Hauxtr n).
  rewrite /pred_at in Hauxtr.
  destruct Hauxtr as [m Hauxtr].
  destruct (after m auxtr) eqn:Heqn; [|done].
  eapply traces_match_after in Hξ as [extr' [Hafter' Hextr']]; [|done].
  exists m. rewrite /pred_at. rewrite Hafter'.
  inversion Hextr'; simplify_eq.
  - destruct H as [? [? [n [? ?]]]]. simplify_eq. done.
  - destruct H0 as [? [? [n [? ?]]]]. simplify_eq. done.
Qed.

Instance the_model_mstate_countable : EqDecision (mstate the_model).
Proof. intros x y. apply make_decision. Qed.
Instance the_model_mlabel_countable : EqDecision (mlabel the_model).
Proof. solve_decision. Qed.

(** Proof that program refines model up to ξ_yesno *)

Lemma yesno_incr_sim l :
  continued_simulation
    (sim_rel_with_user the_model (ξ_yesno_trace l))
    (trace_singleton ([start #l],
                        {| heap := {[l:=#0]};
                           used_proph_id := ∅ |}))
    (trace_singleton (initial_ls (LM := the_model) 0 0)).
Proof.
  assert (yesnoPreG yesnoΣ) as HPreG'.
  { apply _. }
  assert (heapGpreS yesnoΣ the_model) as HPreG.
  { apply _. }
  eapply (strong_simulation_adequacy
            yesnoΣ _ NotStuck _ _ _ ∅); [|set_solver|].
  { eapply rel_finitary_sim_rel_with_user_sim_rel.
    eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl. apply (model_finitary s1). }
  iIntros (?) "!> Hσ Hs Hr Hf".
  iMod (own_alloc (●E 0  ⋅ ◯E 0))%nat as (γ_yes_at) "[Hyes_at_auth Hyes_at]".
  { apply auth_both_valid_2; eauto. by compute. }
  iMod (own_alloc (●E 1  ⋅ ◯E 1))%nat as (γ_no_at) "[Hno_at_auth Hno_at]".
  { apply auth_both_valid_2; eauto. by compute. }
  pose (the_names := {|
   yes_name := γ_yes_at;
   no_name := γ_no_at;
  |}).
  iMod (inv_alloc (nroot .@ "yes_no") _ (yesno_inv_inner l) with "[Hσ Hs Hr Hyes_at_auth Hno_at_auth]") as "#Hinv".
  { iNext. unfold yesno_inv_inner. iExists 0.
    replace (∅ ∖ live_roles the_fair_model 0) with
      (∅:gset (fmrole the_fair_model)) by set_solver.
    simpl. rewrite /yn_live_roles.
    iFrame.
    rewrite big_sepM_singleton. iFrame. }
  iModIntro.
  iSplitL.
  { simpl. rewrite /yn_live_roles.
    replace (gset_to_gmap 61 {[No; Y]}) with
      ({[Y := 61; No := 61]} : gmap _ _); last first.
    { rewrite /gset_to_gmap. simpl.
      rewrite !map_fmap_union. rewrite !map_fmap_singleton.
      rewrite map_union_comm; last first.
      { rewrite map_disjoint_singleton_l.
        by rewrite lookup_insert_ne. }
      rewrite -!insert_union_l.
      rewrite left_id. done. }
    iApply (start_spec with "[$Hf $Hyes_at $Hno_at $Hinv]"); [lia|].
    by iIntros "!>?". }
  iIntros (extr auxtr c) "_ _ _ %Hends _ _ [_ [Hσ Hδ]]Hposts".
  iInv "Hinv" as (M) "(_ & >Hmod & >Hn & _)" "Hclose".
  iApply fupd_mask_intro; [set_solver|].
  iIntros "Hclose'".
  iDestruct (gen_heap_valid with "Hσ Hn") as %Hn.
  iDestruct "Hδ" as (??) "(_&_&_&_&_&Hδ&_)".
  iDestruct (model_agree with "Hδ Hmod") as %Hn'.
  iSplitL; last first.
  { iPureIntro.
    exists M. split; [done|].
    rewrite -Hn'. by destruct auxtr. }
  rewrite /trace_ends_in in Hends.
  rewrite Hends.
  rewrite bi.pure_impl.
  rewrite !big_sepL_omap.
  rewrite !big_sepL_zip_with.
  simpl.
  
Admitted.

(** Proof that execution trace actually progresses *)
(* TODO: Needs assumption that trace is maximal *)
Theorem yesno_ex_progresses (l:loc) (extr : heap_lang_extrace) :
  extrace_valid extr →
  (∀ tid, fair_ex tid extr) →
  trfirst extr = ([start #l],
                        {| heap := {[l:=#0]};
                           used_proph_id := ∅ |}) →
  yesno_ex_progress l extr.
Proof.
  intros Hvalid Hfair Hfirst.
  pose proof (yesno_incr_sim l) as Hsim.

  assert (∃ iatr,
             valid_inf_system_trace
               (continued_simulation (sim_rel_with_user the_model (ξ_yesno_trace l)))
               (trace_singleton (trfirst extr))
               (trace_singleton (initial_ls (LM:=the_model) 0 0))
               (from_trace extr)
               iatr) as [iatr Hiatr].
  { eexists _. eapply produced_inf_aux_trace_valid_inf. econstructor.
    Unshelve.
    - rewrite Hfirst. done.
    - eapply from_trace_preserves_validity; eauto; first econstructor. }

  assert (∃ (auxtr : auxtrace the_model),
             traces_match labels_match
               (live_tids /2\ (ξ_yesno l))
               locale_step
               the_model.(lm_ls_trans) extr auxtr) as [auxtr Hmatch_strong].
  { exists (to_trace (initial_ls (LM := the_model) 0 0 ) iatr).
    eapply (valid_inf_system_trace_implies_traces_match_strong
              (continued_simulation (sim_rel_with_user the_model (ξ_yesno_trace l)))); eauto.
    - intros ? ? ?%continued_simulation_rel. by destruct H as [[_ H] _].
    - intros ? ? ?%continued_simulation_rel. by destruct H as [[H _] _].
    - intros extr' auxtr' ?%continued_simulation_rel.
      destruct H as [_ [H1 H2]].
      split; [done|].
      destruct H2 as [n [H21 H22]].
      exists n. split; [done|]. by destruct auxtr'.
    - by apply from_trace_spec.
    - by apply to_trace_spec. }

  assert (exaux_traces_match extr auxtr) as Hmatch.
  { eapply traces_match_impl; [| |done].
    - done.
    - by intros ?? [? ?]. }
  have Hstutter:=Hmatch.
  apply can_destutter_auxtr in Hstutter; last first.
  { intros ?? Hstep. inversion Hstep. done. }
  destruct Hstutter as [mtr Hupto].

  assert (infinite_trace extr) as Hinf by admit.

  have Hfairaux := fairness_preserved extr auxtr Hinf Hmatch Hfair.
  have Hvalaux := exaux_preserves_validity extr auxtr Hmatch.
  have Hfairm := upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  have Hmtrvalid := upto_preserves_validity auxtr mtr Hupto Hvalaux.

  pose proof (fairness_preserved extr auxtr Hinf Hmatch Hfair) as Hfair'.
  pose proof (upto_stutter_fairness auxtr mtr Hupto Hfair') as Hfair''.

  assert (infinite_trace mtr) as Hinf''.
  { eapply upto_stutter_infinite_trace; [done|].
    by eapply traces_match_infinite_trace. }
  assert (mtrace_valid mtr) as Hvalid''.
  { eapply upto_preserves_validity; [done|].
    by eapply exaux_preserves_validity. }

  (* TODO: Improve proof *)
  assert (trfirst mtr = 0) as Hfirst''.
  { apply traces_match_first in Hmatch_strong.
    destruct Hmatch_strong as [_ [_ [n [Hσ Hmdl]]]].
    rewrite Hfirst in Hσ. simpl in *. rewrite lookup_insert in Hσ.
    simplify_eq. punfold Hupto; [|by apply upto_stutter_mono'].
    assert (0 = ls_under (trfirst auxtr)) as Hσ' by lia.
    inversion Hupto; simplify_eq;
    by rewrite Hσ'. }

  pose proof (yesno_mdl_progresses mtr Hinf'' Hvalid'' Hfair'' Hfirst'')
    as Hprogress.
  eapply (yesno_aux_ex_progress_preserved l _ auxtr); [done|].
  by eapply yesno_mtr_aux_progress_preserved.
Admitted.
