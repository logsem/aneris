From iris.proofmode Require Import tactics.
From trillium.program_logic Require Import weakestpre.
From trillium.prelude Require Import finitary quantifiers sigma classical_instances.
Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Import lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang Require Import simulation_adequacy_lm simulation_adequacy_lm_ext em_lm.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From stdpp Require Import finite.
From trillium.fairness Require Import fairness_finiteness lm_lsi_top resources. 

Import derived_laws_later.bi.

From trillium.fairness Require Import lm_fairness_preservation lm_fair lm_fair_traces fair_termination.
From trillium.fairness.ext_models Require Import destutter_ext ext_models.
From trillium.fairness.examples.comp Require Import lib lib_ext client_defs.
From trillium.fairness.examples.comp Require Import traces_equiv.
From trillium.fairness Require Import fair_termination_natural subtrace.
From trillium.fairness Require Import lm_fairness_preservation_wip.
From trillium.fairness Require Import my_omega lemmas trace_len trace_helpers trace_lookup comp_utils.

Close Scope Z_scope. 

Local Ltac gd t := generalize dependent t.

Lemma client_model_step_fin (s1 : fmstate client_model_impl):
  next_states s1. 
Proof.
  destruct s1 as (δ_lib, c).
  pose proof (lib_model_impl_fin (ls_under δ_lib)) as [ie_lib IE_LIB]. 
  pose proof (role_LM_step_dom_all δ_lib ((ls_under δ_lib) :: ie_lib) (elements lib_gs) (LM := lib_model lib_gs)) as STEPS_LIB.

  remember (map fst (enumerate_next δ_lib ((ls_under δ_lib) :: ie_lib) (elements lib_gs) (LM := lib_model lib_gs))) as steps_lib.
  set (steps := [((δ_lib, c - 1));
                 ((reset_lm_st ρlg δ_lib ρlg_in_lib_gs, c - 1))] ++
                 ((fun δ' => ((δ', c))) <$> steps_lib)). 

  exists steps. 
  intros [δ' c'] oρ TRANS.
  simpl in TRANS. inversion TRANS; subst.
  1,2,4: set_solver. 
  subst steps. apply elem_of_app. right. apply elem_of_list_fmap.
  eexists. split; eauto.
  simpl in LIB_STEP. destruct LIB_STEP as (ℓ & LIB_STEP & MATCH). 
  apply elem_of_list_In. eapply STEPS_LIB; eauto.
  { apply elem_of_cons. 
    edestruct @locale_trans_fmtrans_or_eq as [[? FM] | EQ]. 
    { eexists. eauto. }
    - right. eauto.
    - by left. }
  rewrite list_to_set_elements_L. by apply δ'.
Qed.

Let client_model_finitary s1 := model_finitary_helper s1 (client_model_step_fin s1).
 
  
Section ClientRA.

  Definition clientPreΣ : gFunctors :=
    #[ GFunctor (authUR (optionR (exclR natO)));
       fairnessΣ lib_grole lib_model_impl].
  
  Global Instance subG_clientPreΣ {Σ}:
    subG clientPreΣ Σ → clientPreGS Σ.
  Proof. solve_inG. Qed.

End ClientRA.


Lemma δ_lib0_init_roles:
  live_roles lib_model_impl 0 = ∅.
Proof.
  set_solver. 
Qed. 

Definition δ_lib0: LiveState lib_grole lib_model_impl (LSI_groups_fixed lib_gs).
  refine (build_LS_ext (0: fmstate lib_model_impl) ∅ _ {[ ρlg := ∅ ]} _ _ _).
  - rewrite δ_lib0_init_roles. set_solver.   
  - intros. setoid_rewrite lookup_singleton_Some. set_solver. 
  - intros. 
    erewrite lookup_singleton_Some in H.
    rewrite lookup_singleton_Some in H0.
    destruct H, H0. congruence.
  - red. rewrite dom_singleton. rewrite /lib_gs. done.  
Defined.   


Definition is_client_step := fun (step: model_trace_step client_model_impl) => 
                               step_label_matches step (eq (Some $ inr ρy)).
Definition is_lib_step := fun (step: model_trace_step client_model_impl) =>
                            step_label_matches step (fun ρ => exists ρlg, Some $ inl ρlg = ρ).

Lemma client_steps_finite (tr: mtrace client_model_impl)
  (VALID: mtrace_valid tr)
  (CL: ∀ i s step, tr !! i = Some (s, step) → is_client_step (s, step) \/ step = None):
  exists l, trace_len_is tr (NOnum l) /\ 
         (forall s, tr S!! (l - 1) = Some s -> snd s = snd (trfirst tr) - (l - 1)). 
Proof.
  pose proof (state_lookup_0 tr) as S0.
  destruct (trfirst tr) as [δ0 c0] eqn:ST0. 
  gd tr. gd δ0. induction c0.
  { intros. exists 1.
    pose proof (trace_has_len tr) as [len LEN].
    destruct (tr !! 0) as [[δ0_ c0_]| ] eqn:STEP0.
    2: { eapply trace_lookup_dom_neg in STEP0; eauto.
         lia_NO' len. assert (n = 0) as -> by lia. 
         by apply trace_len_0_inv in LEN. }
    forward eapply trace_state_lookup_simpl; eauto. intros ->.
    specialize (CL _ _ _ STEP0). destruct CL.
    2: { subst. 
         pattern (δ0, 0) in STEP0. eapply ex_intro, trace_lookup_dom_eq in STEP0; eauto. subst.
         simpl in *. split; auto.
         intros. destruct s. simpl in *. congruence. }
    do 2 red in H. destruct H as (?&?&?&[[=] <-]). subst.
    pose proof (trace_valid_steps' _ _ VALID _ _ _ _ STEP0) as STEP.
    inversion STEP. }

  intros.
  pose proof (trace_has_len tr) as [len LEN].
  destruct (tr !! 0) as [[δ0_ c0_]| ] eqn:STEP0.
  2: { eapply trace_lookup_dom_neg in STEP0; eauto.
       lia_NO' len. assert (n = 0) as -> by lia. 
       by apply trace_len_0_inv in LEN. }
  forward eapply trace_state_lookup_simpl; eauto. intros ->.

  pose proof CL as CL'. specialize (CL' _ _ _ STEP0).
  destruct CL'.
  2: { subst. 
       pattern (δ0, S c0) in STEP0. eapply ex_intro, trace_lookup_dom_eq in STEP0; eauto. subst.
       simpl in *. eexists. split; eauto.
       intros. destruct s. simpl in *. congruence. }
  do 2 red in H. destruct H as (?&?&?&[[=] <-]). subst.
  pose proof (trace_valid_steps' _ _ VALID _ _ _ _ STEP0) as STEP.
  destruct x1 as [δ1 c0_].
  assert (c0_ = c0) as ->. 
  { inversion STEP; lia. }
  pose proof STEP0 as (atr & AFTER & HEAD)%trace_lookup_after_strong.
  apply after_S_tr_cons in AFTER. 
  specialize (IHc0 δ1 atr). specialize_full IHc0; eauto. 
  { eapply trace_valid_after; eauto. }
  { intros. apply (CL (S i)). rewrite -H.
    symmetry. rewrite -Nat.add_1_r Nat.add_comm.
    eapply trace_lookup_after; eauto. }
  { by rewrite -HEAD -state_lookup_0. }
  destruct IHc0 as (l' & LEN' & C).
  destruct l'.
  { simpl in LEN'. by apply trace_len_0_inv in LEN'. }
  exists (S l' + 1). split.
  { forward eapply (trace_len_after tr) as LEN'_; eauto.
    forward eapply (trace_len_uniq _ _ _ LEN' LEN'_) as L_; eauto.
    lia_NO' len. inversion L_. subst.
    enough (S (l' + 1) = n); [subst; done| ]. lia. } 
  intros. destruct s as [δ c].
  erewrite state_lookup_after in C; eauto.
  simpl. simpl in C. rewrite Nat.sub_0_r.
  rewrite Nat.add_sub in H. rewrite Nat.sub_0_r in C. 
  specialize (C _ H). simpl in *. lia. 
Qed. 

Arguments NOmega.le _ _ : simpl nomatch.


(* TODO: unify with client_step_ex_dec ? *)
Instance client_step_ex_dec: forall st oρ st', 
    Decision (client_trans st oρ st').
Proof.
  intros. destruct oρ as [ρ| ].
  2: { right. intros T. inversion T. }
  destruct st' as [δ_lib' c']. 
  
  pose proof (@lib_LF _ lib_gs_ne). (* why it's not inferred anymore? *)
  pose proof lib_lm_EI_eqdec. 
  Local Ltac nostep := right; intros T; inversion T.
  destruct st as [δ_lib n]. destruct n; [| destruct n]; [..| destruct n]; [..| destruct n]. 
  - by nostep. 
  - destruct ρ as [l | y].
    + destruct l.
      2: by nostep. 
      destruct f.
      destruct (decide (locale_trans δ_lib () δ_lib' (LM := lib_model lib_gs))).
      ** destruct (decide (c' = 1)).
         *** left. subst. econstructor. eauto.
         *** by nostep.  
      ** nostep. simpl in LIB_STEP. eauto. 
    + destruct y. 
      destruct (ls_tmap δ_lib !! ρlg) eqn:LIB_OBLS.
      2: { nostep. subst. congruence. }
      destruct (decide (g = ∅)).
      * subst. destruct (decide (c' = 0 /\ δ_lib' = δ_lib)) as [[-> ->] |].
        ** subst. left. econstructor. eauto.
        ** nostep. subst. by apply n. 
      * nostep. subst. set_solver.
  - destruct ρ as [l | y]; [destruct l| ]. 
    1, 3: by nostep.
    destruct e as [i].      
    destruct (decide (δ_lib' = reset_lm_st ρlg δ_lib ρlg_in_lib_gs /\ lm_is_stopped ρlg δ_lib /\ c' = 1 /\ i = (eiG ρlg))) as [(-> & STOP & -> & ->)|].
    + left. by econstructor.
    + nostep. subst. tauto. 
  - assert (EqDecision client_role).
    { rewrite /client_role.
      assert (EqDecision y_role). (* not inferred? *)
      { solve_decision. }
        solve_decision. }
    destruct (decide (ρ = ρ_cl /\ c' = 2 /\ δ_lib' = δ_lib)) as [(->&->&->)|?]. 
    + left. econstructor; eauto.
    + nostep. subst. tauto.  
  - by nostep. 
Qed.


Definition project_lib_trace (tr: mtrace client_model_impl): elmftrace (ELM := ExtLibLM) :=
  project_nested_trace fst 
    (fun ℓ => match ℓ with | Some (inl l) => Some $ Some l | _ => None end)
    tr. 
    
Ltac unfold_slm H :=
  match type of H with 
  | step_label_matches ?step ?P => destruct H as (?&?&?&->&?Pstep)
  end. 
 
Lemma lib_trace_construction (tr: mtrace client_model_impl)
  (VALID: mtrace_valid tr)
  (LIB_STEPS: ∀ i res, tr !! i = Some res → is_lib_step res \/ is_end_state res):
    lm_model_traces_match
      (transA := @ext_trans _ ExtLibLM)
      ((option_fmap _ _ inl): option (@ext_role _ ExtLibLM) -> option $ fmrole client_model_impl)
      (fun c δ_lib => fst c = δ_lib)
      tr
      (project_lib_trace tr).
Proof.
  do 2 red.
  rewrite /out_A_labels_match. simpl.
  eapply traces_match_impl; cycle 1. 
  { intros *. intros X. apply X. }
  { eapply nested_trace_construction.
    { done. }
    { intros * ITH. apply LIB_STEPS in ITH as [LIB | ?]; [| tauto].
      red in LIB. unfold_slm LIB. destruct Pstep as [? <-].
      left. do 3 eexists. eauto. }
    intros. destruct ℓ; [| done]. destruct c; [| done].
    inversion H0. subst.
    inversion H; subst; simpl in *.
    2: { econstructor; eauto. }
    simpl. econstructor. simpl.
    red. split; eauto. }
  simpl. intros. destruct ℓ1; [| done]. destruct c; [| done].
  by inversion H.
Qed. 

(* TODO: abstract the nested LM state *)
Local Instance inh_client: Inhabited (lm_ls client_model).
Proof.
  pose proof (LSI_gf_ls_inh (lib_model lib_gs) lib_gs_ne) as [δ].  
  assert (Inhabited (locale heap_lang)) as [τ] by apply _.
  apply populate.
  refine {| ls_under := (δ, 0): fmstate client_model_impl;
       ls_fuel := kmap (inl ∘ inl) (gset_to_gmap 0 (dom (ls_tmap δ))): gmap (fmrole client_model_impl) nat;
        ls_tmap := {[ τ := set_map (inl ∘ inl) (dom (ls_tmap δ)) ]}: gmap (locale heap_lang) (gset (fmrole client_model_impl))
         ;
    |}.
  - by rewrite live_roles_0.
  - intros ρ. 
    rewrite dom_kmap dom_gset_to_gmap. rewrite !elem_of_map.
    setoid_rewrite lookup_singleton_Some.
    etrans.
    2: { symmetry. apply ex_det_iff with (a := τ). by intros ? (?&[??]&?). } 
    etrans.
    2: { symmetry. eapply ex_det_iff. intros ? ([??]&?). symmetry. apply H0. }
    rewrite elem_of_map. tauto.
  - red. intros * NEQ TM1%lookup_singleton_Some TM2%lookup_singleton_Some.
    destruct TM1, TM2. congruence.
  - red. intros.
    rewrite /mapped_roles. rewrite map_img_singleton_L flatten_gset_singleton.
    apply elem_of_map. eexists. split; [reflexivity| ].
    destruct H. eapply mim_in_1; eauto. apply ls_mapping_tmap_corr.
Qed. 

Local Instance client_eq: EqDecision (fmstate client_model_impl).
Proof.
  pose proof (@LS_eqdec _ _ _ _ _ _ (lib_LF _ lib_gs_ne)).
  solve_decision. 
Defined.

(* TODO: almost a copypaste from spinlock, unify? *)
Instance client_lm_dec_ex_step:
  ∀ τ δ1, Decision (∃ δ2, locale_trans δ1 τ δ2 (LM := client_model)).
Proof.
  intros.
  pose proof (client_model_finitary (ls_under δ1)) as FIN.
  apply locale_trans_ex_dec_fin with (steps := map (fst ∘ proj1_sig) (@enum _ _ FIN)).
  - intros. apply in_map_iff.
    unshelve eexists.
    { eapply (exist _ (s2, oρ)). by left. }
    split; [done| ]. 
    apply elem_of_list_In. apply elem_of_enum.
  - intros. eexists. eapply rearrange_roles_spec.
    Unshelve.
    + exact client_model. 
    + red. intros ? [??].
      erewrite <- mapped_roles_dom_fuels_gen.
      2: { apply rrm_tmap_fuel_same_doms. }
      pose proof (ls_inv δ2) as LSI2. red in LSI2. 
      specialize (LSI2 _ ltac:(eauto)).
      by rewrite -mapped_roles_dom_fuels in LSI2. 
Defined. 
 

Local Instance client_LF: LMFairPre client_model.
  esplit; apply _.
Defined.

(* Let lib_ALM := ELM_ALM (lib_keeps_asg (NE := lib_gs_ne)). *)

Definition comp_LM_trace_exposing :=
  outer_LM_trace_exposing lib_keeps_asg
    (inl ∘ inl) (option_fmap _ _ inl) (λ c δ_lib, c.1 = δ_lib). 
  

(* Lemma outer_exposing_subtrace ltr tr i str  *)
(*   (OUTER_CORR: outer_LM_trace_exposing ltr tr) *)
(*   (SUB: subtrace tr i NOinfinity = Some str): *)
(*   exists sltr,  *)
(*     outer_LM_trace_exposing sltr str. *)
(* Proof.  *)
(*   red in OUTER_CORR. destruct OUTER_CORR as (UPTO & FAIR_AUX & INNER_OBLS). *)
(*   pose proof (trace_has_len tr) as [len LEN]. *)
(*   pose proof SUB as X. eapply subtrace_equiv_after in X as (atr & AFTER & EQUIV); eauto. *)
(*   2: { lia_NO len. } *)
(*   forward eapply upto_stutter_after; eauto. intros (i' & latr & AFTER' & UPTO'). *)
(*   exists latr. split; [| split]. *)
(*   - eauto. eapply upto_stutter_Proper; [.. |eapply UPTO']; eauto. *)
(*     + reflexivity.  *)
(*     + by symmetry. *)
(*   - intros. *)
(*     forward eapply fair_by_gen_after; [apply AFTER' |..]; eauto. *)
(*     intros. apply FAIR_AUX. *)
(*   - eapply inner_obls_exposed_after; eauto. *)
(* Qed.    *)


Local Notation " 'step_of' M " := 
  (fmstate M * option (option (fmrole M) * fmstate M))%type 
    (at level 10).

Lemma client_trace_lookup (tr: mtrace client_model_impl) i
  (VALID: mtrace_valid tr)
  :
  terminating_trace tr \/
  exists step, tr !! i = Some step /\
            (is_client_step step \/
             is_lib_step step /\ (snd $ fst step = 2 \/ snd $ fst step = 1)).
Proof.
  pose proof (trace_has_len tr) as [len LEN].
  destruct (tr !! i) as [[st step]|] eqn:ST.
  2: { left. eapply terminating_trace_equiv; eauto.
       eapply trace_lookup_dom_neg in ST; eauto.
       lia_NO' len. eauto. }
  destruct step as [[ℓ st']|].
  2: { pattern st in ST. eapply ex_intro, trace_lookup_dom_eq in ST; eauto.
       left. eapply terminating_trace_equiv; eauto. }
  right. eexists. split; eauto. simpl.
  forward eapply (trace_valid_steps' _ _ VALID i) as TRANS; [eauto| ].
  simpl in TRANS.
  inversion TRANS; subst; simpl.
  1, 4: by (left; do 2 red; eauto). 
  all: right; split; eauto; do 2 red; do 3 eexists; eauto. 
Qed. 

Lemma client_step_mono s1 oρ s2
  (STEP: client_trans s1 oρ s2):
  s2.2 <= s1.2.
Proof. inversion STEP; simpl; lia. Qed. 

(* TODO: use this lemma more extensively *)
Lemma client_trace_mono (tr: mtrace client_model_impl) i j si sj
  (VALID : mtrace_valid tr)
  (LE: i <= j)
  (ITH: tr S!! i = Some si) (JTH: tr S!! j = Some sj):
  sj.2 <= si.2.
Proof. 
  apply Nat.le_sum in LE as [d ->].
  gd sj. induction d.
  { intros. rewrite Nat.add_0_r in JTH. rewrite ITH in JTH. by inversion JTH. }
  rewrite Nat.add_succ_r -Nat.add_1_r. intros sj' JTH'. 
  pose proof (trace_has_len tr) as [len LEN].  
  destruct (proj2 (trace_lookup_dom_strong _ _ LEN (i + d))) as (sj & ρ & sj'_ & JTH). 
  { eapply state_lookup_dom; eauto. }
  apply state_label_lookup in JTH as (JTH & JTH'_ & JTHρ).
  rewrite JTH' in JTH'_. inversion JTH'_. subst sj'_. clear JTH'_.   
  specialize (IHd _ JTH). etrans; [| apply IHd].
  eapply client_step_mono.
  eapply trace_valid_steps''; eauto.
Qed. 

(* TODO: inline? *)
Lemma c1_preserved (tr: mtrace client_model_impl)
  (m1 m2 : nat) s  
  (VALID : mtrace_valid tr)
  (L2: ∀ i res, m1 ≤ i → i < m2 → tr !! i = Some res → is_lib_step res)
  (Sm1 : tr S!! m1 = Some s)
  (C1 : s.2 = 1)
  :
  ∀ j s, m1 <= j <= m2 → tr S!! j = Some s → s.2 = 1.
Proof. 
  eapply preserved_prop_kept; eauto.
  intros ??? LIB STEP EQ1.
  do 2 red in LIB. destruct LIB as (?&?&?&[=]&[? <-]). subst.
  simpl in STEP. inversion STEP.
  - by subst.
  - by simpl in *.
Qed.

(* TODO: inline? *)  
Lemma done_lib_preserved (tr: mtrace client_model_impl)
  (m1 m2 : nat) s  
  (VALID : mtrace_valid tr)
  (L2: ∀ i res, m1 ≤ i → i < m2 → tr !! i = Some res → is_client_step res)
  (Sm1 : tr S!! m1 = Some s)
  (NOLIB1 : ls_tmap s.1 !! ρlg = Some ∅):
  ∀ j s, m1 <= j <= m2 → tr S!! j = Some s → ls_tmap s.1 !! ρlg = Some ∅.
Proof. 
  eapply preserved_prop_kept; eauto.
  intros ??? CL STEP EQ1.
  do 2 red in CL. destruct CL as (?&?&?&[=]&[=]). subst. 
  simpl in STEP. inversion STEP; subst; done. 
Qed. 

Definition is_lib_ext_step := 
  fun step => step_label_matches (step: model_trace_step client_model_impl)
             (fun ρ => exists e, Some $ inl (inr e) = ρ).

Instance is_lib_ext_step_dec res: Decision (is_lib_ext_step res).
Proof.
  apply slm_dec. intros.
  destruct ρ as [ρ| ].
  2: { right. by intros [??]. }
  destruct ρ as [[ | ]|].
  2: by left; eauto.
  all: by right; intros [? [=]].
Qed. 
  

Lemma lib_ext_trans_bound (tr: mtrace client_model_impl)
  (VALID : mtrace_valid tr):
  trans_bounded tr (λ oℓ, ∃ l : env_role, oℓ = Some (inl (inr l))).
Proof. 
  red.
  pose proof (trace_has_len tr) as [len LEN]. 
  forward eapply (trace_prop_split tr (not ∘ is_lib_ext_step)) as [l1 (L1 & NL1 & DOM1)]; eauto.
  { solve_decision. }
  apply NOmega.nomega_le_lt_eq in DOM1 as [DOM1 | ->].
  2: { exists 0. intros i ? _ ITH. intros [? ->].
       apply trace_label_lookup_simpl' in ITH as (?&?&ITH). 
       eapply L1; eauto.
       - eapply trace_lookup_dom; eauto.
       - do 2 red. do 3 eexists. split; eauto. }
  destruct l1 as [| n]; [lia_NO len| ].
  pose proof DOM1 as NTH. eapply trace_lookup_dom in NTH as [step NTH]; eauto.  
  specialize (NL1 _ _ eq_refl NTH).
  apply dec_stable in NL1.
  do 2 red in NL1. destruct NL1 as (?&?&?&->&[? <-]).
  pose proof NTH as STEP. eapply trace_valid_steps' in STEP; eauto.
  inversion STEP; subst.
  exists (S n). intros j ? LT JTH. intros [? ->].
  apply trace_label_lookup_simpl' in JTH as (?&?&JTH). 
  pose proof JTH as STEP'. eapply trace_valid_steps' in STEP'; eauto.
  inversion STEP'. subst.
  apply state_label_lookup in NTH as (?&NTH'&?). 
  apply state_label_lookup in JTH as (JTH&?&?). 
  epose proof (client_trace_mono _ _ _ _ _ VALID _ NTH' JTH) as LE.
  simpl in LE. lia.
  Unshelve. lia.
Qed.

(* TODO: move*)
Global Instance inj_EqDec {A B: Type} (f: A -> B)
  (EDA: EqDecision A)
  (INJ: @Inj A B eq eq f):
  forall a1 a2, Decision (f a1 = f a2).
Proof.
  intros. destruct (decide (a1 = a2)); [subst; by left| ].
  right. by intros ->%INJ.
Qed. 
  
Lemma client_model_fair_term tr lmtr
  (OUTER_CORR: comp_LM_trace_exposing lmtr tr):
  mtrace_fairly_terminating tr.
Proof.
  intros. red. intros VALID FAIR.
  (* destruct (infinite_or_finite tr) as [INF|]; [| done]. *)
  pose proof (trace_has_len tr) as [len LEN]. 

  assert (len = NOnum 1 \/ NOmega.lt_nat_l 1 len /\ snd (trfirst tr) <= 3) as [-> | [LENnz BOUNDc]].
  { pose proof (trace_lookup_0_Some tr) as [[δ0 step0] STEP0].
    destruct step0.
    2: { left. rewrite -(plus_O_n 1).
         eapply trace_lookup_dom_eq; eauto. }
    destruct p. 
    right. split.
    { rewrite -(plus_O_n 1). eapply trace_lookup_dom_strong; eauto. }
    forward eapply (trace_valid_steps' _ _ VALID 0) as TRANS; [eauto| ].
    apply state_label_lookup in STEP0 as (ST0 & ?&?). 
    rewrite state_lookup_0 in ST0. inversion ST0. rewrite H2. 
    inversion TRANS; subst; simpl; lia. }
  { eapply terminating_trace_equiv; eauto. }

  forward eapply (trace_prop_split tr is_client_step) as [l1 (L1 & NL1 & DOM1)]; eauto.
  { eapply slm_dec. intros.
    (* TODO: why it's not inferred automatically? *)                          
    destruct ρ as [ρ| ]; [| by nostep].
    apply inj_EqDec; [| by apply _]. 
    unshelve eapply sum_eq_dec. solve_decision. }

  (* assert (exists n1, l1 = NOnum n1 /\ (forall s, tr S!! (n1 - 1) = Some s -> snd s < 2)) as (m1 & LEN1 & BOUNDc').  *)
  assert (exists n1, l1 = NOnum n1) as (m1 & LEN1).
  { 
    destruct l1; eauto.
    forward eapply (subtrace_len tr _ 0 NOinfinity) as SUB1; eauto.
    { done. }
    destruct SUB1 as (str & SUB & LEN1). 
    forward eapply (client_steps_finite str) as (m1 & LEN1' & XX); eauto.
    { eapply (subtrace_valid tr); eauto.
      (* TODO: get rid of excessive arguments *)
      Unshelve. all: exact True. }  
    { intros. left. eapply L1; [done| ].
      rewrite -H.
      rewrite -{2}(plus_O_n i). symmetry.
      eapply subtrace_lookup; eauto. done. }
    forward eapply (trace_len_uniq _ _ _ LEN1 LEN1'). done. }

  subst l1. simpl in *. 

  forward eapply (trace_prop_split' tr is_lib_step _ m1)
    as (l2 & L2 & NL2 & LE2 & LE2'); eauto.
  { eapply slm_dec. intros.
    destruct ρ as [ρ| ]; [| by nostep].
    destruct ρ; [left | right]; eauto. by intros [??]. }

  assert (exists m2, l2 = NOnum m2) as [m2 ->].
  { destruct l2 eqn:L2_EQ; [| by eauto].
    forward eapply (subtrace_len tr _ m1 l2) as SUB2; eauto. 
    1, 2: by lia_NO' l2.
    destruct SUB2 as (str & SUB2 & LEN2).

    forward eapply (lib_trace_construction str) as MATCH. 
    { subst. eapply (subtrace_valid tr); eauto.
      (* TODO: get rid of excessive arguments *)
      Unshelve. all: exact True.  }
    { subst. intros i res RES.
      pose proof RES as H. 
      eapply mk_is_Some, trace_lookup_dom in H; eauto.
      left. apply (L2 (m1 + i)); [lia| ..]; eauto.
      rewrite -RES. symmetry. 
      eapply subtrace_lookup; eauto. }

    (* forward eapply (simulation_adequacy_terminate_general' (LM := lib_model)). *)
    (* 3: { Unshelve. *)
    (*   apply MATCH.  *)

    (* forward eapply (simulation_adequacy_terminate_general'_ext str (project_lib_trace str)). *)
    (* 4: { apply MATCH.  *)
    eapply @simulation_adequacy_terminate_general'_ext in MATCH; eauto; cycle 1. 
    (* eapply simulation_adequacy_terminate_general'_ext in MATCH; eauto; cycle 1.  *)
    { apply lib_proj_keep_ext. }
    { intros.
      eapply fin_ext_fair_termination; eauto.
      apply lib_fair_term. }
    { subst l2. simpl in *.
      assert (trans_bounded str (fun oℓ => exists l, oℓ = Some (inl $ inr l))).
      { eapply lib_ext_trans_bound; eauto.
        eapply (subtrace_valid tr); eauto. }
      destruct H as [b BOUND]. exists b. intros. intros [? ->].
      pose proof H0 as ITH'. 
      eapply traces_match_label_lookup_2 in ITH' as (ℓ & ITH' & MATCH'); [| apply MATCH].
      red in MATCH'. simpl in MATCH'. subst.  
      apply BOUND in ITH'; auto. destruct ITH'. eauto. }  
    { 
      subst. simpl in *.
      forward eapply outer_exposing_subtrace; eauto.
      intros [? EXP'].

      unshelve eapply ELM_ALM_afair_by_next.
      { red. apply lib_keeps_asg. }  

      eapply inner_LM_trace_fair_aux.
      - apply _.
      - done. 
      - by apply EXP'. 
      - simpl. intros ?? [=<-].
        by apply EXP'.
      - by apply EXP'.
      - by apply MATCH. }

    red in MATCH. specialize_full MATCH; eauto.
    { subst. eapply (subtrace_valid tr); eauto. }
    { subst. eapply fair_by_subtrace; eauto. }
    apply (terminating_trace_equiv _ _ LEN2) in MATCH as [??].
    subst. done. }

  simpl in *.
  assert (terminating_trace tr \/ exists step, (snd (fst step) = 2 \/ snd (fst step) = 1) /\ tr !! m2 = Some step /\ is_client_step step /\ ls_tmap step.1.1 !! ρlg = Some ∅) as NEXT. 
  { edestruct (client_trace_lookup tr m2) as [?|STEP]; eauto.
    destruct STEP as [[s step] [STEP [CL | [LIB BOUND]]]].
    2: { eapply NL2 in LIB; done. }  
    edestruct (client_trace_lookup tr m1) as [?|STEP']; eauto.
    destruct STEP' as [step' [STEP' [CL' | [LIB BOUND]]]].
    { eapply NL1 in CL'; done. }
    right. do 2 red in CL. destruct CL as (?&?&?&[=]&[=]).
    subst.
    eexists. apply and_comm, and_assoc. 
    split; [apply STEP|]. simpl.
    apply and_assoc. split; [by do 2 red; eauto| ].
    assert (x.2 = 2 \/ x.2 = 1).
    { apply state_label_lookup in STEP.
      do 2 red in LIB. destruct LIB as (?&?&?&[=]&[? <-]).
      subst. apply state_label_lookup in STEP'. simpl in *.

      destruct BOUND.
      2: { right. eapply c1_preserved.
           3: { apply (proj1 STEP'). }
           all: eauto.
           apply STEP. }

      assert (m2 = m1 \/ m1 + 1 <= m2) as [-> | LE] by lia.
      { destruct STEP. destruct STEP'. rewrite H0 in H2.
        inversion H2. subst x0. tauto. }
    
      forward eapply (trace_valid_steps'' _ _ VALID m1) as TRANS; eauto; try by apply STEP'.
      simpl in TRANS. inversion TRANS; subst; simpl in *. 
      2: { lia. }

      right.
      destruct STEP' as (?&X&?).
      eapply c1_preserved.
      3: { apply X. }
      all: eauto.
      2: by apply STEP.
      intros. apply (L2 i); eauto; try lia. }
    
    forward eapply (trace_valid_steps' _ _ VALID m2) as TRANS; eauto.
    simpl in TRANS. inversion TRANS; subst. 
    { simpl in H. lia. }
    eauto. }
  
  destruct NEXT as [? | (step & BOUND & STm2 & CL2 & NOlib)]; [done| ].
  forward eapply (trace_prop_split' tr is_client_step _ m2) as [l3 (L3 & NL3 & DOM3)]; eauto.
  { eapply slm_dec. intros.
    (* TODO: why it's not inferred automatically? *)
    assert (EqDecision client_role).    
    { unshelve eapply sum_eq_dec. solve_decision. } 
    (* apply (@sum_eq_dec (fmrole lib_fair) lib_role_EqDec y_role y_EqDec).   *)
    solve_decision.
    Unshelve. all: exact True.  
  }

  forward eapply (subtrace_len tr _ m2 l3) as SUB3; eauto.
  { lia_NO' l3. apply proj1, le_lt_eq_dec in DOM3 as [?| ->]; [done| ].
    eapply NL3 in STm2; done. }
  { apply DOM3. }
  destruct SUB3 as (str3 & SUB3 & LEN3).
  (* TODO: refactor usages of this lemma  *)
  forward eapply (client_steps_finite str3) as (m3 & LEN3' & BOUND3); eauto.
  { eapply (subtrace_valid tr); [..| apply SUB3]; eauto.
    apply DOM3.
    Unshelve. all: exact True. 
  }  
  { intros. destruct step0 as [[ℓ s']| ]; eauto. left.
    (* pose proof H as X%trace_lookup_dom_strong.  *)
    assert (NOmega.lt_nat_l (i + 1) (NOmega.sub l3 (NOnum m2))). 
    { eapply trace_lookup_dom_strong; eauto. }
    erewrite @subtrace_lookup in H; eauto.
    eapply L3; [..| apply H]; [lia| ].
    lia_NO l3. }
    
  pose proof (trace_len_uniq _ _ _ LEN3 LEN3').
  lia_NO' l3. inversion H. subst m3.
  forward eapply (client_trace_lookup tr n); eauto.
  intros [? | [stepn [STEPn [CL3 | LIB3]]]]; [done| ..].
  { eapply NL3 in CL3; done. }
  destruct LIB3 as [LIB3 BOUND3'].
  do 2 red in LIB3. destruct LIB3 as (?&?&?&[=]&[? <-]).
  subst. simpl in *.
  destruct DOM3 as [LE3 DOM3].

  destruct x2.
  2: { (* corner case of only ext step without following lib steps *)
    destruct BOUND3'.
    2: { eapply trace_valid_steps' in STEPn; eauto.
         inversion STEPn. subst. simpl in *. lia. }
    do 2 red in CL2. destruct CL2 as (st_m2&?&st_m2'&[=]&?). subst. 
    apply Nat.le_lteq in LE3 as [LT | ->].
    2: { rewrite STm2 in STEPn. inversion STEPn. }
    simpl in BOUND.
    assert (st_m2'.2 <= 1) as BOUND'.
    { eapply trace_valid_steps' in STm2; eauto.
      inversion STm2; subst; simpl in *; lia. }
    apply state_label_lookup in STm2 as (?&M2TH'&?). 
    apply state_label_lookup in STEPn as (NTH&?&?). 
    epose proof (client_trace_mono _ _ _ _ _ VALID _ M2TH' NTH) as LE.
    simpl in *. lia.
    Unshelve. lia. } 

  rename f into x2. 

  enough (ls_tmap x.1 !! x2 = Some ∅).
  2: { apply state_label_lookup in STEPn. 
       eapply done_lib_preserved. 
       6: apply STEPn.
       all: eauto.
       destruct CL2 as (?&?&?&[=]&[=]). subst. simpl.
       eapply state_label_lookup; eauto. }
       
  forward eapply (trace_valid_steps' _ _ VALID n) as TRANS; eauto.
  simpl in TRANS. inversion TRANS. subst.
  apply fm_live_spec in LIB_STEP.
  eapply LM_map_empty_notlive in LIB_STEP; eauto. done.  
  
Qed. 

Lemma client_LM_inner_exposed (auxtr: lmftrace (LM := client_model)):
  inner_obls_exposed (option_fmap _ _ inl) (λ c δ_lib, c.1 = δ_lib) auxtr (LMo := client_model) (AMi := ELM_ALM (lib_keeps_asg (NE := lib_gs_ne))).
Proof. 
  red. simpl. intros n δ gl NTH (?&?&?&MAP).
  eexists. split; [reflexivity| ].
  rewrite (ls_same_doms δ) mapped_roles_dom_fuels. 
  apply (ls_inv δ). rewrite H. eauto. 
Qed.


From trillium.fairness.heap_lang Require Import em_lm_heap_lang. 


Local Instance LF': LMFairPre' client_model.
esplit; apply _.
Defined.

  
(* TODO: try to unify it with general lemma.
   The problem is that proving client model trace termination
   now depends on client LM trace with certain properties,
   whereas in original lemma all model traces are required to be terminating. *)
(* TODO: generalize the initial state in general lemma as well? *)
Theorem simulation_adequacy_terminate_client (Σ: gFunctors)
        {hPre: @heapGpreS Σ (fair_model_model (@LM_Fair _ _ _ _ _ _ client_LF)) (@LM_EM_HL _ _ client_model LF')} (s: stuckness)
        e1 (s1: fmstate client_model_impl) FR
        (LSI0: initial_ls_LSI s1 0 (M := client_model_impl) (LM := client_model) (LSI := client_LSI))
        (extr : heap_lang_extrace)
        (Hexfirst : (trfirst extr).1 = [e1])
  :
  rel_finitary (sim_rel client_model (LF := client_LF)) →
  wp_premise (λ _ _, True) (trfirst extr).2 e1 s1 s FR LSI0 ->
  extrace_fairly_terminating extr.
Proof.
  intros Hfb Hwp Hvex Hfair.

  destruct (simulation_adequacy_model_trace
              Σ _ e1 s1 FR LSI0 extr Hvex Hexfirst Hfb Hwp) as (auxtr&mtr&Hmatch&Hupto&A0).

  (* TODO: clarify which types of fairness we need in this proof *)
  assert (forall ρ, fair_aux_SoU (LM_ALM client_model) ρ auxtr (LM := client_model)) as FAIR_SOU.
  { apply group_fairness_implies_step_or_unassign; eauto.
    { eapply traces_match_valid2; eauto. }
    eapply fairness_preserved; eauto.
    { apply _. }
    { intros. apply match_locale_enabled_states_livetids. }
    intros.
    destruct ζ.
    { apply Hfair. }
    simpl. red. simpl in *. by intros ?(?&?&?)%pred_at_trace_lookup. }

  pose proof (ex_fairness_preserved _ _ Hmatch Hfair) as Hfairaux'.
  pose proof (proj1 (LM_ALM_afair_by_next _ auxtr) Hfairaux') as Hfairaux.  
  
  have Hfairm := lm_fair_traces.upto_stutter_fairness auxtr mtr Hupto Hfairaux.
  pose proof (traces_match_valid2 _ _ _ _ _ _ Hmatch) as Hvalaux. 
  have Hmtrvalid := lm_fair_traces.upto_preserves_validity auxtr mtr Hupto Hvalaux.

  assert (mtrace_fairly_terminating mtr) as FAIR_TERM. 
  { eapply client_model_fair_term.
    red. split; [| split]; eauto.
    by apply client_LM_inner_exposed. }
  assert (terminating_trace mtr) as Hterm.
  { eapply FAIR_TERM; eauto. }
    
  eapply traces_match_preserves_termination =>//.
  eapply lm_fair_traces.upto_stutter_finiteness =>//.
Qed.

Lemma δ_lib0_map: ls_mapping δ_lib0 = ∅. 
Proof.
  eapply build_LS_ext_spec_mapping. 
  red. intros. split; try set_solver. intros (? & L & IN).
  rewrite lookup_singleton_Some in L. set_solver.  
Qed.   

Lemma init_lib_state: lm_is_stopped ρlg δ_lib0 (NE := lib_gs_ne).
Proof.
  repeat split; simpl; done. 
Qed.

(* (* TODO: move *) *)
From trillium.fairness.examples.comp Require Import comp.

Theorem client_terminates
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [client #()]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  set (Σ := gFunctors.app (heapΣ (@LM_EM_HL _ _ client_model LF')) clientPreΣ). 
  assert (heapGpreS Σ (@LM_EM_HL _ _ client_model LF')) as HPreG.
  { apply _. }
  (* eset (δ_lib0: LiveState lib_grole lib_model_impl).  := {| |}). *)
  set (st0 := (δ_lib0, 3): fmstate client_model_impl).
  assert (initial_ls_LSI st0 0 (LM := client_model)) as LSI0.
  { subst st0. red. red.
    intros gi [ρ MAP]. simpl in MAP.
    by rewrite δ_lib0_map in MAP. } 
  eapply (simulation_adequacy_terminate_client Σ NotStuck _ (st0: fmstate client_model_impl) _ LSI0); try done.  
  - eapply valid_state_evolution_finitary_fairness_simple.
    apply client_model_finitary.
  - intros ?. iStartProof.    
    rewrite /LM_init_resource. iIntros "!> (Hm & FR & Hf) !>".
    iSplitL.
    2: { (* TODO: make a lemma, move it to simulation_adequacy_lm *)
      iIntros (?). iIntros "**". 
      iApply (fupd_mask_weaken ∅); first set_solver. by iIntros "_ !>". }

    simpl.
    iApply (client_spec ∅ δ_lib0 with "[] [Hm Hf FR]"); eauto.
    { set_solver. }
    { apply init_lib_state. }
    { iApply lm_lsi_toplevel. }
    iFrame. 
    iSplitL "FR".
    + simpl. rewrite dom_gset_to_gmap. rewrite difference_twice_L.
      rewrite difference_disjoint; [by iFrame| ].
      subst st0. erewrite live_roles_3. set_solver. 
    + subst st0.
      iApply has_fuels_proper; [reflexivity| | by iFrame].
      pose proof (live_roles_3 δ_lib0). simpl in H.
      replace (client_lr (δ_lib0, 3)) with ({[inr ρy]}: gset (fmrole client_model_impl)).
      2: { symmetry. apply leibniz_equiv. apply live_roles_3. }
      rewrite -gset_to_gmap_singletons big_opS_singleton. done.
Qed. 
