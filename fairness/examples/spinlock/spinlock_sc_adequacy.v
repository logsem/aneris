From iris.proofmode Require Import tactics.
From trillium.program_logic Require Import weakestpre.
From trillium.prelude Require Import finitary quantifiers sigma classical_instances.

Require Import stdpp.decidable.
From trillium.fairness.heap_lang Require Export lang lifting tactics proofmode.
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang Require Import simulation_adequacy_lm em_lm_heap_lang em_lm.
From iris.base_logic.lib Require Import invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import excl_auth.
From iris.bi Require Import bi.
From stdpp Require Import finite.
From trillium.fairness Require Import fairness_finiteness actual_resources_interface lm_fair utils.

Import derived_laws_later.bi.

From trillium.fairness.examples.spinlock Require Import spinlock_sc. 
(* From trillium.fairness Require Import fairness fair_termination. *)
From trillium.fairness Require Import fair_termination_natural.


Definition sm_order (s1 s2: spinlock_model_impl): Prop :=
  Forall2 le s1 s2.
                                                     
Instance sm_order_po: PartialOrder sm_order. 
Proof.
  constructor.
  - apply PreOrder_instance_1. econstructor; red; lia.
  - apply AntiSymm_instance_1. red. lia. 
Qed.


Definition rem_actions (st: spinlock_model_impl): nat := list_sum st. 

Lemma not_Forall2 {A B: Type} (f: A -> B -> Prop) (la: list A) (lb: list B)
      (LEN: length la = length lb)
      (NF2: ¬ Forall2 f la lb)
      (DEC: RelDecision f):
  exists i a b, la !! i = Some a /\ lb !! i = Some b /\ not (f a b).
Proof.
  generalize dependent lb. induction la.
  { intros. simpl in LEN. symmetry in LEN. apply nil_length_inv in LEN. subst.
    by destruct NF2. }
  intros. destruct lb.
  { by simpl in LEN. }
  simpl in LEN. apply eq_add_S in LEN.
  destruct (DEC a b).
  2: { exists 0%nat, a, b. auto. }
  edestruct @Forall2_dec with (x := la) (y := lb); eauto.
  { destruct NF2. eauto. }
  specialize (IHla _ LEN n). destruct IHla as (i & a' & b' & ? & ? & ?).
  exists (S i), a', b'. simpl. eauto.
Qed. 
  
Lemma sm_order_sum_le (st1 st2: spinlock_model_impl) (LE: sm_order st1 st2):
  list_sum st1 <= list_sum st2.
Proof.
  generalize dependent st2. induction st1.
  { intros. red in LE. apply Forall2_nil_inv_l in LE. subst. lia. }
  intros. destruct st2.
  { red in LE. by apply Forall2_nil_inv_r in LE. }
  inversion LE. subst.
  simpl. specialize (IHst1 _ H4). lia.
Qed.

Lemma sm_order_insert st (i v v': nat)
  (ITH: st !! i = Some v) (LE: v' <= v):
  sm_order (<[i:=v']> st) st.
Proof.
  red. apply Forall2_same_length_lookup_2; [by apply insert_length| ].
  intros j x y JTH' ITH_. destruct (dec_eq_nat j i).
  + subst j. rewrite ITH_ in ITH. inversion ITH. subst v. 
    rewrite list_lookup_insert in JTH'.
    2: { by eapply lookup_lt_Some. }
    inversion JTH'. lia.
  + rewrite list_lookup_insert_ne in JTH'; auto.
    rewrite ITH_ in JTH'. inversion JTH'. lia.
Qed. 

Lemma strict_sm_order_insert st (i v v': nat)  (ITH: st !! i = Some v) (LT: v' < v):
  strict sm_order (<[i:=v']> st) st.
Proof.
  red. split; [eapply sm_order_insert; eauto; lia| ].
  intros ORD. red in ORD.
  eapply Forall2_lookup_lr with (y := v') in ORD; eauto; [lia| ].
  apply list_lookup_insert. by eapply lookup_lt_Some. 
Qed. 

Lemma unlocked_dec (st: spinlock_model_impl):
  Decision (state_unlocked st).
Proof.
  red. induction st.
  { by left. }
  destruct IHst.
  2: { right. unfold state_unlocked in *. intros UNL. destruct n.
       intros. by apply UNL with (j := S j). }
  destruct (Nat.eq_dec a 1%nat) as [-> | A].
  { right. intros UNL. red in UNL. specialize (UNL 0%nat 1%nat eq_refl). lia. }
  left. red. intros. destruct j.
  { simpl in JV. inversion JV. lia. }
  simpl in JV. by eapply s.
Qed.

Lemma locked_dec (st: spinlock_model_impl): 
  {i | state_locked_by st i} +
  {not (exists i, state_locked_by st i)}. 
Proof.
  destruct (list_find (eq 1%nat) st) eqn:IN1.
  2: { right. intros [i [ITH NOJ]]. 
       apply list_find_None in IN1.
       eapply Forall_lookup_1 in ITH; eauto. done. }
  destruct p as [i v].
  (* pose proof IN1 as IN_. *)
  apply list_find_Some in IN1. destruct IN1 as (ITH & <- & PREV).  
  destruct (list_find (eq 1%nat) (drop (S i) st)) eqn:IN2. 
  2: { apply list_find_None in IN2. 
       left. exists i. red. split; auto.
       intros. destruct (Nat.lt_trichotomy i j) as [LT | [? | LT]]; [| done| ].
       2: { specialize (PREV _ _ JV). lia. }
       eapply Forall_lookup_1 with (i := (j - (S i))%nat) in IN2.
       2: { rewrite lookup_drop. rewrite le_plus_minus_r; eauto. }
       lia. }
  destruct p as [j v].
  apply list_find_Some in IN2. destruct IN2 as (JTH & <- & PREV').
  right. intros [k [KTH NOOTHER]].
  destruct (Nat.lt_trichotomy k i) as [LT | [? | LT]].
  { eapply PREV in LT; eauto. }
  { subst k. edestruct (NOOTHER (S i + j)%nat); try lia. 
    { by rewrite lookup_drop in JTH. }
    all: lia. }  
  destruct (Nat.lt_trichotomy k (S i + j)) as [LT' | [-> | LT']].
  { apply Nat.le_exists_sub in LT as [d [-> _]]. 
    edestruct (PREV' d); eauto; [| lia].
    rewrite lookup_drop. by rewrite Nat.add_comm. }
  { edestruct (NOOTHER i); eauto; lia. }
  edestruct (NOOTHER (S i + j)%nat); eauto. 
  { by rewrite lookup_drop in JTH. }
  all: lia. 
Qed. 

Open Scope nat_scope. 
  
Lemma unlocked_next st (UNL: state_unlocked st):
  {i | exists v, st !! i = Some v /\ v >= 2%nat /\
            forall j v' (PREV: j < i) (JTH: st !! j = Some v'), v' < 2} +
  {Forall (eq 0%nat) st}.
Proof.
  edestruct (list_find (fun x => 2 <= x) st) eqn:IN.
  { left. destruct p as [i v]. exists i.
    apply list_find_Some in IN as (? & ? & ?). eexists. repeat split; eauto.
    intros. specialize (H1 _ _ JTH). lia. }
  right. 
  apply Forall_lookup_2. intros. 
  red in UNL. specialize (UNL _ _ H). destruct UNL; auto.
  apply list_find_None in IN. eapply Forall_lookup_1 in H; [| apply IN].
  by simpl in H. 
Qed. 

Lemma get_model_status (st: spinlock_model_impl):
  state_unlocked st * 
  ({i | exists v, st !! i = Some v /\ v >= 2 /\
              forall j v' (PREV: j < i) (JTH: st !! j = Some v'), v' < 2} + 
    {Forall (eq 0) st}) + 
  {i: nat | state_locked_by st i} +
  {~ state_unlocked st /\ ~ (exists i, state_locked_by st i)}.
  (* } + *)
  (* {True}. *)
Proof.  
  destruct (unlocked_dec st). 
  - repeat left. split; auto.
    destruct (unlocked_next st s) as [[]| ?]; [left | right]; eauto.
  - destruct (locked_dec st) as [[]| ?]; eauto.
Qed.


Lemma unlocked_locked_incompat (s: spinlock_model_impl)
      (UNLOCKED : state_unlocked s) (LOCKED: ∃ j, state_locked_by s j):
  False.
Proof.
  destruct LOCKED as [i [LOCKi]]. specialize (UNLOCKED _ _ LOCKi). lia.
Qed.

Lemma live_roles_alt (s: spinlock_model_impl) i v
        (ITH: s !! i = Some v)
        (V: v ≥ 1):
  i ∈ live_roles spinlock_model_impl s.
Proof.
  simpl. unfold spinlock_lr. apply elem_of_list_to_set, elem_of_list_In.  
  apply filter_In. split. 
  * apply in_seq. apply lookup_lt_Some in ITH. lia.
  * rewrite ITH. simpl. apply Nat.ltb_lt. lia.
Qed. 

Lemma state_locked_by_det (st: spinlock_model_impl) (i j: nat)
      (LOCKi: state_locked_by st i) (LOCKj: state_locked_by st j):
  i = j.
Proof.
  destruct LOCKi as [I1 NOJ]. destruct LOCKj as [J1 NOI].
  destruct (dec_eq_nat i j) as [? | NEQ]; auto.
  specialize (NOJ _ _ J1). lia.
Qed.

Lemma state_locked_by_simpl (st: spinlock_model_impl) (i j: nat)
      (DOMi: i < length st)
      (LOCK: state_locked_by (<[i:=1]> st) j):
  i = j.
Proof.
  destruct LOCK as [I1 NOJ].
  destruct (dec_eq_nat i j) as [? | NEQ]; auto.
  edestruct (NOJ i); eauto.
  { by eapply list_lookup_insert. }
  all: lia.
Qed. 

Lemma sm_step_le (s s': spinlock_state) (oρ: option nat)
      (STEP: spinlock_model_step s oρ s'):
  sm_order s' s.
Proof. 
  inversion STEP; subst.
  - eapply sm_order_insert; eauto. lia.
  - destruct LOCKi. eapply sm_order_insert; eauto.
  - red. apply Reflexive_instance_0. red. lia.
Qed. 

  
Program Instance spinlock_model_terminates:  
  FairTerminatingModelSimple spinlock_model_impl :=
  {|
  ftms_leq := sm_order;
  |}.
Next Obligation.
  eapply wf_projected with (f := rem_actions).
  2: { apply lt_wf. }
  unfold sm_order, rem_actions. intros x y [LE NGE].
  edestruct @not_Forall2 as (i & a & b & [? [?]]); [| eauto |..].
  { symmetry. by eapply Forall2_length. }
  { apply Nat.le_dec. }
  rewrite <- (take_drop_middle x i b), <- (take_drop_middle y i a); auto.
  repeat (rewrite list_sum_app; simpl).
  apply PeanoNat.Nat.add_le_lt_mono.
  { apply sm_order_sum_le. by apply Forall2_take. }
  apply PeanoNat.Nat.add_lt_le_mono; [lia| ].
  apply sm_order_sum_le. by apply Forall2_drop. 
Qed.
Next Obligation.
  intros. red.
  destruct (get_model_status s) as [[[UNL [[i READY] | ALL0]] | [i LOCK]] | [NO1 NO2]].
  - left. destruct READY, H. red. exists (Some i).
    eexists. econstructor; eauto. lia.
  - right. intros ACT. red in ACT. destruct ACT, H. inversion H; subst.
    1,3: eapply Forall_lookup_1 in READYi; eauto; lia.
    destruct LOCKi. eapply Forall_lookup_1 in H0; eauto. lia.
  - left. destruct LOCK. exists (Some i).
    eexists. eapply sm_unlock. red. eauto.
  - right. intros ACT. red in ACT. destruct ACT, H.
    inversion H; subst; try tauto. 
    edestruct NO2; eauto. 
Qed.
Next Obligation.
  (* TODO: refactor *)
  intros. red in ACTIVE. destruct ACTIVE, H.
  destruct x as [ρ | ].
  2: { inversion H. }
  inversion H; subst. 
  1, 2: (exists ρ; split; [by eapply fm_live_spec; eauto| subst; intros]).
  - inversion STEPρ; subst.
    2, 3: edestruct unlocked_locked_incompat; eauto.
    eapply strict_sm_order_insert; eauto.
  - inversion STEPρ; subst.
    { edestruct unlocked_locked_incompat; eauto. }
    { red in LOCKi. destruct LOCKi. eapply strict_sm_order_insert; eauto. }
    destruct LOCKED. 
    pose proof (state_locked_by_det _ _ _ LOCKi H0) as <-; eauto.
    destruct H0. rewrite H0 in READYi. inversion READYi. lia.
  - destruct LOCKED as [j LOCKED]. exists j. split.
    { eapply fm_live_spec. eapply sm_unlock; eauto. }
    intros. 
    inversion STEPρ; subst.
    { edestruct unlocked_locked_incompat; eauto. }
    { red in LOCKi. destruct LOCKi. eapply strict_sm_order_insert; eauto. }
    destruct LOCKED0. 
    pose proof (state_locked_by_det _ _ _ H0 LOCKED) as <-; eauto.
    destruct H0. rewrite H0 in READYi0. inversion READYi0. lia.
Qed.
Next Obligation.
  intros. by eapply sm_step_le. 
Qed.

Instance proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in spinlock_model_step s ℓ s' 
                                              ∨ s' = s ∧ ℓ = None): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma le_states_list (s: spinlock_model_impl):
  {l: list spinlock_state | forall s' (LE: sm_order s' s), In s' l }. 
Proof.
  induction s as [| a s [l IHl]].
  (* induction s.  *)
  { exists [[]]. intros. inversion LE. subst. simpl. tauto. }
  exists (flat_map (fun (i: nat) => map (fun s_ => i :: s_) l) (seq 0 (S a))).
  intros. inversion LE. subst. 
  apply in_flat_map.
  exists x. split.
  { apply in_seq. lia. }
  apply in_map_iff. eexists. split; eauto.
Qed.

Lemma sm_step_role_bound (s s': spinlock_state) (oρ: option nat)
      (STEP: spinlock_model_step s oρ s'):
  exists ρ, oρ = Some ρ /\ ρ < length s.
Proof.
  inversion STEP; eexists; split; eauto; apply lookup_lt_is_Some; subst; eauto.
  destruct LOCKi. eauto.
Qed. 
  
  
Lemma spinlock_model_finitary (s: spinlock_model_impl):
  Finite { '(s', ℓ) | spinlock_model_step s ℓ s' ∨ s' = s ∧ ℓ = None}.
Proof.
  destruct (le_states_list s) as [ls INls].
  set (l := (s, None) :: 
              flat_map (fun (i: nat) => map (fun s_ => (s_, Some i)) ls) (seq 0 (length s))).
  eapply in_list_finite with (l := l). intros [s' ℓ'] STEP'.
  destruct STEP' as [STEP | [-> ->]].
  2: { subst l. apply elem_of_list_here. }
  subst l. apply elem_of_list_further. 
  apply elem_of_list_In, in_flat_map.
  pose proof (sm_step_role_bound s s' ℓ' STEP) as [ρ [-> LT]].
  exists ρ. split.
  { apply in_seq. lia. }
  apply in_map_iff. eexists. split; eauto.
  apply INls. by eapply sm_step_le.
Qed.


Section SpinlockRA.
    
  Definition spinlockΣ : gFunctors :=
    #[ GFunctor (exclR unitR); GFunctor (excl_authR natO) ].
  
  Global Instance subG_spinlockΣ {Σ}:
    subG spinlockΣ Σ → spinlockPreG Σ.
  Proof. solve_inG. Qed.

End SpinlockRA.

(* (* TODO: generalize to any LSI_True model *) *)
(* Instance sl_model_inh: Inhabited (lm_ls spinlock_model). *)
(* Proof.  *)
(*   pose proof (fmrole_inhabited spinlock_model_impl) as [ρ]. *)
(*   pose proof (fmstate_inhabited spinlock_model_impl) as [s]. *)
(*   eapply populate, (initial_ls' s ρ). done. *)
(* Qed.      *)

Lemma state_unlocked_alt s:
  state_unlocked s <-> Forall (fun v => v = 0 ∨ v ≥ 2) s.
Proof. 
  by rewrite Forall_lookup.
Qed. 

Lemma state_locked_by_alt s j:
  state_locked_by s j <-> s !! j = Some 1 /\ Forall (fun v => v = 0 ∨ v ≥ 2) (take j s ++ drop (S j) s).
Proof. 
  rewrite /state_locked_by.
  apply Morphisms_Prop.and_iff_morphism; [done| ].
  rewrite Forall_app. rewrite !Forall_lookup.
  setoid_rewrite lookup_take_Some. setoid_rewrite lookup_drop.
  split.
  - intros LOCK. split.
    + intros ?? [??]. eapply LOCK; eauto. lia.
    + intros ?? ?. eapply LOCK; eauto. lia.
  - intros [LOCK1 LOCK2]. intros.
    apply not_eq in JNI as [LT | LT].
    + eapply LOCK1; eauto. 
    + apply Nat.le_succ_l in LT. apply Nat.le_sum in LT as [? ->]. 
      eapply LOCK2; eauto.
Qed.
  
Instance state_locked_by_dec s ρ: Decision (state_locked_by s ρ). 
Proof.
  eapply Decision_iff_impl.
  { symmetry. apply state_locked_by_alt. }
  apply and_dec; try solve_decision.
  apply Forall_dec. intros.
  apply or_dec; try solve_decision.
  eapply Decision_iff_impl; [apply PeanoNat.Nat.leb_le| ]. solve_decision.
Qed. 
  
Instance le_dec x y: Decision (x <= y).
Proof. eapply Decision_iff_impl; [apply PeanoNat.Nat.leb_le| ]. solve_decision. Qed.

Instance sl_dec_trans s1 ρ s2:
  Decision (fmtrans spinlock_model_impl s1 (Some ρ) s2).
Proof.
  set thread_steps_2 := exists v, s1 !! ρ = Some v /\ v >= 2 /\ state_unlocked s1 /\ s2 = (<[ρ:=1]> s1). 
  set thread_steps_1 := state_locked_by s1 ρ /\ s2 = <[ρ:=0]> s1.
  set thread_steps' := exists v, s1 !! ρ = Some v /\ v >= 2 /\ s2 = s1 /\ exists j, state_locked_by s1 j. 
  apply Decision_iff_impl with (P := thread_steps_2 \/ thread_steps_1 \/ thread_steps').
  { simpl. split.
    - intros [STEP|[STEP|STEP]]; red in STEP. 
      + destruct STEP as (?&?&?&?&->). econstructor; eauto.
      + destruct STEP as (?&->). econstructor; eauto.
      + destruct STEP as (?&?&?&->&?). econstructor; eauto.
    - intros STEP. inversion STEP; subst.
      + left. red. eauto.
      + right. left. red. eauto.
      + right. right. red. eauto. }
  repeat apply or_dec.
  - rewrite /thread_steps_2.
    apply ex_fin_dec with (l := match s1 !! ρ with Some v => [v] | _ => [] end).
    2: { intros ? (->&?&?). set_solver. }
    intros. repeat apply and_dec; try solve_decision.
    eapply Decision_iff_impl.
    { symmetry. apply state_unlocked_alt. }
    apply Forall_dec. intros. apply or_dec; solve_decision.
  - rewrite /thread_steps_1.
    apply and_dec; solve_decision.
  - rewrite /thread_steps'.
    apply ex_fin_dec with (l := match s1 !! ρ with Some v => [v] | _ => [] end).
    2: { intros ? (->&?&?). set_solver. }
    intros. repeat apply and_dec; try solve_decision. 
    apply ex_fin_dec with (l := seq 0 (length s1)). 
    2: { rewrite /state_locked_by. intros ? [IN _].
         apply in_seq. apply lookup_lt_Some in IN. lia. } 
    solve_decision. 
Qed.

Instance sl_lm_dec_ex_step:
  ∀ τ δ1,
    Decision (∃ δ2, locale_trans δ1 τ δ2 (LM := spinlock_model)).
Proof. 
  intros. Set Printing Coercions.
  pose proof (spinlock_model_finitary (ls_under δ1)) as FIN.
  (* sig *)
  (* apply finite_sig_pred_finite in FIN. red in FIN. destruct FIN as [dom FIN].  *)  
  apply locale_trans_ex_dec_fin with (steps := map (fst ∘ proj1_sig) (@enum _ _ FIN)).
  - intros. apply in_map_iff.
    unshelve eexists.
    { eapply (exist _ (s2, oρ)). by left. }
    split; [done| ]. 
    apply elem_of_list_In. apply elem_of_enum.  
  - intros. eexists. eapply rearrange_roles_spec.
    Unshelve.
    + exact spinlock_model.
    + done. 
Defined. 

Local Instance LF_SL': LMFairPre' spinlock_model.
Proof. 
  esplit; by apply _.
Defined. 

Theorem spinlock_terminates
        (extr : heap_lang_extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [program #()]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  set (Σ := gFunctors.app (heapΣ (@LM_EM_HL _ _ spinlock_model LF_SL')) spinlockΣ). 
  assert (heapGpreS Σ (@LM_EM_HL _ _ _ LF_SL')) as HPreG.
  { apply _. }
  set s0 := [2; 2] : fmstate spinlock_model_impl.
  set δ0 := initial_ls' s0 0 I: lm_ls spinlock_model.
  (* pose conv_init := ((fun hGS => LM_init_resource 0%nat δ0): heapGS Σ LM_EM_HL -> iProp Σ). *)

  unshelve eapply (simple_simulation_adequacy_terminate_ftm Σ NotStuck _ s0 ∅) =>//.
  - done. 
  - eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl.
    apply (spinlock_model_finitary s1).    
  - intros ?. iStartProof.
    rewrite /LM_init_resource.
    simpl. 
    iIntros "!> (ST & Hfr & Hf) !>". simpl.
    iAssert (|==> frag_free_roles_are ∅)%I as "-#FR".
    { rewrite /frag_free_roles_are. iApply own_unit. }
    iSplitL.
    2: { (* TODO: make a lemma, move it to simulation_adequacy_lm *)
      iIntros (?). iIntros "**". 
      iApply (fupd_mask_weaken ∅); first set_solver. by iIntros "_ !>". }
    iMod "FR" as "FR". 
    iApply (program_spec _ ∅ True _ with "[] [Hf FR ST]"); eauto. 
    { iApply ActualOwnershipPartial.
      Unshelve. set_solver. }
    (* rewrite subseteq_empty_difference_L; [| set_solver].  *)
    iFrame. iSplitR; [done| ].
    iApply has_fuels_proper; [..| iFrame]; try done.
    rewrite /spinlock_lr. simpl.
    rewrite !gset_to_gmap_union_singleton gset_to_gmap_empty.
    done. 
Qed.
