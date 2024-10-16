Require Import Relation_Operators.
From stdpp Require Import namespaces. 
From trillium.fairness Require Import fairness locales_helpers.
From trillium.fairness.lawyer.obligations Require Import obls_utils.


Class ObligationsParams (Degree Level Locale: Type) (LIM_STEPS: nat) := {
  opar_deg_eqdec :> EqDecision Degree;
  opar_deg_cnt :> Countable Degree;
  (* opar_deg_lt: Degree -> Degree -> Prop; *)
  deg_le: relation Degree;
  deg_PO :> PartialOrder deg_le;

  opar_lvl_eqdec :> EqDecision Level;
  opar_lvl_cnt :> Countable Level;

  lvl_le: relation Level;
  lvl_PO :> PartialOrder lvl_le;
}. 


Section Model.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).
  (* opar_loc_eqdec :> EqDecision Locale; *)
  (* opar_loc_cnt :> Countable Locale; *)
  Context `{Countable Locale}. 

  Definition Phase := namespace. 
  Definition phase_le : Phase -> Phase -> Prop :=
    fun π1 π2 => (↑π2: coPset) ⊆ ↑π1. 

  Definition SignalId := nat.
  Definition SignalState: Type := Level * bool. 

  Definition CallPermission: Type := Phase * Degree.

  Definition ExpectPermission: Type := SignalId * Phase * Degree.

  Definition deg_lt := strict deg_le. 
  Definition lvl_lt := strict lvl_le. 

  (* TODO: can we merge obligations and signals? *)
  Record ProgressState := {
      ps_cps: gmultiset CallPermission;
      ps_sigs: gmap SignalId SignalState;
      ps_obls: gmap Locale (gset SignalId);
      ps_eps: gset ExpectPermission;
      ps_phases: gmap Locale Phase;
      ps_exc_bound: nat;
  }.

  Let PS := ProgressState. 

  Definition update_cps cps '(Build_ProgressState _ b c d e f) :=
    Build_ProgressState cps b c d e f. 
  Definition update_sigs sigs '(Build_ProgressState a _ c d e f) :=
    Build_ProgressState a sigs c d e f.
  Definition update_obls obls '(Build_ProgressState a b _ d e f) :=
    Build_ProgressState a b obls d e f.
  Definition update_eps eps '(Build_ProgressState a b c _ e f) :=
    Build_ProgressState a b c eps e f.
  Definition update_phases phases '(Build_ProgressState a b c d _ f) :=
    Build_ProgressState a b c d phases f.

  Definition lt_locale_obls l θ ps: Prop :=
    let obls: gset SignalId := default ∅ (ps_obls ps !! θ) in
    let levels': gset (option Level) :=
      set_map (fun s => (ps_sigs ps !! s ≫= Some ∘ fst)) obls in
    let levels := extract_Somes_gset levels' in
    set_Forall (lvl_lt l) levels.
    
  Inductive burns_cp: PS -> Locale -> PS -> Phase -> Degree -> Prop :=
  | bcp_step ps θ π δ π__max
      (LOC_PHASE: ps_phases ps !! θ = Some π__max)
      (LE: phase_le π π__max)
      (CP: (π, δ) ∈ ps_cps ps):
    burns_cp ps θ (update_cps (ps_cps ps ∖ {[+ (π, δ) +]}) ps) π δ. 

  Inductive exchanges_cp: PS -> Locale -> PS -> Phase -> Degree -> Degree -> nat -> Prop :=
  | lcp_step ps θ π δ δ' n π__max 
      (LOC_PHASE: ps_phases ps !! θ = Some π__max)
      (PHASE_LE: phase_le π π__max)
      (CP: (π, δ) ∈ ps_cps ps)
      (DEG_LE: deg_lt δ' δ)
      (LOW_BOUND: n <= ps_exc_bound ps):
    let new_cps := ps_cps ps ∖ {[+ (π, δ) +]} ⊎ n *: {[+ (π, δ') +]} in
    exchanges_cp ps θ (update_cps new_cps ps) π δ δ' n.

  Definition next_sig_id ps: SignalId :=
    list_max (elements $ dom $ ps_sigs ps) + 1. 

  Lemma next_sig_id_fresh ps:
    next_sig_id ps ∉ dom (ps_sigs ps).
  Proof using. 
    rewrite /next_sig_id. 
    intros IN. apply elem_of_elements, elem_of_list_In in IN.
    eapply List.Forall_forall in IN.
    2: { apply list_max_le. reflexivity. }
    simpl in IN. 
    clear -IN. 
    assert (forall n, n + 1 <= n -> False) as C by lia.
    by apply C in IN.
  Qed.
      
  Inductive creates_signal: PS -> Locale -> PS -> Level -> Prop :=
  | cs_step ps θ l
      (DOM: θ ∈ dom $ ps_obls ps):
    let s := next_sig_id ps in
    let new_sigs := <[ s := (l, false) ]> (ps_sigs ps) in
    let cur_loc_obls := default ∅ (ps_obls ps !! θ) in
    let new_obls := <[ θ := cur_loc_obls ∪ {[ s ]} ]> (ps_obls ps) in
    let new_ps := update_obls new_obls $ update_sigs new_sigs ps in
    creates_signal ps θ new_ps l.

  Inductive sets_signal: PS -> Locale -> PS -> SignalId -> Prop :=
  | ss_step ps θ s l v
      (SIG: ps_sigs ps !! s = Some (l, v))
      (DOM: θ ∈ dom $ ps_obls ps):
    let new_sigs := <[ s := (l, true) ]> (ps_sigs ps) in
    let cur_loc_obls := default ∅ (ps_obls ps !! θ) in
    let new_obls := <[ θ := cur_loc_obls ∖ {[ s ]} ]> (ps_obls ps) in
    let new_ps := update_obls new_obls $ update_sigs new_sigs ps in
    sets_signal ps θ new_ps s.

  Inductive creates_ep: PS -> Locale -> PS -> SignalId -> Phase -> Degree -> Degree -> Prop :=
  | cep_step ps θ s π π__max δ δ'
      (SIG: s ∈ dom (ps_sigs ps))      
      (LOC_PHASE: ps_phases ps !! θ = Some π__max)
      (LE: phase_le π π__max)
      (CP: (π, δ) ∈ ps_cps ps)
      (DEG_LE: deg_lt δ' δ):
    let new_cps := ps_cps ps ∖ {[+ (π, δ) +]} in
    let new_eps := ps_eps ps ∪ {[ (s, π, δ') ]} in
    let new_ps := update_eps new_eps $ update_cps new_cps ps in
    creates_ep ps θ new_ps s π δ δ'.

  Inductive expects_ep: PS -> Locale -> PS -> SignalId -> Phase -> Degree -> Prop :=
  | eep_step ps θ s π π__max δ l
      (LOC_PHASE: ps_phases ps !! θ = Some π__max)
      (LE: phase_le π π__max)
      (SIG: ps_sigs ps !! s = Some (l, false))
      (EP: (s, π, δ) ∈ ps_eps ps)
      (OBLS_LT: lt_locale_obls l θ ps):
    let new_cps := ps_cps ps ⊎ {[+ (π__max, δ) +]} in
    expects_ep ps θ (update_cps new_cps ps) s π δ.

  Definition fork_left (π: Phase): Phase := ndot π 0. 
  Definition fork_right (π: Phase): Phase := ndot π 1. 

  Inductive forks_locale: PS -> Locale -> PS -> Locale -> gset SignalId -> Prop :=
  | fl_step ps θ θ' π0 obls_
      (LOC_PHASE: ps_phases ps !! θ = Some π0)
      (FRESH': θ' ∉ dom $ ps_phases ps)
      :
      let cur_obls := default ∅ (ps_obls ps !! θ) in
      let obls' := cur_obls ∩ obls_ in
      let new_obls := <[ θ' := obls']> $ <[ θ := cur_obls ∖ obls' ]> $ ps_obls ps in
      let new_phases := <[ θ' := fork_right π0 ]> $ <[ θ := fork_left π0 ]> $ ps_phases ps in
      let ps' := update_phases new_phases $ update_obls new_obls ps in
      forks_locale ps θ ps' θ' obls_.

  (* Definition phase_step ps1 (θ: Phase) ps2 := *)
  (*   (exists δ, burns_cp ps1 θ ps2 δ) \/ *)
  (*   (exists δ δ' n, exchanges_cp ps1 θ ps2 δ δ' n) \/ *)
  (*   (exists l, creates_signal ps1 θ ps2 l) \/ *)
  (*   (exists s, sets_signal ps1 θ ps2 s) \/ *)
  (*   (exists s π δ δ', creates_ep ps1 θ ps2 s π δ δ') \/ *)
  (*   (exists s π δ, expects_ep ps1 θ ps2 s π δ).  *)

  (* Definition ghost_step ps1 (θ: Phase) ps2 := *)
  (*   (exists δ, burns_cp ps1 θ ps2 δ) \/ *)
  (*   (exists δ δ' n, exchanges_cp ps1 θ ps2 δ δ' n) \/ *)
  (*   (exists l, creates_signal ps1 θ ps2 l) \/ *)
  (*   (exists s, sets_signal ps1 θ ps2 s) \/ *)
  (*   (exists s π δ δ', creates_ep ps1 θ ps2 s π δ δ') \/ *)
  (*   (exists s π δ, expects_ep ps1 θ ps2 s π δ) \/ *)
  (*   (exists obls', forks_locale ps1 θ ps2 obls').  *)

  Definition loc_step ps1 θ ps2 :=
    (exists π δ, burns_cp ps1 θ ps2 π δ) \/
    (exists π δ δ' n, exchanges_cp ps1 θ ps2 π δ δ' n) \/
    (exists l, creates_signal ps1 θ ps2 l) \/
    (exists s, sets_signal ps1 θ ps2 s) \/
    (exists s π δ δ', creates_ep ps1 θ ps2 s π δ δ') \/
    (exists s π δ, expects_ep ps1 θ ps2 s π δ).

  Definition loc_step_of θ := fun ps1 ps2 => loc_step ps1 θ ps2. 
  Definition fork_step_of θ := fun ps1 ps2 => exists τ' R, forks_locale ps1 θ ps2 τ' R. 

  Notation " x ;;; y " := (rel_compose x y) (at level 20).

  Definition progress_step ps1 (θ: Locale) ps2 :=
    exists n, n <= LIM_STEPS /\
           (relations.nsteps (loc_step_of θ) n
             ;;;
            (fun p1 p2 => exists π δ, burns_cp p1 θ p2 π δ)
           )
            ps1 ps2.

  Definition progress_step_of τ := fun δ1 δ2 => progress_step δ1 τ δ2.

  Definition om_trans ps1 (θ: Locale) ps2 :=
    exists ps',
      progress_step ps1 θ ps' /\
      (clos_refl _ (fork_step_of θ)) ps' ps2. 
                  
  Definition om_trans_of τ := fun δ1 δ2 => om_trans δ1 τ δ2.

  Definition ObligationsModel: Model :=
    {| mtrans := om_trans |}. 

  (* Definition phases_incompat π1 π2 := ¬ phase_le π1 π2 /\ ¬ phase_le π2 π1. *)
  Definition phases_disj (π1 π2: Phase) := ↑ π1 ## (↑ π2: coPset).

  Global Instance phases_disj_sym: Symmetric phases_disj.
  Proof using.
    red. rewrite /phases_disj. set_solver.
  Qed. 

  Lemma phases_disj_not_le (π1 π2: Phase)
    (DISJ: phases_disj π1 π2):
      ¬ phase_le π1 π2. 
  Proof using.
    intros LE. red in DISJ.
    pose proof (coPpick_elem_of (↑ π2) (nclose_infinite _)) as IN1.
    edestruct DISJ; eauto.
  Qed.  
  
  Definition phase_lt := strict phase_le.  

  Global Instance phase_le_PreOrder: PreOrder phase_le.
  Proof.
    rewrite /phase_le. 
    split.
    - set_solver.
    - red. set_solver.
  Qed.         
  
  Lemma phase_lt_fork π (d: nat):
    phase_lt π (π .@ d).
  Proof.
    red. split.
    { apply nclose_subseteq. }
    red. rewrite /phase_le.
    (* TODO: make a lemma? *)
    intros SUB. pose proof (nclose_subseteq π (d + 1)).
    pose proof (coPpick_elem_of (↑π.@(d + 1)) (nclose_infinite _)) as IN.
    edestruct @ndot_ne_disjoint; cycle 1. 
    { apply IN. }
    { apply SUB. apply H0. done. }
    lia.
  Qed. 

  Global Instance phase_le_dec: forall x y, Decision (phase_le x y).
  Proof using. 
    intros. rewrite /phase_le. solve_decision. 
  Qed.

  Definition obls_trace_valid := trace_valid (@mtrans ObligationsModel).
  Definition obls_trace := trace (mstate ObligationsModel) (mlabel ObligationsModel).

  Definition has_obls (τ: Locale) (s: mstate ObligationsModel) := default ∅ (ps_obls s !! τ) ≠ ∅. 
  Definition obls_trace_fair := fair_by has_obls eq.


  (** Well-formedness of ProgressState *)
  
  Definition dom_phases_obls δ := dom $ ps_phases δ = dom $ ps_obls δ.

  Definition obls_assigned δ :=
    dom $ filter (fun '(s, (l, b)) => b = false) (ps_sigs δ) ⊆
    flatten_gset $ map_img $ ps_obls δ.

  Definition dom_phases_disj δ :=
    forall τ1 τ2 π1 π2, 
      τ1 ≠ τ2 ->
      ps_phases δ !! τ1 = Some π1 ->
      ps_phases δ !! τ2 = Some π2 ->
      phases_disj π1 π2. 

  Definition eps_phase_bound δ :=
    ¬ (exists τ π ep, ps_phases δ !! τ = Some π /\
                  ep ∈ ps_eps δ /\ phase_lt π ep.1.2).

  Definition cps_phase_bound δ :=
    ¬ (exists τ π cp, ps_phases δ !! τ = Some π /\
                  cp ∈ ps_cps δ /\ phase_lt π cp.1).

  Definition obligations_are_signals δ :=
    flatten_gset $ map_img $ ps_obls δ ⊆ dom $ ps_sigs δ. 

  Definition obls_disjoint δ :=
    forall τ1 τ2, τ1 ≠ τ2 -> 
             default ∅ (ps_obls δ !! τ1) ## default ∅ (ps_obls δ !! τ2).   

  Record om_st_wf (δ: ProgressState) := {
    om_wf_dpo: dom_phases_obls δ;
    om_wf_asg: obls_assigned δ;
    om_wf_ph_disj: dom_phases_disj δ;
    om_wf_cps_ph_bound: cps_phase_bound δ;
    om_wf_eps_ph_bound: eps_phase_bound δ;
    om_wf_obls_are_sigs: obligations_are_signals δ;
    om_wf_obls_disj: obls_disjoint δ;
  }.

  Definition preserved_by 
    (R: ProgressState -> ProgressState -> Prop) (P: ProgressState -> Prop) :=
    ∀ δ1 δ2, P δ1 -> R δ1 δ2 -> P δ2.
  
  Definition preserved_by_loc_step τ := preserved_by (loc_step_of τ).
  Definition preserved_by_fork τ := preserved_by (fork_step_of τ).
  Definition preserved_by_rep_loc_step τ :=
    fun P => forall n, preserved_by (relations.nsteps (loc_step_of τ) n) P. 
  Definition preserved_by_progress_step τ :=
    preserved_by (progress_step_of τ). 
  Definition preserved_by_om_trans τ :=
    preserved_by (om_trans_of τ). 

  Lemma pres_by_loc_step_implies_rep τ P
    (PRES: preserved_by_loc_step τ P)
    :
    preserved_by_rep_loc_step τ P. 
  Proof.
    red. intros n. red. intros δ1.
    induction n.
    { simpl. intros ?? ->%nsteps_0. done. }
    intros ?? (δ'&STEP1&STEP2)%rel_compose_nsteps_next.
    apply IHn in STEP1; eauto.
  Qed.

  Lemma pres_by_loc_step_implies_progress τ P
    (PPRES: preserved_by_loc_step τ P)
    :
    preserved_by_progress_step τ P. 
  Proof using.
    do 2 red. intros δ1 δ2 P1 STEP. 
    red in STEP. destruct STEP as (n&?&STEP).
    eapply rel_compose_mono in STEP.
    2: reflexivity.
    1: apply rel_compose_nsteps_next in STEP.
    2: { do 2 red. intros. by left. }    
    eapply pres_by_loc_step_implies_rep; eauto.
  Qed.

  Lemma pres_by_loc_fork_steps_implies_om_trans τ P
    (PPRES: preserved_by_loc_step τ P)
    (FPRES: preserved_by_fork τ P)
    :
    preserved_by_om_trans τ P. 
  Proof using.
    do 2 red. intros δ1 δ2 P1 STEP. 
    red in STEP. destruct STEP as (?&PSTEP&FSTEP).
    eapply pres_by_loc_step_implies_progress in PPRES.
    do 2 red in PPRES. specialize_full PPRES; eauto.
    inversion FSTEP; subst; try done.
    eapply FPRES; eauto. 
  Qed.

  Lemma pres_by_valid_trace_strong (tr: obls_trace) i j P (T: Locale -> Prop)
    (LE: i <= j)
    (VALID: obls_trace_valid tr)
    (PPRES: forall τ, T τ -> preserved_by_loc_step τ P)
    (FPRES: forall τ, T τ -> preserved_by_fork τ P)
    (Pi: from_option P True (tr S!! i))
    (Tij: forall k τ, i <= k < j -> tr L!! k = Some τ -> T τ)
    :
    from_option P True (tr S!! j). 
  Proof using.
    apply Nat.le_sum in LE as [d ->]. induction d.
    { rewrite Nat.add_0_r. done. }
    rewrite -plus_n_Sm.
    destruct (tr S!! S (i + d)) eqn:NEXT; [| done]. simpl.
    forward eapply (proj1 (next_state_lookup _ _)); eauto.
    intros [[? CUR] [? LBL]].
    rewrite CUR in IHd. simpl in IHd.
    forward eapply trace_valid_steps''; eauto.
    { rewrite Nat.add_1_r. eauto. }
    intros STEP.
    pose proof (Tij (i + d) _ ltac:(lia) LBL).
    eapply pres_by_loc_fork_steps_implies_om_trans; eauto.
    apply IHd. intros. eapply Tij; eauto. lia.  
  Qed.

  Lemma pres_by_valid_trace (tr: obls_trace) i P
    (VALID: obls_trace_valid tr)
    (PPRES: forall τ, preserved_by_loc_step τ P)
    (FPRES: forall τ, preserved_by_fork τ P)
    (Pi: from_option P True (tr S!! i)):
    forall j, i <= j -> from_option P True (tr S!! j).
  Proof using.
    intros. eapply pres_by_valid_trace_strong with (T := fun _ => True); eauto.
  Qed. 

  Ltac inv_loc_step STEP :=
    destruct STEP as [T|[T|[T|[T|[T|T]]]]];
    [destruct T as (?&?&T) |
     destruct T as (?&?&?&?&T) |
     destruct T as (?&T) |
     destruct T as (?&T) |
     destruct T as (?&?&?&?&T) |
     destruct T as (?&?&?&T) ];
    inversion T; subst. 

  Lemma loc_step_dpo_pres τ: preserved_by_loc_step τ dom_phases_obls.
  Proof using.
    do 2 red. intros δ1 δ2 PHASES_CORR STEP.
    inv_loc_step STEP; destruct δ1; try done; simpl in *. 
    - subst new_obls0. red. subst new_ps. simpl. set_solver. 
    - subst new_obls0. simpl. red. set_solver. 
  Qed.

  (* TODO: move *)
  Lemma map_split `{Countable K} {A: Type} (m: gmap K A) k:
    m = from_option (singletonM k) ∅ (m !! k) ∪ delete k m.
  Proof using.
    apply map_eq. intros k'.
    destruct (decide (k' = k)) as [->|?].
    - destruct (m !! k) eqn:KTH.
      + simpl. rewrite lookup_union_l'.
        all: by rewrite lookup_singleton.
      + simpl. rewrite lookup_union_r; [| done].
        by rewrite lookup_delete.
    - rewrite lookup_union_r.
      2: { destruct (m !! k); [| set_solver]. 
           by rewrite lookup_singleton_ne. } 
      by rewrite lookup_delete_ne.
  Qed.

  (* TODO: move *)
  Lemma flatten_gset_empty `{Countable K}:
    flatten_gset ∅ = (∅: gset K).
  Proof using. set_solver. Qed. 

  (* todo: move *)
  Lemma map_img_sets_split_helper `{Countable K, Countable A} (k: K) (m: gmap K (gset A)):
    flatten_gset $ map_img m = default ∅ (m !! k) ∪ (flatten_gset $ map_img (delete k m)).
  Proof using.
    rewrite {1}(map_split m k). rewrite map_img_union_disjoint_L.
    2: { destruct (m !! k) eqn:KTH; simpl. 
         all: apply map_disjoint_dom; set_solver. }
    rewrite flatten_gset_union. f_equal.
    destruct (m !! k) eqn:KTH; simpl.
    - by rewrite map_img_singleton_L flatten_gset_singleton.
    - by rewrite map_img_empty_L flatten_gset_empty.
  Qed. 

  Lemma loc_step_asg_pres τ: preserved_by_loc_step τ obls_assigned.
  Proof using.
    do 2 red. intros δ1 δ2 ASG STEP.
    inv_loc_step STEP; destruct δ1; try done; simpl in *. 
    - subst new_ps. red. simpl.
      subst new_sigs0 new_obls0. 
      rewrite map_filter_insert. setoid_rewrite decide_True; [| done].
      rewrite dom_insert_L.
      rewrite map_img_insert_L.
      rewrite flatten_gset_union flatten_gset_singleton.
      rewrite (union_comm_L _ {[ _ ]}) -union_assoc_L.
      apply union_mono; [done| ]. etrans; [apply ASG| ].
      simpl. rewrite {1}(map_img_sets_split_helper τ ps_obls0). done. 
    - subst new_ps. red. simpl.
      subst new_sigs0 new_obls0.
      rewrite map_filter_insert. setoid_rewrite decide_False; [| done].
      rewrite map_img_insert_L.
      rewrite flatten_gset_union flatten_gset_singleton.
      apply elem_of_dom in DOM as [obls DOM].
      subst cur_loc_obls0. rewrite DOM. simpl.

      apply elem_of_subseteq. intros s' DOM'. rewrite elem_of_union. 
      rewrite elem_of_dom in DOM'. destruct DOM' as [[l' b'] DOM'].
      apply map_filter_lookup_Some in DOM' as [DOM' ->].
      apply lookup_delete_Some in DOM' as [NEQ DOM'].
      forward eapply (@ASG s').
      { simpl. apply elem_of_dom. eexists.
        eapply map_filter_lookup_Some; eauto. split; done. }
      simpl. intros ASG'.
      apply flatten_gset_spec in ASG'. destruct ASG' as (obls'&ASG'&IN').
      apply elem_of_map_img in ASG' as [τ' ASG'].
      destruct (decide (τ' = τ)) as [-> | ]. 
      { rewrite DOM in ASG'. inversion ASG'. subst. set_solver. }
      right. apply flatten_gset_spec. eexists. split; eauto.
      apply elem_of_map_img. eexists. eapply lookup_delete_Some; eauto.
  Qed.

  Lemma loc_step_dpd_pres τ: preserved_by_loc_step τ dom_phases_disj.
  Proof using.
    do 2 red. intros δ1 δ2 DPD STEP.
    inv_loc_step STEP; destruct δ1; try done; simpl in *.
  Qed.

  Definition phases_eq R δ1 := ps_phases δ1 = R.

  Lemma loc_step_phases_pres τ R: preserved_by (loc_step_of τ) (phases_eq R).
  Proof using. 
    do 2 red. intros δ1 δ2 PH STEP.
    inv_loc_step STEP; destruct δ1; try done; simpl in *.
  Qed.

  (* TODO: move *)
  Lemma gmultiset_elem_of_weaken `{Countable K} (x y: gmultiset K) k:
    k ∈ x ∖ y -> k ∈ x.
  Proof using. multiset_solver. Qed. 

  Lemma loc_step_epb_pres' τ: preserved_by_loc_step τ 
                                (fun δ => eps_phase_bound δ /\ dom_phases_disj δ). 
  Proof using.
    do 2 red. intros δ1 δ2 [EPB DPD] STEP.
    split.
    2: { eapply loc_step_dpd_pres; eauto. } 
    pose proof (@loc_step_phases_pres _ _ _ _ ltac:(reflexivity) STEP) as PH.
    add_case (ps_eps δ2 ⊆ ps_eps δ1) EPS_LE.
    { intros LE. red. intros (τ' & π & ep & PH2 & IN & LT).
      eapply elem_of_subseteq in IN; eauto.
      rewrite PH in PH2. 
      edestruct EPB; eauto. set_solver. }
    inv_loc_step STEP; destruct δ1; try done; simpl in *.
    red. intros (τ' & π & ep & PH2 & IN & LT).
    subst new_ps new_eps0. simpl in IN.
    apply elem_of_union in IN as [IN | IN].
    { edestruct EPB; eauto. set_solver. }
    apply elem_of_singleton in IN as ->. (* simpl in *. *)
    simpl in *.
    assert (phase_lt π π__max) as LE' by set_solver.
    pose proof LE' as LE''%strict_include. 
    eapply phases_disj_not_le in LE''; eauto.
    eapply DPD; eauto; [set_solver| ..]; eapply elem_of_map_img; eauto. 
  Qed.

  Lemma loc_step_cpb_pres' τ: preserved_by_loc_step τ
                                (fun δ => cps_phase_bound δ /\ dom_phases_disj δ). 
  Proof using.
    do 2 red. intros δ1 δ2 [CPB DPD] STEP.
    split.
    2: by eapply loc_step_dpd_pres; eauto. 
    pose proof (@loc_step_phases_pres _ _ _ _ ltac:(reflexivity) STEP) as PH.
    add_case (ps_cps δ2 ⊆ ps_cps δ1) CPS_LE.
    { intros LE. red. intros (τ' & π & cp & PH2 & IN & LT).
      eapply gmultiset_elem_of_subseteq in IN; eauto.
      rewrite PH in PH2. 
      edestruct CPB; eauto. set_solver. }
    
    inv_loc_step STEP; destruct δ1; try done; simpl in *.
    - apply CPS_LE. multiset_solver.
    - red. simpl. intros (τ' & π & cp & PH2 & IN & LT).
      subst new_cps0. rewrite gmultiset_elem_of_disj_union in IN.
      destruct IN as [IN | IN].
      { apply gmultiset_elem_of_weaken in IN.
        edestruct CPB; eauto. set_solver. }
      apply gmultiset_elem_of_scalar_mul in IN as [? IN].
      apply gmultiset_elem_of_singleton in IN as ->. simpl in *.
      edestruct CPB; eauto. set_solver.
    - apply CPS_LE. multiset_solver.
    - red. simpl. intros (τ' & π & cp & PH2 & IN & LT).
      subst new_cps0. rewrite gmultiset_elem_of_disj_union in IN.
      destruct IN as [IN | IN].
      { edestruct CPB; eauto. set_solver. }
      apply gmultiset_elem_of_singleton in IN as ->. simpl in *.
      pose proof LT as LE''%strict_include. 
      eapply phases_disj_not_le in LE''; eauto.
      eapply DPD; eauto; [set_solver| ..]; eapply elem_of_map_img; eauto. 
  Qed.

  Lemma loc_step_obls_sigs_pres τ: preserved_by_loc_step τ obligations_are_signals.
  Proof using.
    do 2 red. intros δ1 δ2 OS STEP.
    inv_loc_step STEP; destruct δ1; try done; simpl in *.
    - subst new_ps. red. simpl. subst new_obls0 new_sigs0.
      rewrite map_img_insert_L dom_insert_L.
      rewrite flatten_gset_union flatten_gset_singleton.
      rewrite (union_comm_L _ {[ _ ]}) -union_assoc_L.
      apply union_mono; [done| ].
      red in OS. simpl in OS.
      etrans; [| apply OS].
      rewrite {1}(map_img_sets_split_helper τ ps_obls0). done.
    - subst new_ps. red. simpl. subst new_obls0 new_sigs0.
      etrans; [| etrans]; [| apply OS| ]; simpl.
      2: { set_solver. }
      rewrite map_img_insert_L.
      rewrite flatten_gset_union flatten_gset_singleton.
      rewrite {1}(map_img_sets_split_helper τ ps_obls0). 
      subst cur_loc_obls0. set_solver.
  Qed. 

  Lemma loc_step_obls_disj_pres' τ: preserved_by_loc_step τ
                                      (fun δ => obls_disjoint δ /\ obligations_are_signals δ). 
  Proof using.
    do 2 red. intros δ1 δ2 [DPI OS] STEP.
    split.
    2: by eapply loc_step_obls_sigs_pres; eauto. 
    inv_loc_step STEP; destruct δ1; try done; simpl in *.
    - subst new_ps. red. simpl. intros τ1 τ2 NEQ.
      subst new_obls0. simpl.

      destruct (<[τ:=cur_loc_obls0 ∪ {[s0]}]> ps_obls0 !! τ1) eqn:L1, (<[τ:=cur_loc_obls0 ∪ {[s0]}]> ps_obls0 !! τ2) eqn:L2.
      all: try set_solver. simpl.
      rewrite !lookup_insert_Some in L1, L2. subst cur_loc_obls0.
      destruct L1 as [(<- & EQ1) | (NEQ1 & EQ1)], L2 as [(<- & EQ2) | (NEQ2 & EQ2)]; try done. 
      + subst g. apply disjoint_union_l. split.
        * eapply disjoint_proper. 
          3: eapply DPI; eauto.
          ** simpl. done.
          ** simpl. rewrite EQ2. done.
        * apply disjoint_singleton_l. subst s0.
          intros IN. edestruct next_sig_id_fresh.
          apply OS. simpl. apply flatten_gset_spec. eexists. split; eauto.
          eapply elem_of_map_img; eauto. 
      + subst g0. apply disjoint_union_r. split.
        * symmetry. eapply disjoint_proper. 
          3: eapply DPI; eauto.
          ** simpl. done.
          ** simpl. rewrite EQ1. done.
        * symmetry. apply disjoint_singleton_l. subst s0.
          intros IN. edestruct next_sig_id_fresh.
          apply OS. simpl. apply flatten_gset_spec. eexists. split; eauto.
          eapply elem_of_map_img; eauto. 
      + forward eapply (DPI _ _ NEQ); eauto. simpl. rewrite EQ1 EQ2. set_solver.  
    - subst new_ps. red. simpl. intros τ1 τ2 NEQ.
      subst new_obls0. simpl.
      eapply disjoint_subseteq; revgoals.
      + eapply DPI; eauto.
      + simpl. destruct (decide (τ2 = τ)) as [-> | ?].
        * rewrite lookup_insert. set_solver.
        * rewrite lookup_insert_ne; done.
      + simpl. destruct (decide (τ1 = τ)) as [-> | ?].
        * rewrite lookup_insert. set_solver.
        * rewrite lookup_insert_ne; done.
      + apply _. 
  Qed.
        
  Lemma wf_preserved_by_loc_step τ: preserved_by (loc_step_of τ) om_st_wf.
  Proof using.
    red. intros ?? WF1 STEP. 
    split.
    - eapply loc_step_dpo_pres; eauto. apply WF1.
    - eapply loc_step_asg_pres; eauto. apply WF1.  
    - eapply loc_step_dpd_pres; eauto. apply WF1.
    - eapply loc_step_cpb_pres'; eauto. split; apply WF1.
    - eapply loc_step_epb_pres'; eauto. split; apply WF1.
    - eapply loc_step_obls_sigs_pres; eauto. apply WF1.
    - eapply loc_step_obls_disj_pres'; eauto. split; apply WF1.
  Qed.

  Lemma fork_step_obls_reorder δ1 τ δ2
    (STEP: fork_step_of τ δ1 δ2)
    (DPO1: dom_phases_obls δ1):
    flatten_gset (map_img $ ps_obls δ2) = flatten_gset (map_img $ ps_obls δ1).
  Proof using.
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst.
    assert (x ∉ dom $ ps_obls δ1) as FRESH''.
    { rewrite -DPO1; auto. }
    destruct δ1; subst; simpl in *.
subst new_obls0.
    rewrite map_img_insert_L. rewrite delete_insert_ne.
    2: { intros ->. destruct FRESH'. by apply elem_of_dom. }
    rewrite map_img_insert_L. 
    rewrite (map_img_sets_split_helper x ps_obls0).
    rewrite not_elem_of_dom_1; [| done]. 
    simpl. rewrite union_empty_l_L. erewrite !delete_notin with (i := x).
    2: { by apply not_elem_of_dom. }
    rewrite (map_img_sets_split_helper τ ps_obls0).
    rewrite !flatten_gset_union !flatten_gset_singleton.
    rewrite union_assoc_L. f_equal. 
    subst cur_obls0 obls' cur_obls.
    destruct (ps_obls0 !! τ); simpl; [| set_solver].
    apply set_eq. intros k. destruct (decide (k ∈ x0)); set_solver.
  Qed.  

  Lemma fork_step_dpo_pres τ:
    preserved_by (fork_step_of τ) dom_phases_obls. 
  Proof using.
    do 2 red. intros δ1 δ2 ASG STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst.
    destruct δ1; simpl in *.
    subst new_phases0 new_obls0.
    rewrite !dom_insert_L. set_solver.
  Qed. 

  Lemma fork_step_asg_pres' τ:
    preserved_by (fun δ1 δ2 => fork_step_of τ δ1 δ2 /\ dom_phases_obls δ1) obls_assigned.
  Proof using.
    do 2 red. intros δ1 δ2 ASG [STEP WF1].
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst.
    erewrite fork_step_obls_reorder; eauto.
    2: { red. eauto. }
    destruct δ1; subst; simpl in *. done. 
  Qed.

  Lemma phases_disj_forks π (i j: nat) (NEQ: i ≠ j):
    phases_disj (π .@ i) (π .@ j).
  Proof using.
    red. eapply ndot_ne_disjoint; eauto. 
  Qed.

  Lemma phase_disj_ndot π1 π2 (i: nat)
    (DISJ: phases_disj π1 π2):
    phases_disj (π1 .@ i) π2.
  Proof using.
    red. eapply disjoint_subseteq; [..| apply DISJ].
    - apply _.
    - apply nclose_subseteq.
    - done.
  Qed. 

  Lemma fork_step_dpd_pres τ:
    preserved_by (fork_step_of τ) dom_phases_disj.
  Proof using.
    do 2 red. intros δ1 δ2 DPD STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst. subst ps'. simpl.
    destruct δ1; simpl in *. subst new_phases0.
    intros τ1 τ2 π1 π2. 
    rewrite !lookup_insert_Some.    
    intros NEQ [[-> <-] | [NEQ1 [[<- <-]| [NEQ1' PH1]]]] [[-> <-] | [NEQ2 [[<- <-]| [NEQ2' PH2]]]]; try tauto || by apply phases_disj_forks.
    3, 4: symmetry.
    1-3: by apply phase_disj_ndot; eapply DPD; simpl; eauto. 
    { apply phase_disj_ndot. eapply DPD; [apply NEQ1'| ..]; eauto. }
    eapply DPD; [apply NEQ|..]; eauto. 
  Qed.

  Lemma fork_step_cpb_pres τ: preserved_by (fork_step_of τ) cps_phase_bound.
  Proof using.
    do 2 red. intros δ1 δ2 CPB STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst. subst ps'. simpl.
    destruct δ1; simpl in *. subst new_phases0.
    repeat setoid_rewrite lookup_insert_Some.
    intros (? & ? & ? & ([[-> <-] | [NEQ [[<- <-]| [NEQ' PH]]]] & IN & LT)).
    - destruct CPB. exists τ. do 2 eexists. split; [| split]; eauto.
      etrans; eauto. apply phase_lt_fork.
    - destruct CPB. exists τ. do 2 eexists. split; [| split]; eauto.
      etrans; eauto. apply phase_lt_fork.
    - destruct CPB. exists x1. eauto.
  Qed. 

  Lemma fork_step_epb_pres τ: preserved_by (fork_step_of τ) eps_phase_bound.
  Proof using.
    do 2 red. intros δ1 δ2 EPB STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP. subst. subst ps'. simpl.
    destruct δ1; simpl in *. subst new_phases0.
    repeat setoid_rewrite lookup_insert_Some.
    intros (? & ? & ? & ([[-> <-] | [NEQ [[<- <-]| [NEQ' PH]]]] & IN & LT)).
    - destruct EPB. exists τ. do 2 eexists. split; [| split]; eauto.
      etrans; eauto. apply phase_lt_fork.
    - destruct EPB. exists τ. do 2 eexists. split; [| split]; eauto.
      etrans; eauto. apply phase_lt_fork.
    - destruct EPB. exists x1. eauto.
  Qed. 

  Lemma fork_step_obls_sigs_pres τ: preserved_by (fun δ1 δ2 => fork_step_of τ δ1 δ2 /\ dom_phases_obls δ1) obligations_are_signals.
  Proof using.
    do 2 red. intros δ1 δ2 OS [STEP DPO1].
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP; subst.
    erewrite fork_step_obls_reorder; eauto.
    2: { red. eauto. }
    destruct δ1; simpl in *. done.
  Qed.

  (* (* TODO: move *) *)
  (* Lemma insert_lookup_eq `{Countable K} {A: Type} n a (m: gmap K A) k: *)
  (*   (<[ n := a ]> m) !! k = (if (decide (k = n)) then (Some a) else None) ⋅ (m !! k). *)

  Lemma lookup_map_singleton `{Countable K} {A: Type} (k: K) (a: A) k':
    ({[ k := a ]}: gmap K A) !! k' = if (decide (k' = k)) then Some a else None.
  Proof using.
    destruct decide; subst.
    - apply lookup_singleton.
    - by apply lookup_singleton_ne.
  Qed. 
    
  Lemma fork_step_obls_disj_pres τ:
    preserved_by (fork_step_of τ) obls_disjoint. 
  Proof using.
    do 2 red. intros δ1 δ2 OS STEP. 
    red in STEP. destruct STEP as (?&?&STEP).    
    inversion STEP; subst.
    destruct δ1; simpl in *. subst new_obls0.
    intros τ1 τ2 NEQ. 
    rewrite !insert_union_singleton_l !lookup_union.
    rewrite !lookup_map_singleton.
    
    repeat destruct decide; subst; try tauto.
    all: repeat rewrite union_Some_l; repeat rewrite option_union_left_id; simpl; subst obls' cur_obls cur_obls0.
    - eapply disjoint_subseteq.
      4: { apply OS, NEQ. }
      { apply _. }
      all: set_solver.
    - set_solver. 
    - eapply disjoint_subseteq.
      4: { symmetry. apply OS, n1. }
      { apply _. }
      all: simpl; set_solver.
    - set_solver.
    - eapply disjoint_subseteq.
      4: { symmetry. apply OS, n1. }
      { apply _. }
      all: simpl; set_solver.
    - eapply disjoint_subseteq.
      4: { apply OS, n0. }
      { apply _. }
      all: simpl; set_solver.
    - eapply disjoint_subseteq.
      4: { apply OS, n0. }
      { apply _. }
      all: simpl; set_solver.
    - eapply disjoint_subseteq.
      4: { apply OS, n0. }
      { apply _. }
      all: simpl; set_solver.
    - eapply disjoint_subseteq; eauto. apply _. 
  Qed.     
    
  Lemma wf_preserved_by_fork_step τ: preserved_by (fork_step_of τ) om_st_wf.
  Proof using.
    red. intros ?? WF1 STEP. 
    split.
    - eapply fork_step_dpo_pres; eauto. apply WF1.
    - eapply fork_step_asg_pres'; [| split]; eauto; apply WF1.
    - eapply fork_step_dpd_pres; eauto. apply WF1.
    - eapply fork_step_cpb_pres; eauto. apply WF1.
    - eapply fork_step_epb_pres; eauto. apply WF1.
    - eapply fork_step_obls_sigs_pres; [| split]; eauto; apply WF1.
    - eapply fork_step_obls_disj_pres; eauto. apply WF1.
  Qed.

  Lemma om_trans_wf_pres τ: preserved_by (om_trans_of τ) om_st_wf.
  Proof using.
    apply pres_by_loc_fork_steps_implies_om_trans.
    - apply wf_preserved_by_loc_step.
    - apply wf_preserved_by_fork_step.
  Qed.

  
    
End Model.

Ltac inv_loc_step STEP :=
    destruct STEP as [T|[T|[T|[T|[T|T]]]]];
    [destruct T as (?&?&T) |
     destruct T as (?&?&?&?&T) |
     destruct T as (?&T) |
     destruct T as (?&T) |
     destruct T as (?&?&?&?&T) |
     destruct T as (?&?&?&T) ];
    inversion T; subst. 

