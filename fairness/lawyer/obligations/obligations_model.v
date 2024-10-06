From stdpp Require Import namespaces. 
From trillium.fairness Require Import fairness locales_helpers.
From trillium.fairness.lawyer.obligations Require Import obls_utils.


Class ObligationsParams 
  (Degree Level Locale: Type)
  (* (Degree Level: Type) *)
  (LIM_STEPS: nat) := {
  opar_deg_eqdec :> EqDecision Degree;
  opar_deg_cnt :> Countable Degree;
  opar_deg_lt: Degree -> Degree -> Prop;

  opar_lvl_eqdec :> EqDecision Level;
  opar_lvl_cnt :> Countable Level;

  opar_lvl_lt: Level -> Level -> Prop;
  (* (* TODO: get rid of this? *) *)
  (* opar_l0: Level; *)
  (* opar_l0_least: forall l, l ≠ opar_l0 -> opar_lvl_lt opar_l0 l; *)
  
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
    set_Forall (opar_lvl_lt l) levels.
    
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
      (DEG_LE: opar_deg_lt δ' δ)
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
      (DEG_LE: opar_deg_lt δ' δ):
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
    let new_cps := ps_cps ps ⊎ {[+ (π, δ) +]} in
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

  Require Import Relation_Operators.

  Notation " x ;;; y " := (rel_compose x y) (at level 20).

  Definition progress_step ps1 (θ: Locale) ps2 :=
    exists n, n <= LIM_STEPS /\
           (relations.nsteps (fun p1 p2 => loc_step p1 θ p2) n
             ;;;
            (fun p1 p2 => exists π δ, burns_cp p1 θ p2 π δ)
           )
            ps1 ps2.

  Definition om_trans ps1 (θ: Locale) ps2 :=
    exists ps',
      progress_step ps1 θ ps' /\
      (clos_refl _ (fun p1 p2 => exists τ' R, forks_locale p1 θ p2 τ' R)) ps' ps2. 
                  
  Definition ObligationsModel: Model :=
    {| mtrans := om_trans |}. 


    
  (* Lemma burns_cp_th_obls_pres c τ δ1 δ2 d *)
  (*   (BURN: burns_cp OP δ1 τ δ2 d) *)
  (*   (TH_OWN: threads_own_obls c δ1): *)
  (*   threads_own_obls c δ2. *)
  (* Proof. *)
  (*   inversion BURN; subst. *)
  (*   by destruct δ1. *)
  (* Qed. *)

  (* (* TODO: rename *) *)
  (* Lemma too_too' (c: cfg Λ) (δ: mstate OM) (θ: Phase) *)
  (*   (IN: θ ∈ dom $ ps_obls OP δ) *)
  (*   (TOO: thread_ *)

  (* TODO: can be proved simpler if we could unfold ndot *)
  Lemma ns_ndot_disj (ns: namespace) (i: nat):
    ns ≠ ns .@ i.
  Proof.
    intros EQ.
    pose proof (coPpick_elem_of (↑ ns .@ (i + 1)) (nclose_infinite _)) as IN.
    pose proof IN as IN'. rewrite {2}EQ in IN'.
    apply nclose_subseteq in IN'.
    edestruct @ndot_ne_disjoint; [| apply IN | apply IN'].
    lia.
  Qed. 

  (* TODO: can be proved simpler if we could unfold ndot *)
  Lemma ns_ndot_diff_disj (ns: namespace) (i j: nat)
    (NEQ: i ≠ j):
    ns .@ i ≠ ns .@ j.
  Proof.
    intros EQ.
    pose proof (coPpick_elem_of (↑ ns .@ i) (nclose_infinite _)) as IN1.
    pose proof (coPpick_elem_of (↑ ns .@ j) (nclose_infinite _)) as IN2.
    rewrite -{1}EQ in IN2. 
    edestruct @ndot_ne_disjoint; [| apply IN1 | apply IN2].
    done. 
  Qed. 

  (* Definition obls_corr (δ: mstate OM) (R: gset Phase) (θ: Phase) (b: bool) := *)
  (*   θ ∉ R /\  *)
  (*   if b  *)
  (*   then dom (ps_obls OP δ) = (R ∖ {[ fork_left θ; fork_right θ ]} ∪ {[ θ ]}) /\ {[ fork_left θ; fork_right θ ]} ⊆ R *)
  (*   else dom (ps_obls OP δ) = R.  *)

  Definition obls_eq δ1 R := dom $ ps_obls δ1 = R.
      
  Lemma loc_step_obls_pres δ1 δ2 R θ
    (LSTEP: loc_step δ1 θ δ2)
    (OBLS_CORR: obls_eq δ1 R)
    (* (DOMτ: is_Some (from_locale c.1 τ)): *)
    :
    obls_eq δ2 R.
  Proof using.
    (* clear H H0 H1.  *)
    clear -LSTEP OBLS_CORR. 
    add_case (dom $ ps_obls δ2 = dom $ ps_obls δ1) SAME.
    { intros EQ. red. by rewrite EQ. }
    
    red in LSTEP. destruct LSTEP as [T|[T|[T|[T|[T|T]]]]].
    - destruct T as (?&?&T). inversion T; subst.
      apply SAME. by destruct δ1. 
    - destruct T as (?&?&?&?&T). inversion T; subst. 
      apply SAME. by destruct δ1. 
    - destruct T as (?&T). inversion T; subst.
      apply SAME. destruct δ1. simpl in *.
      subst new_obls0. rewrite dom_insert_L. simpl. set_solver. 
    - destruct T as (?&T). inversion T; subst.
      apply SAME. destruct δ1. simpl in *.  
      subst new_obls0. simpl.
      rewrite dom_insert_L. 
                                            set_solver. 
    - destruct T as (?&?&?&?&T). inversion T; subst.
      apply SAME. by destruct δ1. 
    - destruct T as (?&?&?&T). inversion T; subst.
      apply SAME. by destruct δ1.
  Qed.     
           
  Lemma progress_step_obls_pres δ1 τ δ2 R
    (STEP: progress_step δ1 τ δ2)
    (TH_OWN: obls_eq δ1 R)
    (* (DOMτ: is_Some (from_locale c.1 τ)) *)
    :
    obls_eq δ2 R.
  Proof.
    red in STEP. destruct STEP as (n&?&STEP).
    eapply rel_compose_mono in STEP.
    2: reflexivity.
    1: apply rel_compose_nsteps_next in STEP.
    2: { do 2 red. intros. by left. }
    (* clear -(* DOMτ *) OM STEP TH_OWN. *)
    generalize dependent δ2. induction n.
    { simpl. intros ? ?%nsteps_once_inv. by eapply loc_step_obls_pres. }
    intros ? (δ'&STEP1&STEP2)%rel_compose_nsteps_next.
    apply IHn in STEP1. eapply loc_step_obls_pres; eauto.
    lia. 
  Qed.

  Lemma obls_eq_init δ: obls_eq δ (dom $ ps_obls δ).
  Proof. done. Qed. 
    
  Definition dom_phases_obls δ := dom $ ps_phases δ = dom $ ps_obls δ. 
  Definition phases_eq δ1 R := ps_phases δ1 = R.

  Lemma loc_step_phases_pres δ1 δ2 θ R
    (LSTEP: loc_step δ1 θ δ2)
    (PHASES_CORR: phases_eq δ1 R)
    :
    phases_eq δ2 R.
  Proof using.
    clear -LSTEP PHASES_CORR.
    red in LSTEP. destruct LSTEP as [T|[T|[T|[T|[T|T]]]]].
    - destruct T as (?&?&T). inversion T; subst.
      by destruct δ1. 
    - destruct T as (?&?&?&?&T). inversion T; subst. 
      by destruct δ1. 
    - destruct T as (?&T). inversion T; subst.
      destruct δ1. simpl in *.
      subst new_obls0. red. subst new_ps. simpl. set_solver. 
    - destruct T as (?&T). inversion T; subst.
      destruct δ1. simpl in *.  
      subst new_obls0. simpl.
      red. set_solver. 
    - destruct T as (?&?&?&?&T). inversion T; subst.
      by destruct δ1. 
    - destruct T as (?&?&?&T). inversion T; subst.
      by destruct δ1.
  Qed. 

  (* TODO: refactor *)
  Lemma loc_step_nsteps_phases_pres δ1 δ2 θ R n
    (LSTEPS: relations.nsteps (fun p1 p2 => loc_step p1 θ p2) n δ1 δ2)
    (PHASES_CORR: phases_eq δ1 R)
    :
    phases_eq δ2 R.
  Proof.
    generalize dependent δ2. induction n.
    { simpl. intros ? ->%nsteps_0. done. }
    intros ? (δ'&STEP1&STEP2)%rel_compose_nsteps_next.
    apply IHn in STEP1. eapply loc_step_phases_pres; eauto.
  Qed. 

  (* TODO: refactor *)
  Lemma progress_step_phases_pres δ1 τ δ2 R
    (STEP: progress_step δ1 τ δ2)
    (DPO: phases_eq δ1 R)
    (* (DOMτ: is_Some (from_locale c.1 τ)) *)
    :
    phases_eq δ2 R.
  Proof.
    red in STEP. destruct STEP as (n&?&STEP).
    eapply rel_compose_mono in STEP.
    2: reflexivity.
    1: apply rel_compose_nsteps_next in STEP.
    2: { do 2 red. intros. by left. }
    eapply loc_step_nsteps_phases_pres; eauto.
  Qed.

  Lemma phases_eq_init δ: phases_eq δ (ps_phases δ).
  Proof. done. Qed. 

  (* TODO: refactor *)
  Lemma progress_step_dpo_pres δ1 τ δ2
    (STEP: progress_step δ1 τ δ2)
    (DPO: dom_phases_obls δ1)
    :
    dom_phases_obls δ2.
  Proof.
    red. erewrite progress_step_obls_pres; [| eauto| apply obls_eq_init].
    erewrite progress_step_phases_pres; [| eauto| apply phases_eq_init]. 
    apply DPO. 
  Qed.

  Global Instance phase_le_PreOrder: PreOrder phase_le.
  Proof.
    rewrite /phase_le. 
    split.
    - set_solver.
    - red. set_solver.
  Qed.         
  
  (* TODO: refactor *)
  Definition phase_lt := strict phase_le.
  
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

  Definition obls_trace_valid := trace_valid (@mtrans ObligationsModel).
  Definition obls_trace := trace (mstate ObligationsModel) (mlabel ObligationsModel).

  Definition has_obls (τ: Locale) (s: mstate ObligationsModel) := default ∅ (ps_obls s !! τ) ≠ ∅. 
  Definition obls_trace_fair := fair_by has_obls eq.

End Model.
