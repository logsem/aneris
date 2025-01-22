Require Import Relation_Operators.
From trillium.fairness Require Import fairness.
From trillium.fairness Require Import utils.


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

  loc_eqdec :> EqDecision Locale; 
  loc_cnt :> Countable Locale; 
}. 


Section Model.
  Context `{OP: ObligationsParams Degree Level Locale LIM_STEPS}.
  
  Definition Phase := list natO.
  Definition phase_le : Phase -> Phase -> Prop := suffix. 
    
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
  Definition update_eb eb '(Build_ProgressState a b c d e _) :=
    Build_ProgressState a b c d e eb.

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

  Inductive exchanges_cp: PS -> PS -> Phase -> Degree -> Degree -> nat -> Prop :=
  | lcp_step ps π δ δ' n
      (CP: (π, δ) ∈ ps_cps ps)
      (DEG_LE: deg_lt δ' δ)
      (LOW_BOUND: n <= ps_exc_bound ps):
    let new_cps := ps_cps ps ∖ {[+ (π, δ) +]} ⊎ n *: {[+ (π, δ') +]} in
    exchanges_cp ps (update_cps new_cps ps) π δ δ' n.

  Definition next_sig_id (R: gset SignalId): SignalId :=
    list_max (elements R) + 1.

  Lemma next_sig_id_fresh R:
    next_sig_id R ∉ R.
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
    let s := next_sig_id (default ∅ (ps_obls ps !! θ) ∪ (dom $ ps_sigs ps)) in
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

  Inductive increases_eb: PS -> PS -> Prop :=
  | ieb_step ps:
    increases_eb ps (update_eb (ps_exc_bound ps + 1) ps).

  Definition ext_phase (π: Phase) (d: nat) := d :: π.
  Definition fork_left (π: Phase): Phase := ext_phase π 0.
  Definition fork_right (π: Phase): Phase := ext_phase π 1.

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

  (* small steps that are "made by" a particular locale *)
  Definition loc_step_of ps1 θ ps2 :=
    (exists π δ, burns_cp ps1 θ ps2 π δ) \/
    (exists l, creates_signal ps1 θ ps2 l) \/
    (exists s, sets_signal ps1 θ ps2 s) \/
    (exists s π δ δ', creates_ep ps1 θ ps2 s π δ δ') \/
    (exists s π δ, expects_ep ps1 θ ps2 s π δ).

  (* small steps that don't depend on any thread *)
  Definition loc_step0 ps1 ps2 :=
    (exists π δ δ' n, exchanges_cp ps1 ps2 π δ δ' n) \/
    (increases_eb ps1 ps2).

  Definition loc_step_ex ps1 ps2 :=
    (exists θ, loc_step_of ps1 θ ps2) \/ loc_step0 ps1 ps2.

  Definition loc_step_with ps1 θ ps2 :=
    loc_step_of ps1 θ ps2 \/ loc_step0 ps1 ps2.

  Definition fork_step_of θ := fun ps1 ps2 => exists τ' R, forks_locale ps1 θ ps2 τ' R.

  Definition obls_any_step_of θ := 
    fun ps1 ps2 => loc_step_ex ps1 ps2 \/ fork_step_of θ ps1 ps2. 

  Notation " x ;;; y " := (rel_compose x y) (at level 20).

  Definition progress_step ps1 (θ: Locale) ps2 :=
    exists n, n <= LIM_STEPS /\
           (relations.nsteps loc_step_ex n
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

  Definition π0: Phase := nil.

  (* Definition phases_incompat π1 π2 := ¬ phase_le π1 π2 /\ ¬ phase_le π2 π1. *)
  (* Definition phases_disj (π1 π2: Phase) := ↑ π1 ## (↑ π2: coPset). *)
  Definition phases_disj (π1 π2: Phase) := 
    ¬ phase_le π1 π2 /\ ¬ phase_le π2 π1.

  Global Instance phases_disj_sym: Symmetric phases_disj.
  Proof using.
    red. rewrite /phases_disj. set_solver.
  Qed. 

  Lemma phases_disj_not_le (π1 π2: Phase)
    (DISJ: phases_disj π1 π2):
      ¬ phase_le π1 π2. 
  Proof using.
    intros LE. red in DISJ. tauto. 
  Qed.  
  
  Definition phase_lt := strict phase_le.  

  Global Instance phase_le_PO: PartialOrder phase_le.
  Proof.
    apply _. 
  Defined. 
  
  Lemma phase_lt_fork π (d: nat):
    phase_lt π (ext_phase π d).
  Proof.
    rewrite /ext_phase. 
    apply strict_spec_alt. split; try set_solver. 
    - exists [d]. done.  
    - intros EQ. apply (f_equal length) in EQ.
      simpl in EQ. lia. 
  Qed. 

  Global Instance phase_le_dec: forall x y, Decision (phase_le x y).
  Proof using.
    solve_decision. 
  Defined. 

  Definition dom_phases_obls δ := dom $ ps_phases δ = dom $ ps_obls δ.

  Definition obls_trace_valid := trace_valid (@mtrans ObligationsModel).
  Definition obls_trace := trace (mstate ObligationsModel) (mlabel ObligationsModel).

  Definition has_obls (τ: Locale) (s: mstate ObligationsModel) := default ∅ (ps_obls s !! τ) ≠ ∅. 
  Definition obls_trace_fair := fair_by has_obls eq.

End Model.


Ltac inv_loc_step_of STEP :=
  destruct STEP as [T|[T|[T|[T|T]]]];
  [destruct T as (?π&?d&T) |
    destruct T as (?l&T) |
    destruct T as (?s&T) |
    destruct T as (?s&?π&?d&?d'&T) |
    destruct T as (?s&?π&?d&T)
  ];
  inversion T; subst. 

Ltac inv_loc_step0 STEP :=
  destruct STEP as [T|T];
  [destruct T as (?π&?d&?d'&?n&T) | ];
  inversion T; subst. 

Ltac inv_loc_step_ex STEP :=
  destruct STEP as [[?τ T]|T]; [inv_loc_step_of T | inv_loc_step0 T]. 

Ltac inv_loc_step_with STEP :=
  destruct STEP as [T | T]; [inv_loc_step_of T | inv_loc_step0 T]. 

