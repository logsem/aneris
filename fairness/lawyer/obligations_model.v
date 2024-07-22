From trillium.fairness Require Import fairness.

Class ObligationsParams (Degree Level Locale: Type) (LIM_STEPS: nat) := {
  opar_deg_eqdec :> EqDecision Degree;
  opar_deg_cnt :> Countable Degree;
  opar_deg_le: Degree -> Degree -> Prop;

  opar_lvl_eqdec :> EqDecision Level;
  opar_lvl_cnt :> Countable Level;  
  opar_lvl_lt: Level -> Level -> Prop;
  (* TODO: get rid of this? *)
  opar_l0: Level;
  opar_l0_least: forall l, l ≠ opar_l0 -> opar_lvl_lt opar_l0 l;
  
  opar_loc_eqdec :> EqDecision Locale;
  opar_loc_cnt :> Countable Locale;
}. 


Section Model.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).

  Definition Phase := unit.
  Definition phase_le : Phase -> Phase -> Prop := fun _ _ => True.

  Definition SignalId := nat.
  Definition SignalState: Type := Level * bool. 

  Definition CallPermission: Type := Phase * Degree.

  Definition ExpectPermission: Type := SignalId * Phase * Degree. 
  
  Record ProgressState := {
      ps_cps: gmultiset CallPermission;
      ps_sigs: gmap SignalId SignalState;
      ps_obls: gmap Locale (gset SignalId);
      ps_eps: gset ExpectPermission;
      ps_phases: gmap Locale Phase;
      ps_low_bound: nat;
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

  Definition lt_locale_obls l θ ps :=
    let obls := default ∅ (ps_obls ps !! θ) in
    let levels: gset Level := 
      set_map (fun s => from_option fst opar_l0 (ps_sigs ps !! s)) obls in
    set_Forall (opar_lvl_lt l) levels. 
    
  (* Definition phases_for_degree ps π: gset Phase := *)
    
  Inductive burns_cp: PS -> Locale -> PS -> Phase -> Degree -> Prop :=
  | bcp_step ps θ π δ π__max
      (LOC_PHASE: ps_phases ps !! θ = Some π__max)
      (LE: phase_le π π__max)
      (CP: (π, δ) ∈ ps_cps ps):
    burns_cp ps θ (update_cps (ps_cps ps ∖ {[+ (π, δ) +]}) ps) π δ. 

  Inductive lowers_cp: PS -> Locale -> PS -> Phase -> Degree -> Degree -> nat -> Prop :=
  | lcp_step ps θ π δ δ' n π__max 
      (LOC_PHASE: ps_phases ps !! θ = Some π__max)
      (PHASE_LE: phase_le π π__max)
      (CP: (π, δ) ∈ ps_cps ps)
      (DEG_LE: opar_deg_le δ' δ)
      (LOW_BOUND: n <= ps_low_bound ps):
    let new_cps := ps_cps ps ∖ {[+ (π, δ) +]} ∪ n *: {[+ (π, δ') +]} in
    lowers_cp ps θ (update_cps new_cps ps) π δ δ' n. 
      
  Inductive creates_signal: PS -> Locale -> PS -> SignalId -> Level -> Prop :=
  | cs_step ps θ s l
      (FRESH: s ∉ dom (ps_sigs ps)):
    let new_sigs := <[ s := (l, false) ]> (ps_sigs ps) in
    let cur_loc_obls := default ∅ (ps_obls ps !! θ) in
    let new_obls := <[ θ := cur_loc_obls ∪ {[ s ]} ]> (ps_obls ps) in
    let new_ps := update_obls new_obls $ update_sigs new_sigs ps in
    creates_signal ps θ new_ps s l.

  Inductive sets_signal: PS -> Locale -> PS -> SignalId -> Prop :=
  | ss_step ps θ s l v
      (SIG: ps_sigs ps !! s = Some (l, v)):
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
      (DEG_LE: opar_deg_le δ' δ):
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
    let new_cps := ps_cps ps ∪ {[+ (π__max, δ) +]} in
    expects_ep ps θ (update_cps new_cps ps) s π δ.

  Definition ghost_step ps1 θ ps2 :=
    (exists π δ, burns_cp ps1 θ ps2 π δ) \/
    (exists π δ δ' n, lowers_cp ps1 θ ps2 π δ δ' n) \/
    (exists s l, creates_signal ps1 θ ps2 s l) \/
    (exists s, sets_signal ps1 θ ps2 s) \/
    (exists s π δ δ', creates_ep ps1 θ ps2 s π δ δ') \/
    (exists s π δ, expects_ep ps1 θ ps2 s π δ).

  (* From stdpp Require Import relations. *)
  
  (* TODO: find existing definition *)
  Definition rel_compose {A: Type} (R1 R2 : relation A): relation A :=
    fun x y => exists z, R1 x z /\ R2 z y.   

  Definition progress_step ps1 θ ps2 :=
    exists n, n <= LIM_STEPS /\
          rel_compose
            (relations.nsteps (fun p1 p2 => ghost_step p1 θ p2) n)
            (fun p1 p2 => exists π δ, burns_cp p1 θ p2 π δ)
            ps1 ps2.

  Definition ObligationsModel: Model :=
    {| mtrans := progress_step |}. 

End Model.


(* TODO: move *)
From trillium.fairness Require Import execution_model. 
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat.
Section ObligationsEM.
  (* Context {DegO LevelO: ofe}.  *)
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}. 

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context {Locale: Type} {LIM_STEPS: nat}.
  Context (OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Context (OM: ObligationsModel OP).

  Let cpO := prodO unitO DegO. 
  Let sstR := prodR (agreeR LevelO) (excl' boolO).

  Let epO := prodO (prodO natO unitO) DegO. 

  Class ObligationsPreGS Σ := {
      obls_pre_cps :> inG Σ (authUR (gmultisetUR cpO));
      obls_pre_sigs :> inG Σ (authUR (gmapUR SignalId sstR));
      obls_pre_obls :> inG Σ (authUR (gmapUR Locale (gset natO)));
      obls_pre_eps :> inG Σ (authUR (gsetUR epO));
      obls_pre_phs :> inG Σ (authUR (gmapUR Locale unitO));
      obls_pre_lb :> inG Σ mono_natUR;
  }.
  Class ObligationsGS Σ := {
      obls_pre :> ObligationsPreGS Σ;
      obls_cps: gname;
      obls_sigs: gname;
      obls_obls: gname;
      obls_eps: gname;
      obls_phs: gname;
      obls_lb: gname;
  }.
  
  Context `{ObligationsGS Σ}. 

  Definition sig_map_repr smap: gmapUR SignalId sstR :=
    [^op map] sg ↦ sst ∈ smap, {[ sg := (to_agree sst.1, Excl' sst.2) ]}.
  
  Definition obls_msi (ps: ProgressState OP): iProp Σ :=
    own obls_cps (● (ps_cps OP ps)) ∗
    own obls_sigs (● (sig_map_repr (ps_sigs OP ps))) ∗
    own obls_obls (● (ps_obls OP ps)) ∗
    own obls_eps (● (ps_eps OP ps)) ∗
    own obls_phs (● (ps_phases OP ps)) ∗
    own obls_lb (●MN (ps_low_bound OP ps))
  . 
  
End ObligationsEM.
