From trillium.fairness Require Import fairness.


Section Model.
  Context {Degree: Type}.
  Context `{Countable Degree}.
  Context {degree_le: Degree -> Degree -> Prop}.

  Context {Level: Type}.
  Context `{Countable Level}.
  Context {level_lt: Level -> Level -> Prop}.
  (* TODO: get rid of this? *)
  Context {l0: Level}.
  Context {l0_least: forall l, l ≠ l0 -> level_lt l0 l}.
  
  Context {Locale: Type}.
  Context `{Countable Locale}.

  Context {LIM_STEPS: nat}. 

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
      set_map (fun s => from_option fst l0 (ps_sigs ps !! s)) obls in
    set_Forall (level_lt l) levels. 
    
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
      (DEG_LE: degree_le δ' δ)
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
      (DEG_LE: degree_le δ' δ):
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
