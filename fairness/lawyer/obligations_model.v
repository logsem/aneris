From trillium.fairness Require Import fairness.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat.
From stdpp Require Import namespaces. 
From trillium.fairness.lawyer Require Import obls_utils.


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
  (* TODO: get rid of this? *)
  opar_l0: Level;
  opar_l0_least: forall l, l ≠ opar_l0 -> opar_lvl_lt opar_l0 l;
  
  opar_loc_eqdec :> EqDecision Locale;
  opar_loc_cnt :> Countable Locale;
}. 


Section Model.
  Context `(OP: ObligationsParams Degree Level Locale LIM_STEPS).

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

  Definition lt_locale_obls l θ ps :=
    let obls := default ∅ (ps_obls ps !! θ) in
    let levels: gset Level :=
      set_map (fun s => from_option fst opar_l0 (ps_sigs ps !! s)) obls in
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
      
  Inductive creates_signal: PS -> Locale -> PS -> Level -> Prop :=
  | cs_step ps θ s l
      (FRESH: s ∉ dom (ps_sigs ps))
      (DOM: θ ∈ dom $ ps_obls ps):
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
  | fl_step ps θ θ' π0 obls'
      (LOC_PHASE: ps_phases ps !! θ = Some π0)
      (FRESH': θ' ∉ dom $ ps_phases ps)
      :
      let new_obls := <[ θ' := obls']> $ <[ θ := (default ∅ (ps_obls ps !! θ)) ∖ obls' ]> $ ps_obls ps in
      let new_phases := <[ θ' := fork_right π0 ]> $ <[ θ := fork_left π0 ]> $ ps_phases ps in
      let ps' := update_phases new_phases $ update_obls new_obls ps in
      forks_locale ps θ ps' θ' obls'.

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

End Model.


Section ObligationsRepr.
  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO} `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  (* Context {Locale: Type}. *)
  Context {Λ: language}.
  (* Context `{Countable (locale Λ)}.  *)
  Let Locale := locale Λ. 
  Context {LIM_STEPS: nat}.
  Context (OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Let OM := ObligationsModel OP.

  Let phO := listO positiveO. 
  Let cpO := prodO phO DegO. 
  Let sstR := prodR (agreeR LevelO) (excl' boolO).
 
  Let epO := prodO (prodO natO phO) DegO.

  (* From iris.algebra.lib Require Import gset_bij.  *)
  From iris.algebra.lib Require Import gset_bij.
  From iris.base_logic.lib Require Import gset_bij.

  Class ObligationsPreGS Σ := {
      obls_pre_cps :> inG Σ (authUR (gmultisetUR cpO));
      obls_pre_sigs :> inG Σ (authUR (gmapUR SignalId sstR));
      obls_pre_obls :> inG Σ (authUR (gmapUR Locale (exclR (gsetUR natO))));
      obls_pre_eps :> inG Σ (authUR (gsetUR epO)); (* allowing duplication of eps *)
      obls_pre_phs :> inG Σ (authUR (gmapUR Locale (exclR phO)));
      obls_pre_lb :> inG Σ mono_natUR;
      si_obls_in :> gset_bijG Σ (locale Λ) Phase;
  }.
  Class ObligationsGS Σ := {
      obls_pre :> ObligationsPreGS Σ;
      obls_cps: gname;
      obls_sigs: gname;
      obls_obls: gname;
      obls_eps: gname;
      obls_phs: gname;
      obls_exc_lb: gname;
      (* obls_bij: gname; *)
  }.  

  Definition sig_map_repr smap: gmapUR SignalId sstR :=
    (fun '(l, b) => (to_agree l, Excl' b)) <$> smap. 
    (* [^op map] sg ↦ sst ∈ smap, {[ sg := (to_agree sst.1, Excl' sst.2) ]}. *)

  Definition obls_map_repr (omap: gmap Locale (gset SignalId)):
    gmapUR Locale (exclR (gsetUR natO)) :=
    Excl <$> omap.

  Definition phases_repr (pmap: gmap Locale Phase):
    gmapUR Locale (exclR phO) :=
    fmap Excl pmap (FMap := gmap_fmap).
  
  (* Context `{ObligationsGS Σ}.  *)
  (* Set Printing All. *)

  Definition eps_repr (eps: gset ExpectPermission): gsetUR epO :=
    eps.

  Definition cps_repr (cps: gmultiset (@CallPermission Degree)): (gmultisetUR cpO) := cps.

  (* Definition obls_repr (obls: gmap Locale (gset SignalId)):  *)
  
  (* Definition obls_msi `{ObligationsGS Σ} (ps: ProgressState OP): iProp Σ := *)
  (*   own obls_eps ((● (eps_repr $ ps_eps OP ps)): authUR (gsetUR epO)) *)
  (* .  *)
  Definition obls_msi `{ObligationsGS Σ} (ps: ProgressState OP): iProp Σ :=
    own obls_cps (● (cps_repr $ ps_cps OP ps)) ∗
    own obls_sigs (● (sig_map_repr $ ps_sigs OP ps)) ∗
    own obls_obls (● (obls_map_repr $ ps_obls OP ps)) ∗
    own obls_eps (● (eps_repr $ ps_eps OP ps)) ∗
    own obls_phs (● (phases_repr $ ps_phases OP ps)) ∗
    own obls_exc_lb (●MN (ps_exc_bound OP ps))
  . 
  
  From trillium.fairness Require Import execution_model.
  From iris.proofmode Require Import tactics.

  Let locales_of_cfg (c: cfg Λ): gset (locale Λ) :=
        list_to_set (locales_of_list c.1).

  Definition threads_own_obls (c: cfg Λ) (δ: mstate OM) (* m *) :=
    (* bij (locales_of_cfg c) (dom $ ps_obls OP δ).  *)
    
    (* forall ζ, ζ ∈ dom (ps_obls OP δ) <-> is_Some (from_locale c.1 ζ). *)
    
    (* gset_bijective m /\  *)
    (* set_map fst m = (locales_of_cfg c) /\ *)
    (* set_map snd m = (dom $ ps_obls OP δ).  *)
    locales_of_cfg c = dom $ ps_obls OP δ. 
    
    
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

  (* TODO: move? *)
  Ltac add_case C name :=
    match goal with
    | |- ?G => assert (C -> G) as name
    end.

  (* Definition obls_corr (δ: mstate OM) (R: gset Phase) (θ: Phase) (b: bool) := *)
  (*   θ ∉ R /\  *)
  (*   if b  *)
  (*   then dom (ps_obls OP δ) = (R ∖ {[ fork_left θ; fork_right θ ]} ∪ {[ θ ]}) /\ {[ fork_left θ; fork_right θ ]} ⊆ R *)
  (*   else dom (ps_obls OP δ) = R.  *)

  Definition obls_eq δ1 R := dom $ ps_obls OP δ1 = R.
      
  Lemma loc_step_obls_pres δ1 δ2 R θ
    (LSTEP: loc_step OP δ1 θ δ2)
    (OBLS_CORR: obls_eq δ1 R)
    (* (DOMτ: is_Some (from_locale c.1 τ)): *)
    :
    obls_eq δ2 R.
  Proof using.
    (* clear H H0 H1.  *)
    clear -LSTEP OBLS_CORR. 
    add_case (dom $ ps_obls OP δ2 = dom $ ps_obls OP δ1) SAME.
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

  (*   - destruct T as (?&T). inversion T; subst. *)
  (*     red in OBLS_CORR.  *)
  (*     destruct b1; [| set_solver]. destruct OBLS_CORR as (? & DOM1 & SUB). *)
  (*     exists false. split; [| done]. *)
  (*     red. split; auto. *)
  (*     subst ps' new_obls0. destruct δ1; simpl in *. *)
  (*     rewrite !dom_insert_L dom_delete_L. *)
  (*     rewrite DOM1. *)
  (*     rewrite difference_union_distr_l_L difference_diag_L union_empty_r_L. *)
  (*     clear -H3 SUB. *)
  (*     pose proof (ns_ndot_disj θ 0). *)
  (*     pose proof (ns_ndot_disj θ 1). *)
  (*     assert (fork_left θ ≠ fork_right θ). *)
  (*     { apply ns_ndot_diff_disj. done. } *)
  (*     rewrite difference_disjoint_L; [| set_solver]. *)
  (*     rewrite union_assoc_L. rewrite (union_comm_L {[ _ ]} _).   
      rewrite union_comm_L. rewrite difference_union_L. *)
  (*     set_solver.  *)
  (* Qed. *)

  (* Lemma ghost_step_th_obls_pres' c τ δ1 δ2 *)
  (*   (GSTEP: ghost_step OP δ1 τ δ2) *)
  (*   (TH_OWN: threads_own_obls c δ1) *)
  (*   (DOMτ: is_Some (from_locale c.1 τ)): *)
  (*   threads_own_obls' c δ2 (dom (ps_phases _ δ2) ∖ dom (ps_phases _ δ1)).  *)
  (* Proof. *)
  (* Admitted.  *)
 
  (* Lemma progress_step_th_obls_pres' c τ δ1 δ2 *)
  (*   (STEP: progress_step OP δ1 τ δ2) *)
  (*   (TH_OWN: threads_own_obls c δ1) *)
  (*   (DOMτ: is_Some (from_locale c.1 τ)): *)
  (*   threads_own_obls' c δ2 (dom (ps_phases _ δ2) ∖ dom (ps_phases _ δ1)). *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma locale_step_th_obls_pres c1 c2 τ δ *)
  (*   (STEP: locale_step c1 (Some τ) c2) *)
  (*   (TH_OWN: threads_own_obls c1 δ): *)
  (*   threads_own_obls c2 δ. *)
  (* Proof. *)
  (*   destruct c1, c2.  *)
  (*   red. intros. *)
  (*   assert (forall δ, dom (ps_obls OP δ) = dom (ps_phases OP δ)) as DOM by admit. *)    
  (*   eapply from_locale_step; eauto. *)
  (* Qed.  *)
       
  Lemma progress_step_obls_pres δ1 τ δ2 R
    (STEP: progress_step OP δ1 τ δ2)
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

  Lemma obls_eq_init δ: obls_eq δ (dom $ ps_obls OP δ).
  Proof. done. Qed. 
    
  Lemma locale_nofork_step_obls_pres c1 c2 τ θ δ1 δ2
    (STEP: locale_step c1 (Some τ) c2)
    (TH_OWN: threads_own_obls c1 δ1)
    (TRANS: progress_step OP δ1 θ δ2)
    (NOFORK: locales_of_cfg c2 = locales_of_cfg c1)
    :
    threads_own_obls c2 δ2.
  Proof.
    destruct c1 as [tp1 σ1], c2 as [tp2 σ2].
    red. rewrite NOFORK.
    eapply progress_step_obls_pres in TRANS; [| apply obls_eq_init].
    rewrite TRANS. done. 
  Qed.

  (* Definition valid_bij_step *)
  (*   (σ1: cfg Λ) (oζ: olocale Λ) (σ2: cfg Λ) *)
  (*   (δ1: mstate OM) (ℓ: mlabel OM) (δ2: mstate OM) *)
  (*   m1 m2 *)
  (*   := *)
  (*   exists ζ,  *)
  (*     threads_own_obls σ1 δ1 m1 /\ *)
  (*     threads_own_obls σ2 δ2 m2 /\  *)
  (*     oζ = Some ζ /\ (ζ, ℓ) ∈ m1 /\ *)
  (*     match decide (locales_of_cfg σ2 ∖ locales_of_cfg σ1 = ∅) with *)
  (*     | left _ => m2 = m1 *)
  (*     | right NEQ => *)
  (*         let ζ' := proj1_sig $ finitary.set_choose_L' _ NEQ in *)
  (*         m2 = (m1 ∖ {[ (ζ, ℓ) ]}) ∪ {[ (ζ, fork_left ℓ); (ζ', fork_right ℓ) ]} *)
  (*     end. *)


  (* Lemma valid_bij_nofork_restore *)
  (*   (σ1: cfg Λ) (ζ: locale Λ) (σ2: cfg Λ) *)
  (*   (δ1: mstate OM) (ℓ: mlabel OM) (δ2: mstate OM) *)
  (*   m1 *)
  (*   (TH_OWN: threads_own_obls σ1 δ1 m1) *)
  (*   (OBLS_EQ: dom $ ps_obls OP δ1 = dom $ ps_obls OP δ2) *)
  (*   (STEP_LOCS: locales_of_cfg σ1 = locales_of_cfg σ2) *)
  (*   (IN: (ζ, ℓ) ∈ m1) *)
  (*   : *)
  (*   exists m2, valid_bij_step σ1 (Some ζ) σ2 δ1 ℓ δ2 m1 m2. *)
  (* Proof.  *)
  (*   rewrite /valid_bij_step. *)
  (*   exists m1, ζ. rewrite STEP_LOCS difference_diag_L. *)
  (*   (* Set Printing All. *) *)
  (*   rewrite decide_True_pi. *)
  (*   split; auto. split; [| auto]. *)
  (*   red. rewrite -OBLS_EQ -STEP_LOCS. done. *)
  (* Qed.  *)
      
  Definition obls_valid_evolution_step
    (σ1: cfg Λ) (oζ: olocale Λ) (σ2: cfg Λ)
    (δ1: mstate OM) (ℓ: mlabel OM) (δ2: mstate OM) :=
    (* exists m1 m2, *)
      (* valid_bij_step σ1 oζ σ2 δ1 ℓ δ2 m1 m2 /\ *)
      mtrans δ1 ℓ δ2 /\
      oζ = Some ℓ                
  .


  Definition obls_si `{ObligationsGS Σ}
    (σ: cfg Λ) (δ: mstate OM): iProp Σ :=
    (* ∃ m,  *)
      obls_msi δ ∗
      ⌜ threads_own_obls σ δ (* m *)⌝
      (* ∗ gset_bij_own_auth obls_bij (DfracOwn 1) m *)
. 

  (* Definition thread_phase `{ObligationsGS Σ} (τ: locale Λ) (π: Phase): iProp Σ := *)
  (*   gset_bij_own_elem obls_bij τ π.  *)

  Definition obls_init_resource `{ObligationsGS Σ}
    (δ: mstate OM) (_: unit): iProp Σ :=
    own obls_cps (◯ (cps_repr $ ps_cps _ δ)) ∗
    own obls_sigs (◯ (sig_map_repr $ ps_sigs _ δ)) ∗
    own obls_obls (◯ (obls_map_repr $ ps_obls _ δ)) ∗
    own obls_eps (◯ (eps_repr $ ps_eps _ δ)) ∗
    own obls_phs (◯ (phases_repr $ ps_phases _ δ)) ∗
    own obls_exc_lb (◯MN (ps_exc_bound _ δ))
  .

  (* Definition obls_si_init_resource `{ObligationsGS Σ}: iProp Σ := *)
  (*   ∃ (τ: locale Λ), thread_phase τ nroot. *)

  Definition obls_is_init_st (σ: cfg Λ) (δ: mstate OM) :=
    (* exists τ0 e0, σ.1 = [e0] /\ from_locale σ.1 τ0 = Some e0 /\ *)
    (*         dom (ps_obls OP δ) = {[ τ0 ]}.  *)
    exists τ0, locales_of_cfg σ = {[ τ0 ]} /\ dom $ ps_obls OP δ = {[ τ0 ]}. 

  Let obls_Σ: gFunctors := #[
      GFunctor (authUR (gmultisetUR cpO));
      GFunctor (authUR (gmapUR SignalId sstR));
      GFunctor (authUR (gmapUR Locale (exclR (gsetR natO))));
      GFunctor (authUR (gsetUR epO));
      GFunctor (authUR (gmapUR Locale (exclR phO)));
      GFunctor (mono_natUR);
      GFunctor (gset_bijR (locale Λ) Phase)
   ].

  Definition cp `{ObligationsGS Σ} (ph: Phase) (deg: Degree): iProp Σ :=
    own obls_cps (◯ (cps_repr ({[+ ((ph, deg)) +]}))). 

  Definition cp_mul `{ObligationsGS Σ} ph deg n: iProp Σ :=
    (* fold_right bi_sep (⌜ True ⌝)%I (repeat (cp ph deg) n).  *)
    own obls_cps (◯ (n *: {[+ (ph, deg) +]})). 

  Definition cps `{ObligationsGS Σ} (m: gmultiset (@CallPermission Degree)) : iProp Σ :=
      own obls_cps (◯ (cps_repr m)). 

  Definition sgn `{ObligationsGS Σ} (sid: SignalId) (l: Level) (ob: option bool): iProp Σ :=
    own obls_sigs (◯ ({[ sid := (to_agree l, mbind (Some ∘ Excl) ob ) ]})).

  Definition obls `{ObligationsGS Σ} τ (R: gset SignalId) :=
    own obls_obls (◯ ({[ τ := Excl R]}: gmapUR Locale (exclR (gsetR natO)))).

  Definition sgns_level_gt `{ObligationsGS Σ} (R: gset SignalId) lm: iProp Σ :=
    [∗ set] s ∈ R, (∃ l, sgn s l None ∗ ⌜ opar_lvl_lt lm l ⌝). 
  
  Definition ep `{ObligationsGS Σ} (sid: SignalId) π d: iProp Σ :=
    own obls_eps (◯ {[ (sid, π, d) ]}). 

  Definition exc_lb `{ObligationsGS Σ} (n: nat) :=
    own obls_exc_lb (mono_nat_lb n).

  Definition th_phase_ge `{ObligationsGS Σ} ζ π: iProp Σ :=
    ∃ π__max, own obls_phs (◯ (phases_repr {[ ζ := π__max]})) ∗ ⌜ phase_le π π__max⌝.

  Program Definition ObligationsEM: ExecutionModel Λ OM :=
    {| 
      em_preGS := ObligationsPreGS;
      em_GS := ObligationsGS;
      em_Σ := obls_Σ;
      em_valid_evolution_step := obls_valid_evolution_step;
      em_thread_post Σ `{ObligationsGS Σ} := 
        fun τ => (obls τ ∅)%I;
      em_msi Σ `{ObligationsGS Σ} := obls_si;
      em_init_param := unit; (* ? *)
      em_init_resource Σ `{ObligationsGS Σ} := obls_init_resource;
      em_is_init_st := obls_is_init_st;
    |}.
  Next Obligation.
    solve_inG.
  Qed. 
  Next Obligation.
    simpl. intros ? PRE δ σ ? INIT. iStartProof.
    iMod (own_alloc (● (cps_repr $ ps_cps _  δ) ⋅ ◯ _)) as (?) "[CPa CPf]".
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (sig_map_repr (ps_sigs _ δ)) ⋅ ◯ _)) as (?) "[SIGSa SIGSf]".
    { apply auth_both_valid_2; [| reflexivity].
      rewrite /sig_map_repr.
      intros s. destruct lookup eqn:L; [| done].
      apply lookup_fmap_Some in L. 
      destruct L as ([l b]&<-&?).
      done. }
    iMod (own_alloc (● (obls_map_repr $ ps_obls _ δ) ⋅ ◯ _)) as (?) "[OBLSa OBLSf]". 
    { apply auth_both_valid_discrete. split; [reflexivity| ].
      intros τ. rewrite lookup_fmap. 
      by destruct lookup. }
    iMod (own_alloc (● (eps_repr $ ps_eps _ δ) ⋅ ◯ _)) as (?) "[EPSa EPSf]". 
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (phases_repr $ ps_phases _ δ) ⋅ ◯ _)) as (?) "[PHa PHf]". 
    { apply auth_both_valid_2; [| reflexivity].
      rewrite /phases_repr. intros τ. destruct lookup eqn:L; [| done].
      rewrite lookup_fmap_Some in L. destruct L as (? & <- & L). done. }
    iMod (own_alloc (●MN (ps_exc_bound _ δ) ⋅ mono_nat_lb _)) as (?) "[LBa LBf]".
    { apply mono_nat_both_valid. reflexivity. }
    iModIntro. iExists {| obls_pre := PRE; |}.
    iFrame.
    iPureIntro. red.
    red in INIT. destruct INIT as [??]. set_solver. 
  Qed.

  (* Instance foo: SingletonMS (Phase * Degree) (gmultiset CallPermission).  *)
  (* Existing Instance namespace_eq_dec.  *)
  (* Existing Instance namespace_countable.  *)

  (* Instance foo: SingletonMS (Phase * Degree) (gmultiset (@CallPermission Degree)). *)
  (* apply gmultiset_singleton. *)
  (* Defined.  *)
    
  Section ResourcesFacts.
    Context `{ObligationsGS Σ}. 
    
    (* Global Instance th_phase_ge_Pers ζ π: Persistent (th_phase_ge ζ π). *)
    
    (* ⌜ ps_phases OP δ !! τ = Some π__max /\ phase_le ph π__max /\ *)
    Lemma cp_msi_dom δ ph deg:
      ⊢ obls_msi δ -∗ cp ph deg -∗
        ⌜ (ph, deg) ∈ ps_cps OP δ ⌝.
    Proof.
      rewrite /obls_msi. iIntros "(CPS&_) CP". 
      iCombine "CPS CP" as "CPS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete, proj1 in V.
      apply gmultiset_singleton_subseteq_l.
      by apply gmultiset_included.
    Qed.

    Lemma obls_msi_exact δ ζ R:
      ⊢ obls_msi δ -∗ obls ζ R -∗
        ⌜ ps_obls OP δ !! ζ = Some R ⌝.
    Proof. 
      rewrite /obls_msi. iIntros "(_&_&OBLS&_) OB". 
      iCombine "OBLS OB" as "OBLS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      eapply singleton_included_exclusive_l in SUB; try done.
      2: { apply _. }
      apply leibniz_equiv_iff in SUB.
      rewrite lookup_fmap_Some in SUB. destruct SUB as (?&?&?).
      set_solver.
    Qed. 

    (* TODO: unify sigs_msi_.. proofs *)
    Lemma sigs_msi_in δ sid l ov:
      ⊢ obls_msi δ -∗ sgn sid l ov -∗
        ⌜ exists v, ps_sigs OP δ !! sid = Some (l, v) ⌝.
    Proof. 
      rewrite /obls_msi. iIntros "(_&SIGS&_) SIG". 
      iCombine "SIGS SIG" as "SIGS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      apply @singleton_included_l in SUB. destruct SUB as ([l' y]&SIG'&LE').

      simpl in LE'. rewrite -SIG' in LE'.
      rewrite /sig_map_repr in LE'.
      rewrite lookup_fmap in LE'.
      destruct (ps_sigs OP δ !! sid) as [[??]|] eqn:LL.
      all: rewrite LL in LE'; simpl in LE'.
      2: { apply option_included_total in LE' as [?|?]; set_solver. }
      rewrite Some_included_total in LE'.
      apply pair_included in LE' as [LE1 LE2].      
      apply to_agree_included in LE1.
      set_solver. 
    Qed. 

    Lemma sigs_msi_exact δ sid l v:
      ⊢ obls_msi δ -∗ sgn sid l (Some v) -∗
        ⌜ ps_sigs OP δ !! sid = Some (l, v) ⌝.
    Proof. 
      rewrite /obls_msi. iIntros "(_&SIGS&_) SIG". 
      iCombine "SIGS SIG" as "SIGS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      apply @singleton_included_l in SUB. destruct SUB as ([l' y]&SIG'&LE').

      simpl in LE'. rewrite -SIG' in LE'.
      rewrite /sig_map_repr in LE'.
      rewrite lookup_fmap in LE'.
      destruct (ps_sigs OP δ !! sid) as [[??]|] eqn:LL.
      all: rewrite LL in LE'; simpl in LE'.
      2: { apply option_included_total in LE' as [?|?]; set_solver. }
      rewrite Some_included_total in LE'.
      apply pair_included in LE' as [LE1 LE2].      
      apply to_agree_included in LE1.
      apply Excl_included in LE2.
      set_solver. 
    Qed.

    Instance sgn_ex_pers sid l: Persistent (sgn sid l None).
    Proof. apply _. Qed.  

    Lemma sgn_get_ex sid l ov:
      ⊢ sgn sid l ov -∗ sgn sid l ov ∗ sgn sid l None. 
    Proof.
      iIntros "SIG". rewrite -own_op. iApply own_proper; [| done]. 
      rewrite -auth_frag_op. rewrite gmap_op. simpl.
      rewrite -!insert_empty. simpl.
      erewrite <- insert_merge_r.
      2: { rewrite insert_empty. rewrite lookup_singleton. done. }
      rewrite fin_maps.RightId_instance_0.
      rewrite insert_insert.
      rewrite -pair_op. rewrite op_None_right_id.
      rewrite agree_idemp. done.
    Qed.

    (* Global Instance sgns_level_gt_pers (R: gset SignalId) lm: *)
    (*   Persistent (sgns_level_gt R lm). *)
    (* Proof. apply _. Qed.  *)

    (* Global Instance ep_pers sid π d: Persistent (ep sid π d). *)
    (* Proof. apply _. Qed.  *)

    Lemma th_phase_msi_ge_strong δ ζ π:
      ⊢ obls_msi δ -∗ th_phase_ge ζ π -∗        
        obls_msi δ ∗ ∃ π__max, own obls_phs (◯ phases_repr {[ζ := π__max]}) ∗ ⌜ ps_phases OP δ !! ζ = Some π__max /\ phase_le π π__max ⌝. 
    Proof.
      rewrite /obls_msi. iIntros "(?&?&?&?&PHASES&?) PH".
      iRevert "PHASES PH". iFrame. iIntros "PHASES PH".  
      rewrite /th_phase_ge. iDestruct "PH" as "(%π__max & PH & %LE)". 
      iDestruct (own_valid with "[PHASES PH]") as "#V".
      { iApply own_op. iApply bi.sep_comm. iFrame. }
      iDestruct "V" as %V. 
      iFrame. iExists _. iFrame. iPureIntro. 
      split; eauto. 
      apply auth_both_valid_discrete in V as [SUB V].
      rewrite /phases_repr in SUB. rewrite map_fmap_singleton in SUB. 
      apply @singleton_included_l in SUB. destruct SUB as (π'&PH'&LE').
      destruct π' as [π'| ].
      2: { specialize (V ζ). rewrite PH' in V. done. }
      apply Excl_included in LE'.
      rewrite -LE' in PH'.

      apply leibniz_equiv_iff in PH'.
      rewrite lookup_fmap_Some in PH'. by destruct PH' as (?&[=->]&?).
    Qed.

    Lemma th_phase_msi_ge δ ζ π:
      ⊢ obls_msi δ -∗ th_phase_ge ζ π -∗        
        ⌜ exists π__max, ps_phases OP δ !! ζ = Some π__max /\ phase_le π π__max ⌝. 
    Proof.
      iIntros "? ?". 
      iDestruct (th_phase_msi_ge_strong with "[$] [$]") as "[? L]".
      iDestruct "L" as (?) "[? %F]".
      iPureIntro. eauto. 
    Qed.

    Lemma exc_lb_msi_bound δ n:
      ⊢ obls_msi δ -∗ exc_lb n -∗ ⌜ n <= ps_exc_bound OP δ ⌝.
    Proof.
      rewrite /obls_msi. iIntros "(_&_&_&_&_&B) LB".
      iCombine "B LB" as "LB".
      iDestruct (own_valid with "LB") as %V. iPureIntro.
      by apply mono_nat_both_valid in V.
    Qed.

    Lemma obls_sgn_lt_locale_obls δ ζ R lm:
      ⊢ obls_msi δ -∗ obls ζ R -∗ sgns_level_gt R lm -∗
        ⌜ lt_locale_obls OP lm ζ δ ⌝.
    Proof.
      (* rewrite /obls_msi. *)
      iIntros "MSI OBLS SIGS_LT".
      iDestruct (obls_msi_exact with "[$] [$]") as %Rζ. 
      (* iIntros "(?&?&?&?&?&?) OBLS SIGS_LT". *)
      rewrite /lt_locale_obls. rewrite Rζ. simpl.
      rewrite -pure_forall_2. setoid_rewrite <- bi.pure_impl_2. 
      iIntros (l [sid [-> IN]]%elem_of_map).
      iDestruct (big_sepS_forall with "SIGS_LT") as "LT".
      iSpecialize ("LT" $! _ IN). iDestruct "LT" as "(%l & SIG & %LT)".
      iDestruct (sigs_msi_in with "[$] [$]") as %[? SIG]. rewrite SIG.
      done.
    Qed. 

    (* Global Instance th_phase_ge_pers ζ π: Persistent (th_phase_ge ζ π). *)
    (* Proof. apply _. Qed.  *)
    
    Lemma ep_msi_in δ sid π d:
      ⊢ obls_msi δ -∗ ep sid π d -∗
        ⌜ ((sid, π, d): (@ExpectPermission _)) ∈ (ps_eps OP δ) ⌝. 
    Proof. 
      rewrite /obls_msi. iIntros "(_&_&_&EPS&_) EP". 
      iCombine "EPS EP" as "EPS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      by apply gset_included, singleton_subseteq_l in SUB.
    Qed. 

  End ResourcesFacts.

  Section ResourcesUpdates.
    Context `{ObligationsGS Σ}.

    Let OU' (R: ProgressState OP -> Locale -> ProgressState OP -> Prop) ζ P: iProp Σ :=
      ∀ δ, obls_msi δ ==∗ ∃ δ', obls_msi δ' ∗ ⌜ R δ ζ δ'⌝ ∗ P. 

    Definition OU := OU' (loc_step OP). 

    Lemma OU_wand ζ P Q:
      (P -∗ Q) -∗ OU ζ P -∗ OU ζ Q.
    Proof.
      iIntros "PQ OU".
      rewrite /OU /OU'. iIntros "**".
      iSpecialize ("OU" with "[$]"). iMod "OU" as "(%&?&?&?)". iModIntro.
      iExists _. iFrame. by iApply "PQ". 
    Qed.
        
    Lemma OU_create_sig ζ R l:
      ⊢ obls ζ R -∗ OU ζ (∃ sid, sgn sid l (Some false) ∗ obls ζ (R ∪ {[ sid ]})).
    Proof.
      rewrite /OU /OU'. iIntros "OB %δ MSI".
      set (sid := list_max (elements $ dom $ sig_map_repr $ ps_sigs OP δ) + 1).
      iDestruct (obls_msi_exact with "[$] [$]") as %Rζ. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&SIGS&OBLS&?&?&?)".
      destruct δ. simpl. iFrame. simpl in *.
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _ _). 
      iRevert "SIGS OBLS". iFrame. iIntros "SIGS OBLS". simpl.
      rewrite !bi.sep_assoc. 

      assert (sid ∉ dom ps_sigs0) as FRESH.
      { subst sid. 
        rewrite dom_fmap_L.
        intros IN. apply elem_of_elements, elem_of_list_In in IN.
        eapply List.Forall_forall in IN.
        2: { apply list_max_le. reflexivity. }
        simpl in IN. 
        clear -IN. 
        assert (forall n, n + 1 <= n -> False) as C by lia.
        by apply C in IN. }

      rewrite bi.sep_comm bi.sep_assoc.  
      iSplitL.
      2: { iPureIntro.
           red. do 2 right. left. exists l. 
           erewrite (f_equal (creates_signal _ _ _)).
           { econstructor; eauto. simpl. eapply elem_of_dom; eauto. }
           simpl. reflexivity. }

      iMod (own_update with "[OB OBLS]") as "X".
      2: iCombine "OBLS OB" as "?"; iFrame.
      { apply auth_update.
        apply singleton_local_update_any.
        intros ? RR. apply lookup_fmap_Some in RR as (R_&?&Rζ_).
        rewrite Rζ in Rζ_. inversion Rζ_. subst R_. subst.
        apply exclusive_local_update with (x' := Excl (R ∪ {[sid]})). done. }
      rewrite Rζ. simpl. iDestruct "X" as "[??]".
      rewrite bi.sep_exist_r. iApply bupd_exist. iExists sid. 
      rewrite -fmap_insert. iFrame.

      rewrite -own_op. iApply own_update; [| by iFrame].
      rewrite cmra_comm. apply auth_update_alloc. 
      eapply local_update_proper.
      1: reflexivity.
      2: eapply alloc_local_update.
      { rewrite /sig_map_repr. rewrite insert_empty fmap_insert. reflexivity. }
      2: done.
      apply not_elem_of_dom. by rewrite dom_fmap.
    Qed. 

    (* TODO: do we need to generalize to "optional v" instead? *)
    Lemma OU_set_sig ζ R sid l v
      (IN: sid ∈ R):
      ⊢ obls ζ R -∗ sgn sid l (Some v) -∗
        OU ζ (sgn sid l (Some true) ∗ obls ζ (R ∖ {[ sid ]})).
    Proof.
      rewrite /OU /OU'. iIntros "OB SIG %δ MSI".
      iDestruct (sigs_msi_exact with "[$] [$]") as %Sζ.
      iDestruct (obls_msi_exact with "[$] [$]") as %Rζ. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&SIGS&OBLS&?&?&?)".
      destruct δ. simpl in *.
      iCombine "OBLS OB" as "OBLS". iCombine "SIGS SIG" as "SIGS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _ _). 
      iRevert "OBLS SIGS". iFrame. simpl. iIntros "OBLS SIGS".

      rewrite bi.sep_comm -!bi.sep_assoc.  
      iSplitR.
      { iPureIntro.
        red. do 3 right. left. exists sid. 
        erewrite (f_equal (sets_signal _ _ _)).
        { econstructor; eauto. simpl. eapply elem_of_dom; eauto. }
        simpl. reflexivity. }
      
      iMod (own_update with "OBLS") as "OBLS".
      { apply auth_update.
        apply singleton_local_update_any.
        intros ? RR. apply lookup_fmap_Some in RR as (R_&?&Rζ_).
        rewrite Rζ in Rζ_. inversion Rζ_. subst R_. subst.
        apply exclusive_local_update with (x' := Excl (R ∖ {[ sid ]})). 
        done. }
      iDestruct "OBLS" as "[??]". rewrite Rζ. simpl.
      rewrite -fmap_insert. iFrame.

      rewrite /sgn. rewrite bi.sep_comm. rewrite -!own_op.
      iApply own_update; [| by iFrame].  
      apply auth_update. simpl.
      eapply local_update_proper.
      1: reflexivity.
      2: eapply singleton_local_update_any.
      { rewrite /sig_map_repr. rewrite fmap_insert. reflexivity. }
      intros ?. rewrite /sig_map_repr.
      rewrite lookup_fmap_Some. intros [[??] [<- Sζ']].
      rewrite Sζ in Sζ'. inversion Sζ'. subst.
      apply prod_local_update'; [done| ].
      apply option_local_update.  
      by apply exclusive_local_update.
    Qed.

    Lemma exchange_cp_upd ζ π d d' b k
      (LE: k <= b)
      (DEG: opar_deg_lt d' d):
      ⊢ cp π d -∗ th_phase_ge ζ π -∗ exc_lb b -∗ OU ζ (cp_mul π d' k ∗ th_phase_ge ζ π). 
    Proof.
      rewrite /OU /OU'. iIntros "CP PH #LB %δ MSI".
      iDestruct (exc_lb_msi_bound with "[$] [$]") as %LB.
      iDestruct (th_phase_msi_ge with "[$] [$]") as %(? & ? & ?).
      iDestruct (cp_msi_dom with "[$] [$]") as %CP. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl in *.
      iCombine "CPS CP" as "CPS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _ _). 
      iRevert "CPS". iFrame. simpl. iIntros "CPS".

      rewrite bi.sep_comm -!bi.sep_assoc.  
      iSplitR.
      { iPureIntro.
        red. right. left. exists π, d, d', k. 
        erewrite (f_equal (exchanges_cp _ _ _)).
        { econstructor; eauto. simpl. lia. }
        simpl. reflexivity. }

      rewrite /cps_repr. rewrite bi.sep_comm. rewrite /cp_mul /cp. rewrite -own_op.
      iApply own_update; [| by iFrame].
      apply auth_update.
      etrans.
      { eapply gmultiset_local_update_dealloc. reflexivity. }
      rewrite gmultiset_difference_diag.
      eapply local_update_proper.
      1: reflexivity.
      2: eapply gmultiset_local_update_alloc.
      by rewrite gmultiset_disj_union_left_id. 
    Qed.

    (* TODO: ? use duplicable "signal exists" resource *)
    Lemma create_ep_upd ζ π d d' sid l ov (DEG: opar_deg_lt d' d) 
      :
      ⊢ cp π d -∗ sgn sid l ov -∗ th_phase_ge ζ π -∗ 
        OU ζ (ep sid π d' ∗ sgn sid l ov ∗ th_phase_ge ζ π).
    Proof.
      rewrite /OU /OU'. iIntros "CP SIG PH %δ MSI".
      iDestruct (sigs_msi_in with "[$] [$]") as %[v Sζ].
      iDestruct (th_phase_msi_ge with "[$] [$]") as %(? & ? & ?).
      iDestruct (cp_msi_dom with "[$] [$]") as %CP. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&SIGS&?&EPS&?&?)".
      destruct δ. simpl in *.
      iCombine "CPS CP" as "CPS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _ _). 
      iRevert "CPS EPS". iFrame. simpl. iIntros "CPS EPS".

      rewrite bi.sep_comm -!bi.sep_assoc.
      iSplitR.
      { iPureIntro.
        red. do 4 right. left. exists sid. do 3 eexists. 
        erewrite (f_equal (creates_ep _ _ _)).
        { econstructor; eauto.
          simpl. by apply elem_of_dom. }
        simpl. reflexivity. }

      rewrite /ep. rewrite /cps_repr /eps_repr. 
      rewrite bi.sep_comm -bi.sep_assoc.
      
      iMod (own_update with "EPS") as "EPS".
      { apply auth_update_alloc.
        eapply gset_local_update.
        eapply union_subseteq_l. }
      iSplitR "EPS".
      2: { iDestruct "EPS" as "[A F]".
           iSplitL "A".
           { iApply "A". }           
           iModIntro. iApply own_mono; [| by iFrame].
           apply auth_frag_mono. apply gset_included. apply union_subseteq_r. }
      
      iApply own_update; [| by iFrame].
      apply auth_update_dealloc.
      eapply local_update_proper.
      1: reflexivity.
      2: { apply gmultiset_local_update_dealloc. reflexivity. }
      rewrite gmultiset_difference_diag. set_solver.
    Qed. 
      
    Lemma expect_sig_upd ζ sid π d l R
      :
      ⊢ ep sid π d -∗ sgn sid l (Some false) -∗ obls ζ R -∗
        sgns_level_gt R l -∗ th_phase_ge ζ π -∗
        OU ζ (cp π d ∗ sgn sid l (Some false) ∗ obls ζ R ∗ th_phase_ge ζ π).
    Proof.
      rewrite /OU /OU'. iIntros "#EP SIG OBLS #SIGS_LT PH %δ MSI".
      iDestruct (sigs_msi_exact with "[$] [$]") as %Sζ.
      iDestruct (th_phase_msi_ge with "[$] [$]") as %(? & ? & ?).
      iDestruct (ep_msi_in with "[$] [$]") as %EP. 
      iDestruct (obls_sgn_lt_locale_obls with "[$] [$] [$]") as %LT. 

      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl in *.
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _ _). 
      iRevert "CPS". iFrame. simpl. iIntros "CPS".

      rewrite /cp /cps_repr /eps_repr. 
      rewrite bi.sep_comm -bi.sep_assoc.
      iSplitR.
      { iPureIntro.
        red. do 5 right. do 3 eexists. 
        erewrite (f_equal (expects_ep _ _ _)).
        { econstructor; eauto. }
        simpl. reflexivity. }

      rewrite bi.sep_comm. rewrite -own_op.
      iApply own_update; [| by iFrame].
      apply auth_update_alloc.
      eapply local_update_proper.
      1: reflexivity.
      2: eapply gmultiset_local_update_alloc.
      f_equiv. rewrite gmultiset_disj_union_left_id. set_solver.
    Qed. 

    (* TODO: ? refactor these proofs about burn_cp *)
    Lemma burn_cp_upd_impl δ ζ π deg
      (PH_MAX: exists π__max, ps_phases OP δ !! ζ = Some π__max /\ phase_le π π__max)
      :
      ⊢ obls_msi δ -∗ cp π deg ==∗ ∃ δ', obls_msi δ' ∗ ⌜ burns_cp OP δ ζ δ' π deg⌝.
    Proof.
      iIntros "MSI CP".
      iDestruct (cp_msi_dom with "[$] [$]") as "%IN". 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl in *. iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _ _). 
      simpl. iRevert "CPS". iFrame. iIntros "CPS". simpl.
      rewrite /cp.
      iCombine "CPS CP" as "CPS". iMod (own_update with "CPS").
      { apply auth_update_dealloc.
        eapply local_update_proper; [..| eapply gmultiset_local_update_dealloc].
        1, 3: reflexivity.
        f_equiv. by rewrite gmultiset_difference_diag. }
      iModIntro. iFrame. iPureIntro.
      destruct PH_MAX as (?&?&?). 
      erewrite (f_equal (burns_cp _ _ _)).
      { econstructor; eauto. }
      done. 
    Qed.

    Lemma burn_cp_upd_burn ζ π deg:
      ⊢ cp π deg -∗ th_phase_ge ζ π -∗ 
        OU' (fun δ1 ζ' δ2 => burns_cp OP δ1 ζ' δ2 π deg) ζ (th_phase_ge ζ π). 
    Proof.
      rewrite /OU'. iIntros "CP PH % MSI".
      iDestruct (th_phase_msi_ge with "[$] [$]") as %(? & ? & ?). 
      iMod (burn_cp_upd_impl with "[$] [$]") as "R"; eauto.
      iDestruct "R" as "(%&?&?)". iModIntro. iExists _. iFrame.
    Qed.

    Lemma burn_cp_upd ζ π deg:
      ⊢ cp π deg -∗ th_phase_ge ζ π -∗ OU ζ (th_phase_ge ζ π). 
    Proof.
      iIntros "??".
      iPoseProof (burn_cp_upd_burn with "[$] [$]") as "OU'".
      rewrite /OU /OU'. iIntros "% MSI".
      iMod ("OU'" with "[$]") as "(%&?&%&?)". iModIntro.
      iExists _. iFrame. iPureIntro.
      red. eauto.
    Qed. 

    Lemma cp_mul_take ph deg n:
      cp_mul ph deg (S n) ⊣⊢ cp_mul ph deg n ∗ cp ph deg.
    Proof. 
      rewrite /cp_mul. rewrite -own_op -auth_frag_op. 
      iApply own_proper. f_equiv.
      rewrite gmultiset_op.
      by rewrite gmultiset_scalar_mul_S_r. 
    Qed.

    (* TODO: refactor *)
    Definition phase_lt π1 π2 := phase_le π1 π2 /\ π1 ≠ π2.

    (* TODO: make an instance*)
    Lemma phase_le_refl π: phase_le π π.
    Proof. set_solver. Qed. 

    (* TODO: ? refactor these proofs about fork step *)
    Lemma fork_locale_upd_impl δ ζ ζ' π R0 R'
      (FRESH: ζ' ∉ dom $ ps_phases OP δ)
      (* TODO: where else it's needed? *)
      (DOM_EQ: dom $ ps_phases OP δ = dom $ ps_obls OP δ)
      :
      ⊢ obls_msi δ -∗ th_phase_ge ζ π -∗ obls ζ R0 ==∗ 
        ∃ δ' π1 π2, obls_msi δ' ∗ th_phase_ge ζ π1 ∗ th_phase_ge ζ' π2 ∗
                    obls ζ (R0 ∖ R') ∗ obls ζ' R' ∗
                    ⌜ forks_locale OP δ ζ δ' ζ' R' ⌝.
    Proof.
      iIntros "MSI PH OB".
      iDestruct (th_phase_msi_ge_strong with "[$] [$]") as "(MSI & %π0 & (PH & %PH & %PLE))".
      iDestruct (obls_msi_exact with "[$] [$]") as %OBLS. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&?&OBLS&?&PHASES&?)".
      destruct δ. simpl in *. iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _ _). 
      simpl. iRevert "OBLS PHASES". iFrame. iIntros "OBLS PHASES". simpl.
      iCombine "OBLS OB" as "OBLS". iCombine "PHASES PH" as "PHASES".
      iExists (fork_left π0), (fork_right π0).

      rewrite !bi.sep_assoc. iSplitL.
      2: { iPureIntro.
           erewrite (f_equal (forks_locale _ _ _)).
           { econstructor; eauto. }
           simpl. reflexivity. }

      rewrite !OBLS. simpl.  
      rewrite -(bi.sep_assoc _ _ (obls _ _)). rewrite bi.sep_comm.
      rewrite -!bi.sep_assoc.
      do 2 rewrite bi.sep_assoc. 
      rewrite -bupd_sep. 
      iSplitL "OBLS". 
      - rewrite -!own_op. iApply own_update; [| by iFrame].
        rewrite -auth_frag_op. rewrite (cmra_comm (◯ _) _).
        etrans.
        2: { rewrite auth_frag_op.
             rewrite (cmra_comm (◯ _) _). rewrite cmra_assoc cmra_comm.
             apply cmra_update_op; [reflexivity| ].
             apply auth_update_alloc.
             rewrite /obls_map_repr. rewrite fmap_insert.
             apply alloc_singleton_local_update; [| done].
             apply not_elem_of_dom. rewrite dom_fmap dom_insert_L.
             rewrite not_elem_of_union not_elem_of_singleton. split.
             - intros ->. destruct FRESH. by apply elem_of_dom.
             - by rewrite -DOM_EQ. }
        rewrite (cmra_comm (◯ _) _).
        apply auth_update.
        rewrite fmap_insert. apply singleton_local_update_any.
        intros. apply exclusive_local_update. done.
      - rewrite /th_phase_ge.
        rewrite !bi.sep_exist_l; iExists _.
        rewrite !bi.sep_assoc. iSplitL.
        2: { iPureIntro. apply phase_le_refl. }
        rewrite bi.sep_comm.
        rewrite !bi.sep_exist_l; iExists _.
        rewrite !bi.sep_assoc. iSplitL.
        2: { iPureIntro. apply phase_le_refl. }
        rewrite -bi.sep_assoc bi.sep_comm.
        rewrite -!own_op. iApply own_update; [| by iFrame].
        etrans.
        2: { rewrite cmra_comm. rewrite cmra_assoc.
             apply cmra_update_op; [| reflexivity].
             rewrite cmra_comm. apply auth_update_alloc.
             rewrite /phases_repr !fmap_insert. 
             rewrite fmap_empty insert_empty.
             apply alloc_singleton_local_update; [| done].
             apply not_elem_of_dom. rewrite dom_insert_L dom_fmap.
             rewrite not_elem_of_union not_elem_of_singleton. split.
             - intros ->. destruct FRESH. by apply elem_of_dom.
             - done. }
        apply auth_update.
        rewrite /phases_repr !fmap_insert. 
        rewrite fmap_empty insert_empty.
        apply singleton_local_update_any.
        intros. eapply exclusive_local_update. done.
        Unshelve. apply excl_exclusive.
    Qed.       

  End ResourcesUpdates.

End ObligationsRepr.
