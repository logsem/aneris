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
      
  Inductive creates_signal: PS -> Locale -> PS -> Level -> Prop :=
  | cs_step ps θ s l
      (FRESH: s ∉ dom (ps_sigs ps)):
    let new_sigs := <[ s := (l, false) ]> (ps_sigs ps) in
    let cur_loc_obls := default ∅ (ps_obls ps !! θ) in
    let new_obls := <[ θ := cur_loc_obls ∪ {[ s ]} ]> (ps_obls ps) in
    let new_ps := update_obls new_obls $ update_sigs new_sigs ps in
    creates_signal ps θ new_ps l.

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
    (exists l, creates_signal ps1 θ ps2 l) \/
    (exists s, sets_signal ps1 θ ps2 s) \/
    (exists s π δ δ', creates_ep ps1 θ ps2 s π δ δ') \/
    (exists s π δ, expects_ep ps1 θ ps2 s π δ).

  (* From stdpp Require Import relations. *)
  
  (* TODO: find existing definition *)
  Definition rel_compose {A: Type} (R1 R2 : relation A): relation A :=
    fun x y => exists z, R1 x z /\ R2 z y.

  (* TODO: find existing *)
  Global Instance rel_subseteq {A: Type}: SubsetEq (relation A) :=
    fun R1 R2 => forall x y, R1 x y -> R2 x y. 
  
  Global Instance rel_compose_mono {A: Type}:
    Proper (subseteq ==> subseteq ==> subseteq) (@rel_compose A).
  Proof.
    red. intros ??????. rewrite /rel_compose.
    red. intros ?? (?&?&?). eexists. eauto.
  Qed.

  Lemma rel_compose_nsteps_plus {A: Type} (r: relation A) n m:
    forall x y,
    rel_compose (relations.nsteps r n) (relations.nsteps r m) x y <->
    relations.nsteps r (n + m) x y.
  Proof using.
    clear. 
    intros. 
  Admitted.
           
  Lemma rel_compose_nsteps_next {A: Type} (r: relation A) n:
    forall x y,
    rel_compose (relations.nsteps r n) r x y <->
    relations.nsteps r (S n) x y.
  Proof using.
    intros. rewrite -Nat.add_1_r. 
    rewrite -rel_compose_nsteps_plus.
    apply exist_proper. intros.
    apply Morphisms_Prop.and_iff_morphism; auto.
    split; intros.
    - by apply nsteps_once.
    - by apply nsteps_once_inv.
  Qed.            

  Global Instance rel_subseteq_po {A: Type}: PreOrder (@rel_subseteq A).
  Proof.
    rewrite /rel_subseteq. split; eauto.
  Qed. 

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
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat.
Section ObligationsRepr.
  (* Context {DegO LevelO: ofe}.  *)
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}. 

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  (* Context {Locale: Type}. *)
  Context {Λ: language}.
  Let Locale := locale Λ. 
  Context {LIM_STEPS: nat}.
  Context (OP: ObligationsParams Degree Level Locale LIM_STEPS).
  Let OM := ObligationsModel OP.

  Let cpO := prodO unitO DegO. 
  Let sstR := prodR (agreeR LevelO) (excl' boolO).

  Let epO := prodO (prodO natO unitO) DegO. 

  Class ObligationsPreGS Σ := {
      obls_pre_cps :> inG Σ (authUR (gmultisetUR cpO));
      obls_pre_sigs :> inG Σ (authUR (gmapUR SignalId sstR));
      obls_pre_obls :> inG Σ (authUR (gmapUR Locale (exclR (gsetR natO))));
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
  

  Definition sig_map_repr smap: gmapUR SignalId sstR :=
    (fun '(l, b) => (to_agree l, Excl' b)) <$> smap. 
    (* [^op map] sg ↦ sst ∈ smap, {[ sg := (to_agree sst.1, Excl' sst.2) ]}. *)

  Definition obls_map_repr omap: gmapUR Locale (exclR (gsetR natO)) :=
    Excl <$> omap. 
  
  (* Context `{ObligationsGS Σ}.  *)
  Definition obls_msi `{ObligationsGS Σ} (ps: ProgressState OP): iProp Σ :=
    own obls_cps (● (ps_cps OP ps)) ∗
    own obls_sigs (● (sig_map_repr $ ps_sigs OP ps)) ∗
    own obls_obls (● (obls_map_repr $ ps_obls OP ps)) ∗
    own obls_eps (● (ps_eps OP ps)) ∗
    own obls_phs (● (ps_phases OP ps)) ∗
    own obls_lb (●MN (ps_low_bound OP ps))
  . 
  
  From trillium.fairness Require Import execution_model.
  From iris.proofmode Require Import tactics.

  Let obls_Σ: gFunctors := #[
      GFunctor (authUR (gmultisetUR cpO));
      GFunctor (authUR (gmapUR SignalId sstR));
      GFunctor (authUR (gmapUR Locale (exclR (gsetR natO))));
      GFunctor (authUR (gsetUR epO));
      GFunctor (authUR (gmapUR Locale unitO));
      GFunctor (mono_natUR)
   ].

  Definition threads_own_obls (c: cfg Λ) (δ: mstate OM) :=
    forall ζ, ζ ∈ dom (ps_obls OP δ) -> is_Some (from_locale c.1 ζ).

  Lemma burns_cp_th_obls_pres c τ δ1 δ2 π d
    (BURN: burns_cp OP δ1 τ δ2 π d)
    (TH_OWN: threads_own_obls c δ1):
    threads_own_obls c δ2.
  Proof.
    inversion BURN; subst.
    by destruct δ1.
  Qed.

  Lemma ghost_step_th_obls_pres c τ δ1 δ2
    (GSTEP: ghost_step OP δ1 τ δ2)
    (TH_OWN: threads_own_obls c δ1)
    (DOMτ: is_Some (from_locale c.1 τ)):
    threads_own_obls c δ2.
  Proof.
    red in GSTEP. destruct GSTEP as [T|[T|[T|[T|[T|T]]]]].
    - destruct T as (?&?&T). inversion T; subst. by destruct δ1.
    - destruct T as (?&?&?&?&T). inversion T; subst. by destruct δ1.
    - destruct T as (?&T). inversion T; subst.
      red. subst new_ps new_obls0. simpl.
      destruct δ1; simpl in *.      
      intros ζ'. rewrite dom_insert elem_of_union elem_of_singleton.
      intros [-> | ?]; auto.
    - destruct T as (?&T). inversion T; subst.
      red. subst new_ps new_obls0. simpl.
      destruct δ1; simpl in *.
      intros ζ'. rewrite dom_insert elem_of_union elem_of_singleton.
      intros [-> | ?]; auto.
    - destruct T as (?&?&?&?&T). inversion T; subst. by destruct δ1.
    - destruct T as (?&?&?&T). inversion T; subst. by destruct δ1.
  Qed.

  Lemma progress_step_th_obls_pres c τ δ1 δ2
    (STEP: progress_step OP δ1 τ δ2)
    (TH_OWN: threads_own_obls c δ1)
    (DOMτ: is_Some (from_locale c.1 τ)):
    threads_own_obls c δ2.
  Proof.
    red in STEP. destruct STEP as (n&?&STEP).
    eapply rel_compose_mono in STEP.
    2: reflexivity.
    1: apply rel_compose_nsteps_next in STEP. 
    2: { do 2 red. intros. by left. }
    clear -DOMτ STEP TH_OWN. generalize dependent δ2. induction n.
    { simpl. intros ? ?%nsteps_once_inv. by eapply ghost_step_th_obls_pres. }
    intros ? (δ'&STEP1&STEP2)%rel_compose_nsteps_next.
    apply IHn in STEP1. eapply ghost_step_th_obls_pres; eauto.
  Qed.
    
  Lemma locale_step_th_obls_pres c1 c2 τ δ
    (STEP: locale_step c1 (Some τ) c2)
    (TH_OWN: threads_own_obls c1 δ):
    threads_own_obls c2 δ.
  Proof.
    destruct c1, c2. 
    red. intros. eapply from_locale_step; eauto.
  Qed. 
      
  Definition obls_valid_evolution_step
    (* (σ1: cfg Λ) *) (oζ: olocale Λ) (σ2: cfg Λ)
    (δ1: mstate OM) (ℓ: mlabel OM) (δ2: mstate OM) :=
      oζ = Some ℓ /\
      mtrans δ1 ℓ δ2 /\
      threads_own_obls σ2 δ2. 

  Definition obls_si `{ObligationsGS Σ}
    (σ: cfg Λ) (δ: mstate OM): iProp Σ :=
    obls_msi δ ∗ ⌜ threads_own_obls σ δ ⌝.

  Definition obls_init_resource `{ObligationsGS Σ}
    (δ: mstate OM) (_: unit): iProp Σ :=
    own obls_cps (◯ (ps_cps _ δ)) ∗
    own obls_sigs (◯ (sig_map_repr $ ps_sigs _ δ)) ∗
    own obls_obls (◯ (obls_map_repr $ ps_obls _ δ)) ∗
    own obls_eps (◯ (ps_eps _ δ)) ∗
    own obls_phs (◯ (ps_phases _ δ)) ∗
    own obls_lb (◯MN (ps_low_bound _ δ))
  .
    
  Definition obls_is_init_st (σ: cfg Λ) (δ: mstate OM) :=
    exists τ0 e0, σ.1 = [e0] /\ from_locale σ.1 τ0 = Some e0 /\
            dom (ps_obls OP δ) = {[ τ0 ]}. 

  Program Definition ObligationsEM: ExecutionModel Λ OM :=
    {| 
      em_preGS := ObligationsPreGS;
      em_GS := ObligationsGS;
      em_Σ := obls_Σ;
      em_valid_evolution_step := obls_valid_evolution_step;
      em_thread_post Σ `{ObligationsGS Σ} := 
        fun τ => own obls_obls (◯ {[τ := Excl ∅ ]});
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
    iMod (own_alloc (● (ps_cps _  δ) ⋅ ◯ _)) as (?) "[CPa CPf]".
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
    iMod (own_alloc (● (ps_eps _ δ) ⋅ ◯ _)) as (?) "[EPSa EPSf]". 
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (ps_phases _ δ) ⋅ ◯ _)) as (?) "[PHa PHf]". 
    { apply auth_both_valid_2; [| reflexivity].
      intros τ. destruct lookup; done. }
    iMod (own_alloc (●MN (ps_low_bound _ δ) ⋅ mono_nat_lb _)) as (?) "[LBa LBf]".
    { apply mono_nat_both_valid. reflexivity. }
    iModIntro. iExists {| obls_pre := PRE; |}.
    iFrame.
    iPureIntro. red. intros τ DOMτ.
    red in INIT. destruct σ, INIT as (τ0 & e0 & -> & LOC & DOM).
    rewrite DOM in DOMτ. apply elem_of_singleton in DOMτ.
    subst. simpl. done.
  Qed.  
  
  Definition cp `{ObligationsGS Σ} (ph: Phase) (deg: Degree): iProp Σ :=
    own obls_cps (◯ {[+ (ph, deg) +]}). 

  Definition sgn `{ObligationsGS Σ} (sid: SignalId) (l: Level) (ob: option bool): iProp Σ :=
    own obls_sigs (◯ ({[ sid := (to_agree l, mbind (Some ∘ Excl) ob ) ]})).

  Definition obls `{ObligationsGS Σ} ζ (R: gset SignalId) :=
    own obls_obls (◯ ({[ ζ := Excl R]}: gmapUR Locale (exclR (gsetR natO)))). 
  
  Section ResourcesFacts.
    Context `{ObligationsGS Σ}. 
    
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

  End ResourcesFacts.

  Section ResourcesUpdates.
    Context `{ObligationsGS Σ}.

    Definition OU ζ P: iProp Σ :=
      ∀ δ, obls_msi δ ==∗ ∃ δ', obls_msi δ' ∗ ⌜ ghost_step OP δ ζ δ'⌝ ∗ P. 
    
    Lemma OU_create_sig ζ R l:
      ⊢ obls ζ R -∗ OU ζ (∃ sid, sgn sid l (Some false) ∗ obls ζ (R ∪ {[ sid ]})).
    Proof.
      rewrite /OU. iIntros "OB %δ MSI".
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
           { econstructor; eauto. }
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

    Lemma burn_cp_upd δ ζ π deg
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

  End ResourcesUpdates.

End ObligationsRepr.
