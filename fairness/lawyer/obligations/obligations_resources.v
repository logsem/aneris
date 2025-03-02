From stdpp Require Import namespaces. 
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import own ghost_map fancy_updates.
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat gmap_view.
From trillium.fairness Require Import locales_helpers utils.
From trillium.fairness.lawyer.obligations Require Import obligations_model obls_utils obligations_wf.

Section ObligationsRepr.
  Context {DegO LevelO: ofe}.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}
    `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}
  .

  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context {Locale: Type}.
  Context {LIM_STEPS: nat}.
  Context {OP: ObligationsParams Degree Level Locale LIM_STEPS}.
  Let OM := ObligationsModel.

  Let phO := listO natO. 
  Let cpO := prodO phO DegO. 
  Let sstR := prodR (agreeR LevelO) (excl' boolO).
 
  Let epO := prodO (prodO natO phO) DegO.

  (* used to avoid applying leibnizO directly to list nat.
     See comment in ofe.v *)
  Record phase_wrapped := PhWr { ph_wr_car: Phase }.
  Definition wrap_phase := PhWr.
  Definition unwrap_phase (p: phase_wrapped) := match p with | PhWr π => π end.
  Lemma phase_wrap_unwrap π: unwrap_phase (wrap_phase π) = π.
  Proof using. done. Qed. 
  Lemma phase_unwrap_wrap p: wrap_phase (unwrap_phase p) = p.
  Proof using. by destruct p. Qed.

  Class ObligationsPreGS Σ := {
      obls_pre_cps :> inG Σ (authUR (gmultisetUR cpO));
      obls_pre_sigs :> inG Σ (authUR (gmapUR SignalId sstR));
      (* obls_pre_obls :> inG Σ (authUR (gmapUR Locale (exclR (gsetUR natO)))); *)
      obls_pre_obls :> inG Σ (authUR (gmapUR Locale (authUR (gset_disjUR natO))));
      obls_pre_eps :> inG Σ (authUR (gsetUR epO));
      (* obls_pre_phs :> inG Σ (authUR (gmapUR Locale (exclR phO))); *)
      obls_pre_phs :> ghost_mapG Σ Locale phase_wrapped;
      obls_pre_lb :> inG Σ mono_natUR;
  }.
  
  Class ObligationsGS Σ := {
      obls_pre :> ObligationsPreGS Σ;
      obls_cps: gname;
      obls_sigs: gname;
      obls_obls: gname;
      obls_eps: gname;
      obls_phs: gname;
      obls_exc_lb: gname;
  }.

  Definition sig_map_repr smap: gmapUR SignalId sstR :=
    (fun '(l, b) => (to_agree l, Excl' b)) <$> smap. 

  (* Definition obls_map_repr (omap: gmap Locale (gset SignalId)): *)
  (*   gmapUR Locale (exclR (gsetUR natO)) := *)
  (*   Excl <$> omap. *)
  Definition obls_map_repr (omap: gmap Locale (gset SignalId)):
    gmapUR Locale (authUR (gset_disjUR natO)) :=
    (fun R => ● (GSet R) ⋅ ◯ (GSet R)) <$> omap.
 
  (* Definition phases_repr_auth (pmap: gmap Locale Phase): *)
  (*   (* gmapUR Locale (exclR phO) := *) *)
  (*   (* fmap Excl pmap (FMap := gmap_fmap). *) *)
  (*   gmap_viewR Locale (leibnizO phase_wrapped) := *)
  (*   gmap_view_auth (DfracOwn 1) (wrap_phase <$> pmap) (V:=leibnizO phase_wrapped). *)
  
  Definition eps_repr (eps: gset ExpectPermission): gsetUR epO :=
    eps.

  Definition cps_repr (cps: gmultiset (@CallPermission Degree)): (gmultisetUR cpO) := cps.

  Definition obls_msi {Σ: gFunctors} {oGS: ObligationsGS Σ} (ps: ProgressState): iProp Σ :=
    own obls_cps (● (cps_repr $ ps_cps ps)) ∗
    own obls_sigs (● (sig_map_repr $ ps_sigs ps)) ∗
    own obls_obls (● (obls_map_repr $ ps_obls ps)) ∗
    own obls_eps (● (eps_repr $ ps_eps ps)) ∗
    ghost_map_auth obls_phs 1%Qp (wrap_phase <$> ps_phases ps) ∗
    own obls_exc_lb (●MN (ps_exc_bound ps))
  .
  
  Definition obls_Σ: gFunctors := #[
      GFunctor (authUR (gmultisetUR cpO));
      GFunctor (authUR (gmapUR SignalId sstR));
      (* GFunctor (authUR (gmapUR Locale (exclR (gsetR natO)))); *)
      GFunctor (authUR (gmapUR Locale (authUR (gset_disjUR natO))));
      GFunctor (authUR (gsetUR epO));
      (* GFunctor (authUR (gmapUR Locale (exclR phO))); *)
      ghost_mapΣ Locale phase_wrapped;
      GFunctor (mono_natUR)
   ].

  Global Instance obls_Σ_pre:
    ∀ Σ, subG obls_Σ Σ → ObligationsPreGS Σ.
  Proof using. solve_inG. Qed.

  Section Resources.
    Context `{oGS: ObligationsGS Σ}. 

    (* Without phase weakening, the phase of initial cps would mismatch thread's phase after it performs a fork.
       It'd lead to having "phase_le .." hypotheses to allow burning initial cps.
       These hypotheses would have to be propagated in all specs. *)
    Definition cp (ph_ub: Phase) (deg: Degree): iProp Σ :=
      ∃ ph, own obls_cps (◯ (cps_repr ({[+ ((ph, deg)) +]}))) ∗ ⌜ phase_le ph ph_ub ⌝.

    (* sealing this definition to avoid annoying unfolds (see Mattermost message) *)
    (* TODO: find a better solution? *)
    Local Definition cp_mul_def (ph_ub: Phase) deg n: iProp Σ :=
      [∗] replicate n (cp ph_ub deg).
    Local Definition cp_mul_aux : seal cp_mul_def. by eexists. Qed.
    Definition cp_mul := unseal cp_mul_aux. 
    Local Definition cp_mul_unseal : cp_mul = cp_mul_def := seal_eq cp_mul_aux.

    Definition sgn (sid: SignalId) (l: Level) (ob: option bool): iProp Σ :=
      own obls_sigs (◯ ({[ sid := (to_agree l, mbind (Some ∘ Excl) ob ) ]})).
    
    (* Definition obls τ (R: gset SignalId) := *)
    (*   own obls_obls (◯ ({[ τ := Excl R]}: gmapUR Locale (exclR (gsetR natO)))). *)

    (* Definition lvls_sets_lt (X Y: Level -> Prop) := *)
    (*   forall lx ly, X lx -> Y ly -> lvl_lt lx ly. *)
    Definition lvls_lt_lvl (L: Level -> Prop) (l: Level) :=
      forall l', L l' -> lvl_lt l' l.
    
    Definition obls_rel (L: Level -> Prop)
      τ (R: gset SignalId): iProp Σ :=
      (* own obls_obls (◯ ({[ τ := Excl R]}: gmapUR Locale (exclR (gsetR natO)))). *)
      ∃ R0, 
        own obls_obls (◯ ({[ τ := ● (GSet R0)]})) ∗ 
        own obls_obls (◯ ({[ τ := ◯ (GSet R)]})) ∗
        ([∗ set] s ∈ (R0 ∖ R), ∃ l__s, sgn s l__s None ∗ ⌜ lvls_lt_lvl L l__s ⌝). 
    
    Definition sgns_levels_rel (rel: Level -> Level -> Prop)
      (R: gset SignalId) (L: gset Level): iProp Σ := 
      [∗ set] s ∈ R, (∃ l, sgn s l None ∗ ⌜ set_Forall (rel l) L ⌝). 

    Definition sgns_levels_gt' := sgns_levels_rel (flip lvl_lt).
    Definition sgns_levels_ge' := sgns_levels_rel (flip lvl_le).

    Definition sgns_level_gt (R: gset SignalId) lm: iProp Σ :=
      sgns_levels_gt' R {[ lm ]}.    
    Definition sgns_level_ge (R: gset SignalId) lm: iProp Σ :=
      sgns_levels_ge' R {[ lm ]}.

    Definition ep (sid: SignalId) (π__ub: Phase) d: iProp Σ :=
      ∃ π, own obls_eps (◯ {[ (sid, π, d) ]}) ∗ ⌜ phase_le π π__ub ⌝.
    
    Definition exc_lb (n: nat) :=
      own obls_exc_lb (mono_nat_lb n).

    Definition th_phase_frag ζ π (q: Qp): iProp Σ :=
      ghost_map_elem obls_phs ζ (DfracOwn q) (wrap_phase π).

    Definition th_phase_eq ζ π: iProp Σ :=
      th_phase_frag ζ π 1%Qp.

    (* Lemma obls_proper ζ R1 R2 (EQUIV: R1 ≡ R2): *)
    (*   ⊢ obls ζ R1 ∗-∗ obls ζ R2. *)
    (* Proof using. clear H H0 H1. set_solver. Qed. *)
    
    Lemma empty_sgns_levels_rel rel L:
      ⊢ sgns_levels_rel rel ∅ L.
    Proof using.
      clear.
      rewrite /sgns_levels_rel. set_solver.
    Qed.

    Global Instance sgns_levels_rel'_Proper rel:
      Proper (equiv ==> equiv ==> equiv) (sgns_levels_rel rel).
    Proof using. solve_proper. Qed.

    Lemma cp_msi_unfold δ ph deg:
      ⊢ obls_msi δ -∗ cp ph deg -∗
        obls_msi δ ∗ ∃ π0, own obls_cps (◯ ({[+ ((π0, deg)) +]})) ∗ ⌜ (π0, deg) ∈ ps_cps δ /\ phase_le π0 ph⌝.
    Proof using.
      clear H H0 H1.
      rewrite /obls_msi. iIntros "(CPS&?) CP".
      iDestruct "CP" as "(%π & CP & %PH_LE)". 
      iCombine "CPS CP" as "CPS". 
      iDestruct (own_valid with "[$]") as %V.
      iDestruct "CPS" as "[??]". iFrame. 
      iExists _. iFrame. iPureIntro. split; [| done]. 
      apply auth_both_valid_discrete, proj1 in V. 
      rewrite /cps_repr in V. simpl in V.
      apply gmultiset_singleton_subseteq_l. 
      by apply gmultiset_included.
    Qed.

    (* TODO: unify sigs_msi_.. proofs *)
    Lemma sigs_msi_in δ sid l ov:
      ⊢ obls_msi δ -∗ sgn sid l ov -∗
        ⌜ exists v, ps_sigs δ !! sid = Some (l, v) ⌝.
    Proof using H1 H0. 
      clear H. 
      rewrite /obls_msi. iIntros "(_&SIGS&_) SIG". 
      iCombine "SIGS SIG" as "SIGS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      apply @singleton_included_l in SUB. destruct SUB as ([l' y]&SIG'&LE').

      simpl in LE'. rewrite -SIG' in LE'.
      rewrite /sig_map_repr in LE'.
      rewrite lookup_fmap in LE'.
      destruct (ps_sigs δ !! sid) as [[??]|] eqn:LL.
      all: rewrite LL in LE'; simpl in LE'.
      2: { apply option_included_total in LE' as [?|?]; set_solver. }
      rewrite Some_included_total in LE'.
      apply pair_included in LE' as [LE1 LE2].
      apply to_agree_included in LE1.
      set_solver. 
   Qed.

    Lemma sigs_msi_exact δ sid l v:
      ⊢ obls_msi δ -∗ sgn sid l (Some v) -∗
        ⌜ ps_sigs δ !! sid = Some (l, v) ⌝.
    Proof using H1 H0.
      clear H. 
      rewrite /obls_msi. iIntros "(_&SIGS&_) SIG". 
      iCombine "SIGS SIG" as "SIGS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      apply @singleton_included_l in SUB. destruct SUB as ([l' y]&SIG'&LE').

      simpl in LE'. rewrite -SIG' in LE'.
      rewrite /sig_map_repr in LE'.
      rewrite lookup_fmap in LE'.
      destruct (ps_sigs δ !! sid) as [[??]|] eqn:LL.
      all: rewrite LL in LE'; simpl in LE'.
      2: { apply option_included_total in LE' as [?|?]; set_solver. }
      rewrite Some_included_total in LE'.
      apply pair_included in LE' as [LE1 LE2].      
      apply to_agree_included in LE1.
      apply Excl_included in LE2.
      set_solver. 
    Qed.

    Instance sgn_ex_pers sid l: Persistent (sgn sid l None).
    Proof using. apply _. Qed.

    Lemma sgn_get_ex sid l ov:
      ⊢ sgn sid l ov -∗ sgn sid l ov ∗ sgn sid l None. 
    Proof using.
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

    Lemma obls_rel_msi_exact_res δ L ζ R:
      ⊢ obls_msi δ -∗ obls_rel L ζ R -∗
        ∃ R0, obls_msi δ ∗ own obls_obls (◯ ({[ ζ := ● (GSet R0) ⋅ ◯ (GSet R)]})) ∗
              ([∗ set] s ∈ (R0 ∖ R), ∃ l__s, sgn s l__s None ∗ ⌜ lvls_lt_lvl L l__s ⌝) ∗
                ⌜ ps_obls δ !! ζ = Some R0 /\ R ⊆ R0 /\ 
                 forall s', s' ∈ R0 ∖ R -> exists l' v', 
                     ps_sigs δ !! s' = Some (l', v') /\ lvls_lt_lvl L l'⌝.
    Proof using H1 H0.
      clear H. 
      rewrite {1}/obls_msi. iIntros "(CPS & SIGS & OBLS & MSI') OB".
      rewrite /obls_rel. iDestruct "OB" as "(%R0 & OB0 & OB & #REST)".
      iCombine "OBLS OB0 OB" as "OBLS". 
      iDestruct (own_valid with "[$]") as %V. 
      apply auth_both_valid_discrete in V as [SUB V].
      eapply singleton_included_l in SUB as (AR & OB & SUB).

      rewrite /obls_map_repr in OB.
      rewrite lookup_fmap in OB. 
      apply fmap_Some_equiv_1 in OB. destruct OB as (R0_ & OB & EQUIV).
      rewrite EQUIV in SUB.
      iExists _. rewrite (bi.sep_assoc (obls_msi _)). iSplit.
      { iFrame. iDestruct "OBLS" as "[??]". iFrame. }

      rewrite Some_included_total in SUB.
      apply auth_both_included in SUB as [[=->] SUB%gset_disj_included].
      iFrame "REST".
      do 2 (iSplit; [done| ]).
      
      iIntros (s' REST).
      iDestruct (big_sepS_elem_of_acc with "[$]") as "[SGN _]"; [eauto| ].
      iDestruct "SGN" as "(%l__s & #SGN & %LT)".
      iDestruct "OBLS" as "[OBLS OB]".
      iCombine "CPS OBLS SIGS MSI'" as "MSI".
      iDestruct (sigs_msi_in with "[MSI] [$]") as %[v' IN].
      { iDestruct "MSI" as "(?&?&?&?&?&?)". iFrame. }
      iPureIntro. do 2 eexists. eauto.
    Qed.
     
    (* Lemma obls_rel_msi_exact δ L `{forall l, Decision (L l)} ζ R: *)
    (*   ⊢ obls_msi δ -∗ obls_rel L ζ R -∗ *)
    (*     ∃ R0, ⌜ ps_obls δ !! ζ = Some R0 /\ R ⊆ R0 /\  *)
    (*              forall s', s' ∈ R0 ∖ R -> exists l' v',  *)
    (*                  ps_sigs δ !! s' = Some (l', v') /\ lvls_lt_lvl L l'⌝. *)
    (* Proof using H1 H0. *)
    (*   clear H. *)
    (*   iIntros "? ?".  *)
      
    (*   rewrite /obls_msi. iIntros "(CPS & SIGS & OBLS & MSI') OB". *)
    (*   rewrite /obls_rel. iDestruct "OB" as "(%R0 & OB0 & OB & #REST)". *)
    (*   iCombine "OBLS OB0 OB" as "OBLS".  *)
    (*   iDestruct (own_valid with "[$]") as %V.  *)
    (*   apply auth_both_valid_discrete in V as [SUB V]. *)
    (*   eapply singleton_included_l in SUB as (AR & OB & SUB). *)

    (*   rewrite /obls_map_repr in OB. *)
    (*   rewrite lookup_fmap in OB.  *)
    (*   apply fmap_Some_equiv_1 in OB. destruct OB as (R0_ & OB & EQUIV). *)
    (*   rewrite EQUIV in SUB. *)
    (*   iExists _. iSplit; [eauto| ].  *)

    (*   rewrite Some_included_total in SUB. *)
    (*   apply auth_both_included in SUB as [[=->] SUB%gset_disj_included]. *)
    (*   iSplit; [done| ]. *)
      
    (*   iIntros (s' REST). *)
    (*   iDestruct (big_sepS_elem_of_acc with "[$]") as "[SGN _]"; [eauto| ]. *)
    (*   iDestruct "SGN" as "(%l__s & #SGN & %LT)". *)
    (*   iDestruct "OBLS" as "[OBLS OB]". *)
    (*   iCombine "CPS OBLS SIGS MSI'" as "MSI". *)
    (*   iDestruct (sigs_msi_in with "[MSI] [$]") as %[v' IN]. *)
    (*   { iDestruct "MSI" as "(?&?&?&?&?&?)". iFrame. } *)
    (*   iPureIntro. do 2 eexists. eauto. *)
    (* Qed. *)

    Instance wrap_phase_inj: Inj eq eq wrap_phase.
    Proof using.
      intros ?? EQ. apply (@f_equal _ _ unwrap_phase) in EQ.
      by rewrite !phase_wrap_unwrap in EQ.
    Qed.

    Lemma th_phase_msi_frag δ ζ π q:
      ⊢ obls_msi δ -∗ th_phase_frag ζ π q -∗ ⌜ ps_phases δ !! ζ = Some π ⌝. 
    Proof using.
      clear H1 H0 H. 
      rewrite /obls_msi. iIntros "(?&?&?&?&PHASES&?) PH".
      iRevert "PHASES PH". iFrame. iIntros "PHASES PH".
      rewrite /th_phase_frag.
      iDestruct (ghost_map_lookup with "[$] [$]") as %V.
      apply lookup_fmap_Some in V as (?&?&?). set_solver.
    Qed.

    Lemma exc_lb_msi_bound δ n:
      ⊢ obls_msi δ -∗ exc_lb n -∗ ⌜ n <= ps_exc_bound δ ⌝.
    Proof using.
      rewrite /obls_msi. iIntros "(_&_&_&_&_&B) LB".
      iCombine "B LB" as "LB".
      iDestruct (own_valid with "LB") as %V. iPureIntro.
      by apply mono_nat_both_valid in V.
    Qed.

    Lemma exc_lb_max n m:
      exc_lb n ∗ exc_lb m ⊣⊢ exc_lb (max n m). 
    Proof using.
      rewrite /exc_lb. rewrite -own_op. by rewrite mono_nat_lb_op.
    Qed.

    Lemma exc_lb_le n m (LE: n <= m):
      exc_lb m ⊢ exc_lb n.
    Proof using.
      rewrite /exc_lb. erewrite mono_nat_lb_op_le_l; eauto.
      rewrite own_op. by iIntros "[??]". 
    Qed.

    Lemma obls_sgn_lt_locale_obls δ (L: Level -> Prop) ζ R lm
      (WAIT_L: L lm):
      ⊢ obls_msi δ -∗ obls_rel L  ζ R -∗ sgns_level_gt R lm -∗
        ⌜ lt_locale_obls lm ζ δ ⌝.
    Proof using H1 H0.
      clear H. 
      iIntros "MSI OBLS SIGS_LT".
      iDestruct (obls_rel_msi_exact_res with "[$] [$]") as "(%R0 & MSI & OB & #REST & %Rζ & %SUB & %REST)".
      rewrite /lt_locale_obls. rewrite Rζ. simpl.
      rewrite -pure_forall_2. setoid_rewrite <- bi.pure_impl_2. 
      iIntros (l IN).

      (* TODO: lemma? *)
      apply extract_Somes_gset_spec in IN. simpl in IN.
      apply elem_of_map in IN. destruct IN as [sid [EQ IN]].
      destruct (ps_sigs δ !! sid) as [[l' b]| ] eqn:SID; [| done].
      simpl in EQ. inversion EQ. subst l'. 

      iDestruct (big_sepS_forall with "SIGS_LT") as "LT".
      destruct (decide (sid ∈ R)). 
      - iSpecialize ("LT" $! _ ltac:(eauto)). iDestruct "LT" as "(%l_ & SIG & %LT)".
        iDestruct (sigs_msi_in with "[$] [$]") as %[? SIG].
        set_solver.
      - specialize (REST sid ltac:(set_solver)) as (l' & v' & SIG' & LT').
        rewrite SID in SIG'. inversion SIG'. subst l' v'.
        iPureIntro. by apply LT'. 
    Qed.

    Lemma ep_msi_in δ sid π__ub d:
      ⊢ obls_msi δ -∗ ep sid π__ub d -∗
        ∃ π, ⌜ ((sid, π, d): (@ExpectPermission _)) ∈ (ps_eps δ) /\ phase_le π π__ub⌝. 
    Proof using. 
      rewrite /obls_msi. iIntros "(_&_&_&EPS&_) EP".
      iDestruct "EP" as "(%π & EP & %PH_LE)". 
      iCombine "EPS EP" as "EPS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      eexists. split; [| done].
      by apply gset_included, singleton_subseteq_l in SUB.
    Qed.

    Lemma th_phase_frag_combine τ π q p:
      th_phase_frag τ π q ∗ th_phase_frag τ π p ⊣⊢ th_phase_frag τ π (Qp.add q p). 
    Proof using.
      rewrite /th_phase_frag. by rewrite ghost_map.ghost_map_elem_fractional.
    Qed.

    Lemma th_phase_frag_combine' τ π q p
      (LE: Qp.le p q):
      th_phase_frag τ π q ⊣⊢ th_phase_frag τ π p ∗ from_option (fun d => th_phase_frag τ π d) ⌜ True ⌝ (Qp.sub q p). 
    Proof using.
      destruct (q - p)%Qp eqn:D. 
      - simpl. rewrite th_phase_frag_combine.
        by apply Qp.sub_Some in D as ->.
      - simpl. apply Qp.sub_None in D.
        assert (p = q) as ->.
        { eapply @partial_order_anti_symm; eauto. apply _. }
        by rewrite bi.sep_True'.
    Qed.

    Lemma th_phase_frag_halve τ π q:
      th_phase_frag τ π q ⊣⊢ th_phase_frag τ π (q /2) ∗ th_phase_frag τ π (q /2).
    Proof using.
      rewrite /th_phase_frag.
      rewrite th_phase_frag_combine. by rewrite Qp.div_2.
    Qed.

    Lemma cp_weaken π1 π2 deg
      (PH_LE: phase_le π1 π2):
      cp π1 deg -∗ cp π2 deg.
    Proof using.
      rewrite /cp. iIntros "(%&?&%)".
      iExists _. iFrame. iPureIntro. etrans; eauto.
    Qed.
      
    Lemma cp_mul_alt π d n:
      cp_mul π d n ⊣⊢ ([∗ mset] '(π, d) ∈ (n *: {[+ (π, d) +]}), cp π d).
    Proof using.
      clear H1 H0 H.
      rewrite cp_mul_unseal. rewrite /cp_mul_def.
      iInduction n as [| n] "IH".
      { set_solver. }
      simpl. rewrite gmultiset_scalar_mul_S_l big_sepMS_disj_union.
      rewrite big_sepMS_singleton.
      iSplit; iIntros "[??]"; iFrame; by iApply "IH".
    Qed.

    Lemma cp_mul_take ph deg n:
      cp_mul ph deg (S n) ⊣⊢ cp_mul ph deg n ∗ cp ph deg.
    Proof using.
      rewrite cp_mul_unseal. 
      rewrite /cp_mul. simpl. by rewrite bi.sep_comm. 
    Qed.

    Lemma cp_mul_split ph deg m n:
      cp_mul ph deg (m + n) ⊣⊢ cp_mul ph deg m ∗ cp_mul ph deg n.
    Proof using.
      rewrite cp_mul_unseal.
      rewrite /cp_mul_def. rewrite replicate_add.
      by rewrite big_sepL_app. 
    Qed.
 
    Lemma cp_mul_split' (ph : listO natO) (deg : DegO) (m n : nat)
      (LE: m <= n):
      cp_mul ph deg n ⊣⊢ cp_mul ph deg m ∗ cp_mul ph deg (n - m).
    Proof using.
      apply Nat.le_sum in LE as [? ->]. rewrite Nat.sub_add'.
      apply cp_mul_split.
    Qed.

    Lemma cp_mul_weaken π1 π2 deg n1 n2
      (PH_LE: phase_le π1 π2)
      (LE: n2 <= n1):
      cp_mul π1 deg n1 -∗ cp_mul π2 deg n2.
    Proof using.
      clear H1 H0 H.
      iIntros "CPS".
      apply Nat.le_sum in LE as [? ->].
      iDestruct (cp_mul_split with "CPS") as "[CPS _]".
      rewrite cp_mul_unseal.
      iInduction n2 as [| n] "IH".
      { set_solver. }
      simpl. iDestruct "CPS" as "[CP CPS]". iSplitL "CP".
      { by iApply cp_weaken. }
      by iApply "IH".
    Qed.

    Lemma cps_mset (M: gmultiset CallPermission):
      own obls_cps (◯ M) -∗ ([∗ mset] '(π, d) ∈ M, cp π d).
    Proof using.
      clear H1 H0 H. 
      iIntros "CPS".
      iInduction M as [| cp M] "IH" using gmultiset_ind.
      { set_solver. }
      rewrite big_sepMS_disj_union.
      rewrite -gmultiset_op. iDestruct "CPS" as "[CP CPS]". iSplitL "CP".
      - rewrite big_opMS_singleton. destruct cp.
        iExists _. by iFrame.
      - by iApply "IH".
    Qed.

    Lemma cp_mul_0 π d:
      ⊢ |==> cp_mul π d 0.
    Proof using.
      clear H H0 H1.
      rewrite cp_mul_unseal. 
      rewrite /cp_mul_def. simpl. set_solver. 
    Qed.

    Lemma cp_mul_1 π d:
      cp π d ⊣⊢ cp_mul π d 1.
    Proof using.
      rewrite cp_mul_unseal. 
      rewrite /cp_mul_def. simpl.
      by rewrite bi.sep_emp.
    Qed.

    Let OU' (R: ProgressState -> ProgressState -> Prop) P: iProp Σ :=
      ∀ δ, obls_msi δ ==∗ ∃ δ', obls_msi δ' ∗ ⌜ R δ δ'⌝ ∗ P. 

    Definition OU := OU' (loc_step_ex).

    Lemma OU'_wand rel P Q:
      (P -∗ Q) -∗ OU' rel P -∗ OU' rel Q.
    Proof using.
      iIntros "PQ OU".
      rewrite /OU'. iIntros "**".
      iSpecialize ("OU" with "[$]"). iMod "OU" as "(%&?&?&?)". iModIntro.
      iExists _. iFrame. by iApply "PQ".
    Qed.
        
    Lemma OU_wand P Q:
      (P -∗ Q) -∗ OU P -∗ OU Q.
    Proof using. by apply OU'_wand. Qed.
        
    Global Instance OU_entails:
      Proper (bi_entails ==> bi_entails) OU.
    Proof using.
      intros ?? IMPL. iIntros "OU".
      iApply (OU_wand with "[] [$]").  
      iApply IMPL. 
    Qed.

    Global Instance OU_equiv:
      Proper (equiv ==> equiv) OU.
    Proof using.
      intros ?? [PQ QP]%bi.equiv_entails.
      iSplit; iApply OU_entails; [iApply PQ | iApply QP].  
    Qed.

    Fixpoint OU_rep n P: iProp Σ :=
      match n with
      | 0 => OU' eq P (* access obls_msi even on trivial case *)
      | S n => OU (OU_rep n P)
      end.

    Lemma OU_bupd P:
      (OU (|==> P)) -∗ OU P.
    Proof using.
      rewrite /OU. iIntros "OU" (?) "?".
      iMod ("OU" with "[$]") as (?) "(?&?& P)". iMod "P".
      iModIntro. iExists _. iFrame.
    Qed.

    Lemma OU_rep_frame_l n P Q:
      (P ∗ OU_rep n Q) -∗ OU_rep n (P ∗ Q).
    Proof using.
      iIntros "[P OUs]". iInduction n as [| n] "IH".
      { simpl. iFrame. iIntros "% ?".
        iMod ("OUs" with "[$]") as "(%&?&?&?)". iExists _. by iFrame. }
      simpl. iApply (OU_wand with "[-OUs] [$]").
      by iApply "IH".
    Qed.

    Lemma OU_rep_wand n P Q:
      (P -∗ Q) -∗ OU_rep n P -∗ OU_rep n Q.
    Proof using.
      iIntros "PQ OUs". iInduction n as [| n] "IH"; simpl.
      { by iApply (OU'_wand with "[$]"). }
      iApply (OU_wand with "[-OUs] [$]").
      iIntros "OUs". by iApply ("IH" with "[$]").
    Qed.

    Lemma OU'_proper' (P Q: iProp Σ) rel:
      (P ∗-∗ Q) -∗ OU' rel P ∗-∗ OU' rel Q.
    Proof using.
      iIntros "EQUIV". rewrite /OU.
      iSplit; iIntros "OU % MSI"; iMod ("OU" with "[$]") as "(%&?&?&?)"; iModIntro; iExists _; iFrame; by iApply "EQUIV".
    Qed.

    Global Instance OU_rep_proper n:
      Proper (equiv ==> equiv) (OU_rep n).
    Proof using.
      clear H1 H0 H.
      intros ???. iInduction n as [| n] "%IH".
      { simpl. iSplit; iApply OU'_wand; set_solver. } 
      simpl. by iApply OU'_proper'.
    Qed.

    Lemma OU_create_sig_cur ζ R l (L: Level -> Prop)
      (Ll: L l):
      ⊢ obls_rel L ζ R -∗ OU (∃ sid, sgn sid l (Some false) ∗ obls_rel L ζ (R ∪ {[ sid ]}) ∗
                                 ⌜ sid ∉ R ⌝).
    Proof using H1 H0.
      clear H. 
      rewrite /OU /OU'. iIntros "OB %δ MSI".
      iDestruct (obls_rel_msi_exact_res with "[$] [$]") as "(%R0 & MSI & OB & #REST & %Rζ & %SUB & %REST)".
      set (sid := next_sig_id (R0 ∪ (dom $ ps_sigs δ))).
      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&SIGS&OBLS&?&?&?)".
      destruct δ. simpl. iFrame. simpl in *.
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "SIGS OBLS". iFrame. iIntros "SIGS OBLS". simpl.
      rewrite !bi.sep_assoc. 

      rewrite bi.sep_comm bi.sep_assoc.  
      iSplitL.
      2: { iPureIntro. left. exists ζ. 
           red. do 1 right. left. exists l. 
           erewrite (f_equal (creates_signal _ _)).
           { econstructor; eauto. simpl. eapply elem_of_dom; eauto. }
           simpl. reflexivity. }

      assert (sid ∉ R0) as FRESH.
      { eapply not_elem_of_weaken. 
        { by intros IN%next_sig_id_fresh. }
        set_solver. }

      rewrite /obls_rel. 
      iMod (own_update with "[OB OBLS]") as "X".
      2: iCombine "OBLS OB" as "?"; iFrame.
      { apply auth_update.
        apply singleton_local_update_any.
        intros ? RR. apply lookup_fmap_Some in RR as (R_&?&Rζ_).
        rewrite Rζ in Rζ_. inversion Rζ_. subst R_. subst.
        apply auth_local_update.
        { apply gset_disj_alloc_op_local_update with (Z := {[ sid ]}).
          by apply disjoint_singleton_l. }
        { rewrite gset_disj_union; [reflexivity| ].
          by apply disjoint_singleton_l. }
        done. }
      rewrite Rζ. simpl. iDestruct "X" as "[OBLS OB]".
      iApply bi.sep_assoc. iSplitR "OBLS".
      2: { iModIntro. fold sid.
           iApply own_proper; [| by iFrame]. apply auth_auth_proper.
           rewrite union_comm_L. rewrite gset_disj_union.
           2: { by apply disjoint_singleton_l. }
           rewrite /obls_map_repr. simpl.
           by rewrite fmap_insert. }
           
      rewrite bi.sep_exist_r. iApply bupd_exist. iExists sid.
      rewrite -bi.sep_assoc. rewrite bi.sep_comm. rewrite -bi.sep_assoc.

      iSplitR "SIGS".
      2: { 
      rewrite -own_op. iApply own_update; [| by iFrame].
      apply auth_update_alloc. 
      eapply local_update_proper.
      1: reflexivity.
      2: eapply alloc_local_update.
      { rewrite /sig_map_repr. rewrite insert_empty fmap_insert. reflexivity. }
      2: done.
      apply not_elem_of_dom.
      subst sid. rewrite dom_fmap_L.
      eapply not_elem_of_weaken; [apply next_sig_id_fresh| ]. set_solver. }

      iSplitL; [| set_solver].
      iDestruct "OB" as "[??]". iExists _. iFrame.
      rewrite union_comm_L. rewrite gset_disj_union.
      2: { apply disjoint_singleton_l. set_solver. }
      iFrame. iModIntro.
      rewrite difference_union_distr_l_L.
      rewrite (subseteq_empty_difference_L _ (_ ∪ _)).
      2: { apply union_subseteq_l. }
      rewrite union_empty_l_L. rewrite difference_union_distr_r_L.
      rewrite (difference_disjoint_L _ {[ _ ]}).
      2: { by apply disjoint_singleton_r. }
      rewrite intersection_comm_L. rewrite subseteq_intersection_1_L; [| set_solver].
      done.
    Qed.
      
    (* TODO: do we need to generalize to "optional v" instead? *)
    Lemma OU_set_sig L ζ R sid l v
      (IN: sid ∈ R):
      ⊢ obls_rel L ζ R -∗ sgn sid l (Some v) -∗
        OU (sgn sid l (Some true) ∗ obls_rel L ζ (R ∖ {[ sid ]})).
    Proof using H1 H0.
      clear H.
      rewrite bi.sep_comm. 
      rewrite /OU /OU'. iIntros "OB SIG %δ MSI".
      iDestruct (sigs_msi_exact with "[$] [$]") as %Sζ.
      iDestruct (obls_rel_msi_exact_res with "[$] [$]") as "(%R0 & MSI & OB & #REST & %Rζ & %SUB & %REST)".

      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&SIGS&OBLS&?&?&?)".
      destruct δ. simpl in *.
      iCombine "OBLS OB" as "OBLS". iCombine "SIGS SIG" as "SIGS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "OBLS SIGS". iFrame. simpl. iIntros "OBLS SIGS".

      rewrite bi.sep_comm -!bi.sep_assoc.  
      iSplitR.
      { iPureIntro. left. exists ζ.
        red. do 2 right. left. exists sid. 
        erewrite (f_equal (sets_signal _ _)).
        { econstructor; eauto. simpl. eapply elem_of_dom; eauto. }
        simpl. reflexivity. }
      
      apply elem_of_subseteq_singleton, union_difference_L in IN.
      remember (R ∖ {[ sid ]}) as R'. subst R.
      apply subseteq_disjoint_union_L in SUB as (R'' & -> & DISJ).
      iMod (own_update with "OBLS") as "OBLS".
      { apply auth_update.
        apply singleton_local_update_any.
        intros ? RR. apply lookup_fmap_Some in RR as (R_&?&Rζ_).
        rewrite Rζ in Rζ_. inversion Rζ_. subst R_. subst.
        rewrite -!union_assoc_L. 
        rewrite -(gset_disj_union {[ sid ]}).
        2: set_solver. 
        rewrite -(gset_disj_union {[ sid ]}).
        2: set_solver. 
        apply auth_local_update.
        { eapply gset_disj_dealloc_op_local_update. }
        { reflexivity. }
        done. }

      rewrite bi.sep_comm -!bi.sep_assoc.
      rewrite bi.sep_assoc. iSplitR "OBLS".
      2: { iModIntro. 
           iDestruct "OBLS" as "[OBLS OB]". rewrite Rζ. simpl.
           iSplitL "OBLS".
           - iApply own_proper; [| by iFrame]. apply auth_auth_proper.
             rewrite /obls_map_repr. rewrite fmap_insert.
             f_equiv. f_equal.
             all: do 2 f_equal; set_solver.
           - rewrite /obls_rel. iDestruct "OB" as "[??]". iExists _. iFrame.
             iApply big_sepS_mono'; [.. | iApply "REST"].
             2: { set_solver. }
             done. }

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

    Lemma exchange_cp_upd π d d' b k
      (LE: k <= b)
      (DEG: deg_lt d' d):
      ⊢ cp π d -∗ exc_lb b -∗ OU (cp_mul π d' k).
    Proof using.
      clear H1 H0 H.
      rewrite /OU /OU'. iIntros "CP #LB %δ MSI".
      iDestruct (exc_lb_msi_bound with "[$] [$]") as %LB.
      (* iDestruct (th_phase_msi_frag with "[$] [$]") as "%". *)
      (* iDestruct "CP" as "(%π0 & CP & %PH_LE)".  *)
      iDestruct (cp_msi_unfold with "[$] [$]") as "(MSI & %π0 & CP & [%IN %PH_LE])".
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl in *.
      iCombine "CPS CP" as "CPS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "CPS". iFrame. simpl. iIntros "[CPS CP]".

      rewrite bi.sep_comm -!bi.sep_assoc.
      iSplitR.
      { iPureIntro. right. left. 
        exists π0, d, d', k. 
        erewrite (f_equal (exchanges_cp _)).
        { econstructor; eauto.
          simpl. lia. }
        simpl. reflexivity. }

      rewrite /cps_repr. rewrite bi.sep_comm.
      rewrite cp_mul_unseal. 
      rewrite /cp_mul_def /cp. iCombine "CPS CP" as "CPS".
      iMod (own_update with "[$]") as "foo".
      { apply auth_update.
      etrans.
      { eapply gmultiset_local_update_dealloc. reflexivity. }
      rewrite gmultiset_difference_diag.
      eapply local_update_proper.
      1: reflexivity.
      2: eapply gmultiset_local_update_alloc.
      by rewrite gmultiset_disj_union_left_id. }

      iModIntro. iDestruct "foo" as "[AUTH FRAG]". iFrame.

      iInduction k as [| k] "IH".
      { set_solver. }
      simpl. rewrite gmultiset_scalar_mul_S_r.
      rewrite -gmultiset_op. rewrite auth_frag_op.
      iDestruct "FRAG" as "[CPS CP]".
      iSplitL "CP".
      { iExists _. by iFrame. }
      iApply ("IH" with "[] [$]"). iPureIntro. lia. 
    Qed.

    (* TODO: ? use duplicable "signal exists" resource *)
    Lemma create_ep_upd ζ π q d d' sid l ov (DEG: deg_lt d' d)
      :
      ⊢ cp π d -∗ sgn sid l ov -∗ th_phase_frag ζ π q -∗ 
        OU (ep sid π d' ∗ sgn sid l ov ∗ th_phase_frag ζ π q).
    Proof using H1 H0.
      rewrite /OU /OU'. iIntros "CP SIG PH %δ MSI".
      iDestruct (sigs_msi_in with "[$] [$]") as %[v Sζ].
      iDestruct (th_phase_msi_frag with "[$] [$]") as "%".
      iDestruct (cp_msi_unfold with "[$] [$]") as "(MSI & %π0 & CP & [%IN %PH_LE])".
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&SIGS&?&EPS&?&?)".
      destruct δ. simpl in *.
      iCombine "CPS CP" as "CPS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "CPS EPS". iFrame. simpl. iIntros "CPS EPS".
 
      rewrite bi.sep_comm -!bi.sep_assoc.
      iSplitR.
      { iPureIntro. left. exists ζ. 
        red. do 3 right. left. exists sid, π0. do 2 eexists. 
        erewrite (f_equal (creates_ep _ _)).
        { econstructor; eauto.
          - simpl. by apply elem_of_dom. }
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
           iModIntro. iExists _. iSplit; [| done].
           iApply own_mono; [| by iFrame].
           apply auth_frag_mono. apply gset_included. apply union_subseteq_r. }
      
      iApply own_update; [| by iFrame].
      apply auth_update_dealloc.
      eapply local_update_proper.
      1: reflexivity.
      2: { apply gmultiset_local_update_dealloc. reflexivity. }
      rewrite gmultiset_difference_diag. set_solver.
    Qed.
      
    Lemma th_phase_msi_align δ ζ π q:
      ⊢ obls_msi δ -∗ th_phase_frag ζ π q -∗
        obls_msi δ ∗ th_phase_frag ζ (default π (ps_phases δ !! ζ)) q. 
    Proof using.
      iIntros "? ?". 
      iDestruct (th_phase_msi_frag with "[$] [$]") as "->".
      iFrame.
    Qed.

    Lemma expect_sig_upd (L: Level -> Prop) ζ sid π q d l R
      (Ll: L l)
      :
      ⊢ ep sid π d -∗ sgn sid l (Some false) -∗ obls_rel L ζ R -∗
        sgns_level_gt R l -∗ th_phase_frag ζ π q -∗
        OU (cp π d ∗ sgn sid l (Some false) ∗ obls_rel L ζ R ∗ th_phase_frag ζ π q).
    Proof using H1 H0.
      rewrite /OU /OU'. iIntros "#EP SIG OBLS #SIGS_LT PH %δ MSI".
      iDestruct (sigs_msi_exact with "[$] [$]") as %Sζ.
      (* iDestruct (th_phase_msi_ge with "[$] [$]") as %(? & PH__ζ & LE__πx). *)
      iDestruct (th_phase_msi_frag with "[$] [$]") as "%PH".
      iDestruct (th_phase_msi_align with "[$] [$]") as "[MSI PH]".
      rewrite PH. simpl.
      iDestruct (ep_msi_in with "[$] [$]") as %(π__e & IN & PH_LE).
      iDestruct (obls_sgn_lt_locale_obls with "[$] [$] [$]") as %LT; [done| ].

      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl in *.
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "CPS". iFrame. simpl. iIntros "CPS".

      rewrite /cp /cps_repr /eps_repr. 
      rewrite bi.sep_comm -bi.sep_assoc.
      iSplitR.
      { iPureIntro. left. exists ζ. 
        red. do 4 right. do 3 eexists. 
        erewrite (f_equal (expects_ep _ _)).
        { econstructor.
          { apply PH. }
          { apply PH_LE. }
          all: eauto. }
        done. }

      rewrite bi.sep_comm.
      (* iApply bi.sep_exist_l. iExists x. rewrite bi.sep_assoc. *)
      (* iSplitL "CPS".  *)
      (* 2: { iFrame. iPureIntro. split; try done. *)
      (*      etrans; eauto. }  *)
      iApply bi.sep_exist_l. iExists π.
      rewrite bi.sep_assoc. rewrite -own_op.
      iApply bupd_frame_r. iSplit; [| done].
      iApply own_update; [| by iFrame].
      apply auth_update_alloc.
      eapply local_update_proper.
      1: reflexivity.
      2: eapply gmultiset_local_update_alloc.
      f_equiv. rewrite gmultiset_disj_union_left_id. set_solver.
    Qed.

    Lemma expect_sig_upd_rep (L: Level -> Prop) ζ sid π q d l R n
      (Ll: L l):
      ⊢ ep sid π d -∗ sgn sid l (Some false) -∗ obls_rel L ζ R -∗
        sgns_level_gt R l -∗ th_phase_frag ζ π q -∗
        OU_rep n (cp_mul π d n ∗ sgn sid l (Some false) ∗
                  obls_rel L ζ R ∗ th_phase_frag ζ π q).
    Proof using H0 H1.
      iIntros "#EP ?? #GT ?".
      iInduction n as [| n] "IH".
      { iFrame. iIntros "% ?".
        iExists _. iFrame. iApply bupd_frame_l. 
        iSplit; [done| ]. iApply cp_mul_0. }
      simpl. iApply (OU_wand with "[]").
      2: { iApply (expect_sig_upd with "EP [$] [$] [$] [$]"). done. }
      iIntros "(CP & ?&?&?)".
      rewrite cp_mul_take. rewrite (bi.sep_comm _ (cp _ _)). rewrite -bi.sep_assoc.
      iApply OU_rep_frame_l. iFrame. iApply ("IH" with "[$] [$] [$]").
    Qed.

    (* TODO: ? refactor these proofs about burn_cp *)
    Lemma burn_cp_upd_impl δ ζ π deg
      (PH_MAX: exists π__max, ps_phases δ !! ζ = Some π__max /\ phase_le π π__max)
      :
      ⊢ obls_msi δ -∗ cp π deg ==∗ ∃ δ', obls_msi δ' ∗ ⌜ ∃ π__b, burns_cp δ ζ δ' π__b deg⌝.
    Proof using.
      iIntros "MSI CP".
      (* iDestruct (cp_msi_dom with "[$] [$]") as "%IN".  *)
      iDestruct (cp_msi_unfold with "[$] [$]") as "(MSI & %π0 & CP & [%IN %PH_LE])".
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl in *. iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      simpl. iRevert "CPS". iFrame. iIntros "CPS". simpl.
      rewrite /cp.
      iCombine "CPS CP" as "CPS". iMod (own_update with "CPS").
      { apply auth_update_dealloc.
        eapply local_update_proper; [..| eapply gmultiset_local_update_dealloc].
        1, 3: reflexivity.
        f_equiv. by rewrite gmultiset_difference_diag. }
      iModIntro. iFrame. iPureIntro.
      destruct PH_MAX as (?&?&?).
      exists π0. 
      erewrite (f_equal (burns_cp _ _)).
      { econstructor; eauto. etrans; eauto. }
      done. 
    Qed.

    Lemma burn_cp_upd_burn ζ π q deg:
      ⊢ cp π deg -∗ th_phase_frag ζ π q -∗ 
        OU' (fun δ1 δ2 => exists π__b, burns_cp δ1 ζ δ2 π__b deg) (th_phase_frag ζ π q).
    Proof using.
      rewrite /OU'. iIntros "CP PH % MSI".
      (* iDestruct (th_phase_msi_ge with "[$] [$]") as %(? & ? & ?).  *)
      iDestruct (th_phase_msi_frag with "[$] [$]") as "%PH".
      iMod (burn_cp_upd_impl with "[$] [$]") as "R"; eauto.
      { eexists. split; eauto. done. }
      iDestruct "R" as "(%&?&?)". iModIntro. iExists _. iFrame.
    Qed.

    Lemma burn_cp_upd ζ π q deg:
      ⊢ cp π deg -∗ th_phase_frag ζ π q -∗ OU (th_phase_frag ζ π q).
    Proof using.
      iIntros "??".
      iPoseProof (burn_cp_upd_burn with "[$] [$]") as "OU'".
      rewrite /OU /OU'. iIntros "% MSI".
      iMod ("OU'" with "[$]") as "(%&?&[% %]&?)". iModIntro.
      iExists _. iFrame. iPureIntro.
      left. eexists. left. eauto. 
    Qed.

    (* actually the locale doesn't matter here, but we need to provide some according to the definition of loc_step_ex.
       In fact, the only place where it matters is last burning fuel step and fork.
       TODO: remove locale parameter from the cases of loc_step_ex, rename it *)
    Lemma increase_eb_upd n:
      ⊢ exc_lb n -∗ OU (exc_lb (S n)).
    Proof using.
      clear H1 H0 H. 
      rewrite /OU /OU'. iIntros "EB %δ MSI".
      iDestruct (exc_lb_msi_bound with "[$] [$]") as %LB. iClear "EB".
      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&?&?&?&?&EE)".
      destruct δ. simpl. iFrame. simpl in *.
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "EE". iFrame. iIntros "EE". simpl.
      
      rewrite bi.sep_comm -bi.sep_assoc.  
      iSplitR.
      { iPureIntro. right. right. 
        erewrite (f_equal (increases_eb _)).
        { econstructor; eauto. }
        simpl. reflexivity. }

      rewrite -own_op cmra_comm. 
      iApply (own_update with "[$]").
      etrans. 
      { eapply mono_nat_update. apply PeanoNat.Nat.le_succ_diag_r. }
      rewrite Nat.add_1_r. apply cmra_update_included.
      rewrite {2}mono_nat_auth_lb_op. apply cmra_mono_l.
      apply mono_nat_lb_mono. lia.
    Qed.
    
    Lemma OU'_mod P rel R:
      (∀ δ, obls_msi δ -∗ obls_msi δ ∗ R) -∗ (R -∗ OU' rel P) -∗ OU' rel P.
    Proof using.
      iIntros "GET OU". rewrite /OU'.
      iIntros "% MSI". iDestruct ("GET" with "[$]") as "[MSI R]".
      iApply ("OU" with "[$] [$]").
    Qed.

    Lemma OU_rep_mod P n R:
      (∀ δ, obls_msi δ -∗ obls_msi δ ∗ R) -∗ (R -∗ OU_rep n P) -∗ OU_rep n P.
    Proof using.
      iIntros "GET OU".
      iInduction n as [| n] "IH".
      { iApply (OU'_mod with "[$] [$]"). }
      simpl.
      iApply (OU'_mod with "[$] [$]").
    Qed.

    Lemma increase_eb_upd_rep n k:
      ⊢ exc_lb n -∗ OU_rep k (exc_lb (n + k)).
    Proof using.
      clear H1 H0 H.
      iIntros "EB".
      iInduction k as [| k] "IH" forall (n); simpl.
      { iFrame "#∗". rewrite Nat.add_0_r.
        iIntros (?) "?". iExists _. by iFrame. }      
      iApply (OU_wand with "[]").
      2: { iApply (increase_eb_upd with "[$]"). }
      iIntros "EB". iApply (OU_rep_wand with "[]").
      2: { iApply ("IH" with "[$]"). }
      rewrite Nat.add_succ_comm. set_solver.
    Qed.

 (*    (* TODO: move *) *)
 (*    Lemma gmap_merge1 `{Countable K} `{Op A} (k: K) (a1 a2: A): *)
 (*      merge op ({[ k := a1 ]}: gmap K A) {[ k := a2 ]} = {[ k := a1 ⋅ a2 ]}.  *)

 (* (◯ merge op {[ζ := ● GSet (R0 ∖ R')]} {[ζ := ◯ GSet (R ∖ R')]})) *)

    Lemma increase_eb_upd_rep0 k:
      ⊢ OU_rep k (exc_lb k).
    Proof using.
      clear H1 H0 H.
      iApply (OU_rep_mod _ _ (exc_lb 0)).
      2: { iIntros. rewrite -{2}(Nat.add_0_l k). iApply (increase_eb_upd_rep with "[$]"). }
      iIntros "% (?&?&?&?&?&EX)".
      rewrite mono_nat_auth_lb_op. iDestruct "EX" as "[??]". iFrame.
      iApply (exc_lb_le with "[$]"). lia.
    Qed.

    Local Lemma merge_helper ζ' R1 R2: 
      @merge _ (@gmap_merge Locale _ _) _ _ _ op
           {[ζ' := ● GSet R1]} {[ζ' := ◯ @GSet SignalId _ _ R2]} =
        {[ζ' := ● GSet R1 ⋅ ◯ GSet R2]}.
    Proof using.
      etrans.
      2: eapply merge_singleton.
      { reflexivity. }
      done.
    Qed.

    (* TODO: use in other places, upstream? *)
    Lemma gset_disj_dealloc_diff_local_update:
  ∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} (X Y Z : gset K)
    (SUB_ZY: Z ⊆ Y),
    (GSet X, GSet Y) ~l~> (GSet (X ∖ Z), GSet (Y ∖ Z)).
    Proof using.
      clear. 
      intros .
      apply local_update_discrete. intros mz VALID EQUIV.
      apply subseteq_disjoint_union_L in SUB_ZY as (D&->&DISJ).
      split.
      { eapply cmra_valid_included; eauto. set_solver. }
      destruct mz; [| set_solver]. simpl in EQUIV. destruct c; [| set_solver]. simpl.
      rewrite EQUIV in VALID. rewrite gset_disj_union in EQUIV.
      2: { by apply gset_disj_valid_op. }
      inversion EQUIV. subst.
      rewrite gset_disj_union; set_solver.
    Qed. 
      

    (* TODO: ? refactor these proofs about fork step *)
    Lemma fork_locale_upd_impl (L: Level -> Prop) δ ζ ζ' π R R'
      (FRESH: ζ' ∉ dom $ ps_phases δ)
      (DOM_EQ: dom_phases_obls δ)
      (SUB: R' ⊆ R)
      :
      ⊢ obls_msi δ -∗ th_phase_eq ζ π -∗ obls_rel L ζ R ==∗ 
        ∃ δ' π1 π2, obls_msi δ' ∗ th_phase_eq ζ π1 ∗ th_phase_eq ζ' π2 ∗
              obls_rel L ζ (R ∖ R') ∗
              obls_rel (fun _ => (True: Prop)) ζ' R' ∗ (* !!! *)
              ⌜ forks_locale δ ζ δ' ζ' R' ⌝ ∗
              ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝. 
    Proof using H1 H0.
      clear H.
      iIntros "MSI PH OB".
      (* iDestruct (th_phase_msi_ge_strong with "[$] [$]") as "(MSI & %π0 & (PH & %PH & %PLE))". *)
      iDestruct (th_phase_msi_frag with "[$] [$]") as "%PH".
      iDestruct (obls_rel_msi_exact_res with "[$] [$]") as "(%R0 & MSI & OB & #REST & %Rζ & %SUB0 & %REST)".
      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&?&OBLS&?&PHASES&?)".
      destruct δ. simpl in *. iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      simpl. iRevert "OBLS PHASES". iFrame. iIntros "OBLS PHASES". simpl.
      iCombine "OBLS OB" as "OBLS". iCombine "PHASES PH" as "PHASES".
      
      iExists (fork_left π), (fork_right π).
      rewrite !bi.sep_assoc. iSplitL.
      2: { iPureIntro. split.
           (* all: eapply strict_transitive_r; [eauto | apply phase_lt_fork].   *)
           all: by apply phase_lt_fork. }

      iSplitL.
      2: { iPureIntro.
           erewrite (f_equal (forks_locale _ _)).
           { econstructor; eauto. }
           simpl. reflexivity. }

      rewrite !Rζ. simpl.  
      (* rewrite -(bi.sep_assoc _ _ (obls _ _)). rewrite -(bi.sep_comm (obls _ _ ∗ obls _ _)%I). *)
      (* rewrite -!bi.sep_assoc. *)
      (* do 2 rewrite bi.sep_assoc.  *)
      rewrite -!bi.sep_assoc. rewrite (bi.sep_comm (own _ _)).
      rewrite -!bi.sep_assoc. do 2 rewrite bi.sep_assoc.

      iSplitL "PHASES".
      - iDestruct "PHASES" as "[AUTH PH]".
        iMod (ghost_map_update with "[$] [$]") as "[AUTH PH]". iFrame "PH".
        iMod (ghost_map_insert with "[$]") as "[AUTH PH]".
        2: { iFrame. by rewrite !fmap_insert. }
        rewrite lookup_insert_ne.
        2: { intros <-. destruct FRESH. by apply elem_of_dom. }
        rewrite lookup_fmap. by rewrite not_elem_of_dom_1.
      - rewrite intersection_comm_L subseteq_intersection_1_L.
        2: { set_solver. }
        rewrite /obls_rel.

        iApply bi.sep_exist_r. iExists (R0 ∖ R').
        rewrite (bi.sep_assoc _ (own _ _)). rewrite -own_op.
        
        rewrite -bi.sep_assoc. rewrite bi.sep_comm. rewrite -bi.sep_assoc.
        iSplitR.
        { iApply big_sepS_mono'; [..| by iApply "REST"].
          { done. }
          set_solver. }
        
        rewrite -bi.sep_assoc. iApply bi.sep_exist_r. iExists R'.
        rewrite (bi.sep_assoc _ (own _ (◯ _))). rewrite -own_op. 
        rewrite -auth_frag_op.
        rewrite -bi.sep_assoc. rewrite bi.sep_comm. rewrite -bi.sep_assoc.
        iSplitR.
        { rewrite difference_diag_L. set_solver. }

        rewrite -auth_frag_op. rewrite !gmap_op.
        rewrite !merge_helper. 
                
        rewrite -!own_op. iApply own_update; [| by iFrame].
        (* rewrite -auth_frag_op. rewrite (cmra_comm (◯ _) _). *)
        etrans.
        (* { apply auth_update. *)
        (*   rewrite fmap_insert. apply singleton_local_update_any. *)
        (*   intros. replace (R0 ∖ (R0 ∩ R')) with (R0 ∖ R') by set_solver.  *)
        (*   apply exclusive_local_update. done. *)


        
        2: {
          (* rewrite auth_frag_op. *)
             
             rewrite -cmra_assoc. rewrite (cmra_comm (◯ _) _) cmra_assoc.
             apply cmra_update_op; [| reflexivity].
             apply auth_update_alloc.
             rewrite /obls_map_repr.
             rewrite fmap_insert.
             rewrite fmap_insert.             
             apply alloc_singleton_local_update.
             2: { by apply auth_both_valid_2. } 
             apply not_elem_of_dom. rewrite dom_insert_L dom_fmap.
             rewrite not_elem_of_union not_elem_of_singleton. split.
             - intros ->. destruct FRESH. by apply elem_of_dom.
             - by rewrite -DOM_EQ. }
        (* rewrite (cmra_comm (◯ _) _). *)
        apply auth_update.
        
        (* rewrite fmap_insert. *)
        apply singleton_local_update_any.
        intros ? EQ. replace (R0 ∖ (R0 ∩ R')) with (R0 ∖ R') by set_solver.
        rewrite lookup_fmap Rζ in EQ. simpl in EQ. inversion EQ. subst x.

        apply auth_local_update. apply gset_disj_dealloc_diff_local_update.
        all: done.
    Qed.


    (***** Bounded obligations update *****)
    
    Definition obls_msi_interim δ (k: nat): iProp Σ :=
      ∃ δ__k, obls_msi δ__k ∗ ⌜ nsteps (fun p1 p2 => loc_step_ex p1 p2) k δ δ__k ⌝.

    Context {invs_inΣ: invGS_gen HasNoLc Σ}.

    Definition BOU E b (P: iProp Σ): iProp Σ :=
      ∀ δ k, obls_msi_interim δ k ={E}=∗ ∃ k', obls_msi_interim δ k' ∗ ⌜ k' - k <= b ⌝ ∗ P. 

    Lemma lse_rep_phases_eq_helper δ1 δ2 n
      (TRANSS: nsteps loc_step_ex n δ1 δ2):
      ps_phases δ1 = ps_phases δ2.
    Proof using.
      symmetry. pattern δ2. 
      eapply pres_by_loc_step_implies_rep; eauto.
      apply loc_step_phases_pres.
    Qed.

    Lemma obls_msi_interim_progress_impl δ n τ π deg
      (BOUND: n <= LIM_STEPS)
      (PH: ps_phases δ !! τ = Some π):
      ⊢ obls_msi_interim δ n -∗ cp π deg ==∗
        ∃ δ', obls_msi δ' ∗ ⌜ progress_step δ τ δ' ⌝.
    Proof.
      iIntros "MSI' cp".
      rewrite /obls_msi_interim.
      
      iDestruct "MSI'" as (δ__k) "(MSI&%TRANSS)".
      iDestruct (cp_msi_unfold with "[$] [$]") as "[MSI (%π' & CP & [%IN %LE])]".
      
      iMod (burn_cp_upd_impl with "[$] [CP]") as "X".
      2: { iExists _. iFrame. done. }
      { eexists. split; [| reflexivity].
        erewrite <- lse_rep_phases_eq_helper; eauto. }
      iDestruct "X" as "(%δ' & MSI & [%π__b %BURNS])". 
      iModIntro. iExists _. iFrame.

      iPureIntro. eexists. split; eauto.
      eexists. split; eauto.
    Qed.
    
    Lemma obls_msi_interim_progress δ E τ π q P:
      ⊢ obls_msi δ -∗ BOU E LIM_STEPS (∃ d, cp π d ∗ th_phase_frag τ π q ∗ P)
         ={E}=∗ ∃ δ', obls_msi δ' ∗ ⌜ progress_step δ τ δ' ⌝ ∗ th_phase_frag τ π q ∗ P.
    Proof using.
      iIntros "MSI BOU".
      rewrite /BOU. iMod ("BOU" with "[MSI]") as (n) "(MSI & %BOUND & (%d & CP & PH & P))".
      { rewrite /obls_msi_interim. iExists _. iFrame.
        iPureIntro. by apply nsteps_0. }
      iFrame "P".
      rewrite /obls_msi_interim. iDestruct "MSI" as (?) "(MSI & %STEPS)".
      iDestruct (th_phase_msi_frag with "[$] [$]") as "%PH".
      iFrame. iApply (obls_msi_interim_progress_impl with "[MSI] [$]").
      3: { iExists _. by iFrame. }
      { lia. }
      erewrite lse_rep_phases_eq_helper; eauto.
    Qed.

    Lemma obls_msi_interim_omtrans_fork_impl L δ n τ τ' π deg R R'
      (BOUND: n <= LIM_STEPS)
      (FRESH: τ' ∉ dom $ ps_phases δ)
      (DPO: dom_phases_obls δ)
      (SUB: R' ⊆ R)
      :
      ⊢ obls_msi_interim δ n -∗ cp π deg  -∗ obls_rel L τ R -∗ th_phase_eq τ π ==∗
        ∃ δ' π1 π2,
          obls_msi δ' ∗
            obls_rel L τ (R ∖ R') ∗ th_phase_eq τ π1 ∗
            obls_rel (fun _ => True: Prop) τ' R' ∗ th_phase_eq τ' π2 ∗
            ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝ ∗
                                ⌜ rel_compose (flip progress_step τ) (fork_step_of τ) δ δ' ⌝.
    Proof using H1 H0.
      clear H.
      iIntros "MSI' CP OB PH".
      rewrite /obls_msi_interim. 
      iDestruct "MSI'" as (δ__k) "(MSI&%TRANSS)".
      iDestruct (th_phase_msi_frag with "[$] [$]") as "%PH".

      pose proof TRANSS as PH_EQ. 
      unshelve eapply (pres_by_loc_step_implies_rep _ _ _ _ _) in PH_EQ.
      { eapply loc_step_phases_pres. }
      2: reflexivity.
      
      iMod (obls_msi_interim_progress_impl _ _ τ with "[MSI] [$]") as (?) "(MSI&%PSTEP)".
      3: { iExists _. iFrame. eauto. }
      { eauto. }
      { by rewrite -PH_EQ. }

      iMod (fork_locale_upd_impl with "[$] [$] [$]") as "Y"; eauto.
      { unshelve eapply (pres_by_loc_step_implies_progress _ _ _ _ _) in PSTEP.
        { eapply loc_step_phases_pres. }
        3: reflexivity.
        2: { rewrite -PSTEP in FRESH. apply FRESH. }
      }
      { eapply pres_by_loc_step_implies_progress; eauto.
        apply loc_step_dpo_pres. }
      
      iDestruct "Y" as "(%δ'' & %π1 & %π2 & MSI & PH1 & PH3 & OB1 & OB2 & %FORKS & [%LT1 %LT2])".
      iModIntro. do 3 iExists _. iFrame. iPureIntro. split; eauto.
      eexists. split; eauto.
      red. eauto.
    Qed.

    Lemma obls_msi_interim_omtrans_fork L δ E τ τ' π R R' P
      (FRESH: τ' ∉ dom $ ps_phases δ)
      (DPO: dom_phases_obls δ)
      (SUB: R' ⊆ R)
      :
      ⊢ obls_msi δ -∗
        BOU E LIM_STEPS (∃ d, cp π d ∗ obls_rel L τ R ∗ th_phase_eq τ π ∗ P) ={E}=∗
        ∃ δ' π1 π2,
          obls_msi δ' ∗
            obls_rel L τ (R ∖ R') ∗ th_phase_eq τ π1 ∗
            obls_rel (fun _ => True: Prop) τ' R' ∗ th_phase_eq τ' π2 ∗
            ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝ ∗
            ⌜ rel_compose (flip progress_step τ) (fork_step_of τ) δ δ' ⌝ ∗ P. 
    Proof using H1 H0.
      iIntros "MSI BOU".
      rewrite /BOU. iMod ("BOU" with "[MSI]") as (n) "(MSI & %BOUND & (%d & PHN & OB & CP & P))".
      { rewrite /obls_msi_interim. iExists _. iFrame.
        iPureIntro. by apply nsteps_0. }
      iFrame "P".
      iApply (obls_msi_interim_omtrans_fork_impl with "[$] [$] [$] [$]"); try done.
      lia.
    Qed.
      
    Lemma BOU_intro E b (P : iProp Σ):
      ⊢ P -∗ BOU E b P.
    Proof using.
      rewrite /BOU. iIntros "**". 
      iExists _. iFrame. iPureIntro. lia.
    Qed.
    
    Global Instance BOU_proper:
      Proper (equiv ==> eq ==> equiv ==> equiv) BOU.
    Proof using. solve_proper. Qed.
    
    Lemma BOU_frame_l E b (P Q : iProp Σ):
      ⊢ P -∗ BOU E b Q -∗ BOU E b (P ∗ Q).
    Proof using.
      rewrite /BOU. iIntros "P BOU **".
      iMod ("BOU" with "[$]") as "(%&?&?&?)". iModIntro.
      iExists _. iFrame.
    Qed.
    
    Lemma BOU_frame_r E b (P Q : iProp Σ):
      ⊢ Q -∗ BOU E b P -∗ BOU E b (P ∗ Q).
    Proof using.
      rewrite bi.sep_comm. iApply BOU_frame_l.
    Qed.
    
    Lemma BOU_weaken E1 E2 m1 m2 P1 P2
      (LE: m1 <= m2)
      (SUB: E1 ⊆ E2):
      ⊢ (P1 -∗ P2) -∗ BOU E1 m1 P1 -∗ BOU E2 m2 P2.
    Proof using.
      rewrite /BOU.
      iIntros "IMPL BOU". iIntros "**".
      iApply fupd_mask_mono; [apply SUB| ].
      iMod ("BOU" with "[$]") as (?) "(? & % & ?)". iModIntro.
      iExists _. iFrame. iSplitR.
      { iPureIntro. lia. }
      by iApply "IMPL".
    Qed.
    
    Lemma BOU_wand E b (P Q : iProp Σ):
      ⊢ (P -∗ Q) -∗ BOU E b P -∗ BOU E b Q.
    Proof using.
      iIntros "**". by iApply (BOU_weaken with "[$]").
    Qed.
    
    Lemma BOU_lower E m n P (LE: m <= n):
      ⊢ BOU E m P -∗ BOU E n P.
    Proof using.
      clear H1 H0 H.
      iIntros "**". iApply (BOU_weaken); try done. set_solver.
    Qed.
    
    Lemma BOU_invs E P n:
      (|={E, ∅}=> BOU ∅ n (|={∅, E}=>P)) -∗ BOU E n P.
    Proof using.
      iIntros "BOU". rewrite /BOU. iIntros.
      iMod "BOU". iMod ("BOU" with "[$]") as (?) "(SI & % & P)".
      iMod "P". iModIntro. iExists _. by iFrame.
    Qed.
    
    Lemma BOU_mask_comm E E' n Φ P
      (SUB: E' ⊆ E):
      (P -∗ BOU E n Φ) -∗ (|={E', E}=> P) -∗ BOU E' n (|={E', E}=> Φ).
    Proof using.
      iIntros "BOU CLOS".
      rewrite /BOU. iIntros.
      iMod "CLOS" as "P".
      iSpecialize ("BOU" with "[$] [$]").
      iMod "BOU" as (?) "(?&?&?)".
      iApply fupd_mask_intro; [done| ].
      iIntros "CLOS". iFrame. iExists _. iFrame.
    Qed.

    Lemma BOU_mask_comm' E E' n Φ P Q
      (SUB: E' ⊆ E):
      (P -∗ BOU E n (Q -∗ Φ)) -∗ (|={E', E}=> P) -∗ BOU E' n (Q ={E', E}=∗ Φ).
    Proof using.
      iIntros "BOU CLOS".
      rewrite /BOU. iIntros.
      iMod "CLOS" as "P".
      iSpecialize ("BOU" with "[$] [$]").
      iMod "BOU" as (?) "(?&?&WAND)".
      iApply fupd_mask_intro; [done| ].
      iIntros "CLOS". iFrame. iExists _. iFrame.
      iIntros "?". iMod "CLOS". by iApply "WAND".
    Qed.
  
    Lemma BOU_split E P n m:
      ⊢ BOU E n (BOU E m P) -∗ BOU E (n + m) P.
    Proof using.
      iIntros "BOU1".
      rewrite {1}/BOU. 
      iIntros (δ k) "TI'".
      iMod ("BOU1" with "[$]") as (t) "(TI' & %LE & BOU')".
      iMod ("BOU'" with "[$]") as (v) "(TI' & %LE' & P)".
      iModIntro. iExists _. iFrame. iPureIntro. lia. 
    Qed.

    Lemma OU_BOU E P b:
      ⊢ OU (BOU E b P) -∗ BOU E (S b) P.
    Proof using.
      iIntros "OU". rewrite {2}/BOU /obls_msi_interim.
      iIntros (δ n) "TI'".
      iDestruct "TI'" as "(%δ_ & MSI & %TRANS1)".
      rewrite /OU. iMod ("OU" with "[$]") as "(%δ' & MSI & %TRANS2 & CONT)".
      
      iSpecialize ("CONT" with "[MSI]").
      { iExists _. iFrame. 
        iPureIntro.
        eapply rel_compose_nsteps_next. eexists. split; eauto. }
      iMod "CONT" as "(%n' & TI' & %BOUND' & P)". iModIntro.
      iExists _. iFrame.
      iPureIntro. lia. 
    Qed.

    Lemma OU_BOU' E P b
      (NZ: 0 < b):
      ⊢ OU (BOU E (b - 1) P) -∗ BOU E b P.
    Proof using.
      red in NZ. apply Nat.le_sum in NZ as [? ->].
      rewrite Nat.sub_add'. iApply OU_BOU.
    Qed.

    Lemma OU_BOU_rep E P b:
      ⊢ OU_rep b P -∗ BOU E b P.
    Proof using.
      iIntros "OUs". iInduction b as [| b] "IH"; simpl.
      { rewrite /BOU /obls_msi_interim.
        iIntros (δ n) "TI'".
        iDestruct "TI'" as "(%δ_ & MSI & %TRANS1)".
        iMod ("OUs" with "[$]") as "(% & ? & -> & ?)".
        iModIntro. iExists n. iFrame. iSplit; [| by rewrite Nat.sub_diag].        
        iExists _. iFrame. eauto. }
      iApply OU_BOU. iApply (OU_wand with "[-OUs] [$]"). done.
    Qed.
    
    (* (* an example usage of OU+BOU *) *)
    (* Lemma BOU_step_create_signal E ζ P b l R: *)
    (*   ⊢ (∀ sid, sgn sid l (Some false) -∗ obls ζ (R ∪ {[ sid ]}) -∗ BOU E b P) -∗ obls ζ R -∗ BOU E (S b) P. *)
    (* Proof using. *)
    (*   iIntros "CONT OB". *)
    (*   iApply OU_BOU. iApply (OU_wand with "[CONT]"). *)
    (*   { setoid_rewrite bi.wand_curry. rewrite -bi.exist_wand_forall. *)
    (*     iFrame. } *)
    (*   iPoseProof (OU_create_sig with "OB") as "OU". *)
    (*   iApply (OU_wand with "[-OU] [$]"). *)
    (*   iIntros "(%&?&?&?)". iExists _. iFrame.  *)
    (* Qed. *)

    (* useful as the first step's BOU of a function call *)
    Lemma first_BOU π d0 d n E
      (DEG_LT: deg_lt d d0):
      cp π d0 -∗ BOU E (S n) (cp_mul π d n ∗ exc_lb n).
    Proof using.
      iIntros "CP".
      do 2 rewrite -Nat.add_1_r. simpl. iApply BOU_split.
      iApply OU_BOU_rep.
      iApply (OU_rep_wand with "[-]").
      2: { iApply (increase_eb_upd_rep0). }
      iIntros "#EB".
      
      iApply OU_BOU. iApply (OU_wand with "[-CP]").
      2: { iApply (exchange_cp_upd with "[$] [$]").
           { reflexivity. }
           eauto. }
      iIntros "CPS".
      iApply BOU_intro. iFrame "#∗".
    Qed.

  End Resources.

End ObligationsRepr.
