From iris.proofmode Require Import tactics.
From iris.base_logic Require Import own. 
From iris.algebra Require Import auth gmap gset excl gmultiset big_op mono_nat.
From trillium.fairness Require Import (* fairness *) locales_helpers utils.
From trillium.fairness.lawyer.obligations Require Import obligations_model. 
From stdpp Require Import namespaces. 
From trillium.fairness.lawyer.obligations Require Import obls_utils.

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

  Class ObligationsPreGS Σ := {
      obls_pre_cps :> inG Σ (authUR (gmultisetUR cpO));
      obls_pre_sigs :> inG Σ (authUR (gmapUR SignalId sstR));
      obls_pre_obls :> inG Σ (authUR (gmapUR Locale (exclR (gsetUR natO))));
      obls_pre_eps :> inG Σ (authUR (gsetUR epO)); (* allowing duplication of eps *)
      obls_pre_phs :> inG Σ (authUR (gmapUR Locale (exclR phO)));
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

  Definition obls_map_repr (omap: gmap Locale (gset SignalId)):
    gmapUR Locale (exclR (gsetUR natO)) :=
    Excl <$> omap.

  Definition phases_repr (pmap: gmap Locale Phase):
    gmapUR Locale (exclR phO) :=
    fmap Excl pmap (FMap := gmap_fmap).
  
  Definition eps_repr (eps: gset ExpectPermission): gsetUR epO :=
    eps.

  Definition cps_repr (cps: gmultiset (@CallPermission Degree)): (gmultisetUR cpO) := cps.

  Definition obls_msi {Σ: gFunctors} {oGS: ObligationsGS Σ} (ps: ProgressState): iProp Σ :=
    own obls_cps (● (cps_repr $ ps_cps ps)) ∗
    own obls_sigs (● (sig_map_repr $ ps_sigs ps)) ∗
    own obls_obls (● (obls_map_repr $ ps_obls ps)) ∗
    own obls_eps (● (eps_repr $ ps_eps ps)) ∗
    own obls_phs (● (phases_repr $ ps_phases ps)) ∗
    own obls_exc_lb (●MN (ps_exc_bound ps))
  . 
  
  Definition obls_Σ: gFunctors := #[
      GFunctor (authUR (gmultisetUR cpO));
      GFunctor (authUR (gmapUR SignalId sstR));
      GFunctor (authUR (gmapUR Locale (exclR (gsetR natO))));
      GFunctor (authUR (gsetUR epO));
      GFunctor (authUR (gmapUR Locale (exclR phO)));
      GFunctor (mono_natUR)
   ].

  Global Instance obls_Σ_pre:
    ∀ Σ, subG obls_Σ Σ → ObligationsPreGS Σ.
  Proof using. solve_inG. Qed.           

  Section Resources.
    Context `{oGS: ObligationsGS Σ}. 

    Definition cp (ph: Phase) (deg: Degree): iProp Σ :=
      own obls_cps (◯ (cps_repr ({[+ ((ph, deg)) +]}))). 

    Definition cp_mul ph deg n: iProp Σ :=
      own obls_cps (◯ (n *: {[+ (ph, deg) +]})). 

    Definition cps (m: gmultiset (@CallPermission Degree)) : iProp Σ :=
      own obls_cps (◯ (cps_repr m)). 

    Definition sgn (sid: SignalId) (l: Level) (ob: option bool): iProp Σ :=
      own obls_sigs (◯ ({[ sid := (to_agree l, mbind (Some ∘ Excl) ob ) ]})).
    
    Definition obls τ (R: gset SignalId) :=
      own obls_obls (◯ ({[ τ := Excl R]}: gmapUR Locale (exclR (gsetR natO)))).
    
    Definition sgns_level_gt (R: gset SignalId) lm: iProp Σ :=
      [∗ set] s ∈ R, (∃ l, sgn s l None ∗ ⌜ lvl_lt lm l ⌝). 
    
    Definition ep (sid: SignalId) π d: iProp Σ :=
    own obls_eps (◯ {[ (sid, π, d) ]}). 
    
    Definition exc_lb (n: nat) :=
      own obls_exc_lb (mono_nat_lb n).

    (* Definition th_phase_ge ζ π: iProp Σ := *)
    (*   ∃ π__max, own obls_phs (◯ (phases_repr {[ ζ := π__max]})) ∗ ⌜ phase_le π π__max⌝. *)
    Definition th_phase_eq ζ π: iProp Σ :=
      own obls_phs (◯ (phases_repr {[ ζ := π]})). 

    Lemma obls_proper ζ R1 R2 (EQUIV: R1 ≡ R2):
      ⊢ obls ζ R1 ∗-∗ obls ζ R2.
    Proof using. clear H H0 H1. set_solver. Qed.
    
    Lemma cp_msi_dom δ ph deg:
      ⊢ obls_msi δ -∗ cp ph deg -∗
        ⌜ (ph, deg) ∈ ps_cps δ ⌝.
    Proof using.
      clear H H0 H1.
      rewrite /obls_msi. iIntros "(CPS&_) CP". 
      iCombine "CPS CP" as "CPS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete, proj1 in V.
      apply gmultiset_singleton_subseteq_l.
      by apply gmultiset_included.
    Qed.

    Lemma obls_msi_exact δ ζ R:
      ⊢ obls_msi δ -∗ obls ζ R -∗
        ⌜ ps_obls δ !! ζ = Some R ⌝.
    Proof using.
      clear H0 H H1. 
      rewrite /obls_msi. iIntros "(_&_&OBLS&_) OB". 
      iCombine "OBLS OB" as "OBLS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      eapply singleton_included_exclusive_l in SUB; try done.
      2: { apply _. }
      apply leibniz_equiv.
      rewrite /obls_map_repr in SUB.
      rewrite lookup_fmap in SUB. 
      apply fmap_Some_equiv_1 in SUB. destruct SUB as (?&?&?).
      inversion H0. subst. rewrite H. set_solver. 
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
    Proof. apply _. Qed.  

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

    Lemma th_phase_msi_eq_strong δ ζ π:
      ⊢ obls_msi δ -∗ th_phase_eq ζ π -∗        
        obls_msi δ ∗ own obls_phs (◯ phases_repr {[ζ := π]}) ∗ ⌜ ps_phases δ !! ζ = Some π ⌝. 
    Proof using.
      rewrite /obls_msi. iIntros "(?&?&?&?&PHASES&?) PH".
      iRevert "PHASES PH". iFrame. iIntros "PHASES PH".  
      rewrite /th_phase_eq. 
      iDestruct (own_valid with "[PHASES PH]") as "#V".
      { iApply own_op. iApply bi.sep_comm. iFrame. }
      iDestruct "V" as %V. 
      iFrame. iPureIntro. 
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

    (* Lemma th_phase_msi_ge δ ζ π: *)
    (*   ⊢ obls_msi δ -∗ th_phase_ge ζ π -∗         *)
    (*     ⌜ exists π__max, ps_phases δ !! ζ = Some π__max /\ phase_le π π__max ⌝.  *)
    (* Proof using. *)
    (*   iIntros "? ?".  *)
    (*   iDestruct (th_phase_msi_ge_strong with "[$] [$]") as "[? L]". *)
    (*   iDestruct "L" as (?) "[? %F]". *)
    (*   iPureIntro. eauto.  *)
    (* Qed. *)

    (* Global Instance th_phase_ge_Proper: *)
    (*   Proper (eq ==> (flip phase_le) ==> bi_entails) th_phase_ge. *)
    (* Proof using. *)
    (*   red. intros ??-> ???. *)
    (*   rewrite /th_phase_ge. iIntros "(% & ? & %)". *)
    (*   iExists _. iFrame. iPureIntro. etrans; eauto. *)
    (* Qed. *)

    Lemma exc_lb_msi_bound δ n:
      ⊢ obls_msi δ -∗ exc_lb n -∗ ⌜ n <= ps_exc_bound δ ⌝.
    Proof using.
      rewrite /obls_msi. iIntros "(_&_&_&_&_&B) LB".
      iCombine "B LB" as "LB".
      iDestruct (own_valid with "LB") as %V. iPureIntro.
      by apply mono_nat_both_valid in V.
    Qed.

    Lemma obls_sgn_lt_locale_obls δ ζ R lm:
      ⊢ obls_msi δ -∗ obls ζ R -∗ sgns_level_gt R lm -∗
        ⌜ lt_locale_obls lm ζ δ ⌝.
    Proof using H1 H0.
      iIntros "MSI OBLS SIGS_LT".
      iDestruct (obls_msi_exact with "[$] [$]") as %Rζ. 
      rewrite /lt_locale_obls. rewrite Rζ. simpl.
      rewrite -pure_forall_2. setoid_rewrite <- bi.pure_impl_2. 
      iIntros (l IN).

      (* TODO: lemma? *)
      apply extract_Somes_gset_spec in IN. simpl in IN.
      apply elem_of_map in IN. destruct IN as [sid [EQ IN]].
      destruct (ps_sigs δ !! sid) as [[l' b]| ] eqn:SID; [| done].
      simpl in EQ. inversion EQ. subst l'. 

      iDestruct (big_sepS_forall with "SIGS_LT") as "LT".
      iSpecialize ("LT" $! _ IN). iDestruct "LT" as "(%l_ & SIG & %LT)".
      iDestruct (sigs_msi_in with "[$] [$]") as %[? SIG].
      rewrite SID in SIG. inversion SIG. subst l_ x. 
      done.
    Qed. 

    Lemma ep_msi_in δ sid π d:
      ⊢ obls_msi δ -∗ ep sid π d -∗
        ⌜ ((sid, π, d): (@ExpectPermission _)) ∈ (ps_eps δ) ⌝. 
    Proof using. 
      rewrite /obls_msi. iIntros "(_&_&_&EPS&_) EP". 
      iCombine "EPS EP" as "EPS". 
      iDestruct (own_valid with "[$]") as %V. iPureIntro.
      apply auth_both_valid_discrete in V as [SUB V].
      by apply gset_included, singleton_subseteq_l in SUB.
    Qed. 

    Let OU' (R: ProgressState -> ProgressState -> Prop) P: iProp Σ :=
      ∀ δ, obls_msi δ ==∗ ∃ δ', obls_msi δ' ∗ ⌜ R δ δ'⌝ ∗ P. 

    Definition OU := OU' (loc_step_ex).

    Lemma OU_wand P Q:
      (P -∗ Q) -∗ OU P -∗ OU Q.
    Proof using.
      iIntros "PQ OU".
      rewrite /OU /OU'. iIntros "**".
      iSpecialize ("OU" with "[$]"). iMod "OU" as "(%&?&?&?)". iModIntro.
      iExists _. iFrame. by iApply "PQ".
    Qed.
        
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

    Lemma OU_create_sig ζ R l:
      ⊢ obls ζ R -∗ OU (∃ sid, sgn sid l (Some false) ∗ obls ζ (R ∪ {[ sid ]}) ∗
                                 ⌜ sid ∉ R ⌝).
    Proof using.
      clear H1 H0 H. 
      rewrite /OU /OU'. iIntros "OB %δ MSI".
      set (sid := next_sig_id (R ∪ (dom $ ps_sigs δ))).
      iDestruct (obls_msi_exact with "[$] [$]") as %Rζ. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&SIGS&OBLS&?&?&?)".
      destruct δ. simpl. iFrame. simpl in *.
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "SIGS OBLS". iFrame. iIntros "SIGS OBLS". simpl.
      rewrite !bi.sep_assoc. 

      rewrite bi.sep_comm bi.sep_assoc.  
      iSplitL.
      2: { iPureIntro. exists ζ. 
           red. do 2 right. left. exists l. 
           erewrite (f_equal (creates_signal _ _)).
           { econstructor; eauto. simpl. eapply elem_of_dom; eauto. }
           simpl. reflexivity. }

      iMod (own_update with "[OB OBLS]") as "X".
      2: iCombine "OBLS OB" as "?"; iFrame.
      { apply auth_update.
        apply singleton_local_update_any.
        intros ? RR. apply lookup_fmap_Some in RR as (R_&?&Rζ_).
        rewrite Rζ in Rζ_. inversion Rζ_. subst R_. subst.
        apply exclusive_local_update with (x' := Excl (R ∪ {[sid]})). done. }
      rewrite Rζ. simpl. iDestruct "X" as "[OBLS ?]".
      rewrite bi.sep_exist_r. iApply bupd_exist. iExists sid. 
      rewrite -fmap_insert. iFrame.

      rewrite bi.sep_comm. rewrite bi.sep_assoc. iSplitL.
      2: { iPureIntro. eapply not_elem_of_weaken. 
           { by intros IN%next_sig_id_fresh. }
           set_solver. }
      
      rewrite -own_op. iApply own_update; [| by iFrame].
      apply auth_update_alloc. 
      eapply local_update_proper.
      1: reflexivity.
      2: eapply alloc_local_update.
      { rewrite /sig_map_repr. rewrite insert_empty fmap_insert. reflexivity. }
      2: done.
      apply not_elem_of_dom.
      subst sid. rewrite dom_fmap_L.
      eapply not_elem_of_weaken; [apply next_sig_id_fresh| ]. set_solver. 
    Qed.

    (* TODO: do we need to generalize to "optional v" instead? *)
    Lemma OU_set_sig ζ R sid l v
      (IN: sid ∈ R):
      ⊢ obls ζ R -∗ sgn sid l (Some v) -∗
        OU (sgn sid l (Some true) ∗ obls ζ (R ∖ {[ sid ]})).
    Proof using H1 H0. 
      rewrite /OU /OU'. iIntros "OB SIG %δ MSI".
      iDestruct (sigs_msi_exact with "[$] [$]") as %Sζ.
      iDestruct (obls_msi_exact with "[$] [$]") as %Rζ. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(?&SIGS&OBLS&?&?&?)".
      destruct δ. simpl in *.
      iCombine "OBLS OB" as "OBLS". iCombine "SIGS SIG" as "SIGS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "OBLS SIGS". iFrame. simpl. iIntros "OBLS SIGS".

      rewrite bi.sep_comm -!bi.sep_assoc.  
      iSplitR.
      { iPureIntro. exists ζ.
        red. do 3 right. left. exists sid. 
        erewrite (f_equal (sets_signal _ _)).
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

    Lemma exchange_cp_upd ζ π π__cp d d' b k
      (LE: k <= b)
      (PH_LE: phase_le π__cp π)
      (DEG: deg_lt d' d):
      ⊢ cp π__cp d -∗ th_phase_eq ζ π -∗ exc_lb b -∗ OU (cp_mul π__cp d' k ∗ th_phase_eq ζ π).
    Proof using.
      rewrite /OU /OU'. iIntros "CP PH #LB %δ MSI".
      iDestruct (exc_lb_msi_bound with "[$] [$]") as %LB.
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(MSI & PH & %)". 
      iDestruct (cp_msi_dom with "[$] [$]") as %CP. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl in *.
      iCombine "CPS CP" as "CPS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "CPS". iFrame. simpl. iIntros "CPS".

      rewrite bi.sep_comm -!bi.sep_assoc.  
      iSplitR.
      { iPureIntro. exists ζ. 
        red. right. left. exists π__cp, d, d', k. 
        erewrite (f_equal (exchanges_cp _ _)).
        { econstructor; eauto.
          simpl. lia. }
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
    Lemma create_ep_upd ζ π π__cp d d' sid l ov (DEG: deg_lt d' d)
      (PH_LE: phase_le π__cp π)
      :
      ⊢ cp π__cp d -∗ sgn sid l ov -∗ th_phase_eq ζ π -∗ 
        OU (ep sid π__cp d' ∗ sgn sid l ov ∗ th_phase_eq ζ π).
    Proof using H1 H0.
      rewrite /OU /OU'. iIntros "CP SIG PH %δ MSI".
      iDestruct (sigs_msi_in with "[$] [$]") as %[v Sζ].
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(MSI & PH & %)".
      iDestruct (cp_msi_dom with "[$] [$]") as %CP. 
      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&SIGS&?&EPS&?&?)".
      destruct δ. simpl in *.
      iCombine "CPS CP" as "CPS".
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "CPS EPS". iFrame. simpl. iIntros "CPS EPS".
 
      rewrite bi.sep_comm -!bi.sep_assoc.
      iSplitR.
      { iPureIntro. exists ζ. 
        red. do 4 right. left. exists sid, π__cp. do 2 eexists. 
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
           iModIntro. iApply own_mono; [| by iFrame].
           apply auth_frag_mono. apply gset_included. apply union_subseteq_r. }
      
      iApply own_update; [| by iFrame].
      apply auth_update_dealloc.
      eapply local_update_proper.
      1: reflexivity.
      2: { apply gmultiset_local_update_dealloc. reflexivity. }
      rewrite gmultiset_difference_diag. set_solver.
    Qed.
      
    Lemma th_phase_msi_align δ ζ π:
      ⊢ obls_msi δ -∗ th_phase_eq ζ π -∗
        obls_msi δ ∗ th_phase_eq ζ (default π (ps_phases δ !! ζ)). 
    Proof using.
      iIntros "? ?". 
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(? & ? & ->)".
      iFrame. 
    Qed.

    Lemma expect_sig_upd ζ sid π π__e d l R
      (PH_EXP: phase_le π__e π)
      :
      ⊢ ep sid π__e d -∗ sgn sid l (Some false) -∗ obls ζ R -∗
        sgns_level_gt R l -∗ th_phase_eq ζ π -∗
        OU (cp π d ∗ sgn sid l (Some false) ∗ obls ζ R ∗ th_phase_eq ζ π).
    Proof using H1 H0.
      rewrite /OU /OU'. iIntros "#EP SIG OBLS #SIGS_LT PH %δ MSI".
      iDestruct (sigs_msi_exact with "[$] [$]") as %Sζ.
      (* iDestruct (th_phase_msi_ge with "[$] [$]") as %(? & PH__ζ & LE__πx). *)
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(MSI & PH & %PH)".
      iDestruct (th_phase_msi_align with "[$] [$]") as "[MSI PH]".
      rewrite PH. simpl.
      iDestruct (ep_msi_in with "[$] [$]") as %EP. 
      iDestruct (obls_sgn_lt_locale_obls with "[$] [$] [$]") as %LT. 

      rewrite {1}/obls_msi. iDestruct "MSI" as "(CPS&?&?&?&?&?)".
      destruct δ. simpl in *.
      iApply bupd_exist. iExists (Build_ProgressState _ _ _ _ _ _). 
      iRevert "CPS". iFrame. simpl. iIntros "CPS".

      rewrite /cp /cps_repr /eps_repr. 
      rewrite bi.sep_comm -bi.sep_assoc.
      iSplitR.
      { iPureIntro. exists ζ. 
        red. do 5 right. do 3 eexists. 
        erewrite (f_equal (expects_ep _ _)).
        { econstructor.
          { apply PH. }
          { eauto. (* etrans; [apply PH_EXP | apply LE__πx].  *)}
          all: eauto. }
        done. }

      rewrite bi.sep_comm.
      (* iApply bi.sep_exist_l. iExists x. rewrite bi.sep_assoc. *)
      (* iSplitL "CPS".  *)
      (* 2: { iFrame. iPureIntro. split; try done. *)
      (*      etrans; eauto. }  *)
      rewrite -own_op. 
      iApply own_update; [| by iFrame].
      apply auth_update_alloc.
      eapply local_update_proper.
      1: reflexivity.
      2: eapply gmultiset_local_update_alloc.
      f_equiv. rewrite gmultiset_disj_union_left_id. set_solver.
    Qed.

    (* TODO: ? refactor these proofs about burn_cp *)
    Lemma burn_cp_upd_impl δ ζ π deg
      (PH_MAX: exists π__max, ps_phases δ !! ζ = Some π__max /\ phase_le π π__max)
      :
      ⊢ obls_msi δ -∗ cp π deg ==∗ ∃ δ', obls_msi δ' ∗ ⌜ burns_cp δ ζ δ' π deg⌝.
    Proof using.
      iIntros "MSI CP".
      iDestruct (cp_msi_dom with "[$] [$]") as "%IN". 
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
      erewrite (f_equal (burns_cp _ _)).
      { econstructor; eauto. }
      done. 
    Qed.

    Lemma burn_cp_upd_burn ζ π__cp π deg
      (LE: phase_le π__cp π):
      ⊢ cp π__cp deg -∗ th_phase_eq ζ π -∗ 
        OU' (fun δ1 δ2 => burns_cp δ1 ζ δ2 π__cp deg) (th_phase_eq ζ π).
    Proof using.
      rewrite /OU'. iIntros "CP PH % MSI".
      (* iDestruct (th_phase_msi_ge with "[$] [$]") as %(? & ? & ?).  *)
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(MSI & PH & %PH)".
      iMod (burn_cp_upd_impl with "[$] [$]") as "R"; eauto.
      iDestruct "R" as "(%&?&?)". iModIntro. iExists _. iFrame.
    Qed.

    Lemma burn_cp_upd ζ π__cp π deg
      (LE: phase_le π__cp π):
      ⊢ cp π__cp deg -∗ th_phase_eq ζ π -∗ OU (th_phase_eq ζ π). 
    Proof using.
      iIntros "??".
      iPoseProof (burn_cp_upd_burn with "[$] [$]") as "OU'"; [done| ].
      rewrite /OU /OU'. iIntros "% MSI".
      iMod ("OU'" with "[$]") as "(%&?&%&?)". iModIntro.
      iExists _. iFrame. iPureIntro.
      red. eexists. left. eauto. 
    Qed.

    Lemma cp_mul_take ph deg n:
      cp_mul ph deg (S n) ⊣⊢ cp_mul ph deg n ∗ cp ph deg.
    Proof using. 
      rewrite /cp_mul. rewrite -own_op -auth_frag_op. 
      iApply own_proper. f_equiv.
      rewrite gmultiset_op.
      by rewrite gmultiset_scalar_mul_S_r. 
    Qed.

    (* TODO: find existing lemmas? *)
    Lemma cp_mul_split ph deg m n:
      cp_mul ph deg (m + n) ⊣⊢ cp_mul ph deg m ∗ cp_mul ph deg n.
    Proof using.
      clear H H0 H1. 
      induction n.
      { rewrite Nat.add_0_r. rewrite /cp_mul.
        rewrite gmultiset_scalar_mul_0.
        rewrite -own_op -auth_frag_op.
        rewrite gmultiset_op.
        rewrite gmultiset_disj_union_right_id. done. }
      rewrite Nat.add_succ_r. rewrite !cp_mul_take.
      rewrite IHn. iFrame. rewrite bi.sep_assoc. iFrame. set_solver.
    Qed. 
 
    (* TODO: ? refactor these proofs about fork step *)
    Lemma fork_locale_upd_impl δ ζ ζ' π R0 R'
      (FRESH: ζ' ∉ dom $ ps_phases δ)
      (DOM_EQ: dom_phases_obls δ)
      :
      ⊢ obls_msi δ -∗ th_phase_eq ζ π -∗ obls ζ R0 ==∗ 
        ∃ δ' π1 π2, obls_msi δ' ∗ th_phase_eq ζ π1 ∗ th_phase_eq ζ' π2 ∗
              obls ζ (R0 ∖ R') ∗ obls ζ' (R0 ∩ R') ∗
              ⌜ forks_locale δ ζ δ' ζ' R' ⌝ ∗
              ⌜ phase_lt π π1 /\ phase_lt π π2 ⌝. 
    Proof using.
      clear H1 H0 H.
      iIntros "MSI PH OB".
      (* iDestruct (th_phase_msi_ge_strong with "[$] [$]") as "(MSI & %π0 & (PH & %PH & %PLE))". *)
      iDestruct (th_phase_msi_eq_strong with "[$] [$]") as "(MSI & PH & %PH)".
      iDestruct (obls_msi_exact with "[$] [$]") as %OBLS. 
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
             rewrite /obls_map_repr.
             rewrite fmap_insert.
             apply alloc_singleton_local_update; [| done].
             apply not_elem_of_dom. rewrite dom_fmap dom_insert_L.
             rewrite not_elem_of_union not_elem_of_singleton. split.
             - intros ->. destruct FRESH. by apply elem_of_dom.
             - by rewrite -DOM_EQ. }
        rewrite (cmra_comm (◯ _) _).
        apply auth_update.
        rewrite fmap_insert. apply singleton_local_update_any.
        intros. replace (R0 ∖ (R0 ∩ R')) with (R0 ∖ R') by set_solver. 
        apply exclusive_local_update. done.
      - rewrite /th_phase_eq.
        (* rewrite !bi.sep_exist_l; iExists _. *)
        (* rewrite !bi.sep_assoc. iSplitL.  *)
        (* 2: { iPureIntro. reflexivity. } *)
        (* rewrite bi.sep_comm. *)
        (* rewrite !bi.sep_exist_l; iExists _. *)
        (* rewrite !bi.sep_assoc. iSplitL. *)
        (* 2: { iPureIntro. reflexivity. } *)
        (* rewrite -bi.sep_assoc bi.sep_comm. *)
        rewrite -!own_op. iApply own_update; [| by iFrame].
        etrans.
        2: {
             rewrite (cmra_comm (◯ _) _). 
             rewrite cmra_assoc.
             apply cmra_update_op; [| reflexivity].
             (* rewrite cmra_comm.  *)
             apply auth_update_alloc.
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
    Qed.

  End Resources.

End ObligationsRepr.
