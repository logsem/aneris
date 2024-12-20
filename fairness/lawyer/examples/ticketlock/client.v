(* TODO: move *)
Section OneShot.
  Context {V: ofe}.
  
  Definition one_shotR := csumR (exclR unitO) (agreeR V).
  Definition Pending : one_shotR := Cinl (Excl ()).
  Definition Shot (v : V) : one_shotR := Cinr (to_agree v).
  
  Class one_shotG Σ := { one_shot_inG : inG Σ one_shotR }.
  Global Existing Instance one_shot_inG.
  
  Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
  Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
  Proof. solve_inG. Qed.

  Section Lemmas.
    Context `{one_shotG}. 
    
    Lemma os_shoot γ v: ⊢ own γ Pending ==∗ own γ $ Shot v.
    Proof using.
      iIntros "P".
      iApply own_update; [| by iFrame].
      by apply cmra_update_exclusive.
    Qed. 

    Lemma os_pending_excl `{OfeDiscrete V} γ (os': one_shotR):
      ⊢ own γ Pending -∗ own γ os' -∗ False.
    Proof using.
      rewrite bi.wand_curry -own_op.
      iIntros "P". eauto 10.
      iDestruct (own_valid with "P") as "%X".
      by apply exclusive_l in X; [| apply _].   
    Qed.

  End Lemmas.

End OneShot.


Class ClientPreG Σ := {
    cl_ow_sig_pre :> inG Σ (excl_authUR (optionUR SignalId));
    (* eofin_sigs :> inG Σ (authUR (gmapUR nat (agreeR SignalId))); *)
    cl_one_shot_pre :> @one_shotG unitR Σ;
    cl_sig_map_pre :> SigMapPreG Σ;
}.

Class ClientG Σ := {
    cl_PreG :> ClientPreG Σ;
    cl_γ__ow: gname;
    cl_γ__os: gname;
    cl_sig_map :> SigMapG Σ;
}.

Section MotivatingClient.
  Context `{ODd: OfeDiscrete DegO} `{ODl: OfeDiscrete LevelO}.
  Context `{LEl: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  
  Let OAM := ObligationsAM.
  Let ASEM := ObligationsASEM.

  Context `{EM: ExecutionModel heap_lang M}. 

  Context {Σ: gFunctors}.
  (* Context {invs_inΣ: invGS_gen HasNoLc Σ}. *)
  Context {oGS: @asem_GS _ _ ASEM Σ}.
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

  Context {FLP: FairLockPre} (FL: FairLock (FLP := FLP) (oGS := oGS)).

  Context (l__o l__f: Level).
  Hypothesis
    (LVL_ORDo: forall l, l ∈ fl_acq_lvls FLP -> lvl_lt l__o l)
    (LVL_ORDf: forall l, l ∈ fl_acq_lvls FLP -> lvl_lt l l__f)
    (* in case fl_lvls is empty *)
    (LVL_ORDof: lvl_lt l__o l__f).


  Section AfterInit.
    Context {CL: ClientG Σ}.
    Context {FLG: fl_GS FLP Σ}. 

    Existing Instance cl_sig_map. 
    
    Definition flag_unset := own cl_γ__os Pending.
    Definition flag_set := own cl_γ__os (Shot ()).

    Definition lock_owner_auth (oo: option SignalId) :=
      own cl_γ__ow (● Excl' oo). 
    Definition lock_owner_frag (oo: option SignalId) :=
      own cl_γ__ow (◯ Excl' oo). 
    
    Definition P__lock flag s__f (b: bool): iProp Σ :=
      flag ↦ #b ∗ (⌜ b = false ⌝ ∗ sgn s__f l__f (Some false) (oGS := oGS) ∨
                    ⌜ b = true ⌝ ∗ flag_set).

    Let s__def: SignalId := 0.

    Definition smap_repr_cl r K smap: iProp Σ :=
      smap_repr (fun _ => l__o) (flip Nat.ltb r) (oGS := oGS) smap ∗
      ⌜ dom smap = set_seq 0 K ⌝.
    
    Definition client_inv_inner lk flag s__f: iProp Σ :=
      ∃ r b oo smap, fl_LK FLP (lk, r, b) (FLG := FLG) ∗ lock_owner_auth oo ∗
        (⌜ b = true ⌝ ∗ (∃ s__o, ⌜ oo = Some s__o /\ smap !! r = Some s__o⌝
         (* ∗ sgn s__o l__o (Some false) (oGS := oGS) *)
                 )
         ∨
         ⌜ b = false ⌝ ∗ lock_owner_frag None ∗ ∃ f, P__lock flag s__f f) ∗
        smap_repr_cl r (r + (if b then 1 else 0)) smap.

    Definition client_ns := nroot .@ "client". 
    
    Definition client_inv lk flag sf: iProp Σ :=
      inv client_ns (client_inv_inner lk flag sf).

    Definition left_thread: val :=
      λ: "lk" "flag",
          (fl_acquire FL) "lk" ;;
           "flag" <- #true ;;
           (fl_release FL) "lk"
    .

    Definition c__cl: nat := 4.

    Context (d2 d1 d0: Degree).    

    Hypothesis (FL_STEPS: fl_B FLP c__cl ≤ LIM_STEPS).
    Hypothesis (INVS_DISJ: fl_ι FLP ## client_ns). 

    Definition RR__L π (r': option nat): iProp Σ := 
      match r' with
      | None => ⌜ True ⌝
      | Some r => ∃ s (* π__e *),
      ith_sig r s ∗ ep s π (fl_d__l FLP) (oGS := oGS)
        (* ∗ ⌜ phase_le π__e π ⌝ *)
      end.

    (* Lemma RR_higher_phase π1 π2 r *)
    (*   (LE: phase_le π1 π2): *)
    (*   RR__L π1 (Some r) ⊢ RR__L π2 (Some r). *)
    (* Proof using. *)
    (*   iIntros "(%&%&?&?&%)". *)
    (*   do 2 iExists _. iSplit; [by iFrame| ].  *)
    (*   iFrame "#∗". iPureIntro. etrans; eauto. *)
    (* Qed. *)

    (* need to assume at least one FL level *)
    (* TODO: can we change either TAU or levels order? *)
    Context (l__fl: Level).
    Hypothesis (L__FL: l__fl ∈ fl_acq_lvls FLP). 

    Lemma BMU_wait_owner τ π O r m smap π__e i
      (PH_EXP: phase_le π__e π)
      (WAIT: r <= i):
      obls τ O (oGS := oGS) ∗ sgns_level_ge' O (fl_acq_lvls FLP) (oGS := oGS)∗
      th_phase_eq τ π (oGS := oGS) ∗ RR__L π__e (Some i) ∗ smap_repr_cl r m smap ⊢ 
      BMU ∅ 1 (cp π (fl_d__l FLP) (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗ 
          obls τ O (oGS := oGS) ∗ smap_repr_cl r m smap
      ) (oGS := oGS).
    Proof using LVL_ORDo L__FL ODl LEl.
      clear FL_STEPS.
      
      iIntros "(OBLS & #LVLS & PH & #RR & [SR %SR_DOM])".
      rewrite /RR__L. iDestruct "RR" as (s) "(#ITH & #EP)".  (* & %PH__e *)
      iApply OU_BMU. 
      iApply (OU_wand with "[]").
      2: { rewrite /smap_repr_cl. 
           iApply (ith_sig_expect (λ _, l__o) with "[$] [$] [$] [$] [$] []").
           { done. }
           { simpl. apply Nat.ltb_nlt. lia. } 
           rewrite /sgns_level_ge' /sgns_level_gt /sgns_level_ge.
           iDestruct (big_sepS_forall with "LVLS") as "LVLS'".
           iSpecialize ("LVLS'" $! l__fl with "[//]").
           iApply big_sepS_impl; [by iFrame| ].
           iModIntro. iIntros (??) "(%l & ? & %LE)".
           iExists _. iFrame. iPureIntro.
           eapply strict_transitive_l; [| apply LE]. by apply LVL_ORDo. }
      iIntros "(?&?&?&?)". iApply BMU_intro. 
      iFrame. iPureIntro. repeat split; try done.
    Qed.

    Hypothesis (DEG_LH: deg_lt (fl_d__l FLP) (fl_d__h FLP)). 

    Lemma BMU_create_wait_owner τ π r m smap i
      (DOM: i ∈ dom smap)
      :
      th_phase_eq τ π (oGS := oGS) ∗ cp π (fl_d__h FLP) (oGS := oGS) ∗ smap_repr_cl r m smap ⊢ 
      BMU ∅ 1 (th_phase_eq τ π (oGS := oGS) ∗ RR__L π (Some i) ∗ 
                smap_repr_cl r m smap) (oGS := oGS).
    Proof using LVL_ORDo L__FL DEG_LH ODd ODl LEl.
      iIntros "(PH & CP & [SR %SR_DOM])".
      rewrite /RR__L.
      
      iApply OU_BMU. 
      iApply (OU_wand with "[]").
      2: { iApply (smap_create_ep (λ _, l__o) with "[$] [$] [$]").
           { reflexivity. }
           { done. }
           apply DEG_LH. }

      iIntros "X". iMod "X" as "(%s&?&?&?&?)". iApply BMU_intro.
      iFrame. iSplit; [| done]. iExists _. iFrame "#∗".
      Unshelve. apply _. 
    Qed.

    (* Lemma lock_owner_alloc oo: *)
    (*   ⊢ |==> ∃ γ, lock_owner_auth γ oo ∗ lock_owner_frag γ oo. *)
    (* Proof using. *)
    (*   iMod (own_alloc (●E n ⋅  ◯E n)) as (?) "[A F]". *)
    (*   { by apply auth_both_valid_2. } *)
    (*   iExists _. by iFrame. *)
    (* Qed.        *)

    Lemma lock_owner_agree n1 n2:
      lock_owner_auth n1-∗ lock_owner_frag n2 -∗ ⌜ n1 = n2 ⌝. 
    Proof using.
      rewrite /lock_owner_frag /lock_owner_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".      
      iDestruct (own_valid with "H") as "%Hval".
      iPureIntro. apply excl_auth_agree_L in Hval. set_solver. 
    Qed.

    Lemma lock_owner_update n1 n2 n':
      lock_owner_auth n1 -∗ lock_owner_frag n2 ==∗
      lock_owner_auth n' ∗ lock_owner_frag n'. 
    Proof using.
      rewrite /lock_owner_frag /lock_owner_auth.
      iIntros "HA HB". iCombine "HB HA" as "H".
      rewrite -!own_op. iApply own_update; [| by iFrame].
      apply excl_auth_update.
    Qed.

    Lemma acquire_left τ (lk: val) flag s__f π:
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗ flag_unset ∗
          obls τ {[ s__f ]} (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
          cp π (fl_d__m FLP) (oGS := oGS) ∗
          sgn s__f l__f None (oGS := oGS)
      }}}
        (fl_acquire FL) lk @ τ
      {{{ v, RET v; ∃ s__o, obls τ {[ s__f; s__o ]} (oGS := oGS) ∗ flag_unset ∗
                          th_phase_eq τ π (oGS := oGS) ∗ 
                          P__lock flag s__f false ∗ lock_owner_frag (Some s__o) ∗
                          ⌜ s__o ≠ s__f ⌝
      }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & UNSET & OB & PH & CPm & #SF') POST".

      iApply (wp_step_fupd _ _ ⊤ _ _ with "[POST]").
      { done. }
      { iModIntro. iNext. iModIntro. iApply "POST". }

      iPoseProof (fl_acquire_spec FL _ _ τ with "[$]") as "ACQ".
      rewrite /TLAT.

      iApply ("ACQ" $! _ _ _ (RR__L π) with "[] [OB PH CPm]").
      { done. }
      { iFrame.
        rewrite /sgns_level_gt'.
        iApply big_sepS_forall. iIntros (??).
        rewrite /sgns_level_gt. rewrite big_opS_singleton.
        iExists _. iFrame "#∗". iPureIntro.
        by apply LVL_ORDf. }

      iApply (TAU_intro with "[UNSET]").
      4: { iSplit; [| iApply "UNSET"].
           iCombine "INV SF'" as "X". iApply "X". }
      1, 2: by apply _.
      iIntros "((#INV & #SF') & UNSET)".
      rewrite /TAU_acc.
      iInv "INV" as "inv" "CLOS".
      iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'".
      rewrite {1}/client_inv_inner.
      iDestruct "inv" as (r b oo smap) "(LK & LOCK_OW & ST & SR)".
      iExists (lk, r, b).
      iFrame "LK". iSplit; [done| ]. 
      
      iSplit; [| iSplit].
      
      3: { iIntros "[LK %]".
           iMod "CLOS'" as "_". iFrame.
           iMod ("CLOS" with "[-]") as "_".
           2: { by iFrame "#∗". } 
           iNext. rewrite /client_inv_inner. do 4 iExists _. iFrame. }

      { iIntros (O') "(OB & #LVLS' & PH & (%r' & #RR' & CASES) & %BB)".
        apply not_false_is_true in BB as ->.
        (* TODO: don't unfold BMU *)
        remember_goal.
        iDestruct "ST" as "[>(_ & (%s__o & [-> %SMAP__o])) | [>% ?]]"; [| done].
        iMod "LOCK_OW". iMod "SR".
        iApply "GOAL". iClear "GOAL".

        iAssert (BMU ∅ 1 (RR__L π (Some r) ∗ th_phase_eq τ π (oGS := oGS) ∗
                           smap_repr_cl r (r + 1) smap))%I with "[CASES PH SR]" as "EXP".
        { iDestruct "CASES" as "[-> | RR]".
          { iApply BMU_intro. iFrame "#∗". }
          iApply (BMU_wand with "[]").
          2: { iApply BMU_create_wait_owner; [..| iFrame "#∗"].
               eapply elem_of_dom; eauto. }
          iIntros "(?&?&?)". iFrame. }

        iApply (BMU_split _ _ 1 _). iApply (BMU_wand with "[-EXP] EXP").
        iIntros "(#RR & PH & SR)". 
        iApply (BMU_lower _ 1); [unfold c__cl; lia| ].
        iApply (BMU_wand with "[-OB PH SR]").
        2: { iApply BMU_wait_owner; [..| iFrame "#∗"]. all: done. }
        iIntros "(CP & PH & OB & SR)".
        iFrame "#∗". iIntros "[LK %]".
        iMod "CLOS'" as "_".
        iMod ("CLOS" with "[-]") as "_"; [| done].
        iNext. rewrite /client_inv_inner. do 4 iExists _. iFrame.
        iLeft. iSplit; [done| ]. iExists _. iFrame "#∗". done. }

      { iIntros "([%r' RR'] & -> & OB & PH)".
        remember_goal.
        iDestruct "ST" as "[[>% ?] | X]"; [done| ].
        iDestruct "X" as "(_& >LOCKED & >[%f P])".
        iMod "LOCK_OW". iMod "SR" as "[SR %DOM]".
        iApply "GOAL". iClear "GOAL".

        rewrite Nat.add_0_r in DOM.
        iApply (BMU_split _ _ 1).
        iApply (BMU_wand with "[-OB SR]").
        2: { iApply (BMU_smap_extend (λ _, l__o) _ r with "[$] [$]").
             { intros. reflexivity. }
             { simpl. apply Nat.ltb_irrefl. }
             rewrite DOM. intros ?%elem_of_set_seq. lia. 
             Unshelve. apply _. }
        iIntros "X". iMod "X" as "(%s' & SR & #SIGr & OB & %FRESH')".
        iApply BMU_intro.
        iIntros ([[??]?]) "[LK (%X & % & %)]". 
        simpl in *. inversion X. subst.
        iMod "CLOS'" as "_".
        Unshelve.
        iMod (lock_owner_update _ _ (Some s') with "[$] [$]") as "[LOCK_OW LOCKED]".
        iMod ("CLOS" with "[LK SR LOCK_OW]").
        { iNext. rewrite /client_inv_inner.
          do 4 iExists _. iFrame. iSplit.
          2: { iPureIntro. rewrite dom_insert_L.
               rewrite set_seq_add_L. set_solver. }
          iLeft. iSplit; [done| ].
          rewrite lookup_insert. eauto. }
        
        iModIntro. iIntros "POST !>". iApply "POST". 
        rewrite {1}/P__lock. iDestruct "P" as "[F [[-> ?] | [-> SET]]]".
        2: { by iDestruct (os_pending_excl with "[$] [$]") as %?. }
        iExists _. iFrame. iSplit; [| set_solver].
        iLeft. iFrame. done. }
    Qed.


    Lemma release_left (lk: val) τ s__o flag s__f π
      (SIGS_NEQ: s__o ≠ s__f):
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗
          flag_unset ∗ obls τ {[ s__f; s__o ]} (oGS := oGS) ∗ 
          th_phase_eq τ π (oGS := oGS) ∗ cp π (fl_d__m FLP) (oGS := oGS) ∗
          (* P__lock flag s__f false ∗ *)
          flag ↦ #true ∗ sgn s__f l__f (Some false) (oGS := oGS) ∗
          
          lock_owner_frag (Some s__o) }}}
        (fl_release FL) lk @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & UNSET & OB & PH & CPm & FLAG & SGNf & LOCKED) POST".

      iApply (wp_step_fupd _ _ ⊤ _ _ with "[POST]").
      { done. }
      { iModIntro. iNext. iModIntro. iApply "POST". }

      iPoseProof (fl_release_spec FL lk _ τ with "[$]") as "REL".
      rewrite /TLAT.
      iApply ("REL" $! _ _ _ (RR__L π) with "[] [OB PH CPm]").
      { done. }
      { iFrame.
        rewrite /sgns_level_gt'. set_solver. }

      iApply (TAU_intro with "[-]").
      4: { iSplit; [| iAccu]. 
           iCombine "INV" as "X". iApply "X". }
      1, 2: by apply _.
      iIntros "(#INV & UNSET & FLAG & SGNf & LOCKED)".
      iInv "INV" as "inv" "CLOS".
      iDestruct "inv" as (r b oo smap) "(LK & >LOCK_OW & >ST & >SR)".

      iDestruct "ST" as "[[-> ST]| [? [UNLOCKED ?]]]".
      2: { iExFalso. iCombine "LOCKED UNLOCKED" as "X".
           iDestruct (own_valid with "X") as %V%auth_frag_valid_1.
           rewrite Some_valid in V. done. }

      iDestruct "ST" as "[%so_ [-> %SM__o]]".
      iExists _.
      iFrame "LK".
      iDestruct (lock_owner_agree with "[$] [$]") as "%EQ".
      inversion EQ. subst.       

      iDestruct "SR" as "[SR %DOM]".
      iMod (ith_sig_retrieve with "[//] SR") as "[#RTH SR]".
      
      iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'".
      iSplit; [done| ].      
      iSplit; [| iSplit].
      3: { iIntros "[LK %]".
           iMod "CLOS'" as "_". iFrame.
           iMod ("CLOS" with "[-]") as "_".
           2: { by iFrame "#∗". } 
           iNext. rewrite /client_inv_inner. do 4 iExists _. iFrame.
           iSplit; [| done]. 
           iLeft. iSplit; [done| ]. eauto. }
      { iIntros (?) "(?&?&?&?&%)". done. }
      { iIntros "([%r__p RR'] & _ & OB & PH)".
        iApply OU_BMU. 
        iApply (OU_wand with "[-OB SR]").
        2: { iApply (smap_set_sig (λ _, l__o) with "[$] [$] [$]").
             { Unshelve. 2: exact (flip Nat.ltb (S r)).
               simpl. apply Nat.ltb_lt. lia. }
             { set_solver. }
             (* TODO: extract lemma, use in eo_fin *)
             intros. simpl.
             rewrite DOM in H0. apply elem_of_set_seq in H0.
             destruct (Nat.lt_trichotomy j (S r)) as [LT | [-> | LT]]; revgoals.
             1,2: rewrite !(proj2 (Nat.ltb_ge _ _)); lia.
             rewrite !(proj2 (Nat.ltb_lt _ _)); lia. }
        iIntros "[SR OB]".
        replace ({[s__f; s__o]} ∖ {[s__o]}) with ({[s__f]}: gset _) by set_solver.
        
        iApply OU_BMU.
        iApply (OU_wand with "[-OB SGNf]").
        2: { iApply (OU_set_sig (oGS := oGS) with "[$] [$]"). set_solver. }
        iIntros "[SGNf OB]". rewrite difference_diag_L.

        iApply BMU_intro.
        iIntros (st). destruct st as ((?&?)&?). 
        rewrite /release_at_post. simpl.
        iIntros "(LK & (->&->&->))".
        iMod (lock_owner_update _ _ None with "[$] [$]") as "[UNL' UNL]".
        iMod (os_shoot _ () with "[$]") as "#SET".
        iMod "CLOS'" as "_".
        iMod ("CLOS" with "[-OB PH]") as "_".
        2: { iModIntro. iIntros "POST". iModIntro. iApply "POST". iFrame. }
        iNext. rewrite /client_inv_inner. do 4 iExists _. iFrame.
        iSplitR "SR".
        2: { rewrite Nat.add_0_r -Nat.add_1_r. iFrame. done. }
        iRight. iSplit; [done| ]. iFrame.
        iExists _. iFrame. iRight. iSplit; [done| ]. iFrame "#∗". }
    Qed.

    (* TODO: move, remove duplicates *)
    Ltac BMU_burn_cp :=
      iApply BMU_intro;
      iDestruct (cp_mul_take with "CPS") as "[CPS CP]";
      iSplitR "CP";
      [| do 2 iExists _; iFrame; iPureIntro; done].   
    
    Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS _ EM hGS (↑ nroot)}.
    
    Ltac MU_by_BMU :=
      iApply OBLS_AMU; [by rewrite nclose_nroot| ];
      iApply (BMU_AMU with "[-PH] [$]"); [by eauto| ]; iIntros "PH". 
    
    Ltac MU_by_burn_cp := MU_by_BMU; BMU_burn_cp.
    
    Ltac pure_step_hl := 
      iApply sswp_MU_wp; [done| ];
      iApply sswp_pure_step; [done| ]; simpl;
      iNext.
    
    Ltac pure_step := pure_step_hl; MU_by_burn_cp.   
    Ltac pure_step_cases := pure_step || (iApply wp_value; []) || wp_bind (RecV _ _ _ _)%V.
    Ltac pure_steps := repeat (pure_step_cases; []).

    Theorem left_thread_spec (lk: val) τ flag s__f π:
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗ flag_unset ∗
          obls τ {[ s__f ]} (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
          cp_mul π (fl_d__m FLP) 2 (oGS := oGS) ∗
          sgn s__f l__f None (oGS := oGS) ∗

          cp_mul π d0 20 (oGS := oGS)
      }}}
        left_thread lk #flag @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & ?&?&PH&CPSm&? & CPS) POST".
      rewrite /left_thread.
      pure_steps. simpl.

      wp_bind (fl_acquire FL lk).
      iDestruct (cp_mul_take with "CPSm") as "[CPSm CPm]". 
      iApply (acquire_left with "[-CPSm CPS POST]").
      { iFrame "#∗". }
      iNext. iIntros (v) "(% & OB & UNSET & PH & P & LOCKED & %)".
      rewrite /P__lock. iDestruct "P" as "[FLAG [[_ SGNf]| [% ?]]]".
      2: done.

      wp_bind (Rec _ _ _)%E. pure_steps.
      wp_bind (_ <- _)%E.
      iApply sswp_MU_wp.
      { done. }
      iApply (wp_store with "[$]"). iIntros "!> FLAG".
      MU_by_burn_cp.
      pure_steps.

      wp_bind (Rec _ _ _)%E. pure_steps.
      iDestruct (cp_mul_take with "CPSm") as "[CPSm CPm]".
      iApply (release_left with "[-POST]").
      { done. }
      { iFrame "#∗". }
      iNext. done. 
    Qed.

  End AfterInit.
    
End MotivatingClient.

