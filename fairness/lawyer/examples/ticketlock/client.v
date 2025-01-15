From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import signal_map obls_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From trillium.fairness.lawyer.examples.ticketlock Require Import obls_atomic fair_lock.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


Ltac remember_goal :=
  match goal with | |- envs_entails _ ?P =>
    iAssert (P -∗ P)%I as "GOAL"; [iIntros "X"; by iApply "X"| ]
  end.

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

  Context {OBLS_AMU: @AMU_lift_MU _ _ _ oGS _ EM hGS (↑ nroot)}.

  Definition left_thread: val :=
    λ: "lk" "flag",
      (fl_acquire FL) "lk" ;;
      "flag" <- #true ;;
      (fl_release FL) "lk"
    .

    Definition right_thread_iter: val :=
      λ: "lk" "flag" "c",
        (fl_acquire FL) "lk" ;;
        "c" <- !"flag" ;;
        (fl_release FL) "lk"
    .

    Definition right_thread_rep: val :=
      rec: "right" "lk" "flag" "c" :=
        right_thread_iter "lk" "flag" "c" ;;
        if: (!"c" = #true) then #() else "right" "lk" "flag" "c"
    .

    Definition right_thread: val :=
      λ: "lk" "flag",
        let: "c" := ref #false in
        right_thread_rep "lk" "flag" "c"
    .

  Definition client_prog: val :=
    λ: <>,
      let: "lk" := fl_create FL #() in
      let: "flag" := ref #false in
      (Fork (left_thread "lk" "flag") ;;
       Fork (right_thread "lk" "flag")).

  (* TODO: move, remove duplicate *)
  Context (d0 d__r: Degree).
  Hypothesis (LThm: deg_lt (fl_d__m FLP) d__r). 
  Hypothesis (LT0m: deg_lt d0 (fl_d__m FLP)).

  Hypothesis (CR_LIM: fl_c__cr FLP ≤ LIM_STEPS).
  Definition c__cl: nat := 4.
  Hypothesis (FL_STEPS: fl_B FLP c__cl ≤ LIM_STEPS).
  (* TODO: make tactics more specific wrt. the lower bound on LIM_STEPS *)
  Hypothesis (LS_LB: 2 <= LIM_STEPS).

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
        (⌜ b = true ⌝ ∗ (∃ s__o, ⌜ oo = Some s__o /\ smap !! r = Some s__o⌝)
         ∨
         ⌜ b = false ⌝ ∗ lock_owner_frag None ∗ ∃ f, P__lock flag s__f f) ∗
        smap_repr_cl r (r + (if b then 1 else 0)) smap.

    Definition client_ns := nroot .@ "client".
    
    Definition client_inv lk flag sf: iProp Σ :=
      inv client_ns (client_inv_inner lk flag sf).

    Hypothesis (INVS_DISJ: fl_ι FLP ## client_ns).

    Definition RR__L π (r': option nat): iProp Σ :=
      match r' with
      | None => ⌜ True ⌝
      | Some r => ∃ s, ith_sig r s ∗ ep s π (fl_d__l FLP) (oGS := oGS)
      end.

    (* need to assume at least one FL level *)
    (* TODO: can we change either TAU or levels order? *)
    Context (l__fl: Level).
    Hypothesis (L__FL: l__fl ∈ fl_acq_lvls FLP).

    Lemma BMU_wait_owner τ π q O r m smap π__e i
      (PH_EXP: phase_le π__e π)
      (WAIT: r <= i):
      obls τ O (oGS := oGS) ∗ sgns_level_ge' O (fl_acq_lvls FLP) (oGS := oGS)∗
      th_phase_frag τ π q (oGS := oGS) ∗ RR__L π__e (Some i) ∗ smap_repr_cl r m smap ⊢
      BMU ∅ 1 (cp π (fl_d__l FLP) (oGS := oGS) ∗ th_phase_frag τ π q (oGS := oGS) ∗
          obls τ O (oGS := oGS) ∗ smap_repr_cl r m smap
      ) (oGS := oGS).
    Proof using LVL_ORDo L__FL ODl LEl.
      clear LS_LB CR_LIM.
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

    Lemma BMU_create_wait_owner τ π q r m smap i
      (DOM: i ∈ dom smap)
      :
      th_phase_frag τ π q (oGS := oGS) ∗ cp π (fl_d__h FLP) (oGS := oGS) ∗ smap_repr_cl r m smap ⊢
      BMU ∅ 1 (th_phase_frag τ π q (oGS := oGS) ∗ RR__L π (Some i) ∗
                smap_repr_cl r m smap) (oGS := oGS).
    Proof using LVL_ORDo L__FL ODd ODl LEl.
      iIntros "(PH & CP & [SR %SR_DOM])".
      rewrite /RR__L.
      
      iApply OU_BMU.
      iApply (OU_wand with "[]").
      2: { iApply (smap_create_ep (λ _, l__o) with "[$] [$] [$]").
           { reflexivity. }
           { done. }
           apply fl_degs_lh. }

      iIntros "X". iMod "X" as "(%s&?&?&?&?)". iApply BMU_intro.
      iFrame. iSplit; [| done]. iExists _. iFrame "#∗".
      Unshelve. apply _.
    Qed.

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

    Lemma acquire_usage τ (lk: val) flag s__f π Ob:
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗
          obls τ Ob (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
          cp π (fl_d__m FLP) (oGS := oGS) ∗
          sgns_level_gt' Ob (fl_acq_lvls FLP) (oGS := oGS)
      }}}
        (fl_acquire FL) lk @ τ
      {{{ v, RET v; ∃ s__o (f: bool), obls τ (Ob ∪ {[ s__o ]}) (oGS := oGS) ∗ 
                          th_phase_eq τ π (oGS := oGS) ∗
                          P__lock flag s__f f ∗ lock_owner_frag (Some s__o) ∗
                          ⌜ s__o ∉ Ob ⌝ ∗ fl_release_token FL
      }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & OB & PH & CPm & #OB_GT) POST".

      iApply (wp_step_fupd _ _ ⊤ _ _ with "[POST]").
      { done. }
      { iModIntro. iNext. iModIntro. iApply "POST". }

      iPoseProof (fl_acquire_spec FL _ _ τ with "[$]") as "ACQ".
      rewrite /TLAT.

      iApply ("ACQ" $! _ _ _ _ (RR__L π) with "[] [OB PH CPm]").
      { done. }
      { iFrame "#∗". }

      iApply (TAU_intro with "[]").
      4: { iSplit; [| iAccu].
           iCombine "INV" as "X". iApply "X". }
      1, 2: by apply _.
      iIntros "(#INV & _)".
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

      { iIntros (O' q') "(OB & #LVLS' & PH & %Q' & (%r' & #RR' & CASES) & %BB)".
        apply not_false_is_true in BB as ->.
        (* TODO: don't unfold BMU *)
        remember_goal.
        iDestruct "ST" as "[>(_ & (%s__o & [-> %SMAP__o])) | [>% ?]]"; [| done].
        iMod "LOCK_OW". iMod "SR".
        iApply "GOAL". iClear "GOAL".

        iAssert (BMU ∅ 1 (RR__L π (Some r) ∗ th_phase_frag τ π q' (oGS := oGS) ∗
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

      { iIntros "%q' (-> & OB & PH & %Q')".
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
        iApply BMU_intro. iFrame.
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
        
        iModIntro. iIntros "PH_CLOS RT POST !>". iApply "POST".
        do 2 iExists _. iFrame.
        iDestruct (th_phase_frag_combine' with "[$PH $PH_CLOS]") as "foo".
        { done. }
        by iFrame. }
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
                          ⌜ s__o ≠ s__f ⌝ ∗ fl_release_token FL
      }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & UNSET & OB & PH & CPm & #SF') POST".

      iApply (acquire_usage with "[-UNSET POST]").
      { iFrame "#∗". 
        (* TODO: make a lemma? *)
        rewrite /sgns_level_gt'.
        iApply big_sepS_forall. iIntros (??).
        rewrite /sgns_level_gt. rewrite big_opS_singleton.
        iExists _. iFrame "#∗". iPureIntro.
        by apply LVL_ORDf. }
      
      iNext. iIntros (?) "(%s__o & %f & OB & PH & P & LOCKED & %ADD & RT)".
      rewrite /P__lock. iDestruct "P" as "[FLAG [[-> ?] | [-> ?]]]". 
      { iApply "POST". iExists _. iFrame. iSplit; [| set_solver].
        iLeft. by iFrame. }
      by iDestruct (os_pending_excl with "[$] [$]") as "?".
    Qed.

    Lemma release_usage (lk: val) τ s__o s__f flag Ob π f Q
      (* (SIGS_NEQ: s__o ≠ s__f) *)
      (ADD: s__o ∉ Ob)
      :
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗
          obls τ (Ob ∪ {[ s__o ]}) (oGS := oGS) ∗
          th_phase_eq τ π (oGS := oGS) ∗ cp π (fl_d__m FLP) (oGS := oGS) ∗
          P__lock flag s__f f ∗ fl_release_token FL ∗ lock_owner_frag (Some s__o) ∗
          (∀ q, ⌜ Qp.le q 1 ⌝ -∗ th_phase_frag τ π q (oGS := oGS) -∗ obls τ Ob (oGS := oGS) -∗
           BMU ∅ 3 (((Qp.sub 1%Qp q) ≫= Some ∘ th_phase_frag τ π (oGS := oGS)) -∗? Q) (oGS := oGS))
          (* ∗ (P__lock flag s__f f ==∗ P__lock flag s__f f ∗ W) *)
      }}}
        (fl_release FL) lk @ τ
      {{{ v, RET v; Q }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & OB & PH & CPm & P & RT & LOCKED & FIN_BMU) POST".

      iApply (wp_step_fupd _ _ ⊤ _ _ with "[POST]").
      { done. }
      { iModIntro. iNext. iModIntro. iApply "POST". }

      iPoseProof (fl_release_spec FL lk _ τ with "[$]") as "REL".
      rewrite /TLAT.
      iApply ("REL" $! _ _ _ _ (RR__L π) with "[] [OB PH CPm]").
      { done. }
      { iFrame.
        (* TODO: make a lemma *)
        rewrite /sgns_level_gt'. set_solver. }

      iApply (TAU_intro with "[-]").
      4: { iSplit; [| iAccu].
           iCombine "INV" as "X". iApply "X". }
      1, 2: by apply _.
      iIntros "(#INV & P & LOCKED & FIN_BMU)".
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
      { iIntros (??) "(?&?&?&?&?&%)". done. }
      { iIntros "% (_ & OB & PH & %Q')".
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
        rewrite difference_union_distr_l_L difference_diag_L.
        rewrite union_empty_r_L (difference_disjoint_L Ob); [| set_solver].

        iSpecialize ("FIN_BMU" with "[//][$] [$]").
        iApply (BMU_wand with "[-FIN_BMU] [$]").
        iIntros "FIN".
        
        iIntros (st). destruct st as ((?&?)&?).
        rewrite /release_at_post. simpl.
        iIntros "(LK & (->&->&->))".
        iMod (lock_owner_update _ _ None with "[$] [$]") as "[UNL' UNL]".
        (* iMod ("WW" with "[$]") as "[P W]". *)
        iMod "CLOS'" as "_".
        iMod ("CLOS" with "[-FIN]") as "_".
        2: { iModIntro. iIntros "PH_CLOS POST". iApply "POST".
             iFrame. iModIntro.
             iApply "FIN".
             destruct (1 - q')%Qp; simpl; done. }
        iNext. rewrite /client_inv_inner. do 4 iExists _. iFrame.
        iSplitR "SR".
        2: { rewrite Nat.add_0_r -Nat.add_1_r. iFrame. done. }
        iRight. iSplit; [done| ]. iFrame.
        iExists _. iFrame. }
    Qed.

    (* TODO: move, change the original lemma*)
    Lemma th_phase_frag_combine'' τ π q p
      (LE: Qp.le p q):
      th_phase_frag τ π q (oGS := oGS) ⊣⊢ th_phase_frag τ π p (oGS := oGS)∗
        default emp ((q - p)%Qp ≫= Some ∘ th_phase_frag τ π (oGS := oGS)).
    Proof using.
      rewrite th_phase_frag_combine'; [| eauto].
      iApply bi.sep_proper; [done| ].
      destruct (Qp.sub q p); simpl; done.
    Qed.

    Lemma release_left (lk: val) τ s__o flag s__f π
      (SIGS_NEQ: s__o ≠ s__f):
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗
          flag_set ∗ obls τ {[ s__f; s__o ]} (oGS := oGS) ∗
          th_phase_eq τ π (oGS := oGS) ∗ cp π (fl_d__m FLP) (oGS := oGS) ∗
          (* P__lock flag s__f false ∗ *)
          flag ↦ #true ∗ sgn s__f l__f (Some false) (oGS := oGS) ∗
          lock_owner_frag (Some s__o) ∗ fl_release_token FL }}}
        (fl_release FL) lk @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & SET & OB & PH & CPm & FLAG & SGNf & LOCKED & RT) POST".

      iApply (release_usage with "[-POST]").
      2: iFrame "#∗".
      3: by iApply "POST".
      { set_solver. }
      iSplitL "SET".
      { iRight. by iFrame. }
      iIntros (?) "%QQ PH OB".
      iApply OU_BMU. iApply (OU_wand with "[-OB SGNf]").
      2: { iApply (OU_set_sig (oGS := oGS) with "[$] [$]"). set_solver. }
      iIntros "[SGNf OB]". rewrite difference_diag_L.
      iApply BMU_intro. simpl.

      iIntros "PH'". iFrame.
      iDestruct (th_phase_frag_combine'' with "[$PH $PH']") as "foo"; [done| ].
      iFrame.
    Qed.      

    Theorem left_thread_spec (lk: val) τ flag s__f π
      (* π__cp (PH_LE: phase_le π__cp π) *)
      :
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
      iNext. iIntros (v) "(% & OB & UNSET & PH & P & LOCKED & % & RT)".
      rewrite /P__lock. iDestruct "P" as "[FLAG [[_ SGNf]| [% ?]]]".
      2: done.

      wp_bind (Rec _ _ _)%E. pure_steps.
      wp_bind (_ <- _)%E.
      iApply sswp_MU_wp.
      { done. }
      iApply (wp_store with "[$]"). iIntros "!> FLAG".
      MU_by_burn_cp.
      pure_steps.

      iMod (os_shoot _ () with "UNSET") as "SET". 
      wp_bind (Rec _ _ _)%E. pure_steps.
      iDestruct (cp_mul_take with "CPSm") as "[CPSm CPm]".
      iApply (release_left with "[-POST]").
      { done. }
      { iFrame "#∗". }
      iNext. done.
    Qed.

    Lemma acquire_right τ (lk: val) flag s__f π:
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗
          obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
          cp π (fl_d__m FLP) (oGS := oGS)
      }}}
        (fl_acquire FL) lk @ τ
      {{{ v, RET v; ∃ s__o f, obls τ {[ s__o ]} (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
                          P__lock flag s__f f ∗ lock_owner_frag (Some s__o) ∗
                          fl_release_token FL
      }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & OB & PH & CPm) POST".

      iApply (acquire_usage with "[-POST]").
      { iFrame "#∗". 
        (* TODO: make a lemma? *)
        rewrite /sgns_level_gt'.
        iApply big_sepS_forall. iIntros (??).
        rewrite /sgns_level_gt. rewrite big_opS_empty. done. } 

      iNext. iIntros (?) "(%s__o & %f & OB & PH & P & LOCKED & %ADD & RT)".
      rewrite union_empty_l_L. iApply "POST". do 2 iExists _.
      iFrame.
    Qed.

    (* TODO: maybe generalize release_usage ? *)
    Lemma release_right (lk: val) τ s__o flag s__f π f:
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗
          ep s__f π (fl_d__m FLP) (oGS := oGS) ∗
          obls τ {[ s__o ]} (oGS := oGS) ∗
          th_phase_eq τ π (oGS := oGS) ∗ cp π (fl_d__m FLP) (oGS := oGS) ∗
          P__lock flag s__f f ∗          
          lock_owner_frag (Some s__o) ∗ fl_release_token FL }}}
        (fl_release FL) lk @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗ 
                         (⌜ f = true ⌝ ∗ flag_set ∨ ⌜ f = false ⌝ ∗ cp_mul π (fl_d__m FLP) 3 (oGS := oGS)) }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & #EPf & OB & PH & CPm & P & LOCKED & RT) POST".

      iApply (wp_step_fupd _ _ ⊤ _ _ with "[POST]").
      { done. }
      { iModIntro. iNext. iModIntro. iApply "POST". }

      iPoseProof (fl_release_spec FL lk _ τ with "[$]") as "REL".
      rewrite /TLAT.
      iApply ("REL" $! _ _ _ _ (RR__L π) with "[] [OB PH CPm]").
      { done. }
      { iFrame.
        rewrite /sgns_level_gt'. set_solver. }

      iApply (TAU_intro with "[-]").
      4: { iSplit; [| iAccu].
           iCombine "INV EPf" as "X". iApply "X". }
      1, 2: by apply _.
      iIntros "([#INV #EPf] & P & LOCKED)".
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
      { iIntros (??) "(?&?&?&?&?&%)". done. }
      { iIntros "%q' (_ & OB & PH & %Q')".
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
        rewrite difference_diag_L.

        iAssert (BMU ∅ 3 ((⌜f = true⌝ ∗ flag_set ∨ ⌜f = false⌝ ∗ cp_mul π (fl_d__m FLP) 3 (oGS := oGS)) ∗ P__lock flag s__f f ∗ obls τ ∅ (oGS := oGS) ∗ th_phase_frag τ π q' (oGS := oGS)) (oGS := oGS))%I with "[P OB PH]" as "FIN".
        { rewrite /P__lock. destruct f.
          { iDestruct "P" as "[? [[% ?] | [_ #SET]]]"; [done| ].
            iApply BMU_intro. iFrame.
            rewrite bi.or_comm. iSplitL ""; iRight; by iFrame "#∗". }
          iDestruct "P" as "[FLAG [[_ UNSET] | [% ?]]]"; [| done].
          iApply OU_BMU_rep. iApply (OU_rep_wand with "[FLAG]").
          2: { iApply (expect_sig_upd_rep with "EPf [$] [$] [] [$]").
               { done. }
               (* TODO: make a lemma*)
               rewrite /sgns_level_gt'.
               iApply big_sepS_forall. iIntros (??). set_solver. }
          iIntros "(CPSm & UNSET & OB & PH)". iFrame.
          rewrite bi.or_comm. iSplitL "CPSm"; iLeft; by iFrame "#∗". }
        
        iApply (BMU_wand with "[-FIN] [$]"). iIntros "(FIN & P & OB & PH)". 
        iIntros (st). destruct st as ((?&?)&?).
        rewrite /release_at_post. simpl.
        iIntros "(LK & (->&->&->))".
        iMod (lock_owner_update _ _ None with "[$] [$]") as "[UNL' UNL]".
        iMod "CLOS'" as "_".
        iMod ("CLOS" with "[-OB PH FIN]") as "_".
        2: { iModIntro. iIntros "PH_CLOS POST". iModIntro. iApply "POST". iFrame.
             iDestruct (th_phase_frag_combine' with "[$PH $PH_CLOS]") as "foo".
             all: done. }
        iNext. rewrite /client_inv_inner. do 4 iExists _. iFrame.
        iSplitR "SR".
        2: { rewrite Nat.add_0_r -Nat.add_1_r. iFrame. done. }
        iRight. iSplit; [done| ]. iFrame.
        by iExists _. }
    Qed.

    Lemma right_thread_iter_spec (lk: val) τ π flag s__f (c: loc):
      {{{ fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗ 
          obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
          sgn s__f l__f None (oGS := oGS) ∗
          ep s__f π (fl_d__m FLP) (oGS := oGS) ∗
          cp_mul π (fl_d__m FLP) 2 (oGS := oGS) ∗
          c ↦ #false ∗
          cp_mul π d0 20 (oGS := oGS)
      }}}
        right_thread_iter lk #flag #c @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
                    ∃ (v: bool), c ↦ #v ∗ (⌜ v = true ⌝ ∗ flag_set ∨ ⌜ v = false ⌝ ∗ cp_mul π (fl_d__m FLP) 3 (oGS := oGS))
                     }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#LOCK & #INV & OB & PH & #SGNf & #EPf & CPSm & C & CPS) POST".
      rewrite /right_thread_iter.

      pure_steps.
      wp_bind (fl_acquire _ _)%E.
      split_cps "CPSm" 1. rewrite -!cp_mul_1. 
      iApply (acquire_right with "[PH OB CPSm]").
      { by iFrame "#∗". }

      iNext. iIntros (v) "(%s__o & %f & OB & PH & P & LOCKED & RT)".
      wp_bind (Rec _ _ _)%E. pure_steps.
      wp_bind (! _)%E. rewrite /P__lock. iDestruct "P" as "[FLAG P]".
      iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> FLAG".
      MU_by_burn_cp. pure_steps.
      wp_bind (_ <- _)%E.
      iApply sswp_MU_wp; [done| ]. iApply (wp_store with "[C]"); [by iFrame| ].
      iIntros "!> C". MU_by_burn_cp. pure_steps.
      wp_bind (Rec _ _ _)%E. pure_steps.
      
      iApply (release_right with "[OB PH P LOCKED FLAG CPSm' RT]").
      { iFrame "#∗". }

      iNext. iIntros (?) "(OB & PH & FIN)".
      iApply "POST". iFrame. iExists _. iFrame.
    Qed.

    Lemma right_thread_rep_spec (lk: val) τ π (flag c: loc) s__f:
      {{{ exc_lb 30 (oGS := oGS) ∗
          fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗ 
          obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
          sgn s__f l__f None (oGS := oGS) ∗
          ep s__f π (fl_d__m FLP) (oGS := oGS) ∗
          cp_mul π (fl_d__m FLP) 2 (oGS := oGS) ∗
          c ↦ #false ∗
          cp_mul π d0 30 (oGS := oGS)
      }}}
        right_thread_rep lk #flag #c @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
                    flag_set ∗ c ↦ #true }}}.
    Proof using All.
      iIntros (Φ).
      iLöb as "IH".
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#EB & #LOCK & #INV & OB & PH & #SGNf & #EPf & CPSh & C & CPS) POST".
      rewrite /right_thread_rep.

      do 1 pure_step_cases.

      do 1 pure_step_cases.
      wp_bind (Rec _ _ _)%E.
      do 7 pure_step_cases.
      wp_bind (right_thread_iter _ _ _)%E.

      split_cps "CPS" 20.
      iApply (right_thread_iter_spec with "[-POST CPS]").
      { iFrame "#∗". }
      iIntros "!> %r (OB & PH & (%f & C & ITER))".
      wp_bind (Rec _ _ _)%E. pure_steps.      
      wp_bind (! _)%E.
      iApply sswp_MU_wp; [done| ]. iApply (wp_load with "[$]"). iIntros "!> C".
      MU_by_burn_cp. pure_steps.
      wp_bind (_ = _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step.
      { simpl. tauto. }
      MU_by_burn_cp. pure_steps.
      
      iDestruct "ITER" as "[[-> SET] | [-> CPh]]".
      - rewrite bool_decide_eq_true_2; [| tauto].
        pure_steps. iApply "POST". iFrame.
      - rewrite bool_decide_eq_false_2; [| done].
        pure_step_hl.
        split_cps "CPh" 1.
        MU_by_BMU. iApply OU_BMU.
        iApply (OU_wand with "[-PH CPh']").
        2: { rewrite -cp_mul_1. iApply (exchange_cp_upd with "[$] [$] [$]").
             1, 2: reflexivity.
             apply LT0m. }
        iIntros "[CPSm PH]". BMU_burn_cp. 
        iApply ("IH" with "[-POST]"); [| done]. iFrame "#∗".
    Qed.

    Theorem right_thread_spec (lk: val) τ π (flag: loc) s__f:
      {{{ exc_lb 30 (oGS := oGS) ∗ 
          fl_is_lock FL lk c__cl (FLG := FLG) ∗ client_inv lk flag s__f ∗ 
          obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
          sgn s__f l__f None (oGS := oGS) ∗
          cp_mul π d__r 2 (oGS := oGS) ∗
          (* cp π (fl_d__m FLP) (oGS := oGS) ∗ *)
          cp_mul π d0 40 (oGS := oGS)
      }}}
        right_thread lk #flag @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
                    flag_set }}}.
    Proof using All.
      iIntros (Φ).
      pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
      iIntros "(#EB & #LOCK & #INV & OB & PH & #SGNf & CPSm & CPS) POST".
      rewrite /right_thread. pure_steps. simpl.

      wp_bind (ref _)%E.
      iApply sswp_MU_wp; [done| ]. iApply wp_alloc. iIntros "!> %c C _".
      (* MU_by_BMU. *)
      iApply OBLS_AMU; [by rewrite nclose_nroot| ]. 
      iApply (BMU_AMU with "[-PH] [$]").
      { reflexivity. }
      iIntros "PH".
      iApply BMU_lower; [apply LS_LB| ]. iApply OU_BMU.
      split_cps "CPSm" 1. rewrite -!cp_mul_1.
      iApply (OU_wand with "[-CPSm PH]").
      2: { iApply (@create_ep_upd with "[$] [$] [$]").
           { apply LThm. } (* TODO: rename that hypothesis *)
           reflexivity. }
      iIntros "(EPf & _ & PH)". iApply OU_BMU.
      iApply (OU_wand with "[-CPSm' PH]").
      2: { iApply (exchange_cp_upd with "[$] [$] [$]").
           1, 2: reflexivity.
           apply LThm. }
      iIntros "[CPSh PH]".
      
      BMU_burn_cp.

      do 1 pure_step_cases.

      wp_bind (Rec _ _ _)%E.
      do 1 pure_step_cases. iApply wp_value.
      do 1 pure_step_cases. 

      split_cps "CPS" 10. simpl.
      iApply (right_thread_rep_spec with "[-POST]").
      2: { iNext. iIntros (?) "(?&?&?&?)". iApply "POST". iFrame. }
      iFrame "#∗".
      split_cps "CPSh" 2. iFrame.
      iDestruct (cp_mul_split with "[CPS CPS']") as "CPS"; [by iFrame| ]. 
      split_cps "CPS" 30. iFrame.
    Qed.

  End AfterInit.

  (* TODO: move *)
  Ltac burn_cp_after_BMU :=
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]";
    iSplitR "CP";
    [| do 2 iExists _; iFrame; iPureIntro; done].

  (* TODO: remove another one *)
  Hypothesis (LS_LB': 3 <= LIM_STEPS).

  Context {OBLS_AMU__f: forall τ, @AMU_lift_MU__f _ _ _ τ oGS _ EM _ ⊤}.
  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ (oGS := oGS) -∗ fork_post τ v}. 

  (* TODO: move, remove duplicates *)
  Lemma exc_lb_le n m
    (LE: n <= m):
    exc_lb m (oGS := oGS) ⊢ exc_lb n (oGS := oGS).
  Proof using.
    rewrite /exc_lb. erewrite mono_nat_lb_op_le_l; eauto.
    rewrite own_op. by iIntros "[??]". 
  Qed.

  Theorem client_spec `{ClientPreG Σ, fl_GpreS FLP Σ} τ π:
    {{{ exc_lb 70 (oGS := oGS) ∗
        obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
        cp_mul π d__r 4 (oGS := oGS) }}}
      client_prog #() @ τ
    {{{ v, RET v; obls τ ∅ (oGS := oGS) }}}.
  Proof using.
    iIntros (Φ) "(#EB & OB & PH & CPSr) POST". rewrite /client_prog.
    pure_step_hl. 
    MU_by_BMU. iApply OU_BMU.
    split_cps "CPSr" 1. rewrite -cp_mul_1. iApply (OU_wand with "[-CPSr' PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         etrans; [apply LT0m | apply LThm]. }
    iIntros "[CPS PH]".    
    split_cps "CPSr" 1. rewrite -cp_mul_1.
    iApply OU_BMU. iApply (OU_wand with "[-CPSr' PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         apply LThm. }
    iIntros "[CPSm PH]".
    iApply OU_BMU. iApply (OU_wand with "[-OB]").
    2: { iApply (OU_create_sig _ _ l__f with "OB"). }
    iIntros "(%s__f & SGNf & OB & _)". rewrite union_empty_l_L.
    iDestruct (sgn_get_ex with "[$]") as "[SGNf #SGNf']".
    BMU_burn_cp.

    wp_bind (fl_create FL _)%E.
    unshelve iApply (fl_create_spec FL with "[//] [$]").
    { eauto. }
    { exact c__cl. }
    iIntros "!> %lk (%FLG & LK & LOCK)".
    pose proof (fl_is_lock_pers FL lk c__cl (FLG := FLG)) as PERS. (* TODO: why Existing Instance doesn't work? *)
    iDestruct "LOCK" as "#LOCK".

    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (ref _)%E. iApply sswp_MU_wp_fupd; [done| ]. iModIntro. 
    iApply wp_alloc. iIntros "!> %flag FLAG _".
    iNext. MU_by_BMU.
    
    iMod (own_alloc (● Excl' None ⋅ ◯ _: excl_authUR (optionUR SignalId))) as (?) "[OW_A OW_F]".
    { apply auth_both_valid_2; [| reflexivity]. done. }
    iMod (own_alloc (@Pending unitO)) as (?) "UNSET"; [done| ].
    iPoseProof (init_smap_repr (fun _ => l__o) _ _ (flip Nat.ltb 0) ∅ with "OB") as "SR".
    rewrite size_empty. simpl. iApply (BMU_weaken ∅ _ 0 with "[-SR] [$]"); [lia| done| ..].
    iIntros "(%smap & %SMG & SR & %DOM__SM & OB)". burn_cp_after_BMU.
    apply dom_empty_inv_L in DOM__SM as ->. rewrite map_img_empty_L union_empty_r_L.

    set (CG := {| cl_γ__ow := γ; cl_γ__os := γ0 |}).
    iMod (inv_alloc client_ns _ (client_inv_inner lk flag s__f) with "[LK FLAG OW_A OW_F SR SGNf]") as "#INV".
    { iNext. rewrite /client_inv_inner.
      do 4 iExists _. iFrame.
      iSplit.
      2: { simpl. iPureIntro. set_solver. }
      iRight. iSplit; [done| ].
      iFrame. iExists _. iFrame. iLeft. by iFrame. }
    iModIntro.

    pure_steps. wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (Fork _)%E. 
    split_cps "CPS" 20. split_cps "CPSm" 2.
    iApply sswp_MUf_wp. iIntros "%τ' !>".
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]". 
    iApply (MU__f_wand with "[-CP PH OB]").
    2: { iApply OBLS_AMU__f; [done| ].
         iApply (BMU_AMU__f with "[-PH] [$]"); [reflexivity| ..].
         iIntros "?". iApply BMU_intro. iFrame.
         iSplitR; [iAccu| ]. 
         do 2 iExists _. by iFrame. }
    iIntros "(_ & (%π1 & %π2 & PH1 & OB1 & PH2 & OB2 & [%PH_LT1 %PH_LT2]))".

    iSplitL "CPS' CPSm' OB2 PH2 UNSET".
    { iApply (left_thread_spec with "[-]").
      { admit. }
      { admit. }
      2: { iIntros "!> % [OB PH]". by iApply NO_OBS_POST. }
      iFrame "#∗". iSplitL "OB2".
      { iApply obls_proper; [| done]. symmetry. apply intersection_idemp. }
      replace π2 with π by admit. iFrame. }

    iRename "PH1" into "PH". rewrite difference_diag_L.
    (* Unset Printing Notations. *)
    apply strict_include in PH_LT1. 
    wp_bind (Rec _ _ _)%E. pure_steps.

    iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
    iApply sswp_MUf_wp. iIntros "%τ2 !>". 
    iApply (MU__f_wand with "[-CP PH OB1]").
    2: { iApply OBLS_AMU__f; [done| ].
         iApply (BMU_AMU__f with "[-PH] [$]"); [reflexivity| ..].
         iIntros "?". iApply BMU_intro. iFrame.
         iSplitR; [iAccu| ]. 
         do 2 iExists _. by iFrame. }
    iIntros "(_ & (%π11 & %π12 & PH1 & OB1 & PH2 & OB2 & [%PH_LT11 %PH_LT12]))".

    iSplitR "POST OB1".
    2: { iApply "POST". iApply obls_proper; [| done].
         symmetry. apply difference_diag. }

    iApply (right_thread_spec with "[-PH1]").
    1, 2: admit.
    2: { iIntros "!> % [OB PH]". by iApply NO_OBS_POST. }
    rewrite intersection_idemp_L. iFrame "#∗".
    replace π12 with π by admit. iFrame.
    iApply (exc_lb_le with "[$]"). lia.

  Admitted. 

    
End MotivatingClient.

