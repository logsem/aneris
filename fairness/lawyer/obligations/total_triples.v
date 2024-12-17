From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em.
From iris.proofmode Require Import tactics.


Section TotalTriples.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  
  Context {Σ: gFunctors}.
  Context {invs_inΣ: invGS_gen HasNoLc Σ}.

  (* Context {Inhabited Locale}. *)
  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}.

  (* TODO: move *)
  Definition sgns_level_ge (R: gset SignalId) lm: iProp Σ :=
    [∗ set] s ∈ R, (∃ l, sgn s l None (oGS := oGS) ∗ ⌜ lvl_le lm l ⌝). 

  (* TODO: move *)
  Definition sgns_level_ge' (R: gset SignalId) (L: gset Level): iProp Σ := 
    [∗ set] l ∈ L, sgns_level_ge R l.
  (* TODO: move *)
  Definition sgns_level_gt' (R: gset SignalId) (L: gset Level): iProp Σ := 
    [∗ set] l ∈ L, sgns_level_gt R l (oGS := oGS).

  Let Locale := locale heap_lang. 


  Section AtomicTriples. 
    Context
      (τ: Locale)(* TODO: should it be fixed? *)
      {ST: Type}
      (P: ST -> iProp Σ) (Q: ST -> ST -> iProp Σ) (* second ST is the previous state *)
      (L: gset Level) (* TODO: only finite sets? *)
      {RO: Type}
      (round: ST -> RO) (* TODO: can we get away with ST only? *)
      (TGT: ST -> Prop) (* `{forall x, Decision (TGT x)} *)
      (d__h d__l d__m: Degree)
      (c: nat) (B: nat -> nat)
      (ε__m: coPset)
    .

    Section AtomicUpdates.
      Context
        (ε: coPset)
        (π: Phase)
        (Φ: val -> iProp Σ)
        (O: gset SignalId)
        (RR: option RO -> iProp Σ)
      .

      Definition TAU1: iProp Σ.
      Admitted.

      Definition TAU1_acc (V: iProp Σ): iProp Σ :=
        |={ε, ∅}=> ∃ x, ▷ P x ∗ (
                           let abort := P x ={∅, ε}=∗ V in
                           ((∃ r__p, RR r__p) ∗ ⌜ TGT x ⌝ ∗ obls τ O (oGS := oGS) -∗
                              BMU ∅ c (oGS := oGS) (∀ y, ▷ Q y x ={∅, ε}=∗ Φ #())) ∧
                             abort
                         ).
      
      Lemma TAU1_elim:
        TAU1 ⊣⊢ TAU1_acc TAU1.
      Proof using. Admitted.

      Definition TAU2: iProp Σ.
      Admitted.

      Lemma BMU_merge_equiv (PP QQ: bool -> iProp Σ) E n:
        let bmu := BMU (oGS := oGS) in
        (PP true -∗ bmu E n (QQ true)) ∧ (PP false -∗ bmu E n (QQ false)) ⊣⊢ (∀ b, PP b -∗ bmu E n (QQ b)).
      Proof using.
        iSplit. 
        - iIntros "B %b P".
          destruct b. 
          + iDestruct (bi.and_elim_l with "B") as "B". iSpecialize ("B" with "P").
            iApply (BMU_wand with "[] [$]"). iIntros "?". iFrame.
          + iDestruct (bi.and_elim_r with "B") as "B". iSpecialize ("B" with "P").
            iApply (BMU_wand with "[] [$]"). iIntros "?". iFrame.
        - iIntros "B". iSplit; iApply "B".
      Qed. 

      (* TODO: unify with TAU1_acc *)
      Definition TAU2_acc (V: iProp Σ): iProp Σ :=
        |={ε, ∅}=> ∃ x, ▷ P x ∗ (
              let abort := ▷ P x ={∅, ε}=∗ V in
              (let r := round x in
               ∀ O', obls τ O' (oGS := oGS) ∗ sgns_level_ge' O' L ∗
                        th_phase_eq τ π (oGS := oGS) ∗
                      (∃ r__p, RR r__p ∗ (⌜ r__p = Some r ⌝ ∨ cp π d__h (oGS := oGS))) ∗
                      ⌜ ¬ TGT x ⌝ -∗
                      BMU ∅ c (oGS := oGS) (
                        RR (Some r) ∗ cp π d__l (oGS := oGS) ∗
                        th_phase_eq τ π (oGS := oGS) ∗
                        obls τ O' (oGS := oGS) ∗
                        abort
                      )
              ) ∧
              ((∃ r__p, RR r__p) ∗ ⌜ TGT x ⌝ ∗ obls τ O (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) -∗
               BMU ∅ c (oGS := oGS) (∀ y, ▷ Q y x ={∅, ε}=∗ Φ #())) ∧
              abort
      ).
      
      Lemma TAU2_elim:
        TAU2 ⊣⊢ TAU2_acc TAU2.
      Proof using. Admitted.

      Lemma TAU2_intro (R: iProp Σ):
        (R ⊢ TAU2_acc R) ->
        (R ⊢ TAU2).
      Proof using. Admitted.

    End AtomicUpdates.

    Context `{EM: ExecutionModel heap_lang M}. 
    Context `{hGS: @heapGS Σ _ EM}.
    Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

    Let TLAT__impl (tau: coPset → Phase -> (val -> iProp Σ) → gset SignalId → (option RO → iProp Σ) -> iProp Σ)
      (e: expr) (s: stuckness): iProp Σ :=
      ∀ (Φ: val -> iProp Σ) (π: Phase) (O: gset SignalId) (RR: option RO -> iProp Σ),
        let ε := ⊤ ∖ ε__m in
        ⌜ B c <= LIM_STEPS ⌝ -∗
        RR None ∗ obls τ O (oGS := oGS) ∗ sgns_level_gt' O L ∗
        th_phase_eq τ π (oGS := oGS) ∗ cp π d__m (oGS := oGS) -∗
        tau ε π Φ O RR -∗
        WP e @ s; τ; ⊤ {{ v, Φ v }}.
    
    Definition TLAT1 := TLAT__impl TAU1. 
    Definition TLAT2 := TLAT__impl TAU2.

  End AtomicTriples.

End TotalTriples.


(* TODO: move to another file *)
Section FairLockSpec.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  
  Context {Σ: gFunctors}.
  Context {invs_inΣ: invGS_gen HasNoLc Σ}.

  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}.

  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

  Record FairLock := {
    fl_create: expr; fl_acquire: expr; fl_release: expr;
    fl_c__cr: nat; fl_B: nat -> nat;
    fl_LK: val * nat * bool -> iProp Σ;
    fl_is_lock: val -> nat -> iProp Σ;               
    fl_lvls: gset Level;
    fl_d__h: Degree;
    fl_d__l: Degree;
    fl_d__m: Degree;
    fl_degs_lh: deg_lt fl_d__l fl_d__h;
    fl_degs_hm: deg_lt fl_d__h fl_d__m;
    fl_ι: namespace;

    (* fl_spec_helper tlat c P Q tgt e τ := *)
    (*     tlat τ P Q *)
    (*       fl_lvls *)
    (*       (fun '(_, r, _) => r) tgt *)
    (*       fl_d__h fl_d__l fl_d__m *)
    (*       c fl_B *)
    (*       (↑ fl_ι) (e #()) NotStuck; *)
    fl_is_lock_pers lk c :> Persistent (fl_is_lock lk c);

    fl_create_spec: ⊢ ⌜ fl_c__cr <= LIM_STEPS ⌝ -∗ ∀ τ c,
      {{{ ⌜ True ⌝ }}} fl_create #() @ τ {{{ lk, RET lk; fl_LK (lk, 0, false) ∗ fl_is_lock lk c }}};

    fl_acquire_spec (lk: loc) c τ: fl_is_lock #lk c ⊢
        TLAT2 τ (fun x => fl_LK x ∗ ⌜ x.1.1 = #lk ⌝) (fun y x => fl_LK y ∗ ⌜ y.1 = x.1 /\ x.2 = false /\ y.2 = true⌝)
          fl_lvls
          (fun '(_, r, _) => r) (fun '(_, _, b) => b = false)
          fl_d__h fl_d__l fl_d__m
          c fl_B                        
          (↑ fl_ι) (fl_acquire #lk) NotStuck
          (oGS := oGS);               

    fl_release_spec (lk: loc) c τ: fl_is_lock #lk c ⊢
        TLAT1 τ (fun x => fl_LK x ∗ ⌜ x.2 = true /\ x.1.1 = #lk⌝) (fun y x => fl_LK y ∗ ⌜ y.1.2 = (x.1.2 + 1)%nat /\ y.2 = false /\ y.1.1 = x.1.1 ⌝)
          fl_lvls
          (fun '(_, r, _) => r) (fun _ => True%type)
          fl_d__h fl_d__l fl_d__m
          c fl_B
          (↑ fl_ι) (fl_release #lk) NotStuck
          (oGS := oGS)
  }. 

End FairLockSpec.


From iris.algebra Require Import auth gmap gset excl excl_auth csum.
From iris.base_logic.lib Require Import invariants.
From trillium.fairness.lawyer.examples Require Import signal_map.

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
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
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
  Context {invs_inΣ: invGS_gen HasNoLc Σ}.
  Context {oGS: @asem_GS _ _ ASEM Σ}.
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

  Context {FL: FairLock (oGS := oGS)}.

  Context (l__o l__f: Level).
  Hypothesis
    (LVL_ORDo: forall l, l ∈ fl_lvls FL -> lvl_lt l__o l)
    (LVL_ORDf: forall l, l ∈ fl_lvls FL -> lvl_lt l l__f)
    (* in case fl_lvls is empty *)
    (LVL_ORDof: lvl_lt l__o l__f).


  Section AfterInit.
    Context {CL: ClientG Σ}.
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
      ∃ r b oo smap, fl_LK FL (lk, r, b) ∗ lock_owner_auth oo ∗
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

    Existing Instance fl_is_lock_pers.

    Hypothesis (FL_STEPS: fl_B FL c__cl ≤ LIM_STEPS).
    Hypothesis (INVS_DISJ: fl_ι FL ## client_ns). 

    Definition RR__L π (r': option nat): iProp Σ := 
      match r' with
      | None => ⌜ True ⌝
      | Some r => ∃ s (* π__e *),
      ith_sig r s ∗ ep s π (fl_d__l FL) (oGS := oGS)
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

    From iris.proofmode Require Import tactics coq_tactics.

    Ltac remember_goal :=
      match goal with | |- envs_entails _ ?P =>
        iAssert (P -∗ P)%I as "GOAL"; [iIntros "X"; by iApply "X"| ]
      end.

    (* need to assume at least one FL level *)
    (* TODO: can we change either TAU or levels order? *)
    Context (l__fl: Level).
    Hypothesis (L__FL: l__fl ∈ fl_lvls FL). 

    Lemma BMU_wait_owner τ π O r m smap π__e i
      (PH_EXP: phase_le π__e π)
      (WAIT: r <= i):
      obls τ O (oGS := oGS) ∗ sgns_level_ge' O (fl_lvls FL) (oGS := oGS)∗
      th_phase_eq τ π (oGS := oGS) ∗ RR__L π__e (Some i) ∗ smap_repr_cl r m smap ⊢ 
      BMU ∅ 1 (cp π (fl_d__l FL) (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗ 
          obls τ O (oGS := oGS) ∗ smap_repr_cl r m smap
          (* ∗ ⌜ phase_le π π' /\ phase_le π__e π' ⌝ *)
      ) (oGS := oGS).
    Proof using LVL_ORDo L__FL.
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

    Hypothesis (DEG_LH: deg_lt (fl_d__l FL) (fl_d__h FL)). 

    Lemma BMU_create_wait_owner τ π r m smap i
      (DOM: i ∈ dom smap)
      :
      th_phase_eq τ π (oGS := oGS) ∗ cp π (fl_d__h FL) (oGS := oGS) ∗ smap_repr_cl r m smap ⊢ 
      BMU ∅ 1 (th_phase_eq τ π (oGS := oGS) ∗ RR__L π (Some i) ∗ 
                smap_repr_cl r m smap) (oGS := oGS).
    Proof using LVL_ORDo L__FL DEG_LH.
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

    Lemma acquire_left τ (lk: loc) flag s__f π:
      {{{ fl_is_lock FL #lk c__cl ∗ client_inv #lk flag s__f ∗ flag_unset ∗
          obls τ {[ s__f ]} (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) ∗
          cp_mul π (fl_d__m FL) 20 (oGS := oGS) ∗
          sgn s__f l__f None (oGS := oGS)
      }}}
        (fl_acquire FL) #lk @ τ
      {{{ v, RET v; ∃ s__o, obls τ {[ s__f; s__o ]} (oGS := oGS) ∗ flag_unset ∗
                          th_phase_eq τ π (oGS := oGS) ∗ 
                          P__lock flag s__f false ∗ lock_owner_frag (Some s__o) }}}.
    Proof using.
      iIntros (Φ). iIntros "(#LOCK & #INV & UNSET & OB & PH & CPSm & #SF') POST".
      iPoseProof (fl_acquire_spec FL _ _ τ with "[$]") as "ACQ".
      rewrite /TLAT2.

      iDestruct (cp_mul_take with "CPSm") as "[CPSm CP]".
      iSpecialize ("ACQ" $! Φ _ _ (RR__L π) with "[] [OB PH CP]").
      { done. }
      { iFrame.
        rewrite /sgns_level_gt'.
        iApply big_sepS_forall. iIntros (??).
        rewrite /sgns_level_gt. rewrite big_opS_singleton.
        iExists _. iFrame "#∗". iPureIntro.
        by apply LVL_ORDf. }
      iSpecialize ("ACQ" with "[UNSET POST]").
      2: { iApply "ACQ". }

      iApply (TAU2_intro with "[UNSET POST]").
      2: { (* iAccu. *)
           iCombine "INV SF' UNSET POST" as "X". iApply "X". }
      iIntros "(#INV & #SF' & UNSET & POST)".
      rewrite /TAU2_acc.
      iInv "INV" as "inv" "CLOS".
      iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'".
      rewrite {1}/client_inv_inner.
      iDestruct "inv" as (r b oo smap) "(LK & LOCK_OW & ST & SR)".
      iExists (#lk, r, b). iFrame "LK". iSplit; [done| ]. 
      
      iSplit; [| iSplit].
      
      3: { iIntros "[LK >%]".
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
        iFrame "#∗". iIntros "[LK >%]".
        iMod "CLOS'" as "_".
        iMod ("CLOS" with "[-]") as "_"; [| done].
        iNext. rewrite /client_inv_inner. do 4 iExists _. iFrame.
        iLeft. iSplit; [done| ]. iExists _. iFrame "#∗". done. }

      { iIntros "([%r' RR'] & -> & OB & PH)".
        remember_goal.
        iDestruct "ST" as "[[>% ?] | X]"; [done| ].
        iDestruct "X" as "(_& >LOCKED & >[%f P])".
        iMod "LOCK_OW". iMod "SR" as "[SR %DOM]".
        (* iMod "POST".  *)
        assert (forall v, Timeless (Φ v)) as TLΦ.
        { admit. }
        iMod "POST".
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
        iIntros ([[??]?]) "[LK >(%X & % & %)]". 
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
        
        iModIntro. iApply ("POST" with "[-]").
        rewrite {1}/P__lock. iDestruct "P" as "[F [[-> ?] | [-> SET]]]".
        2: { by iDestruct (os_pending_excl with "[$] [$]") as %?. }
        iExists _. iFrame. iLeft. iFrame. done.

    Admitted. 


    Lemma release_left (lk: loc) τ s__o flag s__f π:
      {{{ fl_is_lock FL #lk c__cl ∗ client_inv #lk flag s__f ∗
          flag_unset ∗ obls τ {[ s__f; s__o ]} (oGS := oGS) ∗ 
          th_phase_eq τ π (oGS := oGS) ∗ cp_mul π (fl_d__m FL) 20 (oGS := oGS) ∗
          P__lock flag s__f false ∗ lock_owner_frag (Some s__o) }}}
        (fl_release FL) #lk @ τ
      {{{ v, RET v; obls τ ∅ (oGS := oGS) ∗ th_phase_eq τ π (oGS := oGS) }}}.
    Proof using.
      iIntros (Φ).
      iIntros "(#LOCK & #INV & UNSET & OB & PH & CPSm & P & LOCKED) POST".
      iPoseProof (fl_release_spec FL lk _ τ with "[$]") as "REL".
      rewrite /TLAT1.
      iDestruct (cp_mul_take with "CPSm") as "[CPSm CP]".
      iSpecialize ("REL" $! Φ _ _ (RR__L π) with "[] [OB PH CP]").
      { done. }
      { iFrame.
        rewrite /sgns_level_gt'.
        iApply big_sepS_forall. iIntros (??).
        rewrite /sgns_level_gt.
        foobar. remove obligations set from release spec.
        rewrite big_opS_singleton.
        iExists _. iFrame "#∗". iPureIntro.
        by apply LVL_ORDf. }


      
    
End MotivatingClient.
