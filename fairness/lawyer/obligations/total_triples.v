From iris.base_logic Require Export gen_heap.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em.


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
        |={ε, ∅}=> ∃ x, P x ∗ (
                           let abort := P x ={∅, ε}=∗ V in
                           ((∃ r__p, RR r__p) ∗ ⌜ TGT x ⌝ ∗ obls τ O (oGS := oGS) -∗
                              BMU ∅ c (oGS := oGS) (∀ y, Q y x ={∅, ε}=∗ Φ #())) ∧
                             abort
                         ).
      
      Lemma TAU1_elim:
        TAU1 ⊣⊢ TAU1_acc TAU1.
      Proof using. Admitted.

      Definition TAU2: iProp Σ.
      Admitted.

      (* TODO: unify with TAU1_acc *)
      Definition TAU2_acc (V: iProp Σ): iProp Σ :=
        |={ε, ∅}=> ∃ x, P x ∗ (
              let abort := P x ={∅, ε}=∗ V in
              (let r := round x in
               ∀ O', obls τ O' (oGS := oGS) ∗ sgns_level_ge' O' L ∗
                      th_phase_ge τ π (oGS := oGS) ∗
                      (∃ r__p, RR r__p ∗ (⌜ r__p = Some r ⌝ ∨ cp π d__h (oGS := oGS))) ∗
                      ⌜ ¬ TGT x ⌝ -∗
                      BMU ∅ c (oGS := oGS) (
                        RR (Some r) ∗ cp π d__l (oGS := oGS) ∗
                        th_phase_ge τ π (oGS := oGS) ∗
                        obls τ O' (oGS := oGS) ∗
                        abort
                      )
              ) ∧
              ((∃ r__p, RR r__p) ∗ ⌜ TGT x ⌝ ∗ obls τ O (oGS := oGS) -∗
               BMU ∅ c (oGS := oGS) (∀ y, Q y x ={∅, ε}=∗ Φ #())) ∧
              abort
      ).
      
      Lemma TAU2_elim:
        TAU2 ⊣⊢ TAU2_acc TAU2.
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
        th_phase_ge τ π (oGS := oGS) ∗ cp π d__m (oGS := oGS) -∗
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
        TLAT2 τ (fun x => fl_LK x ∗ ⌜ x.1.1 = #lk ⌝) (fun y x => fl_LK y ∗ ⌜ y = x /\ x.2 = false ⌝)
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
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.

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

    (* Lemma os_pending_excl γ (os': one_shotR): *)
    (*   ⊢ own γ Pending -∗ own γ os' -∗ False.  *)
    (* Proof using. *)
    (*   rewrite bi.wand_curry -own_op. *)
    (*   iIntros "P". eauto 10.  *)
    (*   iDestruct (own_valid with "P") as "%V". *)
    (* Qed.  *)

  End Lemmas.

End OneShot.


Class ClientPreG Σ := {
    cl_ow_sig_pre :> inG Σ (excl_authUR (optionUR SignalId));
    (* eofin_sigs :> inG Σ (authUR (gmapUR nat (agreeR SignalId))); *)
    cl_one_shot_pre :> @one_shotG unitR Σ;
}.

Class ClientG Σ := {
    cl_PreG :> ClientPreG Σ;
    cl_γ__ow: gname;
    cl_γ__os: gname;
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
    
    Definition flag_unset := own cl_γ__os Pending.
    Definition flag_set := own cl_γ__os (Shot ()).

    Definition lock_owner_auth (oo: option SignalId) :=
      own cl_γ__ow (● Excl' oo). 
    Definition lock_owner_frag (oo: option SignalId) :=
      own cl_γ__ow (◯ Excl' oo). 
    
    Definition P__lock flag s__f (b: bool): iProp Σ :=
      flag ↦ #b ∗ (⌜ b = false ⌝ ∗ sgn s__f l__f (Some false) (oGS := oGS) ∨
                    ⌜ b = true ⌝ ∗ flag_set).
    
    Definition client_inv_inner lk flag s__f: iProp Σ :=
      ∃ r b oo, fl_LK FL (lk, r, b) ∗ lock_owner_auth oo ∗
        (⌜ b = true ⌝ ∗ (∃ o, ⌜ oo = Some o ⌝ ∗ sgn o l__o (Some false) (oGS := oGS)) ∨
         ⌜ b = false ⌝ ∗ lock_owner_frag None ∗ ∃ f, P__lock flag s__f f).

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

    Definition RR__cl (r': option nat): iProp Σ := 
      match r' with
      | None => ⌜ True ⌝
      | Some r => ⌜ False ⌝
      end. 

    Lemma acquire_left τ (lk: loc) flag s__f π:
      {{{ fl_is_lock FL #lk c__cl ∗ client_inv #lk flag s__f ∗ flag_unset ∗
          obls τ {[ s__f ]} (oGS := oGS) ∗ cp_mul π d2 20 (oGS := oGS) ∗ th_phase_ge τ π (oGS := oGS)
      }}}
        (fl_acquire FL) #lk @ τ
      {{{ v, RET v; ∃ s__o, obls τ {[ s__f; s__o ]} (oGS := oGS) ∗ flag_unset ∗
                          P__lock lk s__f false ∗ lock_owner_frag (Some s__o) }}}.
    Proof using.
      iIntros (Φ). iIntros "(#LOCK & #INV & UNSET & OB & CPS & PH) POST".
      iPoseProof (fl_acquire_spec FL with "[$]") as "ACQ".
      rewrite /TLAT2. iApply "ACQ".  
      
    
End MotivatingClient.
