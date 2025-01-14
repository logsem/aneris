From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fixpoint.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.
From trillium.program_logic Require Export weakestpre adequacy ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em.
From trillium.fairness.lawyer Require Import program_logic.


Section TotalTriples.
  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{LEl: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
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

  Let Locale := locale heap_lang. 

  Section AtomicTriples. 
    Context
      {ST: Type}
      {RO: Type}
      (τ: Locale)(* TODO: should it be fixed? *)
      (P: ST -> iProp Σ) (Q: ST -> ST -> iProp Σ) (* second ST is the previous state *)
      (L: gset Level) (* TODO: only finite sets? *)
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
        (q0: Qp)
        (Φ: ST -> ST -> iProp Σ)
        (O: gset SignalId)
        (RR: option RO -> iProp Σ)
      .

      Definition TAU_acc (V: iProp Σ): iProp Σ :=
        |={ε, ∅}=> ∃ x, P x ∗ (
              let abort := P x ={∅, ε}=∗ V in
              let PH q := th_phase_frag τ π q (oGS := oGS) in
              (let r := round x in
               ∀ O' q', obls τ O' (oGS := oGS) ∗ sgns_level_ge' O' L (oGS := oGS) ∗ 
                        PH q' ∗ ⌜ Qp.le q' q0 ⌝ ∗
                      (∃ r__p, RR r__p ∗ (⌜ r__p = Some r ⌝ ∨ cp π d__h (oGS := oGS))) ∗
                      ⌜ ¬ TGT x ⌝ -∗
                      BMU ∅ c (oGS := oGS) (
                        RR (Some r) ∗ cp π d__l (oGS := oGS) ∗ PH q' ∗
                        obls τ O' (oGS := oGS) ∗
                        abort
                      )
              ) ∧
              (∀ q',
               (* (∃ r__p, RR r__p) ∗ *)
               ⌜ TGT x ⌝ ∗ obls τ O (oGS := oGS)
                 ∗ PH q' ∗ ⌜ Qp.le q' q0 ⌝
                 -∗
               BMU ∅ c (oGS := oGS) (
                 ∀ y, Q y x ={∅, ε}=∗ from_option PH ⌜ True ⌝ (Qp.sub q0 q') -∗ Φ y x)) ∧
              abort
      ).

      Definition TAU_pre (V : () → iProp Σ) (_ : ()) : iProp Σ :=
        TAU_acc (V ()).

      Lemma TAU_acc_mono V1 V2:
        (V1 -∗ V2) -∗ TAU_acc V1 -∗ TAU_acc V2.
      Proof using.
        iIntros "V12 T1". rewrite /TAU_acc.
        iMod "T1" as (?) "[P T1]". iModIntro. iExists _. iFrame "P".
        iSplit; [| iSplit].
        - iIntros (??) "X". iDestruct "T1" as "[T1 _]".
          iSpecialize ("T1" with "[$]").
          iApply (BMU_wand with "[-T1]"); [| done].
          iIntros "(?&?&?&?&AB)". iFrame.
          iIntros "?". iMod ("AB" with "[$]"). by iApply "V12".
        - iDestruct "T1" as "[_ [T1 _]]". done.
        - iDestruct "T1" as "[_ [_ AB]]".
          iIntros "?". iMod ("AB" with "[$]"). by iApply "V12".
      Qed.

      Global Instance TAU_pre_mono : BiMonoPred TAU_pre.
      Proof.
        constructor.
        - iIntros (P1 P2 ??) "#HP12". iIntros ([]) "AU".
          rewrite /TAU_pre.
          iApply (TAU_acc_mono with "[] [$]"). done. 
        - intros ??. solve_proper.
      Qed.

      Local Definition TAU_def :=
        bi_greatest_fixpoint TAU_pre ().

      (* TODO: seal *)
      Definition TAU := TAU_def.
      
      Lemma TAU_elim:
        TAU ⊣⊢ TAU_acc TAU.
      Proof using.
        rewrite /TAU /TAU_def /=. apply: greatest_fixpoint_unfold.
      Qed.

      Lemma TAU_intro U V:
        Absorbing U → Persistent U →
        (U ∧ V ⊢ TAU_acc V) → U ∧ V ⊢ TAU.
      Proof.
        rewrite /TAU /TAU_def /=.
        iIntros (?? HAU) "[#HP HQ]".
        iApply (greatest_fixpoint_coiter _ (λ _, V)); last done.
        iIntros "!>" ([]) "HQ".
        iApply HAU. iSplit; by iFrame.
      Qed.

    End AtomicUpdates.

    Context `{EM: ExecutionModel heap_lang M}. 
    Context `{hGS: @heapGS Σ _ EM}.
    Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

    Definition TLAT_pre (RR: option RO -> iProp Σ) π q (O: gset SignalId): iProp Σ :=
      RR None ∗ obls τ O (oGS := oGS) ∗ sgns_level_gt' O L (oGS := oGS) ∗
      th_phase_frag τ π q (oGS := oGS) ∗ cp π d__m (oGS := oGS).
    
    Definition TLAT e s
      (POST: ST -> ST -> option (iProp Σ))
      (get_ret: ST -> ST -> val)
      : iProp Σ :=
      ∀ Φ q π O (RR: option RO -> iProp Σ),
        ⌜ B c <= LIM_STEPS ⌝ -∗ TLAT_pre RR π q O -∗
        TAU (⊤ ∖ ε__m) π q (fun y x => POST y x -∗? Φ (get_ret y x)) O RR -∗
        WP e @ s; τ; ⊤ {{ v, Φ v }}.

  End AtomicTriples.

  Global Instance TAU_acc_Proper {ST RO: Type}:
    Proper
      (eq ==> (eq ==> equiv) ==> (eq ==> eq ==> equiv) ==> equiv ==> 
       (eq ==> eq) ==> (eq ==> iff) ==> eq ==> eq ==> eq ==> equiv ==> 
       eq ==> eq ==> (eq ==> eq ==> equiv ) ==> equiv ==> (eq ==> equiv) ==> equiv ==>
       equiv) (TAU_acc (ST := ST) (RO := RO)).
  Proof using.
    (* TODO: simplify *)
    red. repeat intro. subst. 
    rewrite /TAU_acc.
    apply leibniz_equiv_iff in H4, H10, H14. subst.
    iApply fupd_proper. 
    iApply bi.exist_proper. iIntros (?).
    iApply bi.sep_proper; [by eauto| ].
    iApply bi.and_proper.
    { do 2 (iApply bi.forall_proper; iIntros (?)).
      iApply bi.wand_proper.
      { repeat iApply bi.sep_proper; try done. 
        2: { iApply bi.pure_proper. apply not_iff_compat. eauto. }
        iApply bi.exist_proper. iIntros (?).
        iApply bi.sep_proper; eauto.
        iApply bi.or_proper; eauto.
        iApply bi.pure_proper. split; intros ->; subst; f_equal; [| symmetry]; eauto. }
      rewrite -(H5 a); [| done]. rewrite -(H2 a); [| done]. rewrite H16.
      rewrite -(H15 _); reflexivity. }
    rewrite -(H2 a); [| done].
    iApply bi.and_proper.
    2: { solve_proper. }
    iApply bi.forall_proper; iIntros (?).
    rewrite -(H6 a); [| done].
    (* rewrite H16. *)
    setoid_rewrite <- (H3 _ _ _ _); try reflexivity.
    setoid_rewrite <- (H13 _ _ _ _); reflexivity.
  Qed.

  Global Instance TAU_Proper {ST RO: Type}:
    Proper
      (eq ==> (eq ==> equiv) ==> (eq ==> eq ==> equiv) ==> equiv ==> 
       (eq ==> eq) ==> (eq ==> iff) ==> eq ==> eq ==> eq ==> equiv ==> 
       eq ==> eq ==> (eq ==> eq ==> equiv ) ==> equiv ==> (eq ==> equiv) ==> equiv)
      (TAU (ST := ST) (RO := RO)).
  Proof using.
    rewrite /TAU /TAU_def.
    red. repeat intro. subst.
    eapply greatest_fixpoint_proper; [| done].
    repeat intro. rewrite /TAU_pre. iApply TAU_acc_Proper; eauto.
  Qed.

End TotalTriples.


(* TODO: move to another file *)
Section FairLockSpec.

  Definition FL_st: Type := val * nat * bool.

  Definition fl_round: FL_st -> nat := fun '(_, r, _) => r. 

  Context `{OfeDiscrete DegO} `{OfeDiscrete LevelO}.
  Context `{@LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}. 
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.
  
  Record FairLockPre := {
    fl_c__cr: nat; fl_B: nat -> nat;
    fl_GS :> gFunctors -> Set;
    fl_LK `{FLG: fl_GS Σ} {HEAP: gen_heapGS loc val Σ}: FL_st -> iProp Σ;
    fl_d__h: Degree;
    fl_d__l: Degree;
    fl_d__m: Degree;
    fl_degs_lh: deg_lt fl_d__l fl_d__h;
    fl_degs_hm: deg_lt fl_d__h fl_d__m;
    fl_ι: namespace;
    fl_acq_lvls: gset Level;                                     
  }.


  Context {Σ: gFunctors}.
  (* Context {invs_inΣ: invGS_gen HasNoLc Σ}. *)
  
  Let OAM := ObligationsAM. 
  Let ASEM := ObligationsASEM.
  Context {oGS: @asem_GS _ _ ASEM Σ}.
  
  Context `{EM: ExecutionModel heap_lang M}.
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).
  
  Context {FLP: FairLockPre}.
  
  Definition TAU_FL τ P Q L TGT c π q
    (* (Φ: val -> iProp Σ) *)
    Φ
    O (RR: option nat -> iProp Σ): iProp Σ := 
    TAU τ P Q L fl_round TGT (fl_d__h FLP) (fl_d__l FLP)
      c
      (⊤ ∖ ↑(fl_ι FLP))
      π q
      (* (fun _ _ => Φ #()) *)
      Φ
      O RR
      (oGS := oGS). 
  
  Definition TLAT_FL τ P Q L TGT (POST: FL_st -> FL_st -> option (iProp Σ))
    get_ret c e : iProp Σ := 
    TLAT τ P Q L          
      fl_round TGT
      (fl_d__h FLP) (fl_d__l FLP) (fl_d__m FLP)
      c (fl_B FLP)
      (↑ (fl_ι FLP)) e NotStuck
      POST
      get_ret
      (oGS := oGS).
  
  Definition acquire_at_pre {FLG: fl_GS FLP Σ} (lk: val) (x: FL_st): iProp Σ :=
    ▷ fl_LK FLP x (FLG := FLG) ∗ ⌜ x.1.1 = lk ⌝. 
  Definition acquire_at_post {FLG: fl_GS FLP Σ} (lk: val) (y x: FL_st): iProp Σ :=
    fl_LK FLP y (FLG := FLG) ∗ ⌜ y.1 = x.1 /\ x.2 = false /\ y.2 = true⌝.
  Definition release_at_pre {FLG: fl_GS FLP Σ} (lk: val) (x: FL_st): iProp Σ :=
    ▷ fl_LK FLP x (FLG := FLG) ∗ ⌜ x.2 = true /\ x.1.1 = lk⌝. 
  Definition release_at_post {FLG: fl_GS FLP Σ} (lk: val) (y x: FL_st): iProp Σ :=
    fl_LK FLP y (FLG := FLG) ∗ ⌜ y.1.2 = (x.1.2 + 1)%nat /\ y.2 = false /\ y.1.1 = x.1.1 ⌝.
  
  Record FairLock := {    
    fl_create: val; fl_acquire: val; fl_release: val;

    fl_is_lock `{FLG: fl_GS FLP Σ} {HEAP: gen_heapGS loc val Σ}: val -> nat -> iProp Σ;
    fl_is_lock_pers {FLG: fl_GS FLP Σ} lk c :> Persistent (fl_is_lock lk c (FLG := FLG));

    fl_release_token: iProp Σ;

    fl_create_spec: ⊢ ⌜ fl_c__cr FLP <= LIM_STEPS ⌝ -∗ ∀ τ c,
      {{{ ⌜ True ⌝ }}} fl_create #() @ τ {{{ lk, RET lk;
         ∃ FLG: fl_GS FLP Σ, fl_LK FLP (lk, 0, false) (FLG := FLG) ∗ fl_is_lock lk c (FLG := FLG) }}};

    fl_acquire_spec {FLG: fl_GS FLP Σ} (lk: val) c τ: (fl_is_lock (FLG := FLG)) lk c ⊢
        TLAT_FL τ 
        (acquire_at_pre lk (FLG := FLG))
        (acquire_at_post lk (FLG := FLG))
        (fl_acq_lvls FLP)
        (fun '(_, _, b) => b = false)
        (fun _ _ => Some fl_release_token)
        (fun _ _ => #())
        c (fl_acquire lk);
                                     
    fl_release_spec {FLG: fl_GS FLP Σ} (lk: val) c τ: (fl_is_lock (FLG := FLG)) lk c ∗ fl_release_token ⊢
        TLAT_FL τ
        (release_at_pre lk (FLG := FLG))
        (release_at_post lk (FLG := FLG))
        ∅
        (fun _ => True%type)
        (fun _ _ => None)
        (fun _ '(_, r, _) => #r)
        c (fl_release lk);
  }.
  
End FairLockSpec.


Section Ticketlock.
  Context `{ODd: OfeDiscrete DegO} `{ODl: OfeDiscrete LevelO}.
  Context `{LEl: @LeibnizEquiv (ofe_car LevelO) (ofe_equiv LevelO)}.
  
  Let Degree := ofe_car DegO.
  Let Level := ofe_car LevelO.

  Context `{OPRE: ObligationsParamsPre Degree Level LIM_STEPS}.
  Let OP := LocaleOP (Locale := locale heap_lang).
  Existing Instance OP.
  Let OM := ObligationsModel.

  Definition Tid := locale heap_lang.

  Local Infix "*'" := prod (at level 10, left associativity).
  (* Definition tau_codom Σ: Type := (((Tid * Phase) * gset SignalId) * gset Level) *  *)
  (*                                   (* (iProp Σ) *) *)
  (*                                   (ofe_mor val (iProp Σ)) *)
  Definition tau_codom Σ: Type :=
    Tid *' Phase *' Qp *'
    (gset SignalId) *' (gset Level) *'
    (ofe_mor val (iProp Σ)) *' (ofe_mor (option nat) (iProp Σ)).

  Local Infix "**" := prodO (at level 10, left associativity).

  (* Definition tau_codomO Σ: ofe := prodO (prodO (prodO (prodO Tid Phase) (gsetO SignalId)) (gsetR Level)) *)
  (*                                   (* ((iPropO Σ)) *) *)
  (*                                       (ofe_morO valO (iPropO Σ)) *)
  (* . *)
  Definition tau_codomO Σ: ofe :=
    Tid ** Phase ** Qp ** (gsetO SignalId) ** (gsetR Level) **
    (ofe_morO valO (iPropO Σ)) ** (ofe_morO (optionR natO) (iPropO Σ)).
 
  Class TicketlockPreG Σ := {
      tl_tau_map_pre :> inG Σ (authUR (gmapUR nat (exclR $ tau_codomO Σ)));
      tl_tokens_pre :> inG Σ (authUR (gset_disjUR natO));
      tl_held_pre :> inG Σ (excl_authUR boolO);
      tl_ow_lb_pre :> inG Σ mono_natUR;
      tl_rel_tok_pre :> inG Σ (exclR unitO);
  }.

  Class TicketlockG Σ := {
      tl_pre :> TicketlockPreG Σ;
      tl_γ_tau_map: gname; tl_γ_tokens: gname; tl_γ_held: gname;
      tl_γ_ow_lb: gname; tl_γ_rel_tok: gname;
  }.

  Definition tau_map_auth `{TicketlockG Σ} (TM: gmap nat (tau_codom Σ)) :=
    own tl_γ_tau_map ((● (Excl <$> TM)): authUR (gmapUR nat (exclR $ tau_codomO Σ))).
  Definition ticket_tau `{TicketlockG Σ} (n: nat) (cd: tau_codom Σ) :=
    own tl_γ_tau_map ((◯ {[ n := Excl cd ]}): authUR (gmapUR nat _)).

  Definition tokens_auth `{TicketlockG Σ} (N: nat) :=
    own tl_γ_tokens ((● (GSet $ set_seq 0 N)): authUR (gset_disjUR natO)).
  Definition ticket_token `{TicketlockG Σ} (i: nat) :=
    own tl_γ_tokens ((◯ (GSet {[ i ]})): authUR (gset_disjUR natO)).

  Definition held_auth `{TicketlockG Σ} (b: bool) :=
    own tl_γ_held ((● Excl' b): (excl_authUR boolO)).
  Definition held_frag `{TicketlockG Σ} (b: bool) :=
    own tl_γ_held ((◯ Excl' b): (excl_authUR boolO)).

  Definition ow_exact `{TicketlockG Σ} (n: nat) :=
    own tl_γ_ow_lb ((●MN n): mono_natUR).
  Definition ow_lb `{TicketlockG Σ} (n: nat) :=
    own tl_γ_ow_lb (mono_nat_lb n).

  Definition rel_tok `{TicketlockG Σ} := own tl_γ_rel_tok (Excl ()).

  Lemma ticket_token_excl `{TicketlockG Σ} i:
    ticket_token i -∗ ticket_token i -∗ False.
  Proof using.
    clear ODl ODd LEl.
    iApply bi.wand_curry. rewrite -own_op -auth_frag_op.
    iIntros "X". iDestruct (own_valid with "X") as %V.
    rewrite auth_frag_valid in V. apply gset_disj_valid_op in V. set_solver.
  Qed.

  Lemma ticket_token_bound `{TicketlockG Σ} i N:
    ticket_token i -∗ tokens_auth N -∗ ⌜ i < N ⌝.
  Proof using.
    iApply bi.wand_curry. rewrite bi.sep_comm -own_op.
    iIntros "X". iDestruct (own_valid with "X") as %V.
    apply auth_both_valid_discrete in V as [IN V].
    apply gset_disj_included, elem_of_subseteq_singleton in IN.
    apply elem_of_set_seq in IN. iPureIntro. lia.
  Qed.

  Lemma held_agree `{TicketlockG Σ} b1 b2:
    held_auth b1-∗ held_frag b2 -∗ ⌜ b1 = b2 ⌝.
  Proof using.
    iIntros "HA HB". iCombine "HB HA" as "H".
    iDestruct (own_valid with "H") as "%Hval".
    iPureIntro. apply excl_auth_agree_L in Hval. set_solver.
  Qed.

  Lemma held_update `{TicketlockG Σ} b1 b2 b':
    held_auth b1 -∗ held_frag b2 ==∗
    held_auth b' ∗ held_frag b'.
  Proof using.
    iIntros "HA HB". iCombine "HB HA" as "H".
    rewrite -!own_op. iApply own_update; [| by iFrame].
    apply excl_auth_update.
  Qed.

  Lemma ticket_tau_alloc `{TicketlockG Σ} TM n cd
    (FRESH: n ∉ dom TM):
    tau_map_auth TM ==∗ tau_map_auth (<[ n := cd ]> TM) ∗ ticket_tau n cd.
  Proof using.
    clear ODl ODd LEl.
    iIntros. rewrite -own_op. iApply own_update; [| by iFrame].
    apply auth_update_alloc.
    rewrite fmap_insert. apply alloc_singleton_local_update.
    2: done.
    apply not_elem_of_dom. set_solver.
  Qed.

  Lemma tau_map_ticket `{TicketlockG Σ} TM i cd:
    tau_map_auth TM -∗ ticket_tau i cd -∗ TM !! i ≡ Some cd.
  Proof using.
    rewrite /tau_map_auth /ticket_tau.
    iApply bi.wand_curry. rewrite -own_op. iIntros "X".
    iDestruct (own_valid with "[$]") as "#V".
    iAssert ((Excl <$> TM) !! i ≡ Excl' cd)%I as "#EQ'".
    2: { rewrite lookup_fmap. destruct (TM !! i) eqn:TMi.
         2: { simpl. intuition. by rewrite !option_equivI. }
         simpl. by rewrite !option_equivI excl_equivI. }
    rewrite auth_both_dfrac_validI. iDestruct "V" as "(_ & [% #EQ] & -#VM)".
    iRewrite "EQ".
    rewrite lookup_op lookup_singleton.
    rewrite Some_op_opM. simpl.
    rewrite gmap_validI. iSpecialize ("VM" $! i).
    destruct (c !! i) eqn:CI; rewrite CI; [| done].
    simpl. iRewrite "EQ" in "VM". rewrite lookup_op CI lookup_singleton. simpl.
    rewrite -Some_op. rewrite option_validI.
    iDestruct (uPred_primitive.cmra_valid_elim with "VM") as %V.
    done.
  Qed.

  Lemma ow_exact_lb `{TicketlockG Σ} n:
    ow_exact n -∗ ow_exact n ∗ ow_lb n.
  Proof using.
    iIntros "EX".
    rewrite /ow_exact. rewrite mono_nat_auth_lb_op.
    rewrite /ow_lb -own_op.
    erewrite (mono_nat_lb_op_le_l n) at 1; [| reflexivity].
    by rewrite cmra_assoc.
  Qed.

  Lemma ow_exact_increase `{TicketlockG Σ} n m
    (LE: n <= m):
    ow_exact n ==∗ ow_exact m ∗ ow_lb m.
  Proof using.
    iIntros "EX".
    rewrite /ow_exact.
    rewrite /ow_lb -!own_op.
    iApply (own_update with "[$]").
    etrans.
    { apply mono_nat_update, LE. }
    by rewrite {1}mono_nat_auth_lb_op.
  Qed.

  Lemma ow_lb_le_exact `{TicketlockG Σ} i n:
    ow_lb i -∗ ow_exact n -∗ ⌜ i <= n ⌝.
  Proof using.
    iApply bi.wand_curry. rewrite bi.sep_comm -own_op. iIntros "X".
    iDestruct (own_valid with "X") as %V%mono_nat_both_valid. done.
  Qed.

  Definition tl_LK `{TicketlockG Σ} `{gen_heapGS loc val Σ}
    (st: FL_st): iProp Σ :=
    let '(lk, r, b) := st in
    ∃ (l__ow l__tk: loc),
      ⌜ lk = (#l__ow, #l__tk)%V ⌝ ∗ l__ow ↦{/ 2} #r ∗
      held_frag b.

  (* Right now we just assume that the resulting OM has all needed degrees and levels *)
  Context (d__w d__l0 d__h0 d__e d__m0: Degree).
  Hypothesis
    (fl_degs_wl0: deg_lt d__w d__l0)
    (fl_degs_lh0: deg_lt d__l0 d__h0)
    (fl_degs_he: deg_lt d__h0 d__e)
    (fl_degs_em: deg_lt d__e d__m0)
  .
        
  Definition tl_ns := nroot .@ "tl".

  Program Definition TLPre: FairLockPre := {|
    fl_c__cr := 2;
    fl_B := fun c => 2 * c + 3;
    fl_GS := TicketlockG;
    fl_LK := fun Σ FLG HEAP => tl_LK;
    fl_degs_lh := fl_degs_lh0;
    fl_d__m := d__m0;
    fl_ι := tl_ns;
    fl_acq_lvls := ∅;
  |}.
  Next Obligation.
    etrans; eauto.
  Defined.

  Let OAM := ObligationsAM.
  Let ASEM := ObligationsASEM.

  Context {Σ: gFunctors}.
  (* Context {invs_inΣ: invGS_gen HasNoLc Σ}. *)
  Context {oGS: @asem_GS _ _ ASEM Σ}.
  Context `{EM: ExecutionModel heap_lang M}.
  Context `{hGS: @heapGS Σ _ EM}.
  Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).
           
  Let tl_TAU := TAU_FL (FLP := TLPre) (oGS := oGS).

  Definition TAU_stored `{TLG: TicketlockG Σ} (lk: val) (c: nat) (cd: tau_codom Σ): iProp Σ :=
    let '(τ, π, q, Ob, L, Φ, RR) := cd in
    obls τ Ob (oGS := oGS) ∗ sgns_level_gt' Ob L (oGS := oGS) ∗
    th_phase_frag τ π (q /2) (oGS := oGS) ∗
    tl_TAU τ (acquire_at_pre lk (FLP := TLPre) (FLG := TLG)) (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        L
        (fun '(_, _, b) => b = false)
        c π
        (* (fun _ _ => bi_wand (th_phase_eq τ π (oGS := oGS): iProp Σ) (Φ #())) *)
        q
        (fun _ _ => Φ #())
        Ob RR.

  Instance TAU_stored_Proper `{TLG: TicketlockG Σ}:
    Proper (eq ==> eq ==> equiv ==> equiv) TAU_stored.
  Proof using.
    intros ?????????. subst. rewrite /TAU_stored.
    destruct x1 as [[[[[[]]]]]], y1 as [[[[[[]]]]]].
    rename H1 into X.
    repeat (inversion X as [X1 ?Y]; clear X; rename X1 into X). simpl in *. subst.
    apply leibniz_equiv_iff in Y1, Y2, X, Y3, Y4. subst.
    rewrite {1 2}X. rewrite Y3. 
    rewrite /tl_TAU /TAU_FL. simpl.
    do 3 (iApply bi.sep_proper; [by eauto| ]).
    iApply TAU_Proper; solve_proper.
  Qed.

  Definition tau_interp `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) (i: nat) (cd: tau_codom Σ): iProp Σ :=
      (* let Φ := cd.1.2 in let q := cd.1.2 in *)
      let '((((((τ, π), q), _), _), Φ), _) := cd in   
      (TAU_stored lk c cd ∗ ⌜ ow < i ⌝ ∨
       (((th_phase_frag τ π (q /2) (oGS := oGS) -∗ Φ #()) ∗ rel_tok ∨ ticket_token i) ∗ ⌜ ow = i ⌝) ∨
       ticket_token i ∗ ⌜ i < ow ⌝).

  Lemma tau_interp_Proper_impl' `{TicketlockG Σ} lk c ow i x y:
    (x ≡ y) -∗ tau_interp lk c ow i x -∗ tau_interp lk c ow i y.
  Proof using.
    iIntros "#EQUIV". rewrite /tau_interp.
    rewrite /TAU_stored.
    destruct x as [[[[[[]]]]]], y as [[[[[[]]]]]]. simpl.
    repeat rewrite prod_equivI. simpl. iDestruct "EQUIV" as "[[[[[[%U %W] %V] %Y]%Z] #A] #B]".
    apply leibniz_equiv_iff in Y, Z. apply (proj1 (leibniz_equiv_iff _ _)) in U, W, V. subst.
    rewrite !ofe_morO_equivI.
    iIntros "T". iDestruct "T" as "[T | [T | T]]"; try by (iRight; iFrame).
    2: { iRight. iLeft. iDestruct "T" as "[T ->]". iSplit; [| done].
         iDestruct "T" as "[T | ?]"; [| by iFrame].
         iSpecialize ("A" $! #()).
         iLeft. by iRewrite -"A". }
    iLeft.
    iDestruct "T" as "[[? (?&?&T)] ?]". iFrame.
    rewrite /tl_TAU /TAU_FL.

    (* TODO: extract lemma *)
    rewrite /TAU /TAU_def.
    iDestruct (greatest_fixpoint_strong_mono with "[] T") as "foo".
    2: by iFrame.
    iModIntro. iIntros (Φ ?). rewrite /TAU_pre. rewrite /TAU_acc.
    (* iApply fupd_mono. *)
    iIntros "X". iMod "X" as (?) "[P T1]". iModIntro. iExists _. iFrame "P".
    iSplit; [| iSplit].
    - iIntros (??) "X". iDestruct "T1" as "[T1 _]".
      iApply (BMU_wand with "[]").
      2: { iApply "T1". iDestruct "X" as "(?&?&?&?&X&?)". iFrame.
           iDestruct "X" as (?) "(?&?)". iExists _. iFrame.
           iSpecialize ("B" $! r__p). by iRewrite "B". }
      iIntros "(C&?&?&?&?)". iFrame.
      iSpecialize ("B" $! (Some (fl_round x0))). by iRewrite "B" in "C".
    - iDestruct "T1" as "[_ [T1 _]]".
      iIntros (?) "(%&?&?)".
      iApply (BMU_wand with "[]").
      2: { iApply "T1". iFrame. done. }
      iIntros "P". iFrame. iIntros (?) "?". iSpecialize ("P" with "[$]").
      iMod "P". iModIntro. by iRewrite -("A" $! #()).
    - by iDestruct "T1" as "[_ [_ T1]]".
  Qed.

  (* Lemma tau_interp_Proper_impl `{TicketlockG Σ}: *)
  (*   Proper (eq ==> eq ==> eq ==> eq ==> equiv ==> bi_entails) (tau_interp). *)
  (* Proof using. *)
  (*   intros ???????????????. subst. *)
  (*   iStartProof. rewrite /tau_interp. *)
  (*   iIntros "T". iDestruct "T" as "[T | [T | T]]"; try by (iRight; iFrame). *)
  (*   2: { iRight. iLeft. iDestruct "T" as "[T ?]". iSplit; [| done]. *)
  (*        iDestruct "T" as "[T | ?]"; [| by iFrame]. *)
  (*        iLeft. *)
  (*        destruct x3 as [[??]?], y3 as [[??]?]. simpl. inversion H4. *)
  (*        simpl in *. inversion H0. simpl in *. *)
  (*        by iApply H3. } *)
  (*   rewrite H4. by iLeft. *)
  (* Qed. *)

  (* Instance tau_interp_Proper `{TicketlockG Σ}: *)
  (*   Proper (eq ==> eq ==> eq ==> eq ==> (fun x y => equiv (A:=tau_codom Σ) x y) ==> equiv) (tau_interp). *)
  (* Proof using. *)
  (*   intros ???????????????. subst. *)
  (*   iStartProof. iSplit; iApply tau_interp_Proper_impl; done. *)
  (* Qed. *)
    
  Definition tau_map_interp `{TicketlockG Σ} (lk: val) (c: nat) (ow: nat) (TM: gmap nat (tau_codom Σ)): iProp Σ :=
    [∗ map] i ↦ cd ∈ TM, tau_interp lk c ow i cd.
  
  Definition tl_inv_inner `{TicketlockG Σ} (tl: val) (c: nat): iProp Σ :=
    ∃ (l__ow l__tk: loc) (ow tk: nat) TM,
      ⌜ tl = (#l__ow, #l__tk)%V ⌝ ∗ ⌜ ow <= tk ⌝ ∗ exc_lb (tk - ow + 2) (oGS := oGS) ∗
      l__ow ↦{/ 2} #ow ∗ l__tk ↦ #tk ∗ ow_exact ow ∗ held_auth (negb (ow =? tk)) ∗
      tokens_auth tk ∗
      ⌜ dom TM = set_seq 0 tk ⌝ ∗ tau_map_auth TM ∗ tau_map_interp tl c ow TM ∗
      (⌜ ow = tk ⌝ → rel_tok).

  Lemma tau_map_ticket_interp `{TicketlockG Σ} TM i cd lk c ow:
    tau_map_auth TM -∗ ticket_tau i cd -∗ tau_map_interp lk c ow TM -∗
    tau_interp lk c ow i cd ∗ ticket_tau i cd ∗ tau_map_auth TM ∗ (tau_interp lk c ow i cd -∗ tau_map_interp lk c ow TM).
  Proof using.
    clear fl_degs_wl0 d__w ODl ODd LEl.
    iIntros "TM T TMI".
    iDestruct (tau_map_ticket with "[$] [$]") as "#TK".
    rewrite {1}/tau_map_interp. rewrite {3}(map_split TM i).
    rewrite big_opM_union.
    2: { apply map_disjoint_dom. destruct lookup; set_solver. }
    iDestruct "TMI" as "[TKI CLOS]".
    destruct (TM !! i) eqn:TMi; rewrite option_equivI; [| done].
    simpl. rewrite big_sepM_singleton.
    iDestruct (tau_interp_Proper_impl' with "TK TKI") as "TKI". iFrame.
    iIntros "TKI".
    rewrite internal_eq_sym.
    iDestruct (tau_interp_Proper_impl' with "TK TKI") as "TKI".
    iDestruct (big_sepM_insert_delete with "[CLOS TKI]") as "TMI".
    { repeat iFrame. }
    rewrite insert_id; [| done]. iFrame.
  Qed.
    
  Lemma TMI_extend_queue `{TicketlockG Σ} lk c ow TM tk cd
    (DOM: dom TM = set_seq 0 tk)
    (QUEUE: ow < tk):
    tau_map_interp lk c ow TM -∗ TAU_stored lk c cd -∗
    tau_map_interp lk c ow (<[ tk := cd ]> TM).
  Proof using.
    iIntros "TMI TAU".
    rewrite /tau_map_interp. rewrite big_opM_insert.
    2: { apply not_elem_of_dom. rewrite DOM. intros ?%elem_of_set_seq. lia. }
    iFrame. rewrite /tau_interp.
    destruct cd as [[[[[[]]]]]]. iLeft. by iFrame.
  Qed.

  Lemma TMI_extend_acquire `{TicketlockG Σ} lk c ow TM (cd: tau_codom Σ)
    (DOM: dom TM = set_seq 0 ow):
    let '((((((τ, π), q), _), _), Φ), _) := cd in   
    tau_map_interp lk c ow TM -∗ rel_tok -∗
    (th_phase_frag τ π (q /2) (oGS := oGS) -∗ cd.1.2 #()) -∗
    tau_map_interp lk c ow (<[ ow := cd ]> TM).
  Proof using.
    destruct cd as [[[[[[]]]]]].
    iIntros "TMI RTOK TAU".
    rewrite /tau_map_interp. rewrite big_opM_insert.
    2: { apply not_elem_of_dom. rewrite DOM. intros ?%elem_of_set_seq. lia. }
    iFrame. iRight. iLeft. iSplit; [| done]. iLeft. iFrame. 
  Qed.

  Lemma tokens_alloc `{TicketlockG Σ} (N: nat):
    tokens_auth N ==∗ tokens_auth (S N) ∗ ticket_token N.
  Proof using.
    iIntros. rewrite /tokens_auth /ticket_token.
    rewrite -own_op. iApply own_update; [| by iFrame].
    apply auth_update_alloc.
    rewrite set_seq_S_end_union_L. simpl.
    etrans.
    1: eapply gset_disj_alloc_empty_local_update.
    2: { reflexivity. }
    apply disjoint_singleton_l. by (intros ?%elem_of_set_seq; lia).
  Qed.

  Definition get_ticket: val :=
    λ: "lk", FAA (Snd "lk") #1.

  Definition wait: val :=
    rec: "wait" "lk" "t" :=
      let: "o" := !(Fst "lk") in
      if: "t" = "o"
      then #()
      else "wait" "lk" "t"
  .

  Definition tl_acquire : val :=
    λ: "lk",
      let: "t" := get_ticket "lk" in
      wait "lk" "t"
  .

  Definition tl_release: val :=
      λ: "lk", FAA (Fst "lk") #1
  .

  Definition tl_is_lock `{TicketlockG Σ} lk c := inv tl_ns (tl_inv_inner lk c).

  Context {TLG: TicketlockG Σ}.
  
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

  (* Definition mk_tcd (τ: Tid) (π: Phase) (R: gset SignalId) *)
  (*                   (Φ: ofe_mor val (iProp Σ)) (RR: ofe_mor (option nat) (iProp Σ)): *)
  (*   tau_codom Σ := *)
  (*   (τ, π, R, Φ, RR).  *)

  (* TODO: find existing *)
  Lemma fupd_frame_all E1 E2 P:
    ((|==> P) ∗ |={E1, E2}=> emp: iProp Σ) ⊢ |={E1, E2}=> P.
  Proof using.
    iIntros "[P ?]". iMod "P". by iFrame.
  Qed.

  Definition wait_res o' t τ π q Ob Φ (RR : ofe_mor (optionO natO) (iPropO Σ)): iProp Σ :=
    ⌜ o' <= t ⌝ ∗
    ow_lb o' ∗ cp_mul π d__h0 (t - o') (oGS := oGS) ∗
    (∃ r__p, RR r__p ∗ (⌜ r__p = Some o' ⌝ ∨ cp π d__h0 (oGS := oGS))) ∗
    cp_mul π d__w 10 (oGS := oGS) ∗
    let cd: tau_codom Σ := (τ, π, q, Ob, ∅, Φ, RR) in
    ticket_token t ∗ ticket_tau t cd
    ∗ th_phase_frag τ π (q / 2) (oGS := oGS)
  .

  (* TODO: move, remove duplicates *)
  Ltac remember_goal :=
  match goal with | |- envs_entails _ ?P =>
    iAssert (P -∗ P)%I as "GOAL"; [iIntros "X"; by iApply "X"| ]
  end.

  (* TODO: mention exc_lb in the proof OR implement its increase *)
  Lemma get_ticket_spec s (lk: val) c (τ: locale heap_lang) π q
    (Φ: ofe_mor val (iProp Σ))
    (Ob: gset SignalId) (RR: ofe_mor (option nat) (iProp Σ))
    (LIM_STEPS': fl_B TLPre c <= LIM_STEPS):
    tl_is_lock lk c ∗ exc_lb 20 (oGS := oGS) ⊢
        TAU_FL τ
        (acquire_at_pre lk (FLP := TLPre) (FLG := TLG))
        (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        ∅
        (fun '(_, _, b) => b = false)
        c π q (fun _ _ => Φ #())
        Ob RR
        (oGS := oGS) (FLP := TLPre)
        -∗
        TLAT_pre τ ∅ d__e RR π q Ob (oGS := oGS) -∗
        cp_mul π d__w 10 (oGS := oGS) -∗
        WP (get_ticket lk) @ s; τ; ⊤ {{ tv, ∃ (t o': nat), ⌜ tv = #t ⌝ ∗ wait_res o' t τ π q Ob Φ RR }}.
  Proof using OBLS_AMU fl_degs_wl0.
    clear ODl ODd LEl.
    iIntros "[#INV #EB]". rewrite /TLAT_FL /TLAT.
    iIntros "TAU PRE CPS".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(RR0 & OB & _ & PH & CPe)".
    rewrite /get_ticket.

    (* pure_step_hl. MU_by_BMU. *)
    (* iApply (BMU_lower _ 2). *)
    (* { simpl. lia. } *)
    (* iApply OU_BMU. iApply (OU_wand with "[-CP PH]"). *)
    (* 2: { (* TODO: can we remove phase restriction for exchange? *) *)
    (*      iApply (exchange_cp_upd with "[$] [$] [$]"). *)
    (*      1, 2: reflexivity. *)
    (*      apply fl_degs_hm. } *)
    (* iIntros "[CPSh PH]". iDestruct (cp_mul_take with "CPSh") as "[CPSh CPh]".  *)
    (* iApply OU_BMU. iApply (OU_wand with "[-CPw PH]"). *)
    (* 2: { iApply (exchange_cp_upd with "[$] [$] [$]"). *)
    (*      1, 2: reflexivity. *)
    (*      trans d__h0; eauto. } *)
    (* iIntros "[CPS PH]". BMU_burn_cp. *)
    pure_steps.

    (* TODO: ??? worked fine when get_ticket was inlined into tl_acquire *)
    (* wp_bind (Snd _)%E. *)
    assert (FAA (Snd lk) #1 = fill_item (FaaLCtx #(LitInt 1)) (Snd lk)) as CTX by done.
    iApply (wp_bind [(FaaLCtx #1)] s ⊤ τ (Snd lk) (Λ := heap_lang)). simpl.
    
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & #EBd & >OW & >TK & >EXACT & >HELD & >TOKS & >%DOM__TM & TM & TAUS & RTOK)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    rewrite /TAU_FL. rewrite TAU_elim. iMod "TAU" as (st) "[[ST %ST__lk] TAU]".
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_faa with "TK").
    iIntros "!> TK'". iNext. MU_by_BMU.
    simpl. rewrite (Nat.add_comm _ 3). iApply OU_BMU.
    (* iDestruct (cp_mul_take with "CPSw") as "[CPSw CPw]". *)
    apply Nat.le_sum in LEot as [d ->].
    iApply (OU_wand with "[-CPe PH]").
    2: { iApply (exchange_cp_upd with "[$] [$]").
         { apply (Nat.le_refl (S (S d))). }
         { done. }
         { apply fl_degs_he. }
         rewrite Nat.sub_add'. by rewrite Nat.add_comm. }
    iIntros "[CPSh PH]".
    iDestruct (cp_mul_take with "CPSh") as "[CPSh CPh]".

    iApply OU_BMU. iApply (OU_wand with "[-CPh PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] EB").
         { Unshelve. 3: exact 10. lia. shelve. }
         { done. }
         etrans; [apply fl_degs_wl0 | apply fl_degs_lh0]. }
    iIntros "[CPS' PH]".

    iApply OU_BMU. iApply (OU_wand with "[-PH]").
    2: { iApply (increase_eb_upd with "EBd [$]"). }
    iClear "EBd". iIntros "[#EBd' PH]".
    
    iDestruct (ow_exact_lb with "[$]") as "[EXACT LB]".
    remember_goal.
    iMod (tokens_alloc with "[$]") as "[TOKS TOK]".
    iMod (ticket_tau_alloc with "[$]") as "[TM TK_TAU]".
    { rewrite DOM__TM. intros [_ IN]%elem_of_set_seq. simpl in IN.
      by apply Nat.lt_irrefl in IN. }
    iApply "GOAL". iClear "GOAL".

    iDestruct (th_phase_frag_halve with "PH") as "[PH PH']".
    destruct (Nat.eq_0_gt_0_cases d) as [-> | QUEUE].
    2: { BMU_burn_cp.
         rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. simpl.
         iModIntro.
         pure_steps.
         do 2 iExists _. iFrame. rewrite Nat.sub_add'.
         rewrite cp_mul_take. iDestruct "CPSh" as "[CPSh CPh]".
         iFrame.
         iApply fupd_frame_all.
         iSplitL "RR0".
         { iModIntro. iSplit; [done| ]. iSplit; [iPureIntro; lia| ].
           iExists _. iFrame. }
         iDestruct "TAU" as "[_ [_ AB]]".
         iMod ("AB" with "[ST]") as "TAU"; [by iFrame| ].
         iDestruct (TMI_extend_queue with "[$] [TAU PH OB]") as "TAUS"; eauto.
         { lia. }
         { rewrite /TAU_stored.
           Unshelve. 2: repeat eapply pair.
           simpl. iFrame "OB PH TAU".
           by iApply sgns_level_gt'_empty. }
         iClear "RTOK".
         iMod ("CLOS" with "[HELD TK' OW EXACT TOKS TAUS TM]") as "_"; [| done].
         iNext. rewrite /tl_inv_inner.
         do 5 iExists _. iFrame.
         (* Set Printing Coercions. *)
         (* Set Printing All. *)

         rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
         replace (((ow + d)%nat + 1)%Z) with (Z.of_nat $ S (ow + d)) by lia.
         iFrame. rewrite !bi.sep_assoc. iSplit.
         2: { iIntros "%". lia. }
         replace ((S (ow + d) - ow + 2)) with (S (d + 2)) by lia. iFrame "#∗".
         iPureIntro. split.
         { split; [done| lia]. }
         rewrite dom_insert_L DOM__TM.
         by rewrite set_seq_S_end_union_L. }

    rewrite (proj2 (Nat.eqb_eq _ _)); [| done]. simpl.
    iApply (BMU_lower _ (c + (0 + c))); [lia| ].
    iApply BMU_split.
    rewrite /tl_LK. destruct st as [[]]. iDestruct "ST" as (??) "(-> & OW' & HELD')".
    rewrite !Nat.add_0_r. rewrite Nat.add_0_r in DOM__TM.
    iDestruct "TAU" as "[_ [COMM _]]".
    iDestruct (held_agree with "[$] [$]") as "<-".
    rewrite /tl_LK.
    iSpecialize ("COMM" with "[OB PH']").
    { iFrame. iSplit; [done| ]. iPureIntro. by apply Qp.div_le. }

    iApply (BMU_wand with "[-COMM]"); [| done].
    iIntros "COMM".
    BMU_burn_cp. iModIntro. iApply wp_value.
    do 2 iExists _. iFrame. iApply fupd_frame_all.
    iSplitL "CPSh RR0".
    { rewrite Nat.sub_diag. iModIntro.
      iSplit; [done| ]. iSplit; [done| ]. iApply bi.sep_exist_l.
      iExists _. iFrame. rewrite bi.sep_or_l. iRight.
      by rewrite -cp_mul_take. }
    iMod (held_update _ _ true with "[$] [$]") as "[HELD HELD']".
    iMod ("COMM" $! (_, _, _) with "[HELD' OW']") as "Φ".
    { rewrite /acquire_at_post. simpl. rewrite /tl_LK.
      iFrame. iSplit; [| done]. do 2 iExists _. iFrame. done. }
    rewrite -{2}(Qp.div_2 q). rewrite Qp.add_sub. simpl.
    
    iSpecialize ("RTOK" with "[//]"). 
    iDestruct (TMI_extend_acquire _ _ _ _ (((((((_), _), _), _), _), _), _) with "[$] [$] [$]") as "TMI"; eauto.

    (* iDestruct (TMI_extend_acquire _ _ _ _ (((((τ, π), (q /2)%Qp), ∅), Φ), RR) with "[$] [$]") as "TMI"; eauto. *)

    iApply "CLOS". iNext. rewrite /tl_inv_inner.
    rewrite -(Nat.add_1_r ow).
    replace (Z.of_nat ow + 1)%Z with (Z.of_nat (ow + 1)) by lia.
    do 5 iExists _. iFrame.
    rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. iFrame.
    iFrame. rewrite !bi.sep_assoc. iSplit.
    2: { iIntros "%". lia. }
    rewrite Nat.sub_diag Nat.sub_add'. iFrame "#∗".
    iPureIntro. split.
    { split; [done| lia]. }
    rewrite dom_insert_L DOM__TM.
    rewrite set_seq_add_L. simpl.
    set_solver.
  Qed.

  (* TODO: move, remove duplicates *)
  Ltac split_cps cps_res n :=
    let fmt := constr:(("[" ++ cps_res ++ "' " ++ cps_res ++ "]")%string) in
    iDestruct (cp_mul_split' _ _ n with cps_res) as fmt; [lia| ].

  Lemma wait_spec (lk: val) c o' (t: nat) τ π q Ob Φ RR
    (LIM_STEPS': fl_B TLPre c <= LIM_STEPS):
    tl_is_lock lk c ∗ exc_lb 20 (oGS := oGS) ∗ wait_res o' t τ π q Ob Φ RR 
    ⊢ WP (wait lk #t) @ τ {{ v, Φ v ∗ rel_tok }}.
  Proof using fl_degs_wl0 OBLS_AMU.
    clear ODl ODd LEl.
    iLöb as "IH" forall (o').
    rewrite {2}/wait_res. iIntros "(#INV & #EXC & %LEo't & OW_LB & CPSh & RR & CPS & TOK & TAU & PH)".
    rewrite {2}/wait.
    pure_steps.

    wp_bind (Fst _)%E.
    (* TODO: make a lemma? and remove duplicates *)
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    wp_bind (! _)%E.
    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & #EBd & >OW & >Ltk & >EXACT & >HELD & >TOKS & >%DOM__TM & TM & TAUS & RTOK)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_load with "[OW]"); [done| ]. iIntros "!> OW".
    
    iDestruct (ticket_token_bound with "[$] [$]") as %LTttk.
    destruct (decide (ow = t)) as [-> | QUEUE].
    { rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
      iDestruct (tau_map_ticket_interp with "[$] [$] [$]") as "(TAUtk & TAU & TM & TMI_CLOS)".
      rewrite {1}/tau_interp. iDestruct "TAUtk" as "[[? %] | [[TAUtk _] | [? %]]]".
      1, 3: lia.
      simpl. iDestruct "TAUtk" as "[[Φ RTOK'] | TOK']".
      2: { by iDestruct (ticket_token_excl with "[$] [$]") as %?. }
      iSpecialize ("TMI_CLOS" with "[TOK]").
      { rewrite /tau_interp. iRight. iLeft. iSplit; [| done]. iFrame. }
      MU_by_burn_cp. iModIntro. pure_steps.
      iMod ("CLOS" with "[TMI_CLOS OW TOKS HELD EXACT Ltk TM]") as "_".
      { rewrite /tl_inv_inner. iNext. do 5 iExists _. iFrame "#∗".
        rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
        rewrite !bi.sep_assoc. iSplitL; [by iFrame| ].
        iIntros "%". lia. }
      iModIntro.

      wp_bind (Rec _ _ _)%V. pure_steps.
      wp_bind (_ = _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step.
      { simpl. tauto. }
      iNext. MU_by_burn_cp. rewrite bool_decide_eq_true_2; [| tauto].
      pure_steps. iFrame. by iApply "Φ". }

    iDestruct (tau_map_ticket_interp with "[$] [$] [$]") as "(TAUtk & TAU & TM & TMI_CLOS)".
    rewrite {1}/tau_interp.
    apply Nat.le_lteq in LEot as [LTot | EQ].
    2: { subst tk. iDestruct "TAUtk" as "[[? %] | [[? %] | [? %]]]".
         all: try lia.
         by iDestruct (ticket_token_excl with "[$] [$]") as %?. }

    iDestruct "TAUtk" as "[[TAUs %] | [[? %] | [? %]]]".
    all: try lia.
    2: { by iDestruct (ticket_token_excl with "[$] [$]") as %?. }
    rewrite (proj2 (Nat.eqb_neq _ _)); [| lia].
    rewrite /TAU_stored. iDestruct "TAUs" as "(OB & #SLT & PH' & TAUs)".
    rewrite /tl_TAU /TAU_FL. rewrite TAU_elim.
    rewrite /TAU_acc. iNext. MU_by_BMU.
    iApply BMU_invs. simpl.
    iMod "TAUs" as ([[lk_ r] b]) "[PRE [WAIT _]]".
    rewrite /acquire_at_pre. simpl. iDestruct "PRE" as "[>(%&%&%EQ&OW'&HELD') ->]".
    inversion EQ. subst l__ow0 l__tk0. clear EQ.
    iDestruct (held_agree with "[$] [$]") as %<-.
    iDestruct (mapsto_agree with "[$] [$]") as %EQ. inversion EQ as [EQ'].
    apply Nat2Z.inj' in EQ'. subst r. clear EQ.
    iDestruct (ow_lb_le_exact with "[$] [$]") as %LBow.
    replace (t - o') with (t - ow + (ow - o')) by lia.
    rewrite cp_mul_split. iDestruct "CPSh" as "[CPSh CPSh']".
    iSpecialize ("WAIT" with "[OB PH RR CPSh']").
    { iFrame. iSplitR.
      { rewrite /sgns_level_ge'. set_solver. }
      iSplit.
      { iPureIntro. by apply Qp.div_le. }
      iSplit; [| done].
      iDestruct "RR" as (r) "[RR RR']". iExists _. iFrame.
      iDestruct "RR'" as "[-> | ?]"; [| by iFrame].
      apply Nat.le_sum in LBow as [d ->]. rewrite Nat.sub_add'.
      destruct d.
      - rewrite Nat.add_0_r. by iLeft.
      - rewrite cp_mul_take. iDestruct "CPSh'" as "[??]". iFrame. }
    iModIntro.
    iApply (BMU_lower _ (c + (3 + c))); [lia| ].
    iApply BMU_split. iApply (BMU_wand with "[-WAIT] [$]").
    iIntros "(RR & CP & PH & OB & CLOS')".
    iSpecialize ("CLOS'" with "[OW' HELD']").
    { iFrame. iSplit; [| done]. iNext. do 2 iExists _. iFrame. eauto. }
    iApply OU_BMU.
    iApply (OU_wand with "[-CP PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] EXC").
         1, 2: reflexivity.
         apply fl_degs_wl0. }
    iIntros "[CPS' PH]".
    iDestruct (cp_mul_split with "[CPS CPS']") as "CPS"; [iFrame| ]. simpl.
    iApply BMU_intro. iMod "CLOS'" as "TAUs". iModIntro.
    (* rewrite cp_mul_take. iDestruct "CPS" as "[CPS CP]". *)
    split_cps "CPS" 1. rewrite -cp_mul_1. 
    iSplitR "CPS'".
    2: { do 2 iExists _. iFrame. done. }
    iModIntro. pure_steps.
    iSpecialize ("TMI_CLOS" with "[TAUs SLT OB PH']").
    { rewrite /tau_interp. iLeft. iSplit; [| done].
      rewrite /TAU_stored. by iFrame. }
    iClear "OW_LB". iDestruct (ow_exact_lb with "[$]") as "[EXACT OW_LB]".
    iMod ("CLOS" with "[TMI_CLOS OW TOKS HELD EXACT Ltk TM]") as "_".
    { rewrite /tl_inv_inner. iNext. do 5 iExists _. iFrame.
      rewrite (proj2 (Nat.eqb_neq _ _)); [| lia]. iFrame "#∗".
      rewrite !bi.sep_assoc. iSplit.
      { iPureIntro. repeat split; eauto. lia. }
      iIntros "->". lia. }
    iModIntro.
    wp_bind (Rec _ _ _)%V. pure_steps.
    wp_bind (_ = _)%E.
    iApply sswp_MU_wp; [done| ].
    iApply sswp_pure_step.
    { simpl. tauto. }
    iNext. MU_by_burn_cp. rewrite bool_decide_eq_false_2.
    2: { intros [=EQ%Nat2Z.inj']. lia. }
    do 2 pure_step_cases.

    iApply ("IH" $! ow).
    iFrame "#∗". iSplit; [iPureIntro; lia| ]. iSplitL "RR".
    { iExists _. iFrame. by iLeft. }
    replace 21 with (10 + 11) by lia. rewrite cp_mul_split.
    iDestruct "CPS" as "[??]". iFrame.
  Qed.

  Lemma rel_tok_excl: rel_tok -∗ rel_tok -∗ ⌜ False ⌝.
  Proof using.
    iStartProof. rewrite bi.wand_curry -own_op.
    iIntros "X". by iDestruct (own_valid with "[$]") as %V.
  Qed.

  Lemma tau_map_interp_update (TM: gmap nat (tau_codom Σ)) (l__ow l__tk: loc) c (ow: nat)
    (lk := (#l__ow, #l__tk)%V)
    (next := bool_decide (ow + 1 ∈ dom TM)):
    tau_map_interp lk c ow TM -∗ held_auth false -∗
    l__ow ↦{/ 2} #(ow + 1)%nat -∗ rel_tok -∗
    BMU (⊤ ∖ ↑tl_ns) c (held_auth next ∗ l__ow ↦{/ 2} #(ow + 1)%nat ∗
                        (⌜ next = false ⌝ → rel_tok) ∗
                        tau_map_interp lk c (ow + 1) TM) (oGS := oGS).
  Proof using.
    clear fl_degs_wl0 d__w ODl ODd LEl OBLS_AMU.
    iIntros "TMI AUTH LOW RTOK". rewrite /tau_map_interp.

    (* rewrite {1 4}(map_split TM ow). *) rewrite (map_split TM ow).
    rewrite !big_opM_union.
    2, 3: apply map_disjoint_dom; destruct lookup; set_solver.
    iDestruct "TMI" as "[OW TMI]".

    rewrite (map_split (delete _ _ ) (ow + 1)).
    rewrite !big_opM_union.
    2, 3: apply map_disjoint_dom; destruct lookup; set_solver.
    iDestruct "TMI" as "[OW' TMI]".
    rewrite !bi.sep_assoc. iApply (BMU_frame_r with "[TMI]").
    { iApply (big_sepM_impl with "[$]").
      iIntros "!>" (i cd ITH) "TI".
      apply lookup_delete_Some in ITH as [? [? ITH]%lookup_delete_Some].
      rewrite /tau_interp. destruct cd as [[[[[[]]]]]].
      iDestruct "TI" as "[[? %] | [[? %] | [? %]]]"; try lia.
      - iLeft. iFrame. iPureIntro. lia.
      - do 2 iRight. iFrame. iPureIntro. lia. }
    rewrite -bi.sep_assoc bi.sep_comm -bi.sep_assoc.
    iPoseProof BMU_frame_l as "foo". rewrite bi.wand_curry. iApplyHyp "foo".

    iApply (bi.wand_frame_l with "[-RTOK OW]").
    2: { destruct (TM !! ow) as [cd| ] eqn:OW.
         2: { iSplitR "RTOK"; [| iAccu]. set_solver. }
         simpl. rewrite !big_sepM_singleton.
         rewrite /tau_interp. destruct cd as [[[[[[]]]]]].
         iDestruct "OW" as "[[? %] | [[OW %] | [? %]]]"; try lia.
         iDestruct "OW" as "[CD | TT]".
         { iDestruct "CD" as "[_ RT]".
           by iDestruct (rel_tok_excl with "[$] [$]") as "?". }
         iFrame. do 2 iRight. iFrame. iPureIntro. lia. }
    iIntros "RTOK".
    rewrite !lookup_delete_ne; [| lia].
    destruct (TM !! (ow + 1)) as [[[[[[[]]]]]]| ] eqn:OW'; simpl; subst next.
    2: { rewrite bool_decide_eq_false_2; [| by apply not_elem_of_dom].
         iApply BMU_intro. iFrame. set_solver. }
    simpl. rewrite bool_decide_eq_true_2; [| by apply elem_of_dom].
    rewrite !big_sepM_singleton.
    rewrite {1}/tau_interp. iDestruct "OW'" as "[[TAU %] | [[? %] | [? %]]]"; try lia.
    rewrite /TAU_stored. iDestruct "TAU" as "(OB' & #SLT' & PH' & TAUs')". simpl.
    rewrite /tl_TAU /TAU_FL. rewrite TAU_elim. simpl.
    rewrite /TAU_acc.
    
    iApply BMU_invs.
    iMod "TAUs'" as ([[lk_ r] b]) "[PRE [_ [COMM _]]]". iModIntro.

    rewrite /acquire_at_pre. simpl.
    remember_goal.
    iDestruct "PRE" as "[>(%&%&%EQ&LOW'&HELD') ->]".
    iApply "GOAL". iClear "GOAL".
    subst lk. inversion_clear EQ.
    iDestruct (held_agree with "[$] [$]") as %<-.
    iDestruct (mapsto_agree with "LOW LOW'") as %EQ.
    inversion EQ as [EQ'']. assert (r = ow + 1) as -> by lia. clear EQ'' EQ.
    iSpecialize ("COMM" with "[$OB' $PH']").
    { iPureIntro. split; [done| ]. by apply Qp.div_le. }
    iApply (BMU_wand with "[-COMM] [$]"). iIntros "CLOS'".
    iMod (held_update _ _ true with "[$] [$]") as "[HELD HELD']".
    iFrame "HELD LOW".
    iMod ("CLOS'" $! (_, ow + 1, true) with "[-RTOK]").
    { rewrite /acquire_at_post. simpl. iSplit; [| done].
      rewrite Nat2Z.inj_add. do 2 iExists _. iFrame. eauto. }
    iModIntro. rewrite /tau_interp.
    iSplitL.
    2: { by iIntros "%". }
    iRight. iLeft.
    rewrite -{1}(Qp.div_2 q). rewrite Qp.add_sub. simpl.
    iSplit; [| done]. iLeft. iFrame.
  Qed.

  (* TODO: move *)
  Lemma exc_lb_le n m
    (LE: n <= m):
    exc_lb m (oGS := oGS) ⊢ exc_lb n (oGS := oGS).
  Proof using.
    rewrite /exc_lb. erewrite mono_nat_lb_op_le_l; eauto.
    rewrite own_op. by iIntros "[??]". 
  Qed.

  (* TODO: mention exc_lb in the proof OR implement its increase *)
  Lemma tl_release_spec (lk: val) c τ:
    tl_is_lock lk c ∗ exc_lb 20 (oGS := oGS) ∗ rel_tok ⊢
        TLAT_FL τ
        (release_at_pre lk (FLP := TLPre) (FLG := TLG))
        (release_at_post lk (FLP := TLPre) (FLG := TLG))
        ∅
        (fun _ => True%type)
        (fun _ _ => None)
        (fun _ '(_, r, _) => #r)
         c
         (tl_release lk)
        (oGS := oGS)
        (FLP := TLPre).
  Proof using fl_degs_wl0 OBLS_AMU.
    clear ODl ODd LEl.
    iIntros "(#INV & #EB & RT)". rewrite /TLAT_FL /TLAT.
    iIntros (Φ q π Ob RR) "%LIM_STEPS' PRE TAU".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(RR0 & OB & _ & PH & CP)".
    rewrite /tl_release.

    pure_step_hl. MU_by_BMU.
    iApply (BMU_lower _ 2).
    { simpl. lia. }
    iApply OU_BMU. iApply (OU_wand with "[-CP PH]").
    2: { (* TODO: can we remove phase restriction for exchange? *)
         iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         trans d__e; [trans d__h0| ]; [trans d__l0|..]; eauto. }
    iIntros "[CPS PH]". BMU_burn_cp.

    assert (FAA (Fst lk) #1 = fill_item (FaaLCtx #(LitInt 1)) (Fst lk)) as CTX by done.
    iApply (wp_bind [(FaaLCtx #1)] NotStuck ⊤ τ (Fst lk) (Λ := heap_lang)). simpl.
    iApply wp_atomic.
    iMod (fupd_mask_subseteq _) as "CLOS'"; [| iInv "INV" as "inv" "CLOS"]; [set_solver| ].
    iModIntro. rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (l__ow l__tk ???) "[>%EQ inv]". subst lk.
    pure_steps. iMod ("CLOS" with "[inv]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _. iFrame. done. }
    iMod "CLOS'" as "_". iModIntro.
    clear TM ow tk.

    iApply wp_atomic.
    iInv "INV" as "inv" "CLOS". rewrite {1}/tl_inv_inner.
    iDestruct "inv" as (?? ow tk TM) "(>%EQ_ & >%LEot & >#EBD & >OW & >Ltk & >EXACT & >HELD & >TOKS & >%DOM__TM & TM & TAUS & _)".
    inversion EQ_. subst l__ow0 l__tk0. clear EQ_.
    iModIntro.
    iApply sswp_MU_wp_fupd; [done| ].
    rewrite TAU_elim.
    iMod "TAU" as ([[]]) "[ST TAU]". iModIntro.
    rewrite /release_at_pre. simpl.
    remember_goal.
    iDestruct "ST" as "(>(%&%&%&OW'&HELD')&[% %EQ])". subst.
    iApply "GOAL". iClear "GOAL".
    inversion EQ. subst. clear EQ.
    iDestruct (mapsto_agree with "OW OW'") as %EQ. inversion EQ as [EQ'].
    apply Nat2Z.inj' in EQ'. subst n. clear EQ.
    iCombine "OW OW'" as "OW". rewrite Qp.inv_half_half.
    iDestruct (held_agree with "[$] [$]") as %EQ.
    destruct Nat.eqb eqn:EQ'; [done| ]. apply PeanoNat.Nat.eqb_neq in EQ'. clear EQ.
    iApply (wp_faa with "[$]"). iIntros "!> OW".
    iDestruct "TAU" as "[_ [TAU _]]".
    iNext. MU_by_BMU.
    iSpecialize ("TAU" with "[$OB $PH]").
    { done. }    
    simpl. rewrite -Nat.add_assoc. iApply BMU_split.
    iApply (BMU_wand with "[-TAU] [$]"). iIntros "CLOS'". rewrite -Nat.add_assoc.
    iSpecialize ("CLOS'" $! (_, (ow + 1), false)).
    remember_goal.
    iMod (held_update _ _ false with "[$] [$]") as "[HELD HELD']".
    iMod (ow_exact_increase _ (ow + 1) with "[$]") as "[EXACT OW_LB]"; [lia| ].
    iApply "GOAL". iClear "GOAL".
    
    rewrite -{2}Qp.inv_half_half. rewrite mapsto_fractional. iDestruct "OW" as "[OW OW']".
    iSpecialize ("CLOS'" with "[OW' HELD']").
    { rewrite /release_at_post. simpl. iSplit; [| by eauto].
      do 2 iExists _. iSplitR; [by eauto| ]. iFrame.
      Set Printing Coercions.
      by rewrite Nat2Z.inj_add. }

    iApply BMU_proper.
    1, 2: reflexivity.
    { apply bi.sep_comm. }
    iDestruct (cp_mul_take with "CPS") as "[CPS CP]".
    iApply (BMU_frame_l with "[CP]").
    { do 2 iExists _. by iFrame. }
    iApply (BMU_mask_comm with "[-CLOS'] [$]"); [set_solver| ].
    iIntros "Φ". simpl.

    iPoseProof (tau_map_interp_update with "[$] [$] [OW] [$]") as "UPD".
    { by rewrite Nat2Z.inj_add. }
    iApply BMU_split. iApply (BMU_wand with "[-UPD] [$]"). iIntros "(HELD & OW & RTOK & TMI)".
    rewrite Qp.sub_diag. simpl. iSpecialize ("Φ" with "[//]"). 
    iApply BMU_intro. pure_steps.
    iMod ("CLOS" with "[-Φ RR0 CPS OW_LB]") as "_".
    { iNext. rewrite /tl_inv_inner. do 5 iExists _.
      iRevert "EBD". iFrame. iIntros "#EBd".
      iSplit; [done| ]. iSplit; [iPureIntro; lia| ].
      erewrite bool_decide_ext with (Q := ow + 1 ≠ tk). 
      2: { rewrite DOM__TM elem_of_set_seq. simpl. lia. }
      iSplitR.
      { iApply (exc_lb_le with "EBd"). lia. }
      rewrite bi.sep_assoc. iSplitR "RTOK".
      2: { iApply bi.impl_proper; [..| done | by iFrame].
           rewrite bool_decide_eq_false. iPureIntro. tauto. }
      iSplit; [| done].
      rewrite /held_auth. erewrite Excl_proper; [by iFrame| ].
      destruct Nat.eqb eqn:OW'.
      - apply Nat.eqb_eq in OW'. apply bool_decide_eq_false. lia.
      - apply Nat.eqb_neq in OW'. apply bool_decide_eq_true. lia. }

    iModIntro. by iApply "Φ".
  Qed.

  (* TODO: mention exc_lb in the proof OR implement its increase *)
  Lemma tl_acquire_spec (lk: val) c τ:
    tl_is_lock lk c ∗ exc_lb 20 (oGS := oGS) ⊢
        TLAT_FL τ
        (acquire_at_pre lk (FLP := TLPre) (FLG := TLG))
        (acquire_at_post lk (FLP := TLPre) (FLG := TLG))
        ∅
        (fun '(_, _, b) => b = false)
        (fun _ _ => Some rel_tok)
        (fun _ _ => #())
        c (tl_acquire lk)
        (oGS := oGS)
        (FLP := TLPre).
  Proof using fl_degs_wl0 d__w OBLS_AMU.
    clear ODl ODd LEl. 
    iIntros "[#INV #EB]". rewrite /TLAT_FL /TLAT.
    iIntros (Φ q π Ob RR) "%LIM_STEPS' PRE TAU".
    rewrite /TLAT_pre. simpl. iDestruct "PRE" as "(RR0 & OB & _ & PH & CP)".

    rewrite /tl_acquire. pure_step_hl. MU_by_BMU.
    iApply (BMU_lower _ 3).
    { simpl. lia. }
    iApply OU_BMU. iApply (OU_wand with "[-CP PH]").
    2: { (* TODO: can we remove phase restriction for exchange? *)
         iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         apply fl_degs_em. }
    iIntros "[CPSe PH]". iDestruct (cp_mul_take with "CPSe") as "[CPSe CPe]".
    iApply OU_BMU. iApply (OU_wand with "[-CPe PH]").
    2: { iApply (exchange_cp_upd with "[$] [$] [$]").
         1, 2: reflexivity.
         apply fl_degs_he. }
    iIntros "[CPSh PH]". iDestruct (cp_mul_take with "CPSh") as "[CPSh CPh]".
    iApply OU_BMU. iApply (OU_wand with "[-CPh PH]").
    2: { iApply (exchange_cp_upd _ _ _ _ _ d__w with "[$] [$] [$]").
         1, 2: reflexivity.
         do 2 (etrans; eauto). }
    iIntros "[CPS PH]". BMU_burn_cp.
    replace 19 with (10 + 9) at 4 by lia. iDestruct (cp_mul_split with "CPS") as "[CPS1 CPS]".

    Set Printing Coercions.
    (* set (post :=  (fun x => bi_wand (th_phase_frag τ π (q /2) (oGS := oGS)) (Φ x)): ofe_car valO → ofe_car (iPropO Σ)). *)
    set (post := (fun x => bi_wand rel_tok (Φ x)) : ofe_car valO → ofe_car (iPropO Σ)). 
    assert (NonExpansive post) as NE_Φ by apply _.
    assert (NonExpansive RR) as NE_RR.
    { (* TODO: why it's not inferred automatically? *)
      simpl in *.
      red. intros ????.
      apply discrete_iff in H.
      2: by apply _.
      apply leibniz_equiv_iff in H. by subst. }
    pure_steps.
    rewrite cp_mul_take. iDestruct "CPSe" as "[CPSe CPe]".
    iApply (wp_wand with "[TAU OB PH CPe RR0 CPS1]").
    { iApply (get_ticket_spec with "[$] [TAU] [OB PH CPe RR0] [$]").
      { done. }
      { simpl. rewrite /TAU_FL. simpl.
        iApply (TAU_Proper with "[$]").
        all: try reflexivity.
        Unshelve. 4: by econstructor; apply NE_RR. 3: by econstructor; apply NE_Φ.
        all: done. }
      rewrite /TLAT_pre. iFrame. iApply sgns_level_gt'_empty. }
    simpl. iIntros (?) "(%&%&->&WR)".
    rewrite /wait_res. rewrite !bi.sep_assoc. iDestruct "WR" as "[WR_ PH]".

    wp_bind (Rec _ _ _)%V.
    do 3 pure_step_cases.
    iApply (wp_wand with "[WR_ PH]").
    { iApply wait_spec; eauto.
      rewrite -!bi.sep_assoc. iDestruct "WR_" as "(?&?&?&?&?&?&?)".
      iFrame "#∗". }

    subst post. simpl. iIntros (?) "[POST ?]". by iApply "POST".
  Qed.
  
End Ticketlock.
