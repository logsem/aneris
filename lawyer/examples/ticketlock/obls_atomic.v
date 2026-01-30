From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From lawyer Require Import sub_action_em.


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

  Context `{oGS': @asem_GS _ _ ASEM Σ}.
  Let oGS: ObligationsGS (OP := OP) Σ := oGS'.
  Existing Instance oGS.

  Let Locale := locale heap_lang. 

  Section AtomicTriples. 

    Context
      {ST: Type}
      (τ: Locale)
      (P: ST -> iProp Σ)
      (Q: ST -> ST -> iProp Σ) (** second ST is the previous state *)
      (L: gset Level)
      (d__m: Degree)
      (c: nat) (B: nat -> nat)
      (ε__m: coPset)
    .

    Record AbortClause := {
        ac_pre: ST -> iProp Σ;
        ac_post: ST -> iProp Σ;
    }.

    Definition AC_RR {RO: Type} d__l π
      (round: ST -> RO) (cond: ST -> iProp Σ)
      (RR: option RO -> iProp Σ) (d__h: Degree): AbortClause := {|
        ac_pre := fun x => (cond x ∗ (RR (Some $ round x) ∨ cp π d__h))%I;
        ac_post := fun x => (RR (Some $ round x) ∗ cp π d__l)%I;
    |}.

    Definition AC_none: AbortClause := {|
      ac_pre := fun _ => (False)%I; ac_post := fun _ => (False)%I;
    |}.

    Definition AC_always π d__l: AbortClause := {|
      ac_pre := fun _ => (True)%I; ac_post := fun _ => (cp π d__l)%I;
    |}.

    Section AtomicUpdates.
      Context
        (ε: coPset)
        (π: Phase)
        (q0: Qp)
        (Φ: ST -> ST -> iProp Σ)
        (O: gset SignalId)
        (ac: AbortClause)
      .

      Definition TAU_acc (V: iProp Σ): iProp Σ :=
        |={ε, ∅}=> ∃ x, P x ∗ (
              let abort := P x ={∅, ε}=∗ V in
              let PH q := th_phase_frag τ π q in
              (∀ O' q', obls τ O' ∗ sgns_levels_ge' O' L ∗ 
                        PH q' ∗ ⌜ Qp.le q' q0 ⌝ ∗
                        ac_pre ac x -∗
                      BOU ∅ c (
                        ac_post ac x ∗ 
                        PH q' ∗
                        obls τ O' ∗
                        abort
                      )
              ) ∧
              (∀ q',
                 obls τ O
                 ∗ PH q' ∗ ⌜ Qp.le q' q0 ⌝
                 -∗
                 ∀ y, Q y x -∗
               BOU ∅ c (
                  |={∅, ε}=> (from_option PH ⌜ True ⌝ (Qp.sub q0 q') -∗ Φ y x))) ∧
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
          iApply (BOU_wand with "[-T1]"); [| done].
          iIntros "(?&?&?&AB)". iFrame.
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

      Definition TAU := TAU_def.
      
      Lemma TAU_elim:
        TAU ⊣⊢ TAU_acc TAU.
      Proof using.
        rewrite /TAU /TAU_def /=. apply: greatest_fixpoint_unfold.
      Qed.

      Lemma TAU_intro U V:
        Persistent U →
        (U ∧ V ⊢ TAU_acc V) → U ∧ V ⊢ TAU.
      Proof using.
        rewrite /TAU /TAU_def /=.
        iIntros (? HAU) "[#HP HQ]".
        iApply (greatest_fixpoint_coiter _ (λ _, V)); last done.
        iIntros "!>" ([]) "HQ".
        iApply HAU. iSplit; by iFrame.
      Qed.

    End AtomicUpdates.

    Definition ac_equiv ac1 ac2: Prop :=
      (∀ r, ac_pre ac1 r ≡ ac_pre ac2 r) /\ (∀ r, ac_post ac1 r ≡ ac_post ac2 r).

    Lemma ac_equiv_sym ac1 ac2:
      ac_equiv ac1 ac2 -> ac_equiv ac2 ac1.
    Proof using.
      intros (X&Y). split; symmetry; auto. 
    Qed.
    
    Lemma TAU_acc_proper'_impl E π q Ob
      Φ1 Φ2 ac1 ac2 (V1 V2: iProp Σ):
      (∀ y x, Φ1 y x ≡ Φ2 y x) -∗ ⌜ ac_equiv ac1 ac2 ⌝ -∗ (V1 ≡ V2) -∗
        TAU_acc E π q Φ1 Ob ac1 V1 -∗ TAU_acc E π q Φ2 Ob ac2 V2.
    Proof using. 
      iIntros "#EQ_Φ #(%EQ_WPRE & %EQ_WPOST) #EQ_V TAU". rewrite /TAU_acc.

      iMod "TAU" as (?) "[P T1]". iModIntro. iExists _. iFrame "P".
      iSplit; [| iSplit].
    - iIntros (??) "X". iDestruct "T1" as "[T1 _]".
      iApply (BOU_wand with "[]").
      2: { iApply "T1". iDestruct "X" as "(?&?&?&?&X)". iFrame.
           by rewrite EQ_WPRE. }
      iIntros "(C&?&?& VV)".
      rewrite EQ_WPOST. 
      iFrame.      
      iRewrite "EQ_V" in "VV". iFrame. 
    - iDestruct "T1" as "[_ [T1 _]]".
      iIntros (?) "(?&?&%)". iIntros (?) "Q".
      iApply (BOU_wand with "[]").
      2: { iApply ("T1" with "[-Q] [$]"). iFrame. done. }
      iIntros "P". 
      iMod "P". iModIntro. by iRewrite -("EQ_Φ" $! y x).
    - iRewrite -"EQ_V". 
      by iDestruct "T1" as "[_ [_ T1]]".
    Qed.
   
    Lemma TAU_acc_proper' E π q Ob
      Φ1 Φ2 ac1 ac2 (V1 V2: iProp Σ):
      (∀ y x, Φ1 y x ≡ Φ2 y x) -∗ ⌜ ac_equiv ac1 ac2 ⌝ -∗ (V1 ≡ V2) -∗
        TAU_acc E π q Φ1 Ob ac1 V1 ∗-∗ TAU_acc E π q Φ2 Ob ac2 V2.
    Proof using.
      iIntros "#EQ_Φ %EQ_RR #EQ_V". iSplit; iApply TAU_acc_proper'_impl; (iFrame "#∗" || (try (iIntros; iApply internal_eq_sym; by iFrame "#∗"))).
      all: iPureIntro; done || by apply ac_equiv_sym. 
    Qed.

    Lemma TAU_proper'_impl E π q Ob
      Φ1 Φ2 ac1 ac2:
      (∀ y x, Φ1 y x ≡ Φ2 y x) -∗ ⌜ ac_equiv ac1 ac2 ⌝ -∗
        TAU E π q Φ1 Ob ac1 -∗ TAU E π q Φ2 Ob ac2.
    Proof using.
      iIntros "#EQ_Φ #EQ_RR".
      iDestruct (greatest_fixpoint_strong_mono with "[]") as "X".
      2: by iFrame.
      iModIntro. iIntros. iApply (TAU_acc_proper'_impl with "[$] [$] [//] [$]").
    Qed.

    Lemma TAU_proper' E π q Ob
      Φ1 Φ2 ac1 ac2:
      (∀ y x, Φ1 y x ≡ Φ2 y x) -∗ ⌜ ac_equiv ac1 ac2 ⌝ -∗
        TAU E π q Φ1 Ob ac1 ∗-∗ TAU E π q Φ2 Ob ac2.
    Proof using.
      iIntros "#EQ_Φ %EQ_RR".
      iSplit; iApply TAU_proper'_impl; (iFrame "#∗" || (try (iIntros; iApply internal_eq_sym; by iFrame "#∗"))).
      all: iPureIntro; try done || by apply ac_equiv_sym.
    Qed.

    Context `{EM: ExecutionModel heap_lang M}. 
    Context `{hGS: @heapGS Σ _ EM}.
    Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

    Definition TLAT_pre
      π q (O: gset SignalId): iProp Σ :=
      obls τ O ∗ sgns_levels_gt' O L ∗
      th_phase_frag τ π q ∗ cp π d__m.

    (** we have to use a separate definition for rounds-based TLAT,
        since the round resource is quantified over and chosen by the client *)

    Definition TLAT e s
      ac
      (POST: ST -> ST -> option (iProp Σ))
      (get_ret: ST -> ST -> val)
      : iProp Σ :=
      ∀ Φ q π O,
        ⌜ B c <= LIM_STEPS ⌝ -∗ TLAT_pre π q O -∗
        TAU (⊤ ∖ ε__m) π q (fun y x => POST y x -∗? Φ (get_ret y x)) O ac -∗
        WP e @ s; τ; ⊤ {{ v, Φ v }}.

    Definition TLAT_RR {RO: Type} e s
      d__h d__l
      round cond
      (POST: ST -> ST -> option (iProp Σ))
      (get_ret: ST -> ST -> val)
      : iProp Σ :=
      ∀ Φ q π O (RR: option RO -> iProp Σ),
        let ac := AC_RR d__l π round cond RR d__h in
        ⌜ B c <= LIM_STEPS ⌝ -∗ TLAT_pre π q O -∗
        TAU (⊤ ∖ ε__m) π q (fun y x => POST y x -∗? Φ (get_ret y x)) O ac -∗
        WP e @ s; τ; ⊤ {{ v, Φ v }}.

  End AtomicTriples.

  Global Instance TAU_acc_Proper {ST: Type}:
    Proper
      (eq ==> (eq ==> equiv) ==> (eq ==> eq ==> equiv) ==> equiv ==> 
       eq ==> eq ==> eq ==> eq ==>
       (eq ==> eq ==> equiv ) ==> equiv ==> ac_equiv ==> equiv ==>
       equiv) (TAU_acc (ST := ST)).
  Proof using.
    red.
    rewrite /respectful.
    intros ?? -> ?? EQUIV_P ?? EQUIV_Q ?? ->%leibniz_equiv_iff.
    intros ?? -> ?? -> ?? -> ?? -> ?? EQ' ?? ->%leibniz_equiv_iff.
    intros ?? (EQ_WPRE & EQ_WPOST) ?? EQUIV_V.    
    rewrite /TAU_acc.
    iApply fupd_proper. 
    iApply bi.exist_proper. iIntros (?).
    iApply bi.sep_proper; [by eauto| ].
    iApply bi.and_proper.
    { do 2 (iApply bi.forall_proper; iIntros (?)).
      iApply bi.wand_proper.
      { repeat iApply bi.sep_proper; try done. }
      rewrite EQ_WPOST.
      erewrite EQUIV_P; [| reflexivity]. rewrite EQUIV_V. reflexivity.  
    }
    rewrite EQUIV_P; [| done]. 
    iApply bi.and_proper.
    2: { solve_proper. }
    iApply bi.forall_proper; iIntros (?).
    setoid_rewrite EQUIV_Q. 2, 3: reflexivity. 
    setoid_rewrite EQ'. 2, 3: reflexivity.
    reflexivity. 
  Qed.

  Global Instance TAU_Proper {ST: Type}:
    Proper
      (eq ==> (eq ==> equiv) ==> (eq ==> eq ==> equiv) ==> equiv ==> 
       eq ==> eq ==> eq ==> eq ==>
       (eq ==> eq ==> equiv ) ==> equiv ==> ac_equiv ==> equiv)
      (TAU (ST := ST)).
  Proof using.
    rewrite /TAU /TAU_def.
    red. repeat intro. subst.
    eapply greatest_fixpoint_proper; [| done].
    repeat intro. rewrite /TAU_pre. iApply TAU_acc_Proper; eauto.
  Qed.

End TotalTriples.
