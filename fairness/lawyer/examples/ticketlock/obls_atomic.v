From iris.proofmode Require Import tactics coq_tactics.
From iris.bi.lib Require Import fixpoint.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic.
From trillium.fairness.lawyer Require Import sub_action_em.


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
  (* Context {oGS: @asem_GS _ _ ASEM Σ}. *)
  (* Keeping the more general interface for future developments *)
  Context `{oGS': @asem_GS _ _ ASEM Σ}.
  Let oGS: ObligationsGS (OP := OP) Σ := oGS'.
  Existing Instance oGS.

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
              let PH q := th_phase_frag τ π q in
              (let r := round x in
               ∀ O' q', obls τ O' ∗ sgns_levels_ge' O' L ∗ 
                        PH q' ∗ ⌜ Qp.le q' q0 ⌝ ∗
                      (∃ r__p, RR r__p ∗ (⌜ r__p = Some r ⌝ ∨ cp π d__h)) ∗
                      ⌜ ¬ TGT x ⌝ -∗
                      BMU ∅ c (oGS' := oGS) (
                        RR (Some r) ∗ cp π d__l ∗ PH q' ∗
                        obls τ O' ∗
                        abort
                      )
              ) ∧
              (∀ q',
               (* (∃ r__p, RR r__p) ∗ *)
               ⌜ TGT x ⌝ ∗ obls τ O
                 ∗ PH q' ∗ ⌜ Qp.le q' q0 ⌝
                 -∗
               BMU ∅ c (oGS' := oGS) (
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

    Lemma TAU_acc_proper'_impl E π q Ob
      Φ1 Φ2 RR1 RR2 (V1 V2: iProp Σ):
      (∀ y x, Φ1 y x ≡ Φ2 y x) -∗ (∀ x, RR1 x ≡ RR2 x) -∗ (V1 ≡ V2) -∗
        TAU_acc E π q Φ1 Ob RR1 V1 -∗ TAU_acc E π q Φ2 Ob RR2 V2.
    Proof using. 
      iIntros "#EQ_Φ #EQ_RR #EQ_V TAU". rewrite /TAU_acc.

      iMod "TAU" as (?) "[P T1]". iModIntro. iExists _. iFrame "P".
      iSplit; [| iSplit].
    - iIntros (??) "X". iDestruct "T1" as "[T1 _]".
      iApply (BMU_wand with "[]").
      2: { iApply "T1". iDestruct "X" as "(?&?&?&?&X&?)". iFrame.
           iDestruct "X" as (?) "(?&?)". iExists _. iFrame.
           iSpecialize ("EQ_RR" $! r__p). by iRewrite "EQ_RR". }
      iIntros "(C&?&?&?& VV)". iFrame.
      iSpecialize ("EQ_RR" $! (Some (round x))). iRewrite "EQ_RR" in "C".
      iRewrite "EQ_V" in "VV". iFrame. 
    - iDestruct "T1" as "[_ [T1 _]]".
      iIntros (?) "(%&?&?)".
      iApply (BMU_wand with "[]").
      2: { iApply "T1". iFrame. done. }
      iIntros "P". iFrame. iIntros (?) "?". iSpecialize ("P" with "[$]").
      iMod "P". iModIntro. by iRewrite -("EQ_Φ" $! y x).
    - iRewrite -"EQ_V". 
      by iDestruct "T1" as "[_ [_ T1]]".
    Qed.

    Lemma TAU_acc_proper' E π q Ob
      Φ1 Φ2 RR1 RR2 (V1 V2: iProp Σ):
      (∀ y x, Φ1 y x ≡ Φ2 y x) -∗ (∀ x, RR1 x ≡ RR2 x) -∗ (V1 ≡ V2) -∗
        TAU_acc E π q Φ1 Ob RR1 V1 ∗-∗ TAU_acc E π q Φ2 Ob RR2 V2.
    Proof using.
      iIntros "#EQ_Φ #EQ_RR #EQ_V". iSplit; iApply TAU_acc_proper'_impl; (iFrame "#∗" || (iIntros; iApply internal_eq_sym; by iFrame "#∗")).
    Qed.

    Lemma TAU_proper'_impl E π q Ob
      Φ1 Φ2 RR1 RR2:
      (∀ y x, Φ1 y x ≡ Φ2 y x) -∗ (∀ x, RR1 x ≡ RR2 x) -∗
        TAU E π q Φ1 Ob RR1 -∗ TAU E π q Φ2 Ob RR2.
    Proof using.
      iIntros "#EQ_Φ #EQ_RR".
      iDestruct (greatest_fixpoint_strong_mono with "[]") as "X".
      2: by iFrame.
      iModIntro. iIntros. iApply (TAU_acc_proper'_impl with "[$] [$] [//] [$]").
    Qed.

    Lemma TAU_proper' E π q Ob
      Φ1 Φ2 RR1 RR2:
      (∀ y x, Φ1 y x ≡ Φ2 y x) -∗ (∀ x, RR1 x ≡ RR2 x) -∗
        TAU E π q Φ1 Ob RR1 ∗-∗ TAU E π q Φ2 Ob RR2.
    Proof using.
      iIntros "#EQ_Φ #EQ_RR".
      iSplit; iApply TAU_proper'_impl; (iFrame "#∗" || (iIntros; iApply internal_eq_sym; by iFrame "#∗")).
    Qed.

    Context `{EM: ExecutionModel heap_lang M}. 
    Context `{hGS: @heapGS Σ _ EM}.
    Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

    Definition TLAT_pre (RR: option RO -> iProp Σ) π q (O: gset SignalId): iProp Σ :=
      RR None ∗ obls τ O ∗ sgns_levels_gt' O L ∗
      th_phase_frag τ π q ∗ cp π d__m.
    
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
