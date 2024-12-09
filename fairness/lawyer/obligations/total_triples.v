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
      (τ: Locale) (π: Phase)(* TODO: should it be fixed? *)
      {ST: Type}
      (P: ST -> iProp Σ) (Q: val -> ST -> iProp Σ)
      (L: gset Level) (* TODO: only finite sets? *)
      {RO: Type}
      (round: ST -> RO) (* TODO: can we get away with ST only? *)
      (TGT: ST -> Prop) `{forall x, Decision (TGT x)}
      (d__h d__l: Degree)
      (c: nat)
      (d__m: Degree)
      (ε__m: coPset)
      (B: nat -> nat)
    .

    Section AtomicUpdates.
      Context
        (ε: coPset)
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
                              BMU ∅ c (oGS := oGS) (∀ v, Q v x ={∅, ε}=∗ Φ v)) ∧
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
               BMU ∅ c (oGS := oGS) (∀ v, Q v x ={∅, ε}=∗ Φ v)) ∧
              abort
      ).
      
      Lemma TAU2_elim:
        TAU2 ⊣⊢ TAU2_acc TAU2.
      Proof using. Admitted.

    End AtomicUpdates.

    Context `{EM: ExecutionModel heap_lang M}. 
    Context `{hGS: @heapGS Σ _ EM}.
    Let eGS: em_GS Σ := heap_fairnessGS (heapGS := hGS).

    Let TLAT__impl (tau: coPset → (val → iProp Σ) → gset SignalId → (option RO → iProp Σ) -> iProp Σ)
      (e: expr) (s: stuckness): iProp Σ :=
      ∀ (Φ: val -> iProp Σ) (O: gset SignalId) (RR: option RO -> iProp Σ),
        let ε := ⊤ ∖ ε__m in
        ⌜ B c <= LIM_STEPS ⌝ -∗
        RR None ∗ cp π d__m (oGS := oGS) ∗ obls τ O (oGS := oGS) ∗ sgns_level_gt' O L -∗
        tau ε Φ O RR -∗
        WP e @ s; τ; ⊤ {{ v, Φ v }}.
    
    Definition TLAT1 := TLAT__impl TAU1. 
    Definition TLAT2 := TLAT__impl TAU2. 

  End AtomicTriples.

End TotalTriples.
