From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import obls_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.


(**** adapted from Iris' implementation of parallel composition *)

Class parG Σ := SpawnG { #[local] spawn_tokG :: inG Σ (exclR unitO) }.

Definition parΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_parΣ {Σ} : subG parΣ Σ → parG Σ.
Proof. solve_inG. Qed.
  
Definition spawn : val :=
  λ: "f",
    let: "c" := ref NONE in
    Fork ("c" <- SOME ("f" #())) ;; "c".

Definition join : val :=
  rec: "join" "c" :=
    match: !"c" with
      SOME "x" => "x"
    | NONE => "join" "c"
    end.

Definition par : val :=
  λ: "e1" "e2",
    let: "handle" := spawn "e1" in
    let: "v2" := "e2" #() in
    let: "v1" := join "handle" in
    ("v1", "v2").

Definition par_sym : val :=
  λ: "e1" "e2",
    let: "h1" := spawn "e1" in
    let: "h2" := spawn "e2" in
    let: "v1" := join "h1" in
    let: "v2" := join "h2" in
    ("v1", "v2").


Section SpawnJoin.
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}. 
  
  Context {PARΣ: parG Σ}.

  Definition parN : namespace := nroot .@ "par".

  Context (l__s l__w: Level).
  Hypothesis (LT2h: lvl_lt l__s l__w).

  Context (d0 d1 d2: Degree).
  Hypothesis (LT01: deg_lt d0 d1). 
  Hypothesis (LT12: deg_lt d1 d2).

  Definition spawn_inv (γ : gname) (l : loc) (s__h: SignalId) (Ψ : val → iProp Σ) : iProp Σ :=
    ∃ lv b, l ↦ lv ∗ sgn s__h l__w (Some b) ∗ (⌜lv = NONEV /\ b = false ⌝ ∨
                      ∃ w, ⌜lv = SOMEV w /\ b = true⌝ ∗ (Ψ w ∨ own γ (Excl ()))).
  
  Definition join_handle (l : loc) s__h π (Ψ : val → iProp Σ) : iProp Σ :=
    ∃ γ, own γ (Excl ()) ∗ inv parN (spawn_inv γ l s__h Ψ) ∗ ep s__h π d0.

  Global Instance spawn_inv_ne n γ l s__h :
    Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l s__h).
  Proof. solve_proper. Qed.

  Global Instance join_handle_ne n l s__h π:
    Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l s__h π).
  Proof. solve_proper. Qed.

  Local Definition fuels_spawn := 20.

  Context (LS_LB: fuels_spawn <= LIM_STEPS).

  (* TODO: move *)
  Lemma sgns_levels_rel_singleton s l l' (R: LvlO -> LvlO -> Prop) ov
    (REL: R l l'):
    sgn s l ov ⊢ sgns_levels_rel R {[s]} {[ l' ]}.
  Proof using.
    clear -REL.
    iIntros "SGN".
    rewrite /sgns_levels_rel. rewrite big_sepS_singleton.
    iDestruct (sgn_get_ex with "[$]") as "[? #SGN0]".
    iExists _. iFrame "#".
    iPureIntro. set_solver.
  Qed.

  Context {NO_OBS_POST: ∀ τ v, obls τ ∅ -∗ fork_post τ v}.

  Definition spawnee_spec (e: expr) R d__s Q: iProp Σ :=
    ∀ F τ π, obls τ (R ∪ F) -∗ sgns_level_gt F l__s -∗
            th_phase_eq τ π -∗ cp π d__s -∗
            WP e @ τ {{ v, ∃ π', Q v ∗ obls τ F ∗ th_phase_eq τ π' ∗ ⌜ phase_le π π' ⌝ }}.

  Lemma spawn_spec τ π (f : val) (R__w R__s: gset SignalId) Q__s (d__s: Degree)
    (DISJws: R__w ## R__s)
    :
    {{{ spawnee_spec (f #()) R__s d__s Q__s ∗
        obls τ (R__w ∪ R__s) ∗ th_phase_eq τ π ∗ cp_mul π d1 2 ∗
        cp π d__s
    }}}
      spawn f @ τ
    {{{ l, RET #l; ∃ s__h π', join_handle l s__h π' Q__s ∗ obls τ R__w ∗ th_phase_eq τ π' ∗ ⌜ phase_le π π' ⌝ }}}.
  Proof.
    iIntros (Φ) "(SPEC2 & OB & PH & CPS0 & CP2) POST".
    rewrite /spawn /=.

    split_cps "CPS0" 1.
    pure_step_hl. MU_by_BOU.
    rewrite -!cp_mul_1. 
    iApply BOU_lower; [apply LS_LB| ].
    iMod (first_BOU with "CPS0'") as "[CPS #EB]".
    { apply LT01. }
    { rewrite /fuels_spawn. reflexivity. }
    BOU_burn_cp.    

    wp_bind (InjL _)%E. pure_steps.     
    wp_bind (ref _)%E.
    iMod (own_alloc (Excl ())) as (γ) "TOK"; first done.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply wp_alloc. iIntros "!> %hnd HANDLE _".
    MU_by_BOU.

    iMod (OU_create_sig _ _ l__w with "[$]") as "[%s__h (SGNh & OB & %FRESH)]".
    { try_solve_bounds. }
    iDestruct (sgn_get_ex with "[$]") as "[SGNh #SGNh']". 

    iMod (inv_alloc parN _ (spawn_inv γ hnd _ Q__s) with "[HANDLE SGNh]") as "#INV".
    { iNext. iExists NONEV, _. iFrame; eauto. }

    BOU_burn_cp. iModIntro.

    pure_steps. wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (Fork _)%E. iApply sswp_MUf_wp. iIntros "%τ' !>".
    split_cps "CPS" 1.
    iApply (MU__f_wand with "[-CPS' PH OB]").
    2: { iApply ohe_obls_AMU__f; [done| ].
         iApply BOU_AMU__f.
         iApply BOU_intro. iFrame.
         rewrite -cp_mul_1. 
         iSplitR; [iAccu| ].
         by iExists _. }
    iIntros "(_ & (%π__w & %π__s & PHw & OBw & PHs & OBs & [%PH_LTw %PH_LTs]))".
    Unshelve. 2: exact (R__s ∪ {[s__h]}).
    replace (_ ∖ _) with R__w by set_solver. replace (_ ∩ _) with (R__s ∪ {[s__h]}) by set_solver.

    split_cps "CPS" 2.
    iSplitL "SPEC2 CP2 CPS' OBs PHs".
    - wp_bind (f _)%E. iApply (wp_wand with "[-CPS']"). 
      { rewrite cp_weaken; [| apply PH_LTs]. 
        iApply ("SPEC2" with "[$] [] [$] [$]").
        iApply sgns_levels_rel_singleton; [| by iFrame]. done. }
      simpl. iIntros "%v (%π__s' & Qs & OBs & PH & %PH_LEs')".

      rewrite cp_mul_weaken; [| | reflexivity].
      2: { etrans; [apply PH_LTs | apply PH_LEs']. }
      iRename "CPS'" into "CPS".
      wp_bind (InjR _)%E. pure_steps.

      iApply wp_atomic.
      iInv parN as "(%t & %b & (>HND & >SGN & ?))" "CLOS". iModIntro.
      iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
      iApply (wp_store with "[$]"). iIntros "!> HANDLE".
      MU_by_BOU.
      iMod (OU_set_sig with "OBs SGN") as "[SGN OBs]".
      { set_solver. }
      { try_solve_bounds. }
      rewrite difference_diag_L.
      BOU_burn_cp. iModIntro.

      iApply wp_value. iMod ("CLOS" with "[HANDLE SGN Qs]") as "_".
      { do 2 iExists _. iFrame. iRight. iExists _. by iFrame. }
      iModIntro. simpl. 
      by iApply NO_OBS_POST.
      Unshelve. exact #(). 
    - rewrite cp_mul_weaken; [| | reflexivity].
      2: { apply PH_LTw. }
      iRename "PHw" into "PH".
      wp_bind (Rec _ _ _)%E.

      pure_step_hl. MU_by_BOU.
      rewrite cp_weaken; [| by apply PH_LTw].
      iMod (create_ep_upd with "CPS0 SGNh' PH") as "(#EP & _ & PH)".
      { eauto. }
      { try_solve_bounds. }
      BOU_burn_cp. 
      pure_steps.
      iApply "POST". do 2 iExists _. iFrame.
      iSplitL; [| iPureIntro; by apply PH_LTw].
      rewrite /join_handle. iExists _. iFrame "#∗".
  Qed.

  Lemma join_spec τ (Q__s : val → iProp Σ) h s__h R π:
    {{{ join_handle h s__h π Q__s ∗ obls τ R ∗
        th_phase_eq τ π ∗ cp_mul π d0 fuels_spawn ∗
        sgns_level_gt R l__w }}}
      join #h @ τ
    {{{ v, RET v; Q__s v ∗ obls τ R ∗ th_phase_eq τ π }}}.
  Proof.
    iIntros (Φ) "(HANDLE & OB & PH & CPS & #SGNS_GT) POST".
    rewrite /join_handle. iDestruct "HANDLE" as (γ) "(TOK & #INV & #EP)".
    iLöb as "IH". rewrite /join.

    pure_steps.
    wp_bind (! _)%E. iApply wp_atomic.
    iInv parN as "(%t & %b & (>HND & >SGN & CASES))" "CLOS". iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_load with "[$]"). iIntros "!> HANDLE".

    iDestruct "CASES" as "[%EQ | FIN]".
    2: { iDestruct "FIN" as "(% & %EQ & [Q__s | TOK'])"; destruct EQ as [-> ->].
         2: { iCombine "TOK TOK'" gives %[]. }
         MU_by_burn_cp. iModIntro. pure_steps.
         iMod ("CLOS" with "[HANDLE SGN TOK]") as "_".
         { do 2 iExists _. iFrame. iRight. iExists _. by iFrame. }
         iModIntro. pure_steps.
         wp_bind (Rec _ _ _)%E. pure_steps.
         iApply "POST". iFrame. }

    destruct EQ as [-> ->].
    MU_by_BOU.
    iApply OU_BOU_rep. iApply (OU_rep_wand with "[-OB PH SGN]").
    2: { iApply (expect_sig_upd_rep with "EP SGN [$] [$] [$]"). }
    iIntros "(CPS' & SGN & OB & PH)". iFrame.
    burn_cp_after_BOU. iModIntro. pure_steps.
    iMod ("CLOS" with "[HANDLE SGN]") as "_".
    { do 2 iExists _. iFrame. by iLeft. }
    iModIntro.
    pure_step. wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.
    iApply ("IH" with "[$] [$] [$] [CPS'] [$]").
    iApply (cp_mul_weaken with "[$]"); done.
  Qed.

  Definition waiter_spec (e: expr) R R' d__w Q: iProp Σ :=
    ∀ τ π, obls τ R -∗ th_phase_eq τ π -∗ cp π d__w -∗
            WP e @ τ {{ v, ∃ π', Q v ∗ obls τ R' ∗ th_phase_eq τ π' ∗ ⌜ phase_le π π' ⌝ }}.

  Lemma join_handle_weaken l s Φ π1 π2
    (LE: phase_le π1 π2):
    join_handle l s π1 Φ ⊢ join_handle l s π2 Φ. 
  Proof using.
    rewrite /join_handle. iIntros "(% & ? & ? & EP)".
    iExists _. iFrame. by iApply ep_weaken.
  Qed.

  (* Notice that this allows us to strip a later *after* the two Ψ have been
     brought together.  That is strictly stronger than first stripping a later
     and then merging them, as demonstrated by [tests/joining_existentials.v].
     This is why these are not Texan triples. *)
  Lemma par_spec τ π (Q__w Q__s : val → iProp Σ) R__s R__w R__w'
    (f__s f__w : val) (Φ : val → iProp Σ) d__w d__s
    (DISJsw: R__s ## R__w):
      waiter_spec (f__w #()) R__w R__w' d__w Q__w -∗
      spawnee_spec (f__s #()) R__s d__s Q__s -∗
      (* TODO: is it possible to avoid mentioning phase specifically? *)
      (* tried to do so, but have problems with eliminating laters and/or phase disappearing *)
      (▷ ∀ vw vs, obls τ R__w' -∗ Q__w vw -∗ Q__s vs -∗
                        (* th_phase_eq τ π2' -∗ ⌜ phase_le π π2' ⌝ -∗ *)
                        ▷ Φ (vs, vw)%V) -∗
      obls τ (R__w ∪ R__s) -∗ th_phase_eq τ π -∗
      cp π d2 -∗ cp π d__s -∗ cp π d__w -∗
      sgns_level_gt R__w' l__w -∗
      WP par f__s f__w @ τ {{ v, Φ v ∗ ∃ π', th_phase_eq τ π' ∗ ⌜ phase_le π π' ⌝ }}.
  Proof.
    iIntros "WAITER SPAWNEE POST OB PH CP2 CPs CPw #SGNS_GT".
    rewrite /par.

    wp_bind (App _ _)%E.
    pure_steps. pure_step_hl. MU_by_BOU.
    iApply BOU_lower; [apply LS_LB| ].
    iMod (first_BOU with "CP2") as "[CPS #EB]".
    { apply LT12. }
    { rewrite /fuels_spawn. reflexivity. }
    BOU_burn_cp.
    pure_steps.

    split_cps "CPS" 2. 
    iApply (spawn_spec with "[SPAWNEE OB PH CPS' CPs]").
    { symmetry. done. }
    { iFrame. }
    iIntros "!> %h (%s__h & %π__w & HANDLE & OBw & PH & %PH_LEw)".

    rewrite cp_mul_weaken; [| apply PH_LEw| reflexivity]. 
    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (f__w _)%E.
    iApply (wp_wand with "[-HANDLE CPS POST]").
    { iApply ("WAITER" with "[$] [$]").
      iApply cp_weaken; done. }
    simpl. iIntros "%vw (%π__w' & Qw & OBw & PH & %PH_LEw')".
    rewrite cp_mul_weaken. 2, 3: by eauto.

    (* exchange bound is smaller than what we need,
       but we can just do two exchanges *)
    split_cps "CPS" 2. iDestruct (cp_mul_take with "CPS'") as "[CP1 CP1']".
    rewrite -cp_mul_1. 
    wp_bind (Rec _ _ _)%E.
    pure_step_hl. MU_by_BOU.
    iMod (exchange_cp_upd with "CP1 [$]") as "CPS0"; eauto.
    { try_solve_bounds. }
    iMod (exchange_cp_upd with "CP1' [$]") as "CPS0'"; eauto.
    { apply Nat.lt_add_lt_sub_l. try_solve_bounds. }
    iCombine "CPS0 CPS0'" as "CPS0". rewrite -cp_mul_split.
    BOU_burn_cp. 

    pure_steps.
    iApply (join_spec with "[-POST Qw CPS]").
    { iFrame "#∗". iSplitL "HANDLE".
      { by iApply join_handle_weaken. }
      iApply (cp_mul_weaken with "[$]").
      { done. }
      rewrite /fuels_spawn. lia. }

    iIntros "!> %vs (Qs & OBw & PH)".
    iSpecialize ("POST" with "[$] [$] [$]").
    wp_bind (Rec _ _ _)%E. pure_steps.
    iFrame. iExists _. iFrame. iPureIntro. etrans; eauto.  
  Qed.

  (* Notice that this allows us to strip a later *after* the two Ψ have been
     brought together.  That is strictly stronger than first stripping a later
     and then merging them, as demonstrated by [tests/joining_existentials.v].
     This is why these are not Texan triples. *)
  Lemma par_sym_spec τ π (Q1 Q2 : val → iProp Σ) R1 R2 R'
    (f1 f2 : val) (Φ : val → iProp Σ) (df1 df2: Degree)
    (DISJ12: R1 ## R2) (DISJ': R' ## (R1 ∪ R2)):
      spawnee_spec (f1 #()) R1 df1 Q1 -∗
      spawnee_spec (f2 #()) R2 df2 Q2 -∗
      (* TODO: is it possible to avoid mentioning phase specifically? *)
      (* tried to do so, but have problems with eliminating laters and/or phase disappearing *)
      (▷ ∀ v1 v2, obls τ R' -∗ Q1 v1 -∗ Q2 v2 -∗
                        (* th_phase_eq τ π2' -∗ ⌜ phase_le π π2' ⌝ -∗ *)
                        ▷ Φ (v1, v2)%V) -∗
      obls τ (R1 ∪ R2 ∪ R') -∗ th_phase_eq τ π -∗
      cp π d2 -∗ cp π df1 -∗ cp π df2 -∗
      sgns_level_gt R' l__w -∗
      WP par_sym f1 f2 @ τ {{ v, Φ v ∗ ∃ π', th_phase_eq τ π' ∗ ⌜ phase_le π π' ⌝ }}.
  Proof.
    iIntros "SPEC1 SPEC2 POST OB PH CPP CP1 CP2 #SGNS_GT".
    rewrite /par_sym.

    wp_bind (App _ _)%E.
    pure_steps. pure_step_hl. MU_by_BOU.
    iApply BOU_lower; [apply LS_LB| ].
    iMod (first_BOU with "CPP") as "[CPS #EB]".
    { apply LT12. }
    { rewrite /fuels_spawn. reflexivity. }
    BOU_burn_cp.
    pure_steps.

    split_cps "CPS" 2.
    replace (R1 ∪ R2 ∪ R') with ((R2 ∪ R') ∪ R1) by set_solver.
    iApply (spawn_spec with "[SPEC1 OB PH CPS' CP1]").
    2: { iFrame. }
    { set_solver. }
    iIntros "!> %h1 (%s__h1 & %π__1 & HANDLE1 & OB & PH & %PH_LE1)".

    rewrite cp_mul_weaken; [| apply PH_LE1| reflexivity]. 
    wp_bind (Rec _ _ _)%E. pure_steps.

    split_cps "CPS" 2.
    rewrite union_comm_L.
    rewrite cp_weaken; [| apply PH_LE1]. 
    iApply (spawn_spec with "[SPEC2 OB PH CPS' CP2]").
    2: { iFrame. }
    { set_solver. }
    iIntros "!> %h2 (%s__h2 & %π__2 & HANDLE2 & OB & PH & %PH_LE2)".

    rewrite cp_mul_weaken; [| apply PH_LE2| reflexivity]. 
    wp_bind (Rec _ _ _)%E.

    (* do 2 pure_step_cases. *)

    (* exchange bound is smaller than what we need,
       but we can just do multiple exchanges *)
    split_cps "CPS" 3.
    iDestruct (cp_mul_take with "CPS'") as "[CP1 CP1']".
    (* rewrite -cp_mul_1.  *)
    wp_bind (Rec _ _ _)%E.
    pure_step_hl. MU_by_BOU.
    iMod (exchange_cp_upd with "CP1' [$]") as "CPS0"; eauto.
    { try_solve_bounds. }
    split_cps "CP1" 1. rewrite -cp_mul_1.
    iMod (exchange_cp_upd with "CP1' [$]") as "CPS0'"; eauto.
    { apply Nat.lt_add_lt_sub_l. try_solve_bounds. }
    iMod (exchange_cp_upd with "CP1 [$]") as "CPS0''"; eauto.
    { rewrite -Nat.sub_add_distr. 
      apply Nat.lt_add_lt_sub_l. try_solve_bounds. }
    iCombine "CPS0 CPS0' CPS0''" as "CPS0". rewrite -!cp_mul_split.
    BOU_burn_cp. 
    pure_steps.

    split_cps "CPS0" fuels_spawn.
    { rewrite /fuels_spawn. lia. }
    iApply (join_spec with "[-POST HANDLE2 CPS CPS0]").
    { iFrame "#∗". by iApply join_handle_weaken. }
    iIntros "!> %v1 (Q1 & OB & PH)".
    wp_bind (Rec _ _ _)%E. pure_steps. 
    
    split_cps "CPS0" fuels_spawn.
    { rewrite /fuels_spawn. lia. }
    iApply (join_spec with "[-POST CPS CPS0 Q1]").
    { iFrame "#∗". }
    iIntros "!> %v2 (Q2 & OB & PH)".
    wp_bind (Rec _ _ _)%E.
    (* pure_steps.  *)
    
    iSpecialize ("POST" with "[$] [$] [$]").
    wp_bind (Rec _ _ _)%E. pure_steps.
    iFrame. iExists _. iFrame. iPureIntro. etrans; eauto.
  Qed.    

End SpawnJoin.
