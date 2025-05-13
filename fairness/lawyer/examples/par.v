From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics coq_tactics.
From trillium.program_logic Require Export weakestpre ectx_lifting.
From trillium.fairness Require Import utils.
From trillium.fairness.lawyer.examples Require Import obls_tactics.
From trillium.fairness.lawyer.obligations Require Import obligations_model obligations_resources obligations_am obligations_em obligations_logic env_helpers.
From trillium.fairness.lawyer Require Import sub_action_em program_logic.
From iris.algebra Require Import auth gmap gset excl excl_auth csum mono_nat.
From iris.base_logic.lib Require Import invariants.


(* TODO: move, remove duplicates *)
Local Ltac try_solve_bounds :=
  (try iPureIntro);
  try (match goal with | |- ?x < ?y => red end);
  match goal with
  | BOUND: ?rfl_fl_sb_fun ?u ≤ ?LIM_STEPS |- ?n <= ?LIM_STEPS =>
      etrans; [| apply BOUND];
      try by (rewrite /rfl_fl_sb_fun; simpl; lia)
  | BOUND: ?N ≤ ?LIM_STEPS |- ?n <= ?LIM_STEPS =>
      etrans; [| apply BOUND];
      try by (try unfold N; simpl; lia)
  end.

Local Ltac use_list_head :=
  match goal with
  | |- ?n ≤ max_list (cons ?i ?l) =>
      trans i; [| simpl; lia];
      (reflexivity || (rewrite Nat.add_comm; simpl; reflexivity))
  end.

Local Ltac use_rfl_fl_sb :=
  use_list_head ||
  match goal with | |- ?n ≤ ?F _ => rewrite /F; use_list_head end.

(**** adapted from Iris' implementation of parallel composition *)

Class parG Σ := SpawnG { #[local] spawn_tokG :: inG Σ (exclR unitO) }.

Definition parΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_parΣ {Σ} : subG parΣ Σ → parG Σ.
Proof. solve_inG. Qed.

Definition parN : namespace := nroot .@ "par".
  
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


Section SpawnJoin.
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.
  Notation "'Degree'" := (om_hl_Degree). 
  Notation "'Level'" := (om_hl_Level).  

  Context {Σ} {OHE: OM_HL_Env OP EM Σ}. 
  
  Context {PARΣ: parG Σ}.
  Context (N: namespace).  

  Context (l2 l__h: Level).
  Hypothesis (LT2h: lvl_lt l2 l__h).

  Context (d0 d1 d2: Degree).
  Hypothesis (LT01: deg_lt d0 d1). 
  Hypothesis (LT12: deg_lt d1 d2).

  Definition spawn_inv (γ : gname) (l : loc) (s__h: SignalId) (Ψ : val → iProp Σ) : iProp Σ :=
    ∃ lv b, l ↦ lv ∗ sgn s__h l__h (Some b) ∗ (⌜lv = NONEV /\ b = false ⌝ ∨
                      ∃ w, ⌜lv = SOMEV w /\ b = true⌝ ∗ (Ψ w ∨ own γ (Excl ()))).
  
  Definition join_handle (l : loc) s__h π (Ψ : val → iProp Σ) : iProp Σ :=
    ∃ γ, own γ (Excl ()) ∗ inv N (spawn_inv γ l s__h Ψ) ∗ ep s__h π d0.

  Global Instance spawn_inv_ne n γ l s__h :
    Proper (pointwise_relation val (dist n) ==> dist n) (spawn_inv γ l s__h).
  Proof. solve_proper. Qed.

  Global Instance join_handle_ne n l s__h π:
    Proper (pointwise_relation val (dist n) ==> dist n) (join_handle l s__h π).
  Proof. solve_proper. Qed.

  Local Definition fuels_spawn := 20.

  Context (LS_LB: fuels_spawn <= LIM_STEPS).

  (* TODO: move *)
  Lemma sgns_levels_rel_singleton s l__s l (R: LvlO -> LvlO -> Prop) ov
    (REL: R l__s l):
    sgn s l__s ov ⊢ sgns_levels_rel R {[s]} {[ l ]}.
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
    ∀ F τ π, obls τ (R ∪ F) -∗ sgns_level_gt F l2 -∗
            th_phase_eq τ π -∗ cp π d__s -∗
            WP e @ τ {{ v, ∃ π', Q v ∗ obls τ F ∗ th_phase_eq τ π' ∗ ⌜ phase_le π π' ⌝ }}.

  Lemma spawn_spec τ π (f : val) (R1 R2: gset SignalId) Q2 (d__s: Degree)
    (DISJ12: R1 ## R2)
    :
    {{{ spawnee_spec (f #()) R2 d__s Q2 ∗
        obls τ (R1 ∪ R2) ∗ th_phase_eq τ π ∗ cp_mul π d1 2 ∗
        cp π d__s
    }}}
      spawn f @ τ
    {{{ l, RET #l; ∃ s__h π1', join_handle l s__h π1' Q2 ∗ obls τ R1 ∗ th_phase_eq τ π1' ∗ ⌜ phase_le π π1' ⌝ }}}.
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

    iMod (OU_create_sig _ _ l__h with "[$]") as "[%s__h (SGNh & OB & %FRESH)]".
    { try_solve_bounds. }
    iDestruct (sgn_get_ex with "[$]") as "[SGNh #SGNh']". 

    iMod (inv_alloc N _ (spawn_inv γ hnd _ Q2) with "[HANDLE SGNh]") as "#INV".
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
    iIntros "(_ & (%π1 & %π2 & PH1 & OB1 & PH2 & OB2 & [%PH_LT1 %PH_LT2]))".
    Unshelve. 2: exact (R2 ∪ {[s__h]}).
    replace (_ ∖ _) with R1 by set_solver. replace (_ ∩ _) with (R2 ∪ {[s__h]}) by set_solver.

    split_cps "CPS" 2.
    iSplitL "SPEC2 CP2 CPS' OB2 PH2".
    - wp_bind (f _)%E. iApply (wp_wand with "[-CPS']"). 
      { rewrite cp_weaken; [| apply PH_LT2]. 
        iApply ("SPEC2" with "[$] [] [$] [$]").
        iApply sgns_levels_rel_singleton; [| by iFrame]. done. }
      simpl. iIntros "%v (%π2' & Q2 & OB & PH & %PH_LE2')".

      rewrite cp_mul_weaken; [| | reflexivity].
      2: { etrans; [apply PH_LT2 | apply PH_LE2']. }
      iRename "CPS'" into "CPS".
      wp_bind (InjR _)%E. pure_steps.

      iApply wp_atomic.
      iInv N as "(%t & %b & (>HND & >SGN & ?))" "CLOS". iModIntro.
      iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
      iApply (wp_store with "[$]"). iIntros "!> HANDLE".
      MU_by_BOU.
      iMod (OU_set_sig with "OB SGN") as "[SGN OB]".
      { set_solver. }
      { try_solve_bounds. }
      rewrite difference_diag_L.
      BOU_burn_cp. iModIntro.

      iApply wp_value. iMod ("CLOS" with "[HANDLE SGN Q2]") as "_".
      { do 2 iExists _. iFrame. iRight. iExists _. by iFrame. }
      iModIntro. simpl. 
      by iApply NO_OBS_POST.
      Unshelve. exact #(). 
    - rewrite cp_mul_weaken; [| | reflexivity].
      2: { apply PH_LT1. }
      iRename "PH1" into "PH".
      wp_bind (Rec _ _ _)%E.

      pure_step_hl. MU_by_BOU.
      rewrite cp_weaken; [| by apply PH_LT1].
      iMod (create_ep_upd with "CPS0 SGNh' PH") as "(#EP & _ & PH)".
      { eauto. }
      { try_solve_bounds. }
      BOU_burn_cp. 
      pure_steps.
      iApply "POST". do 2 iExists _. iFrame.
      iSplitL; [| iPureIntro; by apply PH_LT1].
      rewrite /join_handle. iExists _. iFrame "#∗".
  Qed.

  Lemma join_spec τ (Q2 : val → iProp Σ) h s__h R π:
    {{{ join_handle h s__h π Q2 ∗ obls τ R ∗ th_phase_eq τ π ∗ cp_mul π d0 fuels_spawn ∗
        sgns_level_gt R l__h }}}
      join #h @ τ
    {{{ v, RET v; Q2 v ∗ obls τ R ∗ th_phase_eq τ π }}}.
  Proof.
    iIntros (Φ) "(HANDLE & OB & PH & CPS & #SGNS_GT) POST".
    rewrite /join_handle. iDestruct "HANDLE" as (γ) "(TOK & #INV & #EP)".
    iLöb as "IH". rewrite /join.

    pure_steps.
    wp_bind (! _)%E. iApply wp_atomic.
    iInv N as "(%t & %b & (>HND & >SGN & CASES))" "CLOS". iModIntro.
    iApply sswp_MU_wp_fupd; [done| ]. iModIntro.
    iApply (wp_load with "[$]"). iIntros "!> HANDLE".

    iDestruct "CASES" as "[%EQ | FIN]".
    2: { iDestruct "FIN" as "(% & %EQ & [Q2 | TOK'])"; destruct EQ as [-> ->].
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
  Lemma par_spec τ π (Q1 Q2 : val → iProp Σ) R1 R2 R2' (f1 f2 : val) (Φ : val → iProp Σ) d__w d__s
    (DISJ12: R1 ## R2):
      waiter_spec (f2 #()) R2 R2' d__w Q2 -∗
      spawnee_spec (f1 #()) R1 d__s Q1 -∗
      (* TODO: is it possible to avoid mentioning phase specifically? *)
      (* tried to do so, but have problems with eliminating laters and/or phase disappearing *)
      (▷ ∀ v1 v2, obls τ R2' -∗ Q1 v1 -∗ Q2 v2 -∗
                        (* th_phase_eq τ π2' -∗ ⌜ phase_le π π2' ⌝ -∗ *)
                        ▷ Φ (v1,v2)%V) -∗
      obls τ (R2 ∪ R1) -∗ th_phase_eq τ π -∗
      cp π d2 -∗ cp π d__s -∗ cp π d__w -∗
      sgns_level_gt R2' l__h -∗
      WP par f1 f2 @ τ {{ v, Φ v ∗ ∃ π2', th_phase_eq τ π2' ∗ ⌜ phase_le π π2' ⌝ }}.
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
    iIntros "!> %h (%s__h & %π1' & HANDLE & OB1 & PH & %PH_LE1)".

    rewrite cp_mul_weaken; [| apply PH_LE1| reflexivity]. 
    wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (f2 _)%E.
    iApply (wp_wand with "[-HANDLE CPS POST]").
    { iApply ("WAITER" with "[$] [$]").
      iApply cp_weaken; done. }
    simpl. iIntros "%v2 (%π2' & Q2 & OB2 & PH & %PH_LE12)".
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
    iApply (join_spec with "[-POST Q2 CPS]").
    { iFrame "#∗". iSplitL "HANDLE".
      { by iApply join_handle_weaken. }
      iApply (cp_mul_weaken with "[$]").
      { done. }
      rewrite /fuels_spawn. lia. }

    iIntros "!> %v1 (Q1 & OB2 & PH)".
    iSpecialize ("POST" with "[$] [$] [$]").
    wp_bind (Rec _ _ _)%E. pure_steps.
    iFrame. iExists _. iFrame. iPureIntro. etrans; eauto.  
  Qed.

End SpawnJoin.
