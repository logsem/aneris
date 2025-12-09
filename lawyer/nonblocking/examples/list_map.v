From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants.
From lawyer Require Import program_logic sub_action_em action_model.
From lawyer.obligations Require Import obligations_resources obligations_logic env_helpers obligations_model.
From heap_lang Require Import lang notation. 
From lawyer.nonblocking Require Import wait_free_spec_defs. 

(* Local Definition hl_nil: val := NONEV.  *)
(* Local Definition hl_cons (v l: val): val := SOMEV (v, l). *)

Close Scope Z. 

Inductive is_hl_list (P: val -> Prop) : val -> Prop :=
  | hl_list_nil : is_hl_list P NONEV
  | hl_list_cons v l (LIST: is_hl_list P l) (Pv: P v):
    is_hl_list P (SOMEV (v, l))
.


Definition hl_list_map_cur: val :=
  rec: "lm" "f" "l" :=
    Case "l"
      (** heap_lang has limited pattern-matching,
          so we exclude (InjLV v ∧ v ≠ ()) explicitly *)
      (λ: "v'", if: "v'" = #() then NONEV else #() #())
      (λ: "vl",
         let: "v'" := "f" (Fst "vl") in
         let: "l'" := "lm" "f" (Snd "vl") in
         SOME (Pair "v'" "l'") )
  .

Definition hl_list_map: val :=
  λ: "x", hl_list_map_cur (Fst "x") (Snd "x"). 

Fixpoint hl_list_size (l: val): nat :=
  match l with
  | NONEV => 0
  | SOMEV (_, l') => S $ hl_list_size l'
  | _ => 0 (** we only use this function on lists *)
  end. 


From lawyer.nonblocking.logrel Require Import logrel stuck_utils.
From iris.base_logic Require Import invariants.

From iris.proofmode Require Import proofmode coq_tactics tactics.

Ltac solve_vcs := 
  match goal with
    |- vals_compare_safe ?x ?y => red; set_solver
  end. 

(* TODO: move *)
Ltac pwp_pure_step := 
    (iApply sswp_pwp; [done| ]; iApply sswp_pure_step; (try solve_vcs || done); [ ]; do 2 iModIntro; iEval (simpl) ) ||
    (iApply trillium.program_logic.weakestpre.wp_value; []).   
Ltac pwp_pure_steps := repeat pwp_pure_step. 

Section ListMapPhys.

  Context {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}.

  Lemma list_map_phys_spec' τ (f l: heap_lang.val):
    interp f -∗ interp l -∗
      @pwp _ _ 
      (@irisG_looping heap_lang HeapLangEM Σ iG hG (@si_add_none heap_lang Σ))
      trillium.bi.weakestpre.MaybeStuck ⊤ τ (hl_list_map_cur f l)
      (@interp Σ iG hG).
  Proof using.
    iIntros "#IIf #IIl".
    iLöb as "IH" forall (l) "IIl". 

    rewrite {2}/hl_list_map_cur. 

    rewrite /pwp. 
    wp_bind (App _ f)%E.
    
    pwp_pure_step.
    rewrite /pwp. wp_bind (Rec _ _ _)%E. pwp_pure_step. 
    iApply trillium.program_logic.weakestpre.wp_value.
    
    do 1 pwp_pure_step.

    destruct (is_InjLV_dec l) as [[? ->] | ?].
    { pwp_pure_step.
      rewrite /pwp. wp_bind (Rec _ _ _)%E. pwp_pure_step. 
      iApply trillium.program_logic.weakestpre.wp_value.
      pwp_pure_step.
      rewrite /pwp. wp_bind (_ = _)%E. pwp_pure_step.
      destruct (decide (x = #())).
      - rewrite bool_decide_eq_true_2; [| done].
        repeat pwp_pure_step.
        rewrite {5}interp_unfold. simpl.
        iNext. iLeft. iExists _. iSplit; [done| ].
        by rewrite {5}interp_unfold.
      - pwp_pure_step.
        rewrite bool_decide_eq_false_2; [| done].
        repeat pwp_pure_step.
        solve_stuck_case. }

    destruct (is_InjRV_dec l) as [[v ->] | ?].
    2: solve_stuck_case.

    repeat pwp_pure_step.
    rewrite /pwp. wp_bind (Rec _ _ _)%E. pwp_pure_step.
    iApply trillium.program_logic.weakestpre.wp_value.
    wp_bind (App _ _)%E. pwp_pure_step.    

    rewrite /pwp. wp_bind (Fst _)%E.
    destruct (is_PairV_dec v) as [(c&l'&->) | NO].
    2: solve_stuck_case.

    rewrite {4}interp_unfold /=.
    pwp_pure_steps.    
    wp_bind (App f _)%E.

    iDestruct "IIl" as "[(%&%&?) | (%&%EQ&IIw)]".
    { done. }
    inversion EQ. subst. clear EQ.
    rewrite {4}interp_unfold /=.
    repeat setoid_rewrite bi.later_exist.
    iDestruct "IIw" as "(%&%&(>%EQ&#IIc&#IIl))".
    inversion EQ. subst a a0. clear EQ. 

    destruct (is_RecV_dec f) as [(b&s&ff&->)| ].
    2: solve_stuck_case. 

    rewrite {1}interp_unfold. simpl.

    iApply trillium.program_logic.weakestpre.wp_wand.
    { by iApply "IIf". }

    iIntros "%v #IIv".
    wp_bind (Rec _ _ _)%E.
    do 3 pwp_pure_step.

    rewrite /pwp. wp_bind (App _ _ _)%E. 
    
    wp_bind (Snd _)%E.
    do 2 pwp_pure_step.

    fold hl_list_map_cur.

    iApply trillium.program_logic.weakestpre.wp_wand.
    { by iApply ("IH" $! l'). }

    iIntros (l2) "#IIl2".
    wp_bind (Rec _ _ _)%E.
    pwp_pure_steps.

    rewrite /pwp. wp_bind (Pair _ _)%E.
    pwp_pure_steps.
    rewrite {9}interp_unfold /=.
    iRight. iExists _. iNext. iSplit; [done| ].
    rewrite {9}interp_unfold /=. iNext. 
    do 2 iExists _. iSplit; [done| ]. iFrame "#∗".

    Unshelve. all: apply _. 
  Qed. 

  Lemma list_map_phys_spec:
    ⊢ persistent_pred.pers_pred_car interp hl_list_map.
  Proof using.
    iIntros. rewrite interp_unfold /hl_list_map /=.
    iModIntro. iIntros (τ v) "#IIv".

    iApply sswp_pwp; [done| ]. iApply sswp_pure_step; [done| ].
    do 2 iModIntro. simpl.

    rewrite /pwp.
    wp_bind (Snd _)%E.
    destruct (is_PairV_dec v) as [(f&l&->) | NO].
    2: solve_stuck_case. 

    rewrite {1}interp_unfold /=.

    iApply sswp_pwp; [done| ]. iApply sswp_pure_step; [done| ].
    do 2 iModIntro. simpl.

    iDestruct "IIv" as "(%w1 & %w2 & %EQ & IIf & IIl)".
    inversion EQ. subst w1 w2. clear EQ.  
    
    rewrite /pwp.
    iApply trillium.program_logic.weakestpre.wp_value.
    wp_bind (Fst _)%E.
    
    iApply sswp_pwp; [done| ]. iApply sswp_pure_step; [done| ].
    do 2 iModIntro. simpl.

    iApply trillium.program_logic.weakestpre.wp_value.
    by iApply list_map_phys_spec'.

    Unshelve. all: apply _. 
  Qed.

End ListMapPhys.


From lawyer.examples Require Import obls_tactics.

Section ListMapSpec.
  Context {Σ: gFunctors}. 
  
  Context {DegO LvlO LIM_STEPS} {OP: OP_HL DegO LvlO LIM_STEPS}.
  Context `{EM: ExecutionModel heap_lang M}.

  Context {OHE: OM_HL_Env OP EM Σ}.

  Notation "'Degree'" := (om_hl_Degree).
  Context (d: Degree).

  Existing Instance OHE.

  Let K := 20.

  Definition hl_map_fuel (F: nat) (l: val heap_lang)  := (K + F) * (S $ hl_list_size l). 

  (** ******************** safe specs ****************) 

  Lemma list_map_spec' τ π q (l: val heap_lang)
    f F P Q
    (LIST: is_hl_list P l)
    :
    cp_mul π d (hl_map_fuel F l) -∗ 
    th_phase_frag τ π q -∗ 
    wait_free_method_gen NotStuck f d (fun _ => F) (fun v => ⌜ P v ⌝) (fun v => ⌜ Q v ⌝) -∗
    WP hl_list_map_cur f l @τ {{ l', th_phase_frag τ π q ∗ ⌜is_hl_list Q l'⌝ }}.
  Proof using. 
    iIntros "CPS PH #F_SPEC".
    iInduction LIST as [| ] "IH"; rewrite /hl_list_map_cur. 
    { split_cps "CPS" 10.
      { rewrite /hl_map_fuel. lia. }
      iClear "CPS". iRename "CPS'" into "CPS". 
      pure_steps.  
      wp_bind (Rec _ _ _)%E.
      pure_steps.
      wp_bind (_ = _)%E.
      iApply sswp_MU_wp; [done| ].
      iApply sswp_pure_step; [set_solver| ].
      MU_by_burn_cp.
      pure_steps. 
      iFrame. iPureIntro.
      by constructor. }
    rewrite /hl_map_fuel.
    rewrite (Nat.mul_succ_r _ (hl_list_size (InjRV _))).
    iDestruct (cp_mul_split with "CPS") as "[CPS' CPS]".
    iSpecialize ("IH" with "CPS'"). 
    iDestruct (cp_mul_split with "CPS") as "[CPS CPSf]".
    simpl. 
    pure_steps. wp_bind (Rec _ _ _)%E. pure_steps.

    wp_bind (Fst _)%E. pure_steps.
    wp_bind (f _)%E. 
    iApply ("F_SPEC" with "[$CPSf $PH]").
    { done. }
    iIntros "!>" (v') "[PH %Qv']".
    
    wp_bind (Rec _ _ _)%E. do 3 pure_step_cases.
    wp_bind (Snd _)%E. do 2 pure_step_cases. 
    wp_bind (App _ _ _)%E.
    iApply (wp_wand with "[IH PH]").
    { iApply ("IH" with "[$]"). } 

    simpl. iIntros (h) "(PH & %LIST')".
    wp_bind (Rec _ _ _)%E. pure_steps.
    wp_bind (Pair _ _)%E. pure_steps.
    iFrame. iPureIntro. by constructor.
  Qed.

  Lemma list_map_spec τ π q l
    f F P Q :
    {{{ cp_mul π d (hl_map_fuel F l) ∗ th_phase_frag τ π q ∗
        ⌜ is_hl_list P l ⌝ ∗ wait_free_method_gen NotStuck f d (fun _ => F) (fun v => ⌜ P v ⌝) (fun v => ⌜ Q v ⌝) }}}
      hl_list_map_cur f l @ τ
    {{{ l', RET l'; th_phase_frag τ π q ∗ ⌜ is_hl_list Q l' ⌝ }}}.
  Proof using.
    iIntros (Φ) "(CPS & PH & %LIST & #SPEC) POST".
    iApply (wp_wand with "[-]"). 
    { iApply wp_frame_step_r'. iSplitR "POST"; [| iAccu]. 
      by iApply (list_map_spec' with "[$] [$]"). }
    simpl.
    iIntros "% ([??] & POST)". iApply "POST". iFrame.
  Qed.

  Definition hl_map_unc_fuel (F: nat) (l: val heap_lang) :=
    5 + hl_map_fuel F l. 

  Lemma list_map_spec_unc τ π q l
    f F P Q :
    {{{ cp_mul π d (hl_map_unc_fuel F l) ∗ th_phase_frag τ π q ∗ 
        ⌜ is_hl_list P l ⌝ ∗ wait_free_method_gen NotStuck f d (fun _ => F) (fun v => ⌜ P v ⌝) (fun v => ⌜ Q v ⌝) }}}
      hl_list_map (f, l)%V @ τ
    {{{ l', RET l'; th_phase_frag τ π q ∗ ⌜ is_hl_list Q l' ⌝ }}}.
  Proof using.
    iIntros (Φ) "(CPS & PH & %LIST & #SPEC) POST".
    rewrite /hl_list_map.
    pure_step_cases. 
    wp_bind (Snd _)%E. do 2 pure_step_cases. 
    wp_bind (Fst _)%E. do 2 pure_step_cases.
    iApply (list_map_spec with "[-POST]").
    2: done. 
    iFrame "#∗". iSplit; [| done].
    iApply (cp_mul_weaken with "[$]"); [done| lia].
  Qed.

  (* (** ******************** unsafe specs ****************)  *)

  (* Lemma list_map_spec'_unsafe τ π q (l: val heap_lang) *)
  (*   f F (* P Q *) *)
  (*   (* (LIST: is_hl_list P l) *) *)
  (*   : *)
  (*   cp_mul π d (hl_map_fuel F l) -∗  *)
  (*   th_phase_frag τ π q -∗  *)
  (*   wait_free_method_gen MaybeStuck f d (fun _ => F) (fun v => ⌜ True ⌝) (fun v => ⌜ True ⌝) -∗ *)
  (*   WP hl_list_map_cur f l @ MaybeStuck; τ; ⊤  {{ l', th_phase_frag τ π q }}. *)
  (* Proof using.  *)
  (*   iIntros "CPS PH #F_SPEC". *)
  (*   iInduction LIST as [| ] "IH"; rewrite /hl_list_map_cur.  *)
  (*   { pure_steps.   *)
  (*     wp_bind (Rec _ _ _)%E. *)
  (*     pure_steps. *)
  (*     iFrame. iPureIntro. *)
  (*     by constructor. } *)
  (*   rewrite /hl_map_fuel. *)
  (*   rewrite (Nat.mul_succ_r _ (hl_list_size (InjRV _))). *)
  (*   iDestruct (cp_mul_split with "CPS") as "[CPS' CPS]". *)
  (*   iSpecialize ("IH" with "CPS'").  *)
  (*   iDestruct (cp_mul_split with "CPS") as "[CPS CPSf]". *)
  (*   simpl.  *)
  (*   pure_steps. wp_bind (Rec _ _ _)%E. pure_steps. *)

  (*   wp_bind (Fst _)%E. pure_steps. *)
  (*   wp_bind (f _)%E.  *)
  (*   iApply ("F_SPEC" with "[$CPSf $PH]"). *)
  (*   { done. } *)
  (*   iIntros "!>" (v') "[PH %Qv']". *)
    
  (*   wp_bind (Rec _ _ _)%E. do 3 pure_step_cases. *)
  (*   wp_bind (Snd _)%E. do 2 pure_step_cases.  *)
  (*   wp_bind (App _ _ _)%E. *)
  (*   iApply (wp_wand with "[IH PH]"). *)
  (*   { iApply ("IH" with "[$]"). }  *)

  (*   simpl. iIntros (h) "(PH & %LIST')". *)
  (*   wp_bind (Rec _ _ _)%E. pure_steps. *)
  (*   wp_bind (Pair _ _)%E. pure_steps. *)
  (*   iFrame. iPureIntro. by constructor. *)
  (* Qed. *)

End ListMapSpec.


From lawyer.nonblocking Require Import om_wfree_inst. 

Section ListMapWFree.

  Definition hlm_is_init_st (c: cfg heap_lang) := True. 

  Definition hlm_mod_inv {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}: iProp Σ := True. 

  Lemma hlm_init_mod `{heap1GS Σ, invGS_gen HasNoLc Σ}:
    forall c (INIT: hlm_is_init_st c), ⊢ hl_phys_init_resource c ={⊤}=∗ hlm_mod_inv.
  Proof using. set_solver. Qed.

  Definition hl_snd_opt (v: val heap_lang) :=
    match v with | PairV _ v2 => Some v2 | _ => None end.

  Definition hlm_arg_restr := is_hl_list (fun _ => (True: Prop)). 

  Lemma hlm_spec:
  forall {M} {EM: ExecutionModel heap_lang M} {Σ} {OHE: OM_HL_Env OP_HL_WF EM Σ}
    (f: val heap_lang) (F_inner: nat),
    (let _: heap1GS Σ := iem_phys HeapLangEM EM in hlm_mod_inv) ⊢
      wait_free_method_gen NotStuck hl_list_map d_wfr0
      (from_option (hl_map_unc_fuel F_inner) 0 ∘ hl_snd_opt)
      (ho_arg_restr NotStuck f hlm_arg_restr F_inner)
      (fun _ => emp).
  Proof using.
    simpl. intros.
    rewrite /wait_free_method_gen.
    iIntros "#INV". iIntros "**".
    iIntros "!>" (?) "(CPS & PH & #LIST) POST".

    rewrite /ho_arg_restr. iDestruct "LIST" as "(% & (-> & %LIST) & #WFS)".
    simpl. 

    iApply (list_map_spec_unc with "[-POST]").
    { iFrame. iSplit; [iPureIntro; by apply LIST| ].
      rewrite /wait_free_method_gen.
      iIntros "**". iIntros "!> % (CPS & PH & _) POST".
      iApply ("WFS" with "[-POST]"). 
      { iFrame. }
      iIntros "!> % PH". iApply ("POST" with "[$PH]").
      Unshelve. 2: exact (fun _ => True). done. }
    iIntros "!> % (?&?)". iApply "POST".
    iFrame. 
  Qed.
       
  Lemma hlm_phys_spec
   {Σ} {hG: heap1GS Σ} {iG: invGS_gen HasNoLc Σ}:
    hlm_mod_inv ⊢ persistent_pred.pers_pred_car interp hl_list_map.
  Proof using. iIntros "_". iApply list_map_phys_spec. Qed.

  Definition hlm_WF_HO_spec: WaitFreeSpecHO NotStuck hl_list_map hlm_arg_restr := {|
    wfsho_init_mod Σ _ _ := hlm_init_mod;
    wfsho_spec := @hlm_spec;
    wfsho_safety_spec Σ _ _ := hlm_phys_spec;
  |}.

End ListMapWFree.
