(* From iris.program_logic Require Import lifting ectx_lifting. *)
(* From iris.program_logic Require Export weakestpre. *)

From iris.proofmode Require Import proofmode coq_tactics.
From lawyer.nonblocking Require Import op_eval_helpers.
From lawyer.nonblocking.logrel Require Export persistent_pred substitutions valid_client stuck_utils.
From lawyer.nonblocking.tokens Require Export logrel_tok.
(* From lawyer.nonblocking Require Export pwp.  *)
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
From heap_lang Require Import heap_lang_defs sswp_logic tactics. 


Section typed_interp.
  Context {Σ: gFunctors}
    (* {iG: irisG heap_lang LoopingModel Σ} *)
    {hG: heap1GS Σ}
    {invG: invGS_gen HasNoLc Σ}
  .

  Let iG := irisG_looping HeapLangEM (lG := hG).
  Existing Instance iG. 
  
  Notation D := (persistent_predO val (iPropI Σ)).
  
  Context (tok: iProp Σ).
  Context (si_add: execution_trace heap_lang -> iProp Σ).
  Context (PRES: tok_add_pres tok si_add).
  Context (τ: locale heap_lang).
  Local Notation interp' := (interp tok si_add τ). 

  Lemma interp_binop_eval op n1 n2
    (NOLOC: forall l, n1 ≠ LitV (LitLoc l)):
    ⊢ from_option interp' (⌜ True ⌝) (bin_op_eval op n1 n2).
  Proof using All.
    destruct (bin_op_eval op n1 n2) eqn:EVAL; [| done]. simpl.
    inv_binop_eval EVAL.
    5: set_solver.
    all: by rewrite interp_unfold. 
  Qed.

  Local Notation logrel' := (logrel tok si_add τ).

  (* Goal Inhabited (trillium.program_logic.language.state heap_lang). *)
  (*   apply _. *)
  (*   Show Proof. *)

  Existing Instance state_inhabited.

  Ltac solve_stuck_case := unshelve stuck_utils.solve_stuck_case; apply _. 

  Lemma logrel_var x : ⊢ logrel' (Var x).
  Proof.
    iIntros "!#" (vs) "Henv".
    rewrite subst_env_var /interp_expr.
    iIntros "$". 
    destruct (vs !! x) eqn:XTH; rewrite XTH; simpl. 
    - iApply wp_value.
      iApply interp_env_Some_l; done.
    - solve_stuck_case. 
  Qed.

  Local Notation interp_expr' := (interp_expr tok si_add τ).

  Lemma wp_app_val_val f a:
    pers_pred_car interp' f -∗ ▷ pers_pred_car interp' a -∗
    (* tok -∗ *)
    (* pwp MaybeStuck ⊤ τ (App (Val f) (Val a)) (fun v => pers_pred_car interp' v ∗ tok). *)
    interp_expr' (App (Val f) (Val a)). 
  Proof using All.
    iIntros "Hv1 Hv2 T". rewrite /interp_expr. 
    destruct (@decide (exists b s e, f = RecV b s e)) as [FUN| ]. 
    { destruct f.
      2: by left; eauto.
      all: right; set_solver. }
    2: solve_stuck_case.    
    destruct FUN as (b&s&ff&->). 
    rewrite {1}interp_unfold. simpl.
    iApply ("Hv1" with "[$] [$]").
  Qed. 
    
  Lemma logrel_app e1 e2 : logrel' e1 -∗ logrel' e2 -∗ logrel' (App e1 e2).
  Proof using All.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv T"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 
    iApply (wp_bind [AppRCtx _]).
    iApply (wp_wand with "[T]").
    { iApply ("IH2" with "[$] [$]"). } 
    simpl. iIntros (v2) "[#Hv2 T] /=".
    iApply (wp_bind [AppLCtx _]).
    iApply (wp_wand with "[T]").
    { by iApply "IH1". }
    iIntros (v1) "[#Hv1 T] /=".
    by iApply wp_app_val_val. 
  Qed.

  Local Notation interp_env' := (interp_env tok si_add τ).

  Lemma logrel_App_RecV_env (b x : binder) (f: expr) (vs': gmap string val)
    (NOb : ∀ s : string, b = BNamed s → s ∉ dom vs')
    (NOx : ∀ s : string, x = BNamed s → s ∉ dom vs'):
  □ (∀ (vs0 : gmap string val),
           interp_env' vs0 -∗
           (* tok -∗ *)
           (* pwp MaybeStuck ⊤ τ0 (subst_env vs0 f) (fun v => pers_pred_car interp' v ∗ tok) *)
           interp_expr' (subst_env vs0 f)
    ) -∗
    interp_env' vs' -∗
  □ ∀ (v : val),
      ▷ pers_pred_car interp' v -∗
      (* tok -∗ *)
      (* pwp MaybeStuck ⊤ τ0 (App (Val (RecV b x (subst_env vs' f))) (Val v)) *)
      (*     (fun v => pers_pred_car interp' v ∗ tok). *)
      interp_expr' (App (Val (RecV b x (subst_env vs' f))) (Val v)). 
  Proof using All.
    iIntros "#IH #Henv".
    iLöb as "IHrec".
    iModIntro. iIntros (v) "#ARG TOK".
    iApply (sswp_pwp_pres with "[-TOK] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [done| ].
    do 2 iModIntro. 
    simpl. iIntros "TOK". 

    destruct x; simpl.
    - destruct b; simpl.
      + by iApply ("IH" with "[$] [$]"). 
      + simpl.
        rewrite -subst_env_insert.
        2: { eauto. }
        iApply ("IH" with "[] [$]"). simpl.
        rewrite interp_env_cons; [| set_solver].
        iSplit; [| done]. 
        iEval (rewrite interp_unfold). simpl. iApply "IHrec".  
    - destruct b; simpl.
      + rewrite -subst_env_insert; [| set_solver].
        iApply ("IH" with "[] [$]").
        rewrite interp_env_cons; [| set_solver].
        iSplit; [| done]. 
        iApply "ARG". 
      + simpl.
        destruct (decide (s0 = s)) as [-> | ?].
        * rewrite subst_subst_ignored. 
          rewrite -subst_env_insert; [| set_solver]. simpl.
          iApply ("IH" with "[] [$]"). simpl.
          rewrite interp_env_cons; [| set_solver]. simpl.
          iSplit; [| done]. 
          iEval (rewrite interp_unfold). simpl. iApply "IHrec".
        * do 2 (rewrite -subst_env_insert; [| set_solver]).
          simpl. iApply ("IH" with "[] [$]").
          do 2 (rewrite interp_env_cons; [| set_solver]).
          iFrame "ARG". 
          iSplit; [| done]. 
          iEval (rewrite interp_unfold). simpl. iApply "IHrec".
  Qed.

  Lemma logrel_rec b x f : logrel' f -∗ logrel' (Rec b x f).
  Proof using All.
    iIntros "#IH !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_rec.
    iApply (sswp_pwp_pres with "[] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [done| ].
    iIntros "!> !> TOK". iFrame "TOK".      
    iApply wp_value.
    rewrite {2}interp_unfold. simpl. 
    iModIntro.

    iIntros "**". 
    iApply (logrel_App_RecV_env with "[$] [] [$] [$]").
    - intros ? ->. simpl. set_solver.
    - intros ? ->. simpl. rewrite dom_rm_binder. destruct b; set_solver.
    - iApply interp_env_subseteq; [| done].
      etrans; apply rm_binder_subseteq.
  Qed.

  Lemma interp_RecV b x f : logrel' f -∗ interp' (RecV b x f).
  Proof using All.
    iIntros "#IHf". iEval (rewrite interp_unfold). simpl.
    iModIntro. iIntros (v) "#IHv TOK".
    iPoseProof (logrel_App_RecV_env _ _ _ ∅) as "LR".
    3: { rewrite subst_env_empty. iApply ("LR" with "[$] [] [$] [$]").
         iApply interp_env_nil. }
    all: set_solver.
  Qed.

  Lemma logrel_unop op e:
    logrel' e -∗ logrel' (UnOp op e).
  Proof using All.
    iIntros "#IH !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 

    iApply (wp_bind [UnOpCtx _]).
    iApply (wp_wand with "[TOK]"); [by iApply "IH"| ].
    iIntros (v) "[#Hv TOK] /=".

    destruct (un_op_eval op v) eqn:EVAL; [| solve_stuck_case].
    iApply (sswp_pwp_pres with "[] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [by apply EVAL| ].
    iIntros "!> !> TOK".
    iApply wp_value. iFrame. 

    rewrite {3}interp_unfold.
    inv_unop_eval EVAL; try done.
    destruct (val_into_int_spec v) as [(?&->&?) | (?&->)]; simpl.
    - set_solver.
    - iLeft. iExists _. iSplit; [done| ].
      by rewrite {3}interp_unfold.
  Qed.

  Lemma logrel_binop op e1 e2
    (VALID: valid_bin_op op):
    logrel' e1 -∗ logrel' e2 -∗ logrel' (BinOp op e1 e2).
  Proof using All.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 
    rewrite {3}/pwp.

    iApply (wp_bind [BinOpRCtx _ _]).
    iApply (wp_wand with "[TOK]"); [by iApply "IH2"| ].
    iIntros (v2) "[#Hv2 TOK] /=".
    iApply (wp_bind [BinOpLCtx _ _]).
    iApply (wp_wand with "[TOK]"); [by iApply "IH1"| ].
    iIntros (v1) "[#Hv1 TOK] /=".

    destruct (bin_op_eval op v1 v2) eqn:EVAL; [| solve_stuck_case]. 

    iApply (sswp_pwp_pres with "[] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [by apply EVAL| ].
    iIntros "!> !> TOK".
    iApply wp_value. iFrame. 

    iClear "IH1 IH2 Henv Hv2 Hv1". 
    inv_binop_eval EVAL; by rewrite interp_unfold.
  Qed.

  Lemma logrel_pair e1 e2 : logrel' e1 -∗ logrel' e2 -∗ logrel' (Pair e1 e2).
  Proof using All.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 

    iApply (wp_bind [PairRCtx _]).
    iApply (wp_wand with "[TOK]"); [by iApply "IH2"| ].
    iIntros (v2) "[#Hv2 TOK] /=".
    iApply (wp_bind [PairLCtx _]).
    iApply (wp_wand with "[TOK]") ; [by iApply "IH1"| ].
    iIntros (v1) "[#Hv1 TOK] /=".

    iApply (sswp_pwp_pres with "[] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [done| ].
    iIntros "!> !> TOK". iFrame. 
    iApply wp_value.
    iClear "IH1 IH2".
    rewrite {3}interp_unfold. simpl.
    iIntros "!>". do 2 iExists _. iSplitR; [done| ].
    iFrame "#∗". 
  Qed.

  Lemma logrel_fst e : logrel' e -∗ logrel' (Fst e).
  Proof using All.
    iIntros "#IH !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done].  
    iApply (wp_bind [FstCtx]).
    iApply (wp_wand with "[TOK]"); first by iApply "IH".
    iIntros (v) "[#Hv TOK] /=".

    destruct (@decide (exists v1 v2, v = PairV v1 v2)) as [(?&?&->) | NO]. 
    { destruct v.
      3: { left. eauto. }
      all: right; set_solver. }
    2: solve_stuck_case. 

    iApply (sswp_pwp_pres with "[] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [done| ].
    rewrite {2}interp_unfold. simpl.
    iIntros "!>!> TOK". iFrame. 
    iApply wp_value.    
    iDestruct "Hv" as (??) "(%EQ&?&?)".
    inversion EQ. subst.
    iFrame "#∗".
  Qed.

  Lemma logrel_snd e : logrel' e -∗ logrel' (Snd e).
  Proof using All.
    iIntros "#IH !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [SndCtx]).
    iApply (wp_wand with "[TOK]"); first by iApply "IH".
    iIntros (v) "[#Hv TOK] /=".
    destruct (@decide (exists v1 v2, v = PairV v1 v2)) as [(?&?&->) | NO]. 
    { destruct v.
      3: { left. eauto. }
      all: right; set_solver. }
    2: solve_stuck_case. 
    
    iApply (sswp_pwp_pres with "[] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [done| ].
    rewrite {2}interp_unfold. simpl.
    iIntros "!>!> TOK". iFrame. 
    iApply wp_value.    
    iDestruct "Hv" as (??) "(%EQ&?&?)".
    inversion EQ. subst.
    iFrame "#∗".
  Qed.

  Lemma logrel_injl e : logrel' e -∗ logrel' (InjL e).
  Proof using All.
    iIntros "#IH !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [InjLCtx]).
    iApply (wp_wand with "[TOK]"); first by iApply "IH".
    iIntros (v) "[#Hv TOK] /=".
    
    iApply (sswp_pwp_pres with "[] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [done| ].
    iIntros "!> !> TOK". iFrame "#∗".
    iApply wp_value.
    iClear "IH".
    rewrite {2}interp_unfold. simpl.
    iLeft. iExists _. by iFrame "#∗".     
  Qed.

  Lemma logrel_injr e : logrel' e -∗ logrel' (InjR e).
  Proof using All.
    iIntros "#IH !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [InjRCtx]).
    iApply (wp_wand with "[TOK]"); first by iApply "IH".
    iIntros (v) "[#Hv TOK] /=".
    
    iApply (sswp_pwp_pres with "[] TOK").
    1, 2: done. 
    iApply sswp_pure_step; [done| ].
    iIntros "!> !> TOK". iFrame "#∗".
    iApply wp_value.
    iClear "IH".
    rewrite {2}interp_unfold. simpl.
    iRight. iExists _. by iFrame "#∗".     
  Qed.

  Lemma logrel_case e0 e1 e2 : logrel' e0 -∗ logrel' e1 -∗ logrel' e2 -∗ logrel' (Case e0 e1 e2).
  Proof using All.
    iIntros "#IH0 #IH1 #IH2 !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg3; [| done]. 
    iApply (wp_bind [CaseCtx _ _]).
    iApply (wp_wand with "[TOK]"); first by iApply "IH0".
    iIntros (v0) "[#Hv0 TOK] /=".

    destruct (@decide ((exists v, v0 = InjLV v) \/ (exists v, v0 = InjRV v))) as [CASE| ]. 
    { destruct v0.
      4, 5: by left; eauto.
      all: right; set_solver. }
    2: solve_stuck_case.

    destruct CASE as [(?&->) | (?&->)].
    - iApply (sswp_pwp_pres with "[] TOK").
      1, 2: done. 
      iApply sswp_pure_step; [done| ].
      rewrite {4}interp_unfold. simpl.
      do 2 iModIntro.
      iDestruct "Hv0" as "[(%&%&U1) | (%&%&?)]"; [| done].
      inversion H. subst. 

      iIntros "TOK". 
      iApply (wp_bind [AppLCtx _]).
      iApply (wp_wand with "[TOK]"); [by iApply "IH1"| ].
      iIntros (v1) "[#V1 TOK]". simpl.
      by iApply wp_app_val_val.
    - iApply (sswp_pwp_pres with "[] TOK").
      1, 2: done. 
      iApply sswp_pure_step; [done| ].
      rewrite {4}interp_unfold. simpl.
      do 2 iModIntro.
      iDestruct "Hv0" as "[(%&%&?) | (%&%&U2)]"; [done| ].
      inversion H. subst. 

      iIntros "TOK". 
      iApply (wp_bind [AppLCtx _]).
      iApply (wp_wand with "[TOK]"); [by iApply "IH2"| ].
      iIntros (v2) "[#V2 TOK]". simpl.
      by iApply wp_app_val_val.
  Qed.

  (* Lemma pwp_fork s E τ e Φ: *)
  (*   (∀ τ', pwp s ⊤ τ' e (fun _ => ⌜ True ⌝)) -∗ *)
  (*   Φ (LitV $ LitUnit) -∗ *)
  (*   pwp s E τ (Fork e) Φ. *)
  (* Proof using. *)
  (*   rewrite /pwp wp_unfold /wp_pre. *)
  (*   iIntros "FORK POST". simpl. *)
  (*   iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ". *)
  (*   (* iMod "Hsswp" as "foo". *) *)
  (*   iSimpl in "Hσ". *)
  (*   iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'". *)
  (*   iSplit. *)
  (*   { iPureIntro. destruct s; [| done]. *)
  (*     red. do 3 eexists. econstructor. *)
  (*     3: eapply ForkS. *)
  (*     all: erewrite ectx_fill_emp; reflexivity. } *)
  (*   iIntros (e2 σ2 efs Hstep). *)
  (*   (* iDestruct ("Hsswp" with "[//]") as "Hsswp". *) *)
  (*   iApply (step_fupdN_le 1); [| done| ]. *)
  (*   { pose proof (trace_length_at_least extr). done. } *)
  (*   do 6 iModIntro. iMod "CLOS'" as "_". *)
  (*   iModIntro. iExists tt, tt. *)

  (*   inversion Hstep. subst. simpl in *. *)
  (*   opose proof * (srav_helper (Fork e)). *)
  (*   { solve_no_fill_item. } *)
  (*   { apply H. } *)
  (*   { simpl. by eapply val_head_stuck. } *)
  (*   subst. simpl in *. subst. *)
  (*   inversion H1. subst. *)
  (*   rewrite Hextr. simpl. iFrame. *)
  (*   iSplitL "POST". *)
  (*   - by iApply wp_value. *)
  (*   - iSplitL; [| done]. iApply "FORK". *)
  (* Qed. *)

  (* Lemma logrel_fork e : logrel e -∗ logrel (Fork e). *)
  (* Proof using All. *)
  (*   iIntros "#IH !#" (vs τ) "#Henv TOK"; rewrite /interp_expr /=. *)
  (*   rewrite subst_env_arg1; [| done]. *)
  (*   iApply pwp_fork. *)
  (*   2: by rewrite {2}interp_unfold. *)
  (*   iIntros (?). *)
  (*   iApply (wp_wand with "[TOK]"); [by iApply "IH"| ]. *)
  (*   by iIntros.  *)
  (* Qed. *)

  Lemma logrel_if e0 e1 e2 : logrel' e0 -∗ logrel' e1 -∗ logrel' e2 -∗ logrel' (If e0 e1 e2).
  Proof using All.
    iIntros "#IH0 #IH1 #IH2 !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg3; [| done]. 
    iApply (wp_bind [IfCtx _ _]).
    iApply (wp_wand with "[TOK]"); first by iApply "IH0".
    iIntros (v0) "[#Hv0 TOK] /=".
    destruct (@decide (exists b, v0 = LitV $ LitBool b)) as [BOOL| ]. 
    { destruct v0.
      2-5: right; set_solver.
      destruct l.
      2: left; eauto.
      all: right; set_solver. }
    2: solve_stuck_case. 
    destruct BOOL as (b&->).
    destruct b.
    - iApply (sswp_pwp_pres with "[] TOK").
      1, 2: done. 
      iApply sswp_pure_step; [done| ].
      do 2 iModIntro.
      by iApply "IH1".
    - iApply (sswp_pwp_pres with "[] TOK").
      1, 2: done. 
      iApply sswp_pure_step; [done| ].
      do 2 iModIntro.
      by iApply "IH2".
  Qed.

  Instance is_loc_dec v: Decision (exists l, v = LitV $ LitLoc l).
  Proof using.
    clear. 
    destruct v.
    2-5: right; set_solver.
    destruct l.
    1-4, 6: right; set_solver.
    left. eauto.
  Qed. 

  Instance is_int_dec v: Decision (exists (n: Z), v = LitV $ LitInt n).
  Proof using. 
    clear. 
    destruct v.
    2-5: right; set_solver.
    destruct l.
    2-6: right; set_solver.
    left; eauto.
  Qed.

  Lemma logrel_alloc en ea : logrel' en -∗ logrel' ea -∗ logrel' (AllocN en ea).
  Proof using All.
    iIntros "#IHn #IHa !>" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 
    iApply (wp_bind [AllocNRCtx _]).
    iApply (wp_wand with "[TOK]"); [by iApply "IHa"| ]. 
    iIntros (v) "[#Hv TOK] /=".
    iApply (wp_bind [AllocNLCtx _]).
    iApply (wp_wand with "[TOK]"); [by iApply "IHn"| ]. 
    iIntros (vn) "[#Hn TOK] /=".

    destruct (is_int_dec vn) as [INT| ].
    2: solve_stuck_case. 
    destruct INT as (x&->).
    destruct (decide (0 < x)) as [NZ | ].
    2: solve_stuck_case. 

    iApply (sswp_pwp_fupd_pres with "[] TOK").
    1, 2: done.
    iModIntro.
    iApply wp_allocN_seq; [done| ].
    iIntros "!> %l L".
    iModIntro.

    destruct (Z.to_nat x) eqn:X; [lia| ]. 
    rewrite -cons_seq. simpl. iDestruct "L" as "[[L _] _]".
    rewrite Nat2Z.inj_0. rewrite loc_add_0.
    iMod (inv_alloc with "[L]") as "#L".
    2: { iModIntro. iIntros "$".
         iApply wp_value. rewrite {5}interp_unfold. simpl.
         iExists _. iSplitR; [done| ].
         iApply "L". }
    iLeft. iFrame "L #∗". 
  Qed.

  Ltac solve_head_stuck_with_freed :=
    rewrite ?heap_lang_defs.pointsto_unseal;
    iIntros "* %VALID %LAST (SI & ADD)";
    simpl; iDestruct (gen_heap_valid with "SI [$]") as %V;
    iMod (fupd_mask_subseteq ∅) as "_"; [set_solver| ];
    iModIntro; iPureIntro;
    match goal with 
    | LAST : trace_ends_in _ _, V : heap _ !! _ = Some _ |- _ =>
        rewrite LAST /= in V end;
    solve_head_stuck. 

  (* Ltac solve_stuck_case_with_freed := *)
  Ltac solve_stuck_case_with_freed' :=
    iApply ectx_lifting.wp_lift_head_stuck;
      [done | apply srav_helper; solve_no_fill_item | solve_head_stuck_with_freed]. 
  Ltac solve_stuck_case_with_freed :=
    unshelve solve_stuck_case_with_freed'; by apply _.

  Lemma logrel_free e : logrel' e -∗ logrel' (Free e).
  Proof using All.
    iIntros "#IH !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [FreeCtx]).
    iApply (wp_wand with "[TOK]"); first by iApply "IH".
    iIntros (v) "[#Hv TOK] /=".
    destruct (is_loc_dec v) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).
    rewrite {2}interp_unfold /=. 
    iDestruct "Hv" as "(% & %EQ & INVl)". inversion_clear EQ.
    iApply wp_atomic. 
    iInv "INVl" as "[(%v & >L & #IIv) | >FREE]" "CLOS"; iModIntro. 
    2: solve_stuck_case_with_freed. 

    iApply (sswp_pwp_pres with "[-TOK] TOK").
    1, 2: done. 
    iApply (wp_free with "L").
    iIntros "!> FREE !> $".
    simpl. iApply wp_value.
    iMod ("CLOS" with "[FREE]") as "_".
    { by iRight. }
    by rewrite {4}interp_unfold /=. 
  Qed.

  Lemma logrel_load e : logrel' e -∗ logrel' (Load e).
  Proof using All.
    iIntros "#IH !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [LoadCtx]).
    iApply (wp_wand with "[TOK]"); first by iApply "IH".
    iIntros (v) "[#Hv TOK] /=".
    destruct (is_loc_dec v) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).
    rewrite {2}interp_unfold /=. 
    iDestruct "Hv" as "(% & %EQ & INVl)". inversion_clear EQ.
    iApply wp_atomic. 
    iInv "INVl" as "[(%v & >L & #IIv) | >FREE]" "CLOS"; iModIntro. 
    2: solve_stuck_case_with_freed.

    iApply (sswp_pwp_pres with "[-TOK] TOK").
    1, 2: done. 
    iApply (wp_load with "L").
    iIntros "!> L !> $".
    simpl. iApply wp_value.
    iMod ("CLOS" with "[L IIv]") as "_".
    { iLeft. by iFrame. } 
    by iFrame. 
  Qed.

  Lemma logrel_store el ev : logrel' el -∗ logrel' ev -∗ logrel' (Store el ev).
  Proof using All.
    iIntros "#IHl #IHv !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done].
    iApply (wp_bind [StoreRCtx _]).
    iApply (wp_wand with "[TOK]"); first by iApply "IHv".
    iIntros (v) "[#Hv TOK] /=".
    iApply (wp_bind [StoreLCtx _]).
    iApply (wp_wand with "[TOK]"); first by iApply "IHl".
    iIntros (lv) "[#Hl TOK] /=".
    destruct (is_loc_dec lv) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).
    rewrite {4}interp_unfold /=.
    iDestruct "Hl" as "(% & %EQ & INVl)". inversion_clear EQ.

    iApply wp_atomic. 
    iInv "INVl" as "[(%v_ & >L & #IIv) | >FREE]" "CLOS"; iModIntro. 
    2: solve_stuck_case_with_freed.

    iApply (sswp_pwp_pres with "[-TOK] TOK").
    1, 2: done. 
    iApply (wp_store with "[$]").
    iIntros "!> L !> $". simpl. iApply wp_value.
    iMod ("CLOS" with "[L Hv]").
    { iLeft. by iFrame. }
    by rewrite {6}interp_unfold.
  Qed.

  Lemma logrel_CmpXchg el es ef : logrel' el -∗ logrel' es -∗ logrel' ef -∗ logrel' (CmpXchg el es ef).
  Proof using All.
    iIntros "#IHl #IHs #IHf !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg3; [| done]. 
    iApply (wp_bind [CmpXchgRCtx _ _]).
    iApply (wp_wand with "[TOK]"); first by iApply "IHf".
    iIntros (f) "[#Hf TOK] /=".
    iApply (wp_bind [CmpXchgMCtx _ _]).
    iApply (wp_wand with "[TOK]"); first by iApply "IHs".
    iIntros (s) "[#Hs TOK] /=".
    iApply (wp_bind [CmpXchgLCtx _ _]).
    iApply (wp_wand with "[TOK]"); first by iApply "IHl".
    iIntros (lv) "[#Hl TOK] /=".
    destruct (is_loc_dec lv) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).
    
    rewrite {6}interp_unfold /=.
    iDestruct "Hl" as "(% & %EQ & INVl)". inversion_clear EQ.
    iApply wp_atomic.

    iInv "INVl" as "[(%v & >L & #IIv) | >FREE]" "CLOS"; iModIntro. 
    2: solve_stuck_case_with_freed.
 
    destruct (decide (vals_compare_safe v s)).
    2: solve_stuck_case_with_freed. 

    iApply (sswp_pwp_pres with "[-TOK] TOK").
    1, 2: done.
    destruct (decide (s = v)) as [-> | ?]. 
    - iApply (wp_cmpxchg_suc with "[$L //]"); try done.
      iIntros "!> L !> $". iApply wp_value. simpl. 
      iMod ("CLOS" with "[L Hf]").
      { iLeft. by iFrame. } 
      rewrite {8}interp_unfold. simpl.
      iModIntro. do 2 iExists _. iSplit; [done| ].
      iFrame "#∗". by rewrite {8}interp_unfold. 
    - iApply (wp_cmpxchg_fail with "[$L //]"); try done.
      iIntros "!> L !> $".
      iApply wp_value. simpl.  
      iMod ("CLOS" with "[L IIv]").
      { iLeft. by iFrame. }
      rewrite {8}interp_unfold. simpl.
      iModIntro. do 2 iExists _. iSplit; [done| ].
      iFrame "#∗". by rewrite {8}interp_unfold. 
  Qed.

  Lemma logrel_FAA el ea : logrel' el -∗ logrel' ea -∗ logrel' (FAA el ea).
  Proof using All.
    iIntros "#IHl #IHa !#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 
    iApply (wp_bind [FaaRCtx _]).
    iApply (wp_wand with "[TOK]"); [by iApply "IHa"| ]. 
    iIntros (av) "[#Ha TOK] /=".
    iApply (wp_bind [FaaLCtx _]).
    iApply (wp_wand with "[TOK]"); [by iApply "IHl"| ]. 
    iIntros (lv) "[#Hl TOK] /=".

    destruct (is_loc_dec lv) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).

    destruct (is_int_dec av) as [INT| ]. 
    2: solve_stuck_case.
    destruct INT as (?&->).

    rewrite {4}interp_unfold /=.
    iDestruct "Hl" as "(% & %EQ & INVl)". inversion_clear EQ.  

    iApply wp_atomic. 
    iInv "INVl" as "[(%v & >L & #IIv) | >FREE]" "CLOS"; iModIntro. 
    2: solve_stuck_case_with_freed.
 
    destruct (is_int_dec v) as [INT| ].
    2: { solve_stuck_case_with_freed. }
    destruct INT as (?&->).

    iApply (sswp_pwp_pres with "[-TOK] TOK").
    1, 2: done. 
    iApply (wp_faa with "[$]"). 
    iIntros "!> L !> $".
    iApply wp_value. simpl. 
    iMod ("CLOS" with "[L]").
    { iLeft. iFrame. by rewrite {6}interp_unfold. }
    by rewrite {6}interp_unfold.
  Qed.

  Lemma logrel_ChooseNat: ⊢ logrel' ChooseNat.
  Proof using All.
    iIntros "!#" (vs) "#Henv TOK"; rewrite /interp_expr /=.
    rewrite (subst_env_arg1 (fun _ => ChooseNat) _ (Val $ LitV $ LitUnit)); [| done].
    iApply (sswp_pwp_pres with "[-TOK] TOK").
    1, 2: done. 
    iApply wp_choose_nat.
    iIntros "!> % !> $".
    iApply wp_value.
    by rewrite interp_unfold.
  Qed.

  Theorem fundamental e:
    valid_client e -> no_forks e -> ⊢ logrel' e.
  Proof using All.
    pattern e. apply expr_ind_mut with (P0 := fun v => valid_val v -> val_nf v → ⊢ interp' v).
    all: intros; simpl in *. 
    - iIntros "!#" (vs) "#Henv".
      rewrite (subst_env_arg1 (fun _ => Val v) _ (Val $ LitV $ LitUnit)); [| done].
      rewrite /interp_expr. iIntros "$". 
      iApply wp_value.
      by iApply H. 
    - apply logrel_var.
    - iApply logrel_rec. by iApply H.
    - destruct H1. 
      iApply logrel_app; [iApply H | iApply H0]; tauto. 
    - iApply logrel_unop. by iApply H.
    - destruct H1 as (?&?&?).
      iApply logrel_binop; [done | iApply H | iApply H0]; tauto. 
    - destruct H2 as (?&?&?).
      iApply logrel_if; [iApply H | iApply H0 | iApply H1]; tauto. 
    - destruct H1 as (?&?).
      iApply logrel_pair; [iApply H | iApply H0]; tauto. 
    - iApply logrel_fst. by iApply H.  
    - iApply logrel_snd. by iApply H.
    - iApply logrel_injl. by iApply H.
    - iApply logrel_injr. by iApply H.
    - destruct H2 as (?&?&?).
      iApply logrel_case; [iApply H | iApply H0 | iApply H1]; tauto. 
    - 
      (* iApply logrel_fork. by iApply H. *)
      done. 
    - destruct H1 as (?&?).
      iApply logrel_alloc; [iApply H | iApply H0]; tauto. 
    - iApply logrel_free. by iApply H. 
    - iApply logrel_load. by iApply H.
    - destruct H1 as (?&?).
      iApply logrel_store; [iApply H | iApply H0]; tauto. 
    - destruct H2 as (?&?&?).
      iApply logrel_CmpXchg; [iApply H | iApply H0 | iApply H1]; tauto. 
    - destruct H1 as (?&?).
      iApply logrel_FAA; [iApply H | iApply H0]; tauto. 
    - by iApply logrel_ChooseNat. 
    - rewrite interp_unfold. destruct l; done.   
    - intros. simpl in *.
      iApply interp_RecV. by iApply H.
    - rewrite interp_unfold. simpl.
      iExists _, _. iNext. iSplit; [done| ].
      destruct H1. 
      iSplit; [iApply H | iApply H0]; tauto. 
    - rewrite interp_unfold. simpl.
      iLeft. iExists _. iSplit; [done| ].
      by iApply H.
    - rewrite interp_unfold. simpl.
      iRight. iExists _. iSplit; [done| ].
      by iApply H.
  Qed.

  (* Print Assumptions fundamental. *)

  Lemma ground_lit_interp l:
    is_ground_lit l -> ⊢ interp' (LitV l).
  Proof using iG.
    clear. 
    induction l; intros.
    all: rewrite interp_unfold /=; try done.
    by inversion H.
  Qed.

  Lemma ground_val_interp v:
    is_ground_val v -> ⊢ interp' v.
  Proof using iG.
    clear -iG.
    induction v; intros GV.
    all: inversion GV; try done; subst.
    - by apply ground_lit_interp.
    - rewrite interp_unfold /=.
      iExists _, _. iSplit; [done| set_solver]. 
    - rewrite interp_unfold /=.
      iLeft. iExists _. iSplit; [done| set_solver]. 
    - rewrite interp_unfold /=.
      iRight. iExists _. iSplit; [done| set_solver].
  Qed.

End typed_interp.
