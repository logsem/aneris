(* From iris.program_logic Require Import lifting ectx_lifting. *)
(* From iris.program_logic Require Export weakestpre. *)

From iris.proofmode Require Import proofmode.
From lawyer.nonblocking.logrel Require Export persistent_pred logrel.
From lawyer.nonblocking Require Export pwp. 
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.
From heap_lang Require Import heap_lang_defs sswp_logic.


Section typed_interp.
  Context {Σ: gFunctors}
    (* {iG: irisG heap_lang LoopingModel Σ} *)
    {hG: heap1GS Σ}
    {invG: invGS_gen HasNoLc Σ}
  .

  Let iG := irisG_looping HeapLangEM (lG := hG).
  Existing Instance iG. 
  
  Notation D := (persistent_predO val (iPropI Σ)).

  Lemma subst_env_var x vs:
    subst_env vs (Var x) = from_option Val (Var x) (vs !! x).
  Proof using.
    rewrite /subst_env.

    set (P := fun (e: expr heap_lang) (mp: gmap string (val heap_lang)) =>
                e = from_option Val (Var x) (mp !! x)).
    enough (P (map_fold subst (Var x) vs) vs).
    { done. }

    apply map_fold_weak_ind; clear vs. 
    { done. }
    subst P. simpl. intros s v vs e NIN ->.
    rewrite insert_union_singleton_l. rewrite lookup_union.
    rewrite utils_maps.lookup_map_singleton.

    destruct decide as [-> | NEQ]. 
    { simpl. rewrite NIN. simpl. by rewrite decide_True. }
    rewrite option_union_left_id.
    destruct (vs !! x) eqn:XTH.
    - simpl. done.
    - simpl. by rewrite decide_False.
  Qed.

  Lemma logrel_var x : ⊢ logrel (Var x).
  Proof.
    iIntros "!#" (vs τ) "Henv".
    rewrite subst_env_var /interp_expr. 
    destruct (vs !! x) eqn:XTH; simpl. 
    - iApply wp_value.
      iApply interp_env_Some_l; done.
    - admit. 
  Admitted.

  (* Lemma logrel_lit_noloc (v: base_lit) *)
  (*   (NOLOC: forall l, v ≠ LitLoc l): *)
  (*   ⊢ logrel (LitV v). *)

  (* Lemma logrel_unit : ⊢ logrel UnitV. *)
  (* Proof. *)
  (*   iIntros "!#" (vs) "Henv". *)
  (*   rewrite /interp_expr. *)
  (*   simpl.  *)
  (*   iApply wp_value. rewrite interp_unfold. done. *)
  (* Qed. *)

  (* Lemma logrel_nat n : ⊢ logrel (#n n). *)
  (* Proof. *)
  (*   iIntros "!#" (vs) "Henv". *)
  (*   (* Unset Printing Notations. *) *)
  (*   iApply wp_value. rewrite interp_unfold /=; done. *)
  (* Qed. *)

  (* Lemma logrel_bool b : ⊢ logrel (#♭ b). *)
  (* Proof. iIntros "!#" (vs) "Henv"; iApply wp_value; rewrite interp_unfold /=; done. Qed. *)

  (* Lemma logrel_loc l: ⊢ logrel (Loc l). *)

  Lemma bin_op_eval_inv op a b r
    (EVAL: bin_op_eval op a b = Some r):
    (op = EqOp /\ vals_compare_safe a b /\ r = LitV $ LitBool $ bool_decide (a = b)) \/
    (exists na nb vr, a = LitV $ LitInt na /\ b = LitV $ LitInt nb /\ r = LitV vr /\
                 ((exists i, vr = LitInt i) \/ (exists b, vr = LitBool b)) /\
                 bin_op_eval_int op na nb = Some vr) \/
    (exists ba bb br, a = LitV $ LitBool ba /\ b = LitV $ LitBool bb /\ r = LitV $ LitBool br /\
                 bin_op_eval_bool op ba bb = Some $ LitBool br) \/
    (exists la ob, a = LitV $ LitLoc la /\ b = LitV (LitInt ob) /\ 
              r = LitV (LitLoc (la +ₗ ob))).
  Proof using.
    rewrite /bin_op_eval in EVAL.
    destruct decide.
    { subst. destruct decide; [| done].
      left. inversion EVAL. subst. eauto. }
    destruct a; try done.
    destruct l; try done.
    all: destruct b; (try done); destruct l; try done.
    - apply fmap_Some in EVAL as (?&?&->).
      right. left. do 3 eexists. repeat split; eauto.
      destruct op; simpl in H; set_solver.      
    - apply fmap_Some in EVAL as (?&?&->).
      destruct op; simpl in H; set_solver.
    - destruct l0; try done.
      inversion EVAL. subst. eauto.
      repeat right. eauto.
  Qed.

  Ltac inv_binop_eval H :=
    apply bin_op_eval_inv in H as
        [(-> & ? & ->) | [(?&?&?&->&->&->&[(?&->) | (?&->)]&?) | [(?&?&?&->&->&->&?) | (?&?&->&->&->)]]].

  Lemma interp_binop_eval op n1 n2
    (NOLOC: forall l, n1 ≠ LitV (LitLoc l)):
    ⊢ from_option interp (⌜ True ⌝) (bin_op_eval op n1 n2).
  Proof.
    destruct (bin_op_eval op n1 n2) eqn:EVAL; [| done]. simpl.
    inv_binop_eval EVAL.
    5: set_solver.
    all: by rewrite interp_unfold. 
  Qed.

  Definition valid_base_lit (v: base_lit) : Prop :=
    match v with
    | LitInt _ | LitBool _ | LitUnit => True
    | LitLoc _ | LitProphecy _ | LitPoison => False
  end.

  (* an adversary proram is any program with no hard-coded locations.
     TODO: currently we also exclude prophecies, seems reasonable? *)
  Fixpoint valid_adversary (e : expr heap_lang) : Prop :=
    match e with
    | Val v => valid_val v
    | Var _ | ChooseNat => True
    | Rec _ _  e | UnOp _ e | Fst e | Snd e |
      InjL e | InjR e | Fork e | Load e
      => valid_adversary e
    | App e1 e2 | Pair e1 e2 | BinOp _ e1 e2 |
      AllocN e1 e2 | Store e1 e2 | FAA e1 e2
      => valid_adversary e1 /\ valid_adversary e2
    | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2
      => valid_adversary e0 /\ valid_adversary e1 /\ valid_adversary e2
    end
  with valid_val (v: val heap_lang) : Prop :=
    match v with
    | LitV b => valid_base_lit b
    | RecV _ _ e => valid_adversary e
    | PairV v1 v2 => valid_val v1 /\ valid_val v2
    | InjLV v | InjRV v => valid_val v
    end.

  Lemma subst_env_binop vs op e1 e2:
    subst_env vs (BinOp op e1 e2) = BinOp op (subst_env vs e1) (subst_env vs e2).
  Proof using.
    rewrite /subst_env.
    generalize dependent e1. generalize dependent e2. generalize dependent op. 
    pattern vs. apply map_first_key_ind. 
    { intros. by rewrite !map_fold_empty. }
    intros s v m NIN FKEY IH op e1 e2.
    rewrite !map_fold_insert_first_key; auto.
    by rewrite IH.
  Qed.

  (* TODO: remove duplicates*)
  From iris.proofmode Require Import coq_tactics.
  From heap_lang Require Import tactics. 

Lemma tac_wp_bind
  K Δ s E Φ e f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ s; E {{ v, WP f (Val v) @ s; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ s; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> -> ->. by apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|reduction.pm_prettify]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
      first [ reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
            | fail 1 "wp_bind: cannot find" efoc "in" e ]
  | _ => fail "wp_bind: not a 'wp'"
  end.

  (* Goal forall (e1 e2: expr) (op: bin_op) (mp: gmap string val), False. *)
  (*   intros e1 e2 op vs. *)
  (*   (* Set Ltac Debug.  *) *)
  (*   reshape_expr (BinOp op (subst_env vs e1) (subst_env vs e2)) ltac:(fun K e' => unify e' (subst_env vs e2); wp_bind_core K).  *)

  (* TODO: move? try to unify with sswp_MU_wp_fupd  *)
  Lemma sswp_pwp s E E' τ e Φ
    (NVAL: language.to_val e = None):
    (|={E,E'}=> sswp s E' e (λ e', ▷ |={E',E}=> pwp s E τ e' Φ)%I) -∗
    pwp s E τ e Φ.
  Proof using.
    rewrite /pwp wp_unfold /wp_pre.
    iIntros "Hsswp". rewrite NVAL. 
    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
    iMod "Hsswp" as "foo".
    rewrite /sswp. rewrite NVAL.
    iSimpl in "Hσ".
    iSpecialize ("foo" with "[$]").
    iMod "foo" as (Hs) "Hsswp".
    red in Hextr. rewrite Hextr. 
    iModIntro. iSplit.
    { iPureIntro. by rewrite Hextr in Hs. }
    iIntros (e2 σ2 efs Hstep).
    iDestruct ("Hsswp" with "[//]") as "Hsswp".
    iApply (step_fupdN_le 2); [| done| ].
    { pose proof (trace_length_at_least extr). lia. }
    simpl.
    iApply (step_fupd_wand with "Hsswp").
    iIntros ">(Hσ & HMU & ->)".
    iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS' !> !>".
    iMod "CLOS'" as "_". iMod "HMU". iModIntro.
    iExists tt, tt. by iFrame.
  Qed.

  (* (* TODO: probably can strenghten it *) *)
  (* Lemma fill_item_fill_comm_weak K i e: *)
  (*   exists i' e', fill K (fill_item i e) = fill_item i' e'. *)
  (* Proof using. *)
  (*   generalize dependent i. generalize dependent e. induction K; eauto. *)
  (* Qed. *)

  Lemma foldl_foldr_rev {A B : Type} (f : B → A → B) (b : B) (la : list A):
    foldl f b la = foldr (flip f) b (rev la). 
  Proof using.
    generalize dependent b. induction la.
    { done. }
    simpl. intros. rewrite IHla.
    by rewrite foldr_app.
  Qed.
        
  (* Lemma binop_imm_no_fill op v1 v2: *)
  (*   ¬ exists i K e, BinOp op (Val v1) (Val v2) = fill (i :: K) e. *)
  (* Proof using. *)
  (*   simpl. red. intros (i&K&e&FILL). *)
  (*   generalize dependent i. generalize dependent e. *)
  (*   induction K. *)
  (*   { intros. simpl in FILL. *)
  (*     destruct i; simpl in FILL; try congruence. *)
  (*     - inversion FILL. subst. *)
  (*       admit. *)
  (*     - inversion FILL. subst.  *)

  (* TODO: move? *)
  Lemma binop_srav op v1 v2:
    sub_redexes_are_values (BinOp op (Val v1) (Val v2)).
  Proof using.
    red. simpl. intros. 
    rewrite /fill in H.
    rewrite foldl_foldr_rev in H. simpl in H.
    destruct (rev K) eqn:RR.
    { eapply (@f_equal _ _ length) in RR.
      rewrite length_rev /= in RR.
      destruct K; simpl in *; done. }
    clear RR. simpl in H.
    rewrite -(rev_involutive l) in H. rewrite -foldl_foldr_rev in H.
    replace (foldl (flip fill_item) e' (rev l)) with (fill (rev l) e') in H by done.
    remember (fill (rev l) e') as e''.
    assert (to_val e'' = None).
    { subst.
      destruct (to_val (fill _ _)) eqn:VV; [| done].
      apply to_val_fill_some in VV as (?&->). done. }
    clear Heqe''.       
    destruct e; simpl in H; try congruence.
    all: inversion H; subst; done.
  Qed.

  Lemma logrel_nat_binop op e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (BinOp op e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_binop.
    rewrite {3}/pwp.

    (* Set Ltac Backtrace.  *)
    (* reshape_expr (BinOp op (subst_env vs e1) (subst_env vs e2)) ltac:(fun K e' => unify e' efoc; wp_bind_core K).  *)
    (* Set Ltac Debug.  *)
    (* reshape_expr (BinOp op (subst_env vs e1) (subst_env vs e2)) ltac:(fun K e' => unify e' (subst_env vs e2); wp_bind_core K). *)
    (* TODO: fix wp_bind tactic *)

    iApply (wp_bind [BinOpRCtx _ _]).
    iApply wp_wand; [by iApply "IH2"| ].
    iIntros (v2) "#Hv2 /=".
    iApply (wp_bind [BinOpLCtx _ _]).
    iApply wp_wand; [by iApply "IH1"| ].
    iIntros (v1) "#Hv1 /=".

    destruct (bin_op_eval op v1 v2) eqn:EVAL.
    2: { iApply ectx_lifting.wp_lift_pure_head_stuck; try done.
         { apply binop_srav. }        
         intros. red. simpl. split; [done| ].
         red. simpl. intros ??? STEP.
         inversion STEP. subst. congruence. }

    iApply sswp_pwp; [done| ].
    iModIntro. iApply sswp_pure_step; [by apply EVAL| ].
    iIntros "!> !>".
    iApply wp_value.
    
    destruct (val_cases_nat v1) as [[? ->]|Hnn1], (val_cases_nat v2) as [[? ->]|Hnn2].
    
    destruct (val_cases_nat v1) as [[? ->]|Hnn1].
    - destruct (val_cases_nat v2) as [[? ->]|Hnn2].
      + iApply wp_pure_step_later; first done.
        iNext; iIntros "_".
        iApply wp_value.
        iApply interp_binop_eval.
      + iApply binop_stuck; auto.
    - iApply binop_stuck; auto.
  Qed.

  Lemma logrel_pair e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (Pair e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [PairLCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [PairRCtx _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    iApply wp_value.
    rewrite {5}interp_unfold; simpl.
    eauto 6.
  Qed.

  Lemma logrel_fst e : logrel e -∗ logrel (Fst e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [FstCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    destruct (val_cases_pair v) as [(? & ? & ->)|Hnp]; simpl.
    - rewrite {2}interp_unfold; simpl.
      iDestruct "Hv" as (? ?) "[>% [? ?]]"; simplify_eq.
      iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      by iApply wp_value.
    - iApply fst_stuck; done.
  Qed.

  Lemma logrel_snd e : logrel e -∗ logrel (Snd e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [SndCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    destruct (val_cases_pair v) as [(? & ? & ->)|Hnp]; simpl.
    - rewrite {2}interp_unfold; simpl.
      iDestruct "Hv" as (? ?) "[>% [? ?]]"; simplify_eq.
      iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      by iApply wp_value.
    - iApply snd_stuck; done.
  Qed.

  Lemma logrel_injl e : logrel e -∗ logrel (InjL e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [InjLCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_value.
    rewrite {3}interp_unfold; simpl.
    iLeft; eauto.
  Qed.

  Lemma logrel_injr e : logrel e -∗ logrel (InjR e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [InjRCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_value.
    rewrite {3}interp_unfold; simpl.
    iRight; eauto.
  Qed.

  Lemma logrel_case e0 e1 e2 : logrel e0 -∗ logrel e1 -∗ logrel e2 -∗ logrel (Case e0 e1 e2).
  Proof.
    iIntros "#IH0 #IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [CaseCtx _ _])).
    iApply wp_wand; first by iApply "IH0".
    iIntros (v0) "#Hv0 /=".
    destruct (val_cases_sum v0) as [[[? ->]|[? ->]]|Hns].
    - rewrite {4}interp_unfold; simpl.
      iDestruct "Hv0" as "[Hv0|Hv0]"; iDestruct "Hv0" as (?) "[>% ?]"; [simplify_eq|done].
      iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      asimpl.
      iApply ("IH1" $! (_ :: _)); rewrite interp_env_cons; iFrame "#".
    - rewrite {4}interp_unfold; simpl.
      iDestruct "Hv0" as "[Hv0|Hv0]"; iDestruct "Hv0" as (?) "[>% ?]"; [done|simplify_eq].
      iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      asimpl.
      iApply ("IH2" $! (_ :: _)); rewrite interp_env_cons; iFrame "#".
    - iApply case_stuck; auto.
  Qed.

  Lemma logrel_if e0 e1 e2 : logrel e0 -∗ logrel e1 -∗ logrel e2 -∗ logrel (If e0 e1 e2).
  Proof.
    iIntros "#IH0 #IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [IfCtx _ _])).
    iApply wp_wand; first by iApply "IH0".
    iIntros (v0) "#Hv0 /=".
    destruct (val_cases_bool v0) as [[[] ->]|Hns].
    - iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      iApply "IH1"; done.
    - iApply wp_pure_step_later; first done.
      iNext; iIntros "_".
      iApply "IH2"; done.
    - iApply if_stuck; auto.
  Qed.

  Lemma logrel_rec e : logrel e -∗ logrel (Rec e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply wp_value.
    rewrite {2}interp_unfold; simpl.
    iModIntro.
    iLöb as "IHrec".
    iIntros (v) "#Hv".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    change (Rec _) with (of_val (RecV e.[upn 2 (env_subst vs)])) at 2.
    iApply ("IH" $! (_ :: _ :: vs)).
    rewrite ?interp_env_cons; iFrame "Hv Henv".
    rewrite {5}interp_unfold; simpl.
    iModIntro; done.
  Qed.

  Lemma logrel_lam e : logrel e -∗ logrel (Lam e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply wp_value.
    rewrite {2}interp_unfold; simpl.
    iModIntro.
    iIntros (v) "#Hv".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    iApply ("IH" $! (_ :: vs)).
    rewrite ?interp_env_cons; iFrame "#".
  Qed.

  Lemma logrel_letin e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (LetIn e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    asimpl.
    iApply ("IH2" $! (_ :: vs)).
    rewrite ?interp_env_cons; iFrame "#".
  Qed.

  Lemma logrel_seq e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (Seq e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v) "#Hv /=".
    iApply wp_pure_step_later; first done.
    iNext; iIntros "_".
    iApply "IH2"; done.
  Qed.

  Lemma logrel_app e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (App e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [AppRCtx _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    destruct (val_cases_fun v1) as [[[? ->]|[? ->]]|Hnf].
    - rewrite {3}interp_unfold; simpl.
      iApply "Hv1"; done.
    - rewrite {3}interp_unfold; simpl.
      iApply "Hv1"; done.
    - iApply app_stuck; done.
  Qed.

  Lemma logrel_fork e : logrel e -∗ logrel (Fork e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply wp_fork.
    iSplitR; iNext; first by rewrite {2}interp_unfold.
    iApply wp_wand_l. iSplitL; [|iApply "IH"; auto]; auto.
  Qed.

  Lemma logrel_alloc e : logrel e -∗ logrel (Alloc e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [AllocCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    iApply wp_fupd.
    iApply wp_stuck_weaken.
    iApply wp_alloc; auto 1 using to_of_val.
    iNext; iIntros (l) "Hl".
    rewrite {3}interp_unfold /=.
    iMod (inv_alloc _ with "[Hl]") as "HN";
      [| iModIntro; iExists _; iSplit; trivial]; eauto.
  Qed.

  Lemma logrel_load e : logrel e -∗ logrel (Load e).
  Proof.
    iIntros "#IH !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [LoadCtx])).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    destruct (val_cases_loc v) as [[? ->]|Hnf].
    - iApply wp_stuck_weaken.
      rewrite {2}interp_unfold /=.
      iDestruct "Hv" as (l) "[% #Hv]"; simplify_eq.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      iApply (wp_load with "Hw1").
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
    - iApply load_stuck; done.
  Qed.

  Lemma logrel_store e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (Store e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [StoreLCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [StoreRCtx _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    destruct (val_cases_loc v1) as [[? ->]|Hnf].
    - iApply wp_stuck_weaken.
      rewrite {3}interp_unfold /=.
      iDestruct "Hv1" as (l) "[% #Hv1]"; simplify_eq.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      iApply (wp_store with "Hw1").
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
      rewrite {6}interp_unfold /=; done.
    - iApply store_stuck; done.
  Qed.

  Lemma logrel_CAS e1 e2 e3 : logrel e1 -∗ logrel e2 -∗ logrel e3 -∗ logrel (CAS e1 e2 e3).
  Proof.
    iIntros "#IH1 #IH2 #IH3 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [CasLCtx _ _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [CasMCtx _ _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    iApply (wp_bind (fill [CasRCtx _ _])).
    iApply wp_wand; first by iApply "IH3".
    iIntros (v3) "#Hv3 /=".
    destruct (val_cases_loc v1) as [[? ->]|Hnf].
    - iApply wp_stuck_weaken.
      rewrite {4}interp_unfold /=.
      iDestruct "Hv1" as (l) "[% #Hv1]"; simplify_eq.
      iInv (logN .@ l) as (w) "[Hw1 #Hw2]" "Hclose".
      destruct (decide (v2 = w)) as [|Hneq]; subst.
    + iApply (wp_cas_suc with "Hw1"); auto using to_of_val.
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
      rewrite {8}interp_unfold /=; done.
    + iApply (wp_cas_fail with "Hw1"); auto using to_of_val.
      iNext.
      iIntros "Hw1". iMod ("Hclose" with "[Hw1 Hw2]"); eauto.
      rewrite {8}interp_unfold /=; done.
    - iApply cas_stuck; done.
  Qed.

  Lemma logrel_FAA e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (FAA e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs) "#Henv"; rewrite /interp_expr /=.
    iApply (wp_bind (fill [FAALCtx _])).
    iApply wp_wand; first by iApply "IH1".
    iIntros (v1) "#Hv1 /=".
    iApply (wp_bind (fill [FAARCtx _])).
    iApply wp_wand; first by iApply "IH2".
    iIntros (v2) "#Hv2 /=".
    destruct (val_cases_loc v1) as [[? ->]|Hnf];
      last by iApply faa_stuck_non_loc_or_non_nat; auto.
    destruct (val_cases_nat v2) as [[? ->]|Hnf];
      last by iApply faa_stuck_non_loc_or_non_nat; auto.
    rewrite {3}interp_unfold /=.
    iDestruct "Hv1" as (l) "[% #Hv1]"; simplify_eq.
    iInv (logN .@ l) as (w) "[>Hw1 #Hw2]" "Hclose".
    destruct (val_cases_nat w) as [[? ->]|Hnf].
    -iApply wp_stuck_weaken.
     iApply (wp_FAA with "Hw1"); auto using to_of_val.
     iNext.
     iIntros "Hw1".
     iMod ("Hclose" with "[Hw1]"); last by eauto.
     iNext; iExists _; iFrame.
     rewrite {6}interp_unfold /=; done.
    - iApply faa_stuck_non_nat_loc; done.
  Qed.

  Theorem fundamental e : valid_adversary e → ⊢ logrel e.
  Proof.
    induction e; intros Hedv; simpl in *; intuition.
    - iApply logrel_var; done.
    - iApply logrel_rec; done.
    - iApply logrel_app; done.
    - iApply logrel_lam; done.
    - iApply logrel_letin; done.
    - iApply logrel_seq; done.
    - iApply logrel_unit; done.
    - iApply logrel_nat; done.
    - iApply logrel_bool; done.
    - iApply logrel_nat_binop; done.
    - iApply logrel_if; done.
    - iApply logrel_pair; done.
    - iApply logrel_fst; done.
    - iApply logrel_snd; done.
    - iApply logrel_injl; done.
    - iApply logrel_injr; done.
    - iApply logrel_case; done.
    - iApply logrel_fork; done.
    - iApply logrel_alloc; done.
    - iApply logrel_load; done.
    - iApply logrel_store; done.
    - iApply logrel_CAS; done.
    - iApply logrel_FAA; done.
  Qed.

End typed_interp.
