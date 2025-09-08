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

  (* TODO: move? try to unify with other proofs for fork  *)
  (* TODO: move *)
  Lemma foldl_foldr_rev {A B : Type} (f : B → A → B) (b : B) (la : list A):
    foldl f b la = foldr (flip f) b (rev la). 
  Proof using.
    generalize dependent b. induction la.
    { done. }
    simpl. intros. rewrite IHla.
    by rewrite foldr_app.
  Qed.
        
  (* TODO: remove duplicates*)
  From iris.proofmode Require Import coq_tactics.
  From heap_lang Require Import tactics. 

  (* TODO: move? *)
  Lemma srav_helper (e: expr)
    (NO_FILL_ITEM: ¬ exists i e', e = fill_item i e' /\ to_val e' = None):
    sub_redexes_are_values e.
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

    destruct NO_FILL_ITEM. do 2 eexists. split; eauto.
    destruct (to_val (fill _ _)) eqn:VV; [| done].
    apply to_val_fill_some in VV as (?&->). done. 
  Qed.

  Ltac solve_no_fill_item := 
    intros (i&?&FILL&NVAL);
    destruct i; simpl in FILL; try congruence;
    inversion FILL; subst; done.

  Ltac solve_head_stuck := 
    intros; red; simpl; split; [done| ];
    red; simpl; intros ??? STEP;
    inversion STEP; subst; (congruence || by eauto || set_solver).

  Ltac solve_stuck_case :=
    iApply ectx_lifting.wp_lift_pure_head_stuck;
      [done | apply srav_helper; solve_no_fill_item | solve_head_stuck]. 

  Lemma bin_op_eval_inv op a b r
    (EVAL: bin_op_eval op a b = Some r):
    (op = EqOp /\ vals_compare_safe a b /\ r = LitV $ LitBool $ bool_decide (a = b)) \/
    (exists na nb vr, a = LitV $ LitInt na /\ b = LitV $ LitInt nb /\ r = LitV vr /\
                 ((exists i, vr = LitInt i) \/ (exists b, vr = LitBool b)) /\
                 bin_op_eval_int op na nb = Some vr) \/
    (exists ba bb br, a = LitV $ LitBool ba /\ b = LitV $ LitBool bb /\ r = LitV $ LitBool br /\
                 bin_op_eval_bool op ba bb = Some $ LitBool br) \/
    (exists la ob, a = LitV $ LitLoc la /\ b = LitV (LitInt ob) /\
              op = OffsetOp /\
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
    - destruct l0; try done. destruct op; try done. 
      inversion EVAL. subst. 
      repeat right. do 2 eexists. eauto.
  Qed.

  Ltac inv_binop_eval H :=
    apply bin_op_eval_inv in H as
        [(-> & ? & ->) | [(?&?&?&->&->&->&[(?&->) | (?&->)]&?) | [(?&?&?&->&->&->&?) | (?&?&->&->&->&->)]]].

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

  Definition valid_bin_op (op: bin_op): Prop :=
    match op with 
    | OffsetOp => False
    | _ => True
    end. 

  (* a valid client proram is any program without:
     - hard-coded locations
     - address offset operations
     TODO: currently we also exclude prophecies, seems reasonable? *)
  Fixpoint valid_client (e : expr) : Prop :=
    match e with
    | Val v => valid_val v
    | Var _ | ChooseNat => True
    | Rec _ _  e | UnOp _ e | Fst e | Snd e |
      InjL e | InjR e | Fork e | Load e
      => valid_client e
    | App e1 e2 | Pair e1 e2 | 
      AllocN e1 e2 | Store e1 e2 | FAA e1 e2
      => valid_client e1 /\ valid_client e2
    | BinOp op e1 e2 => valid_bin_op op /\ valid_client e1 /\ valid_client e2
    | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2
      => valid_client e0 /\ valid_client e1 /\ valid_client e2
    end
  with valid_val (v: val) : Prop :=
    match v with
    | LitV b => valid_base_lit b
    | RecV _ _ e => valid_client e
    | PairV v1 v2 => valid_val v1 /\ valid_val v2
    | InjLV v | InjRV v => valid_val v
    end.

  Lemma subst_env_arg3
    (F: expr -> expr -> expr -> expr)
    (DISTR: forall e1 e2 e3 s v, subst s v (F e1 e2 e3) = F (subst s v e1) (subst s v e2) (subst s v e3)):
    forall e1 e2 e3 vs, subst_env vs (F e1 e2 e3) = F (subst_env vs e1) (subst_env vs e2) (subst_env vs e3).
  Proof using.
    intros. rewrite /subst_env.
    pattern vs. apply map_first_key_ind. 
    { intros. by rewrite !map_fold_empty. }
    intros s v m NIN FKEY IH.
    rewrite !map_fold_insert_first_key; auto.
    by rewrite IH.
  Qed.

  Lemma subst_env_arg2 (F: expr -> expr -> expr)
    (DISTR: forall e1 e2 s v, subst s v (F e1 e2) = F (subst s v e1) (subst s v e2)):
    forall e1 e2 vs, subst_env vs (F e1 e2) = F (subst_env vs e1) (subst_env vs e2).
  Proof using.
    intros. rewrite /subst_env.
    pattern vs. apply map_first_key_ind. 
    { intros. by rewrite !map_fold_empty. }
    intros s v m NIN FKEY IH.
    rewrite !map_fold_insert_first_key; auto.
    by rewrite IH.
  Qed.

  Lemma subst_env_arg1 (F: expr -> expr)
    (DISTR: forall e1 s v, subst s v (F e1) = F (subst s v e1)):
    forall e1 vs, subst_env vs (F e1) = F (subst_env vs e1).
  Proof using.
    intros. rewrite /subst_env.
    pattern vs. apply map_first_key_ind. 
    { intros. by rewrite !map_fold_empty. }
    intros s v m NIN FKEY IH.
    rewrite !map_fold_insert_first_key; auto.
    by rewrite IH.
  Qed.

  Lemma logrel_var x : ⊢ logrel (Var x).
  Proof.
    iIntros "!#" (vs τ) "Henv".
    rewrite subst_env_var /interp_expr.
    destruct (vs !! x) eqn:XTH; simpl. 
    - iApply wp_value.
      iApply interp_env_Some_l; done.
    - solve_stuck_case. 
  Qed. 

  Lemma wp_app_val_val f a τ:
    pers_pred_car interp f -∗ ▷ pers_pred_car interp a -∗
    WP App (Val f) (Val a) @τ ?{{ v, pers_pred_car interp v }}.
  Proof using.
    iIntros "Hv1 Hv2".
    destruct (@decide (exists b s e, f = RecV b s e)) as [FUN| ]. 
    { destruct f.
      2: by left; eauto.
      all: right; set_solver. }
    2: solve_stuck_case.    
    destruct FUN as (b&s&ff&->). 
    rewrite {1}interp_unfold. simpl.
    by iApply "Hv1".
  Qed. 
    
  Definition rm_binder (b: binder) (vs: gmap string val) :=
    match b with 
    | BNamed s => delete s vs
    | BAnon => vs
    end.

  Lemma subst_env_empty e: subst_env ∅ e = e.
  Proof using. done. Qed.

  Lemma subst_env_singleton s v e: subst_env {[ s := v ]} e = subst s v e.
  Proof using.
    rewrite /subst_env. by rewrite map_fold_singleton.
  Qed.

  Lemma rm_binder_empty b: rm_binder b ∅ = ∅.
  Proof using. destruct b; set_solver. Qed.

  Ltac gd x := generalize dependent x. 

  Lemma subst_comm s1 v1 s2 v2 e
    (NEQ: s1 ≠ s2):
    subst s1 v1 (subst s2 v2 e) = subst s2 v2 (subst s1 v1 e).
  Proof using.
    gd s1. gd v1. gd s2. gd v2. 
    induction e; intros; simpl; try done.
    all: try by (f_equal; eauto).
    - destruct decide, decide; subst; simpl; try done.
      + by rewrite decide_True.
      + by rewrite decide_True.
      + by rewrite !decide_False.
    - destruct decide, decide; subst; simpl; try done.
      f_equal. eauto.
  Qed.

  Lemma subst_env_insert s v vs e
    (FRESH: s ∉ dom vs):
    subst_env (<[ s := v ]> vs) e = subst s v (subst_env vs e).
  Proof using.
    rewrite /subst_env.
    eapply map_fold_insert_L.
    2: by apply not_elem_of_dom.
    intros. by apply subst_comm.
  Qed.

  Lemma subst_env_insert' s v vs e
    (FRESH: s ∉ dom vs):
    subst_env (<[ s := v ]> vs) e = subst_env vs (subst s v e). 
  Proof using.
    rewrite subst_env_insert; [| done].
    (* TODO: extract lemma *)
    gd e. revert FRESH. pattern vs. apply map_first_key_ind; clear vs. 
    { intros. by rewrite !subst_env_empty. }
    intros. rewrite subst_env_insert; [| by apply not_elem_of_dom].
    rewrite dom_insert_L in FRESH. 
    apply not_elem_of_union in FRESH as [?%not_elem_of_singleton ?].
    rewrite subst_comm; [| done].
    rewrite H1; [| done].  
    rewrite -subst_env_insert; [| by apply not_elem_of_dom]. 
    done.
  Qed.

  Lemma rm_binder_insert_comm b s v vs
    (NEQ: b ≠ BNamed s):
    rm_binder b (<[ s := v ]> vs) = <[ s := v ]> (rm_binder b vs).
  Proof using.
    destruct b as [| sb]; simpl. 
    { done. }
    apply map_eq. intros s'.
    Set Printing Coercions.
    assert (sb ≠ s).
    { congruence. }
    destruct (decide (s' = s)) as [-> | NEQ'].
    { rewrite lookup_delete_ne; [| done].
      by rewrite !lookup_insert. }
    rewrite lookup_insert_ne; [| done].
    destruct (decide (sb = s')) as [-> | NEQ''].
    { by rewrite !lookup_delete. }
    do 2 (rewrite lookup_delete_ne; [| done]).
    rewrite lookup_insert_ne; done.
  Qed.

  Lemma dom_rm_binder b vs:
    dom (rm_binder b vs) = dom vs ∖ match b with | BNamed s => {[ s ]} | _ => ∅ end.
  Proof using.
    rewrite /rm_binder. destruct b; set_solver.
  Qed.

  Lemma subst_env_rec (b x: binder) (f: expr) vs:
    let vs' := rm_binder b $ rm_binder x vs in
    subst_env vs (Rec b x f) = Rec b x (subst_env vs' f).
  Proof using.
    simpl. generalize dependent f. 
    pattern vs. apply map_first_key_ind; clear vs. 
    { intros. by rewrite !rm_binder_empty !subst_env_empty. }
    intros s v vs NIN FKEY IH f.
    rewrite subst_env_insert; [| by apply not_elem_of_dom].
    rewrite IH. simpl. f_equal.
    destruct decide.
    - destruct a. 
      rewrite -subst_env_insert.
      2: { rewrite !dom_rm_binder.
           apply not_elem_of_dom in NIN.
           destruct x, b; set_solver. }
      rewrite rm_binder_insert_comm; [| done].
      f_equal. rewrite rm_binder_insert_comm; [| done].
      done. 
    - apply Classical_Prop.not_and_or in n.
      destruct (decide (BNamed s = x)) as [<- | ?]; simpl. 
      + by rewrite delete_insert_delete.
      + rewrite rm_binder_insert_comm; [| done].
        destruct n as [<-%NNP_P | <-%NNP_P]; simpl; try done.
        by rewrite delete_insert_delete.
  Qed.

  Lemma logrel_app e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (App e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 
    iApply (wp_bind [AppRCtx _]).
    iApply wp_wand; [by iApply "IH2"| ]. 
    iIntros (v2) "#Hv2 /=".
    iApply (wp_bind [AppLCtx _]).
    iApply wp_wand; [by iApply "IH1"| ]. 
    iIntros (v1) "#Hv1 /=".
    by iApply wp_app_val_val. 
  Qed.

  Lemma subst_subst_ignored s v v' e:
    subst s v' (subst s v e) = subst s v e.
  Proof using.
    gd v. gd v'. induction e; simpl; try done.
    all: try by (intros; f_equal; eauto).
    - intros. destruct decide; try done. simpl.
      by rewrite decide_False.
    - destruct decide; try done.
      intros. f_equal. eauto.
  Qed.

  Lemma interp_env_subseteq vs vs' (SUB: vs' ⊆ vs):
    interp_env vs -∗ interp_env vs'.
  Proof using.
    iIntros "#ENV". rewrite /interp_env.
    iApply big_sepM_subseteq; eauto.
  Qed.    

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

  (* Lemma logrel_App_RecV_env (b x : binder) (f: expr) (vs': gmap string val) *)
  (*   (NOb : ∀ s : string, b = BNamed s → s ∉ dom vs') *)
  (*   (NOx : ∀ s : string, x = BNamed s → s ∉ dom vs'): *)
  (* (* □ (∀ (vs0 : gmap string val) (τ0 : nat), *) *)
  (* (*          interp_env vs0 -∗ *) *)
  (* (*          pwp MaybeStuck ⊤ τ0 (subst_env vs0 f) (pers_pred_car interp)) -∗ *) *)
  (*   interp_env vs' -∗ *)
  (*   interp (RecV b x (subst_env vs' f)).  *)
  (* (* □ ∀ (τ0 : nat) (v : val), *) *)
  (* (*     ▷ pers_pred_car interp v *) *)
  (* (*     → pwp MaybeStuck ⊤ τ0 (Val (RecV b x (subst_env vs' f))) *) *)
  (* (*         (pers_pred_car interp). *) *)
  (* Proof using. *)
  (*   (* iIntros "#IH #Henv". *) *)
  (*   iIntros "#Henv". *)
  (*   (* iClear "IH".  *) *)
  (*   iLöb as "IHrec". *)
  (*   rewrite {2}interp_unfold /=. *)
  (*   iModIntro. iIntros (τ' v) "#ARG". *)
  (*   iApply sswp_pwp; [done| ]. iModIntro. *)
  (*   iApply sswp_pure_step; [done| ]. *)
  (*   do 3 iModIntro.  *)
  (*   simpl. *)

  (*   destruct x; simpl. *)
  (*   - destruct b; simpl. *)
  (*     + rewrite {1}interp_unfold. simpl.  *)
  (*       by iApply "IHrec".  *)
  (*     + simpl. *)
  (*       rewrite -subst_env_insert. *)
  (*       2: { eauto. } *)
  (*       iApply "IH". simpl. *)
  (*       rewrite interp_env_cons; [| set_solver]. *)
  (*       iSplit; [| done].  *)
  (*       iEval (rewrite interp_unfold). simpl. iApply "IHrec".   *)
  (*   - destruct b; simpl. *)
  (*     + rewrite -subst_env_insert; [| set_solver]. *)
  (*       iApply "IH". *)
  (*       rewrite interp_env_cons; [| set_solver]. *)
  (*       iSplit; [| done].  *)
  (*       iApply "ARG".  *)
  (*     + simpl. *)
  (*       destruct (decide (s0 = s)) as [-> | ?]. *)
  (*       * rewrite subst_subst_ignored.  *)
  (*         rewrite -subst_env_insert; [| set_solver]. simpl. *)
  (*         iApply "IH". simpl. *)
  (*         rewrite interp_env_cons; [| set_solver]. simpl. *)
  (*         iSplit; [| done].  *)
  (*         iEval (rewrite interp_unfold). simpl. iApply "IHrec". *)
  (*       * do 2 (rewrite -subst_env_insert; [| set_solver]). *)
  (*         simpl. iApply "IH". *)
  (*         do 2 (rewrite interp_env_cons; [| set_solver]). *)
  (*         iFrame "ARG".  *)
  (*         iSplit; [| done].  *)
  (*         iEval (rewrite interp_unfold). simpl. iApply "IHrec". *)
  (* Qed. *)


  Lemma logrel_App_RecV_env (b x : binder) (f: expr) (vs': gmap string val)
    (NOb : ∀ s : string, b = BNamed s → s ∉ dom vs')
    (NOx : ∀ s : string, x = BNamed s → s ∉ dom vs'):
  □ (∀ (vs0 : gmap string val) (τ0 : nat),
           interp_env vs0 -∗
           pwp MaybeStuck ⊤ τ0 (subst_env vs0 f) (pers_pred_car interp)) -∗
    interp_env vs' -∗
  □ ∀ (τ0 : nat) (v : val),
      ▷ pers_pred_car interp v
      → pwp MaybeStuck ⊤ τ0 (App (Val (RecV b x (subst_env vs' f))) (Val v))
          (pers_pred_car interp).
  Proof using.
    iIntros "#IH #Henv".
    iLöb as "IHrec".
    iModIntro. iIntros (τ' v) "#ARG".
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ].
    do 3 iModIntro. 
    simpl.

    destruct x; simpl.
    - destruct b; simpl.
      + by iApply "IH". 
      + simpl.
        rewrite -subst_env_insert.
        2: { eauto. }
        iApply "IH". simpl.
        rewrite interp_env_cons; [| set_solver].
        iSplit; [| done]. 
        iEval (rewrite interp_unfold). simpl. iApply "IHrec".  
    - destruct b; simpl.
      + rewrite -subst_env_insert; [| set_solver].
        iApply "IH".
        rewrite interp_env_cons; [| set_solver].
        iSplit; [| done]. 
        iApply "ARG". 
      + simpl.
        destruct (decide (s0 = s)) as [-> | ?].
        * rewrite subst_subst_ignored. 
          rewrite -subst_env_insert; [| set_solver]. simpl.
          iApply "IH". simpl.
          rewrite interp_env_cons; [| set_solver]. simpl.
          iSplit; [| done]. 
          iEval (rewrite interp_unfold). simpl. iApply "IHrec".
        * do 2 (rewrite -subst_env_insert; [| set_solver]).
          simpl. iApply "IH".
          do 2 (rewrite interp_env_cons; [| set_solver]).
          iFrame "ARG". 
          iSplit; [| done]. 
          iEval (rewrite interp_unfold). simpl. iApply "IHrec".
  Qed.

  Lemma rm_binder_subseteq s vs:
    rm_binder s vs ⊆ vs.
  Proof using.
    destruct s; simpl; try set_solver.
    apply delete_subseteq.
  Qed. 
    
  Lemma logrel_rec b x f : logrel f -∗ logrel (Rec b x f).
  Proof.
    iIntros "#IH !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_rec.
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ].
    iApply wp_value.
    rewrite {2}interp_unfold. simpl. 
    do 3 iModIntro.

    iApply (logrel_App_RecV_env with "[$]").
    - intros ? ->. simpl. set_solver.
    - intros ? ->. simpl. rewrite dom_rm_binder. destruct b; set_solver.
    - iApply interp_env_subseteq; [| done].
      etrans; apply rm_binder_subseteq. 
  Qed.

  Lemma interp_RecV b x f : logrel f -∗ interp (RecV b x f).
  Proof using.
    iIntros "#IHf". iEval (rewrite interp_unfold). simpl.
    iModIntro. iIntros (τ' v) "#IHv".
    iPoseProof (logrel_App_RecV_env _ _ _ ∅) as "LR".
    3: { rewrite subst_env_empty. iApply ("LR" with "[$] [] [$]").
         iApply interp_env_nil. }
    all: set_solver.
  Qed.

  (* Lemma logrel_val v *)
  (*   (VALID: valid_val v) *)
  (*   : ⊢ logrel (Val v). *)
  (* Proof. *)
  (*   iIntros "!#" (vs τ) "#Henv". *)
  (*   rewrite (subst_env_arg1 (fun _ => Val v) _ (Val $ LitV $ LitUnit)); [| done]. *)
  (*   rewrite /interp_expr. *)
  (*   iApply wp_value. *)

  (*   iClear "Henv". clear vs τ. rewrite interp_unfold.  *)
  (*   iInduction (v) as [| | | | ] forall (VALID); simpl.  *)
  (*   - destruct l; done. *)
  (*   - iModIntro.   *)
    
  (*   rewrite interp_unfold. destruct v; simpl in *; try done.  *)
  (*     iApply interp_env_Some_l; done. *)
  (*   - admit.  *)
  (* Admitted. *)

  Lemma valid_client_subst_preserved s v e
    (VALIDe: valid_client e)
    (VALIDv: valid_val v):
    valid_client (subst s v e).
  Proof using.
    induction e; simpl in *; try done.
    all: try tauto. 
    - destruct decide; eauto. 
    - destruct decide; eauto.
  Qed.

  Lemma valid_client_subst'_preserved b v e
    (VALIDe: valid_client e)
    (VALIDv: valid_val v):
    valid_client (subst' b v e).
  Proof using.
    destruct b; try done.
    by apply valid_client_subst_preserved.
  Qed. 

  Lemma pwp_fork s E τ e Φ:
    (* (NVAL: language.to_val e = None): *)
    (∀ τ', pwp s ⊤ τ' e (fun _ => ⌜ True ⌝)) -∗
    Φ (LitV $ LitUnit) -∗
    pwp s E τ (Fork e) Φ.
  Proof using.
    rewrite /pwp wp_unfold /wp_pre.
    iIntros "FORK POST". simpl. 
    iIntros (extr atr K tp1 tp2 σ1 Hvalid Hζ Hextr) "Hσ".
    (* iMod "Hsswp" as "foo". *)
    iSimpl in "Hσ".
    iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'".
    iSplit.
    { iPureIntro. destruct s; [| done].
      red. do 3 eexists. econstructor.
      3: eapply ForkS.
      all: erewrite ectx_fill_emp; reflexivity. }
    iIntros (e2 σ2 efs Hstep).
    (* iDestruct ("Hsswp" with "[//]") as "Hsswp". *)
    iApply (step_fupdN_le 1); [| done| ].
    { pose proof (trace_length_at_least extr). done. }
    do 6 iModIntro. iMod "CLOS'" as "_".
    iModIntro. iExists tt, tt.

    inversion Hstep. subst. simpl in *.
    opose proof * (srav_helper (Fork e)).
    { solve_no_fill_item. }
    { apply H. }
    { simpl. by eapply val_head_stuck. }
    subst. simpl in *. subst.
    inversion H1. subst.
    rewrite Hextr. simpl. iFrame.
    iSplitL "POST".
    - by iApply wp_value.
    - iSplitL; [| done]. iApply "FORK".
  Qed.

  Lemma logrel_nat_binop op e1 e2
    (VALID: valid_bin_op op):
    logrel e1 -∗ logrel e2 -∗ logrel (BinOp op e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 
    rewrite {3}/pwp.

    iApply (wp_bind [BinOpRCtx _ _]).
    iApply wp_wand; [by iApply "IH2"| ].
    iIntros (v2) "#Hv2 /=".
    iApply (wp_bind [BinOpLCtx _ _]).
    iApply wp_wand; [by iApply "IH1"| ].
    iIntros (v1) "#Hv1 /=".

    destruct (bin_op_eval op v1 v2) eqn:EVAL; [| solve_stuck_case]. 

    iApply sswp_pwp; [done| ].
    iModIntro. iApply sswp_pure_step; [by apply EVAL| ].
    iIntros "!> !>".
    iApply wp_value.

    iClear "IH1 IH2 Henv Hv2 Hv1". 
    inv_binop_eval EVAL; by rewrite interp_unfold.
  Qed.

  Lemma logrel_pair e1 e2 : logrel e1 -∗ logrel e2 -∗ logrel (Pair e1 e2).
  Proof.
    iIntros "#IH1 #IH2 !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 

    iApply (wp_bind [PairRCtx _]).
    iApply wp_wand; [by iApply "IH2"| ].
    iIntros (v2) "#Hv2 /=".
    iApply (wp_bind [PairLCtx _]).
    iApply wp_wand; [by iApply "IH1"| ].
    iIntros (v1) "#Hv1 /=".

    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ].
    iIntros "!> !>".
    iApply wp_value.
    iClear "IH1 IH2".
    rewrite {3}interp_unfold. simpl.
    iIntros "!> !>". do 2 iExists _. iSplitR; [done| ].
    iFrame "#∗". 
  Qed.

  Lemma logrel_fst e : logrel e -∗ logrel (Fst e).
  Proof.
    iIntros "#IH !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done].  
    iApply (wp_bind [FstCtx]).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".

    destruct (@decide (exists v1 v2, v = PairV v1 v2)) as [(?&?&->) | NO]. 
    { destruct v.
      3: { left. eauto. }
      all: right; set_solver. }
    2: solve_stuck_case. 
    
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ].
    iApply wp_value.
    iClear "IH".
    rewrite {1}interp_unfold. simpl.
    iNext. iDestruct "Hv" as (??) "(%EQ&?&?)".
    inversion EQ. subst.
    iIntros "!> !>". iFrame "#∗".
  Qed.

  Lemma logrel_snd e : logrel e -∗ logrel (Snd e).
  Proof.
    iIntros "#IH !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [SndCtx]).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".

    destruct (@decide (exists v1 v2, v = PairV v1 v2)) as [(?&?&->) | NO]. 
    { destruct v.
      3: { left. eauto. }
      all: right; set_solver. }
    2: solve_stuck_case. 
    
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ].
    iApply wp_value.
    iClear "IH".
    rewrite {1}interp_unfold. simpl.
    iNext. iDestruct "Hv" as (??) "(%EQ&?&?)".
    inversion EQ. subst.
    iIntros "!> !>". iFrame "#∗".
  Qed.

  Lemma logrel_injl e : logrel e -∗ logrel (InjL e).
  Proof.
    iIntros "#IH !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [InjLCtx]).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ].
    iApply wp_value.
    iClear "IH".
    rewrite {2}interp_unfold. simpl.
    iIntros "!> !> !> !>". iFrame "#∗". by iLeft. 
  Qed.

  Lemma logrel_injr e : logrel e -∗ logrel (InjR e).
  Proof.
    iIntros "#IH !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [InjRCtx]).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_pure_step; [done| ].
    iApply wp_value.
    iClear "IH".
    rewrite {2}interp_unfold. simpl.
    iIntros "!> !> !> !>". iFrame "#∗". by iRight. 
  Qed.
  Lemma logrel_case e0 e1 e2 : logrel e0 -∗ logrel e1 -∗ logrel e2 -∗ logrel (Case e0 e1 e2).
  Proof.
    iIntros "#IH0 #IH1 #IH2 !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg3; [| done]. 
    iApply (wp_bind [CaseCtx _ _]).
    iApply wp_wand; first by iApply "IH0".
    iIntros (v0) "#Hv0 /=".

    destruct (@decide ((exists v, v0 = InjLV v) \/ (exists v, v0 = InjRV v))) as [CASE| ]. 
    { destruct v0.
      4, 5: by left; eauto.
      all: right; set_solver. }
    2: solve_stuck_case.

    destruct CASE as [(?&->) | (?&->)].
    - iApply sswp_pwp; [done| ]. iModIntro.
      iApply sswp_pure_step; [done| ].
      rewrite {4}interp_unfold. simpl.
      do 3 iModIntro.
      iDestruct "Hv0" as "[(%&%&U1) | (%&%&?)]"; [| done].
      inversion H. subst. 

      iApply (wp_bind [AppLCtx _]).
      iApply wp_wand; [by iApply "IH1"| ].
      iIntros (v1) "#V1". simpl.
      by iApply wp_app_val_val.
    - iApply sswp_pwp; [done| ]. iModIntro.
      iApply sswp_pure_step; [done| ].
      rewrite {4}interp_unfold. simpl.
      do 3 iModIntro.
      iDestruct "Hv0" as "[(%&%&?) | (%&%&U2)]"; [done| ].
      inversion H. subst. 

      iApply (wp_bind [AppLCtx _]).
      iApply wp_wand; [by iApply "IH2"| ].
      iIntros (v2) "#V2". simpl.
      by iApply wp_app_val_val.
  Qed.

  Lemma logrel_fork e : logrel e -∗ logrel (Fork e).
  Proof.
    iIntros "#IH !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done].
    iApply pwp_fork.
    2: by rewrite {2}interp_unfold.
    iIntros (?).
    iApply wp_wand; [by iApply "IH"| ].
    by iIntros. 
  Qed.

  Lemma logrel_if e0 e1 e2 : logrel e0 -∗ logrel e1 -∗ logrel e2 -∗ logrel (If e0 e1 e2).
  Proof.
    iIntros "#IH0 #IH1 #IH2 !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg3; [| done]. 
    iApply (wp_bind [IfCtx _ _]).
    iApply wp_wand; first by iApply "IH0".
    iIntros (v0) "#Hv0 /=".
    destruct (@decide (exists b, v0 = LitV $ LitBool b)) as [BOOL| ]. 
    { destruct v0.
      2-5: right; set_solver.
      destruct l.
      2: left; eauto.
      all: right; set_solver. }
    2: solve_stuck_case. 
    destruct BOOL as (b&->).
    destruct b.
    - iApply sswp_pwp; [done| ]. iModIntro.
      iApply sswp_pure_step; [done| ].
      do 3 iModIntro.
      by iApply "IH1".
    - iApply sswp_pwp; [done| ]. iModIntro.
      iApply sswp_pure_step; [done| ].
      do 3 iModIntro.
      by iApply "IH2".
  Qed.

  Instance is_loc_dec v: Decision (exists l, v = LitV $ LitLoc l).
  Proof using. 
    destruct v.
    2-5: right; set_solver.
    destruct l.
    1-4, 6: right; set_solver.
    left. eauto.
  Qed. 

  Instance is_int_dec v: Decision (exists (n: Z), v = LitV $ LitInt n).
  Proof using. 
    destruct v.
    2-5: right; set_solver.
    destruct l.
    2-6: right; set_solver.
    left; eauto.
  Qed.

  Lemma logrel_alloc en ea : logrel en -∗ logrel ea -∗ logrel (AllocN en ea).
  Proof.
    iIntros "#IHn #IHa !>" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 
    iApply (wp_bind [AllocNRCtx _]).
    iApply wp_wand; [by iApply "IHa"| ]. 
    iIntros (v) "#Hv /=".
    iApply (wp_bind [AllocNLCtx _]).
    iApply wp_wand; [by iApply "IHn"| ]. 
    iIntros (vn) "#Hn /=".

    destruct (is_int_dec vn) as [INT| ].
    2: solve_stuck_case. 
    destruct INT as (x&->).
    destruct (decide (0 < x)) as [NZ | ].
    2: solve_stuck_case. 

    iApply sswp_pwp; [done| ]. iModIntro.
    iApply wp_allocN_seq; [done| ].
    iIntros "!> %l L".
    iModIntro.

    destruct (Z.to_nat x) eqn:X; [lia| ]. 
    rewrite -cons_seq. simpl. iDestruct "L" as "[[L _] _]".
    rewrite Nat2Z.inj_0. rewrite loc_add_0.

    iApply wp_value. rewrite {5}interp_unfold. simpl.
    iExists _. iSplitR; [done| ].

    iApply inv_alloc. by iFrame.
  Qed.

  Lemma logrel_load e : logrel e -∗ logrel (Load e).
  Proof.
    iIntros "#IH !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg1; [| done]. 
    iApply (wp_bind [LoadCtx]).
    iApply wp_wand; first by iApply "IH".
    iIntros (v) "#Hv /=".
    destruct (is_loc_dec v) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).
    rewrite {2}interp_unfold /=. 
    iDestruct "Hv" as "(% & %EQ & INVl)". inversion_clear EQ. 
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_fupd; [done| ].
    iInv "INVl" as "(%v & >L & #IIv)" "CLOS".
    iModIntro. 
    iApply (wp_load with "L").
    iIntros "!> L".
    iMod ("CLOS" with "[$L $IIv]").
    do 3 iModIntro. by iApply wp_value.
  Qed.

  Lemma logrel_store el ev : logrel el -∗ logrel ev -∗ logrel (Store el ev).
  Proof.
    iIntros "#IHl #IHv !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done].
    iApply (wp_bind [StoreRCtx _]).
    iApply wp_wand; first by iApply "IHv".
    iIntros (v) "#Hv /=".
    iApply (wp_bind [StoreLCtx _]).
    iApply wp_wand; first by iApply "IHl".
    iIntros (lv) "#Hl /=".
    destruct (is_loc_dec lv) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).
    rewrite {4}interp_unfold /=.
    iDestruct "Hl" as "(% & %EQ & INVl)". inversion_clear EQ. 
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply sswp_fupd; [done| ].
    iInv "INVl" as "(%v0 & >L & #IIv)" "CLOS".
    iModIntro.
    iApply (wp_store with "[$]").
    iIntros "!> L".
    iMod ("CLOS" with "[$L $Hv]").
    do 3 iModIntro. iApply wp_value.
    by rewrite {6}interp_unfold.
  Qed.

  (* TODO: move to trillium *)
  Lemma wp_lift_pure_head_stuck' τ E Φ e :
    to_val e = None →
    sub_redexes_are_values e →
    (∀ σ, head_stuck e σ) →
    ⊢ WP e @ τ; E ?{{ Φ }}.
  Proof using.
    iIntros (?? Hstuck). iApply ectx_lifting.wp_lift_head_stuck; [done|done|].
    iIntros (???????) "_". iMod (fupd_mask_subseteq ∅) as "_"; first set_solver.
    auto; done.
  Qed.

  Lemma logrel_CmpXchg el es ef : logrel el -∗ logrel es -∗ logrel ef -∗ logrel (CmpXchg el es ef).
  Proof.
    iIntros "#IHl #IHs #IHf !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg3; [| done]. 
    iApply (wp_bind [CmpXchgRCtx _ _]).
    iApply wp_wand; first by iApply "IHf".
    iIntros (f) "#Hf /=".
    iApply (wp_bind [CmpXchgMCtx _ _]).
    iApply wp_wand; first by iApply "IHs".
    iIntros (s) "#Hs /=".
    iApply (wp_bind [CmpXchgLCtx _ _]).
    iApply wp_wand; first by iApply "IHl".
    iIntros (lv) "#Hl /=".
    destruct (is_loc_dec lv) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).
    
    rewrite {6}interp_unfold /=.
    iDestruct "Hl" as "(% & %EQ & INVl)". inversion_clear EQ. 
    iInv "INVl" as "(%v0 & >L & #IIv)" "CLOS".

    destruct (decide (vals_compare_safe v0 s)).
    2: { iApply (ectx_lifting.wp_lift_head_stuck). 
         - done.
         - apply srav_helper; solve_no_fill_item.
         - iIntros. simpl. rewrite H0 /=.
           iDestruct (gen_heap_valid with "[$] [$]") as %L.
           iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'".
           iPureIntro.
           solve_head_stuck. }
    
    iApply sswp_pwp; [done| ]. iModIntro.
    destruct (decide (s = v0)) as [-> | ?]. 
    - iApply (wp_cmpxchg_suc with "[$L //]"); try done.
      iIntros "!> L !> !>".
      iApply wp_value. 
      iMod ("CLOS" with "[$L $Hf]").
      rewrite {8}interp_unfold. simpl.
      iModIntro. do 2 iExists _. iSplit; [done| ].
      iFrame "#∗". by rewrite {8}interp_unfold. 
    - iApply (wp_cmpxchg_fail with "[$L //]"); try done.
      iIntros "!> L !> !>".
      iApply wp_value. 
      iMod ("CLOS" with "[$L $IIv]").
      rewrite {8}interp_unfold. simpl.
      iModIntro. do 2 iExists _. iSplit; [done| ].
      iFrame "#∗". by rewrite {8}interp_unfold. 
  Qed.

  Lemma logrel_FAA el ea : logrel el -∗ logrel ea -∗ logrel (FAA el ea).
  Proof.
    iIntros "#IHl #IHa !#" (vs τ) "#Henv"; rewrite /interp_expr /=.
    rewrite subst_env_arg2; [| done]. 
    iApply (wp_bind [FaaRCtx _]).
    iApply wp_wand; [by iApply "IHa"| ]. 
    iIntros (av) "#Ha /=".
    iApply (wp_bind [FaaLCtx _]).
    iApply wp_wand; [by iApply "IHl"| ]. 
    iIntros (lv) "#Hl /=".

    destruct (is_loc_dec lv) as [LOC| ]. 
    2: solve_stuck_case.
    destruct LOC as (l&->).

    destruct (is_int_dec av) as [INT| ]. 
    2: solve_stuck_case.
    destruct INT as (?&->).

    rewrite {4}interp_unfold /=.
    iDestruct "Hl" as "(% & %EQ & INVl)". inversion_clear EQ.  

    iApply wp_atomic. 
    iInv (logN .@ l0) as (w) "[>L IIl]" "CLOS".
    iModIntro.

    destruct (is_int_dec w) as [INT| ].
    2: { iApply ectx_lifting.wp_lift_head_stuck. 
         - done.
         - apply srav_helper; solve_no_fill_item.
         - iIntros. simpl. rewrite H0 /=.
           iDestruct (gen_heap_valid with "[$] [$]") as %L.
           iApply fupd_mask_intro; [set_solver| ]. iIntros "CLOS'".
           iPureIntro.
           solve_head_stuck. }
    destruct INT as (?&->).
    
    iApply sswp_pwp; [done| ]. iModIntro.
    iApply (wp_faa with "[$]"). 
    iIntros "!> L".
    do 2 iModIntro.
    iApply wp_value.
    iMod ("CLOS" with "[$L]").
    { by iEval (rewrite interp_unfold). }
    by iApply "IIl". 
  Qed.

  Scheme expr_ind_mut := Induction for expr Sort Prop
  with val_ind_mut := Induction for val Sort Prop.  

  Theorem fundamental e : valid_client e → ⊢ logrel e.
  Proof.
    pattern e. apply expr_ind_mut with (P0 := fun v => valid_val v → ⊢ interp v).
    all: intros; simpl in *. 
    - iIntros "!#" (vs τ) "#Henv".
      rewrite (subst_env_arg1 (fun _ => Val v) _ (Val $ LitV $ LitUnit)); [| done].
      rewrite /interp_expr.
      iApply wp_value.
      by iApply H.
    - apply logrel_var.
    - iApply logrel_rec. by iApply H.
    - destruct H1. 
      iApply logrel_app; [by iApply H | by iApply H0].
    - admit.
    - destruct H1 as (?&?&?).
      iApply logrel_nat_binop; [done | by iApply H | by iApply H0].
    - destruct H2 as (?&?&?).
      iApply logrel_if; [by iApply H | by iApply H0 | by iApply H1].
    - destruct H1 as (?&?).
      iApply logrel_pair; [by iApply H | by iApply H0].
    - iApply logrel_fst. by iApply H.  
    - iApply logrel_snd. by iApply H.
    - iApply logrel_injl. by iApply H.
    - iApply logrel_injr. by iApply H.
    - destruct H2 as (?&?&?).
      iApply logrel_case; [by iApply H | by iApply H0 | by iApply H1].
    - iApply logrel_fork. by iApply H.
    - destruct H1 as (?&?).
      iApply logrel_alloc; [by iApply H | by iApply H0].
    - iApply logrel_load. by iApply H.
    - destruct H1 as (?&?).
      iApply logrel_store; [by iApply H | by iApply H0].
    - destruct H2 as (?&?&?).
      iApply logrel_CmpXchg; [by iApply H | by iApply H0 | by iApply H1].
    - destruct H1 as (?&?).
      iApply logrel_FAA; [by iApply H | by iApply H0].
    - admit.
    - rewrite interp_unfold. destruct l; done.   
    - intros. simpl in *.
      iApply interp_RecV. by iApply H.
    - rewrite interp_unfold. simpl.
      iExists _, _. iNext. iSplit; [done| ].
      destruct H1. 
      iSplit; [by iApply H | by iApply H0].
    - rewrite interp_unfold. simpl.
      iLeft. iExists _. iSplit; [done| ].
      by iApply H.
    - rewrite interp_unfold. simpl.
      iRight. iExists _. iSplit; [done| ].
      by iApply H.
  Qed.

End typed_interp.
