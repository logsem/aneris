From iris.base_logic Require Export gen_heap. 
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From heap_lang Require Export lang.
From trillium.program_logic Require Export execution_model iris_em.
From heap_lang Require Import tactics notation.



Class heap1GpreS Σ := HeapPreG {
  (* heapGpreS_inv :: invGpreS Σ; *)
  heapGpreS_gen_heap :: gen_heapGpreS loc val Σ;
  (* heapGpreS_em :: em_preGS Σ; *)
}.


Class heap1GS Σ := HeapG {
  heap_inG :: heap1GpreS Σ;
  (* heap_invGS :: invGS_gen HasNoLc Σ; *)
  heap_gen_heapGS :: gen_heapGS loc val Σ;
  (* heap_fairnessGS :: em_GS Σ; *)
}.

Definition heap1Σ : gFunctors :=
  #[ (* invΣ;  *)gen_heapΣ loc val  (* em_Σ *) ].


(* TODO: automatize *)
Global Instance subG_heap1PreG {Σ}:
  subG (heap1Σ) Σ → heap1GpreS Σ.
Proof. solve_inG. Qed.

Global Instance HeapLangEM: LangEM heap_lang. 
refine {| lgem_GS := heap1GS;
          lgem_si `{heap1GS Σ} := fun c => gen_heap_interp (heap c);
          lgem_init_resource `{heap1GS Σ} := fun c => ([∗ map] l↦v ∈ (heap c.2), pointsto l (DfracOwn 1) v)%I; |}. 
- intros. eapply subG_heap1PreG. apply H.
- simpl. intros Σ PRE c.
  iMod (gen_heap_init c.2.(heap)) as (HEAP) "(HEAP & PTO & _)".
  iModIntro. simpl. unshelve iExists _; [done| ].
  iFrame.
Defined.

(** definitions to keep the existing proofs and TC inference working *)
Class heapGpreS {Σ M} {EM: ExecutionModel heap_lang M} := {
  heap_iemgPres :: @IEMGpreS _ _ HeapLangEM EM Σ;
  heap_fairnessGpreS: em_preGS Σ := @iemGpreS_em _ _ _ _ _ heap_iemgPres;
}.

Class heapGS {Σ M} {EM: ExecutionModel heap_lang M} := {
  heap_iemgs :: @IEMGS _ _ HeapLangEM EM Σ;
  heap_fairnessGS: em_GS Σ := @iem_fairnessGS _ _ _ _ _ heap_iemgs;
}.

Global Instance heapPre_of_iemPre {Σ M} {EM: ExecutionModel heap_lang M}
  (hGS: @heapGpreS Σ _ EM):
  gen_heapGpreS loc val Σ.
Proof using. apply hGS. Defined.

Global Instance heap_of_iem {Σ M} {EM: ExecutionModel heap_lang M}
  (hGS: @heapGS Σ _ EM):
  gen_heapGS loc val Σ.
Proof using. apply hGS. Defined.


Section GeneralProperties.
  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{HGS: @heapGS Σ _ EM}.

  Existing Instance EM.
  Let eGS := heap_fairnessGS.
    
  Lemma posts_of_empty_mapping_multiple  (es e: expr) v (tid : nat) (tp : list expr):
    tp !! tid = Some e ->
    to_val e = Some v ->
    (* cur_posts tp e1 (fun _ => em_thread_post 0%nat (em_GS0 := eGS)) -∗ *)
    (let Φs := map (fun τ v => @em_thread_post heap_lang M EM Σ eGS τ v) (seq 0 (length tp)) in
      posts_of tp Φs) -∗
    em_thread_post tid v (em_GS0 := eGS).
  Proof.
    intros Hsome Hval. simpl.
    
    rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (fun v => em_thread_post tid v)) _) //.
    { eauto. } 
    apply elem_of_list_omap.
    exists (e, (fun v => em_thread_post tid v (em_GS0 := eGS))); split; last first.
    - simpl. apply fmap_Some. exists v. split; done. 
    - destruct tp as [|e1' tp]; first set_solver. simpl.
      apply elem_of_cons.
      destruct tid as [|tid]; [left|right]; first by simpl in Hsome; simplify_eq.
      apply elem_of_lookup_zip_with. eexists tid, e, _. do 2 split =>//.
      rewrite /locale_of /=.
      rewrite list_lookup_fmap fmap_Some. simpl in Hsome.
      exists (S tid). split; auto.
      rewrite lookup_seq_lt.
      { set_solver. }
      eapply lookup_lt_is_Some; eauto. 
  Qed.

  (* TODO: derive from previous? *)
  Lemma posts_of_empty_mapping  (e1 e: expr) v (tid : nat) (tp : list expr):
    tp !! tid = Some e ->
    to_val e = Some v ->
    cur_posts tp e1 (fun (* τ  *) v => @em_thread_post heap_lang M EM Σ eGS 0%nat v) -∗
    em_thread_post tid v (em_GS0 := eGS).
  Proof.
    intros Hsome Hval. simpl.
    
    rewrite /cur_posts. 
    rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (fun v => em_thread_post tid v)) _) //.
    { eauto. } 
    apply elem_of_list_omap.
    exists (e, (fun v => em_thread_post tid v (em_GS0 := eGS))); split; last first.
    - simpl. apply fmap_Some. exists v. split; done.
    - destruct tp as [|e1' tp]; first set_solver. simpl.
      apply elem_of_cons.
      destruct tid as [|tid]; [left|right]; first by simpl in Hsome; simplify_eq.
      apply elem_of_lookup_zip_with. eexists tid, e, _. do 2 split =>//.
      rewrite /locale_of /=.
      rewrite list_lookup_fmap fmap_Some. simpl in Hsome.
      exists (e1 :: take tid tp, e). rewrite drop_0. split.
      + erewrite prefixes_from_lookup =>//.
      + rewrite /locale_of /= length_take_le //.
        assert (tid < length tp)%nat; last lia. by eapply lookup_lt_Some.
  Qed.
  
End GeneralProperties.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (pointsto (L:=loc) (V:=val) l (DfracOwn q) v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (pointsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CmpXchg _ _ _) _ _ _ _) => eapply CmpXchgS : core.
Local Hint Extern 0 (head_step (AllocN _ _) _ _ _ _) => apply alloc_fresh : core.
Local Hint Resolve to_of_val : core.

#[global] Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
#[global] Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

#[global] Instance rec_atomic s f x e : Atomic s (Rec f x e).
Proof. solve_atomic. Qed.
#[global] Instance pair_atomic s v1 v2 : Atomic s (Pair (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance injl_atomic s v : Atomic s (InjL (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance injr_atomic s v : Atomic s (InjR (Val v)).
Proof. solve_atomic. Qed.
(** The instance below is a more general version of [Skip] *)
#[global] Instance beta_atomic s f x v1 v2 : Atomic s (App (RecV f x (Val v1)) (Val v2)).
Proof. destruct f, x; solve_atomic. Qed.
#[global] Instance unop_atomic s op v : Atomic s (UnOp op (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance binop_atomic s op v1 v2 : Atomic s (BinOp op (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance if_true_atomic s v1 e2 : Atomic s (If (Val $ LitV $ LitBool true) (Val v1) e2).
Proof. solve_atomic. Qed.
#[global] Instance if_false_atomic s e1 v2 : Atomic s (If (Val $ LitV $ LitBool false) e1 (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance fst_atomic s v : Atomic s (Fst (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance snd_atomic s v : Atomic s (Snd (Val v)).
Proof. solve_atomic. Qed.

#[global] Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.

#[global] Instance alloc_atomic s v w : Atomic s (AllocN (Val v) (Val w)).
Proof. solve_atomic. Qed.
#[global] Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
#[global] Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance cmpxchg_atomic s v0 v1 v2 : Atomic s (CmpXchg (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
#[global] Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

(** The behavior of the various [wp_] tactics with regard to lambda differs in
the following way:

- [wp_pures] does *not* reduce lambdas/recs that are hidden behind a definition.
- [wp_rec] and [wp_lam] reduce lambdas/recs that are hidden behind a definition.

To realize this behavior, we define the class [AsRecV v f x erec], which takes a
value [v] as its input, and turns it into a [RecV f x erec] via the instance
[AsRecV_recv : AsRecV (RecV f x e) f x e]. We register this instance via
[Hint Extern] so that it is only used if [v] is syntactically a lambda/rec, and
not if [v] contains a lambda/rec that is hidden behind a definition.

To make sure that [wp_rec] and [wp_lam] do reduce lambdas/recs that are hidden
behind a definition, we activate [AsRecV_recv] by hand in these tactics. *)
Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
#[global] Hint Mode AsRecV ! - - - : typeclass_instances.
Definition AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.
#[global] Hint Extern 0 (AsRecV (RecV _ _ _) _ _ _) =>
  apply AsRecV_recv : typeclass_instances.

#[global] Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
#[global] Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_beta f x (erec : expr) (v1 v2 : val) `{!AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

#[global] Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

#[global] Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v') | 10.
Proof. solve_pure_exec. Qed.
(* Higher-priority instance for [EqOp]. *)
#[global] Instance pure_eqop v1 v2 :
  PureExec (vals_compare_safe v1 v2) 1
    (BinOp EqOp (Val v1) (Val v2))
    (Val $ LitV $ LitBool $ bool_decide (v1 = v2)) | 1.
Proof.
  intros Hcompare.
  cut (bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2)).
  { intros. revert Hcompare. solve_pure_exec. }
  rewrite /bin_op_eval /= decide_True //.
Qed.

#[global] Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

#[global] Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

#[global] Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

#[global] Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.


Section Heap.
  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{HGS: @heapGS Σ _ EM}.

  (** Heap *)
  (** The usable rules for [allocN] stated in terms of the [array] proposition
are   derived in te file [array]. *)
  Lemma heap_array_to_seq_meta l vs (n : nat) :
    length vs = n →
    ([∗ map] l' ↦ _ ∈ heap_array l vs, meta_token l' ⊤) -∗
      [∗ list] i ∈ seq 0 n, meta_token (l +ₗ (i : nat)) ⊤.
  Proof.
    iIntros (<-) "Hvs". iInduction vs as [|v vs] "IH" forall (l)=> //=.
    rewrite big_opM_union; last first.
    { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
    intros (j&?&Hjl&_)%heap_array_lookup.
    rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
    rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite <-loc_add_assoc.
    rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
  Qed.

  Lemma heap_array_to_seq_mapsto l v (n : nat) :
    ([∗ map] l' ↦ v ∈ heap_array l (replicate n v), l' ↦ v) -∗
  [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
  Proof.
    iIntros "Hvs". iInduction n as [|n] "IH" forall (l); simpl.
    { done. }
    rewrite big_opM_union; last first.
    { apply map_disjoint_spec=> l' v1 v2 /lookup_singleton_Some [-> _].
      intros (j&?&Hjl&_)%heap_array_lookup.
      rewrite loc_add_assoc -{1}[l']loc_add_0 in Hjl. simplify_eq; lia. }
    rewrite loc_add_0 -fmap_S_seq big_sepL_fmap.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
    setoid_rewrite <-loc_add_assoc.
    rewrite big_opM_singleton; iDestruct "Hvs" as "[$ Hvs]". by iApply "IH".
  Qed.

End Heap.
