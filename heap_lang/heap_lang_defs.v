From iris.base_logic Require Export gen_heap.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
(* From fairness Require Export resources fuel. *)
From heap_lang Require Export lang.
From fairness Require Export execution_model.
From heap_lang Require Import tactics notation.

(* TODO: the missing fact of em_GS etc. being typeclasses
   hardens automatic resolution of their instances *)
Class heapGpreS Σ `(EM: ExecutionModel heap_lang M) := HeapPreG {
  heapGpreS_inv :> invGpreS Σ;
  heapGpreS_gen_heap :> gen_heapGpreS loc val Σ;
  heapGpreS_em :> em_preGS Σ;
}.

Class heapGS Σ `(EM: ExecutionModel heap_lang M) := HeapG {
  heap_inG :> heapGpreS Σ EM;

  heap_invGS :> invGS_gen HasNoLc Σ;
  heap_gen_heapGS :> gen_heapGS loc val Σ;

  heap_fairnessGS :> em_GS Σ;
}.

Definition heapΣ `(EM: ExecutionModel heap_lang M) : gFunctors :=
  #[ invΣ; gen_heapΣ loc val; em_Σ ].

(* TODO: automatize *)
Global Instance subG_heapPreG {Σ} `{EM: ExecutionModel heap_lang M}:
  subG (heapΣ EM) Σ → heapGpreS Σ EM.
Proof.
  intros. 
  enough (em_preGS Σ); [solve_inG| ].
  apply em_Σ_subG. solve_inG.
Qed. 

#[global] Instance heapG_irisG `{EM: ExecutionModel heap_lang M} `{HGS: !heapGS Σ EM}:
  irisG heap_lang M Σ := {
    state_interp extr auxtr :=
      (⌜em_valid_state_evolution_fairness extr auxtr⌝ ∗
       gen_heap_interp (trace_last extr).2.(heap) ∗
       em_msi (trace_last extr) (trace_last auxtr) (em_GS0 := heap_fairnessGS))%I ;
    fork_post tid := fun _ => em_thread_post tid (em_GS0 := heap_fairnessGS);
}.

Section GeneralProperties.
  Context `{EM: ExecutionModel heap_lang M}. 
  Context `{HGS: @heapGS Σ _ EM}.
  Let eGS := heap_fairnessGS. 

  Lemma posts_of_empty_mapping  (e1 e: expr) v (tid : nat) (tp : list expr):
    tp !! tid = Some e ->
    to_val e = Some v ->
    (* posts_of tp ( *)
    (*     (fun _ => em_thread_post 0%nat (em_GS0 := eGS)) *)
    (*                ::  (map (λ '(tnew, e), fork_post (locale_of tnew e)) (prefixes_from [e1] (drop (length [e1]) tp)))) *)
    cur_posts tp e1 (fun _ => em_thread_post 0%nat (em_GS0 := eGS))
      -∗
      em_thread_post tid (em_GS0 := eGS).
  Proof.
    intros Hsome Hval. simpl.
    
    rewrite /cur_posts. 
    rewrite (big_sepL_elem_of (λ x, x.2 x.1) _ (v, (fun _ => em_thread_post tid)) _) //.
    apply elem_of_list_omap.
    exists (e, (fun _ => em_thread_post tid (em_GS0 := eGS))); split; last first.
    - simpl. apply fmap_Some. exists v. split; done.
    - destruct tp as [|e1' tp]; first set_solver. simpl.
      apply elem_of_cons.
      destruct tid as [|tid]; [left|right]; first by simpl in Hsome; simplify_eq.
      apply elem_of_lookup_zip_with. eexists tid, e, _. do 2 split =>//.
      rewrite /locale_of /=.
      rewrite list_lookup_fmap fmap_Some. simpl in Hsome.
      exists (e1 :: take tid tp, e). rewrite drop_0. split.
      + erewrite prefixes_from_lookup =>//.
      + rewrite /locale_of /= take_length_le //.
        assert (tid < length tp)%nat; last lia. by eapply lookup_lt_Some.
  Qed.

  (* TODO: upstream? *)
  Lemma gmap_filter_dom_id {K A: Type} `{Countable K} (m: gmap K A):
    filter (fun '(k, _) => k ∈ dom m) m = m.
  Proof.
    rewrite map_filter_id; [done| ].
    intros. by eapply elem_of_dom_2. 
  Qed. 
  
  (* TODO: upstream? *)
  Lemma gmap_empty_subseteq_equiv {K A: Type} `{Countable K} (m: gmap K A):
  m ⊆ ∅ <-> m = ∅. 
  Proof.
    clear.
    split; [| set_solver].
    intros E. destruct (map_eq_dec_empty m); try set_solver.
    apply map_choose in n as (?&?&?).
    eapply lookup_weaken in E; set_solver. 
  Qed. 
  
  (* TODO: upstream? *)
  Lemma gmap_filter_disj_id {K A: Type} `{Countable K} (m1 m2: gmap K A)
    (DISJ: m1 ##ₘ m2):
    m1 = filter (λ '(k, _), k ∈ dom m1) (m1 ∪ m2).
  Proof.
    rewrite map_filter_union; auto.
    rewrite map_union_comm; [| by apply map_disjoint_filter]. 
    rewrite gmap_filter_dom_id.
    symmetry. apply map_subseteq_union. etransitivity; [| apply map_empty_subseteq].
    apply gmap_empty_subseteq_equiv. 
    eapply map_filter_empty_iff. apply map_Forall_lookup_2.
    intros. intros [? ?]%elem_of_dom. eapply map_disjoint_spec; eauto.
  Qed. 

End GeneralProperties.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l (DfracOwn q) v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.
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
(* Local Hint Extern 0 (head_reducible_no_obs _ _) => eexists _, _, _; simpl : core. *)

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
