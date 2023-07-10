From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap gset excl.
From iris.base_logic Require Export gen_heap.
From trillium.prelude Require Import classical_instances.
From trillium.program_logic Require Export weakestpre adequacy.
From trillium.fairness Require Export fairness resources fair_termination fairness_finiteness fuel fuel_termination. 
From trillium.program_logic Require Import ectx_lifting.
From trillium.fairness.heap_lang Require Export lang.
From trillium.fairness.heap_lang Require Import tactics notation.
Set Default Proof Using "Type".

(* Canonical Structure ModelO (M : FairModel) := leibnizO M. *)
Canonical Structure RoleO (M : FairModel) := leibnizO (M.(fmrole)).

Class heapGpreS Σ `(LM: LiveModel heap_lang M) := HeapPreG {
  heapGpreS_inv :> invGpreS Σ;
  heapGpreS_gen_heap :> gen_heapGpreS loc val Σ;
  heapGpreS_fairness :> fairnessGpreS LM Σ;
}.

Class heapGS Σ `(LM:LiveModel heap_lang M) := HeapG {
  heap_inG :> heapGpreS Σ LM;

  heap_invGS :> invGS_gen HasNoLc Σ;
  heap_gen_heapGS :> gen_heapGS loc val Σ;

  heap_fairnessGS :> fairnessGS LM Σ;
}.

Definition heapΣ (M : FairModel): gFunctors :=
  #[ invΣ; gen_heapΣ loc val; fairnessΣ heap_lang M].

Global Instance subG_heapPreG {Σ} `{LM : LiveModel heap_lang M}:
  subG (heapΣ M) Σ → heapGpreS Σ LM.
Proof. solve_inG. Qed.

#[global] Instance heapG_irisG `{LM:LiveModel heap_lang M} `{!heapGS Σ LM} : irisG heap_lang LM Σ := {
    state_interp extr auxtr :=
      (⌜valid_state_evolution_fairness extr auxtr⌝ ∗
       gen_heap_interp (trace_last extr).2.(heap) ∗
       model_state_interp (trace_last extr).1 (trace_last auxtr))%I ;
    (* fork_post tid := λ _, tid ↦M ∅; *)
    fork_post tid := fun _ => frag_mapping_is {[ tid := ∅ ]};
}.


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

Notation "f ⇂ R" := (filter (λ '(k,v), k ∈ R) f) (at level 30).

Lemma own_proper `{inG Σ X} γ (x y: X):
  x ≡ y ->
  own γ x -∗ own γ y.
Proof. by intros ->. Qed.

Lemma auth_fuel_is_proper `{heapGS Σ Mdl} (x y : gmap (fmrole Mdl) nat):
  x = y ->
  auth_fuel_is x -∗ auth_fuel_is y.
Proof. by intros ->. Qed.


Section lifting.
Context `{LM:LiveModel heap_lang M}.
Context `{!heapGS Σ LM}.

Context `{iLM:LiveModel heap_lang iM}.
Context `{PMPP: @PartialModelPredicatesPre _ _ _ Σ iM}.


Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types tid : nat.


(* TODO: fix notations *)
Notation "tid ↦M R" := (partial_mapping_is {[ tid := R ]}) (at level 33).
Notation "tid ↦m ρ" := (partial_mapping_is {[ tid := {[ ρ ]} ]}) (at level 33).
Notation "ρ ↦F f" := (partial_fuel_is {[ ρ := f ]}) (at level 33).

Lemma wp_lift_pure_step_no_fork tid E E' Einvs Φ e1 e2 fs ϕ:
  fs ≠ ∅ ->
  PureExec ϕ 1 e1 e2 ->
  ϕ ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ 
  (|={E}[E']▷=> has_fuels_S tid fs ∗ ((has_fuels tid fs) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using. 
  intros NnO Hpe Hϕ Hinvs.
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hϕ). by apply nsteps_once_inv in Hpe. }
  iIntros "[#PMP H]". iApply wp_lift_step; eauto.
  { destruct Hps as [Hred _]. specialize (Hred inhabitant). eapply reducible_not_val; eauto. }
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  
  iMod "H". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "H" as "[Hfuels Hkont]".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(%&Hgh&Hmi)".

  (* iMod (update_no_step_enough_fuel _ _ ∅ with "Hfuels Hmi") as "H"; eauto; *)
  (*   [by intros X%dom_empty_inv_L | set_solver | set_solver | econstructor =>//; by apply fill_step |]. *)

  (* TODO: get rid of iDestruct? *)
  iDestruct (update_no_step_enough_fuel (PMPP := PMPP) with "PMP") as "-#HH".
  { by intros X%dom_empty_inv_L. }
  { econstructor =>//; by apply fill_step. }

  iDestruct ("HH" with "Hfuels Hmi") as "HH".
  iMod (fupd_mask_mono with "HH") as "H"; [apply Hinvs| ].
 

  iModIntro.
  iDestruct ("H") as (δ2 ℓ [Hlabels Hvse]) "[Hfuels Hmi]".
  iExists δ2, ℓ.
  rewrite /state_interp /=.
  rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
  repeat iSplit; last done.
  - iPureIntro. destruct ℓ =>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iApply "Hkont". iApply (has_fuels_proper with "Hfuels") =>//.
    rewrite map_filter_id //. intros ?? ?%elem_of_dom_2; set_solver.
Qed.

(* (* TODO: restore if needed *)  *)
(* Lemma wp_lift_pure_step_no_fork_remove_role *)
(*   rem s tid E E' Φ e1 e2 *)
(*   (fs: gmap (fmrole iM) nat) *)
(*   ϕ: *)
(*   fs ≠ ∅ -> *)
(*   rem ⊆ dom fs → *)
(*   rem ∩ live_roles _ s = ∅ → *)
(*   PureExec ϕ 1 e1 e2 -> *)
(*   ϕ -> *)
(*   (|={E}[E']▷=> partial_model_is s ∗ has_fuels_S tid fs ∗ *)
(*                  (partial_model_is s -∗ (has_fuels tid (fs ⇂ (dom fs ∖ rem))) -∗ WP e2 @ tid; E {{ Φ }})) *)
(*   ⊢ WP e1 @ tid; E {{ Φ }}. *)
(* Proof. *)
(*   intros NnO Hincl Hdisj Hpe Hϕ. *)
(*   have Hps: pure_step e1 e2. *)
(*   { specialize (Hpe Hϕ). by apply nsteps_once_inv in Hpe. } *)
(*   iIntros "H". iApply wp_lift_step; eauto. *)
(*   { destruct Hps as [Hred _]. specialize (Hred inhabitant). eapply reducible_not_val; eauto. } *)
(*   iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi". *)
(*   iMod "H". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver. *)
(*   iSplit; first by destruct Hps as [Hred _]. *)
(*   iNext. iIntros (e2' σ2 efs Hpstep). *)
(*   destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?). *)
(*   simplify_eq. iMod "Hclose" as "_". iMod "H" as "(Hmod & Hfuels & Hkont)". *)
(*   rewrite !app_nil_r. *)
(*   iDestruct "Hsi" as "(%&Hgh&Hmi)". *)

(*   (* TODO: restore 'rem' parameter in the lemma below *) *)
(*   iMod (update_no_step_enough_fuel _ _ rem with "Hfuels Hmi") as "H"; eauto; *)
(*     [by intros X%dom_empty_inv_L | set_solver | econstructor =>//; by apply fill_step |]. *)
(*   iModIntro. *)
(*   iDestruct ("H") as (δ2 ℓ [Hlabels Hvse]) "[Hfuels Hmi]". *)
(*   iExists δ2, ℓ. *)
(*   rewrite /state_interp /=. *)
(*   rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi". *)
(*   repeat iSplit; last done. *)
(*   - iPureIntro. destruct ℓ =>//. *)
(*   - iPureIntro. destruct Hvse as (?&?&? )=>//. *)
(*   - iPureIntro. destruct Hvse as (?&?&? )=>//. *)
(*   - iApply ("Hkont" with "Hmod"). iApply (has_fuels_proper with "Hfuels") =>//. *)
(* Qed. *)

(* Lemma wp_lift_pure_step_no_fork_2 tid E E' Φ e1 e2 (fs: gmap (fmrole Mdl) nat) R ϕ: *)
(*   R ≠ ∅ -> *)
(*   PureExec ϕ 1 e1 e2 -> *)
(*   ϕ -> *)
(*   (forall (ρ: fmrole Mdl) (f: nat), fs !! ρ = Some f -> f > 0) -> *)
(*   (|={E}[E']▷=> has_fuels tid R fs ∗ ((has_fuels tid R (fmap (λ (x: nat), (x - 1)%nat) fs)) -∗ WP e2 @ tid; E {{ Φ }})) *)
(*   ⊢ WP e1 @ tid; E {{ Φ }}. *)
(* Proof. *)

Lemma wp_lift_pure_step_no_fork' fs tid E E' Einvs Φ e1 e2:
  fs ≠ ∅ ->
  PureExec True 1 e1 e2 ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ (|={E}[E']▷=> has_fuels_S tid fs ∗ ((has_fuels tid fs) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using. 
  intros. by iApply wp_lift_pure_step_no_fork.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole tid E E' Einvs Φ e1 e2 ρ f φ:
  PureExec φ 1 e1 e2 -> φ ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ (|={E}[E']▷=> has_fuel tid ρ (S f) ∗ ((has_fuel tid ρ f) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using. 
  iIntros (???) "H". rewrite has_fuel_fuels_S.
  iApply (wp_lift_pure_step_no_fork {[ ρ := f ]} {[ρ]}); eauto; last first.
  rewrite has_fuel_fuels //. apply map_non_empty_singleton.
Qed.

Lemma wp_lift_pure_step_no_fork_take_step_stash s1 s2 tid E E' Einvs fs1 fs2 fr1 fr_stash Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  Einvs ⊆ E ->
  valid_new_fuelmap (LM := iLM) fs1 fs2 s1 s2 ρ ->
  live_roles iM s2 ∖ live_roles iM s1 ⊆ fr1 →
  fr_stash ⊆ dom fs1 →
  live_roles iM s1 ∩ fr_stash = ∅ → 
  dom fs2 ∩ fr_stash = ∅ ->
  iM.(fmtrans) s1 (Some ρ) s2 ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ (|={E}[E']▷=> partial_model_is s1 ∗ has_fuels tid fs1 ∗ partial_free_roles_are fr1 ∗
                 (partial_model_is s2 -∗ partial_free_roles_are (fr1 ∖ (live_roles iM s2 ∖ live_roles iM s1) ∪ fr_stash)
                  -∗ (has_fuels tid fs2 -∗ WP e2 @ tid; E {{ Φ }})))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using. 
  iIntros (Hpe Hφ Hinvs Hval Hfr ??? Htrans).
  have Hps: pure_step e1 e2.
  { specialize (Hpe Hφ). by apply nsteps_once_inv in Hpe. }
  iIntros "[PMP Hkont]".

  iApply wp_lift_step; eauto.
  { destruct (pure_step_safe _ e2 Hps inhabitant) as (?&?&?&?). by eapply val_stuck. }

  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "Hsi".
  iMod "Hkont". iMod fupd_mask_subseteq as "Hclose"; last iModIntro; first by set_solver.
  iSplit; first by destruct Hps as [Hred _].
  iNext. iIntros (e2' σ2 efs Hpstep).
  destruct Hps as [? Hdet]. specialize (Hdet _ _ _ _ Hpstep) as (?&?&?).
  simplify_eq. iMod "Hclose" as "_". iMod "Hkont" as "(Hmod&Hfuels&Hfr&Hkont)".
  rewrite !app_nil_r.
  iDestruct "Hsi" as "(%&Hgh&Hmi)". simpl.

  iDestruct (update_step_still_alive _ _ _ _ σ1 σ1 with "PMP Hfuels Hmod Hmi Hfr") as "H"; eauto.
  { set_solver. }
  { rewrite Hexend. eauto. }
  { econstructor =>//.
    - rewrite Hexend //=.
    - by apply fill_step. }
  (* { rewrite Hmeq. apply Hval. } *)
  iMod (fupd_mask_mono with "H") as "H"; [apply Hinvs| ]. 

  iModIntro. iDestruct "H" as (δ2 ℓ [Hlabels Hvse]) "(Hfuels&Hmod&Hmi&Hfr)".
  iExists δ2, ℓ.
  rewrite Hexend /=. list_simplifier. iFrame "Hgh Hmi".
  repeat iSplit; last done.
  - iPureIntro. destruct ℓ =>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - iPureIntro. destruct Hvse as (?&?&? )=>//.
  - by iSpecialize ("Hkont" with "Hmod Hfr Hfuels").
Qed. 

Lemma wp_lift_pure_step_no_fork_take_step s1 s2 tid E E' Einvs fs1 fs2 fr1 Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  Einvs ⊆ E ->  
  valid_new_fuelmap (LM := iLM) fs1 fs2 s1 s2 ρ ->
  live_roles iM s2 ∖ live_roles iM s1 ⊆ fr1 →
  iM.(fmtrans) s1 (Some ρ) s2 ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ (|={E}[E']▷=> partial_model_is s1 ∗ has_fuels tid fs1 ∗ partial_free_roles_are fr1 ∗
                 (partial_model_is s2 -∗ partial_free_roles_are (fr1 ∖ (live_roles iM s2 ∖ live_roles iM s1))
                  -∗ (has_fuels tid fs2 -∗ WP e2 @ tid; E {{ Φ }})))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using. 
  iIntros.
  iApply wp_lift_pure_step_no_fork_take_step_stash.
  5: { apply empty_subseteq. }
  all: eauto. 
  1, 2: set_solver.
  by rewrite union_empty_r_L.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole_take_step s1 s2 tid E E' Einvs
  (f1 f2: nat) fr Φ e1 e2 ρ φ:
  PureExec φ 1 e1 e2 -> φ ->
  Einvs ⊆ E ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (f2 ≤ iLM.(lm_fl) s2)%nat -> iM.(fmtrans) s1 (Some ρ) s2 ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ (|={E}[E']▷=> partial_model_is s1 ∗ partial_free_roles_are fr ∗ has_fuel tid ρ f1 ∗
   (partial_model_is s2 -∗ partial_free_roles_are fr -∗ (if decide (ρ ∈ live_roles iM s2) then has_fuel tid ρ f2 else (tid ↦M ∅) ) -∗
                               WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using.
  iIntros (Hpe Hφ Hinvs Hroles Hfl Hmdl).
  rewrite has_fuel_fuels.
  iIntros "[PMP H]".
  iApply (wp_lift_pure_step_no_fork_take_step _ _ _ _ _ _ {[ρ := f1]}
         (if decide (ρ ∈ live_roles iM s2) then {[ρ := f2]} else ∅) fr  with "[PMP H]"); eauto.
  - repeat split.
    + intros ?. rewrite decide_True //. rewrite lookup_singleton //=.
    + destruct (decide (ρ ∈ live_roles _ s2)); set_solver.
    + set_solver.
    + intros ρ' Hdom. destruct (decide (ρ ∈ live_roles iM s2)); set_solver.
    + intros ρ' Hneq Hin. destruct (decide (ρ ∈ live_roles iM s2)); set_solver.
    + destruct (decide (ρ ∈ live_roles iM s2)); set_solver.
    + destruct (decide (ρ ∈ live_roles iM s2)); set_solver.
  - set_solver.
  - iFrame. iMod "H". do 2 iModIntro. iMod "H" as "(Hmod&Hfr&Hfuels&Hkont)". iModIntro.
    iFrame "Hmod Hfr Hfuels". iIntros "Hmod Hfr Hfuels". iApply ("Hkont" with "Hmod [Hfr] [Hfuels]").
    + replace (fr ∖ (live_roles iM s2 ∖ live_roles iM s1)) with fr; [done|set_solver].
    + destruct (decide (ρ ∈ live_roles iM s2)).
      * rewrite -has_fuel_fuels //.
      * iDestruct "Hfuels" as "[Hf _]". rewrite dom_empty_L //.
Qed.

Lemma wp_lift_pure_step_no_fork_singlerole' tid E E' Einvs Φ e1 e2 ρ f:
  PureExec True 1 e1 e2 ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ (|={E}[E']▷=> has_fuel tid ρ (S f) ∗ ((has_fuel tid ρ f) -∗ WP e2 @ tid; E {{ Φ }}))
  ⊢ WP e1 @ tid; E {{ Φ }}.
Proof using.
  iIntros (??) "H". rewrite has_fuel_fuels_S.
  iApply (wp_lift_pure_step_no_fork' {[ ρ := f ]} {[ρ]}); last first.
  2: { done. }
  rewrite has_fuel_fuels //. apply map_non_empty_singleton.
Qed.

(* Let has_fuels_actual := has_fuels (PMPP := ActualOwnershipPartialPre).  *)
(* Let has_fuels_partial := has_fuels (PMPP := PMPP). *)
(* Let has_fuels_S_partial := has_fuels_S (PMPP := PMPP). *)

(* Unset Printing Notations. *)
(* Set Printing Implicit.  *)
(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork_nostep s tid E Einvs e Φ R1 R2
  (fs: gmap (fmrole iM) nat) (Hdisj: R1 ## R2) (Hnemp: fs ≠ ∅):
  R1 ∪ R2 = dom fs ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ (∀ tid', ▷ (has_fuels tid' (fs ⇂ R2) -∗
                WP e @ s; tid'; ⊤ {{ _, partial_mapping_is {[ tid' := ∅ ]}  }})
  ) -∗
     ▷ (has_fuels tid (fs ⇂ R1) ={E}=∗ Φ (LitV LitUnit)) -∗
     has_fuels_S tid fs -∗ WP Fork e @ s; tid; E {{ Φ }}.
Proof using.
  
  iIntros (Hunioneq Hinvs) "[PMP He] HΦ Htid". iApply wp_lift_atomic_head_step; [done|].
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".

  iDestruct (update_fork_split R1 R2 _
       (tp1 ++ ectx_language.fill K (Val $ LitV LitUnit) :: tp2 ++ [e]) fs _ _ _ e _ σ1 with "PMP Htid Hmi") as "HH".
  all: try done. 
  { rewrite -Hloc. rewrite -(language.locale_fill _ _ K). econstructor 1 =>//.
    apply fill_step, head_prim_step. econstructor. }
  { list_simplifier. exists (tp1 ++ fill K #() :: tp2). split; first by list_simplifier.
    rewrite !app_length //=. }

  iMod (fupd_mask_mono with "HH") as "HH"; [apply Hinvs| ]. 
  iDestruct "HH" as (δ2) "(Hfuels2 & Hfuels1 & Hterm & Hσ & %Hvse)". 

  iModIntro. iSplit. iPureIntro; first by eauto. iNext.
  iIntros (e2 σ2 efs Hstep).
  have [-> [-> ->]] : σ2 = σ1 ∧ efs = [e] ∧ e2 = Val $ LitV LitUnit by inv_head_step.
  iMod ("HΦ" with "Hfuels1") as "HΦ". iModIntro. iExists δ2, (Silent_step tid). iFrame.
  rewrite Hexend /=. iFrame "Hsi".
  iSplit; first by iPureIntro.
  iSplit; [|done].
  simpl. 

  list_simplifier.
  iApply (wp_strong_mono with "[Hfuels2 He] [Hterm]").
  1, 2: by reflexivity.
  { iApply "He". iFrame. }
  iIntros. iModIntro.
  by iApply "Hterm". 
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
  

Lemma wp_fork_nostep_alt s tid E Einvs e Φ
  (fs1 fs2: gmap (fmrole iM) nat)
  (DISJ: fs1 ##ₘ fs2)
  (NE: fs1 ∪ fs2 ≠ ∅)
  (Hinvs: Einvs ⊆ E):
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ∗ (∀ tid', ▷ (has_fuels tid' fs2 -∗
                WP e @ s; tid'; ⊤ {{ _, partial_mapping_is {[ tid' := ∅ ]}  }})
  ) -∗
     ▷ (has_fuels tid fs1 ={E}=∗ Φ (LitV LitUnit)) -∗
     has_fuels_S tid (fs1 ∪ fs2) -∗ WP Fork e @ s; tid; E {{ Φ }}.
Proof using.
  iIntros "[PMP FORK] FUEL1 FUEL".
  iApply (wp_fork_nostep with "[PMP FORK] [FUEL1]").
  { by eapply map_disjoint_dom_1. }
  1, 2: set_solver.
  { apply Hinvs. }
  3: done. 
  { iFrame. iIntros (?). iNext. iIntros "FUEL". iApply "FORK".
    iApply has_fuels_proper; [reflexivity| | iFrame].
    rewrite map_union_comm; auto.
    by apply leibniz_equiv_iff, gmap_filter_disj_id. }
  iNext. iIntros "FUEL". iApply "FUEL1".
  iApply has_fuels_proper; [reflexivity| | iFrame].
  by apply leibniz_equiv_iff, gmap_filter_disj_id.
Qed.   


(** Heap *)
(** The usable rules for [allocN] stated in terms of the [array] proposition
are derived in te file [array]. *)
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

(* TODO *)

Lemma wp_allocN_seq_nostep s tid E Einvs v n fs:
  fs ≠ ∅ ->
  0 < n →
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢
  {{{ has_fuels_S tid fs }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; tid; E
  {{{ l, RET LitV (LitLoc l); has_fuels tid fs ∗ [∗ list] i ∈ seq 0 (Z.to_nat n),
      (l +ₗ (i : nat)) ↦ v ∗ meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof using.
  iIntros (HnO Hn Hinvs) "#PMP".
  iIntros (Φ). iModIntro. iIntros "HfuelS HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iModIntro; iSplit; first by eauto.
  iIntros (e2 σ2 efs Hstep). iNext.
  inv_head_step.
  iMod (gen_heap_alloc_big _ (heap_array l (replicate (Z.to_nat n) v)) with "Hsi")
    as "(Hsi & Hl & Hm)".
  { apply heap_array_map_disjoint.
    rewrite replicate_length Z2Nat.id ?Hexend; auto with lia. }
  
  iDestruct (update_no_step_enough_fuel _ _ with "PMP HfuelS Hmi") as "HH". 
  { by intros ?%dom_empty_inv_L. }
  (* { set_solver. } *)
  { rewrite Hexend. apply head_locale_step. by econstructor. }

  iMod (fupd_mask_mono with "HH") as "HH"; [apply Hinvs| ]. 
  iDestruct "HH" as (δ2 ℓ) "([%Hlabel %Hvse] & Hfuel & Hmi)" =>//.

  iModIntro; iExists δ2, ℓ.
  rewrite Hexend //=. iFrame "Hmi Hsi".
  repeat iSplit =>//.
  iApply "HΦ". iSplitL "Hfuel".
  { iApply (has_fuels_proper with "Hfuel") =>//.
    rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver. }
  iApply big_sepL_sep. iSplitL "Hl".
  + by iApply heap_array_to_seq_mapsto.
  + iApply (heap_array_to_seq_meta with "Hm"). by rewrite replicate_length.
Qed.

Lemma wp_alloc_nostep s tid E Einvs v fs :
  fs ≠ ∅ ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ has_fuels_S tid fs }}} Alloc (Val v) @ s; tid; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ ∗ has_fuels tid fs }}}.
Proof using. 
  iIntros (??) "#PMP". iModIntro. iIntros (Φ) "HfuelS HΦ".
  iApply (wp_allocN_seq_nostep with "PMP HfuelS"); auto with lia.
  iIntros "!>" (l) "/= (? & ? & _)". rewrite loc_add_0. by iApply "HΦ"; iFrame.
Qed.

Lemma wp_choose_nat_nostep s tid E Einvs fs :
  fs ≠ ∅ ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ has_fuels_S tid fs }}}
    ChooseNat @ s; tid; E
  {{{ (n:nat), RET LitV (LitInt n); has_fuels tid fs }}}.
Proof using. 
  iIntros (??). iIntros "#PMP". iModIntro. iIntros (Φ) "HfuelS HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr auxtr K tp1 tp2 σ1 Hvalex Hexend Hloc) "(% & Hsi & Hmi)".
  iModIntro; iSplit; eauto.
  (* TODO: Improve this so we hide the (arbitrary) choice of `n` *)
  Unshelve. 2: apply O.
  iIntros (e2 σ2 efs Hstep). iNext.
  inv_head_step.
  iDestruct (update_no_step_enough_fuel _ _ with "PMP HfuelS Hmi") as "HH".
  { by intros ?%dom_empty_inv_L. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iMod (fupd_mask_mono with "HH") as "HH"; [done| ]. 
  iDestruct "HH" as (δ2 ℓ) "([%Hlabel %Hvse] & Hfuel & Hmi)" =>//.

  iModIntro; iExists δ2, ℓ.
  rewrite Hexend //=. iFrame "Hmi Hsi".
  repeat iSplit =>//.
  iApply "HΦ".
  iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.

Lemma wp_load_nostep s tid E Einvs l q v fs:
  fs ≠ ∅ ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ ▷ l ↦{q} v ∗ has_fuels_S tid fs }}} Load (Val $ LitV $ LitLoc l) @ s; tid; E {{{ RET v; l ↦{q} v ∗ has_fuels tid fs }}}.
Proof using. 
  iIntros (??). iIntros "#PMP". iModIntro. iIntros (Φ) "[>Hl HfuelS] HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iDestruct (update_no_step_enough_fuel _ _ with "PMP HfuelS Hmi") as "HH".
  { by intros ?%dom_empty_inv_L. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }
  iMod (fupd_mask_mono with "HH") as "HH"; [done| ].
  iDestruct "HH" as (δ2 ℓ) "([%Hlabels %Hvse] & Hfuel & Hmod)" =>//.
  iModIntro; iExists _,_.
  rewrite Hexend //=. iFrame "Hsi Hmod".
  do 2 (iSplit=>//).
  iApply "HΦ". iFrame. iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.

Lemma wp_store_nostep s tid E Einvs l v' v fs:
  fs ≠ ∅ ->
  Einvs ⊆ E ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ ▷ l ↦ v' ∗ has_fuels_S tid fs }}}
    Store (Val $ LitV (LitLoc l)) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ has_fuels tid fs }}}.
Proof using. 
  iIntros (??). iIntros "#PMP". iModIntro. iIntros (Φ) "[>Hl HfuelS] HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".

  iDestruct (update_no_step_enough_fuel _ _ with "PMP HfuelS Hmi") as "HH". 
  { by intros ?%dom_empty_inv_L. }
  { rewrite Hexend. apply head_locale_step. by econstructor. }

  iMod (fupd_mask_mono with "HH") as "HH"; [done| ].
  iDestruct "HH" as (δ2 ℓ) "([%Hlabels %Hvse] & Hfuel & Hmod)" =>//.
  iModIntro; iExists _,_.
  rewrite Hexend //=. iFrame "Hsi Hmod".
  do 2 (iSplit=>//).
  iApply "HΦ". iFrame. iApply (has_fuels_proper with "Hfuel") =>//.
  rewrite map_filter_id //. intros ???%elem_of_dom_2; set_solver.
Qed.


(* TODO: clean up all those similar lemmas *)
Lemma wp_store_step_keep s tid ρ (fs1 fs2: gmap (fmrole iM) nat) fr fr_stash s1 s2 E Einvs l v' v
  (INVS: Einvs ⊆ E)
  (STEP: fmtrans iM s1 (Some ρ) s2)
  (VFM: valid_new_fuelmap fs1 fs2 s1 s2 ρ (LM := iLM))
  (LR : live_roles iM s2 ∖ live_roles iM s1 ⊆ fr) (STASH : fr_stash ⊆ dom fs1) 
  (NSL : live_roles iM s1 ∩ (fr_stash ∖ {[ρ]}) = ∅)
  (NOS2 : dom fs2 ∩ fr_stash = ∅):
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢
  {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ has_fuels tid fs1 ∗
      ▷ partial_free_roles_are fr}}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ partial_model_is s2 ∗ has_fuels tid fs2 ∗
                        partial_free_roles_are (fr ∖ (live_roles _ s2 ∖ live_roles _ s1) ∪ fr_stash)}}}. 
Proof using. 
  iIntros "#PMP !#" (Φ) "(>Hl & >Hst & >Hfuel1 & Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto.
  iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.

  rewrite Hexend.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iDestruct (update_step_still_alive _ _ _ _ _ _ _ s2 _
            (fs2)
            _ _ _ _ fr_stash
            with "PMP Hfuel1 Hst Hmi Hfr") as
    "UPD".
  
  all: eauto.
  { destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//. }
  iMod (fupd_mask_mono with "UPD") as(δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
  iModIntro; iExists δ2, ℓ. iSplit.
  { iPureIntro. simpl in *. split =>//. }
  iFrame.
  iSplit; first done.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_store_step_singlerole_keep s tid ρ (f1 f2: nat) (* fr *) s1 s2 E Einvs l v' v :
  Einvs ⊆ E ->
  f2 ≤ iLM.(lm_fl) s2 -> fmtrans iM s1 (Some ρ) s2 ->
  (ρ ∉ live_roles iM s2 -> (f2 < f1)%nat ) -> (* TODO: check Zombie case in must_decrease *)
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ has_fuel tid ρ f1
        (* ∗ ▷ partial_free_roles_are fr *)
  }}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ partial_model_is s2 ∗
                          (* partial_free_roles_are fr ∗ *)
      has_fuel tid ρ f2 }}}. 
Proof using. 
  iIntros (Hinvs Hfl Htrans Hdecr ?). iIntros "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & >Hfuel1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto.
  iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite has_fuel_fuels Hexend.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod partial_free_roles_empty as "Hfr". 
  iDestruct (update_step_still_alive _ _ _ _ _ _ _ s2 _
            ({[ ρ := f2 ]})
            _ _ _ _ ∅
            with "PMP Hfuel1 Hst Hmi Hfr") as "UPD". 
  all: eauto.
  1-4: set_solver. 
  - destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles iM s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; first (intros ρ' Hin; set_solver).
      split; set_solver.
    + (* repeat (split; set_solver). *)
      repeat (split; try set_solver).
      * intros. rewrite !lookup_singleton. simpl. eauto.
      * apply fm_live_spec in Htrans. set_solver.
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; [done |]. 
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame.
    iSplit; first done.
    iApply "HΦ". iFrame.
    (* replace (fr ∖ (live_roles iM s2 ∖ live_roles iM s1)) *)
    (*   with fr; [iFrame|set_solver]. *)
    (* rewrite union_empty_r_L. *)
    rewrite has_fuel_fuels //.
Qed.

Lemma wp_store_step_singlerole s tid ρ (f1 f2: nat) s1 s2 E Einvs l v' v :
  Einvs ⊆ E ->
  f2 ≤ iLM.(lm_fl) s2 -> fmtrans iM s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ has_fuel tid ρ f1}}}
    Store (Val $ LitV $ LitLoc l) (Val v) @ s; tid; E
  {{{ RET LitV LitUnit; l ↦ v ∗ partial_model_is s2 ∗ 
      (if decide (ρ ∈ live_roles iM s2) then has_fuel tid ρ f2 else tid ↦M ∅ ∗ partial_free_roles_are {[ ρ ]}) }}}.
Proof using. 
  iIntros (Hinvs Hfl Htrans ?). iIntros "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & >Hfuel1) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  (* iAssert (⌜ ρ ∉ fr ⌝)%I as %FRρ'. *)
  (* { rewrite has_fuel_fuels.  *)
  (*   iDestruct (partial_free_roles_fuels_disj with "[$] [$] [$]") as %?. *)
  (*   set_solver. } *)
  iSplit; first by rewrite Hexend // in Hheap;  eauto.
  iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite has_fuel_fuels Hexend.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  iMod partial_free_roles_empty as "Hfr". 
  iDestruct (update_step_still_alive _ _ _ _ _ _ _ s2 _
            (if decide (ρ ∈ live_roles iM s2) then {[ ρ := f2 ]} else ∅)
            _ _ _ _ ({[ ρ ]} ∖ live_roles _ s2)
            with "PMP Hfuel1 Hst Hmi Hfr")
    as "UPD".
  all: eauto. 
  1-3: set_solver.
  { destruct (decide (ρ ∈ live_roles iM s2)); set_solver. }
  - destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles iM s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; first (intros ρ' Hin; set_solver).
      split; set_solver.
    + repeat (split; set_solver).
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame.
    iSplit; first done.
    iApply "HΦ". iFrame.

    (* iDestruct (partial_free_roles_are_sep with "Hmod") as "[? ?]"; [set_solver| ]. *)
    (* replace (fr ∖ (live_roles iM s2 ∖ live_roles iM s1)) *)
    (*   with fr; [iFrame|set_solver]. *)
    
    destruct (decide (ρ ∈ live_roles iM s2)).
    + rewrite has_fuel_fuels //.
    + do 2 (rewrite difference_disjoint; [| set_solver]). rewrite union_empty_l. 
      iDestruct "Hfuel" as "[Hf _]". rewrite dom_empty_L //. iFrame. 
Qed.


Lemma wp_cmpxchg_fail_step_singlerole s tid ρ (f1 f2: nat) fr s1 s2 E Einvs l q v' v1 v2:
  Einvs ⊆ E ->
  v' ≠ v1 → vals_compare_safe v' v1 → f2 ≤ iLM.(lm_fl) s2 -> iM.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ ▷ l ↦{q} v' ∗ ▷ partial_model_is s1 ∗ ▷ has_fuel tid ρ f1 ∗ ▷ partial_free_roles_are fr }}} CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool false); l ↦{q} v' ∗ partial_model_is s2 ∗ partial_free_roles_are fr ∗
      (if decide (ρ ∈ live_roles iM s2) then has_fuel tid ρ f2 else tid ↦M ∅ ) }}}.
Proof using. 
  iIntros (Hinvs ?? Hfl Htrans ?) "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & >Hfuel1 & > Hfr) HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite bool_decide_false //.
  rewrite has_fuel_fuels Hexend.
  iDestruct (update_step_still_alive _ _ _ _ _ _ _ _ _
            (if decide (ρ ∈ live_roles iM s2) then {[ ρ := f2 ]} else ∅)
            with "PMP Hfuel1 Hst Hmi Hfr") as "UPD". 
  2: { apply empty_subseteq. }
  all: eauto.
  1-3: set_solver. 
  - destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles iM s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; first (intros ρ' Hin; set_solver).
      split; set_solver.
    + repeat (split; set_solver).
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
    rewrite -> bool_decide_eq_false_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame.
    iSplit; first done. iApply "HΦ". iFrame.
    replace (fr ∖ (live_roles iM s2 ∖ live_roles iM s1)) with fr; [iFrame|set_solver].
    rewrite union_empty_r_L. 
    destruct (decide (ρ ∈ live_roles iM s2)).
    + rewrite has_fuel_fuels //. iFrame. 
    + iDestruct "Hfuel" as "[Hf _]". rewrite dom_empty_L //. iFrame. 
Qed.

Lemma wp_cmpxchg_suc_step_singlerole_keep_dead  s tid ρ (f1 f2: nat) fr s1 s2 E Einvs l v' v1 v2:
  Einvs ⊆ E ->
  ρ ∉ live_roles _ s2 →
  v' = v1 → vals_compare_safe v' v1 → f2 < f1 -> iM.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ has_fuel tid ρ f1 ∗ ▷ partial_free_roles_are fr }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 ∗ partial_model_is s2 ∗ partial_free_roles_are fr ∗
      has_fuel tid ρ f2 }}}.
Proof using.
  iIntros (Hinvs ??? Hfl Htrans ?) "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & >Hfuel1 & >Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  rewrite has_fuel_fuels Hexend.
  iDestruct (update_step_still_alive _ _ _ _ _ _ _ _ _ {[ ρ := f2 ]} with "PMP Hfuel1 Hst Hmi Hfr") as "UPD". 
  2: { apply empty_subseteq. }
  all: eauto. 
  1-3: set_solver.
  - apply head_locale_step; econstructor =>//.
  - repeat (split; try done); [|set_solver|set_solver|set_solver| set_solver |].
    + intros ??. rewrite !lookup_singleton /=. lia.
    + rewrite dom_singleton singleton_subseteq_l. simplify_eq.
      (* destruct (decide (ρ ∈ live_roles _ (project_inner (trace_last atr)))); set_solver. *)
      destruct (decide (ρ ∈ live_roles _ s1)); set_solver.
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
    rewrite -> bool_decide_eq_true_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame. iSplit; first done. iApply "HΦ". iFrame.
    rewrite union_empty_r_L. 
    replace (fr ∖ (live_roles iM s2 ∖ live_roles iM s1)) with fr; [iFrame|set_solver].
    by rewrite has_fuel_fuels.
Qed.

Lemma wp_cmpxchg_suc_step_singlerole s tid ρ (f1 f2: nat) fr s1 s2 E Einvs l v' v1 v2:
  Einvs ⊆ E ->
  v' = v1 → vals_compare_safe v' v1 → f2 ≤ iLM.(lm_fl) s2 -> iM.(fmtrans) s1 (Some ρ) s2 ->
  live_roles _ s2 ⊆ live_roles _ s1 ->
  (PartialModelPredicates Einvs (LM := LM) (iLM := iLM) (PMPP := PMPP)) ⊢ {{{ ▷ l ↦ v' ∗ ▷ partial_model_is s1 ∗ ▷ has_fuel tid ρ f1 ∗ ▷ partial_free_roles_are fr }}}
    CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; tid; E
  {{{ RET PairV v' (LitV $ LitBool true); l ↦ v2 ∗ partial_model_is s2 ∗ partial_free_roles_are fr ∗
      (if decide (ρ ∈ live_roles iM s2) then has_fuel tid ρ f2 else tid ↦M ∅ ) }}}.
Proof using. 
  iIntros (Hinvs ?? Hfl Htrans ?) "#PMP". iModIntro. iIntros (Φ) "(>Hl & >Hst & >Hfuel1 & >Hfr) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (extr atr K tp1 tp2 σ1 Hval Hexend Hloc) "(% & Hsi & Hmi) !>".
  iDestruct (@gen_heap_valid with "Hsi Hl") as %Hheap.
  iSplit; first by rewrite Hexend // in Hheap;  eauto. iIntros "!>" (e2 σ2 efs Hstep).
  rewrite Hexend in Hheap. inv_head_step.
  rewrite bool_decide_true //.
  iMod (@gen_heap_update with "Hsi Hl") as "[Hsi Hl]".
  rewrite has_fuel_fuels Hexend.
  iDestruct (update_step_still_alive _ _ _ _ _ _ _ _ _
            (if decide (ρ ∈ live_roles iM s2) then {[ ρ := f2 ]} else ∅)
            with "PMP Hfuel1 Hst Hmi Hfr") as "UPD". 
  2: { apply empty_subseteq. }
  all: eauto. 
  1-3: set_solver.
  - destruct (decide (ρ ∈ live_roles iM s2)); apply head_locale_step; econstructor =>//.
  - destruct (decide (ρ ∈ live_roles iM s2)).
    + split; first by intros _; rewrite lookup_singleton /=; lia.
      split; first set_solver.
      split; first set_solver.
      split; set_solver.
    + repeat (split; set_solver).
  - iMod (fupd_mask_mono with "UPD") as (δ2 ℓ) "([%Hlab %Hvse] & Hfuel & Hst & Hfr & Hmod)"; [done| ]. 
    rewrite -> bool_decide_eq_true_2 in *; eauto.
    iModIntro; iExists δ2, ℓ. iSplit.
    { iPureIntro. simpl in *. split =>//. }
    iFrame. iSplit; first done. iApply "HΦ". rewrite union_empty_r_L. iFrame.    
    replace (fr ∖ (live_roles iM s2 ∖ live_roles iM s1)) with fr; [iFrame|set_solver].
    destruct (decide (ρ ∈ live_roles iM s2)).
    + rewrite has_fuel_fuels //. 
    + iDestruct "Hfuel" as "[Hf _]". rewrite dom_empty_L //. 
Qed.

(* Lemma wp_faa s E l i1 i2 : *)
(*   {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E *)
(*   {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}. *)
(* Proof. *)
(*   iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto. *)
(*   iIntros (σ1 κ κs n) "[Hσ Hκs] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?. *)
(*   iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep); inv_head_step. *)
(*   iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]". *)
(*   iModIntro. iSplit=>//. iFrame. by iApply "HΦ". *)
(* Qed. *)
End lifting.
 
