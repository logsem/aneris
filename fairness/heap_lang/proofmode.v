From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From iris.proofmode Require Export tactics.
From trillium.program_logic Require Import atomic.
From trillium.fairness.heap_lang Require Export tactics lifting. (* derived_laws. *)
From trillium.fairness.heap_lang Require Import notation.
From trillium.fairness.heap_lang Require Import heap_lang_defs. 
From iris.prelude Require Import options.
Import uPred.

Lemma tac_wp_expr_eval `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM}
  Δ tid E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ tid; E {{ Φ }}) → envs_entails Δ (WP e @ tid; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic3(t) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
    notypeclasses refine (tac_wp_expr_eval _ _ _ _ e _ _ _);
      [let x := fresh in intros x; t; unfold x; notypeclasses refine eq_refl|]
  | _ => fail "wp_expr_eval: not a 'wp'"
  end.
Ltac wp_expr_simpl := wp_expr_eval simpl. 

Lemma tac_wp_pure_helper `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} 
  `{iLM: LiveModel G iM LSI_True} `{Countable G}
  `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ iM}  
  tid E Einvs K e1 e2
  (fs: gmap (fmrole iM) nat)
  (* fs *)
  φ n Φ :
(* >>>>>>> origin/pmp_resource *)
  fs ≠ ∅ ->
  PureExec φ n e1 e2 →
  φ →
  (PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := heap_fairnessGS)) -∗ ( ▷^n (has_fuels tid fs -∗ WP (fill K e2) @ tid; E {{ Φ }})) -∗
  has_fuels_plus n tid fs -∗
  WP (fill K e1) @ tid; E {{ Φ }}.
Proof. 
  intros Hne HPE Hφ. specialize (HPE Hφ).
  revert e1 e2 fs Hne HPE. induction n; intros e1 e2 fs Hne HPE.
  { inversion HPE. rewrite has_fuel_fuels_plus_0. simplify_eq.
    iIntros "#? ?". iFrame. }   

  inversion HPE; simplify_eq.

  iIntros "#PMP H Hf".
  rewrite has_fuels_plus_split_S.

  iApply (wp_lift_pure_step_no_fork _ _ _ _ _ _ _ ((λ m : nat, (n + m)%nat) <$> fs)) =>//.
  { by intros ?%fmap_empty_inv. }
  { econstructor =>//; [ by eapply pure_step_ctx | constructor ]. }
  iSplitR; [done| ]. 
  iModIntro; iFrame. do 2 iModIntro.
  iIntros "Hf".
  iApply (IHn _ _ _ with "[PMP] [H] [Hf]") => //. 
Qed.

Lemma equiv_wand {Σ} (P Q: iProp Σ):
  P ≡ Q ->
  P -∗ Q.
Proof. by intros ->. Qed.

Lemma maps_gt_n {Mdl} (fs: gmap (fmrole Mdl) _) n:
  (∀ ρ f, fs !! ρ = Some f -> f >= n)%nat ->
  fs = (λ m, n + m)%nat <$> ((λ m, m - n)%nat <$> fs).
Proof.
  intros Hgt.
  apply map_eq. intros ρ.
  rewrite -map_fmap_compose !lookup_fmap.
  destruct (fs !! ρ) as [f|] eqn:? =>//=. f_equiv.
  assert (f >= n)%nat by eauto.
  apply leibniz_equiv_iff. lia.
Qed.

Lemma has_fuels_gt_n  
  (* `{PMP: PartialModelPredicates heap_lang (M := M) (iM := iM) (LM := LM) (iLM := iLM)} *)
  `{Countable G} `{PMPP: @PartialModelPredicatesPre G _ _ Σ iM}
  (fs: gmap (fmrole iM) _) n tid:
  (∀ ρ f, fs !! ρ = Some f -> f >= n)%nat ->
  has_fuels tid fs (PMPP := PMPP) ⊣⊢ has_fuels tid ((λ m, n + m)%nat <$> ((λ m, m - n)%nat <$> fs)) (PMPP := PMPP).
Proof. intros ?. rewrite {1}(maps_gt_n fs n) //. Qed.

Lemma has_fuels_gt_1
  `{Countable G} `{PMPP: @PartialModelPredicatesPre G _ _ Σ iM}
  (fs: gmap (fmrole iM) _) tid:
  (∀ ρ f, fs !! ρ = Some f -> f >= 1)%nat ->
  has_fuels tid fs ⊣⊢ has_fuels_S tid (((λ m, m - 1)%nat <$> fs)).
Proof. intros ?. by rewrite has_fuels_gt_n //. Qed.

Lemma tac_wp_pure_helper_2 `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM}
  `{iLM: LiveModel G iM LSI_True} `{Countable G}
  (* `{!fairnessGS iLM Σ}   *)
  `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ iM}
  tid E Einvs K e1 e2
  (fs: gmap (fmrole iM) nat)
  φ n Φ :
  (∀ ρ f, fs !! ρ = Some f -> f >= n)%nat ->
  fs ≠ ∅ ->
  PureExec φ n e1 e2 →
  φ →
  (PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := heap_fairnessGS)) -∗ ( ▷^n ((has_fuels tid ((λ m, m - n)%nat <$> fs)) -∗ WP (fill K e2) @ tid; E {{ Φ }})) -∗
  has_fuels tid fs -∗
  WP (fill K e1) @ tid; E {{ Φ }}.
Proof.
  iIntros (Hfs Hne Hpe Hphi) "#PMP H Hf".
  rewrite (has_fuels_gt_n fs n) //.
  iApply (tac_wp_pure_helper with "PMP H [Hf]") =>//.
  by intros ?%fmap_empty_inv.
Qed.

(* Upstream? *)
Lemma maybe_into_latersN_envs_dom {PROP} (Γ Δ: envs PROP) n i:
  MaybeIntoLaterNEnvs n Γ Δ →
  envs_lookup i Γ = None →
  envs_lookup i Δ = None.
Proof.
  intros [??] ?. destruct Γ as [Γp Γs]. destruct Δ as [Δp Δs].
  simpl.
  destruct (env_lookup i Δp) eqn:Hlk.
  - assert (HnN: env_lookup i Γp ≠ None).
    { intros contra%transform_intuitionistic_env_dom.
      rewrite /= in contra. simplify_eq. }
    rewrite not_eq_None_Some in HnN. destruct HnN as [? Hlk'].
    by rewrite /= Hlk' in H.
  - rewrite /= in H.
    destruct (env_lookup i Γp); [simplify_eq|].
    destruct (env_lookup i Γs) eqn:Heq =>//.
    apply transform_spatial_env_dom in Heq.
    by rewrite Heq.
Qed.

Lemma maybe_into_latersN_envs_wf {PROP} (Γ Δ: envs PROP) n:
  MaybeIntoLaterNEnvs n Γ Δ →
  envs_wf Γ →
  envs_wf Δ.
Proof.
  intros [??] [? ? Hdisj]. destruct Γ as [Γp Γs]. destruct Δ as [Δp Δs]. constructor.
  - by apply transform_intuitionistic_env_wf.
  - by apply transform_spatial_env_wf.
  - intros i. destruct (Hdisj i);
      [ by left; apply transform_intuitionistic_env_dom |
        by right;  apply transform_spatial_env_dom].
Qed.

Lemma envs_delete_wf {PROP} i p (Δ: envs PROP) : envs_wf Δ → envs_wf (envs_delete true i p Δ).
Proof.
  intros [?? Hdisj]; destruct Δ. constructor.
  - destruct p; simpl; [by apply env_delete_wf|done].
  - destruct p; simpl; [done|by apply env_delete_wf].
  - intro j. destruct (Hdisj j).
    + left. destruct p; [|done]. simpl in *.
      destruct (decide (i = j)) as [->|?].
      * rewrite env_lookup_env_delete //.
      * rewrite env_lookup_env_delete_ne //.
    + right. destruct p; [done|].
      destruct (decide (i = j)) as [->|?].
      * rewrite env_lookup_env_delete //.
      * rewrite env_lookup_env_delete_ne //.
Qed.

Lemma tac_wp_pure `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM}
  `{iLM: LiveModel G iM LSI_True} `{Countable G}
  (* `{!fairnessGS iLM Σ}   *)
  `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ iM}
  Δ Δ'other tid E Einvs i K e1 e2 φ n Φ
  (fs: gmap (fmrole iM) nat)
  :
  (∀ (ρ: fmrole iM) (f : nat), fs !! ρ = Some f → (f ≥ n)%nat) ->
  fs ≠ ∅ ->
  PureExec φ n e1 e2 →
  φ →
  envs_lookup i Δ = Some (false, has_fuels tid fs)%I →
  let Δother := envs_delete true i false Δ in
  MaybeIntoLaterNEnvs n Δother Δ'other →
  let Δ' := envs_snoc Δ'other false i (has_fuels tid ((λ m, m - n)%nat <$> fs)) in
  envs_entails Δ' ((PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := heap_fairnessGS)) -∗
WP (fill K e2) @ tid; E {{ Φ }}) →
  envs_entails Δ ((PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := heap_fairnessGS)) -∗
WP (fill K e1) @ tid; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ???.
  intros ?? Δother Hlater Δ' Hccl.
  iIntros "H #PMP".
  iAssert (⌜envs_wf Δ⌝)%I as %Hwf.
  (* { unfold of_envs, of_envs', envs_wf. iDestruct "H" as "[% _]". by iPureIntro. } *)
  { unfold of_envs, of_envs', envs_wf. iDestruct "H" as "[%HH _]". by iPureIntro. }

  rewrite envs_lookup_sound // /= -/Δother. iDestruct "H" as "[H1 H2]".
  rewrite into_laterN_env_sound.

  iApply (tac_wp_pure_helper_2 with "[PMP] [H2] [H1]") =>//.
  iNext. simpl. iIntros "H". iApply (Hccl with "[-PMP]"); [| done]. 
  rewrite /Δ' /= (envs_snoc_sound Δ'other false i); first by iApply "H2".
  eapply maybe_into_latersN_envs_dom =>//. rewrite /Δother.
  eapply envs_lookup_envs_delete =>//.
  Unshelve. all: apply H0.
Qed.


Lemma tac_wp_value_nofupd `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM}
  Δ tid E Φ v :
  envs_entails Δ (Φ v) → envs_entails Δ (WP (Val v) @ tid; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply wp_value. Qed.

Lemma tac_wp_value `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM}
  Δ tid E (Φ : val → iPropI Σ) v :
  envs_entails Δ (|={E}=> Φ v) → envs_entails Δ (WP (Val v) @ tid; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. iIntros "?". by iApply wp_value_fupd. Qed.

(** Simplify the goal if it is [WP] of a value.
  If the postcondition already allows a fupd, do not add a second one.
  But otherwise, *do* add a fupd. This ensures that all the lemmas applied
  here are bidirectional, so we never will make a goal unprovable. *)
Ltac wp_value_head :=
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, fupd ?E _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E (Val _) (λ _, wp _ ?E _ _ _)) =>
      eapply tac_wp_value_nofupd
  | |- envs_entails _ (wp ?s ?E _ (Val _) _) =>
      eapply tac_wp_value
  end.

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context. *)
(*      The other two branches are for when either one of the branches reduces to *)
(*      [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

Tactic Notation "solve_pure_exec" :=
  lazymatch goal with
  | |- PureExec _ _ ?e _ =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      eapply (pure_exec_fill K _ _ e');
      [tc_solve                       (* PureExec *)
      (* |try solve_vals_compare_safe    (* The pure condition for PureExec -- handles trivial goals, including [vals_compare_safe] *) *)
      ])
    || fail "failed :("
  end.


Global Hint Extern 0 (PureExec _ _ _ _) => solve_pure_exec: core.
Global Hint Extern 0 (vals_compare_safe _ _) => solve_vals_compare_safe: core.


Ltac solve_fuel_positive :=
        unfold singletonM, map_singleton; intros ??;
        repeat progress match goal with
        | [|- <[ ?x := _ ]> _ !! ?r = Some _ -> _] =>
            destruct (decide (x = r)) as [->| ?];
            [rewrite lookup_insert; intros ?; simplify_eq; lia |
             rewrite lookup_insert_ne; [ try done | done]]
        end.
Ltac simpl_has_fuels :=
  iEval (rewrite ?[in has_fuels _ _]fmap_insert ?[in has_fuels _ _]/= ?[in has_fuels _ _]fmap_empty) in "#∗".
Tactic Notation "wp_pure" open_constr(efoc) :=
  let solve_fuel _ :=
    let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
    iAssumptionCore || fail "wp_pure: cannot find" fs in
  iStartProof;
  rewrite ?has_fuel_fuels;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ _ K e');
        [
        |
        | tc_solve
        | trivial
        | let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
          iAssumptionCore || fail "wp_pures: cannot find" fs
        |tc_solve
        | pm_reduce;
          simpl_has_fuels;
          wp_finish
        ] ; [ solve_fuel_positive
            | try apply map_non_empty_singleton; try apply insert_non_empty; try done
            |])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  | _ => fail "wp_pure: not a 'wp'"
  end.

(* TODO: do this in one go, without [repeat]. *)
Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

(** Unlike [wp_pures], the tactics [wp_rec] and [wp_lam] should also reduce
lambdas/recs that are hidden behind a definition, i.e. they should use
[AsRecV_recv] as a proper instance instead of a [Hint Extern].

We achieve this by putting [AsRecV_recv] in the current environment so that it
can be used as an instance by the typeclass resolution system. We then perform
the reduction, and finally we clear this new hypothesis. *)
Tactic Notation "wp_rec" :=
  let H := fresh in
  assert (H := AsRecV_recv);
  wp_pure (App _ _);
  clear H.

Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_if_true" := wp_pure (If (LitV (LitBool true)) _ _).
Tactic Notation "wp_if_false" := wp_pure (If (LitV (LitBool false)) _ _).
Tactic Notation "wp_unop" := wp_pure (UnOp _ _).
Tactic Notation "wp_binop" := wp_pure (BinOp _ _ _).
Tactic Notation "wp_op" := wp_unop || wp_binop.
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_pure (Rec BAnon (BNamed _) _); wp_lam.
Tactic Notation "wp_seq" := wp_pure (Rec BAnon BAnon _); wp_lam.
Tactic Notation "wp_proj" := wp_pure (Fst _) || wp_pure (Snd _).
Tactic Notation "wp_case" := wp_pure (Case _ _ _).
Tactic Notation "wp_match" := wp_case; wp_pure (Rec _ _ _); wp_lam.
Tactic Notation "wp_inj" := wp_pure (InjL _) || wp_pure (InjR _).
Tactic Notation "wp_pair" := wp_pure (Pair _ _).
Tactic Notation "wp_closure" := wp_pure (Rec _ _ _).

Lemma tac_wp_bind `{EM: ExecutionModel heap_lang M} `{@heapGS Σ _ EM} 
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

(** Heap tactics *)
Section heap.
Context `{EM: ExecutionModel heap_lang M}.
Context `{@heapGS Σ _ EM}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types v : val.
Implicit Types tid : locale heap_lang.

Context `{iLM: LiveModel G iM LSI_True} `{Countable G}.
Context `{!fairnessGS iLM Σ}. 
(* Context `{PMP: PartialModelPredicates heap_lang (M := M) (iM := iM) (LM := LM) (iLM := iLM)}.  *)
Context `{PMPP: @PartialModelPredicatesPre (locale heap_lang) _ _ Σ iM}. 

(* Lemma tac_wp_allocN Δ Δ' s E j K v n Φ : *)
(*   (0 < n)%Z → *)
(*   MaybeIntoLaterNEnvs 1 Δ Δ' → *)
(*   (∀ l, *)
(*     match envs_app false (Esnoc Enil j (heap_array l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ' with *)
(*     | Some Δ'' => *)
(*        envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l) @ s; E {{ Φ }}) *)
(*     | None => False *)
(*     end) → *)
(*   envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite envs_entails_eq=> ? ? HΔ. *)
(*   rewrite -wp_bind. eapply wand_apply; first exact: wp_allocN. *)
(*   rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l. *)
(*   specialize (HΔ l). *)
(*   destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ]. *)
(*   rewrite envs_app_sound //; simpl. *)
(*   apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r. *)
(* Qed. *)
(* Lemma tac_twp_allocN Δ s E j K v n Φ : *)
(*   (0 < n)%Z → *)
(*   (∀ l, *)
(*     match envs_app false (Esnoc Enil j (array l (DfracOwn 1) (replicate (Z.to_nat n) v))) Δ with *)
(*     | Some Δ' => *)
(*        envs_entails Δ' (WP fill K (Val $ LitV $ LitLoc l) @ s; E [{ Φ }]) *)
(*     | None => False *)
(*     end) → *)
(*   envs_entails Δ (WP fill K (AllocN (Val $ LitV $ LitInt n) (Val v)) @ s; E [{ Φ }]). *)
(* Proof. *)
(*   rewrite envs_entails_eq=> ? HΔ. *)
(*   rewrite -twp_bind. eapply wand_apply; first exact: twp_allocN. *)
(*   rewrite left_id. apply forall_intro=> l. *)
(*   specialize (HΔ l). *)
(*   destruct (envs_app _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ]. *)
(*   rewrite envs_app_sound //; simpl. *)
(*   apply wand_intro_l. by rewrite (sep_elim_l (l ↦∗ _)%I) right_id wand_elim_r. *)
(* Qed. *)

(* Lemma tac_wp_alloc Δ Δ' s E j K v Φ : *)
(*   MaybeIntoLaterNEnvs 1 Δ Δ' → *)
(*   (∀ l, *)
(*     match envs_app false (Esnoc Enil j (l ↦ v)) Δ' with *)
(*     | Some Δ'' => *)
(*        envs_entails Δ'' (WP fill K (Val $ LitV l) @ s; E {{ Φ }}) *)
(*     | None => False *)
(*     end) → *)
(*   envs_entails Δ (WP fill K (Alloc (Val v)) @ s; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite envs_entails_eq=> ? HΔ. *)
(*   rewrite -wp_bind. eapply wand_apply; first exact: wp_alloc. *)
(*   rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l. *)
(*   specialize (HΔ l). *)
(*   destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ]. *)
(*   rewrite envs_app_sound //; simpl. *)
(*   apply wand_intro_l. by rewrite (sep_elim_l (l ↦ v)%I) right_id wand_elim_r. *)
(* Qed. *)
(* Lemma tac_twp_alloc Δ s E j K v Φ : *)
(*   (∀ l, *)
(*     match envs_app false (Esnoc Enil j (l ↦ v)) Δ with *)
(*     | Some Δ' => *)
(*        envs_entails Δ' (WP fill K (Val $ LitV $ LitLoc l) @ s; E [{ Φ }]) *)
(*     | None => False *)
(*     end) → *)
(*   envs_entails Δ (WP fill K (Alloc (Val v)) @ s; E [{ Φ }]). *)
(* Proof. *)
(*   rewrite envs_entails_eq=> HΔ. *)
(*   rewrite -twp_bind. eapply wand_apply; first exact: twp_alloc. *)
(*   rewrite left_id. apply forall_intro=> l. *)
(*   specialize (HΔ l). *)
(*   destruct (envs_app _ _ _) as [Δ''|] eqn:HΔ'; [ | contradiction ]. *)
(*   rewrite envs_app_sound //; simpl. *)
(*   apply wand_intro_l. by rewrite (sep_elim_l (l ↦ v)%I) right_id wand_elim_r. *)
(* Qed. *)

(* Lemma tac_wp_free Δ Δ' s E i K l v Φ : *)
(*   MaybeIntoLaterNEnvs 1 Δ Δ' → *)
(*   envs_lookup i Δ' = Some (false, l ↦ v)%I → *)
(*   (let Δ'' := envs_delete false i false Δ' in *)
(*    envs_entails Δ'' (WP fill K (Val $ LitV LitUnit) @ s; E {{ Φ }})) → *)
(*   envs_entails Δ (WP fill K (Free (LitV l)) @ s; E {{ Φ }}). *)
(* Proof. *)
(*   rewrite envs_entails_eq=> ? Hlk Hfin. *)
(*   rewrite -wp_bind. eapply wand_apply; first exact: wp_free. *)
(*   rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl. *)
(*   rewrite -Hfin wand_elim_r (envs_lookup_sound' _ _ _ _ _ Hlk). *)
(*   apply later_mono, sep_mono_r, wand_intro_r. rewrite right_id //. *)
(* Qed. *)
(* Lemma tac_twp_free Δ s E i K l v Φ : *)
(*   envs_lookup i Δ = Some (false, l ↦ v)%I → *)
(*   (let Δ' := envs_delete false i false Δ in *)
(*    envs_entails Δ' (WP fill K (Val $ LitV LitUnit) @ s; E [{ Φ }])) → *)
(*   envs_entails Δ (WP fill K (Free (LitV l)) @ s; E [{ Φ }]). *)
(* Proof. *)
(*   rewrite envs_entails_eq=> Hlk Hfin. *)
(*   rewrite -twp_bind. eapply wand_apply; first exact: twp_free. *)
(*   rewrite envs_lookup_split //; simpl. *)
(*   rewrite -Hfin wand_elim_r (envs_lookup_sound' _ _ _ _ _ Hlk). *)
(*   apply sep_mono_r, wand_intro_r. rewrite right_id //. *)
(* Qed. *)

Lemma tac_wp_load K (fs: gmap (fmrole iM) nat) tid Δ Δ'other E Einvs i j l q v Φ :
  (∀ (ρ : fmrole iM) (f : nat), fs !! ρ = Some f → (f ≥ 1)%nat) ->
  fs ≠ ∅ ->
  i ≠ j ->
  envs_lookup i Δ = Some (false, has_fuels tid fs)%I →
  let Δother := envs_delete true i false Δ in
  MaybeIntoLaterNEnvs 1 Δother Δ'other →
  envs_lookup j Δ'other = Some (false,  l ↦{q} v)%I →
  let Δ' := envs_snoc Δ'other false i (has_fuels tid ((λ m, m - 1)%nat <$> fs)) in
  envs_entails Δ' ((PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := heap_fairnessGS)) -∗
WP fill K (Val v) @ tid; E {{ Φ }}) →
  envs_entails Δ ((PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := heap_fairnessGS)) -∗
WP fill K (Load (LitV l)) @ tid; E {{ Φ }}).
Proof using.
  intros ?? Hij ?.
  rewrite envs_entails_unseal=> Δother ?? Δ' Hccl.
  rewrite -wp_bind.
  iIntros "H #PMP".
  iAssert (⌜envs_wf Δ⌝)%I as %Hwf.
  { unfold of_envs, of_envs', envs_wf. iDestruct "H" as "[% _]". by iPureIntro. }

  rewrite (envs_lookup_sound _ i) // /= -/Δother. iDestruct "H" as "[H1 H2]".
  rewrite into_laterN_env_sound /=.

  rewrite (envs_lookup_sound _ j) // /=.
  pose Δ'' := envs_delete true j false Δ'other. rewrite -/Δ''.
  iDestruct "H2" as "[H2 H3]".

  rewrite has_fuels_gt_1 //.
  iApply (wp_load_nostep with "[$] [H1 H2]"); [| iFrame |]; [by intros ?%fmap_empty_inv|].
  iIntros "!> [Hl Hf]". iApply (Hccl with "[-]"); [| done]. rewrite /Δ' /=.
  iApply (envs_snoc_sound Δ'other false i with "[H3 Hl] [Hf]") =>//.
  - rewrite maybe_into_latersN_envs_dom // /Δother.
    erewrite envs_lookup_envs_delete =>//.
  - iApply (envs_lookup_sound_2 Δ'other) =>//; [| by iFrame].
    eapply maybe_into_latersN_envs_wf =>//.
    rewrite /Δother. by apply envs_delete_wf.
Qed.


Lemma tac_wp_store K (fs: gmap (fmrole iM) nat) tid Δ Δ'other E Einvs i j l v v' Φ :
  (∀ (ρ : fmrole iM) (f : nat), fs !! ρ = Some f → (f ≥ 1)%nat) ->
  fs ≠ ∅ ->
  i ≠ j ->
  envs_lookup i Δ = Some (false, has_fuels tid fs)%I →
  let Δother := envs_delete true i false Δ in
  MaybeIntoLaterNEnvs 1 Δother Δ'other →
  envs_lookup j Δ'other  = Some (false, (l ↦ v)%I) ->
  match envs_simple_replace j false (Esnoc Enil j (l ↦ v')%I) Δ'other  with
  | Some Δ'other2 =>
      let Δ' := envs_snoc Δ'other2 false i (has_fuels tid ((λ m, m - 1)%nat <$> fs)) in
      envs_lookup i Δ'other2 = None (* redondent but easier than  proving it. *) ∧
      envs_entails Δ' ((PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := heap_fairnessGS)) -∗
 WP fill K (Val $ LitV LitUnit) @ tid; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ ((PartialModelPredicates Einvs (EM := EM) (iLM := iLM) (PMPP := PMPP) (eGS := heap_fairnessGS)) -∗
WP fill K (Store (LitV l) (Val v')) @ tid; E {{ Φ }}).
Proof using.
  intros ?? Hij ?.
  rewrite envs_entails_unseal=> Δother ??.
  destruct (envs_simple_replace j false (Esnoc Enil j (l ↦ v'))%I Δ'other) as [Δ'other2|] eqn:Heq; last done.
  move=> /= [Hhack Hccl].

  rewrite -wp_bind.
  iIntros "H #PMP".
  iAssert (⌜envs_wf Δ⌝)%I as %Hwf.
  { unfold of_envs, of_envs', envs_wf. iDestruct "H" as "[% _]". by iPureIntro. }

  rewrite (envs_lookup_sound _ i) // /= -/Δother. iDestruct "H" as "[H1 H2]".
  rewrite into_laterN_env_sound /=.

  rewrite (envs_lookup_sound _ j) //.
  pose Δ'' := envs_delete true j false Δ'other. rewrite -/Δ''.
  iDestruct "H2" as "[H2 H3]".

  rewrite has_fuels_gt_1 //.
  iApply (wp_store_nostep with "[$] [H1 H2]"); [| iFrame |]; [by intros ?%fmap_empty_inv|].
  iIntros "!> [Hl Hf]".
  set Δ' := envs_snoc Δ'other2 false i (has_fuels tid ((λ m, m - 1)%nat <$> fs)).
  fold Δ' in Hccl.

  iApply (Hccl with "[-PMP]"); [| done]. unfold Δ'.
  iApply (envs_snoc_sound Δ'other2 false i with "[H3 Hl] [Hf]") =>//.
  rewrite envs_simple_replace_sound' //=. simpl.
  iApply "H3". iFrame.
Qed.

End heap.

Tactic Notation "wp_load" :=
  let solve_fuel _ :=
    let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
    iAssumptionCore || fail "wp_load: cannot find" fs in
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
      [ (* dealt with later *)
      |
      |
      | let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
          iAssumptionCore || fail "wp_load: cannot find" fs
      | tc_solve
      | let fs := match goal with |- _ = Some (_, ?l ↦{_} _)%I => l end in
          iAssumptionCore || fail "wp_load: cannot find" fs
      | pm_reduce;
        simpl_has_fuels;
        wp_finish
      ]; [ solve_fuel_positive
         | try apply map_non_empty_singleton; try apply insert_non_empty; try done
         | intros ?; by simplify_eq
         |
      ]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_fuel _ :=
    let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
    iAssumptionCore || fail "wp_store: cannot find" fs in
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?locale ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
      [ (* dealt with later *)
      |
      |
      | let fs := match goal with |- _ = Some (_, has_fuels _ ?fs) => fs end in
          iAssumptionCore || fail "wp_store: cannot find" fs
      | tc_solve
      | let fs := match goal with |- _ = Some (_, ?l ↦{_} _)%I => l end in
          iAssumptionCore || fail "wp_store: cannot find" fs
      | split; [done | pm_reduce;
        simpl_has_fuels;
        wp_finish]
      ]; [ solve_fuel_positive
         | try apply map_non_empty_singleton; try apply insert_non_empty; try done
         | intros ?; by simplify_eq
         |
      ]
  | _ => fail "wp_store: not a 'wp'"
  end.
(*
Lemma tac_wp_xchg Δ Δ' s E i K l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ v) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (Xchg (LitV l) (Val v')) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply; first by eapply wp_xchg.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_xchg Δ s E i K l v v' Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ with
  | Some Δ' => envs_entails Δ' (WP fill K (Val $ v) @ s; E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (Xchg (LitV l) v') @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq. intros.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -twp_bind. eapply wand_apply; first by eapply twp_xchg.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cmpxchg Δ Δ' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' with
  | Some Δ'' =>
     v = v1 →
     envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }})
  | None => False
  end →
  (v ≠ v1 →
   envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }})) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) (Val v1) (Val v2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ??? Hsuc Hfail.
  destruct (envs_simple_replace _ _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  destruct (decide (v = v1)) as [Heq|Hne].
  - rewrite -wp_bind. eapply wand_apply.
    { eapply wp_cmpxchg_suc; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_simple_replace_sound //; simpl.
    apply later_mono, sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -wp_bind. eapply wand_apply.
    { eapply wp_cmpxchg_fail; eauto. }
    rewrite into_laterN_env_sound -later_sep /= {1}envs_lookup_split //; simpl.
    apply later_mono, sep_mono_r. apply wand_mono; auto.
Qed.
Lemma tac_twp_cmpxchg Δ s E i K l v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ with
  | Some Δ' =>
     v = v1 →
     envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E [{ Φ }])
  | None => False
  end →
  (v ≠ v1 →
   envs_entails Δ (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E [{ Φ }])) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ?? Hsuc Hfail.
  destruct (envs_simple_replace _ _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  destruct (decide (v = v1)) as [Heq|Hne].
  - rewrite -twp_bind. eapply wand_apply.
    { eapply twp_cmpxchg_suc; eauto. }
    rewrite /= {1}envs_simple_replace_sound //; simpl.
    apply sep_mono_r. rewrite right_id. apply wand_mono; auto.
  - rewrite -twp_bind. eapply wand_apply.
    { eapply twp_cmpxchg_fail; eauto. }
    rewrite /= {1}envs_lookup_split //; simpl.
    apply sep_mono_r. apply wand_mono; auto.
Qed.

Lemma tac_wp_cmpxchg_fail Δ Δ' s E i K l q v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  v ≠ v1 → vals_compare_safe v v1 →
  envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E {{ Φ }}) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ?????.
  rewrite -wp_bind. eapply wand_apply; first exact: wp_cmpxchg_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_cmpxchg_fail Δ s E i K l q v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦{q} v)%I →
  v ≠ v1 → vals_compare_safe v v1 →
  envs_entails Δ (WP fill K (Val $ PairV v (LitV $ LitBool false)) @ s; E [{ Φ }]) →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq. intros. rewrite -twp_bind.
  eapply wand_apply; first exact: twp_cmpxchg_fail.
  (* [//] solves some evars and enables further simplification. *)
  rewrite envs_lookup_split /= // /=. by do 2 f_equiv.
Qed.

Lemma tac_wp_cmpxchg_suc Δ Δ' s E i K l v v1 v2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  v = v1 → vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ' with
  | Some Δ'' =>
     envs_entails Δ'' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ?????; subst.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply.
  { eapply wp_cmpxchg_suc; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_cmpxchg_suc Δ s E i K l v v1 v2 Φ :
  envs_lookup i Δ = Some (false, l ↦ v)%I →
  v = v1 → vals_compare_safe v v1 →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ v2)) Δ with
  | Some Δ' =>
     envs_entails Δ' (WP fill K (Val $ PairV v (LitV $ LitBool true)) @ s; E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (CmpXchg (LitV l) v1 v2) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=>????; subst.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -twp_bind. eapply wand_apply.
  { eapply twp_cmpxchg_suc; eauto. }
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_faa Δ Δ' s E i K l z1 z2 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ LitV z1)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (LitInt (z1 + z2)))) Δ' with
  | Some Δ'' => envs_entails Δ'' (WP fill K (Val $ LitV z1) @ s; E {{ Φ }})
  | None => False
  end →
  envs_entails Δ (WP fill K (FAA (LitV l) (LitV z2)) @ s; E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ???.
  destruct (envs_simple_replace _ _ _) as [Δ''|] eqn:HΔ''; [ | contradiction ].
  rewrite -wp_bind. eapply wand_apply; first exact: (wp_faa _ _ _ z1 z2).
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.
Lemma tac_twp_faa Δ s E i K l z1 z2 Φ :
  envs_lookup i Δ = Some (false, l ↦ LitV z1)%I →
  match envs_simple_replace i false (Esnoc Enil i (l ↦ LitV (LitInt (z1 + z2)))) Δ with
  | Some Δ' => envs_entails Δ' (WP fill K (Val $ LitV z1) @ s; E [{ Φ }])
  | None => False
  end →
  envs_entails Δ (WP fill K (FAA (LitV l) (LitV z2)) @ s; E [{ Φ }]).
Proof.
  rewrite envs_entails_eq=> ??.
  destruct (envs_simple_replace _ _ _) as [Δ'|] eqn:HΔ'; [ | contradiction ].
  rewrite -twp_bind. eapply wand_apply; first exact: (twp_faa _ _ _ z1 z2).
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply sep_mono_r, wand_mono.
Qed.
End heap.

(** The tactic [wp_apply_core lem tac_suc tac_fail] evaluates [lem] to a
hypothesis [H] that can be applied, and then runs [wp_bind_core K; tac_suc H]
for every possible evaluation context [K].

- The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis,
  but can perform other operations in addition (see [wp_apply] and [awp_apply]
  below).
- The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation
  contexts [K], and can perform further operations before invoking [cont] to
  try again.

TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *)
Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         wp_bind_core K; tac_suc H)
     | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         twp_bind_core K; tac_suc H)
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wp_smart_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; try wp_expr_simpl)
                    ltac:(fun cont => wp_pure _; []; cont ()).

(** Tactic tailored for atomic triples: the first, simple one just runs
[iAuIntro] on the goal, as atomic triples always have an atomic update as their
premise.  The second one additionaly does some framing: it gets rid of [Hs] from
the context, which is intended to be the non-laterable assertions that iAuIntro
would choke on.  You get them all back in the continuation of the atomic
operation. *)
Tactic Notation "awp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H) ltac:(fun cont => fail);
  last iAuIntro.
Tactic Notation "awp_apply" open_constr(lem) "without" constr(Hs) :=
  (* Convert "list of hypothesis" into specialization pattern. *)
  let Hs := words Hs in
  let Hs := eval vm_compute in (INamed <$> Hs) in
  wp_apply_core lem
    ltac:(fun H =>
      iApply (wp_frame_wand with
        [SGoal $ SpecGoal GSpatial false [] Hs false]); [iAccu|iApplyHyp H])
    ltac:(fun cont => fail);
  last iAuIntro.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
    first [intros l | fail 1 "wp_alloc:" l "not fresh"];
    pm_reduce;
    lazymatch goal with
    | |- False => fail 1 "wp_alloc:" H "not fresh"
    | _ => iDestructHyp Htmp as H; wp_finish
    end in
  wp_pures;
  (** The code first tries to use allocation lemma for a single reference,
     ie, [tac_wp_alloc] (respectively, [tac_twp_alloc]).
     If that fails, it tries to use the lemma [tac_wp_allocN]
     (respectively, [tac_twp_allocN]) for allocating an array.
     Notice that we could have used the array allocation lemma also for single
     references. However, that would produce the resource l ↦∗ [v] instead of
     l ↦ v for single references. These are logically equivalent assertions
     but are not equal. *)
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [tc_solve
        |finish ()]
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_wp_allocN _ _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac|tc_solve
         |finish ()]
    in (process_single ()) || (process_array ())
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    let process_single _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_alloc _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        finish ()
    in
    let process_array _ :=
        first
          [reshape_expr e ltac:(fun K e' => eapply (tac_twp_allocN _ _ _ Htmp K))
          |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [idtac
        |finish ()]
    in (process_single ()) || (process_array ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  wp_alloc l as "?".

Tactic Notation "wp_free" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_free: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_free _ _ _ _ _ K))
      |fail 1 "wp_free: cannot find 'Free' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_free _ _ _ _ K))
      |fail 1 "wp_free: cannot find 'Free' in" e];
    [solve_mapsto ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_free: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_store _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_xchg" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_xchg: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_xchg _ _ _ _ _ K))
      |fail 1 "wp_xchg: cannot find 'Xchg' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_xchg _ _ _ _ K))
      |fail 1 "wp_xchg: cannot find 'Xchg' in" e];
    [solve_mapsto ()
    |pm_reduce; first [wp_seq|wp_finish]]
  | _ => fail "wp_xchg: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg" "as" simple_intropattern(H1) "|" simple_intropattern(H2) :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_mapsto ()
    |try solve_vals_compare_safe
    |pm_reduce; intros H1; wp_finish
    |intros H2; wp_finish]
  | |- envs_entails _ (twp ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg _ _ _ _ K))
      |fail 1 "wp_cmpxchg: cannot find 'CmpXchg' in" e];
    [solve_mapsto ()
    |try solve_vals_compare_safe
    |pm_reduce; intros H1; wp_finish
    |intros H2; wp_finish]
  | _ => fail "wp_cmpxchg: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg_fail" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg_fail: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_fail _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_fail: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_mapsto ()
    |try (simpl; congruence) (* value inequality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg_fail _ _ _ _ K))
      |fail 1 "wp_cmpxchg_fail: cannot find 'CmpXchg' in" e];
    [solve_mapsto ()
    |try (simpl; congruence) (* value inequality *)
    |try solve_vals_compare_safe
    |wp_finish]
  | _ => fail "wp_cmpxchg_fail: not a 'wp'"
  end.

Tactic Notation "wp_cmpxchg_suc" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cmpxchg_suc: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_cmpxchg_suc _ _ _ _ _ K))
      |fail 1 "wp_cmpxchg_suc: cannot find 'CmpXchg' in" e];
    [tc_solve
    |solve_mapsto ()
    |try (simpl; congruence) (* value equality *)
    |try solve_vals_compare_safe
    |pm_reduce; wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_cmpxchg_suc _ _ _ _ K))
      |fail 1 "wp_cmpxchg_suc: cannot find 'CmpXchg' in" e];
    [solve_mapsto ()
    |try (simpl; congruence) (* value equality *)
    |try solve_vals_compare_safe
    |pm_reduce; wp_finish]
  | _ => fail "wp_cmpxchg_suc: not a 'wp'"
  end.

Tactic Notation "wp_faa" :=
  let solve_mapsto _ :=
    let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
    iAssumptionCore || fail "wp_faa: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_faa _ _ _ _ _ K))
      |fail 1 "wp_faa: cannot find 'FAA' in" e];
    [tc_solve
    |solve_mapsto ()
    |pm_reduce; wp_finish]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_twp_faa _ _ _ _ K))
      |fail 1 "wp_faa: cannot find 'FAA' in" e];
    [solve_mapsto ()
    |pm_reduce; wp_finish]
  | _ => fail "wp_faa: not a 'wp'"
  end.

*)
