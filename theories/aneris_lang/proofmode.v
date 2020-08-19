From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From aneris.aneris_lang Require Import tactics network lifting.
From aneris.aneris_lang.program_logic Require Export aneris_lifting.

Set Default Proof Using "Type".
Import uPred.

Lemma tac_wp_expr_eval `{anerisG Σ} Δ s E Φ e e' :
  (∀ (e'':=e'), e = e'') →
  envs_entails Δ (WP e' @ s; E {{ Φ }}) → envs_entails Δ (WP e @ s; E {{ Φ }}).
Proof. by intros ->. Qed.

Tactic Notation "wp_expr_eval" tactic(t) :=
  try (
    iStartProof;
    first [eapply tac_wp_expr_eval];
      [let x := fresh in intros x; t; unfold x; reflexivity
      |]).

Lemma tac_wp_pure `{!anerisG Σ} Δ Δ' ip E e1 e2 φ n Φ :
  PureExec φ n {| expr_n := ip; expr_e := e1 |}
           {| expr_n := ip; expr_e := e2 |} →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP e2 @[ip] E {{ Φ }}) →
  envs_entails Δ (WP e1 @[ip] E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ??? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' -aneris_wp_pure_step_later //.
Qed.

Lemma tac_wp_value `{!anerisG Σ} Δ ip E Φ v :
  envs_entails Δ (Φ v) →
  envs_entails Δ (WP (Val v) @[ip] E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ->. by apply aneris_wp_value.
Qed.

Ltac wp_expr_simpl := wp_expr_eval simpl.

Ltac wp_value_head :=
  first [eapply tac_wp_value (* || eapply tac_twp_value *)].

Ltac wp_finish :=
  wp_expr_simpl;      (* simplify occurences of subst/fill *)
  try wp_value_head;  (* in case we have reached a value, get rid of the WP *)
  pm_prettify.        (* prettify ▷s caused by [MaybeIntoLaterNEnvs] and
                         λs caused by wp_value *)

Ltac solve_vals_compare_safe :=
  (* The first branch is for when we have [vals_compare_safe] in the context.
     The other two branches are for when either one of the branches reduces to
     [True] or we have it in the context. *)
  fast_done || (left; fast_done) || (right; fast_done).

(** The argument [efoc] can be used to specify the construct that should be
reduced. For example, you can write [wp_pure (EIf _ _ _)], which will search
for an [EIf _ _ _] in the expression, and reduce it.

The use of [open_constr] in this tactic is essential. It will convert all holes
(i.e. [_]s) into evars, that later get unified when an occurences is found
(see [unify e' efoc] in the code below). *)
Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
    let e := eval simpl in e in
    reshape_expr e ltac:(fun K e' =>
      unify e' efoc;
      eapply (tac_wp_pure _ _ _ _ (@fill base_ectxi_lang K e'));
      [iSolveTC                       (* PureExec *)
      |try solve_vals_compare_safe    (* The pure condition for PureExec *)
      |iSolveTC                       (* IntoLaters *)
      |wp_finish                      (* new goal *)
      ])
    || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a redex"
  end.

Ltac wp_pures :=
  iStartProof;
  repeat (wp_pure _; []). (* The `;[]` makes sure that no side-condition
                             magically spawns. *)

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

Tactic Notation "wp_find_from" := wp_pure (FindFrom _ _ _ ).
Tactic Notation "wp_substring" := wp_pure (Substring _ _ _).
Tactic Notation "wp_makeaddress" := wp_pure (MakeAddress _ _).

Lemma tac_wp_bind `{anerisG Σ} K Δ ip E Φ (e : base_lang.expr) f :
  f = (λ e, fill K e) → (* as an eta expanded hypothesis so that we can `simpl` it *)
  envs_entails Δ (WP e @ ip; E {{ v, WP f (of_val v) @ ip; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ ip; E {{ Φ }}).
Proof. rewrite envs_entails_eq=> -> ->. apply: aneris_wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => eapply (tac_wp_bind K); [simpl; reflexivity|lazy beta]
  end.

(* FIXME: wp_bind tactic needs to be fixed w.r.t. expr_n which now is of the form
   of functional application "ip_of_address a" and not of a string
   constant "n" as previously (this probably has something to do with eval hnf in
   wp_bind_core above.*)
Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
    reshape_expr e ltac:(fun K e' => unify e' efoc; wp_bind_core K)
    || fail "wp_bind: cannot find" efoc "in" e
  end.

(** Heap and socket tactics *)
Section state.
Context `{anerisG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (uPredI (iResUR Σ)).
Implicit Types z : Z.

Lemma tac_wp_alloc Δ Δ' ip E j K v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦[ip] v)) Δ' = Some Δ'' ∧
    envs_entails Δ'' (WP fill K (Val $ LitV $ LitLoc l)
                         @[ip] E {{ Φ }})) →
  envs_entails Δ (WP fill K (Alloc (Val v)) @[ip] E {{ Φ }}).
Proof.
  rewrite envs_entails_eq => ? HΔ. rewrite -aneris_wp_bind.
  iIntros "H". rewrite into_laterN_env_sound /=.
  iApply aneris_wp_alloc; first done.
  iNext. iIntros (l) "Hl". destruct (HΔ l) as (Δ''&?&HΔ').
  rewrite envs_app_sound //; simpl. rewrite right_id HΔ'.
  iApply "H"; done.
Qed.

Lemma tac_wp_load Δ Δ' E i K ip l q v Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦[ip]{q} v)%I →
  envs_entails Δ' (WP fill K (of_val v) @[ip] E {{ Φ }}) →
  envs_entails Δ (WP fill K (Load (LitV (LitLoc l))) @[ip] E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ???.
  rewrite -aneris_wp_bind. eapply wand_apply; first exact: aneris_wp_load.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_store Δ Δ' Δ'' E i K ip l v v' Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦[ip] v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦[ip] v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (of_val $ LitV LitUnit) @[ip] E {{ Φ }}) →
  envs_entails Δ (WP fill K (Store (LitV (LitLoc l)) (Val v'))
                     @[ip] E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ????.
  rewrite -aneris_wp_bind. eapply wand_apply; first by eapply aneris_wp_store.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_fail Δ Δ' E i K ip l q v e1 v1 e2 Φ :
  IntoVal e1 v1 → AsVal e2 →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦[ip]{q} v)%I → v ≠ v1 →
  envs_entails Δ' (WP fill K (of_val $ LitV (LitBool false)) @[ip] E {{ Φ }}) →
  envs_entails Δ (WP fill K (CAS (LitV (LitLoc l)) e1 e2) @[ip] E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> <- [? <-] ????.
  rewrite -aneris_wp_bind. eapply wand_apply; first exact: aneris_wp_cas_fail.
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_cas_suc Δ Δ' Δ'' E i K ip l v e1 v1 e2 v2 Φ :
  IntoVal e1 v1 → IntoVal e2 v2 →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦[ip] v)%I → v = v1 →
  envs_simple_replace i false (Esnoc Enil i (l ↦[ip] v2)) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K (of_val $ LitV (LitBool true)) @[ip] E {{ Φ }}) →
  envs_entails Δ (WP fill K (CAS (LitV (LitLoc l)) e1 e2) @[ip] E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> <- <- ?????; subst.
  rewrite -aneris_wp_bind. eapply wand_apply; first exact: aneris_wp_cas_suc.
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_socket Δ Δ' E j K ip v1 v2 v3 Φ :
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ h,
    ∃ Δ'',
      envs_app
        false
        (Esnoc Enil j
          (h ↪[ip]
             ({|
                 Network.sfamily := v1;
                 Network.stype := v2;
                 Network.sprotocol := v3;
                 Network.saddress := None |}, ∅, ∅)))
        Δ' = Some Δ'' ∧
      envs_entails
        Δ'' (WP fill K (of_val $ LitV (LitSocket h)) @[ip] E {{ Φ }})) →
  envs_entails Δ (WP fill K (NewSocket
                               (Val $ LitV $ LitAddressFamily v1)
                               (Val $ LitV $ LitSocketType v2)
                               (Val $ LitV $ LitProtocol v3)) @[ip] E {{ Φ }}).
Proof.
  rewrite envs_entails_eq=> ? HΔ. rewrite -aneris_wp_bind.
  iIntros "H". rewrite into_laterN_env_sound /=.
  iApply aneris_wp_new_socket; first done.
  iNext. iIntros (sh) "Hsh". destruct (HΔ sh) as (Δ''&?&HΔ').
  rewrite envs_app_sound //; simpl. rewrite right_id HΔ'.
  iApply "H"; last done.
Qed.

End state.

(** Evaluate [lem] to a hypothesis [H] that can be applied, and then run
[wp_bind K; tac H] for every possible evaluation context.  [tac] can do
[iApplyHyp H] to actually apply the hypothesis.  TC resolution of [lem] premises
happens *after* [tac H] got executed. *)
Tactic Notation "wp_apply_core" open_constr(lem) tactic(tac) :=
  wp_pures;
  iPoseProofCore lem as false (fun H =>
    lazymatch goal with
    | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
      reshape_expr e ltac:(fun K e' =>
        wp_bind_core K; tac H) ||
      lazymatch iTypeOf H with
      | Some (_,?P) => fail "wp_apply: cannot apply" P
      end
    | _ => fail "wp_apply: not a 'wp'"
    end).
Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem (fun H => iApplyHyp H; try iNext; try wp_expr_simpl).

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
      first [intros l | fail 1 "wp_alloc:" l "not fresh"];
      eexists; split;
      [pm_reflexivity || fail "wp_alloc:" H "not fresh"
      |iDestructHyp Htmp as H; wp_finish] in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
    let process_single _ :=
        first [
            reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc _ _ ip _ Htmp K))
           |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
        [iSolveTC
        |finish()]
    in (process_single ())
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  let H := iFresh in wp_alloc l as H.

Tactic Notation "wp_load" :=
  let solve_mapsto ip :=
    let l := match goal with |- _ = Some (_, (?l ↦[ip]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_load: cannot find" l "↦ ?" in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_load _ _ _ _ K))
      |fail 1 "wp_load: cannot find 'Load' in" e];
    [apply _
    |solve_mapsto ip
    |wp_expr_simpl; try wp_value_head]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_store" :=
  let solve_mapsto ip :=
    let l := match goal with |- _ = Some (_, (?l ↦[ip]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_store: cannot find" l "↦ ?" in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_store _ _ _ _ _ K))
      |fail 1 "wp_store: cannot find 'Store' in" e];
    [iSolveTC
    |solve_mapsto ip
    |pm_reflexivity
    |first [wp_seq|wp_finish]]
  | _ => fail "wp_store: not a 'wp'"
  end.

Tactic Notation "wp_cas_fail" :=
  let solve_mapsto ip :=
    let l := match goal with |- _ = Some (_, (?l ↦[ip]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cas_fail: cannot find" l "↦ ?" in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_cas_fail _ _ _ _ K); [apply _|apply _|..])
      |fail 1 "wp_cas_fail: cannot find 'CAS' in" e];
    [apply _
    |solve_mapsto ip
    |try congruence
    |simpl; try wp_value_head]
  | _ => fail "wp_cas_fail: not a 'wp'"
  end.

Tactic Notation "wp_cas_suc" :=
  let solve_mapsto ip :=
    let l := match goal with |- _ = Some (_, (?l ↦[ip]{_} _)%I) => l end in
    iAssumptionCore || fail "wp_cas_suc: cannot find" l "↦ ?" in
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' =>
         eapply (tac_wp_cas_suc _ _ _ _ _ K); [apply _|apply _|..])
      |fail 1 "wp_cas_suc: cannot find 'CAS' in" e];
    [apply _
    |solve_mapsto ip
    |try congruence
    |reflexivity
    |simpl; try wp_value_head]
  | _ => fail "wp_cas_suc: not a 'wp'"
  end.

Tactic Notation "wp_socket"  ident(l) "as" constr(H) :=
  let Htmp := iFresh in
  let finish _ :=
      first [intros l | fail 1 "wp_socket:" l "not fresh"];
      eexists; split;
      [pm_reflexivity || fail "wp_socket:" H "not fresh"
      |iDestructHyp Htmp as H; wp_finish] in
  wp_pures;
  lazymatch goal with
  | |- envs_entails _ (wp ?ip ?E ?e ?Q) =>
    let process_single _ :=
        first [
            reshape_expr e ltac:(fun K e' => eapply (tac_wp_socket _ _ _ Htmp K ip))
           |fail 1 "wp_socket: cannot find 'NewSocket' in" e];
        [iSolveTC
        |finish()]
    in (process_single ())
  | _ => fail "wp_socket: not a 'wp'"
  end.
