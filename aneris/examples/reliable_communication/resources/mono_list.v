(** OBS!: This is taken directly from Iris, and should instead be obtained
from bumping the Iris version. *)

(** Authoritative CMRA of append-only lists, where the fragment represents a
  snap-shot of the list, and the authoritative element can only grow by
  appending. *)
From iris.algebra Require Export auth dfrac max_prefix_list.
From iris.algebra Require Import updates local_updates proofmode_classes.
From iris.prelude Require Import options.

Definition mono_listR (A : ofe) : cmra  := authR (max_prefix_listUR A).
Definition mono_listUR (A : ofe) : ucmra  := authUR (max_prefix_listUR A).

Definition mono_list_auth {A : ofe} (q : dfrac) (l : list A) : mono_listR A :=
  ●{q} (to_max_prefix_list l) ⋅ ◯ (to_max_prefix_list l).
Definition mono_list_lb {A : ofe} (l : list A) : mono_listR A :=
  ◯ (to_max_prefix_list l).
Global Instance: Params (@mono_list_auth) 2 := {}.
Global Instance: Params (@mono_list_lb) 1 := {}.
Typeclasses Opaque mono_list_auth mono_list_lb.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "●ML{ dq } l" :=
  (mono_list_auth dq l) (at level 20, format "●ML{ dq }  l").
Notation "●ML{# q } l" :=
  (mono_list_auth (DfracOwn q) l) (at level 20, format "●ML{# q }  l").
Notation "●ML□ l" := (mono_list_auth DfracDiscarded l) (at level 20).
Notation "●ML l" := (mono_list_auth (DfracOwn 1) l) (at level 20).
Notation "◯ML l" := (mono_list_lb l) (at level 20).

Section mono_list_props.
  Context {A : ofe}.
  Implicit Types l : list A.
  Implicit Types q : frac.
  Implicit Types dq : dfrac.

  (** Setoid properties *)
  Global Instance mono_list_auth_ne dq : NonExpansive (@mono_list_auth A dq).
  Proof. solve_proper. Qed.
  Global Instance mono_list_auth_proper dq : Proper ((≡) ==> (≡)) (@mono_list_auth A dq).
  Proof. solve_proper. Qed.
  Global Instance mono_list_lb_ne : NonExpansive (@mono_list_lb A).
  Proof. solve_proper. Qed.
  Global Instance mono_list_lb_proper : Proper ((≡) ==> (≡)) (@mono_list_lb A).
  Proof. solve_proper. Qed.

  Global Instance mono_list_lb_dist_inj n : Inj (dist n) (dist n) (@mono_list_lb A).
  Proof. rewrite /mono_list_lb. by intros ?? ?%(inj _)%(inj _). Qed.
  Global Instance mono_list_lb_inj : Inj (≡) (≡) (@mono_list_lb A).
  Proof. rewrite /mono_list_lb. by intros ?? ?%(inj _)%(inj _). Qed.

  (** * Operation *)
  Global Instance mono_list_lb_core_id l : CoreId (◯ML l).
  Proof. rewrite /mono_list_lb. apply _. Qed.
  Global Instance mono_list_auth_core_id l : CoreId (●ML□ l).
  Proof. rewrite /mono_list_auth. apply _. Qed.

  Lemma mono_list_auth_dfrac_op dq1 dq2 l :
    ●ML{dq1 ⋅ dq2} l ≡ ●ML{dq1} l ⋅ ●ML{dq2} l.
  Proof.
    rewrite /mono_list_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma mono_list_lb_op_l l1 l2 : l1 `prefix_of` l2 → ◯ML l1 ⋅ ◯ML l2 ≡ ◯ML l2.
  Proof. intros ?. by rewrite /mono_list_lb -auth_frag_op to_max_prefix_list_op_l. Qed.
  Lemma mono_list_lb_op_r l1 l2 : l1 `prefix_of` l2 → ◯ML l2 ⋅ ◯ML l1 ≡ ◯ML l2.
  Proof. intros ?. by rewrite /mono_list_lb -auth_frag_op to_max_prefix_list_op_r. Qed.
  Lemma mono_list_auth_lb_op dq l : ●ML{dq} l ≡ ●ML{dq} l ⋅ ◯ML l.
  Proof.
    by rewrite /mono_list_auth /mono_list_lb -!assoc -auth_frag_op -core_id_dup.
  Qed.

  Global Instance mono_list_auth_dfrac_is_op dq dq1 dq2 l :
    IsOp dq dq1 dq2 → IsOp' (●ML{dq} l) (●ML{dq1} l) (●ML{dq2} l).
  Proof. rewrite /IsOp' /IsOp=> ->. rewrite mono_list_auth_dfrac_op //. Qed.

  (** * Validity *)
  Lemma mono_list_auth_dfrac_validN n dq l : ✓{n} (●ML{dq} l) ↔ ✓ dq.
  Proof.
    rewrite /mono_list_auth auth_both_dfrac_validN.
    naive_solver apply to_max_prefix_list_validN.
  Qed.
  Lemma mono_list_auth_validN n l : ✓{n} (●ML l).
  Proof. by apply mono_list_auth_dfrac_validN. Qed.

  Lemma mono_list_auth_dfrac_valid dq l : ✓ (●ML{dq} l) ↔ ✓ dq.
  Proof.
    rewrite /mono_list_auth auth_both_dfrac_valid.
    naive_solver apply to_max_prefix_list_valid.
  Qed.
  Lemma mono_list_auth_valid l : ✓ (●ML l).
  Proof. by apply mono_list_auth_dfrac_valid. Qed.

  Lemma mono_list_auth_dfrac_op_validN n dq1 dq2 l1 l2 :
    ✓{n} (●ML{dq1} l1 ⋅ ●ML{dq2} l2) ↔ ✓ (dq1 ⋅ dq2) ∧ l1 ≡{n}≡ l2.
  Proof.
    rewrite /mono_list_auth (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move=> /cmra_validN_op_l /auth_auth_dfrac_op_validN.
      rewrite (inj_iff to_max_prefix_list). naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op auth_both_dfrac_validN.
      naive_solver apply to_max_prefix_list_validN.
  Qed.
  Lemma mono_list_auth_op_validN n l1 l2 : ✓{n} (●ML l1 ⋅ ●ML l2) ↔ False.
  Proof. rewrite mono_list_auth_dfrac_op_validN. naive_solver. Qed.

  Lemma mono_list_auth_dfrac_op_valid dq1 dq2 l1 l2 :
    ✓ (●ML{dq1} l1 ⋅ ●ML{dq2} l2) ↔ ✓ (dq1 ⋅ dq2) ∧ l1 ≡ l2.
  Proof.
    rewrite cmra_valid_validN equiv_dist.
    setoid_rewrite mono_list_auth_dfrac_op_validN. naive_solver eauto using O.
  Qed.
  Lemma mono_list_auth_op_valid l1 l2 : ✓ (●ML l1 ⋅ ●ML l2) ↔ False.
  Proof. rewrite mono_list_auth_dfrac_op_valid. naive_solver. Qed.

  Lemma mono_list_auth_dfrac_op_valid_L `{!LeibnizEquiv A} dq1 dq2 l1 l2 :
    ✓ (●ML{dq1} l1 ⋅ ●ML{dq2} l2) ↔ ✓ (dq1 ⋅ dq2) ∧ l1 = l2.
  Proof. unfold_leibniz. apply mono_list_auth_dfrac_op_valid. Qed.

  Lemma mono_list_both_dfrac_validN n dq l1 l2 :
    ✓{n} (●ML{dq} l1 ⋅ ◯ML l2) ↔ ✓ dq ∧ ∃ l, l1 ≡{n}≡ l2 ++ l.
  Proof.
    rewrite /mono_list_auth /mono_list_lb -assoc
      -auth_frag_op auth_both_dfrac_validN -to_max_prefix_list_includedN.
    f_equiv; split.
    - intros [Hincl _]. etrans; [apply: cmra_includedN_r|done].
    - intros. split; [|by apply to_max_prefix_list_validN].
      rewrite {2}(core_id_dup (to_max_prefix_list l1)). by f_equiv.
  Qed.
  Lemma mono_list_both_validN n l1 l2 :
    ✓{n} (●ML l1 ⋅ ◯ML l2) ↔ ∃ l, l1 ≡{n}≡ l2 ++ l.
  Proof. rewrite mono_list_both_dfrac_validN. split; [naive_solver|done]. Qed.

  Lemma mono_list_both_dfrac_valid dq l1 l2 :
    ✓ (●ML{dq} l1 ⋅ ◯ML l2) ↔ ✓ dq ∧ ∃ l, l1 ≡ l2 ++ l.
  Proof.
    rewrite /mono_list_auth /mono_list_lb -assoc -auth_frag_op
      auth_both_dfrac_valid -max_prefix_list_included_includedN
      -to_max_prefix_list_included.
    f_equiv; split.
    - intros [Hincl _]. etrans; [apply: cmra_included_r|done].
    - intros. split; [|by apply to_max_prefix_list_valid].
      rewrite {2}(core_id_dup (to_max_prefix_list l1)). by f_equiv.
  Qed.
  Lemma mono_list_both_valid l1 l2 :
    ✓ (●ML l1 ⋅ ◯ML l2) ↔ ∃ l, l1 ≡ l2 ++ l.
  Proof. rewrite mono_list_both_dfrac_valid. split; [naive_solver|done]. Qed.

  Lemma mono_list_both_dfrac_valid_L `{!LeibnizEquiv A} dq l1 l2 :
    ✓ (●ML{dq} l1 ⋅ ◯ML l2) ↔ ✓ dq ∧ l2 `prefix_of` l1.
  Proof. rewrite /prefix. rewrite mono_list_both_dfrac_valid. naive_solver. Qed.
  Lemma mono_list_both_valid_L `{!LeibnizEquiv A} l1 l2 :
    ✓ (●ML l1 ⋅ ◯ML l2) ↔ l2 `prefix_of` l1.
  Proof. rewrite /prefix. rewrite mono_list_both_valid. naive_solver. Qed.

  Lemma mono_list_lb_op_validN n l1 l2 :
    ✓{n} (◯ML l1 ⋅ ◯ML l2) ↔ (∃ l, l2 ≡{n}≡ l1 ++ l) ∨ (∃ l, l1 ≡{n}≡ l2 ++ l).
  Proof. by rewrite auth_frag_op_validN to_max_prefix_list_op_validN. Qed.
  Lemma mono_list_lb_op_valid l1 l2 :
    ✓ (◯ML l1 ⋅ ◯ML l2) ↔ (∃ l, l2 ≡ l1 ++ l) ∨ (∃ l, l1 ≡ l2 ++ l).
  Proof. by rewrite auth_frag_op_valid to_max_prefix_list_op_valid. Qed.
  Lemma mono_list_lb_op_valid_L `{!LeibnizEquiv A} l1 l2 :
    ✓ (◯ML l1 ⋅ ◯ML l2) ↔ l1 `prefix_of` l2 ∨ l2 `prefix_of` l1.
  Proof. rewrite mono_list_lb_op_valid / prefix. naive_solver. Qed.

  Lemma mono_list_lb_op_valid_1_L `{!LeibnizEquiv A} l1 l2 :
    ✓ (◯ML l1 ⋅ ◯ML l2) → l1 `prefix_of` l2 ∨ l2 `prefix_of` l1.
  Proof. by apply mono_list_lb_op_valid_L. Qed.
  Lemma mono_list_lb_op_valid_2_L `{!LeibnizEquiv A} l1 l2 :
    l1 `prefix_of` l2 ∨ l2 `prefix_of` l1 → ✓ (◯ML l1 ⋅ ◯ML l2).
  Proof. by apply mono_list_lb_op_valid_L. Qed.

  Lemma mono_list_lb_mono l1 l2 : l1 `prefix_of` l2 → ◯ML l1 ≼ ◯ML l2.
  Proof. intros. exists (◯ML l2). by rewrite mono_list_lb_op_l. Qed.

  Lemma mono_list_included dq l : ◯ML l ≼ ●ML{dq} l.
  Proof. apply cmra_included_r. Qed.

  (** * Update *)
  Lemma mono_list_update {l1} l2 : l1 `prefix_of` l2 → ●ML l1 ~~> ●ML l2.
  Proof. intros ?. by apply auth_update, max_prefix_list_local_update. Qed.
  Lemma mono_list_auth_persist dq l : ●ML{dq} l ~~> ●ML□ l.
  Proof.
    rewrite /mono_list_auth. apply cmra_update_op; [|done].
    by apply auth_update_auth_persist.
  Qed.
End mono_list_props.

Definition mono_listURF (F : oFunctor) : urFunctor :=
  authURF (max_prefix_listURF F).

Global Instance mono_listURF_contractive F :
  oFunctorContractive F → urFunctorContractive (mono_listURF F).
Proof. apply _. Qed.

Definition mono_listRF (F : oFunctor) : rFunctor :=
  authRF (max_prefix_listURF F).

Global Instance mono_listRF_contractive F :
  oFunctorContractive F → rFunctorContractive (mono_listRF F).
Proof. apply _. Qed.
