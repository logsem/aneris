From trillium.fairness.examples Require Import yesno.
From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre.
From trillium.fairness Require Import fairness fair_termination fairness_finiteness.
From trillium.prelude Require Export finitary quantifiers sigma classical_instances.
From trillium.fairness.heap_lang Require Export lang lifting tactics.
From trillium.fairness.heap_lang Require Import notation.

From stdpp Require Import finite.


Section product_of_orders.
  Variables (A B : Type) (leA : relation A) (leB : relation B).
  Context `{HlAtrans: Transitive _ leA}.

  Lemma prod_trans :
     transitive _ leA ->
     transitive _ leB ->
     transitive _ (prod_relation leA leB).
   Proof.
     intros tA tB [x1 y1] [x2 y2] [x3 y3] H.
     inversion H; subst; clear H.
     intros H.
     inversion H; subst; clear H.
     split; eauto.
   Qed.

   Theorem wf_prod :
     well_founded leA ->
     well_founded leB ->
     well_founded (prod_relation leA leB).
   Proof.
     intros wfA wfB [x y]. generalize dependent y.
     induction (wfA x) as [x _ IHx]; clear wfA.
     intros y.
     induction (wfB y) as [y _ IHy]; clear wfB.
     constructor.
     intros [x' y'] H.
     now inversion H; subst; clear H; eauto.
   Qed.

   Theorem wf_prod_strict :
     well_founded (strict leA) ->
     well_founded (strict leB) ->
     well_founded (strict (prod_relation leA leB)).
   Proof.
     intros wfA wfB [x y]. generalize dependent y.
     induction (wfA x) as [x _ IHx]; clear wfA.
     intros y.
     generalize dependent x.
     induction (wfB y) as [y _ IHy]; clear wfB.
     intros x IH.
     constructor.
     intros [x' y'] H.
     inversion H as [[??] [?|?]%Classical_Prop.not_and_or]; subst; clear H; first by apply IH.
     apply IHy; first done. intros ???. eapply IH, strict_transitive_l =>//.
   Qed.

  Global Instance prod_relation_antisym :
    AntiSymm eq leA → AntiSymm eq leB → AntiSymm eq (prod_relation leA leB).
  Proof.
    intros ??[??] [??] [??] [??].
    f_equal; firstorder eauto.
  Qed.

  Global Instance prod_relation_preorder :
    PreOrder leA → PreOrder leB → PreOrder (prod_relation leA leB).
  Proof. firstorder eauto. Qed.

  Global Instance prod_relation_partialorder :
    PartialOrder leA → PartialOrder leB → PartialOrder (prod_relation leA leB).
  Proof.
    intros. split; first (firstorder eauto).
    typeclasses eauto.
  Qed.
End product_of_orders.

Section unstrict_order.
  Context {A B : Type}.
  Variables (lt : relation A).

  Definition unstrict x y :=
    x = y ∨ lt x y.
End unstrict_order.

Definition the_order (s1 s2: the_model): Prop :=
  match s1, s2 with
  | (N1, B1, yf1, nf1), (N2, B2, yf2, nf2) =>
    prod_relation
      (unstrict (lexprod _ _ (strict Nat.le) (strict bool_le)))
      (prod_relation bool_le bool_le)
      (N1, B1, (yf1, nf1))
      (N2, B2, (yf2, nf2))
  end.

Ltac inv_lexs :=
  repeat match goal with
    [ H: lexprod _ _ _ _ _ _ |- _ ] => inversion H; clear H; simplify_eq
         end.


#[local] Instance the_order_po: PartialOrder the_order.
Proof.
  constructor.
  - constructor.
    + intros x. destruct x as [[[??]?]?]. simpl.
      unfold prod_relation. simpl. split; last done.
      by econstructor.
    + intros [[[??]?]?] [[[??]?]?] [[[??]?]?]. simpl.
      unfold prod_relation. simpl. intros (Hlex1&?&?) (Hlex2&?&?). split; last first.
      * split; etransitivity =>//.
      * inversion Hlex1; inversion Hlex2; simplify_eq;
          try (econstructor 1; try (etransitivity; done); inv_lexs; f_equal; done);
          try (econstructor 2; try done).
        inv_lexs.
        ** econstructor. by etransitivity.
        ** econstructor 1 =>//.
        ** econstructor => //.
        ** econstructor 2. by etransitivity.
  -  intros [[[??]?]?] [[[??]?]?]. simpl.
      unfold prod_relation. simpl. intros (Hlex1&?&?) (Hlex2&?&?).
      do 3 f_equal; try (by eapply anti_symm =>//).
     + inversion Hlex1; inversion Hlex2; simplify_eq; try (eapply anti_symm =>//; done);
         inv_lexs; eauto. exfalso; eapply (strict_anti_symm (R := strict Nat.le)) =>//; eapply _.
     + inversion Hlex1; inversion Hlex2; simplify_eq; try (eapply anti_symm =>//; done);
       inv_lexs; eauto; try by eapply anti_symm;
         exfalso; eapply (strict_anti_symm (R := strict Nat.le)); eauto.
       exfalso; eapply (strict_anti_symm (R := strict bool_le)); eauto.
     + eapply anti_symm =>//; apply _.
     + eapply anti_symm =>//; apply _.
       Unshelve. all: exact eq.
Qed.

Definition the_decreasing_role (s: the_model): YN :=
  match s with
  | (0%nat, false, true, false) => Y
  | (0%nat, true, false, true) => No
  | (1%nat, false, true, false) => Y
  | (_, true, _, _) => Y
  | (_, false, _, _) => No
  end.

#[local] Instance eq_antisymm A: Antisymmetric A eq eq.
Proof. by intros ??. Qed.

Definition same: the_model -> (nat * bool * (bool * bool)) :=
  λ '(N, B, yf, nf), (N, B, (yf, nf)).

Lemma strict_unstrict {A} (R: relation A):
  forall x y, strict (unstrict R) x y -> R x y.
Proof.
  unfold strict, unstrict.
  intros x y.
  intros [[?|?] [Hneq HnR]%Classical_Prop.not_or_and] =>//.
Qed.

Lemma wf_bool_le: wf (strict bool_le).
Proof.
  intros b. destruct b; constructor; intros b' h; destruct b'; inversion h as [h1 h2];
              [done| | inversion h1| done]. clear h1 h2.
  constructor; intros b' h'; inversion h' as [h1 h2]; destruct b'; [inversion h1 | exfalso; eauto].
Qed.

#[local] Instance lex_trans `{Transitive A R1, Transitive B R2}: Transitive (lexprod A B R1 R2).
Proof.
  intros [x x'] [y y'] [z z'] Ha Hb.
  inversion Ha; inversion Hb; simplify_eq.
  - constructor 1. etransitivity =>//.
  - by constructor 1.
  - by constructor 1.
  - constructor 2. etransitivity =>//.
Qed.

#[local] Instance test1 `{Transitive A R}: Transitive (unstrict R).
Proof.
  intros x y z [?|?] [?|?]; simplify_eq; ((left; done) || right; eauto).
Qed.

Lemma the_model_almost_wf:
  wf (strict $
    prod_relation
      (unstrict (lexprod _ _ (strict Nat.le) (strict bool_le)))
      (prod_relation bool_le bool_le)).
Proof.
  apply wf_prod_strict.
  - apply _.
  - assert (H: wf (lexprod nat bool (strict Nat.le) (strict bool_le))).
    + apply wf_lexprod; last apply wf_bool_le.
      eapply (wf_projected _ id); last apply Nat.lt_wf_0.
      intros ??[??]. simpl. lia.
    + eapply (wf_projected _ id); last exact H.
      intros ???. apply strict_unstrict => //.
  - apply wf_prod_strict; eauto using wf_bool_le.
    apply _.
Qed.



#[local] Program Instance the_model_terminates: FairTerminatingModel the_model :=
  {|
  ftm_leq := the_order;
  ftm_decreasing_role := the_decreasing_role;
  |}.
Next Obligation.
  eapply (wf_projected _ same); last exact the_model_almost_wf.
  intros [[[? ?] ?] ?] [[[? ?] ? ]?] ?. eauto.
Qed.
Next Obligation.
  intros [[[N B] yf] nf] Hex.
  destruct B.
  - split.
    + simpl. destruct yf.
      * do 2 (destruct N; try set_solver).
      * destruct Hex as [ρ' [s' Hex]].
        inversion Hex; subst. set_solver.
    + intros [[[N' B'] yf'] nf'] Htrans.
      inversion Htrans; simplify_eq; rewrite strict_spec_alt; (split; [| try done; do 2 (destruct N'; eauto)]);
       (constructor; [simpl; eauto; unfold unstrict; (try by left) |]).
      { right. constructor 2. constructor; eauto. constructor. }
      all: simpl; by constructor.
  - split.
    + simpl. destruct nf.
      * destruct N; simpl; destruct yf; try set_solver; destruct N; set_solver.
      * destruct Hex as [ρ' [s' Hex]].
        inversion Hex; subst. destruct N; try set_solver.
        destruct N; try set_solver. lia.
    + intros [[[N' B'] yf'] nf'] Htrans.
      inversion Htrans; simplify_eq; rewrite strict_spec_alt; (split; [| try done; do 2 (destruct N'; eauto)]);
       (constructor ; [simpl; eauto; unfold unstrict; (try by left) |]).
      all: simpl; try by constructor.
      all: right; constructor 1; split; lia.
Qed.
Next Obligation.
  intros [[[N B] yf] nf]  [[[N' B'] yf'] nf'] ρ Htrans Hnex.
  inversion Htrans ; simplify_eq; eauto; simpl in *;
    try (destruct N'; eauto); try lia; (try (destruct N'; done)); try done.
  - destruct yf'; done.
  - destruct B'; try done. destruct nf'; done.
  - have ?: N' = 0%nat by lia. subst. destruct B' =>//.
    destruct nf'=>//.
  - destruct B' =>//; destruct yf' =>//.
Qed.
Next Obligation.
  intros [[[N B] yf] nf] ρ [[[N' B'] yf'] nf'] Htrans.
  destruct ρ; last by inversion Htrans.
  inversion Htrans; simplify_eq; simpl.
  all: constructor; [((left; done) || right; (constructor 1; constructor; done) || (try constructor 2)); simpl | simpl; try reflexivity].
  - constructor. constructor. eauto.
  - constructor 1; split; lia.
  - constructor 1; split; lia.
  - constructor. constructor. eauto. done.
  - constructor; done.
Qed.

(* The model is finitely branching *)
Definition steppable '(n, w, yf, nf): list ((nat * bool * bool * bool) * option YN) :=
  n' ← [n; (n-1)%nat];
  w' ← [w; negb w];
  yf' ← [yf; negb yf];
  nf' ← [nf; negb nf];
  ℓ ← [Some Y; Some No];
  mret ((n', w', yf', nf'), ℓ).

#[local] Instance proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in yntrans s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma model_finitary s:
  Finite { '(s', ℓ) | yntrans s ℓ s'}.
Proof.
  assert (H: forall A (y x: A) xs, (y = x ∨ y ∈ xs) -> y ∈ x::xs) by set_solver.
  eapply (in_list_finite (steppable s)).
  intros [[[n w] yf] nf] Htrans.
  inversion Htrans; try (repeat (rewrite ?Nat.sub_0_r; simpl;
    eapply H; try (by left); right); done).
Qed.

Theorem yesno_terminates
        (N : nat)
        (HN: N > 0)
        (extr : extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [start #N]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  assert (heapGpreS yesnoΣ the_model) as HPreG.
  { apply _. }
  eapply (simulation_adequacy_terminate_ftm (Mdl := the_model) yesnoΣ NotStuck _ (N, true, true, true)) =>//.
  - eapply valid_state_evolution_finitary_fairness.
    intros ?. simpl. apply (model_finitary s1).
  - set_solver.
  - intros ?. iStartProof. iIntros "!> Hm Hf !>". simpl.
    iApply (start_spec _ _ 45 with "[Hm Hf]"); eauto.
    + lia.
    + iSplitL "Hm"; eauto. iSplit; last done.
      assert ({[Y := 45%nat; No := 45%nat]} = gset_to_gmap 45 {[Y; No]}) as <-; last done.
      rewrite -leibniz_equiv_iff. intros ρ.
      destruct (gset_to_gmap 45 {[Y; No]} !! ρ) as [f|] eqn:Heq.
      * apply lookup_gset_to_gmap_Some in Heq as [Heq ->].
        destruct (decide (ρ = Y)) as [-> |].
        ** rewrite lookup_insert //.
        ** rewrite lookup_insert_ne //. assert (ρ = No) as -> by set_solver.
           rewrite lookup_insert //.
      * apply lookup_gset_to_gmap_None in Heq.
        repeat (rewrite lookup_insert_ne //; last set_solver).
Qed.
