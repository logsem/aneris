From trillium.fairness.examples.yesno Require Import yesno.
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

Definition the_order := unstrict (lexprod _ _ (strict Nat.le) (strict bool_le)).

Ltac inv_lexs :=
  repeat match goal with
    [ H: lexprod _ _ _ _ _ _ |- _ ] => inversion H; clear H; simplify_eq
         end.

Lemma lexprod_lexico x y:
  lexprod _ _ (strict Nat.le) (strict bool_le) x y <-> lexico x y.
Proof.
  split.
  - intros [???? H|x' y' z' H].
    + left =>/=. compute. compute in H. lia.
    + right =>/=. compute; split=>//. compute in H. destruct y'; destruct z' =>//; intuition.
  - destruct x as [x1 x2]. destruct y as [y1 y2]. intros [H|[Heq H]]; simpl in *.
    + left =>/=. compute. compute in H. lia.
    + rewrite Heq. right =>/=. destruct x2; destruct y2 =>//; intuition. constructor =>//. eauto.
Qed.

#[local] Instance the_order_po: PartialOrder the_order.
Proof.
  constructor.
  - constructor.
    + intros ?. by left.
    + unfold the_order. intros [x1 x2] [y1 y2] [z1 z2] [|H1] [|H2]; simplify_eq; try (by left); right; eauto.
      rewrite -> lexprod_lexico in *. etransitivity =>//.
  - intros [x1 x2] [y1 y2] [|H1] [|H2]; simplify_eq =>//.
    inversion H1; inversion H2; simplify_eq; try (compute in *; lia).
    destruct x2; destruct y2; compute in *; intuition.
Qed.

Definition the_decreasing_role (s: the_fair_model): YN :=
  match s with
  | (0%nat, false) => Y
  | (_, true) => Y
  | (_, false) => No
  end.

#[local] Instance eq_antisymm A: Antisymmetric A eq eq.
Proof. by intros ??. Qed.

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

#[local] Program Instance the_model_terminates: FairTerminatingModel the_fair_model :=
  {|
  ftm_leq := the_order;
  ftm_decreasing_role := the_decreasing_role;
  |}.
Next Obligation.
  unfold the_order.
  assert (H: wf (lexprod nat bool (strict Nat.le) (strict bool_le))).
  + apply wf_lexprod; last apply wf_bool_le.
    eapply (wf_projected _ id); last apply Nat.lt_wf_0.
    intros ??[??]. simpl. lia.
  + eapply (wf_projected _ id); last exact H.
    intros ???. apply strict_unstrict => //.
Qed.
Next Obligation.
  intros [N B] Hex.
  destruct B.
  - split.
    + simpl. destruct N.
      * destruct Hex as [ρ' [s' Hex]].
        inversion Hex; subst; lia.
      * destruct N; set_solver.
    + intros [??] H. inversion H; simplify_eq.
      * split; [right; right; compute; done| compute; intros [?|contra] =>//].
        inversion contra; simplify_eq; intuition.
      * destruct n =>//.
  - split.
    + destruct N; simpl.
      * destruct Hex as [ρ' [s' Hex]].
        inversion Hex; subst; lia.
      * destruct N; set_solver.
    + intros [[|?] ?] H.
      * inversion H; simplify_eq; [lia|]. unfold strict, the_order; split.
        ** right; left. compute. lia.
        ** intros [|contra] =>//. inversion contra; simplify_eq. compute in *. lia.
      * inversion H; simplify_eq. split; [right;left; compute; lia|].
        intros [|contra] =>//; inversion contra; simplify_eq; last lia. compute in *. lia.
Qed.
Next Obligation.
  intros [N B]  [N' B'] ρ Htrans Hnex.
  inversion Htrans ; simplify_eq; eauto; simpl in *;
    try (destruct N'; eauto); try lia; (try (destruct N'; done)); try done.
Qed.
Next Obligation.
  intros [N B] ρ [N' B'] Htrans.
  destruct ρ; last by inversion Htrans.
  inversion Htrans; simplify_eq; simpl; try reflexivity.
  - right; constructor 2; by compute.
  - right; constructor 1; compute. lia.
Qed.

(* The model is finitely branching *)
Definition steppable '(n, w): list ((nat * bool) * option YN) :=
  n' ← [n; (n-1)%nat];
  w' ← [w; negb w];
  ℓ ← [Some Y; Some No];
  mret ((n', w'), ℓ).

#[local] Instance proof_irrel_trans s x:
  ProofIrrel ((let '(s', ℓ) := x in yntrans s ℓ s'): Prop).
Proof. apply make_proof_irrel. Qed.

Lemma model_finitary s:
  Finite { '(s', ℓ) | yntrans s ℓ s'}.
Proof.
  assert (H: forall A (y x: A) xs, (y = x ∨ y ∈ xs) -> y ∈ x::xs) by set_solver.
  eapply (in_list_finite (steppable s)).
  intros [n w] Htrans.
  inversion Htrans; try (repeat (rewrite ?Nat.sub_0_r; simpl;
    eapply H; try (by left); right); done).
Qed.

Theorem yesno_terminates
        (N : nat)
        (HN: N > 1)
        (extr : extrace)
        (Hvex : extrace_valid extr)
        (Hexfirst : (trfirst extr).1 = [start #N]):
  (∀ tid, fair_ex tid extr) -> terminating_trace extr.
Proof.
  assert (heapGpreS yesnoΣ the_fair_model the_model) as HPreG.
  { apply _. }
  eapply (simulation_adequacy_terminate_ftm (Mdl := the_fair_model) yesnoΣ NotStuck _ (N, true) ∅) =>//.
  - eapply valid_state_evolution_finitary_fairness_simple.
    intros ?. simpl. apply (model_finitary s1).
  - destruct N; [lia|destruct N; set_solver].
  - intros ?. iStartProof. iIntros "!> Hm HFR Hf !>". simpl.
    iApply (start_spec _ _ 61 with "[Hm Hf HFR]"); eauto.
    + iSplitL "Hm"; eauto. do 2 (destruct N; first lia).
      assert (∅ ∖ {[ No; Y ]} = ∅) as -> by set_solver. iFrame. iSplit; last (iPureIntro; lia).
      assert ({[Y := 61%nat; No := 61%nat]} = gset_to_gmap 61 {[No;Y]}) as <-; last done.
      rewrite -leibniz_equiv_iff. intros ρ.
      destruct (gset_to_gmap 61 {[Y; No]} !! ρ) as [f|] eqn:Heq.
      * apply lookup_gset_to_gmap_Some in Heq as [Heq ->].
        destruct (decide (ρ = Y)) as [-> |].
        ** rewrite lookup_insert //. rewrite lookup_gset_to_gmap option_guard_True //. set_solver.
        ** rewrite lookup_insert_ne //. assert (ρ = No) as -> by set_solver.
           rewrite lookup_insert // lookup_gset_to_gmap option_guard_True //. set_solver.
      * apply lookup_gset_to_gmap_None in Heq. destruct ρ; set_solver.
Qed.
