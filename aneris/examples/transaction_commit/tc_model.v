From Coq.ssr Require Export ssreflect.
From stdpp Require Import base gmap.

(* This model follows the transactional commit TLA+ specification:

     https://github.com/tlaplus/Examples/blob/master/specifications/transaction_commit/TCommit.tla

   originally developed as part of the "Consensus on Transaction Commit" paper

     https://www.microsoft.com/en-us/research/uploads/prod/2004/01/twophase-revised.pdf
*)
Section tla_style.
  Context {K : Type} `{Countable K}.
  Context (RMs : gset K).

  Inductive rm_state :=
  | WORKING
  | PREPARED
  | COMMITTED
  | ABORTED.

  Global Instance : EqDecision rm_state.
  Proof. solve_decision. Qed.
  Global Instance : Countable rm_state.
  Proof.
    refine
      {| encode st :=
           match st with
           | WORKING => 1 | PREPARED => 2 | COMMITTED => 3 | ABORTED => 4
           end%positive;
         decode p :=
           match p with
           | 1 => Some WORKING | 2 => Some PREPARED | 3 => Some COMMITTED
           | 4 => Some ABORTED | _ => None
           end%positive |}; by intros [].
  Qed.

  Definition TCState := gmap K rm_state.

  Instance : Countable TCState.
  Proof. apply _. Qed.

  Definition TCInit := gset_to_gmap WORKING RMs.

  Definition canCommit (rmState : TCState) :=
    ∀ rm, rm ∈ RMs → rmState !! rm = Some PREPARED ∨ rmState !! rm = Some COMMITTED.
  Definition notCommitted (rmState : TCState) :=
    ∀ rm, rm ∈ RMs → ¬ (rmState !! rm = Some COMMITTED).

  Inductive TCNext : TCState → TCState → Prop :=
  | tc_prepare rm rmState :
      rmState !! rm = Some WORKING →
      TCNext rmState (<[ rm := PREPARED ]> rmState)
  | tc_decide_commit rm rmState :
      rmState !! rm = Some PREPARED →
      canCommit rmState →
      TCNext rmState (<[ rm := COMMITTED ]> rmState)
  | tc_decide_abort rm rmState :
      (rmState !! rm = Some WORKING ∨ rmState !! rm = Some PREPARED) →
      notCommitted rmState →
      TCNext rmState (<[ rm := ABORTED ]> rmState).

  Theorem TCConsistent rmState rm1 rm2 st1 st2 :
    rm1 ∈ RMs ∧ rm2 ∈ RMs →
    rtc TCNext TCInit rmState →
    rmState !! rm1 = Some st1 ∧ rmState !! rm2 = Some st2 →
    ¬ (st1 = ABORTED ∧ st2 = COMMITTED).
  Proof.
    intros [Helem1 Helem2].
    apply (rtc_ind_r (λ r, r !! _ = _ ∧ r !! _ = _ → ¬ _)).
    { rewrite /TCInit !lookup_gset_to_gmap_Some.
      intros [[] []] []; subst. discriminate. }
    intros r' r'' Hrtc Hnext Hr'.
    inversion Hnext as [|??? HcanC | ??? HnotC]; simplify_eq.
    - destruct (decide (rm = rm1)); simplify_eq.
      { rewrite !lookup_insert. intros [??] [??]; simplify_eq. }
      rewrite lookup_insert_ne //.
      destruct (decide (rm = rm2)); simplify_eq.
      { rewrite !lookup_insert. intros [??] [??]; simplify_eq. }
      rewrite lookup_insert_ne //.
    - destruct (decide (rm = rm1)); simplify_eq.
      { rewrite !lookup_insert. intros [??] [??]; simplify_eq. }
      rewrite lookup_insert_ne //.
      intros [??] [??]; simplify_eq.
      destruct (HcanC rm1) as [|]; [done|simplify_map_eq..].
    - destruct (decide (rm = rm1)); simplify_eq.
      + destruct (decide (rm1 = rm2)); simplify_eq.
        { rewrite !lookup_insert. intros [??] [??]; simplify_eq. }
        rewrite lookup_insert lookup_insert_ne //.
        intros [??] [??]; simplify_eq. by eapply HnotC.
      + rewrite lookup_insert_ne //.
        destruct (decide (rm = rm2)); simplify_eq.
        { rewrite !lookup_insert. intros [??] [??]; simplify_eq. }
        rewrite lookup_insert_ne //.
  Qed.

End tla_style.
