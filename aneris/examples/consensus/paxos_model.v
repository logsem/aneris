From Coq.ssr Require Import ssreflect.
From stdpp Require Import base functions gmap propset finite.
From aneris.prelude Require Import sig_gset gset_map quorum.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* This model follows the Paxos TLA+ specification:

     https://github.com/tlaplus/Examples/blob/master/specifications/PaxosHowToWinATuringAward/Paxos.tla

   The correctness proof uses predicates and intermediate results as stated in
   [Voting.tla] from the same directory on GitHub. *)

(* The paxos model is parameterized over a type of value to agree on, a type of
   acceptors, and a set of acceptors with a notion of quorum *)
Class PaxosParams (A V : Type) `{Countable A, Countable V} := {
  Acceptors : gset A;
  Acceptors_quorum : Quorum Acceptors;
  Values : gset V;
}.

Section model.
  Context `{params : PaxosParams A V}.

  Definition Ballot := nat.
  Definition Acceptor := sig_gset Acceptors.
  Definition Value := sig_gset Values.

  Definition Acceptors' := sig_gset_gset Acceptors.
  Program Definition QuorumA : Quorum Acceptors' :=
    quorum _ (λ Q, Acceptors_quorum (gset_map proj1_sig Q)) _ _.
  Next Obligation.
    intros ??. apply elem_of_subseteq.
    intros [] ?. by apply elem_of_sig_gset_gset.
  Qed.
  Next Obligation.
    simpl. intros ?????.
    assert (gset_map proj1_sig Q1 ∩ gset_map proj1_sig Q2 ≠ ∅).
    { by eapply quorum_intersection_nonempty. }
    set_solver.
  Qed.

  Inductive Message : Type :=
  | msg1a (bal : Ballot)
  | msg1b (acc : Acceptor) (bal : Ballot) (mval : option (Ballot * Value))
  | msg2a (bal : Ballot) (val : Value)
  | msg2b (acc : Acceptor) (bal : Ballot) (val : Value).

  Global Instance : EqDecision Message.
  Proof. solve_decision. Qed.
  Global Instance : Countable Message.
  Proof.
    refine
      (inj_countable'
         (λ m, match m with
               | msg1a bal => inl (inl bal)
               | msg1b acc bal mval => inl (inr (acc, bal, mval))
               | msg2a bal val => inr (inl (bal, val))
               | msg2b acc bal val => inr (inr (acc, bal, val))
               end)
         (λ m, match m  with
               | inl (inl bal) => msg1a bal
               | inl (inr (acc, bal, mval)) => msg1b acc bal mval
               | inr (inl (bal, val)) => msg2a bal val
               | inr (inr (acc, bal, val)) => msg2b acc bal val
               end)  _); by intros [].
  Qed.

  Record PaxosState := MkPaxosState {
    (* [maxBal(a)] is a ballot such that [a] will never cast any further vote in
       a ballot numbered strictly less than [maxBal(a)]. [None] denotes [-1] in
       the TLA specification.  *)
    maxBal  : Acceptor → option Ballot;
    (* The pair [maxVal(a) = (b, v)] is the vote [v] with the largest ballot [b]
       cast by acceptor [a]. This is a unification of [maxVal] and [maxVBal]
       from the TLA model. *)
    maxVal  : Acceptor → option (Ballot * Value);
    (* The set of all messages that have been sent. Messages are added to [msgs]
       when they are sent and are never removed. *)
    msgs : gset Message;
  }.
  Global Instance etaTpState : Settable _ :=
    settable! MkPaxosState <maxBal; maxVal; msgs>.

  Definition PInit := {| maxBal := λ _, None; maxVal := λ _, None; msgs := ∅ |}.

  Implicit Types bal : Ballot.
  Implicit Types b : option Ballot.
  Implicit Types m : Message.
  Implicit Types s : PaxosState.
  Implicit Types a : Acceptor.
  Implicit Types val : Value.
  Implicit Types mval : option (Ballot * Value).

  Definition ShowsSafeAt (s : PaxosState) (Q : gset Acceptor) (bal : Ballot) (val : Value) :=
    (* the set of sent phase 1b messages with ballot [b] sent by acceptors
       from [Q] *)
    let Q1b  := {[ m | m ∈ s.(msgs) ∧ ∃ a mv, m = msg1b a bal mv ∧ a ∈ Q ]} in
    (* the set of sent phase 1b messages with ballot [b] where the acceptor
       has previously cast a vote *)
    let Q1bv := {[ m | m ∈ Q1b ∧ ∃ a mv, m = msg1b a bal (Some mv) ]} in
    (* there must be a phase 1b message in [Q1b] from all acceptors in the
       quorum *)
    (∀ a, a ∈ Q → ∃ m, m ∈ Q1b ∧ ∃ mv, m = msg1b a bal mv) ∧
    (* either the set is empty, meaning the parties in the quorum have not
       voted yet and the proposer is free to propose a value *)
    (Q1bv ≡ ∅ ∨
     (* or at least one value has already been proposed, and the leader must
       propose the value of the vote with the largest ballot *)
     (∃ m a bal1,
         m = msg1b a bal (Some (bal1, val)) ∧ m ∈ Q1bv ∧
         ∀ mm, mm ∈ Q1bv →
               ∃ a bal2 val', mm = msg1b a bal (Some (bal2, val')) ∧
                              bal1 ≥ bal2)).

  Inductive PNext : PaxosState → PaxosState → Prop :=
  (* In the [Phase1a(bal)] action, the leader sends to all acceptors a phase 1a
     message that begins ballot [bal]. *)
  | phase1a bal s :
      PNext s (s <| msgs ::= λ ms, ms ∪ {[msg1a bal]} |>)
  (* Upon receipt of a ballot [bal] from a phase 1a message, acceptor [a] can
     perform a [Phase1b(a)] action only if [bal > maxBal(a)]. The action sets
     [maxBal(a)] to [bal] and sends a phase 1b message to the leader with
     [maxVal(a)]. *)
  | phase1b a s bal b' mval :
      msg1a bal ∈ s.(msgs) →
      s.(maxBal) a = b' →
      s.(maxVal) a = mval →
      (b' = None ∨ ∃ bal', b' = Some bal' ∧ bal > bal') →
      PNext s (s <| maxBal ::= λ mb, <[a := Some bal]>mb |>
                <| msgs   ::= λ ms, ms ∪ {[msg1b a bal mval]} |>)
  (* In the [Phase2a(bal, val)] action, the ballot [bal] leader sends a 2a
     message asking the acceptors to vote for [val] in ballot number [bal]. The
     condition [ShowsSafeAt] is the heart of the Paxos algorithm. *)
  | phase2a bal val s Q :
      (* No phase2a message must have been sent for ballot [b] yet *)
      ¬ (∃ val', msg2a bal val' ∈ s.(msgs)) →
      (* Q is a quorum *)
      QuorumA Q →
      ShowsSafeAt s Q bal val →
      PNext s (s <| msgs ::= λ ms, ms ∪ {[msg2a bal val]} |>)
  (* Acceptor [a] acts on a phase 2a message [m] request, voting for [m.val] in
     ballot number [m.bal], iff [m.bal >= maxBal(a)], which means that [a] has
     not participated in any ballot numbered greater than [m.bal]. [maxBal] and
     [maxVal] are updated to keep their meaning. *)
  | phase2b a s bal val b' :
      msg2a bal val ∈ s.(msgs) →
      s.(maxBal) a = b' →
      (b' = None ∨ ∃ bal', b' = Some bal' ∧ bal ≥ bal') →
      PNext s (s <| maxBal ::= λ mb, <[a := Some bal]>mb |>
                <| maxVal ::= λ mv, <[a := Some (bal, val)]>mv |>
                <| msgs   ::= λ ms, ms ∪ {[msg2b a bal val]} |>).
End model.

Section model_correctness.
  Context `{params : PaxosParams A V}.

  Implicit Types bal : Ballot.
  Implicit Types b : option Ballot.
  Implicit Types m : Message.
  Implicit Types s : PaxosState.
  Implicit Types a : Acceptor.
  Implicit Types val : Value.
  Implicit Types mval : option (Ballot * Value).

  (** * Predicates from the TLA+ proof *)
  Definition VotedFor s a bal val := msg2b a bal val ∈ s.(msgs).

  Definition ChosenAt s bal val :=
    ∃ Q, QuorumA Q ∧ ∀ a, a ∈ Q → VotedFor s a bal val.

  Definition Chosen s val := ∃ bal, ChosenAt s bal val.

  Definition DidNotVoteAt s a bal := ∀ val, ¬ VotedFor s a bal val.

  Definition CannotVoteAt s a bal :=
    ∃ bal', s.(maxBal) a = Some bal' ∧ bal' > bal ∧ DidNotVoteAt s a bal.

  Definition NoneOtherChoosableAt s bal val :=
    ∃ Q, QuorumA Q ∧ ∀ a, a ∈ Q → VotedFor s a bal val ∨ CannotVoteAt s a bal.

  Definition SafeAt s bal val := ∀ c, c < bal → NoneOtherChoosableAt s c val.

  (** * Model correctness lemmas *)
  Lemma VotedFor_send s m a bal v:
    VotedFor s a bal v →
    VotedFor (s <| msgs ::= (λ ms, ms ∪ {[m]}) |>) a bal v.
  Proof. rewrite /VotedFor elem_of_union elem_of_singleton. auto. Qed.

  Lemma DidNotVoteAt_send_not2b s m a bal0 :
    (¬ ∃ a bal v, m = msg2b a bal v) →
    DidNotVoteAt s a bal0 →
    DidNotVoteAt (s <| msgs ::= (λ ms, ms ∪ {[m]}) |>) a bal0.
  Proof.
    intros ? Hs ?. rewrite /VotedFor /= elem_of_union elem_of_singleton.
    intros [|]; eauto. by eapply Hs.
  Qed.

  Lemma DidNotVoteAt_2b_neq s bal0 bal a a' val :
    bal0 ≠ bal →
    DidNotVoteAt s a bal0 →
    DidNotVoteAt (s <| msgs ::= (λ ms, ms ∪ {[msg2b a' bal val]}) |>) a bal0.
  Proof.
    intros ? Hnvote v. rewrite /VotedFor elem_of_union elem_of_singleton.
    intros [|]; [|simplify_eq]. by eapply Hnvote.
  Qed.

  Lemma DidNotVoteAt_no_msg s a bal a' b' mval :
    DidNotVoteAt s a bal →
    DidNotVoteAt (s <| maxBal ::= (λ mb, <[a':= b' ]> mb) |>
                    <| maxVal ::= (λ mv, <[a':= mval]> mv) |>) a bal.
  Proof. done. Qed.

  Lemma CannotVoteAt_send_not2b s m a bal :
    (¬ ∃ a bal' v, m = msg2b a bal' v) →
    CannotVoteAt s a bal →
    CannotVoteAt (s <| msgs ::= (λ ms, ms ∪ {[m]}) |>) a bal.
  Proof.
    rewrite /CannotVoteAt /=. intros ? (?&?&?&?).
    eexists. split_and!; [done|done|]. by eapply DidNotVoteAt_send_not2b.
  Qed.

  Lemma CannotVoteAt_maxBal s a bal0 bal a' :
    (maxBal s a = None ∨
     (∃ bal' : Ballot, maxBal s a = Some bal' ∧ bal > bal')) →
    CannotVoteAt s a' bal0 →
    CannotVoteAt (s <| maxBal ::= (λ mb, <[a := Some bal]> mb) |>) a' bal0.
  Proof.
    rewrite /CannotVoteAt /=.
    destruct (decide (a = a')); last first.
    { rewrite fn_lookup_insert_ne //. }
    intros Hmb (b'&?&?&?); simplify_eq.
    destruct Hmb as [? | (? &?&?)]; simplify_eq.
    exists bal. rewrite fn_lookup_insert.
    split_and!; [done|lia|done].
  Qed.

  Lemma CannotVoteAt_2b_other s a bal0 a' bal val :
    (maxBal s a' = None ∨ (∃ bal', maxBal s a' = Some bal' ∧ bal ≥ bal')) →
    CannotVoteAt s a bal0 →
    CannotVoteAt
      (s <| maxBal ::= (λ mb, <[a' := Some bal]> mb) |>
         <| maxVal ::= (λ mv, <[a' := Some (bal, val)]> mv) |>
         <| msgs   ::= (λ ms, ms ∪ {[msg2b a' bal val]}) |>) a bal0.
  Proof.
    rewrite /CannotVoteAt /=.
    intros Hmb (c & ? & ? & Hnvote).
    destruct (decide (a = a')); simplify_eq.
    - destruct Hmb as [|(?&?&?)]; simplify_eq.
      eexists. rewrite fn_lookup_insert.
      split_and!; [done|lia|].
      apply DidNotVoteAt_2b_neq; [|done].
      lia.
    - rewrite fn_lookup_insert_ne //.
      eexists. split_and!; [done|done|].
      unfold DidNotVoteAt in *. set_solver.
  Qed.

  Lemma SafeAt_send_not2b s m bal v :
    (¬ ∃ a bal' v, m = msg2b a bal' v) →
    SafeAt s bal v → SafeAt (s <| msgs ::= (λ ms, ms ∪ {[m]}) |>) bal v.
  Proof.
    intros Hn2b Hsafe c Hc.
    edestruct Hsafe as (Q & ? & Hvote); [done|].
    exists Q. split; [done|]. intros a' Ha'.
    destruct (Hvote a' Ha'); simpl.
    - left. by apply VotedFor_send.
    - right. apply CannotVoteAt_send_not2b; [|done].
      intros (?&?&?& [=]); eauto.
  Qed.

  Lemma SafeAt_maxBal s a v bal0 bal :
    (maxBal s a = None ∨ (∃ bal', maxBal s a = Some bal' ∧ bal > bal')) →
    SafeAt s bal0 v  →
    SafeAt (s <| maxBal ::= (λ mb, <[a := Some bal]> mb) |>) bal0 v.
  Proof.
    intros Hmb Hsafe c Hc.
    edestruct Hsafe as (Q & ? & Hvote); [done|].
    exists Q. split; [done|]. intros a' Ha'.
    destruct (Hvote a' Ha'); simpl; [eauto|].
    right. by apply CannotVoteAt_maxBal.
  Qed.

  Lemma SafeAt_2b_other s bal0 v a bal val :
    (maxBal s a = None ∨ (∃ bal', maxBal s a = Some bal' ∧ bal ≥ bal')) →
    SafeAt s bal0 v →
    SafeAt (s <| maxBal ::= (λ mb, <[a := Some bal]> mb) |>
              <| maxVal ::= (λ mv, <[a := Some (bal, val)]> mv) |>
              <| msgs   ::= (λ ms : gset Message, ms ∪ {[msg2b a bal val]}) |>)
           bal0 v.
  Proof.
    intros Hmb Hsafe c Hc.
    edestruct Hsafe as (Q & ? & Hvote); [done|].
    exists Q. split; [done|]. intros a' Ha'.
    destruct (Hvote a' Ha'); simpl.
    - left. by apply VotedFor_send.
    - right. by apply CannotVoteAt_2b_other.
  Qed.

  Lemma maxVal_inv s a bal val:
    rtc PNext PInit s → maxVal s a = Some (bal, val) → msg2b a bal val ∈ s.(msgs).
  Proof.
    apply: (rtc_ind_r (λ s, _)); [done|].
    intros s1 s2 Hs1 Hnext IH.
    inversion Hnext as [| | |a' ? ? ? ? H2a ? Hmb];
      simplify_eq=>/=;
      rewrite !elem_of_union !elem_of_singleton; eauto.
    destruct (decide (a = a')); simplify_eq.
    { rewrite fn_lookup_insert. intros ?; simplify_eq. eauto. }
    rewrite fn_lookup_insert_ne //. eauto.
  Qed.

  Lemma msg1b_inv s a bal mv:
    rtc PNext PInit s →
    msg1b a bal mv ∈ s.(msgs) →
    ∃ bal', s.(maxBal) a = Some bal' ∧ bal' ≥ bal.
  Proof.
    apply: (rtc_ind_r (λ s, _)); clear s.
    { rewrite elem_of_empty //. }
    intros s1 s2 Hrtc Hnext IH.
    inversion Hnext as [|a' ? bal0 ? ? H1a ? Hmv Hmb
                        | |a' ? ? ? ? H2a ? Hmb];
      simplify_eq=>/=;
      rewrite elem_of_union elem_of_singleton.
    - intros [|]; [|done]. eauto.
    - intros [H1b | ?].
      + destruct (IH H1b) as (?&?&?).
        destruct (decide (a = a')); simplify_eq.
        * rewrite fn_lookup_insert.
          destruct Hmb as [|(?&?&?)]; simplify_eq. eauto with lia.
        * rewrite fn_lookup_insert_ne; eauto.
      + simplify_eq. rewrite fn_lookup_insert. eauto.
    - intros [|]; [|done]. eauto.
    - intros [H1b | ?]; [|done].
      destruct (IH H1b) as (?&?&?).
      destruct (decide (a = a')); simplify_eq; eexists.
      * rewrite fn_lookup_insert.
        destruct Hmb as [|(?&?&?)]; simplify_eq. eauto with lia.
      * rewrite fn_lookup_insert_ne //.
  Qed.

  Lemma msg1b_agree s a bal mv1 mv2 :
    rtc PNext PInit s →
    msg1b a bal mv1 ∈ msgs s →
    msg1b a bal mv2 ∈ msgs s →
    mv1 = mv2.
  Proof.
    apply: (rtc_ind_r (λ s, _)); clear s.
    { rewrite elem_of_empty //. }
    move=> s1 s2 Hrtc Hnext IH.
    inversion Hnext as [|a' ? bal0 ? ? H1a ? Hmv Hmb| |];
      simplify_eq=>/=; rewrite !elem_of_union !elem_of_singleton.
    - move=> [? | ?] // [? | ?] //. eauto.
    - move=> [?|?] // [?|?] .
      + by apply IH.
      + edestruct msg1b_inv as (?&?&?); [done|done|].
        destruct Hmb as [|(?&?&?)]; simplify_eq. lia.
      + edestruct msg1b_inv as (?&?&?); [done|done|].
        destruct Hmb as [|(?&?&?)]; simplify_eq. lia.
      + by simplify_eq.
    - move=> [? | ?] // [? | ?] //. eauto.
    - move=> [? | ?] // [? | ?] //. eauto.
  Qed.

  Lemma msg2b_inv s a bal val :
    rtc PNext PInit s →
    msg2b a bal val ∈ s.(msgs) →
    msg2a bal val ∈ s.(msgs) ∧
    ∃ balb balv val, s.(maxBal) a = Some balb ∧
                     s.(maxVal) a = Some (balv, val) ∧ bal ≤ balv ≤ balb.
  Proof.
    apply: (rtc_ind_r (λ s, _)); [done|]; clear s.
    intros s1 s2 Hs1 Hnext IH.
    inversion Hnext as [|a' ? bal0 ? ? H1a ? Hmv Hmb
                        |? ? ? Q Hn2a HQ Hssa
                        |a' ? ? ? ? H2a ? Hmb];
      simplify_eq=>/=;
      rewrite !elem_of_union !elem_of_singleton.
    - intros [H2b | ?]; [|done]. destruct (IH H2b) as (?&?). eauto.
    - intros [H2b | ?]; [|done]. destruct (IH H2b) as (?&(?&?&?&?&?&?&?)).
      split; [eauto|].
      destruct (decide (a' = a)); simplify_eq; last first.
      { rewrite fn_lookup_insert_ne //. eauto 8. }
      rewrite fn_lookup_insert.
      destruct Hmb as [? | (?&?&?)]; simplify_eq.
      do 3 eexists. split_and!; [done|done|lia|lia].
    - intros [H2b | ?]; [|done]. destruct (IH H2b) as (?&?). eauto.
    - intros [H2b | ?]; simplify_eq.
      + destruct (IH H2b) as (?&?&?&?&?&?&?). split; [eauto|].
        destruct (decide (a' = a)); simplify_eq; last first.
        { rewrite !fn_lookup_insert_ne //. eauto 10. }
        rewrite !fn_lookup_insert.
        destruct Hmb as [? | (?&?&?)]; simplify_eq.
        do 3 eexists. split_and!; [done|done|lia|lia].
      + split; [auto|].
        rewrite !fn_lookup_insert.
        do 3 eexists. split_and!; [done|done|lia|lia].
  Qed.

  Lemma msg1b_Some_inv s a bal bal' val :
    rtc PNext PInit s →
    msg1b a bal (Some (bal', val)) ∈ s.(msgs) →
    VotedFor s a bal' val ∧ bal' < bal ∧
    ∀ c, bal' < c < bal → DidNotVoteAt s a c.
  Proof.
    apply: (rtc_ind_r (λ s, _)); [done|].
    rewrite /VotedFor.
    intros s1 s2 Hs1 Hnext IH.
    inversion Hnext as [|a' ? bal0 ? ? H1a ? Hmv Hmb
                        | |a' ? ? ? ? H2a ? Hmb];
      simplify_eq=>/=;
      rewrite !elem_of_union !elem_of_singleton.
    - intros [|]; [|done].
      edestruct IH as (?&?&?); [done|].
      split_and!; [auto|done|]. intros ??.
      apply DidNotVoteAt_send_not2b; [|eauto].
      intros (?&?&?&[=]).
    - intros [|]; simplify_eq.
      + edestruct IH as (?&?&?); [done|].
        split_and!; [auto|done|]. intros ??.
        apply DidNotVoteAt_send_not2b; [|eauto].
        intros (?&?&?&[=]).
      + assert (msg2b a' bal' val ∈ s1.(msgs)).
        { by eapply maxVal_inv. }
        edestruct msg2b_inv as (?&?&?&?&?&?&?); [done|done|].
        destruct Hmb as [|(?&?&?)]; simplify_eq.
        split_and!; [eauto|lia|]. intros ??.
        eapply DidNotVoteAt_send_not2b.
        { intros (?&?&?&[=]). }
        symmetry in H3. simplify_eq.
        rewrite /DidNotVoteAt /VotedFor /=.
        intros v Hvote.
        edestruct (msg2b_inv s1 a' c) as (?&?&?&?&?&?&?); [done|done|].
        simplify_eq. lia.
    - intros [|]; [|done].
      edestruct IH as (?&?&?); [done|].
      split_and!; [auto|done|]. intros ??.
      apply DidNotVoteAt_send_not2b; [|eauto].
      intros (?&?&?&[=]).
    - intros [|]; [|done].
      edestruct IH as (?&?&?); [done|].
      split_and!; [auto|done|]. intros ??.
      rewrite /DidNotVoteAt /VotedFor /=.
      intros ?. rewrite elem_of_union elem_of_singleton.
      intros [|].
      { by eapply IH. }
      simplify_eq.
      edestruct msg1b_inv as (?&?&?); [done|done|].
      destruct Hmb as [|(?&?&?)]; simplify_eq. lia.
  Qed.

  Lemma msg1b_None_inv s a bal c :
    rtc PNext PInit s →
    c < bal →
    msg1b a bal None ∈ s.(msgs) →
    DidNotVoteAt s a c.
  Proof.
    apply: (rtc_ind_r (λ s, _)); clear s; [done|].
    intros s1 s2 Hrtc Hnext IH Helem.
    rewrite /DidNotVoteAt /VotedFor.
    inversion Hnext as [|a' ? bal0 ? ? H1a ? Hmv Hmb
                        | |a' ? ? ? ? H2a ? Hmb];
      simplify_eq=>/=;
      move=> + ?; rewrite !elem_of_union !elem_of_singleton.
    - move=> [Hm1 |] // [Hm2 |] //. by eapply IH.
    - intros [Hm1 |] [Hm2 |]; simplify_eq.
      { by eapply IH. }
      edestruct msg2b_inv as (?&?&?&?&?&?&?); [done|done|].
      destruct Hmb as [?|(?&?&?)]; simplify_eq.
      congruence.
    - move=> [Hm1 |] // [Hm2 |] //. by eapply IH.
    - move=> [Hm1 |] // [Hm2 |] //.
      { by eapply IH. }
      intros [=]; simplify_eq.
      edestruct msg1b_inv as (?&?&?); [done|done|].
      destruct Hmb as [|(?&?&?)]; simplify_eq. lia.
  Qed.

  Lemma msg2a_agree s bal v1 v2 :
    rtc PNext PInit s →
    msg2a bal v1 ∈ s.(msgs) →
    msg2a bal v2 ∈ s.(msgs) →
    v1 = v2.
  Proof.
    apply: (rtc_ind_r (λ s, _)); [done|].
    intros s1 s2 Hs1 Hnext IH.
    inversion Hnext; simplify_eq; simpl;
      rewrite !elem_of_union !elem_of_singleton;
      intros [? | [=]] [? | [=]]; simplify_eq;
        eauto || exfalso; eauto.
  Qed.

  Lemma ShowsSafeAt_1a s Q bal val bal0 :
    ShowsSafeAt s Q bal val →
    ShowsSafeAt (s <| msgs ::= (λ ms, ms ∪ {[msg1a bal0]}) |>) Q bal val.
  Proof.
    intros (HQb & HQ1bv). split; [set_solver +HQb| set_solver +HQ1bv].
  Qed.

  Lemma ShowsSafeAt_1b s Q a bal0 bal val mv :
    rtc PNext PInit s →
    maxBal s a = None ∨ (∃ bal', maxBal s a = Some bal' ∧ bal0 > bal') →
    ShowsSafeAt s Q bal val →
    ShowsSafeAt (s <| maxBal ::= (λ mb, <[a:=Some bal0]> mb) |>
                   <| msgs   ::= (λ ms, ms ∪ {[msg1b a bal0 mv]}) |>) Q bal val.
  Proof.
    intros Hrtc Hmb (HQb & HQ1bv). split.
    { set_solver +HQb. }
    destruct HQ1bv as [Hempty | Hmax].
    - left. set_unfold.
      intros m (([|] & H1b) & H1bSome); [by eapply Hempty|].
      destruct H1b as (a' &?&?&?), H1bSome as (?&[? ?]&?). simplify_eq.
      edestruct HQb as (m & (Hm &?&?&?&?) &?&?); [done|]. simplify_eq.
      edestruct msg1b_inv as (?&?&?); [done|done|].
      destruct Hmb as [|(?&?&?)]; simplify_eq. lia.
    - right.
      destruct Hmax as (?&?&?&?& ((?&?&?&?&?) &?&?&?) & Hmm); simplify_eq=>/=.
      do 3 eexists. split; [done|].
      repeat split; [|eauto|eauto|].
      { by apply elem_of_union_l. }
      set_unfold. intros m (([|] & (?&?&?&?)) & (?& [] &?)); simplify_eq.
      { eapply Hmm. repeat split; eauto. }
      do 3 eexists. split; [done|].
      edestruct HQb as (m & (Hm &?&?&?&?) &?&?); [done|]. simplify_eq.
      edestruct msg1b_inv as (?&?&?); [done|done|].
      destruct Hmb as [|(?&?&?)]; simplify_eq. lia.
  Qed.

  Lemma ShowsSafeAt_2a s Q bal val bal0 val0 :
    ShowsSafeAt s Q bal val →
    ShowsSafeAt (s <| msgs ::= (λ ms, ms ∪ {[msg2a bal0 val0]}) |>) Q bal val.
  Proof.
    intros (HQb & HQ1bv). split.
    { set_solver +HQb. }
    destruct HQ1bv as [Hempty | Hmax].
    - left. set_unfold.
      intros m (([|] & H1b) & H1bSome); [by eapply Hempty|].
      destruct H1bSome as (?&?&?). simplify_eq.
    - right.
      destruct Hmax as (?&?&?&?& ((?&?&?&?&?) &?&?&?) & Hmm); simplify_eq=>/=.
      do 3 eexists. split; [done|].
      repeat split; [|eauto|eauto|].
      { by apply elem_of_union_l. }
      set_unfold. intros m (([|] & (?&?&?&?)) & (?& [] &?)); simplify_eq.
      eapply Hmm. repeat split; eauto.
  Qed.

  Lemma ShowsSafeAt_2b s a Q bal0 val0 bal val :
    ShowsSafeAt s Q bal val →
    ShowsSafeAt
      (s <| maxBal ::= (λ mb, <[a:=Some bal0]> mb) |>
         <| maxVal ::= (λ mv, <[a:=Some (bal0, val0)]> mv) |>
         <| msgs   ::= (λ ms, ms ∪ {[msg2b a bal0 val0]}) |>) Q bal val.
  Proof.
    intros (HQb & HQ1bv). split; [set_solver +HQb| set_solver +HQ1bv].
  Qed.

  Lemma msg2a_inv s bal val :
    rtc PNext PInit s →
    msg2a bal val ∈ s.(msgs) → ∃ Q, QuorumA Q ∧ ShowsSafeAt s Q bal val.
  Proof.
    apply: (rtc_ind_r (λ s, _)); [done|]; clear s.
    intros s1 s2 Hs1 Hnext IH.
    inversion Hnext as [|a' ? bal0 ? ? H1a ? Hmv Hmb
                        |? ? ? Q Hn2a HQ Hssa
                        |a' ? ? ? ? H2a ? Hmb];
      simplify_eq=>/=; clear Hnext;
      rewrite elem_of_union elem_of_singleton.
    - intros [H2a | [=]]. destruct (IH H2a) as (Q & ? & Hssa); clear IH.
      eexists. split; [done|]. by apply ShowsSafeAt_1a.
    - intros [H2a | [=]]. destruct (IH H2a) as (Q & ? & Hssa); clear IH.
      eexists. split; [done|]. by apply ShowsSafeAt_1b.
    - intros [H2a | [=]].
      + destruct (IH H2a) as (Q' & ? & Hssa'); clear IH.
        exists Q'. split; [done|]. by apply ShowsSafeAt_2a.
      + simplify_eq. eexists. split; [done|]. by apply ShowsSafeAt_2a.
    - intros [H2a' | [=]]. destruct (IH H2a') as (Q & ? & Hssa); clear IH.
      eexists. split; [done|]. by apply ShowsSafeAt_2b.
  Qed.

  Lemma msg1b_Some_inv_full s a bal bal' val :
    rtc PNext PInit s →
    msg1b a bal (Some (bal', val)) ∈ s.(msgs) →
    ∃ Q, QuorumA Q ∧ ShowsSafeAt s Q bal' val ∧
         bal' < bal ∧
         (∀ c, bal' < c < bal → DidNotVoteAt s a c) ∧
         msg2b a bal' val ∈ s.(msgs) ∧
         msg2a bal' val ∈ s.(msgs).
  Proof.
    intros Hrtc H1b.
    edestruct msg1b_Some_inv as (?&?&?); [done|done|].
    edestruct msg2b_inv as (H2a &?&?&?&?&?&?); [done|done|].
    edestruct msg2a_inv as (?&?&?); [done|done|]; simplify_eq.
    eexists. eauto 10.
  Qed.

  (* Key lemma *)
  Lemma OneValuePerBallot s a1 a2 bal v1 v2 :
    rtc PNext PInit s →
    VotedFor s a1 bal v1 → VotedFor s a2 bal v2 → v1 = v2.
  Proof.
    apply: (rtc_ind_r (λ s, _)); [done|].
    rewrite /VotedFor. move=> s1 s2 Hrtc Hnext IH.
    inversion Hnext; simplify_eq; simpl.
    - rewrite !elem_of_union !elem_of_singleton.
      move=> [? | ?] // [? | ?] //. auto.
    - rewrite !elem_of_union !elem_of_singleton.
      move=> [? | ?] // [? | ?] //. auto.
    - rewrite !elem_of_union !elem_of_singleton.
      move=> [? | ?] // [? | ?] //. auto.
    - rewrite !elem_of_union !elem_of_singleton.
      move=> [Hm1 | ?] [Hm2 | ?] //; simplify_eq; auto.
      + edestruct msg2b_inv as (?&?); [done|done|]. by eapply msg2a_agree.
      + edestruct msg2b_inv as (?&?); [done|done|]. by eapply msg2a_agree.
  Qed.

  Lemma SafeAt_notChosenAt s bal1 bal2 v1 v2 :
    rtc PNext PInit s →
    bal1 < bal2 → SafeAt s bal2 v2 → ¬ (ChosenAt s bal1 v1 ∧ v1 ≠ v2).
  Proof.
    intros Hrtc Hlt Hsafe [(Q1 & H1 & Hvote1) Hneq].
    edestruct (Hsafe bal1 Hlt) as (Q2 & H2 & Hvote2).
    destruct (quorum_choose _ _ H1 H2) as [a [HQ1 HQ2]%elem_of_intersection].
    specialize (Hvote1 _ HQ1).
    destruct (Hvote2 _ HQ2) as [|(?&?&?& Hnv2)].
    { eapply Hneq. by eapply OneValuePerBallot. }
    by eapply Hnv2.
  Qed.

  (* Key lemma *)
  Lemma ShowsSafety s Q bal val :
    rtc PNext PInit s →
    QuorumA Q → ShowsSafeAt s Q bal val → SafeAt s bal val.
  Proof.
    revert Q.
    induction (lt_wf bal) as [bal _ IH].
    intros Q Hrtc Hmaj [HQb HQbv].
    destruct HQbv as [Hempty | Hmax].
    - intros c Hc. exists Q. split; [done|]. intros a Ha.
      right. rewrite /CannotVoteAt /=.
      destruct (HQb a Ha) as (m & (Hm &?&?&?&_) & (mval &?)); simplify_eq.
      destruct mval as [b|].
      { exfalso. eapply (Hempty (msg1b a bal (Some b))).
        set_unfold. split_and!; eauto. }
      edestruct msg1b_inv as (?&?&?); [done|done|].
      eexists. split_and!; [done|lia|].
      by eapply msg1b_None_inv.
    - destruct Hmax as (m & ? & bal0 & ? & ((H1b0 & a0 &?&?&?) &?&?&?) & Hmm);
        simplify_eq.
      edestruct (msg1b_Some_inv_full s a0) as (Q0 & Hmaj0 & Hssa0 & Hlt0 & ? & H2b0 & H2a0);
        [done|done|].
      intros c Hc.
      destruct (decide (c < bal0)).
      { by eapply (IH bal0). }
      exists Q. split; [done|]. intros a Ha.
      destruct (HQb _ Ha) as (m & (H1b &?&?&?&_) & (mval &?)); simplify_eq.
      edestruct (msg1b_inv s a) as (?&?&?); [done|done|].
      destruct mval as [[bal' v]|]; last first.
      { right. eexists. split_and!; [done|lia|]. by eapply msg1b_None_inv. }
      edestruct (Hmm (msg1b a bal (Some (bal', v)))) as (a' & bal2 & v' &?&?); simplify_eq.
      { repeat split; eauto. }
      edestruct (msg1b_Some_inv_full s a') as (Q' & Hmaj' & Hssa' & Hlt' & Hdidn & H2b' & H2a');
          [done|done|].
      destruct (decide (c = bal0)); simplify_eq; last first.
      { right. eexists. split_and!; [done|lia|].
        eapply Hdidn. lia. }
      destruct (decide (bal2 = bal0)); simplify_eq.
      { assert (val = v') by by eapply msg2a_agree.
        simplify_eq. left. eauto. }
      right. eexists. split_and!; [done|lia|].
      eapply Hdidn. lia.
  Qed.

  Lemma SafeAt_2b_this s Q a bal val :
    rtc PNext PInit s →
    QuorumA Q →
    ShowsSafeAt s Q bal val →
    SafeAt (s <| maxBal ::= (λ mb, <[a := Some bal]> mb) |>
              <| maxVal ::= (λ mv, <[a := Some (bal, val)]> mv) |>
              <| msgs ::= (λ ms, ms ∪ {[msg2b a bal val]}) |>) bal val.
  Proof.
    intros Hrtc Hmaj Hssa c Hc.
    apply ShowsSafety in Hssa; [|done|done].
    destruct (Hssa c Hc) as (Q' & ? & Hvote).
    exists Q'. split; [done|]. intros a' Ha'.
    destruct (Hvote a' Ha') as [Hv | (b &?&?&?)].
    - left. by eapply VotedFor_send.
    - right. rewrite /CannotVoteAt /=.
      destruct (decide (a = a')); simplify_eq.
      + eexists. rewrite fn_lookup_insert.
        split_and!; [done|lia|].
        apply DidNotVoteAt_2b_neq; [lia|].
        by apply DidNotVoteAt_no_msg.
      + eexists. rewrite fn_lookup_insert_ne //.
        split_and!; [done|done|].
        apply DidNotVoteAt_2b_neq; [lia|].
        by apply DidNotVoteAt_no_msg.
  Qed.

  Lemma VotesSafe s a bal v :
    rtc PNext PInit s → VotedFor s a bal v → SafeAt s bal v.
  Proof.
    apply: (rtc_ind_r (λ s, _)); [done|].
    rewrite /VotedFor.
    intros s1 s2 Hrtc Hnext IH.
    inversion Hnext as [|a' ? bal0 ? ? H1a ? Hmv Hmb
                        |? ? ? Q Hn2a HQ Hssa
                        |a' ? ? ? ? H2a ? Hmb];
      simplify_eq=>/=; clear Hnext;
      rewrite !elem_of_union !elem_of_singleton.
    - intros [|]; [|done]. apply SafeAt_send_not2b; [|eauto].
      intros (?&?&?& [=]).
    - intros [|]; [|done]. apply SafeAt_send_not2b.
      { intros (?&?&?& [=]). }
      by apply SafeAt_maxBal; [|eauto].
    - intros [|]; [|done]. apply SafeAt_send_not2b; [|eauto].
      intros (?&?&?& [=]).
    - intros [Hm | [=]]; simplify_eq.
      + apply SafeAt_2b_other; eauto.
      + edestruct msg2a_inv as (Q&?&?); [done|done|].
        by eapply SafeAt_2b_this.
  Qed.

  Lemma ChosenAt_agree s bal1 bal2 v1 v2 :
    rtc PNext PInit s → ChosenAt s bal1 v1 → ChosenAt s bal2 v2 → v1 = v2.
  Proof.
    intros ? (Q1 & H1 & Hvote1) (Q2 & H2 & Hvote2).
    destruct (quorum_choose _ _ H1 H2) as [a [HQ1 HQ2]%elem_of_intersection].
    pose proof (Hvote1 _ HQ1) as Hv1.
    pose proof (Hvote2 _ HQ2) as Hv2.
    destruct (decide (bal1 = bal2)); subst.
    { by eapply OneValuePerBallot. }
    apply VotesSafe in Hv1, Hv2; [|done|done].
    destruct (decide (bal1 < bal2)).
    { destruct (decide (v1 = v2)); [done|].
      eapply (SafeAt_notChosenAt _ _ _ v1) in Hv2; [|done|done].
      exfalso. eapply Hv2. split; [|done]. exists Q1. eauto. }
    destruct (decide (v1 = v2)); [done|].
    eapply (SafeAt_notChosenAt _ bal2 _ v2) in Hv1; [|done|lia].
    exfalso. eapply Hv1. split; [|done]. exists Q2. eauto.
  Qed.

  (** * Correctness  *)
  Theorem paxos_correct s v1 v2 :
    rtc PNext PInit s → Chosen s v1 → Chosen s v2 → v1 = v2.
  Proof. intros ? [??] [??]. by eapply ChosenAt_agree. Qed.

End model_correctness.
