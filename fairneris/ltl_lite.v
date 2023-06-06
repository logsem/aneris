From stdpp Require Import option.
From Paco Require Import paco1 paco2 pacotac.
From trillium.fairness Require Export inftraces.

Declare Scope trace_scope.
Delimit Scope trace_scope with trace.
Bind Scope trace_scope with trace.

Definition ltl_pred S L := trace S L → Prop.

Section ltl_constructors.
  Context {S L : Type}.

  Notation ltl_pred := (ltl_pred S L).

  (* Primitive operators *)
  Definition trace_now P : ltl_pred := λ tr, pred_at tr 0 P.
  Definition trace_not P : ltl_pred := λ tr, ¬ P tr.
  Definition trace_or P Q : ltl_pred := λ tr, P tr ∨ Q tr.
  (* Definition trace_next (P : trace S L → Prop) (tr : trace S L) : Prop := *)
  (*   ∀ tr', after 1 tr  = Some tr' → P tr'.  *)
  Definition trace_next P : ltl_pred :=
    λ tr, ∃ tr', after 1 tr = Some tr' ∧ P tr'.
  Inductive trace_until P Q : ltl_pred :=
  | trace_until_here tr : Q tr -> trace_until P Q tr
  | trace_until_next s l tr : P (s -[l]-> tr) → trace_until P Q tr → trace_until P Q (s -[l]-> tr).

  (* Definition trace_until P Q : ltl_pred := *)
  (*   λ tr, ∃ n, (∃ tr', after n tr = Some tr' ∧ Q tr') ∧ *)
  (*              ∀ m, m < n → ∃ tr', after m tr = Some tr' ∧ P tr'. *)

  (* Definition trace_always P : ltl_pred := *)
  (*   λ tr, ∀ n, ∃ tr', after n tr = Some tr' ∧ P tr'. *)
  (* Definition trace_eventually P : ltl_pred := *)
  (*   λ tr, ∃ n tr', after n tr = Some tr' ∧ P tr'. *)
  (* Should maybe be redefined to use ∀ tr' in second conjunct *)

  (* Derived operators *)
  Definition trace_and P Q := (trace_not (trace_or (trace_not P) (trace_not Q))).
  Definition trace_implies P Q := (trace_or (trace_not P) Q).
  Definition trace_biimplies P Q :=
    (trace_and (trace_implies P Q) (trace_implies Q P)).
  Definition trace_true := (trace_now (λ _ _, True)).
  Definition trace_false := (trace_now (λ _ _,False)).
  Definition trace_eventually P := (trace_until trace_true P).
  Definition trace_always P := (trace_not $ trace_eventually (trace_not P)).
  Definition trace_weak_until (P Q : trace S L → Prop) : ltl_pred :=
    trace_or (trace_until P Q) (trace_always P).

  (* Custom constructors *)
  Definition trace_always_eventually_implies
             (P Q : trace S L → Prop) : ltl_pred :=
    trace_always (trace_implies P (trace_eventually Q)).

  Definition trace_always_eventually_implies_now
             (P Q : S → option L → Prop) : ltl_pred :=
    trace_always_eventually_implies (trace_now P) (trace_now Q).

  Lemma trace_eventually_ind (P P0 : trace S L → Prop) :
    (∀ tr : trace S L, P tr → P0 tr) →
    (∀ (s : S) (l : L) (tr : trace S L),
         trace_eventually P tr → P0 tr → P0 (s -[ l ]-> tr)) →
    ∀ t : trace S L, trace_eventually P t → P0 t.
  Proof.
    intros ? IH ??.
    eapply (trace_until_ind trace_true); [done|by intros; apply IH|done].
  Qed.

End ltl_constructors.

Arguments trace_eventually_ind : clear implicits.

Notation "○ P" := (trace_next P) (at level 20, right associativity) : trace_scope.
Notation "□ P" := (trace_always P) (at level 20, right associativity) : trace_scope.
Notation "◊ P" := (trace_eventually P) (at level 20, right associativity) : trace_scope.
Notation "↓ P" := (trace_now P) (at level 20, right associativity) : trace_scope.
Notation "P → Q" := (trace_implies P Q)
                      (at level 99, Q at level 200,
                         format "'[' P  →  '/' '[' Q ']' ']'") : trace_scope.

Section ltl_lemmas.
  Context {S L : Type}.

  Lemma trace_not_not (tr:trace S L) (P : trace S L → Prop) :
    ¬ P tr ↔ trace_not P tr.
  Proof. done. Qed.

  Lemma after_is_Some_le (tr : trace S L) n m :
    m ≤ n → is_Some $ after n tr → is_Some $ after m tr.
  Proof.
    revert tr m.
    induction n; intros tr m Hle.
    { intros. assert (m = 0) as -> by lia. done. }
    intros.
    destruct m; [done|].
    simpl in *.
    destruct tr; [done|].
    apply IHn. lia. done.
  Qed.

  Lemma trace_eventually_until (P : trace S L → Prop) (tr : trace S L) :
    (◊P) tr →
    trace_until (trace_not P) (P) tr.
  Proof.
    assert (∀ tr, P tr ∨ ¬ P tr) as Hdec by by intros; apply ExcludedMiddle.
    induction 1; [by constructor|].
    specialize (Hdec (s -[l]-> tr)) as [H1|H2].
    - by apply trace_until_here.
    - by apply trace_until_next.
  Qed.

  Lemma trace_eventually_cons (P : trace S L → Prop) s l (tr : trace S L) :
    (◊ P) tr → (◊ P) (s -[l]-> tr).
  Proof. intros. by constructor 2. Qed.

  Lemma trace_always_cons (P : trace S L → Prop) s l (tr : trace S L) :
    (□ P) (s -[l]-> tr) → (□ P) tr.
  Proof.
    rewrite /trace_always.
    intros Htr Htr'. apply Htr. clear Htr.
    by apply trace_eventually_cons.
  Qed.

  (* Lemma trace_always_now_cons (P : S → option L → Prop) s l (tr : trace S L) : *)
  (*   (□↓P) (s -[l]-> tr) → P s (Some l). *)
  (* Proof. Admitted. *)

  Definition trace_suffix_of (tr1 tr2 : trace S L) : Prop :=
    ∃ n, after n tr2 = Some tr1.

  Lemma trace_suffix_of_refl (tr : trace S L) :
    trace_suffix_of tr tr.
  Proof. by exists 0. Qed.

  Lemma trace_eventually_intro P (tr : trace S L) :
    P tr → (◊ P) tr.
  Proof. by constructor 1. Qed.

  Lemma trace_eventually_mono_strong (P Q : trace S L → Prop) tr :
    (∀ tr', trace_suffix_of tr' tr → P tr' → Q tr') →
    (◊P) tr → (◊Q) tr.
  Proof.
    intros HPQ.
    induction 1.
    { apply HPQ, trace_eventually_intro in H. done. apply trace_suffix_of_refl. }
    constructor 2; [done|].
    apply IHtrace_until.
    intros tr' Hsuffix HP.
    apply HPQ; [|done].
    destruct Hsuffix as [n Heq].
    exists (Datatypes.S n). done.
  Qed.

  Lemma trace_eventually_mono (P Q : trace S L → Prop) tr :
    (∀ tr, P tr → Q tr) → (◊P) tr → (◊Q) tr.
  Proof.
    intros. eapply trace_eventually_mono_strong; [|done]. intros. by apply H.
  Qed.

  Lemma trace_implies_implies (P Q : trace S L → Prop) tr :
    trace_implies P Q tr ↔ (P tr → Q tr).
  Proof.
    split.
    - by intros [|].
    - intros HPQ.
      assert (P tr ∨ ¬ P tr) as [HP|HP] by apply ExcludedMiddle.
      + by right; apply HPQ.
      + by left.
  Qed.

  Lemma trace_always_mono (P Q : trace S L → Prop) tr :
    (∀ tr, trace_implies P Q tr) → (□P) tr → (□Q) tr.
  Proof.
    intros HPQ HP HQ. apply HP. eapply trace_eventually_mono; [|done].
    clear HP HQ. intros tr' HP HQ. apply HP.
    specialize (HPQ tr'). rewrite trace_implies_implies in HPQ. by apply HPQ.
  Qed.

  Lemma trace_always_mono_strong (P Q : trace S L → Prop) tr :
    (∀ tr', trace_suffix_of tr' tr → trace_implies P Q tr') → (□P) tr → (□Q) tr.
  Proof.
    intros HPQ HP HQ. apply HP. eapply trace_eventually_mono_strong; [|done].
    clear HP HQ. intros tr' Htr' HP HQ. apply HP.
    specialize (HPQ tr'). rewrite trace_implies_implies in HPQ. by apply HPQ.
  Qed.

  Lemma after_is_Some_lt (tr : trace S L) n m :
    m < n → is_Some $ after n tr → is_Some $ after m tr.
  Proof.
    revert tr m.
    induction n; intros tr m Hle.
    { intros. assert (m = 0) as -> by lia. done. }
    intros.
    destruct m; [done|].
    simpl in *.
    destruct tr; [done|].
    apply IHn. lia. done.
  Qed.

  (* TODO: Improve this proof *)
  Lemma trace_alwaysI (P : trace S L → Prop) tr :
    (□P) tr ↔ (∀ tr', trace_suffix_of tr' tr → (□ P) tr').
  Proof. Admitted.
  (*   split. *)
  (*   - rewrite /trace_always.  *)
  (*     intros Halways tr' [n Hafter] HP. apply Halways. *)
  (*     destruct HP as [m [HP HP']]. *)
  (*     destruct HP as [tr'' [Htr'' Hnot]]. *)
  (*     exists (n + m). *)
  (*     split. *)
  (*     + exists tr''. rewrite after_sum'. rewrite Hafter. done. *)
  (*     + intros m' Hlt. *)
  (*       assert (after (n+m) tr = Some tr''). *)
  (*       { rewrite after_sum'. rewrite Hafter. done. }  *)
  (*       assert (is_Some $ after m' tr) as [tr''' Htr''']. *)
  (*       { by eapply after_is_Some_lt. } *)
  (*       exists tr'''. split; [done|]. *)
  (*       by destruct tr'''. *)
  (*   - intros Halways. eapply (Halways). apply trace_suffix_of_refl. *)
  (* Qed. *)

  Lemma trace_always_idemp P (tr : trace S L) :
    (□ P) tr → (□ □ P) tr.
  Proof.
    intros Htr Htr'. induction Htr'.
    { apply H. done. }
    apply IHHtr'. apply trace_always_cons in Htr. done.
  Qed.

  Lemma trace_always_suffix_of (P : trace S L → Prop) tr1 tr2 :
    trace_suffix_of tr2 tr1 → (□P) tr1 → (□P) tr2.
  Proof. rewrite (trace_alwaysI _ tr1). intros Hsuffix HP. by eapply HP. Qed.

  Lemma trace_always_universal (P : trace S L → Prop) (tr : trace S L) :
    (∀ tr, P tr) → (□P) tr.
  Proof.
    intros ? H. induction H using trace_eventually_ind; [|done].
    simplify_eq. specialize (H0 tr). done.
  Qed.

  Lemma trace_not_idemp (P : trace S L → Prop) (tr : trace S L) :
    trace_not (trace_not P) tr ↔ P tr.
  Proof. rewrite /trace_not. split; [apply NNP_P|apply P_NNP]. Qed.

  (* TODO: Replace existing lemma with this *)
  Lemma not_exists_forall_not_alt {A} (P : A → Prop) x : ¬ (∃ x, P x) → ¬ P x.
  Proof. intros Hnex HP; apply Hnex; eauto. Qed.

  Lemma trace_always_elim (P : trace S L → Prop) (tr : trace S L) :
    (□P) tr → P tr.
  Proof.
    intros Htr.
    assert (P tr ∨ ¬ P tr) as [|HP] by apply ExcludedMiddle; [done|].
    rewrite /trace_always in Htr.
    assert (trace_not (trace_not P) tr).
    { intros Htr'. apply Htr. apply trace_eventually_intro. done. }
    done.
  Qed.

  (* TODO: This is a bit of a weird statement *)
  Lemma trace_always_implies (P Q : trace S L → Prop) tr :
    (□(P → Q)) tr → (□P) tr → (□ Q) tr.
  Proof.
    intros HPQ HP.
    eapply trace_always_mono_strong; [|done].
    intros tr' Hsuffix.
    apply trace_always_elim.
    by eapply trace_always_suffix_of.
  Qed.

  Lemma trace_always_eventually_always_implies (P Q : trace S L → Prop) tr :
    trace_always_eventually_implies P Q tr → (□P) tr → (◊Q) tr.
  Proof.
    intros HPQ HP.
    eapply trace_always_implies in HP; [|done].
    by apply trace_always_elim.
  Qed.

  Lemma trace_always_eventually_always_mono (P1 P2 Q1 Q2 : trace S L → Prop) tr :
    (∀ tr, trace_implies P2 P1 tr) → (∀ tr, trace_implies Q1 Q2 tr) →
    trace_always_eventually_implies P1 Q1 tr → trace_always_eventually_implies P2 Q2 tr.
  Proof.
    setoid_rewrite trace_implies_implies.
    intros HP HQ Htr.
    eapply trace_always_mono; [|done].
    intros Htr'.
    apply trace_implies_implies.
    rewrite !trace_implies_implies.
    intros HPQ HP2.
    eapply trace_eventually_mono; [apply HQ|by apply HPQ; apply HP].
  Qed.

  Lemma trace_implies_refl (P : trace S L → Prop) tr :
    trace_implies P P tr.
  Proof. by apply trace_implies_implies. Qed.

  (* This seems a bit too specific *)

  Definition trfirst_label (tr: trace S L) : option L :=
    match tr with
    | ⟨_⟩ => None
    | _ -[ℓ]-> _ => Some ℓ
    end.

  (* This seems a bit too specific *)
  Lemma trace_now_mono_strong (P Q : S → option L → Prop) tr :
    (∀ s l, trfirst tr = s → trfirst_label tr = l → P s l → Q s l) →
    (↓P) tr → (↓Q) tr.
  Proof.
    destruct tr as [s|s l tr].
    - rewrite /trace_now /pred_at /=. intros HPQ Htr. by apply HPQ.
    - rewrite /trace_now /pred_at /=. intros HPQ Htr. by apply HPQ.
  Qed.

  Lemma trace_now_mono (P Q : S → option L → Prop) tr :
    (∀ s l, P s l → Q s l) → (↓P) tr → (↓Q) tr.
  Proof. intros. eapply trace_now_mono_strong; [|done]. by eauto. Qed.

  Lemma trace_andI (P Q : trace S L → Prop) (tr : trace S L) :
    trace_and P Q tr ↔ P tr ∧ Q tr.
  Proof. Admitted.

  Lemma trace_not_eventually_always_not (P : trace S L → Prop) (tr : trace S L) :
    trace_not (◊ P) tr ↔ (□ (trace_not P)) tr.
  Proof. Admitted.
  
  Lemma trace_eventually_not_not_always (P : trace S L → Prop) (tr : trace S L) :
    (◊ trace_not P) tr ↔ (trace_not (□ P)) tr.
  Proof. Admitted.

  Lemma trace_always_and P Q (tr : trace S L) :
    ((□ P) tr ∧ (□ Q) tr) ↔ (□ trace_and P Q) tr.
  Proof.
    split.
    - intros [HP HQ] HPQ. induction HPQ.
      { apply H. apply trace_andI. apply trace_always_elim in HP, HQ. done. }
      by apply IHHPQ; eapply trace_always_cons.
    - intros HPQ.
      assert ((□ P) tr ∨ ¬ (□ P) tr) as [|HP] by apply ExcludedMiddle; last first.
      { apply NNP_P in HP. induction HP using trace_eventually_ind.
        { apply trace_always_elim in HPQ. apply trace_andI in HPQ as [HP HQ].
          done. }
        apply trace_always_cons in HPQ. apply IHHP in HPQ.
        destruct HPQ as [HP' HQ].
        apply trace_eventually_not_not_always in HP. done. }
      assert ((□ Q) tr ∨ ¬ (□ Q) tr) as [|HQ] by apply ExcludedMiddle; last first.
      { apply NNP_P in HQ. induction HQ using trace_eventually_ind.
        { apply trace_always_elim in HPQ. apply trace_andI in HPQ as [HP HQ].
          done. }
        apply trace_always_cons in HPQ.
        apply trace_always_cons in H.
        apply IHHQ in HPQ; [|done].
        destruct HPQ as [HP HQ'].
        apply trace_eventually_not_not_always in HQ. done. }
      done.
  Qed.

  Lemma trace_or_l (P Q : trace S L → Prop) (tr : trace S L) :
    P tr → trace_or P Q tr.
  Proof. intros HP. by left. Qed.

  Lemma trace_or_r (P Q : trace S L → Prop) (tr : trace S L) :
    Q tr → trace_or P Q tr.
  Proof. intros HP. by right. Qed.

  Lemma trace_weak_until_always P Q (tr : trace S L) :
    (□P) tr → trace_weak_until P Q tr.
  Proof. intros HP. by apply trace_or_r. Qed.


  Lemma trace_eventually_next (P : trace S L → Prop) (tr : trace S L) :
    (◊ ○ P) tr → (◊ P) tr.
  Proof.
    (* destruct 1 as [n [HP HP']]. *)
    (* destruct HP as [tr' [HP1 HP2]]. *)
    (* destruct tr. *)
    (* - admit. *)
    (* - simpl in *. *)
    (*   destruct n; simpl in *. *)
    (*   + simplify_eq. exists 0.  split. *)
    (*   + exists tr'. simpl in *. done. *)
  Admitted.

  Lemma trace_trueI (tr : trace S L) :
    trace_true tr.
  Proof. destruct tr; done. Qed.

  Lemma trace_eventually_suffix_of (P : trace S L → Prop) tr1 tr2 :
    trace_suffix_of tr1 tr2 → (◊P) tr1 → (◊P) tr2.
  Proof. Admitted.
  (*   intros [n Hsuffix] [m [[tr' [Hafter HP]] Htrue]]. *)
  (*   exists (n + m). *)
  (*   rewrite after_sum'. rewrite Hsuffix Hafter. *)
  (*   split. *)
  (*   - exists tr'. done. *)
  (*   - intros m' Hm. *)
  (*     assert (after (n + m) tr2 = Some tr'). *)
  (*     { rewrite after_sum'. rewrite Hsuffix Hafter. done. } *)
  (*     assert (is_Some (after m' tr2)) as [tr'' Htr']. *)
  (*     { by eapply after_is_Some_lt. } *)
  (*     exists tr''. split; [done| apply trace_trueI]. *)
  (* Qed. *)

  Lemma trace_eventually_thing_strong (P Q : trace S L → Prop) (tr : trace S L) :
    (∀ tr', trace_suffix_of tr' tr → P tr' → (◊ Q) tr') → (◊ P) tr → (◊ Q) tr.
  Proof. Admitted.
  (*   intros HPQ HP. *)
  (*   destruct HP as [n [[tr' [Hafter HP]] Htrue]]. *)
  (*   apply HPQ in HP; [|by exists n]. *)
  (*   eapply trace_eventually_suffix_of; [|done]. *)
  (*   by exists n. *)
  (* Qed. *)

  Lemma trace_always_eventually P (tr : trace S L) :
    (□ P) tr → (◊ P) tr.
  Proof. Admitted.

  Lemma trace_not_now P (tr : trace S L) :
    trace_not (↓ P) tr ↔ (↓ (λ s l, ¬ P s l)) tr.
  Proof. Admitted.

  Lemma trace_eventually_now P (tr : trace S L) :
    (↓ P) tr → (◊ ↓ P) tr.
  Proof. Admitted.

  Lemma trace_now_exists {A} (P : A → S → option L → Prop) (tr : trace S L) :
    (↓ (λ s l, ∃ (x:A), P x s l)) tr → ∃ (x:A), (↓ P x) tr.
  Proof. rewrite /trace_now /pred_at. intros H. by destruct tr. Qed.

  Lemma trace_nextI (P : trace S L → Prop) s l (tr : trace S L) :
    P tr → (○ P) (s -[l]-> tr).
  Proof. intros ?. exists tr. simpl in *. by simplify_eq. Qed.

  Lemma trace_always_implies_always (P Q : trace S L → Prop) (tr : trace S L) :
    (∀ tr, (□P) tr → Q tr) → ((□P) tr → (□ Q) tr).
  Proof.
    intros HPQ HP%trace_always_idemp. eapply trace_always_mono; [|done].
    intros ?. apply trace_implies_implies, HPQ.
  Qed.

  Lemma trace_eventually_or (P Q : trace S L → Prop) tr :
    (◊ (P \1/ Q)) tr →
    (◊ P) tr ∨ (◊ Q) tr.
  Proof.
    intros Hdisj.
    induction Hdisj.
    { inversion H; [left; by constructor|right; by constructor]. }
    inversion IHHdisj.
    - left. by constructor 2.
    - right. by constructor 2.
  Qed.

  Lemma trace_now_or (P Q : S → option L → Prop) tr :
    (↓ (P \2/ Q)) tr →
    (↓ P) tr ∨ (↓ Q) tr.
  Proof. rewrite /trace_now /pred_at. by destruct tr=>/=. Qed.

  Lemma trace_and_now P Q (tr : trace S L) :
    trace_and (↓P) (↓Q) tr ↔ (↓ (λ s l, P s l ∧ Q s l)) tr.
  Proof. Admitted.

  Lemma trace_now_split P Q (tr : trace S L) :
    (↓ P) tr → (↓ Q) tr → (↓ (λ s l, P s l ∧ Q s l)) tr.
  Proof. Admitted.

  Lemma trace_eventually_cons_2 P s l (tr : trace S L) :
    (◊ P) tr → (◊ P) (s -[l]-> tr).
  Proof. intros. constructor 2; done. Qed.

  Lemma trace_next_cons (P : trace S L → Prop) s l tr : 
    (○ P) (s -[l]-> tr) → P tr.
  Proof. Admitted.

End ltl_lemmas.
