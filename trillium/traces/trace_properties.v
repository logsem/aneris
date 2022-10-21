From stdpp Require Export base prelude finite.
From Coq.ssr Require Import ssreflect.
From trillium.traces Require Import infinite_trace trace.

Import InfListNotations.

Section trace_prop.
  Context {A L : Type}.

  Implicit Types ψ : finite_trace A L → inflist (L * A) → Prop.
  Implicit Types f : finite_trace A L.
  Implicit Types inftr : inflist (L * A).

  Inductive eventually ψ : finite_trace A L → inflist (L * A) → Prop :=
  | eventually_now f inftr : ψ f inftr → eventually ψ f inftr
  | eventually_later f ℓ a inftr :
      eventually ψ (f :tr[ℓ]: a) inftr → eventually ψ f ((ℓ, a) :: inftr).

  CoInductive always ψ : finite_trace A L → inflist (L * A) → Prop :=
  | always_continued f inftr :
      ψ f inftr →
      (∀ ℓ a inftr', inftr = ((ℓ, a) :: inftr')%inflist → always ψ (f :tr[ℓ]: a) inftr') →
      always ψ f inftr.

  (* properties *)
  (* always is a comonad *)
  Lemma always_mono ψ ψ' f inftr :
    (∀ f' inftr', ψ f' inftr' → ψ' f' inftr') →
    always ψ f inftr →
    always ψ' f inftr.
  Proof.
    intros Hψs. revert f inftr.
    cofix IH; intros f inftr Hψ.
    inversion Hψ; simplify_eq.
    constructor; first by apply Hψs.
    intros ? a inftr' ->; auto.
  Qed.

  Lemma always_holds ψ f inftr : always ψ f inftr → ψ f inftr.
  Proof. destruct 1; done. Qed.

  Lemma always_idemp ψ f inftr : always ψ f inftr → always (always ψ) f inftr.
  Proof.
    revert f inftr; cofix IH; intros f inftr.
    inversion 1; simplify_eq.
    constructor; eauto.
  Qed.

  Lemma always_unroll ψ f ℓ a inftr : always ψ f ((ℓ, a) :: inftr) → always ψ (f :tr[ℓ]: a) inftr.
  Proof. inversion 1; auto. Qed.

  Lemma always_unroll_n ψ n f inftr :
    always ψ f inftr →
    always ψ (trace_append_list f (inflist_take n inftr)) (inflist_drop n inftr).
  Proof.
    revert f inftr; induction n as [|n IHn]; intros f inftr Hbase; first done.
    inversion Hbase; simplify_eq.
    destruct inftr; first done.
    destruct x; apply IHn; auto.
  Qed.

  Lemma always_take_drop ψ f inftr :
    always ψ f inftr ↔
    ∀ n, ψ (trace_append_list f (inflist_take n inftr)) (inflist_drop n inftr).
  Proof.
    split.
    - by intros Hal n; apply always_holds, always_unroll_n.
    - revert f inftr.
      cofix IH; intros f inftr.
      intros Hn.
      constructor; first by apply (Hn 0).
      intros ? ? ? ->.
      apply IH.
      intros n; apply (Hn (S n)).
  Qed.

  Lemma always_and ψ1 ψ2 f inftr :
    always ψ1 f inftr ∧ always ψ2 f inftr ↔
    always (λ f' inftr', ψ1 f' inftr' ∧ ψ2 f' inftr') f inftr.
  Proof. setoid_rewrite always_take_drop; firstorder. Qed.

  Lemma always_forall {B} (Ψ : B → finite_trace A L → inflist (L * A) → Prop) f inftr:
    (∀ b, always (Ψ b) f inftr) ↔ always (λ f' inftr', ∀ b, Ψ b f' inftr') f inftr.
  Proof. setoid_rewrite always_take_drop; firstorder. Qed.

  Lemma always_impl P (Ψ : finite_trace A L → inflist (L * A) → Prop) f inftr:
    (P → always Ψ f inftr) ↔ always (λ f' inftr', P → Ψ f' inftr') f inftr.
  Proof. setoid_rewrite always_take_drop; firstorder. Qed.

  (* eventually is a monad *)
  Lemma eventually_mono ψ ψ' f inftr :
    (∀ f' inftr', ψ f' inftr' → ψ' f' inftr') →
    eventually ψ f inftr →
    eventually ψ' f inftr.
  Proof. intros Hψs. induction 1; first by constructor; auto. constructor; done. Qed.

  Lemma holds_eventually ψ f inftr : ψ f inftr → eventually ψ f inftr.
  Proof. by constructor. Qed.

  Lemma eventually_idemp ψ f inftr : eventually (eventually ψ) f inftr → eventually ψ f inftr.
  Proof. induction 1; first done. constructor; done. Qed.


  Lemma eventually_take_drop ψ f inftr :
    eventually ψ f inftr ↔
    ∃ n, ψ (trace_append_list f (inflist_take n inftr)) (inflist_drop n inftr).
  Proof.
    split.
    - intros Hev.
      induction Hev as [|????? [n Hn]]; first by exists 0.
      exists (S n); done.
    - intros [n Hn].
      revert f inftr Hn.
      induction n as [|n IHn]; intros f inftr Hn; first by constructor.
      destruct inftr as [|[??]]; first by constructor.
      constructor 2; apply IHn; done.
  Qed.

  Lemma eventually_exists {B} (Ψ : B → finite_trace A L → inflist (L * A) → Prop) f inftr:
    (∃ b, eventually (Ψ b) f inftr) ↔ eventually (λ f' inftr', ∃ b, Ψ b f' inftr') f inftr.
  Proof. setoid_rewrite eventually_take_drop; firstorder. Qed.

  (* other properties *)

  Lemma always_eventually_idemp ψ f inftr :
    always (eventually ψ) f inftr → always (eventually (always (eventually ψ))) f inftr.
  Proof.
    intros Hae.
    apply always_idemp in Hae.
    eapply always_mono; last apply Hae.
    clear; intros f' inftr' Hae.
    apply holds_eventually; done.
  Qed.

  Lemma eventually_always_combine ψ1 ψ2 f inftr :
    eventually (always ψ1) f inftr →
    eventually (always ψ2) f inftr →
    eventually (λ f' inftr', always ψ1 f' inftr' ∧ always ψ2 f' inftr') f inftr.
  Proof.
    rewrite !eventually_take_drop.
    intros [n Hn] [m Hm].
    exists (n `max` m).
    split.
    - assert (n ≤ n `max` m) as [k ->]%Nat.le_sum by lia.
      rewrite inflist_take_add [n + k]Nat.add_comm inflist_drop_add
      -trace_append_list_assoc.
      apply always_unroll_n; done.
    - assert (m ≤ n `max` m) as [k ->]%Nat.le_sum by lia.
      rewrite inflist_take_add [m + k]Nat.add_comm inflist_drop_add
      -trace_append_list_assoc.
      apply always_unroll_n; done.
  Qed.

  Lemma eventually_and_always ψ1 ψ2 f inftr :
    eventually ψ1 f inftr →
    always ψ2 f inftr →
    eventually (λ f' inftr', ψ1 f' inftr' ∧ always ψ2 f' inftr') f inftr.
  Proof.
    intros [n Hn]%eventually_take_drop Hal.
    apply eventually_take_drop; exists n.
    split; first done.
    apply always_unroll_n; done.
  Qed.

  Lemma eventually_forall_combine `{!EqDecision B} `{!Finite B}
        (Ψ : B → finite_trace A L → inflist (L * A) → Prop) f inftr:
    (∀ b, eventually (always (Ψ b)) f inftr) →
    eventually (λ f' inftr', ∀ b, always (Ψ b) f' inftr') f inftr.
  Proof.
    intros Hfa.
    cut (eventually (λ f' inftr', ∀ b : B, b ∈ enum B → always (Ψ b) f' inftr') f inftr).
    { apply eventually_mono; clear; intros; auto using elem_of_enum. }
    induction (enum B) as [|b l IHl].
    { apply holds_eventually; intros ?; rewrite elem_of_nil; done. }
    assert (eventually (always (λ f' inftr', ∀ b : B, b ∈ l → Ψ b f' inftr')) f inftr) as IHl'.
    { eapply eventually_mono; last by apply IHl.
      simpl; intros f' inftr' Hfa'.
      rewrite -always_forall; intros b'.
      rewrite -always_impl; apply Hfa'. }
    clear IHl.
    eapply eventually_mono; last by apply eventually_always_combine; [apply (Hfa b)| apply IHl'].
    simpl; clear; intros f' inftr' [Hal1 Hal2].
    intros b' [->|Hb']%elem_of_cons; first done.
    revert Hb'. rewrite always_impl.
    revert b'. rewrite always_forall.
    done.
  Qed.

End trace_prop.

Section trace_prop.
  Context {A B L1 L2 : Type}.

  Implicit Types ψ : finite_trace A L1 → finite_trace B L2 → inflist (L1 * A) → inflist (L2 * B) → Prop.
  Implicit Types f : finite_trace A L1.
  Implicit Types g : finite_trace B L2.
  Implicit Types inftr : inflist (L1 * A).
  Implicit Types inftrb : inflist (L2 * B).

  Inductive eventually2 ψ : finite_trace A L1 → finite_trace B L2 → inflist (L1 * A) → inflist (L2 * B) → Prop :=
  | eventually2_now f g inftr inftrb :
      inflist_same_length inftr inftrb →
      ψ f g inftr inftrb →
      eventually2 ψ f g inftr inftrb
  | eventually2_later f ℓ1 ℓ2 a g b inftr inftrb :
      eventually2 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) inftr inftrb →
      eventually2 ψ f g ((ℓ1, a) :: inftr) ((ℓ2, b) :: inftrb).

  CoInductive always2 ψ : finite_trace A L1 → finite_trace B L2 → inflist (L1 * A) → inflist (L2 * B) → Prop :=
  | always2_continued f g inftr inftrb :
      ψ f g inftr inftrb →
      inflist_same_length inftr inftrb →
      (∀ a inftr' b inftrb' ℓ1 ℓ2,
          inftr = ((ℓ1, a) :: inftr')%inflist →
          inftrb = ((ℓ2, b) :: inftrb')%inflist →
          always2 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) inftr' inftrb') →
      always2 ψ f g inftr inftrb.

  (* properties *)
  (* always 2 is a comonad *)
  Lemma always2_mono ψ ψ' f g inftr inftrb :
    (∀ f' inftr' g' inftrb', ψ f' g' inftr' inftrb' → ψ' f' g' inftr' inftrb') →
    always2 ψ f g inftr inftrb →
    always2 ψ' f g inftr inftrb.
  Proof.
    intros Hψs. revert f g inftr inftrb.
    cofix IH; intros f g inftr inftrb Hψ.
    inversion Hψ; simplify_eq.
    constructor; [by apply Hψs|done|].
    intros a' inftr' b' inftrb' ?? -> ->; auto.
  Qed.

  Lemma always2_holds ψ f g inftr inftrb : always2 ψ f g inftr inftrb → ψ f g inftr inftrb.
  Proof. destruct 1; done. Qed.

  Lemma always2_idemp ψ f g inftr inftrb :
    always2 ψ f g inftr inftrb → always2 (always2 ψ) f g inftr inftrb.
  Proof.
    revert f g inftr inftrb; cofix IH; intros f g inftr inftrb.
    inversion 1; simplify_eq.
    constructor; eauto.
  Qed.

  Lemma always2_unroll ψ f a g b ℓ1 ℓ2 inftr inftrb :
    always2 ψ f g ((ℓ1, a) :: inftr) ((ℓ2, b) :: inftrb) → always2 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) inftr inftrb.
  Proof. inversion 1; auto. Qed.

  Lemma always2_unroll_n ψ n f g inftr inftrb :
    always2 ψ f g inftr inftrb →
    always2
      ψ
      (trace_append_list f (inflist_take n inftr))
      (trace_append_list g (inflist_take n inftrb))
      (inflist_drop n inftr)
      (inflist_drop n inftrb).
  Proof.
    revert f g inftr inftrb; induction n as [|n IHn]; intros f g inftr inftrb Hbase; first done.
    inversion Hbase; simplify_eq.
    destruct inftr as [|[??]]; destruct inftrb as [|[??]]; [done|done|done|].
    apply IHn; auto.
  Qed.

  Lemma always2_inflist_same_length ψ f g inftr inftrb :
    always2 ψ f g inftr inftrb → inflist_same_length inftr inftrb.
  Proof. by inversion 1. Qed.

  Lemma always2_and_inflist_same_length ψ f g inftr inftrb :
    always2 ψ f g inftr inftrb ↔
    always2 (λ f' g' inftr' inftrb',
             ψ f' g' inftr' inftrb' ∧ inflist_same_length inftr' inftrb') f g inftr inftrb.
  Proof.
    split; last by apply always2_mono; tauto.
    intros Hal.
    revert f g inftr inftrb Hal.
    cofix IH; intros f g inftr inftrb Hal.
    inversion Hal; simplify_eq.
    constructor; [done|done|].
    intros a' inftr' b' inftrb' ?? -> ->; auto.
  Qed.

  Lemma always2_take_drop ψ f g inftr inftrb :
    always2 ψ f g inftr inftrb ↔
    ∀ n, ψ (trace_append_list f (inflist_take n inftr))
           (trace_append_list g (inflist_take n inftrb))
           (inflist_drop n inftr)
           (inflist_drop n inftrb) ∧
         inflist_same_length inftr inftrb.
  Proof.
    split.
    - intros Hal n.
      split; last by eapply always2_inflist_same_length; eauto.
      by apply always2_holds, always2_unroll_n.
    - revert f g inftr inftrb.
      cofix IH; intros f g inftr inftrb.
      intros Hn.
      constructor; [by apply (Hn 0)|by apply (Hn 0)|].
      intros ? ? ? ? ? ? -> ->.
      apply IH.
      setoid_rewrite inflist_same_length_cons in Hn.
      intros n; apply (Hn (S n)).
  Qed.

  Lemma always2_and ψ1 ψ2 f g inftr inftrb :
    always2 ψ1 f g inftr inftrb ∧ always2 ψ2 f g inftr inftrb ↔
    always2
      (λ f' g' inftr' inftrb',ψ1 f' g' inftr' inftrb' ∧ ψ2 f' g' inftr' inftrb') f g inftr inftrb.
  Proof. rewrite !always2_take_drop; firstorder. Qed.

  Lemma always2_forall `{!Inhabited C}
        (Ψ : C → finite_trace A L1 → finite_trace B L2 → inflist (L1 * A) → inflist (L2 * B) → Prop) f g inftr inftrb :
    (∀ b, always2 (Ψ b) f g inftr inftrb) ↔
    always2 (λ f' g' inftr' inftrb', ∀ b, Ψ b f' g' inftr' inftrb') f g inftr inftrb.
  Proof. setoid_rewrite always2_take_drop; firstorder. Qed.

  Lemma always2_impl P ψ f g inftr inftrb :
    inflist_same_length inftr inftrb →
    (P → always2 ψ f g inftr inftrb) ↔
    always2 (λ f' g' inftr' inftrb', P → ψ f' g' inftr' inftrb') f g inftr inftrb.
  Proof. setoid_rewrite always2_take_drop; firstorder. Qed.

  (* eventually2 is a monad *)
  Lemma eventually2_mono ψ ψ' f g inftr inftrb :
    (∀ f' g' inftr' inftrb', ψ f' g' inftr' inftrb' → ψ' f' g' inftr' inftrb') →
    eventually2 ψ f g inftr inftrb →
    eventually2 ψ' f g inftr inftrb.
  Proof. intros Hψs. induction 1; first by constructor; auto. constructor; done. Qed.

  Lemma holds_eventually2 ψ f g inftr inftrb :
    inflist_same_length inftr inftrb → ψ f g inftr inftrb → eventually2 ψ f g inftr inftrb.
  Proof. by constructor. Qed.

  Lemma eventually2_idemp ψ f g inftr inftrb :
    eventually2 (eventually2 ψ) f g inftr inftrb → eventually2 ψ f g inftr inftrb.
  Proof. induction 1; first done. constructor; done. Qed.

  Lemma eventually2_inflist_same_length ψ f g inftr inftrb :
    eventually2 ψ f g inftr inftrb → inflist_same_length inftr inftrb.
  Proof.
    induction 1; first done.
    rewrite inflist_same_length_cons; done.
  Qed.

  Lemma eventually2_and_inflist_same_length ψ f g inftr inftrb :
    eventually2 ψ f g inftr inftrb ↔
    eventually2 (λ f' g' inftr' inftrb',
             ψ f' g' inftr' inftrb' ∧ inflist_same_length inftr' inftrb') f g inftr inftrb.
  Proof.
    split; last by apply eventually2_mono; tauto.
    intros Hev.
    induction Hev; first by constructor; auto.
    constructor 2; auto.
  Qed.

  Lemma eventually2_take_drop ψ f g inftr inftrb:
    eventually2 ψ f g inftr inftrb ↔
    ∃ n, ψ (trace_append_list f (inflist_take n inftr))
           (trace_append_list g (inflist_take n inftrb))
           (inflist_drop n inftr)
           (inflist_drop n inftrb) ∧
         inflist_same_length inftr inftrb.
  Proof.
    split.
    - intros Hev.
      induction Hev as [|????????? [n Hn]]; first by exists 0.
      setoid_rewrite inflist_same_length_cons.
      exists (S n); done.
    - intros [n Hn].
      revert f g inftr inftrb Hn.
      induction n as [|n IHn]; intros f g inftr inftrb [Hn1 Hn2]; first by constructor.
      destruct inftr as [|[??]]; destruct inftrb as [|[??]]; [by constructor|done|done|]; simpl in *.
      setoid_rewrite inflist_same_length_cons in Hn2.
      constructor 2; apply IHn; done.
  Qed.

  Lemma eventually2_exists
        {C} (Ψ : C → finite_trace A L1 → finite_trace B L2 → inflist (L1 * A) → inflist (L2 * B) → Prop)
        f g inftr inftrb :
    (∃ b, eventually2 (Ψ b) f g inftr inftrb) ↔
    eventually2 (λ f' g' inftr' inftrb', ∃ b, Ψ b f' g' inftr' inftrb') f g inftr inftrb.
  Proof. setoid_rewrite eventually2_take_drop; firstorder. Qed.

  (* other properties *)

  Lemma always2_eventually2_idemp ψ f g inftr inftrb :
    always2 (eventually2 ψ) f g inftr inftrb →
    always2 (eventually2 (always2 (eventually2 ψ))) f g inftr inftrb.
  Proof.
    intros Hae.
    apply always2_idemp in Hae.
    eapply always2_mono; last apply Hae.
    clear; intros f' g' inftr' inftrb' Hae.
    pose proof (always2_inflist_same_length _ _ _ _ _ Hae).
    apply holds_eventually2; done.
  Qed.

  Lemma eventually2_always2_combine ψ1 ψ2 f g inftr inftrb :
    eventually2 (always2 ψ1) f g inftr inftrb →
    eventually2 (always2 ψ2) f g inftr inftrb →
    eventually2 (λ f' g' inftr' inftrb',
                always2 ψ1 f' g' inftr' inftrb' ∧ always2 ψ2 f' g' inftr' inftrb') f g inftr inftrb.
  Proof.
    rewrite !eventually2_take_drop.
    intros [n [Hn1 Hn2]] [m [Hm1 Hm2]].
    exists (n `max` m).
    split; last done.
    split.
    - assert (n ≤ n `max` m) as [k ->]%Nat.le_sum by lia.
      rewrite !inflist_take_add ![n + k]Nat.add_comm !inflist_drop_add
      -!trace_append_list_assoc.
      apply always2_unroll_n; done.
    - assert (m ≤ n `max` m) as [k ->]%Nat.le_sum by lia.
      rewrite !inflist_take_add ![m + k]Nat.add_comm !inflist_drop_add
      -!trace_append_list_assoc.
      apply always2_unroll_n; done.
  Qed.

  Lemma eventually2_and_always2 ψ1 ψ2 f g inftr inftrb :
    eventually2 ψ1 f g inftr inftrb →
    always2 ψ2 f g inftr inftrb →
    eventually2 (λ f' g' inftr' inftrb',
                 ψ1 f' g' inftr' inftrb' ∧ always2 ψ2 f' g' inftr' inftrb') f g inftr inftrb.
  Proof.
    intros [n [Hn1 Hn2]]%eventually2_take_drop Hal.
    apply eventually2_take_drop; exists n.
    split; last done.
    split; first done.
    apply always2_unroll_n; done.
  Qed.

  Lemma eventually2_forall_combine `{!EqDecision C} `{!Finite C} `{!Inhabited C}
        (Ψ : C → finite_trace A L1 → finite_trace B L2 → inflist (L1 * A) → inflist (L2 * B) → Prop)
        f g inftr inftrb :
    (∀ c, eventually2 (always2 (Ψ c)) f g inftr inftrb) →
    eventually2 (λ f' g' inftr' inftrb', ∀ c, always2 (Ψ c) f' g' inftr' inftrb') f g inftr inftrb.
  Proof.
    intros Hfa.
    cut (eventually2
           (λ f' g' inftr' inftrb',
             ∀ c : C, c ∈ enum C → always2 (Ψ c) f' g' inftr' inftrb') f g inftr inftrb).
    { apply eventually2_mono; clear; intros; auto using elem_of_enum. }
    induction (enum C) as [|c l IHl].
    { apply holds_eventually2.
      - specialize (Hfa inhabitant) as Hfa'%eventually2_inflist_same_length; done.
      - intros ?; rewrite elem_of_nil; done. }
    assert (eventually2
              (always2 (λ f' g' inftr' inftrb',
                        ∀ c : C, c ∈ l → Ψ c f' g' inftr' inftrb')) f g inftr inftrb) as IHl'.
    { setoid_rewrite eventually2_and_inflist_same_length in IHl.
      eapply eventually2_mono; last by apply IHl.
      simpl; intros f' g' inftr' inftrb' [Hfa' Hsl].
      rewrite -always2_forall; intros c'.
      rewrite -always2_impl; first by apply Hfa'.
      done. }
    clear IHl.
    assert (eventually2
              (λ f' g' inftr' inftrb',
               (always2 (λ f'' g'' inftr'' inftrb'', Ψ c f'' g'' inftr'' inftrb''))
                 f' g' inftr' inftrb' ∧
               (always2
                  (λ f'' g'' inftr'' inftrb'', ∀ c' : C, c' ∈ l → Ψ c' f'' g'' inftr'' inftrb''))
                 f' g' inftr' inftrb')
              f g inftr inftrb) as IHl.
    { apply eventually2_always2_combine; last done. apply Hfa. }
    clear IHl'.
    eapply eventually2_mono; last apply IHl.
    simpl; intros f' g' inftr' inftrb' [Hal1 Hal2] c' [->|Hc']%elem_of_cons; first done.
    apply always2_inflist_same_length in Hal1.
    revert Hc'; rewrite always2_impl; last done.
    revert c'; rewrite always2_forall; done.
  Qed.

End trace_prop.

Section trace_prop.
  Context {A B C L1 L2 L3: Type}.

  Implicit Types ψ :
    finite_trace A L1 → finite_trace B L2 → finite_trace C L3 → inflist (L1 * A) → inflist (L2 * B) → inflist (L3 * C) → Prop.
  Implicit Types f : finite_trace A L1.
  Implicit Types g : finite_trace B L2.
  Implicit Types h : finite_trace C L3.
  Implicit Types inftr : inflist (L1 * A).
  Implicit Types inftrb : inflist (L2 * B).
  Implicit Types inftrc : inflist (L3 * C).

  Inductive eventually3 ψ :
    finite_trace A L1 → finite_trace B L2 → finite_trace C L3 → inflist (L1 * A) → inflist (L2 * B) → inflist (L3 * C) → Prop :=
  | eventually3_now f g h inftr inftrb inftrc :
      inflist_same_length inftr inftrb →
      inflist_same_length inftrb inftrc →
      ψ f g h inftr inftrb inftrc →
      eventually3 ψ f g h inftr inftrb inftrc
  | eventually3_later f a g b h c ℓ1 ℓ2 ℓ3 inftr inftrb inftrc :
      eventually3 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) (h :tr[ℓ3]: c) inftr inftrb inftrc →
      eventually3 ψ f g h ((ℓ1, a) :: inftr) ((ℓ2, b) :: inftrb) ((ℓ3, c) :: inftrc).

  CoInductive always3 ψ :
    finite_trace A L1 → finite_trace B L2 → finite_trace C L3 → inflist (L1 * A) → inflist (L2 * B) → inflist (L3 * C) → Prop :=
  | always3_continued f g h inftr inftrb inftrc :
      ψ f g h inftr inftrb inftrc →
      inflist_same_length inftr inftrb →
      inflist_same_length inftrb inftrc →
      (∀ a ℓ1 inftr' b ℓ2 inftrb' c ℓ3 inftrc',
          inftr = ((ℓ1, a) :: inftr')%inflist →
          inftrb = ((ℓ2, b) :: inftrb')%inflist →
          inftrc = ((ℓ3, c) :: inftrc')%inflist →
          always3 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) (h :tr[ℓ3]: c) inftr' inftrb' inftrc') →
      always3 ψ f g h inftr inftrb inftrc.

  (* properties *)
  (* always 3 is a comonad *)
  Lemma always3_mono ψ ψ' f g h inftr inftrb inftrc :
    (∀ f' g' h' inftr' inftrb' inftrc',
        ψ f' g' h' inftr' inftrb' inftrc' → ψ' f' g' h' inftr' inftrb' inftrc') →
    always3 ψ f g h inftr inftrb inftrc →
    always3 ψ' f g h inftr inftrb inftrc.
  Proof.
    intros Hψs. revert f g h inftr inftrb inftrc.
    cofix IH; intros f g h inftr inftrb inftrc Hψ.
    inversion Hψ; simplify_eq.
    constructor; [by apply Hψs|done|done|].
    intros ????????? -> -> ->; auto.
  Qed.

  Lemma always3_holds ψ f g h inftr inftrb inftrc :
    always3 ψ f g h inftr inftrb inftrc → ψ f g h inftr inftrb inftrc.
  Proof. destruct 1; done. Qed.

  Lemma always3_idemp ψ f g h inftr inftrb inftrc :
    always3 ψ f g h inftr inftrb inftrc → always3 (always3 ψ) f g h inftr inftrb inftrc.
  Proof.
    revert f g h inftr inftrb inftrc; cofix IH; intros f g h inftr inftrb inftrc.
    inversion 1; simplify_eq.
    constructor; eauto.
  Qed.

  Lemma always3_unroll ψ f a g b h c ℓ1 ℓ2 ℓ3 inftr inftrb inftrc :
    always3 ψ f g h ((ℓ1, a) :: inftr) ((ℓ2, b) :: inftrb) ((ℓ3, c) ::inftrc) →
    always3 ψ (f :tr[ℓ1]: a) (g :tr[ℓ2]: b) (h :tr[ℓ3]:c) inftr inftrb inftrc.
  Proof. inversion 1; eauto.  Qed.

  Lemma always3_unroll_n ψ n f g h inftr inftrb inftrc :
    always3 ψ f g h inftr inftrb inftrc →
    always3
      ψ
      (trace_append_list f (inflist_take n inftr))
      (trace_append_list g (inflist_take n inftrb))
      (trace_append_list h (inflist_take n inftrc))
      (inflist_drop n inftr)
      (inflist_drop n inftrb)
      (inflist_drop n inftrc).
  Proof.
    revert f g h inftr inftrb inftrc.
    induction n as [|n IHn]; intros f g h inftr inftrb inftrc Hbase; first done.
    inversion Hbase; simplify_eq.
    destruct inftr as [|[??]?]; destruct inftrb as [|[??]?]; destruct inftrc as [|[??]?];
      [done|done|done|done|done|done|done|].
    simpl. apply IHn; auto.
  Qed.

  Lemma always3_inflist_same_length ψ f g h inftr inftrb inftrc :
    always3 ψ f g h inftr inftrb inftrc →
    inflist_same_length inftr inftrb ∧ inflist_same_length inftrb inftrc.
  Proof. by inversion 1. Qed.

  Lemma always3_and_inflist_same_length ψ f g h inftr inftrb inftrc :
    always3 ψ f g h inftr inftrb inftrc ↔
    always3 (λ f' g' h' inftr' inftrb' inftrc',
             ψ f' g' h' inftr' inftrb' inftrc' ∧
             inflist_same_length inftr' inftrb' ∧
             inflist_same_length inftrb' inftrc') f g h inftr inftrb inftrc.
  Proof.
    split; last by apply always3_mono; tauto.
    intros Hal.
    revert f g h inftr inftrb inftrc Hal.
    cofix IH; intros f g h inftr inftrb inftrc Hal.
    inversion Hal; simplify_eq.
    constructor; [done|done|done|].
    intros ????????? -> -> ->; auto.
  Qed.

  Lemma always3_take_drop ψ f g h inftr inftrb inftrc :
    always3 ψ f g h inftr inftrb inftrc ↔
    ∀ n, ψ (trace_append_list f (inflist_take n inftr))
           (trace_append_list g (inflist_take n inftrb))
           (trace_append_list h (inflist_take n inftrc))
           (inflist_drop n inftr)
           (inflist_drop n inftrb)
           (inflist_drop n inftrc) ∧
         inflist_same_length inftr inftrb ∧
         inflist_same_length inftrb inftrc.
  Proof.
    split.
    - intros Hal n.
      split; last by eapply always3_inflist_same_length; eauto.
      by apply always3_holds, always3_unroll_n.
    - revert f g h inftr inftrb inftrc.
      cofix IH; intros f g h inftr inftrb inftrc.
      intros Hn.
      constructor; [by apply (Hn 0)|by apply (Hn 0)|by apply (Hn 0)|].
      intros ? ? ? ? ? ? ? ? ? -> -> ->.
      apply IH.
      setoid_rewrite inflist_same_length_cons in Hn.
      intros n; apply (Hn (S n)).
  Qed.

  Lemma always3_and ψ1 ψ2 f g h inftr inftrb inftrc :
    always3 ψ1 f g h inftr inftrb inftrc ∧ always3 ψ2 f g h inftr inftrb inftrc ↔
    always3
      (λ f' g' h' inftr' inftrb' inftrc',
       ψ1 f' g' h' inftr' inftrb' inftrc' ∧ ψ2 f' g' h' inftr' inftrb' inftrc')
      f g h inftr inftrb inftrc.
  Proof. rewrite !always3_take_drop; firstorder. Qed.

  Lemma always3_forall `{!Inhabited D}
        (Ψ : D → finite_trace A L1 → finite_trace B L2 →
             finite_trace C L3 → inflist (L1 * A) → inflist (L2 * B) → inflist (L3 * C) → Prop)
        f g h inftr inftrb inftrc :
    (∀ d, always3 (Ψ d) f g h inftr inftrb inftrc) ↔
    always3 (λ f' g' h' inftr' inftrb' inftrc', ∀ b, Ψ b f' g' h' inftr' inftrb' inftrc')
      f g h inftr inftrb inftrc.
  Proof. setoid_rewrite always3_take_drop; firstorder. Qed.

  Lemma always3_impl P ψ f g h inftr inftrb inftrc :
    inflist_same_length inftr inftrb →
    inflist_same_length inftrb inftrc →
    (P → always3 ψ f g h inftr inftrb inftrc) ↔
    always3 (λ f' g' h' inftr' inftrb' inftrc', P → ψ f' g' h' inftr' inftrb' inftrc')
      f g h inftr inftrb inftrc.
  Proof. setoid_rewrite always3_take_drop; firstorder. Qed.

  (* eventually3 is a monad *)
  Lemma eventually3_mono ψ ψ' f g h inftr inftrb inftrc :
    (∀ f' g' h' inftr' inftrb' inftrc',
        ψ f' g' h' inftr' inftrb' inftrc' → ψ' f' g' h' inftr' inftrb' inftrc') →
    eventually3 ψ f g h inftr inftrb inftrc →
    eventually3 ψ' f g h inftr inftrb inftrc.
  Proof. intros Hψs. induction 1; first by constructor; auto. constructor; done. Qed.

  Lemma holds_eventually3 ψ f g h inftr inftrb inftrc :
    inflist_same_length inftr inftrb →
    inflist_same_length inftrb inftrc →
    ψ f g h inftr inftrb inftrc →
    eventually3 ψ f g h inftr inftrb inftrc.
  Proof. by constructor. Qed.

  Lemma eventually3_idemp ψ f g h inftr inftrb inftrc :
    eventually3 (eventually3 ψ) f g h inftr inftrb inftrc →
    eventually3 ψ f g h inftr inftrb inftrc.
  Proof. induction 1; first done. constructor; done. Qed.

  Lemma eventually3_inflist_same_length ψ f g h inftr inftrb inftrc :
    eventually3 ψ f g h inftr inftrb inftrc →
    inflist_same_length inftr inftrb ∧ inflist_same_length inftrb inftrc.
  Proof.
    induction 1; first done.
    rewrite !inflist_same_length_cons; done.
  Qed.

  Lemma eventually3_and_inflist_same_length ψ f g h inftr inftrb inftrc :
    eventually3 ψ f g h inftr inftrb inftrc ↔
    eventually3 (λ f' g' h' inftr' inftrb' inftrc',
                 ψ f' g' h' inftr' inftrb' inftrc' ∧
                 inflist_same_length inftr' inftrb' ∧
                 inflist_same_length inftrb' inftrc') f g h inftr inftrb inftrc.
  Proof.
    split; last by apply eventually3_mono; tauto.
    intros Hev.
    induction Hev; first by constructor; auto.
    constructor 2; auto.
  Qed.

  Lemma eventually3_take_drop ψ f g h inftr inftrb inftrc :
    eventually3 ψ f g h inftr inftrb inftrc ↔
    ∃ n, ψ (trace_append_list f (inflist_take n inftr))
           (trace_append_list g (inflist_take n inftrb))
           (trace_append_list h (inflist_take n inftrc))
           (inflist_drop n inftr)
           (inflist_drop n inftrb)
           (inflist_drop n inftrc) ∧
         inflist_same_length inftr inftrb ∧
         inflist_same_length inftrb inftrc.
  Proof.
    split.
    - intros Hev.
      induction Hev as [|????????????? [n Hn]]; first by exists 0.
      setoid_rewrite inflist_same_length_cons.
      exists (S n); done.
    - intros [n Hn].
      revert f g h inftr inftrb inftrc Hn.
      induction n as [|n IHn]; intros f g h inftr inftrb inftrc [Hn1 [Hn2 Hn3]];
        first by constructor.
      destruct inftr as [|[??]?]; destruct inftrb as [|[??]?]; destruct inftrc as [|[??]?];
      [by constructor|done|done|done|done|done|done|]; simpl in *.
      setoid_rewrite inflist_same_length_cons in Hn2.
      setoid_rewrite inflist_same_length_cons in Hn3.
      constructor 2; apply IHn; done.
  Qed.

  Lemma eventually3_exists
        {D} (Ψ : D → finite_trace A L1 → finite_trace B L2 →
                 finite_trace C L3 → inflist (L1 * A) → inflist (L2 * B) → inflist (L3 * C) → Prop)
        f g h inftr inftrb inftrc :
    (∃ d, eventually3 (Ψ d) f g h inftr inftrb inftrc) ↔
    eventually3 (λ f' g' h' inftr' inftrb' inftrc', ∃ b, Ψ b f' g' h' inftr' inftrb' inftrc')
      f g h inftr inftrb inftrc.
  Proof. setoid_rewrite eventually3_take_drop; firstorder. Qed.

  (* other properties *)

  Lemma always3_eventually3_idemp ψ f g h inftr inftrb inftrc :
    always3 (eventually3 ψ) f g h inftr inftrb inftrc →
    always3 (eventually3 (always3 (eventually3 ψ))) f g h inftr inftrb inftrc.
  Proof.
    intros Hae.
    apply always3_idemp in Hae.
    eapply always3_mono; last apply Hae.
    clear; intros f' g' h' inftr' inftrb' inftrc' Hae.
    pose proof (always3_inflist_same_length _ _ _ _ _ _ _ Hae) as [? ?].
    apply holds_eventually3; done.
  Qed.

  Lemma eventually3_always3_combine ψ1 ψ2 f g h inftr inftrb inftrc :
    eventually3 (always3 ψ1) f g h inftr inftrb inftrc →
    eventually3 (always3 ψ2) f g h inftr inftrb inftrc →
    eventually3 (λ f' g' h' inftr' inftrb' inftrc',
                 always3 ψ1 f' g' h' inftr' inftrb' inftrc' ∧
                 always3 ψ2 f' g' h' inftr' inftrb' inftrc') f g h inftr inftrb inftrc.
  Proof.
    rewrite !eventually3_take_drop.
    intros [n [Hn1 [Hn2 Hn3]]] [m [Hm1 [Hm2 Hm3]]].
    exists (n `max` m).
    split; last done.
    split.
    - assert (n ≤ n `max` m) as [k ->]%Nat.le_sum by lia.
      rewrite !inflist_take_add ![n + k]Nat.add_comm !inflist_drop_add
      -!trace_append_list_assoc.
      apply always3_unroll_n; done.
    - assert (m ≤ n `max` m) as [k ->]%Nat.le_sum by lia.
      rewrite !inflist_take_add ![m + k]Nat.add_comm !inflist_drop_add
      -!trace_append_list_assoc.
      apply always3_unroll_n; done.
  Qed.

  Lemma eventually3_and_always3 ψ1 ψ2 f g h inftr inftrb inftrc :
    eventually3 ψ1 f g h inftr inftrb inftrc →
    always3 ψ2 f g h inftr inftrb inftrc →
    eventually3 (λ f' g' h' inftr' inftrb' inftrc',
                 ψ1 f' g' h' inftr' inftrb' inftrc' ∧ always3 ψ2 f' g' h' inftr' inftrb' inftrc')
                f g h inftr inftrb inftrc.
  Proof.
    intros [n [Hn1 [Hn2 Hn3]]]%eventually3_take_drop Hal.
    apply eventually3_take_drop; exists n.
    split; last done.
    split; first done.
    apply always3_unroll_n; done.
  Qed.

  Lemma eventually3_forall_combine `{!EqDecision D} `{!Finite D} `{!Inhabited D}
        (Ψ : D → finite_trace A L1 → finite_trace B L2 →
                 finite_trace C L3 → inflist (L1 * A) → inflist (L2 * B) → inflist (L3 * C) → Prop)
        f g h inftr inftrb inftrc :
    (∀ c, eventually3 (always3 (Ψ c)) f g h inftr inftrb inftrc) →
    eventually3 (λ f' g' h' inftr' inftrb' inftrc',
                 ∀ d, always3 (Ψ d) f' g' h' inftr' inftrb' inftrc') f g h inftr inftrb inftrc.
  Proof.
    intros Hfa.
    cut (eventually3
           (λ f' g' h' inftr' inftrb' inftrc',
            ∀ d : D, d ∈ enum D → always3 (Ψ d) f' g' h' inftr' inftrb' inftrc')
           f g h inftr inftrb inftrc).
    { apply eventually3_mono; clear; intros; auto using elem_of_enum. }
    induction (enum D) as [|d l IHl].
    { apply holds_eventually3.
      - specialize (Hfa inhabitant) as [? ?]%eventually3_inflist_same_length; done.
      - specialize (Hfa inhabitant) as [? ?]%eventually3_inflist_same_length; done.
      - intros ?; rewrite elem_of_nil; done. }
    assert (eventually3
              (always3 (λ f' g' h' inftr' inftrb' inftrc',
                        ∀ d : D, d ∈ l → Ψ d f' g' h' inftr' inftrb' inftrc'))
              f g h inftr inftrb inftrc) as IHl'.
    { setoid_rewrite eventually3_and_inflist_same_length in IHl.
      eapply eventually3_mono; last by apply IHl.
      simpl; intros f' g' h' inftr' inftrb' inftrc' [Hfa' [Hsl1 Hsl2]].
      rewrite -always3_forall; intros c'.
      rewrite -always3_impl; [by apply Hfa'|done|done]. }
    clear IHl.
    assert (eventually3
              (λ f' g' h' inftr' inftrb' inftrc',
               (always3 (λ f'' g'' h'' inftr'' inftrb'' inftrc'',
                         Ψ d f'' g'' h'' inftr'' inftrb'' inftrc''))
                 f' g' h' inftr' inftrb' inftrc' ∧
               (always3
                  (λ f'' g'' h'' inftr'' inftrb'' inftrc'',
                   ∀ d' : D, d' ∈ l → Ψ d' f'' g'' h'' inftr'' inftrb'' inftrc''))
                 f' g' h' inftr' inftrb' inftrc')
              f g h inftr inftrb inftrc) as IHl.
    { apply eventually3_always3_combine; last done. apply Hfa. }
    clear IHl'.
    eapply eventually3_mono; last apply IHl.
    simpl; intros f' g' h' inftr' inftrb' inftrc' [Hal1 Hal2] c' [->|Hc']%elem_of_cons; first done.
    apply always3_inflist_same_length in Hal1 as [? ?].
    revert Hc'; rewrite always3_impl; [|done|done].
    revert c'; rewrite always3_forall; done.
  Qed.

End trace_prop.
