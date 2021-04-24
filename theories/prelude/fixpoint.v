From Coq.Unicode Require Import Utf8.
From Coq.ssr Require Import ssreflect.

Definition monotone {A} (Ψ : (A → Prop) → (A → Prop)) :=
  ∀ (P Q : A → Prop), (∀ x, P x → Q x) → ∀ x, Ψ P x → Ψ Q x.

Definition GFX {A} (Ψ : (A → Prop) → (A → Prop)) : A → Prop :=
  λ x, ∃ P, P x ∧ (∀ x, P x → Ψ P x).

Lemma GFX_post_fixpoint {A} (Ψ : (A → Prop) → (A → Prop)) :
  monotone Ψ → ∀ x, GFX Ψ x → Ψ (GFX Ψ) x.
Proof.
  intros Hmono x (P & HP & HΨP).
  eapply Hmono; [|by apply HΨP].
  intros; exists P; split; auto.
Qed.

Lemma GFX_fixpoint {A} (Ψ : (A → Prop) → (A → Prop)) :
  monotone Ψ → ∀ x, Ψ (GFX Ψ) x ↔ GFX Ψ x.
Proof.
  intros Hmono x; split.
  - intros HΨ.
    exists (Ψ (GFX Ψ)); split; first done.
    intros ? ?; eapply Hmono; last by eauto.
    apply GFX_post_fixpoint; done.
  - apply GFX_post_fixpoint; done.
Qed.
