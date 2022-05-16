From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import
     lang network tactics proofmode lifting adequacy.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.ccddb.spec Require Import spec.
From aneris.examples.ccddb Require Import spec_util.
From aneris.examples.ccddb.examples Require Import lib.
From aneris.examples.ccddb.examples.message_passing Require Import prog.


Class mpG Σ := MPG { mp_tokG :> inG Σ (exclR unitO) }.
Definition mpΣ : gFunctors := #[GFunctor (exclR unitO)].

Instance subG_mpΣ {Σ} : subG mpΣ Σ → mpG Σ.
Proof. solve_inG. Qed.

Section Resources.
  Context `{!anerisG Mdl Σ, !DB_time, !DB_events, !DB_resources Mdl Σ,
            !Maximals_Computing, !mpG Σ}.

  Definition token (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma token_exclusive (γ : gname) : token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Definition Ny := nroot.@"y".
  Definition Nx := nroot.@"x".

  Definition inv_x (γ : gname) (a : we) : iProp Σ :=
    (∃ h, "x" ↦ᵤ h ∗ ⌜Maximum h = Some a⌝ ∗ ⌜WE_val a = #37⌝) ∨ token γ.

  Definition inv_y (γ : gname) : iProp Σ :=
    ∃ h, "y" ↦ᵤ h ∗ ∀ a, (⌜a ∈ h ∧ WE_val a = (# 1)⌝) →
                         (∃ a', ⌜a' <ₜ a⌝ ∗ inv Nx (inv_x γ a')).

End Resources.
