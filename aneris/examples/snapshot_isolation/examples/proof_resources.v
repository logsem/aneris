From aneris.aneris_lang Require Import proofmode.
From aneris.examples.snapshot_isolation.specs
     Require Import specs.
From iris.algebra Require Import excl.

Section resources.

Context `{!anerisG Mdl Σ, !KVSG Σ}.

  Definition token (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma token_exclusive (γ : gname) : token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

End resources.
