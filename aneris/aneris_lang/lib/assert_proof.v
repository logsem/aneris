From iris.proofmode Require Import tactics.
From stdpp Require Import binders.
From aneris.aneris_lang Require Import lang tactics proofmode.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
Import ast.


Section library.
  Context `{dG : anerisG Mdl Σ}.

  Lemma wp_assert ip E (Φ : val → iProp Σ) e :
    WP e @[ip] E {{ v, ⌜v = #true⌝ ∧ ▷ Φ #() }} -∗ WP assert: e @[ip] E {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /assert /=.
    wp_pures.
    wp_apply (aneris_wp_wand with "HΦ").
    iIntros (v) "[% H]"; subst. by wp_if.
  Qed.

End library.
