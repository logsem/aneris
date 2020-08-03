From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang tactics proofmode.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.

Section code.

  Definition assert : ground_lang.val :=
    λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)

End code.

Notation "'assert:' e" := (assert (λ: <>, e))%E (at level 99) : expr_scope.

Section library.
  Context `{dG : distG Σ}.

  Lemma wp_assert ip E (Φ : val → iProp Σ) e :
    WP e @[ip] E {{ v, ⌜v = #true⌝ ∧ ▷ Φ #() }} -∗ WP assert: e @[ip] E {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /assert /=.
    wp_pures.
    wp_apply (aneris_wp_wand with "HΦ").
    iIntros (v) "[% H]"; subst. by wp_if.
  Qed.

End library.
