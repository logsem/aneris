From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From aneris Require Import lang lifting tactics proofmode notation.

Section code.

  Definition assert : ground_lang.val :=
    λ: "v", if: "v" #() then #() else #0 #0. (* #0 #0 is unsafe *)

End code.

Notation "'assert:' e" := (assert (λ: <>, e))%E (at level 99) : expr_scope.

Section library.
  Context `{dG : distG Σ}.

  Lemma wp_assert n E (Φ : val → iProp Σ) e :
    WP ⟨n;e⟩ @ E {{ v, ⌜v = 〈n;#true〉⌝ ∧ ▷ Φ 〈n;#()〉 }} -∗ WP ⟨n;assert: e⟩ @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /assert /=. wp_pures.
    wp_apply (wp_wand with "HΦ").
    iIntros (v) "[% H]"; subst. by wp_if.
  Qed.

End library.
