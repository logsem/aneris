From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication.examples Require Import inj_elim_code.

Section with_Σ.
  Context `{anerisG Σ Mdl}.

  Lemma inj_get_left_spec ip E v :
    ⊢ WP inj_get_left (InjLV v) @[ip] E {{ w, ⌜v = w⌝ }}.
  Proof. wp_lam. by wp_pures. Qed.

  Lemma inj_get_right_spec ip E v :
    ⊢ WP inj_get_right (InjRV v) @[ip] E {{ w, ⌜v = w⌝ }}.
  Proof. wp_lam. by wp_pures. Qed.

End with_Σ.
