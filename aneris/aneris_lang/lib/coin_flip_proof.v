From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import lang tactics proofmode.
From aneris.aneris_lang Require Export coin_flip_code.

Section proof.
  Context `{!anerisG Mdl Σ}.

  Lemma coin_flip_spec ip :
    {{{ True }}} coin_flip #() @[ip] {{{ (b : bool), RET #b; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc l as "Hl". wp_let.
    pose proof (nroot .@ "rnd") as rndN.
    iMod (inv_alloc rndN _ (∃ (b : bool), l ↦[ip] #b)%I with "[Hl]") as "#Hinv";
      first by eauto.
    wp_apply aneris_wp_fork; iSplitL.
    - iModIntro. wp_seq. iInv rndN as (?) "?". wp_load.
      iSplitR "HΦ"; first by eauto. by iApply "HΦ".
    - iModIntro. wp_pures. iInv rndN as (?) "?". wp_store; eauto.
  Qed.

End proof.
