From iris.base_logic.lib Require Export invariants.
From aneris.aneris_lang Require Import lang tactics proofmode.

Definition coin_flip : val :=
  λ: <>, let: "l" := ref #true in Fork ("l" <- #false);; !"l".

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
    - iModIntro. iInv rndN as (?) "?". wp_store; eauto.
  Qed.

End proof.
