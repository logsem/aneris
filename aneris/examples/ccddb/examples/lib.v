From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Import lang network tactics proofmode.
From aneris.prelude Require Import misc.
From aneris.examples.ccddb Require Import spec spec_util.

Section helpers.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_events,
            !Maximals_Computing, !DB_resources Mdl Σ}.

  Definition repeat_read_until : val :=
    λ: "rd" "k" "v",
    (rec: "loop" <> :=
       if: ("rd" "k") = SOME "v"
       then #()
       else "loop" #()) #().

  Opaque ip_of_address.

  Lemma repeat_read_until_spec k s v i z rd :
    DB_addresses !! i = Some z →
    read_spec rd i z -∗
    {{{ Seen i s }}}
      repeat_read_until rd #k v @[ip_of_address z]
    {{{ s' e, RET #();
        ⌜s ⊆ s'⌝ ∗ Seen i s' ∗
        ⌜AE_val e = v⌝ ∗ ⌜e ∈ Maximals (restrict_key k s')⌝ ∗
        OwnMemSnapshot k {[erasure e]} ∗ ⌜e = Observe (restrict_key k s')⌝
    }}}.
  Proof.
    iIntros (DB_addr) "#Hrd".
    iIntros (Φ) "!# #Hs HΦ".
    rewrite /repeat_read_until. do 6 wp_pure _.
    iLöb as "IH" forall (Φ).
    wp_pures. wp_bind (rd _).
    wp_apply ("Hrd" with "[//] [$Hs //]").
    iIntros (w). iDestruct 1 as (s' ?) "(Hs' & [(-> & %) | H]) /=".
    { do 2 wp_pure _. by iApply "IH". }
    iDestruct "H" as (u e) "(-> & % & % & HQ)".
    wp_pure _. case_bool_decide; wp_pure _; [|by iApply "IH"].
    iApply "HΦ"; simplify_eq; auto.
  Qed.

End helpers.

Arguments repeat_read_until : simpl never.
