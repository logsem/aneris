From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang Require Import proofmode.
From aneris.prelude Require Import time.
From aneris.examples.rcb Require Import spec.
From aneris.examples.rcb.examples.broadcast_1_2 Require Import prog proof_resources.

Section Broadcast_1_2_spec.
  Context `{!anerisG Mdl Σ, inG Σ (exclR unitO), !RCB_events, !RCB_resources Mdl Σ}.

  (* The specification of the broadcast program. *)
  Lemma broadcast_1_2_spec broadcast γS1 γS2 :
    GlobalInv -∗
    broadcast_spec broadcast 0 z0 -∗
    {{{ inv Nsys (inv_sys γS1 γS2) ∗ OwnLocal 0 ∅ ∗ token γS1 ∗ token γS2 }}}
      (broadcast_1_2 broadcast) @["0.0.0.0"]
    {{{ w, RET w;
        ∃ (e1 e2 : le), ⌜ is_le w e2 ⌝ ∗ OwnLocal 0 {[ e1; e2 ]} ∗
                        ⌜ LE_payload e1 = #1 ⌝ ∗ ⌜ LE_payload e2 = #2 ⌝ ∗
                        ⌜ vector_clock_lt (LE_vc e1) (LE_vc e2) ⌝ }}}.
  Proof.
    iIntros "#HGlobinv #Hbroadcast".
    iIntros (Φ) "!# (#Inv & Hloc & Ht1 & Ht2) HΦ".
    wp_lam.

    (* First broadcast *)
    wp_apply ("Hbroadcast" $! (SerVal #1)); first done.
    iInv "Inv" as ">HInv" "Hclose_inv".
    iDestruct "HInv" as (h) "[HGlob [-> | Hnot_zero]]"; last first.
    { iExFalso.
      iDestruct "Hnot_zero" as "[(% & _ & _ & Ht1') | (% & % & _ & Ht1' & _)]";
      iApply (exclusive_token with "Ht1 Ht1'").
    }
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hclose_other".
    iExists ∅, ∅. iFrame.
    iIntros "!>" (u e1) "(%Hu & _ & _ & %He1 & _ & _ & _ & HGlob & HLoc)".
    iMod "Hclose_other" as "_".
    rewrite !left_id_L.
    iMod ("Hclose_inv" with "[HGlob Ht1]") as "_".
    { iModIntro.
      iExists {[ erasure e1 ]}; iFrame.
      iRight; iLeft. iExists (erasure e1). rewrite erasure_payload. auto with iFrame.
    }
    iModIntro. wp_seq.

    (* Second broadcast *)
    iApply ("Hbroadcast" $! (SerVal #2)); first done.
    iInv "Inv" as ">HInv" "Hclose_inv".
    iDestruct "HInv" as (h) "[HGlob [-> | [Hone | Htwo]]]".
    - iMod (Local_included_Global e1 with "HGlobinv HGlob HLoc") as "%absurd";
        [solve_ndisj | set_solver | set_solver].
    - iDestruct "Hone" as (e1') "(-> & %He1' & Ht1)".
      iMod (Local_included_Global' e1 with "HGlobinv HGlob HLoc")
        as "(%e1_e1' & HGlob & HLoc)";
        [solve_ndisj | set_solver | ].
      apply elem_of_singleton in e1_e1'; subst.
      iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Hclose_other".
      iExists {[ erasure e1 ]}, {[ e1 ]}; iFrame.
      iIntros "!>" (v e2) "(%Hv & %He1_e2 & _ & %He2 & _ & _ & %Hmax & HGlob & HLoc)".
      iMod (OwnLocal_local_ext' with "HGlobinv HLoc") as "[HLoc %ext]"; first solve_ndisj.
      apply compute_maximum_correct in Hmax; last assumption.
      assert (vc_e1_e2 : vector_clock_lt (LE_vc e1) (LE_vc e2)).
      { apply Hmax; set_solver. }
      iMod "Hclose_other" as "_".
      iMod ("Hclose_inv" with "[HGlob Ht1 Ht2]") as "_".
      { iModIntro.
        iExists {[ erasure e1; erasure e2 ]}. iFrame.
        iRight; iRight.
        iExists (erasure e1), (erasure e2).
        rewrite !erasure_payload. rewrite !erasure_vc.
        auto with iFrame.
      }
      iModIntro. iApply "HΦ".
      iExists e1, e2. auto.
    - iExFalso.
      iDestruct "Htwo" as (? ?) "(_ & _ & Ht2' & _)".
      iApply (exclusive_token with "Ht2 Ht2'").
  Qed.
End Broadcast_1_2_spec.
