From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import proofmode.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.prelude Require Import time.
From aneris.examples.rcb Require Import spec.

From aneris.examples.rcb.examples.broadcast_1_2 Require Import prog proof_resources.

Section Deliver_1_2_spec.
  Context `{!anerisG Mdl Σ, inG Σ (exclR unitO), !RCB_events, !RCB_resources Mdl Σ}.

  Lemma deliver_1_2_spec deliver γS1 γS2 :
    GlobalInv -∗
    deliver_spec deliver 1 z1 -∗
    {{{ inv Nsys (inv_sys γS1 γS2) ∗ OwnLocal 1 ∅ }}}
      deliver_1_2 deliver @["0.0.0.1"]
    {{{ RET #();
        ∃ (e1 e2 : le), OwnLocal 1 {[ e1; e2 ]} ∗
                        ⌜ LE_payload e1 = #1 ⌝ ∗ ⌜ LE_payload e2 = #2 ⌝ ∗
                        ⌜ vector_clock_lt (LE_vc e1) (LE_vc e2) ⌝ }}}.
  Proof.
    iIntros "#HGlobinv #Hdel".
    iIntros "!#" (Φ) "[#Inv HLoc] HΦ".
    wp_lam.

    (* First delivering *)
    wp_apply (deliver_spec_implies_simplified_wait_deliver_spec with "Hdel").
    iIntros (wd) "Hwd".
    wp_apply ("Hwd" with "[//] HLoc"); clear wd.
    iIntros (e1 u) "(%Hu_e1 & HLoc & _)".
    rewrite left_id_L.

    (* Satisfying the assertion. *)
    pose proof Hu_e1 as Hu'.
    destruct Hu' as (payload1 & vc1 & o & -> & Hpayload1 & _).
    rewrite erasure_payload in Hpayload1. subst.
    repeat (wp_proj || wp_let).
    wp_apply wp_assert.
    (* In order to satisfy the assertion, we need to prove the payload of e1. To do that, we
       must open the "OwnGlobal", to obtain properties about the (erasure of) e1. *)
    iInv "Inv" as ">HInv" "Hclose".
    iDestruct "HInv" as (h) "[HGlob Hh]".
    iMod (Local_included_Global' e1 with "HGlobinv HGlob HLoc")
      as "(%Hh_e1 & HGlob & HLoc)";
      [ solve_ndisj | set_solver | ]. (* erasure e1 is included in the global events set h *)
    iDestruct (User_Snapshot with "HGlob") as "[HGlob HSnap]".
    (* Causality: (the erasure of) e1 is a minimal event in the global events set h. *)
    iMod (Causality' with "HGlobinv HLoc HSnap") as "[HLoc %caus]"; first solve_ndisj.
    iAssert (⌜ LE_payload e1 = #1 ⌝)%I as "%Hpayload1".
    { iDestruct "Hh" as "[-> | [Hone | Htwo]]".
      - exfalso. set_solver. (* The global events h set cannot be empty. *)
      - iDestruct "Hone" as (e1') "(-> & %He1' & _)".
        apply elem_of_singleton in Hh_e1; subst.
        rewrite erasure_payload in He1'. done.
      - iDestruct "Htwo" as (e1' e2') "(-> & _ & _ & %He1' & _ & %Hvc_e1_e2)".
        (* (The erasure of) e1 is the minimal event e1' of h. *)
        assert (erasure e1 = e1').
        { assert (e1'_or_e2' : erasure e1 = e1' \/ erasure e1 = e2') by set_solver.
          destruct e1'_or_e2' as [ | <-]; first done.
          specialize (caus e1' e1). rewrite erasure_vc in Hvc_e1_e2.
          set_solver.
        }
        subst. rewrite erasure_payload in He1'. done.
    }
    rewrite Hpayload1. wp_pures.
    (* As we did not modify any data, we can close the invariant. *)
    iMod ("Hclose" with "[HGlob Hh]") as "_". { iModIntro. iExists h. iFrame. }
    iModIntro. iSplit; first done. iModIntro. wp_seq.

    (* Second delivering: *)
    wp_apply (deliver_spec_implies_simplified_wait_deliver_spec with "Hdel").
    iIntros (wd) "Hwd".
    wp_apply ("Hwd" with "[//] HLoc").
    iIntros (e2 v) "(%Hv_e2 & HLoc & %e1_not_e2 & _ & _)".

    (* Satisfying the assertion. *)
    apply not_elem_of_singleton in e1_not_e2.
    pose proof Hv_e2 as Hv'.
    destruct Hv' as (payload2 & vc2 & ? & -> & Hpayload2 & _).
    rewrite erasure_payload in Hpayload2; subst.
    repeat (wp_let || wp_proj).
    wp_apply wp_assert.
    (* We again need to open the invariant. *)
    iInv "Inv" as ">HInv" "Hclose".
    iDestruct "HInv" as (h') "[HGlob Hh']".
    (* (The erasure of) e1 is contained in the global events set h'. *)
    iMod (Local_included_Global' e1 with "HGlobinv HGlob HLoc")
      as "(%Hh'_e1 & HGlob & HLoc)";
      [ solve_ndisj | set_solver | ].
    (* (The erasure of) e2 is contained in the global events set h'. *)
    iMod (Local_included_Global' e2 with "HGlobinv HGlob HLoc")
      as "(%Hh'_e2 & HGlob & HLoc)";
      [ solve_ndisj | set_solver | ].
    iMod (OwnLocal_erasure_injectivity' with "HGlobinv HLoc") as "[Hloc %inj]"; first solve_ndisj.
    (* The erasures of e1 and e2 are different. *)
    assert (erasure e1 ≠ erasure e2). { intro. apply e1_not_e2, inj; set_solver. }
    iAssert (⌜ LE_payload e2 = #2 ⌝ ∗ ⌜ vector_clock_lt (LE_vc e1) (LE_vc e2) ⌝)%I
      as "[%Hpayload2 %Hvc]".
    { iDestruct "Hh'" as "[-> | [Hone | Htwo]]".
      - exfalso. set_solver. (* The global events set h' cannot be empty. *)
      - iDestruct "Hone" as (e2') "[-> _]".
        exfalso. set_solver. (* The global events set h' cannot contain only one element. *)
      - iDestruct "Htwo" as (e1' e2') "(-> & _ & _ & %Hpayload1' & %Hpayload2' & %Hvc)".
        assert (erasure e1 = e1') as <-.
        { assert (erasure e1 = e1' \/ erasure e1 = e2') as e1'_or_e2' by set_solver.
          destruct e1'_or_e2' as [ | He1_e2']; first done.
          exfalso. rewrite <-erasure_payload in Hpayload1. congruence.
        }
        assert (erasure e2 = e2') as <- by set_solver.
        rewrite erasure_payload in Hpayload2'. rewrite! erasure_vc in Hvc. auto.
    }
    rewrite Hpayload2. wp_pures.
    (* Again, we can close the invariant. *)
    iMod ("Hclose" with "[HGlob Hh']") as "_". { iModIntro. iExists h'. iFrame. }
    iModIntro. iSplit; first done.

    (* Concluding. *)
    iModIntro. iApply "HΦ".
    iExists e1, e2. auto.
  Qed.
End Deliver_1_2_spec.
