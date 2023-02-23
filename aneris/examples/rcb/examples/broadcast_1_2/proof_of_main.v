From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.rcb Require Import spec.
From aneris.examples.rcb.util Require Import list_proof_alt.
From aneris.examples.rcb.examples.broadcast_1_2 Require Import
  prog proof_broadcasting_node proof_delivering_node proof_resources.

Section main_spec.
  Context `{!anerisG Mdl Σ, inG Σ (exclR unitO), !RCB_init_function, !RCB_init}.

  Definition ips : gset string := {[ "0.0.0.0" ; "0.0.0.1"]}.

  Theorem main_spec :
     ⊢ |={⊤}=> ∃ (_ : RCB_resources Mdl Σ),
    ([∗ list] i ↦ z ∈ RCB_addresses, z ⤇ RCB_socket_proto i) -∗
    z0 ⤳ (∅, ∅) -∗ z1 ⤳ (∅, ∅) -∗
    ([∗ set] ip ∈ ips, free_ip ip) -∗
    WP main @["system"] {{ v, True }}.
  Proof.
    iMod (RCB_init_setup ⊤ with "[//]") as (RCBRS) "(#HGlobinv & Hitks & HGlob & #Hinit)".
    iModIntro. iExists RCBRS.
    iIntros "#Hsis Hmsg_z0 Hmsg_z1 Hips".
    iDestruct "Hitks" as "(Hitk0 & Hitk1 & _)".
    iMod (own_alloc (Excl ())) as (γS1) "Hstk1"; first done.
    iMod (own_alloc (Excl ())) as (γS2) "Hstk2"; first done.
    iMod (inv_alloc Nsys _ (inv_sys γS1 γS2) with "[HGlob]") as "#Hinv_sys".
    { iModIntro. iExists ∅. auto with iFrame. }
    iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "(Hz0 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "(Hz1 & _)";
      first set_solver.

    unfold main.
    wp_apply (aneris_wp_start with "[- $Hz0]").
    iSplitR "Hitk0 Hstk1 Hstk2 Hmsg_z0"; last first.
    { iIntros "!> Hfree".
      wp_apply ("Hinit" $! 0%nat z0 with "[] [] [$]");
        [ iPureIntro; by apply is_list_inject | done | ].
      iIntros (deliver broadcast) "(HLoc & _ & Hbroadcast)".
      wp_pures.
      iApply (broadcast_1_2_spec with "[$] [$] [$HLoc $Hstk1 $Hstk2 $Hinv_sys] []").
      auto.
    }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start with "[- $Hz1]").
    iSplitR; last first.
    { iIntros "!> Hfree".
      wp_apply ("Hinit" $! 1%nat z1 with "[] [] [$]");
        [ iPureIntro; by apply is_list_inject | done | ].
      iIntros (deliver broadcast) "(HLoc & Hdeliver & _)".
     wp_pures.
     iApply (deliver_1_2_spec with "[$] [$] [$]").
     auto.
    }
   done.
  Qed.
End main_spec.
