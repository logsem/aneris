From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import inject.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency.read_committed.specs
  Require Import resources specs.
From aneris.examples.transactional_consistency Require Import user_params aux_defs.
From aneris.examples.transactional_consistency.read_committed.examples.dirty_read
      Require Import dirty_read_code.
From aneris.examples.transactional_consistency.read_committed.implication_proof
      Require Import si_implies_rc.
Import ser_inj.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_proof.
From aneris.examples.transactional_consistency.snapshot_isolation Require Import snapshot_isolation_code.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.
From aneris.examples.transactional_consistency.snapshot_isolation.examples Require Import proof_resources.
From iris.algebra Require Import excl.


Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client_2_addr := SocketAddressInet "0.0.0.2" 80.
Definition client_3_addr := SocketAddressInet "0.0.0.3" 80.

Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"; "y"; "a"; "b"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Definition client_inv_name := nroot.@"clinv".

Section proof_of_code.

  Context `{!anerisG Mdl Σ, !RC_resources Mdl Σ, !KVSG Σ}.

  Definition client_inv_def (γF1 γF2 : gname) : iProp Σ :=
    ∃ V_x V_y V_a V_b, "x" ↦ₖ V_x ∗ "y" ↦ₖ V_y ∗ "a" ↦ₖ V_a ∗ "b" ↦ₖ V_b ∗
    (((⌜V_x = ∅⌝ ∨ (⌜V_x = {[(#1)]}⌝ ∗ token γF1)) ∗ (⌜V_y = ∅⌝ ∨ (⌜V_y = {[(#1)]}⌝ ∗ token γF2)) ∗ ⌜V_a = ∅⌝ ∗ ⌜V_b = ∅⌝) ∨
      (token γF1 ∗ token γF2 ∗ (⌜V_a = ∅⌝ ∨ ⌜V_b = ∅⌝))).

  Definition client_inv (γF1 γF2 : gname) : iProp Σ :=
    inv client_inv_name (client_inv_def γF1 γF2).

  Lemma transaction1_spec γF1 γF2 :
    ∀ (cst : val) sa,
    RC_client_toolbox -∗
    client_inv γF1 γF2 -∗
    GlobalInv -∗
    {{{ token γF1 ∗ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #inv #HGinv %Φ !> (Htok & CanStart & #HiC) HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">(%Vx & %Vy & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
      [([->|(_ & Htok')] & Hdisj & -> & ->)|(Htok' & _)])" "Hclose";
      try iDestruct (token_exclusive with "Htok Htok'") as "[]".
    iModIntro.
    iExists {[ "x" := ∅; "y" := Vy; "a" := ∅; "b" := ∅ ]}.
    iFrame.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hkx Hky Hka Hkb"; first iFrame.
    iNext. iIntros "(Hcstate & (Hkx & Hky & Hka & Hkb & _) 
      & Hcx & Hcy & Hca & Hcb & _)".
    iMod ("Hclose" with "[Hkx Hky Hka Hkb Hdisj]") as "_".
    { 
      iNext. iExists _, _, _, _. iFrame.
      iLeft. iSplitR. by iLeft.
      iSplitL. iFrame. done. 
    }
    iModIntro. wp_pures.
    wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _.
    iFrame.
    iNext.
    iIntros "Hcx".
    iModIntro.
    wp_pures.
    wp_apply ("Hrd" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][][$]"); 
      first solve_ndisj; first set_solver.
    iInv "inv" as ">(%Vx & %Vy' & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
      [([->|(_ & Htok')] & Hdisj & -> & ->)|(Htok' & _)])" "Hclose";
      try iDestruct (token_exclusive with "Htok Htok'") as "[]".
    iModIntro.
    iExists _, _.
    iFrame.
    iNext.
    iIntros  (wo) "(Hcy & Hky & Hdisj')".
    iDestruct "Hdisj" as "[->| (-> & Htok')]".
    - iMod ("Hclose" with "[Hkx Hky Hka Hkb]") as "_".
      { 
        iNext. iExists _, _, _, _. iFrame.
        iLeft. iSplitR. by iLeft.
        iSplitL. by iLeft. done. 
      }
      iModIntro.
      wp_pures.
      iDestruct "Hdisj'" as "[Hdisj | (%Hfalse & _)]"; last done.
      iDestruct "Hdisj" as "(_ & [%Hfalse|->])"; first set_solver.
      wp_pures.
      rewrite /util_code.commitU.
      wp_pures.
      wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
      iInv "inv" as ">(%Vx & %Vy' & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
        [([->|(_ & Htok')] & Hdisj & -> & ->)|(Htok' & _)])" "Hclose";
        try iDestruct (token_exclusive with "Htok Htok'") as "[]".
      iModIntro.
      iExists (dom {["x" := ∅; "y" := Vy; "a" := ∅; "b" := ∅]}),
                ({["x" := Some (#1); "y" := None; "a" := None; "b" := None]}), 
                ({["x" := ∅; "y" := Vy'; "a" := ∅; "b" := ∅]}).
      iFrame.
      iSplitR "HΦ Hclose Hdisj Htok".
      * iSplitR. iPureIntro. set_solver. 
        iSplitR. iPureIntro. set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite !big_sepM_empty. iFrame.
      * iNext.
        iIntros (b) "(Hstate & Hdisj')".
        iMod ("Hclose" with "[Hdisj Hdisj' Htok]") as "_".
        { 
          iNext. iDestruct "Hdisj'" as "[(_ & Hkey)|(_ & Hkey)]".
          - rewrite !big_sepM2_insert; try set_solver.
            simpl. iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
            iExists _, _, _, _.
            iFrame. iLeft.
            iSplitL "Htok".
            iRight. iFrame.
            iPureIntro. set_solver.
            iSplitL. iFrame. done.
          - rewrite !big_sepM_insert; try set_solver.
            iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
            iExists _, _, _, _.
            iFrame. iLeft.
            iSplitL "Htok".
            by iLeft.
            iSplitL. iFrame. done. 
        }
        iModIntro.
        wp_pures.
        by iApply "HΦ".
    - iDestruct "Hdisj'" as "[Hdisj | (%Hfalse & _)]"; last done.
      iDestruct "Hdisj" as "(_ & [(%v & -> & %Hin)|->])".
      + iMod (Seen_creation with "[$HGinv] [$Hky]") as "(Hky & Hseen)"; first solve_ndisj.
        iMod ("Hclose" with "[Hkx Hky Hka Hkb Htok']") as "_".
        { 
          iNext. iExists _, _, _, _. iFrame.
          iLeft. iSplitR. by iLeft.
          iSplitL. iRight. by iFrame. done. 
        }
        iModIntro.
        wp_pures.
        assert (v = (#1)) as ->; first set_solver.
        wp_pures.
        wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
        iModIntro.
        iExists _.
        iFrame.
        iNext.
        iIntros "Hca".
        iModIntro.
        wp_pures.
        rewrite /util_code.commitU.
        wp_pures.
        wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
        iInv "inv" as ">(%Vx & %Vy' & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
          [([->|(_ & Htok')] & Hdisj & -> & ->)|(Htok' & _)])" "Hclose";
          try iDestruct (token_exclusive with "Htok Htok'") as "[]".
        iDestruct "Hdisj" as "[-> |(-> & Htok')]".
        {
          iMod (Seen_valid with "[$HGinv] [$Hky $Hseen]") as "(Hky & %Hfalse)"; first solve_ndisj.
          set_solver.
        }
        iModIntro.
        iExists (dom {["x" := ∅; "y" := Vy; "a" := ∅; "b" := ∅]}),
                 ({["x" := Some (#1); "y" := None; "a" := Some (#1); "b" := None]}), 
                 ({["x" := ∅; "y" := {[#1]}; "a" := ∅; "b" := ∅]}).
        iFrame.
        iSplitR "HΦ Hclose Htok Htok'".
        * iSplitR. iPureIntro. set_solver. 
          iSplitR. iPureIntro. set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        * iNext.
          iIntros (b) "(Hstate & Hdisj')".
          iMod ("Hclose" with "[Htok' Hdisj' Htok]") as "_".
          { 
            iNext. iDestruct "Hdisj'" as "[(_ & Hkey)|(_ & Hkey)]".
            - rewrite !big_sepM2_insert; try set_solver.
              simpl. iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
              iExists _, _, _, _.
              iFrame. iRight.
              iFrame. by iRight.
            - rewrite !big_sepM_insert; try set_solver.
              iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
              iExists _, _, _, _.
              iFrame. iRight.
              iFrame. by iLeft.
          }
          iModIntro.
          wp_pures.
          by iApply "HΦ".
      + iMod ("Hclose" with "[Hkx Hky Hka Hkb Htok']") as "_".
        { 
          iNext. iExists _, _, _, _. iFrame.
          iLeft. iSplitR. by iLeft.
          iSplitL. iRight. by iFrame. done. 
        }
        iModIntro.
        wp_pures.
        rewrite /util_code.commitU.
        wp_pures.
        wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
        iInv "inv" as ">(%Vx & %Vy' & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
          [([->|(_ & Htok')] & Hdisj & -> & ->)|(Htok' & _)])" "Hclose";
          try iDestruct (token_exclusive with "Htok Htok'") as "[]".
        iModIntro.
        iExists (dom {["x" := ∅; "y" := Vy; "a" := ∅; "b" := ∅]}),
                 ({["x" := Some (#1); "y" := None; "a" := None; "b" := None]}), 
                 ({["x" := ∅; "y" := Vy'; "a" := ∅; "b" := ∅]}).
        iFrame.
        iSplitR "HΦ Hclose Hdisj Htok".
        * iSplitR. iPureIntro. set_solver. 
          iSplitR. iPureIntro. set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        * iNext.
          iIntros (b) "(Hstate & Hdisj')".
          iMod ("Hclose" with "[Hdisj Hdisj' Htok]") as "_".
          { 
            iNext. iDestruct "Hdisj'" as "[(_ & Hkey)|(_ & Hkey)]".
            - rewrite !big_sepM2_insert; try set_solver.
              simpl. iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
              iExists _, _, _, _.
              iFrame. iLeft.
              iSplitL "Htok".
              iRight. iFrame.
              iPureIntro. set_solver.
              iSplitL. iFrame. done.
            - rewrite !big_sepM_insert; try set_solver.
              iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
              iExists _, _, _, _.
              iFrame. iLeft.
              iSplitL "Htok".
              by iLeft.
              iSplitL. iFrame. done. 
          }
          iModIntro.
          wp_pures.
          by iApply "HΦ".
  Qed.

  Lemma transaction2_spec γF1 γF2 :
    ∀ (cst : val) sa,
    RC_client_toolbox -∗
    client_inv γF1 γF2 -∗
    GlobalInv -∗
    {{{ token γF2 ∗ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #inv #HGinv %Φ !> (Htok & CanStart & #HiC) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">(%Vx & %Vy & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
      [(Hdisj & [->|(_ & Htok')] & -> & ->)|(_ & Htok' & _)])" "Hclose";
      try iDestruct (token_exclusive with "Htok Htok'") as "[]".
    iModIntro.
    iExists {[ "x" := Vx; "y" := ∅; "a" := ∅; "b" := ∅ ]}.
    iFrame.
    rewrite !big_sepM_insert; try set_solver.
    rewrite big_sepM_empty.
    iSplitL "Hkx Hky Hka Hkb"; first iFrame.
    iNext. iIntros "(Hcstate & (Hkx & Hky & Hka & Hkb & _) 
      & Hcx & Hcy & Hca & Hcb & _)".
    iMod ("Hclose" with "[Hkx Hky Hka Hkb Hdisj]") as "_".
    { 
      iNext. iExists _, _, _, _. iFrame.
      iLeft. iSplitL. iFrame.
      iSplitL. by iLeft. done.
    }
    iModIntro. wp_pures.
    wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _.
    iFrame.
    iNext.
    iIntros "Hcy".
    iModIntro.
    wp_pures.
    wp_apply ("Hrd" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][][$]"); 
      first solve_ndisj; first set_solver.
    iInv "inv" as ">(%Vx' & %Vy & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
      [(Hdisj & [->|(_ & Htok')] & -> & ->)|(_ & Htok' & _)])" "Hclose";
      try iDestruct (token_exclusive with "Htok Htok'") as "[]".
    iModIntro.
    iExists _, _.
    iFrame.
    iNext.
    iIntros  (wo) "(Hcx & Hkx & Hdisj')".
    iDestruct "Hdisj" as "[->| (-> & Htok')]".
    - iMod ("Hclose" with "[Hkx Hky Hka Hkb]") as "_".
      { 
        iNext. iExists _, _, _, _. iFrame.
        iLeft. iSplitL. by iLeft.
        iSplitL. by iLeft. done. 
      }
      iModIntro.
      wp_pures.
      iDestruct "Hdisj'" as "[Hdisj | (%Hfalse & _)]"; last done.
      iDestruct "Hdisj" as "(_ & [%Hfalse|->])"; first set_solver.
      wp_pures.
      rewrite /util_code.commitU.
      wp_pures.
      wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
      iInv "inv" as ">(%Vx' & %Vy & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
        [(Hdisj & [->|(_ & Htok')] & -> & ->)|(_ & Htok' & _)])" "Hclose";
        try iDestruct (token_exclusive with "Htok Htok'") as "[]".
      iModIntro.
      iExists (dom {["x" := Vx; "y" := ∅; "a" := ∅; "b" := ∅]}),
                ({["x" := None; "y" := Some (#1); "a" := None; "b" := None]}), 
                ({["x" := Vx'; "y" := ∅; "a" := ∅; "b" := ∅]}).
      iFrame.
      iSplitR "HΦ Hclose Hdisj Htok".
      * iSplitR. iPureIntro. set_solver. 
        iSplitR. iPureIntro. set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite !big_sepM_empty. iFrame.
      * iNext.
        iIntros (b) "(Hstate & Hdisj')".
        iMod ("Hclose" with "[Hdisj Hdisj' Htok]") as "_".
        { 
          iNext. iDestruct "Hdisj'" as "[(_ & Hkey)|(_ & Hkey)]".
          - rewrite !big_sepM2_insert; try set_solver.
            simpl. iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
            iExists _, _, _, _.
            iFrame. iLeft.
            iSplitL "Hdisj".
            iFrame.
            iSplitL. iRight. iFrame.
            iPureIntro. set_solver.
            done.
          - rewrite !big_sepM_insert; try set_solver.
            iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
            iExists _, _, _, _.
            iFrame. iLeft.
            iSplitL "Hdisj".
            iFrame. iSplitL.
            by iLeft. done.
        }
        iModIntro.
        wp_pures.
        by iApply "HΦ".
    - iDestruct "Hdisj'" as "[Hdisj | (%Hfalse & _)]"; last done.
      iDestruct "Hdisj" as "(_ & [(%v & -> & %Hin)|->])".
      + iMod (Seen_creation with "[$HGinv] [$Hkx]") as "(Hkx & Hseen)"; first solve_ndisj.
        iMod ("Hclose" with "[Hkx Hky Hka Hkb Htok']") as "_".
        { 
          iNext. iExists _, _, _, _. iFrame.
          iLeft. iSplitL. iRight. by iFrame.
          iSplitL. by iLeft. done. 
        }
        iModIntro.
        wp_pures.
        assert (v = (#1)) as ->; first set_solver.
        wp_pures.
        wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
        iModIntro.
        iExists _.
        iFrame.
        iNext.
        iIntros "Hcb".
        iModIntro.
        wp_pures.
        rewrite /util_code.commitU.
        wp_pures.
        wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
        iInv "inv" as ">(%Vx' & %Vy & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
          [(Hdisj & [->|(_ & Htok')] & -> & ->)|(_ & Htok' & _)])" "Hclose";
          try iDestruct (token_exclusive with "Htok Htok'") as "[]".
        iDestruct "Hdisj" as "[-> |(-> & Htok')]".
        {
          iMod (Seen_valid with "[$HGinv] [$Hkx $Hseen]") as "(Hkx & %Hfalse)"; first solve_ndisj.
          set_solver.
        }
        iModIntro.
        iExists (dom {["x" := Vx; "y" := ∅; "a" := ∅; "b" := ∅]}),
                 ({["x" := None; "y" := Some (#1); "a" := None; "b" := Some (#1)]}), 
                 ({["x" := {[#1]}; "y" := ∅; "a" := ∅; "b" := ∅]}).
        iFrame.
        iSplitR "HΦ Hclose Htok Htok'".
        * iSplitR. iPureIntro. set_solver. 
          iSplitR. iPureIntro. set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        * iNext.
          iIntros (b) "(Hstate & Hdisj')".
          iMod ("Hclose" with "[Htok' Hdisj' Htok]") as "_".
          { 
            iNext. iDestruct "Hdisj'" as "[(_ & Hkey)|(_ & Hkey)]".
            - rewrite !big_sepM2_insert; try set_solver.
              simpl. iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
              iExists _, _, _, _.
              iFrame. iRight.
              iFrame. by iLeft.
            - rewrite !big_sepM_insert; try set_solver.
              iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
              iExists _, _, _, _.
              iFrame. iRight.
              iFrame. by iLeft.
          }
          iModIntro.
          wp_pures.
          by iApply "HΦ".
      + iMod ("Hclose" with "[Hkx Hky Hka Hkb Htok']") as "_".
        { 
          iNext. iExists _, _, _, _. iFrame.
          iLeft. iSplitL. iRight. by iFrame.
          iSplitL. by iLeft. done. 
        }
        iModIntro.
        wp_pures.
        rewrite /util_code.commitU.
        wp_pures.
        wp_apply ("Hcom" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][$]"); first solve_ndisj.
        iInv "inv" as ">(%Vx' & %Vy & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
          [(Hdisj & [->|(_ & Htok')] & -> & ->)|(_ & Htok' & _)])" "Hclose";
          try iDestruct (token_exclusive with "Htok Htok'") as "[]".
        iModIntro.
        iExists (dom {["x" := Vx; "y" := ∅; "a" := ∅; "b" := ∅]}),
                 ({["x" := None; "y" := Some (#1); "a" := None; "b" := None]}), 
                 ({["x" := Vx'; "y" := ∅; "a" := ∅; "b" := ∅]}).
        iFrame.
        iSplitR "HΦ Hclose Hdisj Htok".
        * iSplitR. iPureIntro. set_solver. 
          iSplitR. iPureIntro. set_solver.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
        * iNext.
          iIntros (b) "(Hstate & Hdisj')".
          iMod ("Hclose" with "[Hdisj Hdisj' Htok]") as "_".
          { 
            iNext. iDestruct "Hdisj'" as "[(_ & Hkey)|(_ & Hkey)]".
            - rewrite !big_sepM2_insert; try set_solver.
              simpl. iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
              iExists _, _, _, _.
              iFrame. iLeft.
              iSplitL "Hdisj".
              iFrame.
              iSplitL. 
              iRight. iFrame.
              iPureIntro. set_solver.
              done.
            - rewrite !big_sepM_insert; try set_solver.
              iDestruct "Hkey" as "(Hkx & Hky & Hka & Hkb & _)". 
              iExists _, _, _, _.
              iFrame. iLeft.
              iSplitL "Hdisj".
              iFrame. iSplitL.
              by iLeft. done. 
          }
          iModIntro.
          wp_pures.
          by iApply "HΦ".
  Qed.

  Lemma transaction3_spec γF1 γF2 :
    ∀ (cst : val) sa,
    RC_client_toolbox -∗
    client_inv γF1 γF2 -∗
    GlobalInv -∗
    {{{ ConnectionState cst sa CanStart ∗ IsConnected cst sa }}}
      transaction3 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) #inv #HGinv %Φ !> (CanStart & #HiC) HΦ".
    rewrite/transaction3.
    wp_pures.
    wp_apply ("Hst" $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj; eauto.
    iInv "inv" as ">(%Vx & %Vy & %Va & %Vb & Hkx & Hky & Hka & Hkb & Hres)" "Hclose".
    iAssert (((⌜Vx = ∅⌝ ∨ ⌜Vx = {[#1]}⌝ ∗ token γF1) ∗ (⌜Vy = ∅⌝ ∨ ⌜Vy = {[#1]}⌝ ∗ token γF2) ∗ 
              ⌜Va = ∅⌝ ∗ ⌜Vb = ∅⌝ ∨ token γF1 ∗ token γF2 ∗ (⌜Va = ∅⌝ ∨ ⌜Vb = ∅⌝)) 
              ∗ (⌜Va = ∅⌝ ∨ ⌜Vb = ∅⌝))%I with "[Hres]" as "(Hres & %Hempty)".
    {
      iDestruct "Hres" as "[(Hx & Hy & -> & ->)|(Htok1 & Htok2 & [-> | ->])]".
      - iSplitL; last by iLeft.
        iLeft. iFrame. done.
      - iSplitL. iRight. iFrame. by iLeft. by iLeft.
      - iSplitL. iRight. iFrame. by iRight. by iRight. 
    }
    destruct Hempty as [Heq_emp | Heq_emp].
    all : subst.
    1 : iMod (Seen_creation with "[$HGinv] [$Hka]") as "(Hka & Hseen)"; first solve_ndisj.
    2 : iMod (Seen_creation with "[$HGinv] [$Hka]") as "(Hka & Hseen)"; first solve_ndisj.
    all : iModIntro.
    1 : iExists {[ "x" := Vx; "y" := Vy; "a" := ∅; "b" := Vb ]}.
    2 : iExists {[ "x" := Vx; "y" := Vy; "a" := Va; "b" := ∅ ]}.
    all : iFrame.
    all : rewrite !big_sepM_insert; try set_solver.
    all : rewrite big_sepM_empty.
    all : iSplitL "Hkx Hky Hka Hkb"; iFrame.
    all : iNext; iIntros "(Hcstate & (Hkx & Hky & Hka & Hkb & _) 
      & Hcx & Hcy & Hca & Hcb & _)".
    all : iMod ("Hclose" with "[Hkx Hky Hka Hkb Hres]") as "_".
    1 : iNext; iExists _, _, _, _; iFrame.
    2 : iNext; iExists _, _, _, _; iFrame.
    all : iModIntro; wp_pures.
    all : wp_apply ("Hrd" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][][$]"); 
      first solve_ndisj; first set_solver.
    all : iInv "inv" as ">(%Vx' & %Vy' & %Va' & %Vb' & Hkx & Hky & Hka & Hkb & Hres')" "Hclose".
    all : iAssert (((⌜Vx' = ∅⌝ ∨ ⌜Vx' = {[#1]}⌝ ∗ token γF1) ∗ (⌜Vy' = ∅⌝ ∨ ⌜Vy' = {[#1]}⌝ ∗ token γF2) ∗ 
              ⌜Va' = ∅⌝ ∗ ⌜Vb' = ∅⌝ ∨ token γF1 ∗ token γF2 ∗ (⌜Va' = ∅⌝ ∨ ⌜Vb' = ∅⌝)) 
              ∗ (⌜Va' = ∅⌝ ∨ ⌜Vb' = ∅⌝))%I with "[Hres']" as "(Hres' & %Hempty')".
    1 : {
          iDestruct "Hres'" as "[(Hx & Hy & -> & ->)|(Htok1 & Htok2 & [-> | ->])]".
          - iSplitL; last by iLeft.
          iLeft. iFrame. done.
          - iSplitL. iRight. iFrame. by iLeft. by iLeft.
          - iSplitL. iRight. iFrame. by iRight. by iRight. 
        }
    2 : {
          iDestruct "Hres'" as "[(Hx & Hy & -> & ->)|(Htok1 & Htok2 & [-> | ->])]".
          - iSplitL; last by iLeft.
          iLeft. iFrame. done.
          - iSplitL. iRight. iFrame. by iLeft. by iLeft.
          - iSplitL. iRight. iFrame. by iRight. by iRight. 
        }
    all : destruct Hempty' as [Heq_emp | Heq_emp].
    all : subst.
    admit.
    
    (* - admit.



    - iModIntro.
      iExists {[ "x" := Vx; "y" := Vy; "a" := ∅; "b" := ∅ ]}.
      iFrame.
      rewrite !big_sepM_insert; try set_solver.
      rewrite big_sepM_empty.
      iSplitL "Hkx Hky Hka Hkb"; first iFrame.
      iNext. iIntros "(Hcstate & (Hkx & Hky & Hka & Hkb & _) 
        & Hcx & Hcy & Hca & Hcb & _)".
      iMod ("Hclose" with "[Hkx Hky Hka Hkb Hdisj_x Hdisj_y]") as "_".
      { 
        iNext. iExists _, _, _, _. iFrame.
        iLeft. iSplitL "Hdisj_x". iFrame.
        iSplitL. iFrame. done.
      }
      iModIntro. wp_pures.
      wp_apply ("Hrd" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][][$]"); 
        first solve_ndisj; first set_solver.
      iInv "inv" as ">(%Vx' & %Vy' & %Va & %Vb & Hkx & Hky & Hka & Hkb & 
        [(Hdisj_x & Hdisj_y & -> & ->)|(Htok_x & Htok_y & Hdisj)])" "Hclose".
      all : iModIntro.
      all : iExists _, _.
      all : iFrame.
      all : iNext.
      all : iIntros (wo) "(Hca & Hka & Hdisj_a)".
      + iMod ("Hclose" with "[Hkx Hky Hka Hkb Hdisj_x Hdisj_y]") as "_".
        { 
          iNext. iExists _, _, _, _. iFrame.
          iLeft. iSplitL "Hdisj_x". iFrame.
          iSplitL. iFrame. done.
        }
        iModIntro.
        wp_pures.
        wp_apply ("Hrd" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][][$]"); 
        first solve_ndisj; first set_solver.
        iInv "inv" as ">(%Vx'' & %Vy'' & %Va' & %Vb' & Hkx & Hky & Hka & Hkb & 
          [(Hdisj_x & Hdisj_y & -> & ->)|(Htok_x & Htok_y & Hdisj)])" "Hclose".
        all : iModIntro.
        all : iExists _, _.
        all : iFrame.
        all : iNext.
        all : iIntros (wo') "(Hcb & Hkb & Hdisj_b)".
        * iMod ("Hclose" with "[Hkx Hky Hka Hkb Hdisj_x Hdisj_y]") as "_".
          { 
            iNext. iExists _, _, _, _. iFrame.
            iLeft. iSplitL "Hdisj_x". iFrame.
            iSplitL. iFrame. done.
          }
          iModIntro.
          wp_pures.
          rewrite /assert.
          iDestruct "Hdisj_a" as "[(_ & Hdisj_a)| (%Hfalse & _)]"; last done.
          iDestruct "Hdisj_a" as "[%Hfalse|->]"; first set_solver.
          wp_pures.
          admit.
        * iMod ("Hclose" with "[Hkx Hky Hka Hkb Htok_x Htok_y Hdisj]") as "_".
          { 
            iNext. iExists _, _, _, _. iFrame.
            iRight. iFrame.
          }
          iModIntro.
          wp_pures.
          rewrite /assert.
          iDestruct "Hdisj_a" as "[(_ & Hdisj_a)| (%Hfalse & _)]"; last done.
          iDestruct "Hdisj_a" as "[%Hfalse|->]"; first set_solver.
          wp_pures.
          admit.
      + iMod ("Hclose" with "[Hkx Hky Hka Hkb Htok_x Htok_y Hdisj]") as "_".
        { 
          iNext. iExists _, _, _, _. iFrame.
          iRight. iFrame.
        }
        iModIntro.
        wp_pures.
        wp_apply ("Hrd" $! _ _ (⊤ ∖ ↑client_inv_name) with "[][][$]"); 
        first solve_ndisj; first set_solver.
        iInv "inv" as ">(%Vx'' & %Vy'' & %Va' & %Vb' & Hkx & Hky & Hka & Hkb & 
          [(Hdisj_x & Hdisj_y & -> & ->)|(Htok_x & Htok_y & Hdisj)])" "Hclose".
        all : iModIntro.
        all : iExists _, _.
        all : iFrame.
        all : iNext.
        all : iIntros (wo') "(Hcb & Hkb & Hdisj_b)".
        * iMod ("Hclose" with "[Hkx Hky Hka Hkb Hdisj_x Hdisj_y]") as "_".
          { 
            iNext. iExists _, _, _, _. iFrame.
            iLeft. iSplitL "Hdisj_x". iFrame.
            iSplitL. iFrame. done.
          }
          iModIntro.
          wp_pures.
          rewrite /assert.
          destruct (decide (wo = Some (#1))) as [-> | Hneq].
          -- wp_pures.
             admit.
          -- admit.
        * iMod ("Hclose" with "[Hkx Hky Hka Hkb Htok_x Htok_y Hdisj]") as "_".
          { 
            iNext. iExists _, _, _, _. iFrame.
            iRight. iFrame.
          }
          iModIntro.
          wp_pures.
          rewrite /assert.
          admit.
    - admit. *)
  Admitted.

  Lemma transaction1_client_spec γF1 γF2:
    ∀ clt,
    client_inv γF1 γF2 -∗
    GlobalInv -∗
    RC_client_toolbox -∗
    {{{
      token γF1 ∗
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_rc ∗
      unallocated {[clt]} ∗
      KVS_ClientCanConnect clt ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction1_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv #ginv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (Htok & ∅ & #KVS_si & unalloc & Hcc & free) HΦ".
    rewrite/transaction1_client.
    wp_pures.
    wp_apply ("Hinit_cli" with "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "CanStart".
    wp_pures.
    wp_apply (transaction1_spec with "[] [$inv] [$ginv] [$CanStart $Htok]").
    iFrame "#".
    done.
  Qed.

  Lemma transaction2_client_spec γF1 γF2:
    ∀ clt,
    client_inv γF1 γF2 -∗
    GlobalInv -∗
    RC_client_toolbox -∗
    {{{
      token γF2 ∗
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_rc ∗
      unallocated {[clt]} ∗
      KVS_ClientCanConnect clt ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction2_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv #ginv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (Htok & ∅ & #KVS_si & unalloc & Hcc & free) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply ("Hinit_cli" with "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "CanStart".
    wp_pures.
    wp_apply (transaction2_spec with "[] [$inv] [$ginv] [$CanStart $Htok]").
    iFrame "#".
    done.
  Qed.

  Lemma transaction3_client_spec γF1 γF2:
    ∀ clt,
    client_inv γF1 γF2 -∗
    GlobalInv -∗
    RC_client_toolbox -∗
    {{{
      clt ⤳ (∅, ∅) ∗
      KVS_address ⤇ KVS_rc ∗
      unallocated {[clt]} ∗
      KVS_ClientCanConnect clt ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      transaction3_client #clt #KVS_address @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (clt) "#inv #ginv (#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (∅ & #KVS_si & unalloc & Hcc & free) HΦ".
    rewrite/transaction3_client.
    wp_pures.
    wp_apply ("Hinit_cli" with "[$∅ $unalloc $free $KVS_si $Hcc]").
    iIntros (cst) "CanStart".
    wp_pures.
    wp_apply (transaction3_spec with "[] [$inv] [$ginv] [$CanStart]").
    iFrame "#".
    done.
  Qed.

  Lemma server_spec :
    RC_client_toolbox -∗
    {{{
      KVS_Init ∗
      KVS_address ⤳ (∅, ∅) ∗
      free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]} ∗
      KVS_address ⤇ KVS_rc
    }}}
      server #KVS_address @[ip_of_address KVS_address]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> (KVS_Init & ∅ & free & #KVS_si) HΦ".
    rewrite/server.
    wp_pures.
    by wp_apply ("Hinit_kvs" with "[$KVS_si $KVS_Init $∅ $free]").
  Qed.

End proof_of_code.

Section proof_of_runner.

  Context `{!anerisG Mdl Σ, !RC_init, !KVSG Σ}.

  Definition example_runner : expr :=
    let: "serveraddr" := MakeAddress #"0.0.0.0" #80 in
    let: "client1addr" := MakeAddress #"0.0.0.1" #80 in
    let: "client2addr" := MakeAddress #"0.0.0.2" #80 in
    let: "client3addr" := MakeAddress #"0.0.0.3" #80 in
    Start "0.0.0.0" (server "serveraddr") ;;
    Start "0.0.0.1" (transaction1_client "client1addr" "serveraddr") ;;
    Start "0.0.0.2" (transaction2_client "client2addr" "serveraddr") ;;
    Start "0.0.0.3" (transaction3_client "client3addr" "serveraddr").

  Lemma example_runner_spec :
    {{{ server_addr ⤳ (∅, ∅)
      ∗ client_1_addr ⤳ (∅, ∅)
      ∗ client_2_addr ⤳ (∅, ∅)
      ∗ client_3_addr ⤳ (∅, ∅)
      ∗ unallocated {[server_addr]}
      ∗ unallocated {[client_1_addr]}
      ∗ unallocated {[client_2_addr]}
      ∗ unallocated {[client_3_addr]}
      ∗ free_ip (ip_of_address server_addr)
      ∗ free_ip (ip_of_address client_1_addr)
      ∗ free_ip (ip_of_address client_2_addr) 
      ∗ free_ip (ip_of_address client_3_addr)}}}
      example_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iMod (RC_init_module _ {[client_1_addr; client_2_addr; client_3_addr]})
      as (RC_res) "(mem & KVS_Init & #Hginv & Hcc & #specs)";
         first done.
    iMod (own_alloc (Excl ())) as (γF1) "Hftk1"; first done.
    iMod (own_alloc (Excl ())) as (γF2) "Hftk2"; first done.
    iMod (inv_alloc client_inv_name ⊤ (client_inv_def γF1 γF2) with "[mem]") as "#Hinv".
    { 
      iNext.
      iDestruct (big_sepS_delete _ _ "x" with "mem") as "(Hx & mem)";
        first set_solver.
      iDestruct (big_sepS_delete _ _ "y" with "mem") as "(Hy & mem)";
        first set_solver.
      iDestruct (big_sepS_delete _ _ "a" with "mem") as "(Ha & mem)";
        first set_solver.
      iDestruct (big_sepS_delete _ _ "b" with "mem") as "(Hb & mem)";
        first set_solver.
      iExists _, _, _, _.
      iFrame.
      iLeft.
      iSplitL. by iLeft.
      iSplitL. by iLeft. done.
    }
    iIntros (Φ) "(Hsrvhist & Hcli1hist & Hcli2hist & Hcli3hist & Hsrvunalloc & Hcli1unalloc
    & Hcli2unalloc & Hcli3unalloc & ? & ? & ? & ?) HΦ".
    rewrite /example_runner.
    wp_pures.
    wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_rc with "Hsrvunalloc").
    iIntros "#HKVS_rc".
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iDestruct (big_sepS_delete _  _ client_1_addr with "Hcc")
      as "(Hcc1 & Hcc)";
    first set_solver.
    iDestruct (big_sepS_delete _  _ client_2_addr with "Hcc")
      as "(Hcc2 & Hcc)";
    first set_solver.
    iDestruct (big_sepS_delete _  _ client_3_addr with "Hcc")
      as "(Hcc3 & Hcc)";
    first set_solver.
    iSplitR "Hsrvhist KVS_Init".
    - iModIntro. wp_pures.
      wp_apply (aneris_wp_start {[80%positive : port]}).
      iFrame.
      iSplitR "Hcli1hist Hcli1unalloc Hcc1 Hftk1".
      + iModIntro. wp_pures.
        wp_apply (aneris_wp_start {[80%positive : port]}).
        iFrame.
        iSplitR "Hcli2hist Hcli2unalloc Hcc2 Hftk2".
        * iModIntro. wp_pures. 
          wp_apply (aneris_wp_start {[80%positive : port]}).
          iFrame.
          iSplitL "HΦ".
          -- by iApply "HΦ".
          -- iIntros "!> Hports".
              by wp_apply (transaction3_client_spec γF1 γF2 client_3_addr with "[$] [$] [$] [$]").
        * iIntros "!> Hports".
          by wp_apply (transaction2_client_spec γF1 γF2 client_2_addr with "[$] [$] [$] [$]").
      + iIntros "!> Hports".
        by wp_apply (transaction1_client_spec γF1 γF2 client_1_addr with "[$] [$] [$] [$]").
    - iIntros "!> Hports". wp_apply (server_spec with "[$][$]"); done.
  Qed.

End proof_of_runner.

Definition unit_model := model _ (λ _ _, False) ().

Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

Definition ips : gset ip_address :=
  {[ ip_of_address server_addr ; ip_of_address client_1_addr
  ; ip_of_address client_2_addr; ip_of_address client_3_addr ]}.

Definition sa_dom : gset socket_address :=
  {[ server_addr ; client_1_addr; client_2_addr; client_3_addr ]}.

Definition init_state :=
  {|
    state_heaps := {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ms := ∅;
  |}.

Theorem runner_safe :
  aneris_adequate example_runner "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model; KVSΣ]).
  apply (@adequacy Σ unit_model _ _ ips sa_dom ∅ ∅ ∅);
    [apply unit_model_rel_finitary|move=>?|set_solver..].
  iIntros "!> Hunallocated Hhist Hfrag Hips Hlbl _ _ _ _".
  iApply (example_runner_spec with "[Hunallocated Hhist Hfrag Hips Hlbl]" ).
  2 : { iModIntro. done. }
  do 3 (iDestruct (unallocated_split with "Hunallocated") as "[Hunallocated ?]";
  [set_solver|]). iFrame.
  do 3 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hhist" as "[Hhist ?]"; iFrame).
  do 3 (rewrite big_sepS_union; [|set_solver];
  rewrite !big_sepS_singleton;
  iDestruct "Hips" as "[Hips ?]"; iFrame).
  Unshelve.
  apply implication_si_rc.
  apply _.
Qed. 
