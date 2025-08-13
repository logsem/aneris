From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.transactional_consistency.snapshot_isolation.specs Require Import
  time events aux_defs resources specs.
From aneris.examples.transactional_consistency.snapshot_isolation.examples.bank_transfer
  Require Import bank_transfer_code.
Import ser_inj.
From aneris.examples.transactional_consistency.snapshot_isolation.instantiation Require Import
     snapshot_isolation_api_implementation
     instantiation_of_init.
From aneris.examples.transactional_consistency.snapshot_isolation.util Require Import util_proof.
From iris.algebra Require Import excl.
From aneris.examples.transactional_consistency.snapshot_isolation.examples Require Import proof_resources.
From aneris.examples.transactional_consistency Require Import resource_algebras user_params.

Section proof.

  Context `{!User_params, !anerisG Mdl Σ, !SI_resources Mdl Σ, !KVSG Σ}.

  Definition client_inv src dst : iProp Σ :=
    ∃ (h_src h_dst : Hist) (v_src v_dst : nat), src ↦ₖ (h_src ++ [(#v_src)]) ∗ dst ↦ₖ (h_dst ++ [(#v_dst)]).

  Lemma transfer_transaction (amount : nat) (c : val) (src dst : Key) 
    (client_addr : socket_address) (client_inv_name : namespace) :
    SI_client_toolbox -∗
    {{{ ⌜src ∈ KVS_keys⌝ ∗ ⌜dst ∈ KVS_keys⌝ ∗ ⌜src ≠ dst⌝ ∗ 
        ⌜∀ (n : nat), KVS_Serializable #n ⌝ ∗
        ⌜↑KVS_InvName ⊆ (⊤ : coPset) ∖ ↑client_inv_name⌝ ∗
        inv client_inv_name (client_inv src dst) ∗ 
        ConnectionState c client_addr CanStart  ∗ 
        IsConnected c client_addr }}}
      transaction c $amount $src $dst @[ip_of_address client_addr]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> 
    (%Hin & %Hin' & %Hsub & %Hser & %Hneq & #Hinv & Hstate & #Hconn) HΦ".
    rewrite /transaction. wp_pures. 
    wp_apply ("Hst" $! c client_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    iInv (client_inv_name) as ">[%h_src [%h_dst [%v_src [%v_dst (Hks & Hkd)]]]]" "Hclose".
    iModIntro. iFrame.
    iExists {[src := (h_src ++ [(#v_src)]); dst := (h_dst ++ [(#v_dst)])]}.
    rewrite !big_sepM_insert; try set_solver. 
    2 : by apply lookup_singleton_ne.
    2 : by apply lookup_singleton_ne.
    2 : by apply lookup_singleton_ne.
    rewrite big_sepM_empty.
    iSplitL "Hks Hkd"; first iFrame.
    iIntros "(Hcstate & (Hks & Hkd & _) & ((Hcs1 & Hcs2) & (Hcd1 & Hcd2) & _) & _)".
    iMod ("Hclose" with "[Hks Hkd]") as "_".
    { iNext. iExists _,_ ,_ , _. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hrd" $! _ _ ⊤ with "[//][][$]"); first by iPureIntro.
    iModIntro.
    iExists _.
    iFrame.
    iIntros "Hcs1".
    iModIntro.
    do 2 rewrite last_snoc.
    rewrite /util_code.unSOME.
    wp_pures.
    case_bool_decide as Hleq.
    - wp_pures.
      wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #(v_src - amount)) with "[//][][$]"); first set_solver.
      iModIntro.
      iExists _, _.
      iFrame.
      iIntros "(Hcs1 & Hcs2)".
      iModIntro.
      wp_pures.
      wp_apply ("Hrd" $! _ _ ⊤ with "[//][][$]"); first by iPureIntro.
      iModIntro.
      iExists _.
      iFrame.
      iIntros "Hcd1".
      iModIntro.
      wp_pures.
      wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #(v_dst + amount)) with "[//][][$]"); first set_solver.
      iModIntro.
      iExists _, _.
      iFrame.
      iIntros "(Hcd1 & Hcd2)".
      iModIntro.
      wp_pures.
      wp_apply (commitU_spec c client_addr (⊤ ∖ ↑client_inv_name));
      try solve_ndisj. iFrame "#".
      iInv (client_inv_name) as ">[%h_src' [%h_dst' [%v_src' [%v_dst' (Hks' & Hkd')]]]]" "Hclose".
      iModIntro.
      iExists {[src := (h_src' ++ [(#v_src')]); dst := (h_dst' ++ [(#v_dst')])]} , _, 
        {[src := (Some (#(v_src - amount)), true); dst := (Some (#(v_dst + amount)), true)]}.
      iFrame.
      iSplitL "Hcs1 Hcs2 Hcd1 Hcd2 Hks' Hkd'".
        + iSplitR. iPureIntro. set_solver.
          iSplitR. iPureIntro. set_solver.
          iSplitL "Hks' Hkd'".
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          by apply lookup_singleton_ne.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          by apply lookup_singleton_ne.
        + iIntros "[_ HBig]".
          iMod ("Hclose" with "[HBig]") as "_".
          * iNext. 
            iDestruct "HBig" as "[(_ & Hkeys)|(_ & Hkeys)]".
            -- iExists (h_src' ++ _), (h_dst' ++ _), (v_src - amount), (v_dst + amount).
               rewrite !(big_sepM2_insert); try set_solver.
               iDestruct "Hkeys" as "((Hsrc & _) & (Hdst & _) & _)".
               simpl.
               replace #(v_src - amount) with #(v_src - amount)%nat; last first. 
               {
                 repeat f_equal. lia.
               }
               replace #(v_dst + amount) with #(v_dst + amount)%nat; last first. 
               {
                 repeat f_equal. lia.
               }
               iFrame.
               all : by apply lookup_singleton_ne.
            -- iExists _, _, _, _.
               rewrite !(big_sepM_insert); try set_solver.
               iDestruct "Hkeys" as "((Hsrc & _) & (Hdst & _) & _)".
               iFrame.
               by apply lookup_singleton_ne.
          * iModIntro. by iApply "HΦ".
    - wp_pures.
      wp_apply (commitU_spec c client_addr (⊤ ∖ ↑client_inv_name));
      try solve_ndisj. iFrame "#".
      iInv (client_inv_name) as ">[%h_src' [%h_dst' [%v_src' [%v_dst' (Hks' & Hkd')]]]]" "Hclose".
      iModIntro.
      iExists {[src := (h_src' ++ [$ v_src']); dst := (h_dst' ++ [$ v_dst'])]} , _, 
        {[src := (Some ($v_src), false); dst := (Some ($v_dst), false)]}.
      iFrame.
      iSplitL "Hcs1 Hcs2 Hcd1 Hcd2 Hks' Hkd'".
        + iSplitR. iPureIntro. set_solver.
          iSplitR. iPureIntro. set_solver.
          iSplitL "Hks' Hkd'".
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          by apply lookup_singleton_ne.
          rewrite !big_sepM_insert; try set_solver.
          rewrite !big_sepM_empty. iFrame.
          by apply lookup_singleton_ne.
        + iIntros "[_ HBig]".
          iMod ("Hclose" with "[HBig]") as "_".
          * iNext. iExists _, _, _, _.
            iDestruct "HBig" as "[(_ & Hkeys)|(_ & Hkeys)]".
            -- rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "Hkeys" as "((Hsrc & _) & (Hdst & _) & _)".
              iFrame.
              by apply lookup_singleton_ne.
              by apply lookup_singleton_ne.
            -- rewrite !(big_sepM_insert); try set_solver.
              iDestruct "Hkeys" as "((Hsrc & _) & (Hdst & _) & _)".
              iFrame.
              by apply lookup_singleton_ne.
          * iModIntro. by iApply "HΦ".
    Unshelve. 
    replace #(v_src - amount) with #(v_src - amount)%nat; last first. 
    {
      repeat f_equal. lia.
    }
    apply Hser.
    replace #(v_dst + amount) with #(v_dst + amount)%nat; last first. 
    {
      repeat f_equal. lia.
    }
    apply Hser.
  Qed.

End proof.

