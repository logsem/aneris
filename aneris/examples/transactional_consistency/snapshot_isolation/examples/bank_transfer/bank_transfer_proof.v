(* From aneris.aneris_lang Require Import network resources proofmode.
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
    ∃ (h_src h_dst : Hist) (v_src v_dst : nat), src ↦ₖ (h_src ++ [$v_src]) ∗ dst ↦ₖ (h_dst ++ [$v_dst]).

  Lemma transfer_transaction (amount : nat) (c : val) (src dst : Key) 
    (client_addr : socket_address) (client_inv_name : namespace) :
    SI_client_toolbox -∗
    {{{ ⌜src ∈ KVS_keys⌝ ∗ ⌜dst ∈ KVS_keys⌝ ∗ ⌜src ≠ dst⌝ ∗ 
        (* ⌜KVS_InvName ⊆ ⊤ ∖ client_inv_name⌝ ∗ *)
        inv client_inv_name (client_inv src dst) ∗ 
        ConnectionState c client_addr CanStart  ∗ 
        IsConnected c client_addr }}}
      transaction c $amount $src $dst @[ip_of_address client_addr]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros "(#Hinit_kvs & #Hinit_cli & #Hrd & #Hwr & #Hst & #Hcom) %Φ !> 
    (%Hin & %Hin' & %Hneq & #Hinv & Hstate & #Hconn) HΦ".
    rewrite /transaction. wp_pures. 
    wp_apply ("Hst" $! c client_addr (⊤ ∖ ↑client_inv_name)); try solve_ndisj.
    (* Search (_ ⊆ _). *)
    (* iPureIntro. set_solver. *)
    admit.
    iInv (client_inv_name) as ">[%h_src [%h_dst [%v_src [%v_dst (Hks & Hkd)]]]]" "Hclose".
    iModIntro. iFrame.
    iExists {[src := (h_src ++ [$ v_src]); dst := (h_dst ++ [$ v_dst])]}.
    rewrite !big_sepM_insert; try set_solver. 
    2 : by apply lookup_singleton_ne.
    2 : by apply lookup_singleton_ne.
    2 : by apply lookup_singleton_ne.
    rewrite big_sepM_empty.
    iSplitL "Hks Hkd"; first iFrame.
    iNext. iIntros "(Hcstate & (Hks & Hkd & _) & ((Hcs1 & Hcs2) & (Hcd1 & Hcd2) & _) & _)".
    iMod ("Hclose" with "[Hks Hkd]") as "_".
    { iNext. iExists _,_ ,_ , _. iFrame. }
    iModIntro. wp_pures.
    wp_apply ("Hrd" $! _ _ ⊤ with "[//][][$]"); first by iPureIntro.
    iModIntro.
    iExists _.
    iFrame.
    iNext.
    iIntros "Hcs1".
    iModIntro.
    do 2 rewrite last_snoc.
    rewrite /unSOME.
    wp_pures.
    (* wp_op. *)
    (* case_bool_decide. *)
    (* destruct (bin_op_eval LeOp amount v_src) eqn:asd. *)
    case_bool_decide as Hleq.
    - wp_pures.
      admit.
    - wp_pures.
    Search "case_bool_decide".
    wp_op.
    {
      unfold bin_op_eval.
    }
    Search "bin_op_eval_".
    (* wp_op; try done. *)
    wp_apply ("Hwr" $! _ _  ⊤ _ (SerVal #1) with "[//][][$]"); first set_solver.
    iModIntro.
    iExists _, _.
    iFrame.
    iNext.
    iIntros "(Hcx1 & Hcx2)".
    iModIntro.
    wp_pures.
    wp_apply (commitT_spec rpc client_1_addr (⊤ ∖ ↑client_inv_name));
    try solve_ndisj. iFrame "#".
    iInv (client_inv_name) as ">[%h' (Hkx & [-> | (_ & Htok') ])]" "Hclose";
    try iDestruct (token_exclusive with "Htok Htok'") as "[]".
    iModIntro.
    iExists {["x" := []]} , _, {["x" := (Some #1, true)]}.
    iFrame.
    iSplitL "Hcx1 Hcx2 Hkx".
      + iSplitR. iPureIntro. set_solver.
        iSplitR. iPureIntro. set_solver.
        iSplitL "Hkx".
        rewrite !big_sepM_insert; try set_solver.
        rewrite !big_sepM_insert; try set_solver.
        rewrite !big_sepM_empty. iFrame.
      + iNext. iIntros "[_ HBig]".
        iMod ("Hclose" with "[HBig Htok]") as "_".
            * iNext. iExists _.
              rewrite !(big_sepM2_insert); try set_solver.
              iDestruct "HBig" as "((Hkx & _) & _)".
              iFrame.
              iRight.
              iFrame.
              by iPureIntro.
            * iModIntro. by iApply "HΦ".
  Qed.

End proof. *)