From aneris.aneris_lang Require Import tactics adequacy proofmode.
From iris.algebra Require Import excl.
From aneris.examples.snapshot_isolation.examples.example2
        Require Import example2_code.
 From aneris.examples.snapshot_isolation.specs
     Require Import user_params.       
From aneris.examples.snapshot_isolation.specs.specs_deprecated
     Require Import time events resources_points_to_with_key_status specs_points_to_with_key_status.
From aneris.examples.snapshot_isolation
     Require Import snapshot_isolation_code_api.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.snapshot_isolation.instantiation
      Require Import snapshot_isolation_api_implementation.
From aneris.examples.snapshot_isolation.util.util_deprecated Require Import util_proof.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting aneris_adequacy.
Import ser_inj.

Section proof_of_code.

  Context (addr : socket_address).

  Local Instance example2_params : User_params :=
    {|
      KVS_address := addr;
      KVS_keys := {["x"; "y"]};
      KVS_InvName := nroot .@ "kvs_inv";
      KVS_serialization := int_serialization;
      KVS_ser_inj := int_ser_is_ser_injective;
      KVS_ser_inj_alt := int_ser_is_ser_injective_alt
    |}.

  Context `{!anerisG Mdl Σ, !KVS_time, !KVSG Σ, !SI_resources Mdl Σ}.

  Definition local_inv_def γ : iProp Σ :=
    ∃ vx vy, "x" ↦ₖ vx ∗ "y" ↦ₖ vy ∗
        (⌜is_Some vx⌝ -∗ ∃ w, ⌜vy = Some w⌝ ∗ ⌜we_val w = #1⌝) ∗
        ((⌜vx = None⌝ ∗ ⌜vy = None⌝) ∨ own γ (Excl ())).

  Definition N := nroot .@ "example".

  Definition local_inv γ := inv N (local_inv_def γ).

  Lemma transaction1_spec cst sa γ :
    {{{
      local_inv γ ∗
      own γ (Excl ()) ∗
      ConnectionState cst CanStart ∗
      start_spec ∗
      write_spec ∗
      commit_spec
    }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & own_γ & CanStart & #start & #write & #commit) HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply ("start" $! _ _ (⊤ ∖ ↑N)); first solve_ndisj.
    iInv "inv" as ">(% & % & x_none & y_none & _ & [(-> & ->)|abs])"
        "Hclose"; last by iCombine "own_γ abs" gives "%abs".
    iModIntro.
    iExists {["x":=None; "y":=None]}.
    iSplitL "CanStart x_none y_none"; first iFrame.
    {
      iApply (big_sepM_insert _ _ "x"); [done|iFrame].
      iApply (big_sepM_insert _ _ "y"); by [|iFrame].
    }
    iIntros "!>(active & kv_state & snap)".
    iPoseProof (big_sepM_insert _ _ "x" with "kv_state")
              as "(x_none & kv_state)"; first done.
    iPoseProof (big_sepM_insert _ _ "y" with "kv_state")
              as "(y_none & _)"; first done.
    iMod ("Hclose" with "[x_none y_none]") as "_".
    { iNext. iExists None, None. iFrame. iSplit; first by iPureIntro=>[][].
      iLeft. by iSplit. }
    iModIntro.
    wp_pures.
    iPoseProof (big_sepM_insert _ _ "x" with "snap")
              as "(x_none & snap)"; first done.
    iPoseProof (big_sepM_insert _ _ "y" with "snap")
              as "(y_none & _)"; first done.
    wp_apply ("write" $! _ _ _ _ (SerVal #1) with "[] x_none");
            first done.
    iIntros "x_1".
    wp_pures.
    wp_apply ("write" $! _ _ _ _ (SerVal #1) with "[] y_none");
            first done.
    iIntros "y_1".
    wp_pures.
    wp_apply (commitT_spec _ _ (⊤ ∖ ↑N) with "[] commit");
        first solve_ndisj.
    iInv "inv" as ">(% & % & x_none & y_none & _ & [(-> & ->)|abs])"
              "Hclose"; last by iCombine "own_γ abs" gives "%abs".
    iModIntro.
    iExists {["x":=None; "y":=None]}, {["x":=None; "y":=None]},
              {["x":=(Some #1, true); "y":=(Some #1, true)]}.
    iSplitL "x_none y_none x_1 y_1 active".
    {
      iFrame.
      do 2 (iSplit; first done).
      iSplit; first by rewrite 4!dom_insert_L 2!dom_empty_L.
      iSplitL "x_none y_none".
      {
        iApply (big_sepM_insert _ _ "x"); [done|iFrame].
        iApply (big_sepM_insert _ _ "y"); by [|iFrame].
      }
      iApply (big_sepM_insert _ _ "x"); [done|iFrame].
      iApply (big_sepM_insert _ _ "y"); by [|iFrame].
    }
    iIntros "!>(CanStart & (%t & _ & data))".
    iPoseProof (big_sepM2_insert _ _ _ "x" with "data")
              as "(x_none & data)"; [done..|].
    iPoseProof (big_sepM2_insert _ _ _ "y" with "data")
              as "(y_none & _)"; [done..|].
    iMod ("Hclose" with "[x_none y_none own_γ]") as "_".
    {
      iNext.
      iExists (Some {| we_key := "x"; we_val := #1; we_time := t |}),
              (Some {| we_key := "y"; we_val := #1; we_time := t |}).
      iFrame.
      iPureIntro=>_.
      by exists {| we_key := "y"; we_val := #1; we_time := t |}.
    }
    iModIntro.
    by iApply "HΦ".
  Qed.

  Lemma transaction2_spec cst sa γ :
    {{{
      local_inv γ ∗
      ConnectionState cst CanStart ∗
      start_spec ∗
      read_spec ∗
      commit_spec
    }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & CanStart & #start & #read & #commit) HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply ("start" $! _ _ (⊤ ∖ ↑N)); first solve_ndisj.
    iInv "inv" as ">(%vx & %vy & x_vx & y_vy & vx_some & Hγ)" "Hclose".
    iModIntro.
    iExists {["x":=vx; "y":=vy]}.
    iSplitL "x_vx y_vy CanStart"; first iFrame.
    {
      iApply (big_sepM_insert _ _ "x"); [done|iFrame].
      iApply (big_sepM_insert _ _ "y"); by [|iFrame].
    }
    iIntros "!>(active & kv_state & snap)".
    iPoseProof (big_sepM_insert _ _ "x" with "kv_state")
              as "(x_vx & kv_state)"; first done.
    iPoseProof (big_sepM_insert _ _ "y" with "kv_state")
              as "(y_vy & _)"; first done.
    iMod ("Hclose" with "[x_vx y_vy Hγ vx_some]") as "_".
    { iNext. iExists vx, vy. by iFrame. }
    iModIntro.
    wp_pures.
    (* TODO wait for wait_on_keyT_spec to be defined *)
  Admitted.

  Lemma transaction1_client_spec sa γ :
    {{{
      local_inv γ ∗
      own γ (Excl ()) ∗
      unallocated {[sa]} ∗
      KVS_address ⤇ KVS_si ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      init_client_proxy_spec ∗
      start_spec ∗
      write_spec ∗
      commit_spec
    }}}
      transaction1_client #sa #KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & own_γ & unalloc & #KVS_si & ∅ & free & #init & #start &
                  #write & #commit) HΦ".
    rewrite/transaction1_client.
    wp_pures.
    wp_apply ("init" with "[$unalloc $∅ $free $KVS_si]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction1_spec with "[$inv $own_γ $start $write
                $commit $CanStart]").
  Qed.

  Lemma transaction2_client_spec sa γ :
    {{{
      local_inv γ ∗
      unallocated {[sa]} ∗
      KVS_address ⤇ KVS_si ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]} ∗
      init_client_proxy_spec ∗
      start_spec ∗
      read_spec ∗
      commit_spec
    }}}
      transaction2_client #sa #KVS_address @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & unalloc & #KVS_si & ∅ & free & #init & #start & #read &
                  #commit) HΦ".
    rewrite/transaction2_client.
    wp_pures.
    wp_apply ("init" with "[$unalloc $∅ $free $KVS_si]").
    iIntros (cst) "CanStart".
    wp_pures.
    by wp_apply (transaction2_spec with "[$inv $start $read $commit $CanStart]").
  Qed.

End proof_of_code.

(* Concrete parameters *)
Definition addr := SocketAddressInet "0.0.0.0" 80.
Definition clt1 := SocketAddressInet "0.0.0.1" 80.
Definition clt2 := SocketAddressInet "0.0.0.2" 80.

Definition addresses : gset socket_address := {[addr; clt1; clt2]}.
Definition ips : gset ip_address := {["0.0.0.0"; "0.0.0.1"; "0.0.0.2"]}.

Global Instance params : User_params := example2_params addr.

Definition main : expr :=
  Start "0.0.0.0" (server #KVS_address);;
  Start "0.0.0.1" (transaction1_client #clt1 #KVS_address);;
  Start "0.0.0.2" (transaction2_client #clt2 #KVS_address).

Section proof_of_main.

  Context `{!anerisG Mdl Σ, !KVS_time, !KVSG Σ, !SI_resources Mdl Σ}.

  Lemma main_spec γ :
    {{{
      local_inv KVS_address γ ∗
      own γ (Excl ()) ∗
      unallocated {[clt1]} ∗
      unallocated {[clt2]} ∗
      KVS_address ⤇ KVS_si ∗
      KVS_address ⤳ (∅, ∅) ∗
      clt1 ⤳ (∅, ∅) ∗
      clt2 ⤳ (∅, ∅) ∗
      free_ip "0.0.0.0" ∗
      free_ip "0.0.0.1" ∗
      free_ip "0.0.0.2" ∗
      init_client_proxy_spec ∗
      init_kvs_spec ∗
      start_spec ∗
      write_spec ∗
      read_spec ∗
      commit_spec ∗
      KVS_Init
    }}}
      main @["system"]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#inv & own_γ & unalloc_clt1 & unalloc_clt2 & #KVS_si &
              KVS_∅ & clt1_∅ & clt2_∅ & free_KVS & free_clt1 & free_clt2 &
              #init_client & #init_kvs & #start & #write & #read & #commit &
              KVS_Init) HΦ".
    rewrite/main.
    wp_apply (aneris_wp_start {[80%positive]} "0.0.0.0").
    iSplitL "free_KVS"; first done.
    iSplitR "KVS_∅ KVS_Init"; last first.
    {
      iIntros "!>free".
      rewrite/server.
      wp_pures.
      by wp_apply ("init_kvs" with "[$KVS_∅ $KVS_Init $free $KVS_si]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]} "0.0.0.1").
    iSplitL "free_clt1"; first done.
    iSplitR "unalloc_clt1 clt1_∅ own_γ"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction1_client_spec with "[$inv $own_γ $start $write
          $commit $unalloc_clt1 $clt1_∅ $init_client $KVS_si $free]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]} "0.0.0.2").
    iSplitL "free_clt2"; first done.
    iSplitR "unalloc_clt2 clt2_∅"; last first.
    {
      iIntros "!>free".
      by wp_apply (transaction2_client_spec with "[$inv $start $read
          $commit $unalloc_clt2 $clt2_∅ $init_client $KVS_si $free]").
    }
    iNext.
    by iApply "HΦ".
  Qed.

End proof_of_main.

Definition init_state :=
  {|
    state_heaps := {[ "system" := ∅ ]};
    state_sockets := {[ "system" := ∅ ]};
    state_ms := ∅;
  |}.

Definition dummy_model := model unit (fun x y => True) ().

Lemma dummy_model_finitary : adequacy.aneris_model_rel_finitary dummy_model.
Proof.
  move=>[] f /(_ 0%nat 1%nat).
  case:(f 0%nat)=>[][][].
  by case:(f 1%nat)=>[][][]/(_ eq_refl).
Qed.

Theorem main_adequacy : aneris_adequate main "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ dummy_model; KVSΣ]).
  apply (adequacy Σ dummy_model ips addresses ∅ ∅ ∅);
  [apply dummy_model_finitary | iIntros (Mdl) |set_solver..].
  assert (KVS_time) by admit. (* TODO instantiate Time *)
  assert (KVSG Σ) by apply _.
  iStartProof.
  iMod (SI_init_module ⊤ with "[//]") as "(% & #GlobalInv & data & #init_kvs &
          KVS_Init & #init_client & #read & #write & #start & #commit & _)".
  iMod (own_alloc (Excl ())) as "(%γ & own_γ)"; first done.
  iMod (inv_alloc N _ (local_inv_def KVS_address γ) with "[data]")
          as "#inv".
  {
    iNext.
    iPoseProof (big_sepS_insert _ _ "x" with "data")
              as "(x_none & data)"; first done.
    iPoseProof (big_sepS_delete _ _ "y" with "data")
              as "(y_none & _)"; first done.
    iExists None, None.
    iFrame.
    iSplit; first by iPureIntro=>[][].
    iLeft.
    by iSplit.
  }
  iModIntro.
  iIntros "unalloc ∅ _ free _ _ _ _ _".
  iPoseProof (unallocated_split with "unalloc")
          as "(unalloc & unalloc_clt2)"; first set_solver.
  iPoseProof (unallocated_split with "unalloc")
          as "(unalloc_kvs & unalloc_clt1)"; first set_solver.
  iPoseProof (big_sepS_delete _ _ "0.0.0.0" with "free") as "(free_kvs & free)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ "0.0.0.1" with "free") as "(free_clt1 & free)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ "0.0.0.2" with "free") as "(free_clt2 & _)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ addr with "∅") as "(kvs_∅ & ∅)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ clt1 with "∅") as "(clt1_∅ & ∅)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ clt2 with "∅") as "(clt2_∅ & _)";
      first set_solver.
  wp_apply (aneris_wp_socket_interp_alloc_singleton KVS_si with "unalloc_kvs").
  iIntros "#KVS_si".
  by wp_apply (main_spec with "[$inv $own_γ $unalloc_clt1 $unalloc_clt2 $KVS_si
              $kvs_∅ $clt1_∅ $clt2_∅ $free_kvs $free_clt1 $free_clt2 $init_client
              $init_kvs $start $read $write $commit $KVS_Init]").
Admitted.