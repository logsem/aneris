From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.reliable_communication.lib.sharding.spec
        Require Import resources api_spec.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.sharding.proof
        Require Import proof_of_db_init.
From aneris.examples.reliable_communication.examples.sharding_examples
        Require Import causality_example_code.
From aneris.examples.reliable_communication.lib Require Import sharding_code.
From iris.algebra.lib Require Import mono_list.
From aneris.aneris_lang.lib Require Import list_code.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting aneris_adequacy.
From aneris.examples.reliable_communication.spec
     Require Import prelude ras.
Import ser_inj.

Section spec.

  Context `{!anerisG Mdl Σ, !DBG Σ, !inG Σ (mono_listR natO)}.
  Context `{addr : socket_address, addrs : list (socket_address*socket_address),
      addrs_ips : (Forall (λ sa, ip_of_address sa.1 = ip_of_address addr) addrs)}.

  Local Instance dbp : DB_params :=
    {|
      DB_addr := addr;
      DB_addrs := addrs;
      DB_addrs_ips := addrs_ips;
      DB_keys := {["x"; "y"]};
      DB_serialization := int_serialization;
      DB_ser_inj := int_ser_is_ser_injective;
      DB_ser_inj_alt := int_ser_is_ser_injective_alt;
      DB_inv_name := nroot .@ "inv"
    |}.

  Definition N := (nroot .@ "local").

  Definition local_inv_def γ : iProp Σ :=
    ∃ l, own γ (●ML l) ∗
        (⌜l = []⌝ ∗ "y" ↦ₖ None ∨
        own γ (◯ML [37%nat]) ∗ "y" ↦ₖ Some #1 ∗ "x" ↦ₖ Some #37).

  Definition local_inv γ :=
    inv N (local_inv_def γ).

  Lemma do_writes_spec wr sa γ :
  {{{
    write_spec wr sa ∗
    local_inv γ ∗
    "x" ↦ₖ None
  }}}
    do_writes wr @[ip_of_address sa]
  {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#write & #inv & x_none) HΦ".
    iPoseProof (get_atomic_write_spec with "write") as "#atomic_write".
    iPoseProof (get_simplified_write_spec with "write") as "#simplified_write".
    rewrite/do_writes.
    wp_pures.
    wp_apply ("simplified_write" $! (SerVal #37) with "[] x_none");
        first set_solver.
    iIntros "x_37".
    wp_pures.
    wp_apply ("atomic_write" $! (⊤ ∖ ↑N) _ (SerVal #1));
      [solve_ndisj|set_solver|].
    iInv "inv" as ">(%l & ●_γ & [(-> & y_none)|(◯_γ & y_1 & x_37')])" "Hclose";
      last iPoseProof (shard_mapsto_valid with "x_37 x_37'") as "[]".
    iModIntro.
    iExists None.
    iFrame.
    iIntros "!>y_1".
    iMod (own_update with "●_γ") as "●_γ".
    { apply (mono_list_update [37%nat]). apply prefix_nil. }
    rewrite mono_list_auth_lb_op.
    iDestruct "●_γ" as "(●_γ & ◯_γ)".
    iMod ("Hclose" with "[y_1 x_37 ●_γ ◯_γ]"); last by iModIntro; iApply "HΦ".
    iNext.
    iExists [37%nat].
    iFrame.
    iRight.
    iFrame.
  Qed.

  Lemma wait_on_read_spec rd sa γ :
  {{{
    read_spec rd sa ∗
    local_inv γ
  }}}
    wait_on_read rd #"y" #1 @[ip_of_address sa]
  {{{ RET #(); own γ (◯ML [37%nat]) }}}.
  Proof.
    iIntros (Φ) "(#read & #inv) HΦ".
    iPoseProof (get_atomic_read_spec with "read") as "#atomic_read".
    rewrite/wait_on_read.
    do 8 (wp_pure _).
    iLöb as "IH".
    wp_pures.
    wp_apply ("atomic_read" $! (⊤ ∖ ↑N) "y" with "[] [//]"); first solve_ndisj.
    iInv "inv" as ">(%l & ●_γ & [(-> & y_none)|(#◯_γ & y_1 & x_37)])" "Hclose";
    iModIntro; [iExists None | iExists (Some #1)]; iFrame; iNext.
    {
      iIntros "% (y_none & [(%a & -> & %abs)|(-> & _)])"; first done.
      iMod ("Hclose" with "[●_γ y_none]").
      {
        iNext.
        iExists [].
        iFrame.
        iLeft.
        by iFrame.
      }
      iModIntro.
      do 7 (wp_pure _).
      by iApply "IH".
    }
    case l=>[|a l'];
    iCombine "●_γ ◯_γ" gives "%valid";
    apply mono_list_both_valid_L in valid;
    [by apply prefix_nil_not in valid|apply prefix_cons_inv_1 in valid].
    rewrite -valid.
    iIntros "% (y_1 & [(% & -> & %eq)|(-> & %abs)])"; last done.
    move: eq=>[<-].
    iMod ("Hclose" with "[●_γ y_1 x_37]").
    {
      iNext.
      iExists (37%nat::l').
      iFrame.
      iRight.
      iFrame "∗#".
    }
    iModIntro.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma do_reads_spec rd sa γ :
  {{{
    read_spec rd sa ∗
    local_inv γ
  }}}
    do_reads rd @[ip_of_address sa]
  {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#read & #inv) HΦ".
    iPoseProof (get_atomic_read_spec with "read") as "#atomic_read".
    rewrite/do_reads.
    wp_pures.
    wp_apply (wait_on_read_spec with "[$read $inv]").
    iIntros "#◯_γ".
    wp_pures.
    wp_apply ("atomic_read" $! (⊤ ∖ ↑N) "x" with "[] [//]"); first solve_ndisj.
    iInv "inv" as ">(%l & ●_γ & [(-> & y_none)|(_ & y_1 & x_37)])" "Hclose".
    {
      iCombine "●_γ ◯_γ" gives "%valid".
      apply mono_list_both_valid_L in valid.
      by apply prefix_nil_not in valid.
    }
    iModIntro.
    iExists (Some #37).
    iFrame.
    iNext.
    iIntros "% (x_37 & [(% & -> & %eq)|(-> & %abs)])"; last done.
    move:eq=>[<-].
    iMod ("Hclose" with "[●_γ y_1 x_37]").
    {
      iNext.
      iExists l.
      iFrame.
      iRight.
      iFrame "∗#".
    }
    iModIntro.
    wp_pures.
    rewrite/assert.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Lemma node0_spec clt srv_si γ :
  {{{
    init_client_proxy_spec srv_si ∗
    local_inv γ ∗
    "x" ↦ₖ None ∗
    unallocated {[clt]} ∗ 
    clt ⤳ (∅, ∅) ∗
    addr ⤇ srv_si ∗
    free_ports (ip_of_address clt) {[port_of_address clt]}
  }}}
    node0 #clt #addr @[ip_of_address clt]
  {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#init & #inv & x_none & unalloc & ∅ & #srv_si & free) HΦ".
    rewrite/node0.
    wp_pures.
    wp_apply ("init" with "[$unalloc $∅ $free $srv_si]").
    iIntros (wr rd) "(#read & #write)".
    wp_pures.
    by wp_apply (do_writes_spec with "[$write $inv $x_none]").
  Qed.

  Lemma node1_spec clt srv_si γ :
  {{{
    init_client_proxy_spec srv_si ∗
    local_inv γ ∗
    unallocated {[clt]} ∗ 
    clt ⤳ (∅, ∅) ∗
    addr ⤇ srv_si ∗
    free_ports (ip_of_address clt) {[port_of_address clt]}
  }}}
    node1 #clt #addr @[ip_of_address clt]
  {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#init & #inv & unalloc & ∅ & #srv_si & free) HΦ".
    rewrite/node1.
    wp_pures.
    wp_apply ("init" with "[$unalloc $∅ $free $srv_si]").
    iIntros (wr rd) "(#read & #write)".
    wp_pures.
    by wp_apply (do_reads_spec with "[$read $inv]").
  Qed.

  Definition hashf (k : Key) := if (k =? "x")%string then 0%nat else 1%nat.

  Lemma hash_spec_holds : ⊢ hash_spec hash hashf.
  Proof.
    iIntros (k sa k_keys Φ) "!>_ HΦ".
    rewrite/hash.
    wp_pures.
    case k_x : (k =? "x")%string; rewrite/hashf k_x.
    {
      apply String.eqb_eq in k_x.
      rewrite k_x.
      rewrite bool_decide_eq_true_2; last done.
      wp_pures.
      by iApply "HΦ".
    }
    apply String.eqb_neq in k_x.
    rewrite bool_decide_eq_false_2; last by move=>[/k_x].
    wp_pures.
    by iApply "HΦ".
  Qed.

End spec.

Definition addr := SocketAddressInet "0.0.0.0" 80.
Definition srv0 := SocketAddressInet "0.0.0.0" 81.
Definition shard0 := SocketAddressInet "0.0.0.1" 80.
Definition srv1 := SocketAddressInet "0.0.0.0" 82.
Definition shard1 := SocketAddressInet "0.0.0.2" 80.
Definition clt0 := SocketAddressInet "0.0.0.3" 80.
Definition clt1 := SocketAddressInet "0.0.0.4" 80.
Definition A : gset socket_address :=
                    {[addr; srv0; shard0; srv1; shard1; clt0; clt1]}.
Definition ips : gset string :=
                    {["0.0.0.0"; "0.0.0.1"; "0.0.0.2"; "0.0.0.3"; "0.0.0.4"]}.
Definition addrs := [(srv0, shard0); (srv1, shard1)].
Definition addrsv := SOMEV ((#srv0, #shard0), SOMEV ((#srv1, #shard1), NONEV)).

Lemma addrs_ips : (Forall (λ sa, ip_of_address sa.1 = ip_of_address addr) addrs).
Proof.
  repeat (constructor; first done).
  constructor.
Qed.

Global Instance DBP : DB_params := @dbp addr addrs addrs_ips.

Definition main : expr :=
  Start "0.0.0.1" (init_shard DB_serialization.(s_serializer) #shard0);;
  Start "0.0.0.2" (init_shard DB_serialization.(s_serializer) #shard1);;
  Start "0.0.0.0" (init_server DB_serialization.(s_serializer) #addr addrsv hash);;
  Start "0.0.0.3" (node0 #clt0 #addr);;
  Start "0.0.0.4" (node1 #clt1 #addr).

Section main_spec.

  Context `{!anerisG Mdl Σ, !DBG Σ, !inG Σ (mono_listR natO)}.

  Lemma main_spec shards_si srv_si (InitShard0 InitShard1 InitSrv : iProp Σ) γ :
  {{{
    ∃ (shard0_si shard1_si : message → iProp Σ),
    ⌜shards_si !! 0%nat = Some shard0_si⌝ ∗
    ⌜shards_si !! 1%nat = Some shard1_si⌝ ∗
    local_inv γ ∗
    init_shard_spec InitShard0 shard0_si shard0 ∗
    init_shard_spec InitShard1 shard1_si shard1 ∗
    init_server_spec InitSrv srv_si shards_si hashf ∗
    init_client_proxy_spec srv_si ∗
    addr ⤇ srv_si ∗
    shard0 ⤇ shard0_si ∗
    shard1 ⤇ shard1_si ∗
    unallocated {[srv0]} ∗
    unallocated {[srv1]} ∗
    unallocated {[clt0]} ∗
    unallocated {[clt1]} ∗
    free_ip "0.0.0.0" ∗
    free_ip "0.0.0.1" ∗
    free_ip "0.0.0.2" ∗
    free_ip "0.0.0.3" ∗
    free_ip "0.0.0.4" ∗
    addr ⤳ (∅, ∅) ∗
    srv0 ⤳ (∅, ∅) ∗
    srv1 ⤳ (∅, ∅) ∗
    shard0 ⤳ (∅, ∅) ∗
    shard1 ⤳ (∅, ∅) ∗
    clt0 ⤳ (∅, ∅) ∗
    clt1 ⤳ (∅, ∅) ∗
    InitSrv ∗
    InitShard0 ∗
    InitShard1 ∗
    "x" ↦ₖ None
  }}}
    main @["system"]
  {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(%shard0_si & %shard1_si & %shards_si_0 & %shards_si_1 & #inv &
              #init_shard0 & #init_shard1 & #init_srv & #init_clt & #srv_si &
              #shard0_si & #shard1_si & unalloc_srv0 & unalloc_srv1 &
              unalloc_clt0 & unalloc_clt1 & free0 & free1 & free2 & free3 &
              free4 & addr_∅ & srv0_∅ & srv1_∅ & shard0_∅ & shard1_∅ & clt0_∅ &
              clt1_∅ & InitSrv & InitShard0 & InitShard1 & x_none) HΦ".
    rewrite/main.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "InitShard0 shard0_∅"; last first.
    {
      iIntros "!>free".
      by wp_apply ("init_shard0" with "[$InitShard0 $shard0_si $shard0_∅ $free]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "InitShard1 shard1_∅"; last first.
    {
      iIntros "!>free".
      by wp_apply ("init_shard1" with "[$InitShard1 $shard1_si $shard1_∅ $free]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive; 81%positive; 82%positive]}).
    iFrame.
    iSplitR "InitSrv addr_∅ unalloc_srv0 unalloc_srv1 srv0_∅ srv1_∅"; last first.
    {
      iIntros "!>free".
      iDestruct (free_ports_split with "free") as "(free & free_srv1)";
            first set_solver.
      iDestruct (free_ports_split with "free") as "(free_srv & free_srv0)";
            first set_solver.
      wp_apply ("init_srv" with "[] [$InitSrv $addr_∅ $srv_si
              unalloc_srv0 unalloc_srv1 srv0_∅ srv1_∅ $free_srv free_srv0
                free_srv1]"); last done.
      { iPureIntro. exists (InjRV (#srv1, #shard1, InjLV #())).
        split; first done. by exists (InjLV #()). }
      iSplitR; first iApply hash_spec_holds.
      iSplitR.
      {
        iApply big_sepL_cons.
        iSplit.
        { iExists shard0_si. by iSplit. }
        iApply big_sepL_cons.
        iSplit; last done.
        iExists shard1_si. by iSplit.
      }
      iSplitL "unalloc_srv0 unalloc_srv1".
      {
        iApply big_sepL_cons.
        iSplitL "unalloc_srv0"; first done.
        iApply big_sepL_cons.
        by iFrame.
      }
      iSplitL "srv0_∅ srv1_∅".
      {
        iApply big_sepL_cons.
        iSplitL "srv0_∅"; first done.
        iApply big_sepL_cons.
        by iFrame.
      }
      iApply big_sepL_cons.
      iSplitL "free_srv0"; first done.
      iApply big_sepL_cons.
      by iFrame.
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "unalloc_clt0 clt0_∅ x_none"; last first.
    {
      iIntros "!>free".
      by wp_apply (node0_spec clt0 with "[$init_clt $inv $x_none $unalloc_clt0
                    $clt0_∅ $free $srv_si]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitL "HΦ"; first by iNext; iApply "HΦ".
    iIntros "!>free".
    by wp_apply (node1_spec clt1 with "[$init_clt $inv $unalloc_clt1 $clt1_∅ $free
                  $srv_si]").
  Qed.

End main_spec.

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
  set (Σ := #[anerisΣ dummy_model; SpecChanΣ; DBΣ;
              GFunctor (mono_listUR natO)]).
  apply (adequacy Σ dummy_model ips A ∅ ∅ ∅);
  [apply dummy_model_finitary | iIntros (Mdl) |set_solver..].
  assert (DBPreG Σ). apply subG_DB_preGΣ. apply _.
  assert (subG (GFunctor (mono_listUR natO)) Σ → inG Σ (mono_listR natO))
      by solve_inG.
  assert (inG Σ (mono_listR natO)) by apply _.
  assert (Top (DB_Init hashf)) by apply db_init.
  iMod (@DB_init_setup _ _ _ _ hashf ⊤) as "(% & %InitSrv & %InitShards & %srv_si &
              %shards_si & init_keys & InitSrv & #init_srv & #init_clt &
              InitShards & init_shards)"; [move=>k _|set_solver|].
  { rewrite/hashf. case (k =? "x")%string=>/=; lia. }
  iPoseProof (big_sepL_cons with "init_shards") as
          "((%InitShard0 & %shard0_si & %InitShard0_def & %shard0_si_def &
              #init_shard0) & init_shards)".
  iPoseProof (big_sepL_cons with "init_shards") as
          "((%InitShard1 & %shard1_si & %InitShard1_def & %shard1_si_def &
              #init_shard1) & _)".
  iPoseProof (big_sepL_cons with "InitShards") as
          "((%Init & %Init_def & InitShard0) & InitShards)";
        rewrite InitShard0_def in Init_def; move:Init_def=>[<-] {Init}.
  iPoseProof (big_sepL_cons with "InitShards") as
          "((%Init & %Init_def & InitShard1) & _)";
        rewrite InitShard1_def in Init_def; move:Init_def=>[<-] {Init}.
  iPoseProof (big_sepS_insert with "init_keys") as "(x_none & init_keys)";
        first set_solver.
  iPoseProof (big_sepS_delete _ _ "y" with "init_keys") as "(y_none & _)";
        first set_solver.
  iMod (own_alloc (●ML [])) as "(%γ & ●_γ)"; first apply mono_list_auth_valid.
  iMod (inv_alloc N _ (local_inv_def γ) with "[y_none ●_γ]") as "#inv".
  {
    iNext.
    iExists [].
    iFrame.
    iLeft.
    by iFrame.
  }
  iModIntro.
  iIntros "unalloc ∅ _ free _ _ _ _ _".
  iPoseProof (unallocated_split with "unalloc") as "(unalloc & unalloc_clt1)";
      first set_solver.
  iPoseProof (unallocated_split with "unalloc") as "(unalloc & unalloc_clt0)";
      first set_solver.
  iPoseProof (unallocated_split with "unalloc") as "(unalloc & unalloc_shard1)";
      first set_solver.
  iPoseProof (unallocated_split with "unalloc") as "(unalloc & unalloc_srv1)";
      first set_solver.
  iPoseProof (unallocated_split with "unalloc") as "(unalloc & unalloc_shard0)";
      first set_solver.
  iPoseProof (unallocated_split with "unalloc") as "(unalloc_addr & unalloc_srv0)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ "0.0.0.0" with "free") as "(free0 & free)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ "0.0.0.1" with "free") as "(free1 & free)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ "0.0.0.2" with "free") as "(free2 & free)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ "0.0.0.3" with "free") as "(free3 & free)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ "0.0.0.4" with "free") as "(free4 & _)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ addr with "∅") as "(addr_∅ & ∅)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ srv0 with "∅") as "(srv0_∅ & ∅)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ srv1 with "∅") as "(srv1_∅ & ∅)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ shard0 with "∅") as "(shard0_∅ & ∅)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ shard1 with "∅") as "(shard1_∅ & ∅)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ clt0 with "∅") as "(clt0_∅ & ∅)";
      first set_solver.
  iPoseProof (big_sepS_delete _ _ clt1 with "∅") as "(clt1_∅ & _)";
      first set_solver.
  wp_apply (aneris_wp_socket_interp_alloc_singleton srv_si with "unalloc_addr").
  iIntros "#srv_si".
  wp_apply (aneris_wp_socket_interp_alloc_singleton shard0_si with "unalloc_shard0").
  iIntros "#shard0_si".
  wp_apply (aneris_wp_socket_interp_alloc_singleton shard1_si with "unalloc_shard1").
  iIntros "#shard1_si".
  wp_apply (main_spec with "[$inv init_shard0 init_shard1 $init_srv $init_clt
          $srv_si $unalloc_clt0 $unalloc_clt1 $unalloc_srv0 $unalloc_srv1 $free0
          $free1 $free2 $free3 $free4 $addr_∅ $srv0_∅ $srv1_∅ $shard0_∅ $shard1_∅
          $clt0_∅ $clt1_∅ $x_none $InitSrv InitShard0 InitShard1]"); last done.
  iExists shard0_si, shard1_si.
  do 4 (iSplit; first done).
  iFrame "∗#".
Qed.