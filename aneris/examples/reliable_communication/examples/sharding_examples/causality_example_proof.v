From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.reliable_communication.lib.sharding.spec
        Require Import resources api_spec.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.sharding.proof
        Require Import proof_of_db_init.
From aneris.examples.reliable_communication.examples.sharding_examples
        Require Import causality_example_code.
From aneris.examples.reliable_communication.lib Require Import sharding_code.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting aneris_adequacy.
From aneris.examples.reliable_communication.spec
     Require Import prelude ras.
From iris.algebra Require Import excl.
Import ser_inj.
Import inject.

Section spec.

  Context `{!anerisG Mdl Σ}.
  Context `{addr : socket_address, addrs : list (socket_address*socket_address),
      addrs_ips : (Forall (λ sa, ip_of_address sa.1 = ip_of_address addr) addrs)}.

  Definition hashf k := if (k =? "x")%string then 0%nat else 1%nat.

  Context `{hashf_valid : ∀ k, (hashf k < length addrs)%nat}.

  Local Instance dbp : DB_params := {
    (** The type of the keys *)
    Key := string;
    DB_keys_val := _;
    DB_key_eq_dec := _;
    DB_key_countable := _;

    (** The type of the values *)
    Val := Z;
    DB_vals_val := _;

    (** The database's address *)
    DB_addr := addr;

    (** The shard's addresses *)
    DB_addrs := addrs;
    DB_addrs_ips := addrs_ips;

    (** The database's keys *)
    DB_keys := {[ "x"; "y" ]};

    (** The key redistribution function *)
    DB_hash := hashf;
    DB_hash_valid := hashf_valid;

    (** Some serialization lemmas *)
    DB_key_ser := string_serialization;
    DB_val_ser := int_serialization;
    DB_key_ser_inj := string_ser_is_ser_injective;
    DB_key_ser_inj_alt := string_ser_is_ser_injective_alt;
    DB_val_ser_inj := int_ser_is_ser_injective;
    DB_val_ser_inj_alt := int_ser_is_ser_injective_alt;
    DB_keys_serializable := _;
    DB_vals_serializable := _;

    (** The namespace for invariants *)
    DB_inv_name := nroot .@ "DB_inv";
  }.

  Context `{!DBG Σ}.

  Definition N := (nroot .@ "local").

  Definition token γ := own γ (Excl ()).

  Lemma alloc_token : ⊢ |==> ∃ γ : gname, token γ.
  Proof.
    iMod (own_alloc (Excl ())) as "(%γ & Hγ)"; first done.
    iModIntro.
    by iExists γ.
  Qed.

  Definition local_inv_def CanWrite Written_x Written_y NotRead Read
      : iProp Σ :=
    ("x" ↦ₖ None ∗ "y" ↦ₖ None ∗ token CanWrite ∗ token NotRead) ∨
    ("x" ↦ₖ Some 37 ∗ "y" ↦ₖ None ∗ token Written_x ∗ token NotRead) ∨
    ("x" ↦ₖ Some 37 ∗ "y" ↦ₖ Some 1 ∗ token Written_x ∗
        token Written_y ∗ token NotRead) ∨
    ("x" ↦ₖ Some 37 ∗ token Written_x ∗ token Written_y ∗ token Read).

  Definition local_inv CanWrite Written_x Written_y NotRead Read :=
    inv N (local_inv_def CanWrite Written_x Written_y NotRead Read).

  Lemma do_writes_spec wr sa
      CanWrite Written_x Written_y NotRead Read :
    local_inv CanWrite Written_x Written_y NotRead Read -∗
    write_spec wr sa -∗
    {{{ token Written_x ∗ token Written_y }}}
      do_writes wr @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#inv #write !> %Φ (Written_x & Written_y) HΦ".
    rewrite/do_writes.
    wp_pures.
    wp_apply ("write" $! (⊤ ∖ ↑N) with "[] []");
        [solve_ndisj|set_solver|].
    iInv "inv" as ">[(x_none & y_none & CanWrite & NotRead) |
                    [(_ & _ & Written_x' & _) |
                    [(_ & _ & Written_x' & _ & _) |
                    (_ & Written_x' & _ & _)]]]" "close".
    2, 3, 4: by iCombine "Written_x Written_x'" gives "%abs".
    iModIntro.
    iExists None.
    iFrame.
    iIntros "!>x_37".
    iMod ("close" with "[x_37 y_none Written_x NotRead]") as "_".
    { iNext. iRight. iLeft. iFrame. }
    iModIntro.
    wp_pures.
    wp_apply ("write" $! (⊤ ∖ ↑N) with "[] []");
        [solve_ndisj|set_solver|].
    iInv "inv" as ">[(_ & _ & CanWrite' & _) |
                    [(x_37 & y_none & Written_x & NotRead) |
                    [(_ & _ & _ & Written_y' & _) |
                    (_ & _ & Written_y' & _)]]]" "close".
    1: by iCombine "CanWrite CanWrite'" gives "%abs".
    2, 3: by iCombine "Written_y Written_y'" gives "%abs".
    iModIntro.
    iExists None.
    iFrame.
    iIntros "!>y_1".
    iMod ("close" with "[x_37 y_1 Written_x Written_y NotRead]") as "_".
    { iNext. do 2 iRight. iLeft. iFrame. }
    iApply ("HΦ" with "[//]").
  Qed.

  Lemma wait_on_read_spec rd sa
      CanWrite Written_x Written_y NotRead Read :
    local_inv CanWrite Written_x Written_y NotRead Read -∗
    read_spec rd sa -∗
  {{{ token Read }}}
    wait_on_read rd #"y" #1 @[ip_of_address sa]
  {{{ RET #(); token NotRead }}}.
  Proof.
    iIntros "#inv #read !> %Φ Read HΦ".
    rewrite/wait_on_read.
    wp_pures.
    iLöb as "IH".
    wp_apply ("read" $! (⊤ ∖ ↑N) with "[] []");
        [solve_ndisj|set_solver|].
    iInv "inv" as ">[(x_none & y_none & CanWrite & NotRead) |
                    [(x_37 & y_none & Written_x & NotRead) |
                    [(x_37 & y_1 & Written_x & Written_y & NotRead) |
                    (_ & _ & _ & Read')]]]" "close".
    4: by iCombine "Read Read'" gives "%abs".
    all: iModIntro.
    all: iExists _.
    all: iFrame.
    all: iIntros "!> y_vy".
    1: iMod ("close" with "[x_none y_vy CanWrite NotRead]") as "_";
      first (iNext; iLeft; iFrame).
    2: iMod ("close" with "[x_37 y_vy Written_x NotRead]") as "_";
      first (iNext; iRight; iLeft; iFrame).
    3: iMod ("close" with "[x_37 Written_x Written_y Read]") as "_";
      first (iNext; repeat iRight; iFrame).
    all: iModIntro.
    all: wp_pures.
    1, 2: iApply ("IH" with "Read HΦ").
    iApply ("HΦ" with "NotRead").
  Qed.

  Lemma do_reads_spec rd sa
      CanWrite Written_x Written_y NotRead Read :
    local_inv CanWrite Written_x Written_y NotRead Read -∗
    read_spec rd sa -∗
    {{{ token Read }}}
      do_reads rd @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#inv #read !> %Φ Read HΦ".
    rewrite/do_reads.
    wp_pures.
    wp_apply (wait_on_read_spec with "inv read Read").
    iIntros "NotRead".
    wp_pures.
    wp_apply ("read" $! (⊤ ∖ ↑N) with "[] []");
        [solve_ndisj|set_solver|].
    iInv "inv" as ">[(_ & _ & _ & NotRead') |
                    [(_ & _ & _ & NotRead') |
                    [(_ & _ & _ & _ & NotRead') |
                    (x_37 & Written_x & Written_y & Read)]]]" "close".
    1, 2, 3: by iCombine "NotRead NotRead'" gives "%abs".
    iModIntro.
    iExists (Some 37).
    iFrame.
    iIntros "!>x_37".
    iMod ("close" with "[x_37 Written_x Written_y Read]") as "_".
    { iNext. repeat iRight. iFrame. }
    iModIntro.
    rewrite/assert.
    wp_pures.
    iApply ("HΦ" with "[//]").
  Qed.

  Lemma node0_spec clt srv_si
      CanWrite Written_x Written_y NotRead Read :
    local_inv CanWrite Written_x Written_y NotRead Read -∗
    init_client_spec srv_si -∗
    addr ⤇ srv_si -∗
    {{{
      token Written_x ∗ token Written_y ∗
      unallocated {[clt]} ∗ 
      clt ⤳ (∅, ∅) ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      node0 #clt #addr @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#inv #init #srv_si !> %Φ
        (Written_x & Written_y & unalloc & ∅ & free) HΦ".
    rewrite/node0.
    wp_pures.
    wp_apply ("init" with "[$]").
    iIntros (wr rd) "(_ & #write)".
    wp_pures.
    wp_apply (do_writes_spec with "inv write [$]").
    iApply "HΦ".
  Qed.

  Lemma node1_spec clt srv_si
      CanWrite Written_x Written_y NotRead Read :
    local_inv CanWrite Written_x Written_y NotRead Read -∗
    init_client_spec srv_si -∗
    addr ⤇ srv_si -∗
    {{{
      token Read ∗
      unallocated {[clt]} ∗ 
      clt ⤳ (∅, ∅) ∗
      free_ports (ip_of_address clt) {[port_of_address clt]}
    }}}
      node1 #clt #addr @[ip_of_address clt]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#inv #init #srv_si !> %Φ (Read & unalloc & ∅ & free) HΦ".
    rewrite/node1.
    wp_pures.
    wp_apply ("init" with "[$]").
    iIntros (wr rd) "(#read & _)".
    wp_pures.
    wp_apply (do_reads_spec with "inv read [$]").
    iApply "HΦ".
  Qed.

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
    rewrite bool_decide_eq_false_2=>[|[/k_x]]; last done.
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
  by repeat (constructor; first done).
Qed.

Lemma hashf_valid k : (hashf k < length addrs)%nat.
Proof.
  case k_x : (k =? "x")%string.
  all: rewrite/hashf k_x/addrs/=.
  all: lia.
Qed.

Global Instance DBP : DB_params := @dbp addr addrs addrs_ips hashf_valid.

Definition main : expr :=
  Start "0.0.0.1" (init_shard DB_key_ser.(s_serializer) DB_val_ser.(s_serializer)
                    #shard0);;
  Start "0.0.0.2" (init_shard DB_key_ser.(s_serializer) DB_val_ser.(s_serializer)
                    #shard1);;
  Start "0.0.0.0" (init_server DB_key_ser.(s_serializer) DB_val_ser.(s_serializer)
                    #addr addrsv hash);;
  Start "0.0.0.3" (node0 #clt0 #addr);;
  Start "0.0.0.4" (node1 #clt1 #addr).

Section main_spec.

  Context `{!anerisG Mdl Σ, !DBG Σ}.

  Lemma main_spec shards_si srv_si (InitShard0 InitShard1 InitSrv : iProp Σ)
      shard0_si shard1_si CanWrite Written_x Written_y NotRead Read :
    local_inv CanWrite Written_x Written_y NotRead Read -∗
    ⌜shards_si !! 0%nat = Some shard0_si⌝ -∗
    ⌜shards_si !! 1%nat = Some shard1_si⌝ -∗
    init_shard_spec InitShard0 shard0_si shard0 -∗
    init_shard_spec InitShard1 shard1_si shard1 -∗
    init_server_spec InitSrv srv_si shards_si -∗
    init_client_spec srv_si -∗
    addr ⤇ srv_si -∗
    shard0 ⤇ shard0_si -∗
    shard1 ⤇ shard1_si -∗
    {{{
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
      token Written_x ∗ token Written_y ∗ token Read
    }}}
      main @["system"]
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#inv %shards_si0 %shards_si_1 #init_shard0 #init_shard1 #init_srv
              #init_clt #srv_si #shard0_si #shard1_si !> %Φ
              (unalloc_srv0 & unalloc_srv1 & unalloc_clt0 & unalloc_clt1 &
                free0 & free1 & free2 & free3 & free4 &
                addr_∅ & srv0_∅ & srv1_∅ & shard0_∅ & shard1_∅ & clt0_∅ & clt1_∅ &
                InitSrv & InitShard0 & InitShard1 &
                Written_x & Written_y & Read) HΦ".
    rewrite/main.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "InitShard0 shard0_∅"; last first.
    {
      iIntros "!>free".
      by wp_apply ("init_shard0" with "[$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitR "InitShard1 shard1_∅"; last first.
    {
      iIntros "!>free".
      by wp_apply ("init_shard1" with "[$]").
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
    iSplitR "unalloc_clt0 clt0_∅ Written_x Written_y"; last first.
    {
      iIntros "!>free".
      by wp_apply (node0_spec clt0 with "inv init_clt srv_si [$]").
    }
    iNext.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive]}).
    iFrame.
    iSplitL "HΦ"; first by iNext; iApply "HΦ".
    iIntros "!>free".
    by wp_apply (node1_spec clt1 with "inv init_clt srv_si [$]").
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
  set (Σ := #[anerisΣ dummy_model; SpecChanΣ; DBΣ]).
  apply (adequacy Σ dummy_model ips A ∅ ∅ ∅);
  [apply dummy_model_finitary | iIntros (Mdl) |set_solver..].
  assert (DBPreG Σ). apply subG_DBPreGΣ. apply _.
  iMod (DB_init_setup ⊤) as "(% & %InitSrv & %InitShards & %srv_si &
              %shards_si & init_keys & InitSrv & #init_srv & #init_clt &
              InitShards & init_shards)"; first set_solver.
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
  iMod alloc_token as "(%CanWrite & CanWrite)".
  iMod alloc_token as "(%Written_x & Written_x)".
  iMod alloc_token as "(%Written_y & Written_y)".
  iMod alloc_token as "(%NotRead & NotRead)".
  iMod alloc_token as "(%Read & Read)".
  iMod (inv_alloc N _ (local_inv_def CanWrite Written_x Written_y NotRead Read)
      with "[x_none y_none CanWrite NotRead]") as "#inv".
  { iNext. iLeft. iFrame. }
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
  by wp_apply (main_spec with "inv [//] [//] init_shard0 init_shard1
                            init_srv init_clt srv_si shard0_si shard1_si [$]").
Qed.