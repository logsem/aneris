From aneris.examples.reliable_communication.lib.sharding Require Import sharding_code.
From aneris.examples.reliable_communication.lib.sharding.spec
    Require Import resources api_spec.
From aneris.examples.reliable_communication.lib.sharding.proof
    Require Import proof_of_client_handler.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.reliable_communication.lib.mt_server Require Import
                    mt_server_code user_params.
From aneris.aneris_lang.lib Require Import lock_proof list_proof.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.mt_server.proof Require Import
                    mt_server_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
Import inject.

Section utils.

  Context `{!anerisG Mdl Σ, A : Type , B : Type, !Inject A val,
                          !Inject B val, ip : ip_address}.

  Lemma list_map_spec (l : list A) (fv lv : val) (P : nat → A → iProp Σ)
                              (Q : nat → A → B → iProp Σ) :
    ⌜is_list l lv⌝ -∗
    (∀ i x, {{{ ⌜l !! i = Some x⌝ ∗ P i x }}}
             fv $ x @[ip]
            {{{ ret, RET ($ ret); Q i x ret }}}) -∗
    {{{ ([∗ list] i↦x ∈ l, P i x) }}}
      list_map fv lv @[ip]
    {{{ map_l ret, RET ret;
        ⌜is_list map_l ret⌝ ∗ ⌜length map_l = length l⌝ ∗
          ([∗ list] i↦y ∈ map_l, ∃ x, ⌜l !! i = Some x⌝ ∗ Q i x y) }}}.
  Proof.
    iRevert (lv P Q).
    iInduction l as [|a l'] "Hind" using list_ind.
    {
      iIntros (lv P Q ->) "_ %Φ !>_ HΦ".
      rewrite/list_map.
      wp_pures.
      iApply ("HΦ" $! []).
      by do 2 (iSplit; first done).
    }
    iIntros (lv P Q) "(%l'v & -> & %l'v_l') #fv_spec %Φ !>P_l HΦ".
    rewrite/list_map.
    do 7 (wp_pure _).
    iPoseProof (big_sepL_cons with "P_l") as "(P_a & P_l')".
    wp_apply ("Hind" $! l'v (λ i x, P (S i) x) (λ i y, Q (S i) y) l'v_l'
                    with "[] P_l'").
    {
      iIntros (i x Ψ) "!>P HΨ".
      by wp_apply ("fv_spec" $! (S i) with "[P]").
    }
    iIntros (map_l' map_l'v) "(%map_l'_map_l'v & %l'_map_l' & Q_l')".
    wp_pures.
    wp_apply ("fv_spec" $! 0%nat with "[P_a]"); first by iFrame.
    iIntros (b) "Q_b".
    wp_apply (wp_list_cons $! map_l'_map_l'v).
    iIntros (map_l l_map_l).
    iApply "HΦ".
    iSplit; first done.
    iSplit; first by rewrite/=l'_map_l'.
    iApply big_sepL_cons.
    iFrame.
    iExists a.
    by iFrame.
  Qed.

End utils.

Section proof.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Lemma init_server_spec_holds SrvInit srv_si shards_si
    (γs : list _) (MTRs : list _) :
    ⌜∀ k γ, γs !! (DB_hash k) = Some γ → DBG_hash k = γ⌝ -∗
    run_server_spec SrvInit srv_si -∗
    ([∗ list] k↦sa ∈ DB_addrs, ∃ MTR shard_si γ,
    (@init_client_proxy_spec _ _ _ _ (user_params_at_shard γ sa.2) MTR shard_si) ∗
      ⌜γs !! k = Some γ⌝ ∗ ⌜MTRs !! k = Some MTR⌝ ∗
        ⌜shards_si !! k = Some shard_si⌝) -∗
    ([∗ list] k↦sa ∈ DB_addrs, ∃ MTR γ,
      (@make_request_spec _ _ _ _ (user_params_at_shard γ sa.2) MTR) ∗
        ⌜γs !! k = Some γ⌝ ∗ ⌜MTRs !! k = Some MTR⌝) -∗
    init_server_spec SrvInit srv_si shards_si.
  Proof.
    iIntros "%hash_coh #run_srv #init_shards #request_shards".
    iIntros (hash addrs addrs_coh Φ) "!>(#hash_spec & #srv_si & #shards_si &
        SrvInit & addr_∅ & free_addr & unalloc & addrs_∅ & free_addrs) HΦ".
    rewrite/init_server.
    wp_pures.
    iPoseProof (big_sepL_sep_2 with "free_addrs shards_si") as "init".
    iPoseProof (big_sepL_sep_2 with "addrs_∅ init") as "init".
    iPoseProof (big_sepL_sep_2 with "unalloc init") as "init".
    wp_apply (list_map_spec _ _ _ _
      (λ i sa p, (∃ MTR γ lock, ⌜MTRs !! i = Some MTR⌝ ∗ ⌜γs !! i = Some γ⌝ ∗
          (is_lock DB_inv_name (ip_of_address sa.1) lock (p.2)
              (MTR.(MTSCanRequest) (ip_of_address sa.1) (p.1))) ∗
      (@make_request_spec _ _ _ _ (user_params_at_shard γ sa.2) MTR))%I)
          $! addrs_coh with "[] [$init]").
    {
      iIntros (i sa Ψ) "!>(%addrs_x & unalloc & ∅ & free &
                        (%sa_si & %shards_si_sa_si & #sa_si)) HΨ".
      move:sa addrs_x=>[srv shard] addrs_srv_shard.
      wp_pures.
      iPoseProof (big_sepL_lookup _ _ _ _ addrs_srv_shard with "init_shards")
        as "(%MTR & %sa_si' & %γ & #init_shard & %γs_γ
                & %MTRs_MTR & %shards_si_sa_si')".
      rewrite shards_si_sa_si in shards_si_sa_si'.
      move:shards_si_sa_si'=>[<-].
      rewrite -(Forall_lookup_1 _ _ _ _ DB_addrs_ips addrs_srv_shard).
      wp_apply ("init_shard" with "[$unalloc $∅ $free $sa_si]").
      iIntros (rpc) "CanRequest".
      wp_pures.
      wp_apply (newlock_spec DB_inv_name with "CanRequest").
      iIntros (lk lock) "#lock".
      wp_pures.
      have -> : (rpc, lk)%V = $ (rpc, lk) by[].
      iApply "HΨ".
      iExists MTR, γ, lock.
      do 3 (iSplit; first done).
      iPoseProof (big_sepL_lookup _ _ _ _ addrs_srv_shard with "request_shards")
        as "(%MTR' & %γ' & #make_request & %γs_γ' & %MTRs_MTR')".
      rewrite γs_γ in γs_γ'.
      rewrite MTRs_MTR in MTRs_MTR'.
      by move: γs_γ' MTRs_MTR'=>[<-][<-].
    }
    iIntros (data datav) "(%data_datav & %data_addrs & #data)".
    wp_pures.
    wp_apply aneris_wp_fork.
    iSplitL "HΦ"; first by iNext; iApply "HΦ".
    iNext.
    rewrite/start_server.
    wp_pures.
    wp_apply ("run_srv" with "[] [$SrvInit $addr_∅ $free_addr $srv_si]");
          last done.
    iIntros (req reqd Ψ) "!>pre HΨ".
    wp_pures.
    wp_apply (client_request_handler_at_server_spec with "[pre]");
      last by iIntros (rep); iApply "HΨ".
    iSplitL.
    { iDestruct "pre" as "[(%x&%y&%z&%t&H1&H2&H3&H4&H5)
                          |(%x&%y&%z&H1&H2&H3&H4&H5)]".
      - iLeft.
        iExists x, y, z, t.
        iFrame "H1 H2 H3 H4 H5".
      - iRight.
        iExists x, y, z.
        iFrame "H1 H2 H3 H4 H5". }
    { iIntros (k k_keys ψ) "!>_ Hψ".
      wp_apply ("hash_spec" $! _ _ k_keys with "[//]").
      iIntros "_".
      iApply "Hψ".
      move: (DB_hash_valid k).
      rewrite -data_addrs=>/lookup_lt_is_Some_2[[rpc lk] data_k].
      iPoseProof (big_sepL_lookup _ _ _ _ data_k with "data")
        as "(%sa & %addrs_sa &
             (%MTR & %γ & %lock & %MTRs_MTR & %γs_γ & #lock & #make_request))".
      iExists rpc, sa.2, DB_inv_name, lock, MTR, lk, data.
      rewrite -(Forall_lookup_1 _ _ _ _ DB_addrs_ips addrs_sa).
      rewrite (hash_coh _ _ γs_γ).
      by do 3 (iSplit; first done). }
  Qed.

End proof.
