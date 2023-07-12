From aneris.examples.reliable_communication.lib.sharding Require Import sharding_code.
From aneris.examples.reliable_communication.lib.sharding.spec
    Require Import resources api_spec.
From aneris.examples.reliable_communication.lib.sharding.proof
    Require Import proof_of_server_handler proof_of_client_handler
              proof_of_init_server proof_of_init_shard proof_of_init_client.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.examples.reliable_communication.lib.mt_server Require Import
                    mt_server_code user_params.
From aneris.aneris_lang.lib Require Import lock_proof map_proof list_proof.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.examples.reliable_communication.lib.mt_server.proof Require Import
                    mt_server_proof.
From aneris.examples.reliable_communication.spec Require Import ras.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
Import map_code.
Import inject.
Import lock_proof.

Section utils.

  Lemma init_shards `{!anerisG Mdl Σ, !DB_params, !DBG Σ, !SpecChanG Σ} γs E :
      ↑DB_inv_name ⊆ E → length γs = length DB_addrs →
    ⊢ |={E}=> ∃ (ShardsInit : list (iProp Σ)) (shards_si : list _) (MTRs : list _),
      ([∗ list] i ↦ sa ∈ DB_addrs, ∃ ShardInit shard_si γ,
          let MTS := (@user_params_at_shard _ _ _ _ _ γ sa.2) in
          (@run_server_spec _ _ _ _ MTS ShardInit shard_si) ∗
          ⌜ShardsInit !! i = Some ShardInit⌝ ∗ ⌜shards_si !! i = Some shard_si⌝ ∗
        ⌜γs !! i = Some γ⌝) ∗
      ([∗ list] i ↦ sa ∈ DB_addrs, ∃ MTR γ,
          let MTS := (@user_params_at_shard _ _ _ _ _ γ sa.2) in
          (@make_request_spec _ _ _ _ MTS MTR)
        ∗ ⌜γs !! i = Some γ⌝ ∗ ⌜MTRs !! i = Some MTR⌝) ∗
      ([∗ list] i ↦ sa ∈ DB_addrs, ∃ MTR shard_si γ,
          let MTS := (@user_params_at_shard _ _ _ _ _ γ sa.2) in
          (@init_client_proxy_spec _ _ _ _ MTS MTR shard_si) ∗
            ⌜γs !! i = Some γ⌝ ∗ ⌜MTRs !! i = Some MTR⌝ ∗
            ⌜shards_si !! i = Some shard_si⌝) ∗
      ([∗ list] i ↦ sa ∈ DB_addrs, ∃ ShardInit,
        ⌜ShardsInit !! i = Some ShardInit⌝ ∗ ShardInit).
  Proof.
    iIntros (H0).
    iRevert (γs).
    iInduction DB_addrs as [|addr addrs] "Hind"; iIntros (γs len_γs).
    { iModIntro. iExists [], [], []. by do 3 (iSplit; first done). }
    move: γs len_γs=>[//|γ γs/=[]len_γs].
    iMod ("Hind" $! γs len_γs) as "(%ShardsInit & %shards_si & %MTRs &
                  #run_shards & #request_shards & #init_shards_clt & ShardsInit)".
    iClear "Hind".
    set (MTS := @user_params_at_shard _ _ _ _ _ γ addr.2).
    iMod (MTS_init_setup E MTS)
          as "(%shard_si & %ShardInit & %MTR & ShardInit &
                #run_shard & #init_shard_clt & #request_shard)";
          first (simpl; solve_ndisj).
    iModIntro.
    iExists (ShardInit :: ShardsInit), (shard_si :: shards_si),
              (MTR :: MTRs).
    iFrame "#∗".
    iSplitR.
    { iExists ShardInit, shard_si, γ. iFrame "#". by do 2 (iSplit; first done). }
    iSplitR.
    { iExists MTR, γ. iFrame "#". by iSplit. }
    iSplitR.
    { iExists MTR, shard_si, γ. iFrame "#". by do 2 (iSplit; first done). }
    iExists ShardInit. by iFrame.
  Qed.

End utils.

Section Init.

  Context `{!anerisG Mdl Σ, !DB_params, !DBPreG Σ, !SpecChanG Σ}.

  Global Instance db_init : DB_Init.
  Proof.
    constructor=>E name.
    iMod alloc_db as "(%dbg & %γs & %len_γs & %shards_valid
                              & ●_γs & ◯_γs)".
    iMod (MTS_init_setup E (@user_params_at_server _ _ _ _ dbg))
        as "(%srv_si & %SrvInit & %srv_MTR & SrvInit &
              #run_srv & #init_srv_clt & #request_srv)";
          first (simpl; solve_ndisj).
    iMod (init_shards γs) as "(%ShardsInit & %shards_si & %MTRs & #run_shards &
                   #request_shards & #init_shards_clt & ShardsInit)"; [done..|].
    iModIntro.
    iExists dbg, SrvInit,
      (mapi (λ i P, (∃ γ, ⌜γs !! i = Some γ⌝ ∗ P ∗ shard_mem γ
          (gset_to_gmap None DB_keys))%I) ShardsInit),
          srv_si, shards_si.
    iFrame.
    iSplitR.
    {
      iIntros (shardsv addrs addrs_def Φ) "!>(#hash_spec & SrvInit & #srv_si &
                        addr_∅ & addr_free & #shards_si & srv_unalloc & srv_∅ &
                        srv_free) HΦ".
      wp_apply (init_server_spec_holds with "[//] [//]
                 [$hash_spec $srv_si $addr_∅ $addr_free $shards_si
                  $srv_unalloc $srv_∅ $srv_free $run_srv $init_shards_clt
                  $request_shards $SrvInit]"); last done.
    }
    iSplitR.
    {
      iIntros (sa Φ) "!>(unalloc & ∅ & #srv_si & free) HΦ".
      by wp_apply (init_client_spec_holds with "[$unalloc $∅ $srv_si $free
                          $request_srv $init_srv_clt]").
    }
    iSplitL "●_γs ShardsInit".
    {
      iPoseProof (big_sepL_sep_2 with "●_γs ShardsInit") as "ShardsInit".
      iApply (big_sepL_impl with "ShardsInit").
      iIntros "!>%i %sa %addrs_sa ((%γ & %γs_γ & ●_γ) &
              (%ShardInit & %ShardsInit_ShardInit & ShardInit))".
      iExists (∃ γ : gname, ⌜γs !! i = Some γ⌝ ∗ ShardInit ∗
           shard_mem γ (gset_to_gmap None DB_keys))%I.
      iFrame.
      iSplitR.
      {
        iPureIntro.
        case: (mapi_i (λ i P, (∃ γ, ⌜γs !! i = Some γ⌝ ∗ P ∗ shard_mem γ
          (gset_to_gmap None DB_keys))%I)
            _ _ (lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ ShardsInit_ShardInit))) =>
        ShardInit' [?] [].
        by rewrite ShardsInit_ShardInit=>[][<-][/[swap]->->].
      }
      iExists γ.
      by iFrame.
    }
    iApply big_sepL_intro.
    iIntros "!>%i %sa %addrs_sa".
    iPoseProof (big_sepL_lookup _ _ _ _ addrs_sa with "run_shards") as
              "(%ShardInit & %shard_si & %γ & #run_shard & %ShardsInit_ShardInit &
                  %shards_si_shard_si & %γs_γ)".
    iExists (∃ γ : gname, ⌜γs !! i = Some γ⌝ ∗ ShardInit ∗
           shard_mem γ (gset_to_gmap None DB_keys))%I, shard_si.
    iFrame.
    iSplit.
    {
      iPureIntro.
      case: (mapi_i (λ i0 P,  (∃ γ0, ⌜γs !! i0 = Some γ0⌝ ∗ P ∗
        shard_mem γ0 (gset_to_gmap None DB_keys))%I)
            _ _ (lookup_lt_is_Some_1 _ _ (mk_is_Some _ _ ShardsInit_ShardInit)))=>
        ShardInit' [?] [].
      by rewrite ShardsInit_ShardInit=>[][<-][->->].
    }
    iSplit; first done.
    iIntros (Φ) "!>((%γ' & %γs_γ' & ShardInit & ●_γ') & #shard_si & ∅ & free) HΦ".
    rewrite γs_γ in γs_γ'.
    move:γs_γ'=>[<-].
    by wp_apply (init_shard_spec_holds with "[$●_γ' $shard_si $∅ $free
                            $run_shard $ShardInit]").
  Qed.

End Init.