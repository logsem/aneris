From aneris.examples.reliable_communication.lib.sharding Require Import sharding_code.
From aneris.aneris_lang Require Import resources proofmode.
From aneris.aneris_lang.lib Require Import list_proof.
From aneris.examples.reliable_communication.lib.sharding.spec
    Require Import resources.
From aneris.examples.reliable_communication.lib.mt_server
     Require Import user_params.
From aneris.examples.reliable_communication.lib.mt_server.spec
     Require Import api_spec.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
Import inject.

Section Spec.

  Context `{!anerisG Mdl Σ, !DB_params, !DBG Σ}.

  Definition write_spec (wr : val) sa : iProp Σ :=
    ∀ (k : Key) v,
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ old, k ↦ₖ old >>>
      wr $k $v @[ip_of_address sa] (↑DB_inv_name)
    <<<▷ RET #(); k ↦ₖ Some v >>>.

  Definition simplified_write_spec (wr : val) sa : iProp Σ :=
    ∀ v old (k : Key), ⌜k ∈ DB_keys⌝ -∗
    {{{ k ↦ₖ old }}}
      wr $k $v @[ip_of_address sa]
    {{{ RET #(); k ↦ₖ Some v }}}.

  Lemma get_simplified_write_spec wr sa :
    write_spec wr sa -∗ simplified_write_spec wr sa.
  Proof.
    iIntros "#write" (v old k k_keys Φ) "!>k_old HΦ".
    wp_apply ("write" with "[//] [//]").
    iApply fupd_mask_intro; first done.
    iIntros "Hmask!>".
    iExists old.
    iFrame.
    iIntros "k_v". iMod "Hmask" as "_".
    iApply ("HΦ" with "k_v").
  Qed.

  Definition read_spec (rd : val) sa : iProp Σ :=
    ∀ (k : Key),
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ v, k ↦ₖ v >>>
      rd $k @[ip_of_address sa] (↑DB_inv_name)
    <<<▷ RET $v; k ↦ₖ v >>>.

  Definition simplified_read_spec (rd : val) sa : iProp Σ :=
    ∀ (k : Key) v, ⌜k ∈ DB_keys⌝ -∗
    {{{ k ↦ₖ v }}}
      rd $k @[ip_of_address sa]
    {{{ RET $v; k ↦ₖ v }}}.

  Lemma get_simplified_read_spec rd sa :
    read_spec rd sa -∗ simplified_read_spec rd sa.
  Proof.
    iIntros "#read" (k v k_keys Φ) "!>k_v HΦ".
    unshelve wp_apply ("read" $! _ _ _ ⊤ with "[%//]"); first done.
    do 2 iModIntro.
    iExists v.
    iFrame.
    iIntros "k_v".
    iApply ("HΦ" with "k_v").
  Qed.

  Definition hash_spec (hashv : val) (hash : Key → nat) : iProp Σ :=
    ∀ (k : Key) sa, ⌜k ∈ DB_keys⌝ -∗
    {{{ True }}}
      hashv $k @[ip_of_address sa]
    {{{ RET #(hash k); True }}}.

  Definition init_server_spec
    SrvInit srv_si (shards_si : list _) : iProp Σ :=
    ∀ hash addrs, ⌜is_list DB_addrs addrs⌝ -∗
    {{{
      hash_spec hash DB_hash ∗
      DB_addr ⤇ srv_si ∗
      ([∗ list] i↦sa ∈ DB_addrs, ∃ sa_si, ⌜shards_si !! i = Some sa_si⌝ ∗
          (snd sa) ⤇ sa_si) ∗
      SrvInit ∗
      DB_addr ⤳ (∅, ∅) ∗
      free_ports (ip_of_address DB_addr) {[port_of_address DB_addr]} ∗
      ([∗ list] i↦sa ∈ DB_addrs, unallocated {[ (fst sa) ]}) ∗
      ([∗ list] i↦sa ∈ DB_addrs, (fst sa) ⤳ (∅, ∅)) ∗
      ([∗ list] i↦sa ∈ DB_addrs,
            free_ports (ip_of_address (fst sa)) {[port_of_address (fst sa)]})
    }}}
      init_server (s_serializer DB_key_ser) (s_serializer DB_val_ser)
          #DB_addr addrs hash @[ip_of_address DB_addr]
    {{{ RET #(); True }}}.

  Definition init_shard_spec ShardInit shard_si sa : iProp Σ :=
    {{{
      ShardInit ∗
      sa ⤇ shard_si ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]}
    }}}
      init_shard (s_serializer DB_key_ser) (s_serializer DB_val_ser)
          #sa @[ip_of_address sa]
    {{{ RET #(); True }}}.

  Definition init_client_spec srv_si : iProp Σ :=
    ∀ sa,
    {{{
      DB_addr ⤇ srv_si ∗
      unallocated {[sa]} ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]}
    }}}
      init_client (s_serializer DB_key_ser) (s_serializer DB_val_ser)
          #sa #DB_addr @[ip_of_address sa]
    {{{ wr rd, RET (wr, rd); read_spec rd sa ∗ write_spec wr sa }}}.

End Spec.

Section Init.

  Context `{!anerisG Mdl Σ, !DB_params, !DBPreG Σ}.

  Class DB_Init :=
    {
    DB_init_setup E :
      ↑DB_inv_name ⊆ E →
      ⊢ |={E}=>
        ∃ (dbg : DBG Σ) InitSrv
          (InitShards : list _) srv_si shards_si,
        ([∗ set] k ∈ DB_keys, k ↦ₖ None) ∗
        InitSrv ∗
        init_server_spec InitSrv srv_si shards_si ∗
        init_client_spec srv_si ∗
        ([∗ list] i↦sa ∈ DB_addrs, ∃ Init_sa, ⌜InitShards !! i = Some Init_sa⌝ ∗
            Init_sa) ∗
        ([∗ list] i↦sa ∈ DB_addrs, ∃ Init_sa sa_si,
          ⌜(InitShards !! i) = Some Init_sa⌝ ∗ ⌜(shards_si !! i) = Some sa_si⌝ ∗
          init_shard_spec Init_sa sa_si (snd sa));
    }.

End Init.
