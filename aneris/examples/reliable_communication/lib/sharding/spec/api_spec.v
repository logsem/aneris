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

Section Spec.

  Context `{!anerisG Mdl Σ, !DBG Σ, !DB_params}.

  Definition write_spec (wr : val) sa : iProp Σ :=
    ∀ E k v (P Q : iProp Σ),
    □ (⌜↑DB_inv_name ⊆ E⌝ -∗
       ⌜k ∈ DB_keys⌝ -∗
       {{{ P ∗
           □ (P ={⊤, E}=∗ ∃ old, k ↦ₖ old ∗
               ▷ (k ↦ₖ Some (SV_val v) ={E, ⊤}=∗ Q))
       }}}
         wr #k v @[ip_of_address sa]
       {{{ RET #(); Q }}}).

  Definition atomic_write_spec (wr : val) sa : iProp Σ :=
    ∀ (E : coPset) (k : Key) (v : SerializableVal),
    ⌜↑DB_inv_name ⊆ E⌝ -∗
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ old, k ↦ₖ old >>>
      wr #k v @[ip_of_address sa] E
    <<<▷ RET #(); k ↦ₖ Some (SV_val v) >>>.

  Lemma get_atomic_write_spec wr sa :
    write_spec wr sa -∗ atomic_write_spec wr sa.
  Proof.
    iIntros "#write" (E k v inv_name k_keys Φ) "!>HΦ".
    wp_apply ("write" $! _ _ _ _ (Φ #()) with "[//] [//] [HΦ]");
          last by iIntros "HΦ".
    iSplitL "HΦ"; first iApply "HΦ".
    by iIntros "!>HΦ".
  Qed.

  Definition simplified_write_spec (wr : val) sa : iProp Σ := 
    ∀ (v : SerializableVal) (old : option val) (k : Key), ⌜k ∈ DB_keys⌝ -∗
    {{{ k ↦ₖ old }}}
      wr #k v @[ip_of_address sa]
    {{{ RET #(); k ↦ₖ Some (SV_val v) }}}.

  Lemma get_simplified_write_spec wr sa :
    write_spec wr sa -∗ simplified_write_spec wr sa.
  Proof.
    iIntros "#write" (v old k k_keys Φ) "!>k_old HΦ".
    wp_apply ("write" $! ⊤ _ _ (k ↦ₖ old ∗ _)%I (Φ #())
            with "[//] [//] [$k_old HΦ]"); last by iIntros "?".
    iSplitL "HΦ"; first iApply "HΦ".
    iIntros "!>(k_old & HΦ)!>".
    iExists old.
    iFrame.
    iNext.
    iIntros "k_v!>".
    by iApply "HΦ".
  Qed.

  Definition read_spec (rd : val) sa : iProp Σ :=
    ∀ E k (P : iProp Σ) (Q : option val → iProp Σ),
    □ (⌜↑DB_inv_name ⊆ E⌝ -∗
       ⌜k ∈ DB_keys⌝ -∗
       {{{ P ∗
           □ (P ={⊤, E}=∗ ∃ v, k ↦ₖ v ∗ ▷ (k ↦ₖ v ={E,⊤}=∗ Q v))
       }}}
         rd #k @[ip_of_address sa]
       {{{ vo, RET vo; (∃ v, ⌜vo = SOMEV v⌝ ∗ Q (Some v)) ∨
                       (⌜vo = NONEV⌝ ∗ Q None) }}}).

  Definition atomic_read_spec (rd : val) sa : iProp Σ :=
    ∀ (E : coPset) (k : Key),
    ⌜↑DB_inv_name ⊆ E⌝ -∗
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ v, k ↦ₖ v >>>
      rd #k @[ip_of_address sa] E
    <<<▷ ∃∃ vo, RET vo; k ↦ₖ v ∗ ((∃ a, ⌜vo = SOMEV a⌝ ∗ ⌜v = Some a⌝) ∨
                                  (⌜vo = NONEV⌝ ∗ ⌜v = None⌝)) >>>.

  Lemma get_atomic_read_spec rd sa :
    read_spec rd sa -∗ atomic_read_spec rd sa.
  Proof.
    iIntros "#read" (E k inv_name k_keys Φ) "!>HΦ".
    wp_apply ("read" $! _ _ _ (λ v, (∃ a, ⌜v = Some a⌝ ∗ Φ (SOMEV a)) ∨
                       (⌜v = None⌝ ∗ Φ NONEV))%I with "[//] [//] [HΦ]").
    {
      iSplit; first iApply "HΦ".
      iIntros "!>HΦ".
      iMod "HΦ" as "(%v & k_v & HΦ)".
      iModIntro.
      iExists v.
      iFrame.
      iIntros "!>k_v".
      case: v=>[a|];
      [iMod ("HΦ" $! (InjRV a) with "[$k_v]") as "HΦ"; [|iModIntro];
            iLeft; iExists a; by iSplit|
       iMod ("HΦ" $! (InjLV #()) with "[$k_v]") as "HΦ"; [|iModIntro];
            iRight; by iSplit].
    }
    iIntros "% [(%v & -> & [(% & %eq & HΦ)|(%abs & _)])|(-> & [(% & %abs & _)|
              (% & HΦ)])]"; [by move: eq=>[<-]|done..].
  Qed.

  Definition simplified_read_spec (rd : val) sa : iProp Σ := 
    ∀ (k : Key) v, ⌜k ∈ DB_keys⌝ -∗
    {{{ k ↦ₖ v }}}
      rd #k @[ip_of_address sa]
    {{{ vo, RET vo; k ↦ₖ v ∗ ((⌜vo = NONEV⌝ ∗ ⌜v = None⌝) ∨
        (∃ a, ⌜vo = SOMEV a⌝ ∗ ⌜v = Some a⌝)) }}}.

  Lemma get_simplified_read_spec rd sa :
    read_spec rd sa -∗ simplified_read_spec rd sa.
  Proof.
    iIntros "#read" (k v k_keys Φ) "!>k_v HΦ".
    wp_apply ("read" $! ⊤ _ (k ↦ₖ v ∗ _)%I (λ v, (∃ a, ⌜v = Some a⌝ ∗ Φ (SOMEV a)) ∨
                       (⌜v = None⌝ ∗ Φ NONEV))%I with "[//] [//] [$k_v HΦ]").
    {
      iSplit; first iApply "HΦ".
      iIntros "!>(k_v & HΦ)".
      iModIntro.
      iExists v.
      iFrame.
      iIntros "!> k_v!>".
      case: v=>[a|];[iLeft; iExists a|iRight];
        (iSplit; [done|iApply "HΦ"]; iFrame); [iRight; iExists a|iLeft]; by iSplit.
    }
    iIntros "% [(% & -> & [(% & %eq & HΦ)|(%abs & _)])|(-> & [(% & %abs & _)|
              (% & HΦ)])]"; [by move:eq=>[<-]|done..].
  Qed.

  Definition hash_spec (hashv : val) (hash : Key → nat) : iProp Σ :=
    ∀ (k : Key) sa, ⌜k ∈ DB_keys⌝ -∗
    {{{ True }}}
      hashv #k @[ip_of_address sa]
    {{{ RET #(hash k); True }}}.

  Definition init_server_spec
    SrvInit srv_si (shards_si : list _) hash : iProp Σ :=
    ∀ hashv addrs, ⌜is_list DB_addrs addrs⌝ -∗
    {{{
      hash_spec hashv hash ∗
      SrvInit ∗
      DB_addr ⤇ srv_si ∗
      DB_addr ⤳ (∅, ∅) ∗
      free_ports (ip_of_address DB_addr) {[port_of_address DB_addr]} ∗
      ([∗ list] i↦sa ∈ DB_addrs,
          (∃ sa_si , ⌜(shards_si !! i) = (Some sa_si)⌝ ∗ (snd sa) ⤇ sa_si)) ∗
      ([∗ list] i↦sa ∈ DB_addrs, unallocated {[ (fst sa) ]}) ∗ 
      ([∗ list] i↦sa ∈ DB_addrs, (fst sa) ⤳ (∅, ∅)) ∗
      ([∗ list] i↦sa ∈ DB_addrs,
            free_ports (ip_of_address (fst sa)) {[port_of_address (fst sa)]})
    }}}
      init_server (s_serializer DB_serialization) #DB_addr addrs hashv
                                          @[ip_of_address DB_addr]
    {{{ RET #(); True }}}.

  Definition init_shard_spec ShardInit shard_si sa : iProp Σ :=
    {{{
      ShardInit ∗
      sa ⤇ shard_si ∗
      sa ⤳ (∅, ∅) ∗
      free_ports (ip_of_address sa) {[port_of_address sa]}
    }}}
      init_shard (s_serializer DB_serialization) #sa @[ip_of_address sa]
    {{{ RET #(); True }}}.

  Definition init_client_proxy_spec srv_si : iProp Σ :=
    ∀ sa,
    {{{
      unallocated {[sa]} ∗
      sa ⤳ (∅, ∅) ∗
      DB_addr ⤇ srv_si ∗
      free_ports (ip_of_address sa) {[port_of_address sa]}
    }}}
      init_client_proxy (s_serializer DB_serialization) #sa #DB_addr
          @[ip_of_address sa]
    {{{ wr rd, RET (wr, rd); read_spec rd sa ∗ write_spec wr sa }}}.

End Spec.

Section Init.

  Context `{!anerisG Mdl Σ, !DBPreG Σ, !DB_params}.

  Class DB_Init (hash : Key → nat) :=
    {
    DB_init_setup E :
      (∀ k, k ∈ DB_keys → hash k < length DB_addrs)%nat →
      ↑DB_inv_name ⊆ E →
      ⊢ |={E}=>
        ∃ (dbg : @DBG Σ) InitSrv
          (InitShards : list _) srv_si shards_si,
        ([∗ set] k ∈ DB_keys, k ↦ₖ None) ∗
        InitSrv ∗
        @init_server_spec _ _ _ _ InitSrv srv_si shards_si hash ∗
        @init_client_proxy_spec _ _ _ dbg _ srv_si ∗
        ([∗ list] i↦sa ∈ DB_addrs, ∃ Init_sa,
        ⌜(InitShards !! i) = Some Init_sa⌝ ∗ Init_sa) ∗
        ([∗ list] i↦sa ∈ DB_addrs, ∃ Init_sa sa_si,
        ⌜(InitShards !! i) = Some Init_sa⌝ ∗ ⌜(shards_si !! i) = Some sa_si⌝ ∗
        @init_shard_spec _ _ _ _ Init_sa sa_si (snd sa));
    }.

End Init.