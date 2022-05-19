From iris.algebra Require Import auth gmap excl excl_auth.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events resources ras.

Section API_spec.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !Maximals_Computing,
            !DB_events, !DB_resources Mdl Σ}.

  Definition write_spec (wr : val) (sa : socket_address)
      (k : Key) (v : SerializableVal) (h : ghst) : iProp Σ :=
    ⌜k ∈ DB_keys⌝ -∗
    {{{ k ↦ₖ at_key k h ∗ Obs DB_addr h }}}
       wr #k v @[ip_of_address sa]
    {{{ RET #();
        ∃ (hf : ghst) (a: we), ⌜WE_key a = k⌝ ∗ ⌜WE_val a = v⌝ ∗
          ⌜at_key k hf = None⌝ ∗ Obs DB_addr (h ++ hf ++ [a]) ∗
          k ↦ₖ Some a
    }}}%I.

  Definition read_spec (rd : val) (sa : socket_address) (k : Key) (q : Qp)
             (w : option we) : iProp Σ :=
      ⌜k ∈ DB_keys⌝ -∗
    {{{ k ↦ₖ{q} w }}}
      rd #k @[ip_of_address sa]
    {{{vo, RET vo;
         k ↦ₖ{q} w ∗ (⌜vo = NONEV⌝ ∗ ⌜w = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (WE_val a)⌝ ∗ ⌜w = Some a⌝)
    }}}%I.

  Definition read_at_follower_spec
           (rd : val) (k : Key) (sa fa : socket_address) (h : ghst) : iProp Σ :=
      ⌜k ∈ DB_keys⌝ -∗
    {{{ Obs fa h }}}
      rd #k @[ip_of_address sa]
    {{{vo, RET vo;
          ∃ h', ⌜h ≤ₚ h'⌝ ∗ Obs fa h' ∗
         (⌜vo = NONEV⌝ ∗ ⌜at_key k h' = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (WE_val a)⌝ ∗ ⌜at_key k h' = Some a⌝)
    }}}%I.

  Definition init_leader_spec A : iProp Σ :=
       ⌜DB_addr ∈ A⌝ →
       ⌜DB_addrF ∈ A⌝ →
       ⌜ip_of_address DB_addrF = ip_of_address DB_addr⌝ →
       ⌜port_of_address DB_addrF ≠ port_of_address DB_addr⌝ →
        {{{ fixed A ∗
            DB_addr ⤇ db_reserved_leader_socket_interp ∗
            DB_addr ⤳ (∅, ∅) ∗
            DB_addrF ⤳ (∅, ∅) ∗
            free_ports (ip_of_address DB_addr) {[port_of_address DB_addr]} ∗
            free_ports (ip_of_address DB_addrF) {[port_of_address DB_addrF]} }}}
          init_leader (s_serializer DB_serialization)
            #DB_addr #DB_addrF @[ip_of_address DB_addr]
        {{{ RET #(); True }}}.

  Definition init_follower_spec f2La fa A : iProp Σ :=
        ⌜DB_addr ∈ A⌝ →
        ⌜fa ∈ A⌝ →
        ⌜f2La ∉ A⌝ →
        ⌜ip_of_address fa = ip_of_address f2La⌝ →
        ⌜port_of_address fa ≠ port_of_address f2La⌝ →
        {{{ fixed A ∗
            fa ⤇ db_reserved_follower_socket_interp ∗
            DB_addr ⤇ db_reserved_leader_socket_interp ∗
            DB_addr ⤳ (∅, ∅) ∗
            DB_addrF ⤳ (∅, ∅) ∗
            free_ports (ip_of_address fa) {[port_of_address fa]} ∗
            free_ports (ip_of_address f2La) {[port_of_address f2La]} }}}
          init_follower (s_serializer DB_serialization)
            #DB_addr #f2La #fa @[ip_of_address DB_addr]
        {{{ RET #(); True }}}.


  Definition init_client_proxy_leader_spec
             (A : gset socket_address) (sa : socket_address) : iProp Σ :=
        ⌜DB_addr ∈ A⌝ →
        ⌜sa ∉ A⌝ →
        {{{ fixed A ∗
            DB_addr ⤇ db_reserved_leader_socket_interp ∗
            sa ⤳ (∅, ∅) ∗
            free_ports (ip_of_address sa) {[port_of_address sa]} }}}
          init_client_leader_proxy (s_serializer DB_serialization)
            #sa #DB_addr @[ip_of_address sa]
        {{{ rd wr, RET (rd, wr);
            (∀ k q w, read_spec rd sa k q w) ∗
            (∀ k v h, write_spec wr sa k v h) }}}.

  Definition init_client_proxy_follower_spec
             (A : gset socket_address) (sa fa : socket_address) : iProp Σ :=
        ⌜fa ∈ A⌝ →
        ⌜sa ∉ A⌝ →
        {{{ fixed A ∗
            fa ⤇ db_reserved_follower_socket_interp ∗
            sa ⤳ (∅, ∅) ∗
            free_ports (ip_of_address sa) {[port_of_address sa]} }}}
          init_client_follower_proxy (s_serializer DB_serialization)
            #sa #fa @[ip_of_address sa]
        {{{ rd, RET rd;
            Obs fa [] ∗ (∀ k h, read_at_follower_spec rd k sa fa h) }}}.

End API_spec.

Section Init.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !Maximals_Computing,
            !DB_events, !DBG Σ, !DB_init_function}.

  Class DB_init := {
    DB_init_time :> DB_time;
    DB_init_events :> DB_events;
    DB_init_setup E :
      ↑DB_InvName ⊆ E →
        True ⊢ |={E}=> ∃ (DBRS : DB_resources Mdl Σ),
      GlobalInv ∗
      ([∗ set] k ∈ DB_keys, k ↦ₖ None) ∗
      (∀ A, init_leader_spec A) ∗
      (∀ A f2La fa, init_follower_spec f2La fa A) ∗
      (∀ A ca, init_client_proxy_leader_spec A ca) ∗
      (∀ A fa ca, init_client_proxy_follower_spec A fa ca)
    }.

End Init.
