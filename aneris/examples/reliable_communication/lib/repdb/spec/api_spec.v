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
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DB_resources Mdl Σ}.

  Definition write_spec
      (wr : val) (sa : socket_address) : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key) (v : SerializableVal)
         (P : iProp Σ) (Q : we → ghst → ghst → iProp Σ),
        ⌜↑DB_InvName ⊆ E⌝ -∗
        ⌜k ∈ DB_keys⌝ -∗
        □ (P
            ={⊤, E}=∗
              ∃ (h : ghst) (a_old: option we),
                ⌜at_key k h = a_old⌝ ∗
                k ↦ₖ a_old ∗
                Obs DB_addr h ∗
                  ▷ (∀ (hf : ghst) (a_new : we),
                  ⌜at_key k hf = None⌝ ∗
                  ⌜we_key a_new = k⌝ ∗
                  ⌜we_val a_new = v⌝ ∗
                  ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
                  k ↦ₖ Some a_new ∗
                  Obs DB_addr (h ++ hf ++ [a_new]) ={E,⊤}=∗ Q a_new h hf)) -∗
        {{{ P }}}
          wr #k v @[ip_of_address sa]
        {{{ RET #();
           ∃ (h hf : ghst) (a: we), Q a h hf }}})%I.

 (* Definition read_spec
      (rd : val) (sa : socket_address)  : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key)
         (P : iProp Σ)
         (Q1 : option we → ghst → iProp Σ)
         (Q2 : we → ghst → iProp Σ),
        ⌜↑DB_InvName ⊆ E⌝ -∗
        ⌜k ∈ DB_keys⌝ -∗
        □ (P ={⊤, E}=∗
           ∃ (h : ghst) (q : Qp) (ao: option we),
               ⌜at_key k h = ao⌝ ∗
               Obs DB_addr h ∗
               k ↦ₖ{q} ao ∗
               ▷ ((⌜ao = None⌝ ∗ (k ↦ₖ{q} None) ={E,⊤}=∗ Q1 ao h) ∧
                  (∀ a, ⌜ao = Some a⌝ ∗ (k ↦ₖ{q} Some a) ={E,⊤}=∗ Q2 a h))) -∗
        {{{ P }}}
          rd #k @[ip_of_address sa]
          {{{ vo, RET vo;
            ∃ (h : ghst) (eo: option we),
              (⌜vo = NONEV⌝ ∗ ⌜eo = None⌝ ∗ Q1 eo h) ∨
              (∃ v e, ⌜vo = SOMEV v⌝ ∗ ⌜eo = Some e⌝ ∗ ⌜we_val e = v⌝ ∗ Q2 e h)
         }}})%I.
  *)

   Definition simplified_write_spec (wr : val) (sa : socket_address)
      (k : Key) (v : SerializableVal) (h : ghst) : iProp Σ :=
    ⌜k ∈ DB_keys⌝ -∗
    {{{ ∃ wo : option we, k ↦ₖ wo ∗ Obs DB_addr h ∗ ⌜at_key k h = wo⌝ }}}
       wr #k v @[ip_of_address sa]
    {{{ RET #();
        ∃ (hf : ghst) (a: we), ⌜we_key a = k⌝ ∗ ⌜we_val a = v⌝ ∗
          ⌜at_key k hf = None⌝ ∗ Obs DB_addr (h ++ hf ++ [a]) ∗
          k ↦ₖ Some a
    }}}%I.

  Definition read_spec
    (rd : val) (sa : socket_address) (k : Key) (q : Qp)
    (wo : option we) : iProp Σ :=
      ⌜k ∈ DB_keys⌝ -∗
    {{{ k ↦ₖ{q} wo }}}
      rd #k @[ip_of_address sa]
    {{{vo, RET vo;
         k ↦ₖ{q} wo ∗ (⌜vo = NONEV⌝ ∗ ⌜wo = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (we_val a)⌝ ∗ ⌜wo = Some a⌝)
    }}}%I.

  Definition read_at_follower_spec
           (rd : val) (k : Key) (sa fa : socket_address) (h : ghst) : iProp Σ :=
      ⌜k ∈ DB_keys⌝ -∗
    {{{ Obs fa h }}}
      rd #k @[ip_of_address sa]
    {{{vo, RET vo;
          ∃ h', ⌜h ≤ₚ h'⌝ ∗ Obs fa h' ∗
         (⌜vo = NONEV⌝ ∗ ⌜at_key k h' = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (we_val a)⌝ ∗ ⌜at_key k h' = Some a⌝)
    }}}%I.

  Lemma get_simplified_write_spec wr sa :
    write_spec wr sa ⊢ ∀ k v h, simplified_write_spec wr sa k v h.
  Proof.
  Admitted.

  (* Lemma get_simplified_read_spec wr sa :
    read_spec wr sa ⊢ ∀ k q h, simplified_read_spec wr sa k q h.
  Proof.
  Admitted. *)

  Definition init_leader_spec A : iProp Σ :=
       ⌜DB_addr ∈ A⌝ →
       ⌜DB_addrF ∈ A⌝ →
       ⌜ip_of_address DB_addrF = ip_of_address DB_addr⌝ →
       ⌜port_of_address DB_addrF ≠ port_of_address DB_addr⌝ →
        {{{ fixed A ∗
            (* DB_addr ⤇ db_reserved_leader_socket_interp ∗ *)
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
            (* fa ⤇ db_reserved_follower_socket_interp ∗ *)
            (* DB_addr ⤇ db_reserved_leader_socket_interp ∗ *)
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
            (* DB_addr ⤇ db_reserved_leader_socket_interp ∗ *)
            sa ⤳ (∅, ∅) ∗
            free_ports (ip_of_address sa) {[port_of_address sa]} }}}
          init_client_leader_proxy (s_serializer DB_serialization)
            #sa #DB_addr @[ip_of_address sa]
        {{{ rd wr, RET (rd, wr);
            (∀ k q h, read_spec rd sa k q h) ∗
            write_spec wr sa }}}.

  Definition init_client_proxy_follower_spec
             (A : gset socket_address) (sa fa : socket_address) : iProp Σ :=
        ⌜fa ∈ A⌝ →
        ⌜sa ∉ A⌝ →
        {{{ fixed A ∗
            (* fa ⤇ db_reserved_follower_socket_interp ∗ *)
            sa ⤳ (∅, ∅) ∗
            free_ports (ip_of_address sa) {[port_of_address sa]} }}}
          init_client_follower_proxy (s_serializer DB_serialization)
            #sa #fa @[ip_of_address sa]
        {{{ rd, RET rd;
            Obs fa [] ∗ (∀ k h, read_at_follower_spec rd k sa fa h) }}}.

End API_spec.

Section Init.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !DBG Σ, !DB_init_function}.

  Class DB_init := {
    DB_init_time :> DB_time;
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
