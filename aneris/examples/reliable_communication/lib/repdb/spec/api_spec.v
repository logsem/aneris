From iris.algebra Require Import auth gmap excl excl_auth.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import db_params time events resources ras.

Section API_spec.
  Context `{!anerisG Mdl Σ, !DB_time, !DB_params, !DB_resources}.

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
                  ⌜at_key k hf = None⌝ -∗
                  ⌜we_key a_new = k⌝ -∗
                  ⌜we_val a_new = v⌝ -∗
                  ⌜∀ e, e ∈ h → e <ₜ a_new⌝ -∗
                  k ↦ₖ Some a_new -∗
                  Obs DB_addr (h ++ hf ++ [a_new]) ={E,⊤}=∗ Q a_new h hf)) -∗
        {{{ P }}}
          wr #k v @[ip_of_address sa]
        {{{ RET #();
           ∃ (h hf : ghst) (a: we), Q a h hf }}})%I.

  Definition write_spec_atomic
      (wr : val) (sa : socket_address) : iProp Σ :=
    ∀ (E : coPset) (k : Key) (v : SerializableVal),
    ⌜↑DB_InvName ⊆ E⌝ -∗
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ (h : ghst) (a_old : option we),
      ⌜at_key k h = a_old⌝ ∗
      k ↦ₖ a_old ∗
      Obs DB_addr h >>>
      wr #k v @[ip_of_address sa] E
    <<<▷ ∃∃ hf a_new, RET #();
           ⌜at_key k hf = None⌝ ∗
           ⌜we_key a_new = k⌝ ∗
           ⌜we_val a_new = v⌝ ∗
           ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
           k ↦ₖ Some a_new ∗
           Obs DB_addr (h ++ hf ++ [a_new]) >>>.

  Lemma write_spec_write_spec_atomic wr sa :
    write_spec wr sa -∗ write_spec_atomic wr sa.
  Proof.
    iIntros "#Hwr" (E k v HE Hkeys Φ) "!> Hvs".
    iApply ("Hwr" $! E k v _ (λ _ _ _, Φ #()) with "[] [] [] Hvs");
      [ done .. | | ].
    { iIntros "!> Hvs".
      iMod "Hvs" as (h a_old) "[(%Hatkey & Hk & Hobs) Hclose]".
      iModIntro. iExists _, _. iFrame. iSplit; first done.
      iNext. iIntros (hf anew Hhf Hnk Hnv) "Hpre1 Hpre2 Hpre3".
      iApply "Hclose". eauto 10 with iFrame. }
    iIntros "!> H". iDestruct "H" as (_ _ _) "H". iApply "H".
  Qed.

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

  Definition read_spec_atomic (rd : val) (sa : socket_address) : iProp Σ :=
    ∀ (E : coPset) (k : Key),
    ⌜↑DB_InvName ⊆ E⌝ -∗
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ (h : ghst) (q : Qp) (a_old : option we),
            ⌜at_key k h = a_old⌝ ∗
            Obs DB_addr h ∗
            k ↦ₖ{q} a_old >>>
      rd #k @[ip_of_address sa] E
    <<<▷ RET match a_old with None => NONEV | Some a => SOMEV (we_val a) end;
         (⌜a_old = None⌝ ∗ k ↦ₖ{q} None) ∨
         (∃ e, ⌜a_old = Some e⌝ ∗
            (k ↦ₖ{q} Some e)) >>>.

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
         k ↦ₖ{q} wo ∗ ((⌜vo = NONEV⌝ ∗ ⌜wo = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (we_val a)⌝ ∗ ⌜wo = Some a⌝))
    }}}%I.

  Definition read_at_follower_spec
           (rd : val) (csa f2csa : socket_address) (k : Key) (h : ghst) : iProp Σ :=
      ⌜k ∈ DB_keys⌝ -∗
    {{{ Obs f2csa h }}}
      rd #k @[ip_of_address csa]
    {{{vo, RET vo;
          ∃ h', ⌜h ≤ₚ h'⌝ ∗ Obs f2csa h' ∗
         ((⌜vo = NONEV⌝ ∗ ⌜at_key k h' = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (we_val a)⌝ ∗ ⌜at_key k h' = Some a⌝))
    }}}%I.

  Lemma get_simplified_write_spec wr sa :
    write_spec wr sa ⊢ ∀ k v h, simplified_write_spec wr sa k v h.
  Proof.
  Admitted.

  (* Lemma get_simplified_read_spec wr sa :
    read_spec wr sa ⊢ ∀ k q h, simplified_read_spec wr sa k q h.
  Proof.
  Admitted. *)

  Definition init_leader_spec A Init_leader leader_si leaderF_si: iProp Σ :=
    ⌜DB_addr ∈ A⌝ →
    ⌜DB_addrF ∈ A⌝ →
    ⌜ip_of_address DB_addrF = ip_of_address DB_addr⌝ →
    ⌜port_of_address DB_addrF ≠ port_of_address DB_addr⌝ →
    {{{ fixed A ∗
          DB_addr ⤇ leader_si ∗
          DB_addrF ⤇ leaderF_si ∗
          Init_leader ∗
          DB_addr ⤳ (∅, ∅) ∗
          DB_addrF ⤳ (∅, ∅) ∗
          free_ports (ip_of_address DB_addr) {[port_of_address DB_addr]} ∗
          free_ports (ip_of_address DB_addrF) {[port_of_address DB_addrF]} }}}
      init_leader (s_serializer DB_serialization)
      #DB_addr #DB_addrF @[ip_of_address DB_addr]
    {{{ RET #(); True }}}.

  Definition init_follower_spec f2lsa f2csa A initF f_si lF_si : iProp Σ :=
        ⌜DB_addrF ∈ A⌝ →
        ⌜f2csa ∈ A⌝ →
        ⌜f2lsa ∉ A⌝ →
        ⌜ip_of_address f2csa = ip_of_address f2lsa⌝ →
        ⌜port_of_address f2csa ≠ port_of_address f2lsa⌝ →
        {{{ fixed A ∗
            f2csa ⤇ f_si ∗
            DB_addrF ⤇ lF_si ∗
            initF ∗
            f2csa ⤳ (∅, ∅) ∗
            f2lsa ⤳ (∅, ∅) ∗
            free_ports (ip_of_address f2csa) {[port_of_address f2csa]} ∗
            free_ports (ip_of_address f2lsa) {[port_of_address f2lsa]} }}}
          init_follower (s_serializer DB_serialization)
            #DB_addrF #f2lsa #f2csa @[ip_of_address f2csa]
        {{{ RET #(); True }}}.


  Definition init_client_proxy_leader_spec
    (A : gset socket_address) (sa : socket_address) leader_si : iProp Σ :=
    ⌜DB_addr ∈ A⌝ →
    ⌜sa ∉ A⌝ →
    {{{ fixed A ∗
        DB_addr ⤇ leader_si ∗
        sa ⤳ (∅, ∅) ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} }}}
      init_client_leader_proxy (s_serializer DB_serialization)
                               #sa #DB_addr @[ip_of_address sa]
    {{{ wr rd, RET (wr, rd);
        (∀ k q h, read_spec rd sa k q h) ∗
          write_spec wr sa }}}.

  Definition init_client_proxy_follower_spec A csa f2csa f_si : iProp Σ :=
        ⌜f2csa ∈ A⌝ →
        ⌜csa ∉ A⌝ →
        {{{ fixed A ∗
            f2csa ⤇ f_si ∗
            csa ⤳ (∅, ∅) ∗
            free_ports (ip_of_address csa) {[port_of_address csa]} }}}
          init_client_follower_proxy (s_serializer DB_serialization)
            #csa #f2csa @[ip_of_address csa]
        {{{ rd, RET rd;
             (∀ k h, read_at_follower_spec rd csa f2csa k h) }}}.

End API_spec.

Section Init.
  Context `{!anerisG Mdl Σ, DB : !DB_params, !DB_time, !DBPreG Σ }.

  Class DB_init := {
    DB_init_setup E :
      ↑DB_InvName ⊆ E →
      DB_addr ∉ DB_followers →
      DB_addrF ∉ DB_followers →
        True ⊢ |={E}=>
      ∃ (DBRS : @DB_resources _ _ _ _ DB)
        (Init_leader : iProp Σ)
        (leader_si : message → iProp Σ)
        (leaderF_si : message → iProp Σ),
      GlobalInv ∗
      Obs DB_addr [] ∗
      ([∗ set] k ∈ DB_keys, k ↦ₖ None) ∗
      Init_leader ∗
      ((∀ A, init_leader_spec A Init_leader leader_si leaderF_si) ∗
         (∀ A ca, init_client_proxy_leader_spec A ca leader_si)) ∗
      ([∗ set] fsa ∈ DB_followers,
         ∃ (f_si : message → iProp Σ)
           (Init_follower : iProp Σ),
           Init_follower ∗
           Obs fsa [] ∗
           (∀ A f2lsa, init_follower_spec f2lsa fsa A Init_follower f_si leaderF_si) ∗
           (∀ A f2csa csa, init_client_proxy_follower_spec A csa f2csa f_si))
    }.

End Init.
