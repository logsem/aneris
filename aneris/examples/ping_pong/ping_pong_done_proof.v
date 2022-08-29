From iris.algebra.lib Require Import dfrac_agree.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy.
From aneris.aneris_lang.lib Require Import
     pers_socket_proto assert_proof network_util_code network_util_proof.
From aneris.examples.ping_pong Require Import ping_pong_done_code ping_pong_done_runner.
Set Default Proof Using "Type".

(* To conduct the proof, we need to keep track of the last message received by the pong server. *)
Section ghost.
  Context `{!inG Σ (dfrac_agreeR natO)}.

  Definition NONE : nat := 0.
  Definition PONG : nat := 1.
  Definition PING : nat := 2.
  Definition DONE : nat := 3.

  (* We use a fractional agreement. The ghost state is split into two parts: one is given to
     the ping client and the other to the pong server. *)
  Definition last_message (γ : gname) (m : nat) :=
    own γ (to_frac_agree (1 / 2) m).

  Lemma last_message_alloc (m : nat) :
    ⊢ |==> ∃ γ, last_message γ m ∗ last_message γ m.
  Proof.
    unfold last_message. iMod (own_alloc (to_frac_agree 1 m)) as (γ) "Hown". { done. }
    iModIntro. iExists γ. iApply own_op. rewrite<- frac_agree_op. rewrite Qp_half_half.
    iAssumption.
  Qed.

  (* The two copies of `last_message γ` cannot point to different values. *)
  Lemma last_message_agree γ (m0 m1 : nat) :
    last_message γ m0 -∗ last_message γ m1 -∗ ⌜ m0 = m1 ⌝.
  Proof.
    unfold last_message. iIntros "Hm0 Hm1".
    iPoseProof (own_valid_2 with "Hm0 Hm1") as "%Hval".
    iPureIntro.
    apply frac_agree_op_valid_L in Hval. by destruct Hval as [_ Hval].
  Qed.

  (* When the pong server owns the two copies of `last_message γ m`, she is allowed to update the
     content `m` of the ghost state. *)
  Lemma last_message_update γ (m new : nat) :
    last_message γ m -∗ last_message γ m ==∗ (last_message γ new ∗ last_message γ new).
  Proof.
    unfold last_message. iIntros "H0 H1".
    iAssert (own γ (to_frac_agree (1 / 2 + 1 / 2) m)) with "[H0 H1]" as "H".
    { rewrite frac_agree_op. iApply own_op. iFrame. }
    rewrite Qp_half_half. iApply bupd_mono.
    { iIntros "Goal". iApply own_op. rewrite<- frac_agree_op, Qp_half_half. iExact "Goal". }
    iApply (own_update with "H"). apply cmra_update_exclusive. done.
  Qed.

  Class GhostName := {
    γpong : gname
   }.
End ghost.

Section proof.
  Context `{dG : anerisG Mdl Σ}.
  Context `{!inG Σ (dfrac_agreeR natO)}.
  Context `{GhostName}.

  (* The socket interpretation is abstracting over any message received through
     the socket and is a predicate on all received messages. *)
  Definition pong_si : socket_interp Σ  :=
    (λ msg,
     (* client is governed by a protocol Φ *)
     ∃ ϕ, m_sender msg ⤇ ϕ ∗
            (* Either the message is "PING"; *)
            ((⌜m_body msg = "PING"⌝
              (* thus, the pong server did not receive any messages; *)
              ∗ last_message γpong NONE
              (* moreover, the ping client is satisfied by the answer "PONG", and the ownership of
                 the ghost state `last_message γpong PING` as an acknoledgement that the "PING"
                 message has been received. *)
              ∗ (∀ m, ⌜m_body m = "PONG"⌝ ∗ last_message γpong PING → ϕ m)) ∨
             (* Or, the message in "DONE" and the last received message is "PING" *)
             (⌜m_body msg = "DONE"⌝ ∗ last_message γpong PING))
      )%I.

  Lemma pong_spec a ip port :
    ip = ip_of_address a →
    port = port_of_address a →
    (* a is static *)
    (* the address [a] is governed by the pong_si socket protocol *)
    {{{ a ⤇ pong_si
    (* A should contain static addresses & the port should be free *)
      ∗ free_ports ip {[port]}
    (* exclusive ownership of the [a], no messages have been sent nor received. *)
      ∗ a ⤳ (∅, ∅)
      ∗ last_message γpong NONE
    (* pong terminates the last (non ping) received message, that is "DONE" *)
    }}} (pong #a) @[ip] {{{ RET #"DONE"; True }}}.
  Proof.
    iIntros (-> -> Ψ) "(#Hsi & Hport & Ha & Hγpong) HΨ".
    wp_lam.
    wp_socket h as "Hh".
    wp_let.
    wp_socketbind.
    wp_apply (aneris_wp_receivefrom with "[$Hsi $Hh $Ha]"); [done.. | ].
    iIntros (m) "(%Hdest & [Hm | Hm])"; last first.
    { iDestruct "Hm" as "[%abs _]". exfalso. set_solver. }
    iDestruct "Hm" as "(_ & Hh & Ha & _ & Hm_si)".
    iDestruct "Hm_si" as (Φ) "[#Hsend [Hm_in | Hm_out]]"; last first.
    (* The message we received is "PING" or "DONE". Let us eliminate the later case. Indeed, that
       mean that we would also own a ghost state `last_message γpong PING`, but this would be
       incompatible with "Hγpong" : last_message γpong NONE *)
    { iDestruct "Hm_out" as "[_ Hγpong']".
      iDestruct (last_message_agree with "Hγpong Hγpong'") as "%abs".
      inversion abs.
    }
    iDestruct "Hm_in" as "(%Hbody & Hγpong' & HΦ)"; rewrite Hbody.
    wp_apply wp_unSOME. { done. }
    iIntros "_".
    (* Now that we own both parts of `last_message γpong NONE`, we can update the content of the
       ghost variable to PING. *)
    iMod (last_message_update _ _ PING with "Hγpong Hγpong'") as "[Hγpong Hγpong']".
    wp_let; wp_proj; wp_let.
    wp_apply wp_assert.
    wp_pures.
    iSplitR; first done.
    iModIntro; wp_pures.
    wp_send "HΦ Hγpong'".
    { iApply "HΦ". iFrame. done. }
    wp_seq; wp_closure; wp_lam. wp_closure. wp_let.
    iLöb as "IH".
    wp_pures.
    wp_apply (aneris_wp_receivefrom with "[$Hsi $Hh $Ha]"); [done.. | ].
    iIntros (m') "(%Hdest' & Hm')".
    wp_pures.
    iDestruct "Hm'" as "[Hm'_out | Hm'_in]".
    (* Either we received a message that is not a duplicate. *)
    - iDestruct "Hm'_out" as "(_ & Hh & Ha & _ & Hm'_si)".
      iDestruct "Hm'_si" as (?) "[_ [(_ & Hγpong' & _) | (-> & _)]]".
      (* This message must be "DONE" (because of the ghost state `last_message γpong PING` *)
      { iDestruct (last_message_agree with "Hγpong Hγpong'") as "%abs". inversion abs. }
      wp_pures.
      wp_apply wp_unSOME; first done.
      iIntros "_"; wp_pures.
      iApply "HΨ".
      done.
    (* If we receive a duplicate, this must be a "PING" message so we loop back. *)
    - iDestruct "Hm'_in" as "(%m'_recv & ? & ?)".
      rewrite right_id_L in m'_recv.
      apply elem_of_singleton in m'_recv.
      rewrite m'_recv; rewrite Hbody.
      wp_apply wp_unSOME; first done.
      iIntros "_".
      wp_let. wp_proj. wp_let. wp_op. wp_if_true.
      iApply ("IH" with "[$] [$] [$] [$]").
  Qed.

  (* Specifying the ping protocol: *)
  Definition ping_si (server : socket_address) : socket_interp Σ :=
    (λ msg, ⌜m_body msg = "PONG"⌝ ∗ last_message γpong PING)%I.

  Lemma ping_spec (a b : socket_address) ip port :
    ip = ip_of_address a →
    port = port_of_address a →
    (* the address [a] is governed by the pong_si socket protocol *)
    b ⤇ pong_si -∗
    (* A should contain static addresses & the port should be free *)
    unallocated {[a]} -∗
    free_ports ip {[port]} -∗
    (* exclusive ownership of the [a] and its sent and received messages *)
    a ⤳ (∅, ∅) -∗
    last_message γpong NONE -∗
    WP (ping #a #b) @[ip] {{ _, True }}.
  Proof.
    iIntros (-> ->) "#Hsi Hunallocated Hfree Ha Hγpong".
    unfold ping; wp_pures.
    wp_socket sh as "Hsh".
    wp_pures.
    iApply (aneris_wp_socket_interp_alloc_singleton (ping_si b) with "Hunallocated").
    iIntros "#Hping".
    wp_socketbind.
    wp_send "Hγpong".
    { iExists (ping_si _).
      iSplitR; [done | ].
      iLeft.
      iFrame.
      iSplitL; [ done | ].
      iIntros (m) "[Hbody Hγpong]".
      iFrame.
    }
    wp_pures.
    wp_apply (aneris_wp_receivefrom with "[$Hsh $Ha]"); [done.. | ].
    iIntros (m) "(Hdest & [Hm_in | Hm_notin])"; last first.
    { iDestruct "Hm_notin" as "[%abs _]". exfalso. set_solver. }
    iDestruct "Hm_in" as "(_ & Hsh & Ha & _ & Hping_m)".
    iDestruct "Hping_m" as "[-> Hγpong]".
    wp_apply wp_unSOME; first eauto.
    iIntros "_"; wp_let.
    wp_apply wp_assert.
    wp_pures.
    iSplit. { done. }
    iModIntro. wp_seq.
    wp_send "Hγpong".
    { iExists (ping_si _).
      iSplitR; [done | ].
      iRight.
      iFrame.
      done.
    }
   wp_seq. done.
  Qed.

  Definition pong_addr := SocketAddressInet "0.0.0.0" 80.
  Definition ping_addr := SocketAddressInet "0.0.0.1" 80.
  Definition addrs : gset socket_address := {[ pong_addr; ping_addr ]}.
  Definition ips : gset string :=
    {[ ip_of_address pong_addr ; ip_of_address ping_addr ]}.

  Lemma ping_pong_runner_spec :
    {{{ (* the pong server satisfies its socket interpretation *)
        pong_addr ⤇ pong_si
        ∗ pong_addr ⤳ (∅, ∅)
        ∗ ping_addr ⤳ (∅, ∅)
        (* A contain static addresses, and the ips we use are free *)
        ∗ unallocated {[ping_addr]}
        ∗ ([∗ set] ip ∈ ips, free_ip ip)
        ∗ last_message γpong NONE ∗ last_message γpong NONE }}}
    ping_pong_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(#Hsi & Hponga & Hpinga & Hunallocated & Hips & Hγpong & Hγpong') HΦ".
    unfold ping_pong_runner.
    iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "(Hpong & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "(Hping & _)";
      first set_solver.
    wp_pures.
    wp_apply aneris_wp_start; first done.
    iFrame.
    iSplitR "Hγpong Hponga"; last first.
    { iIntros "!> Hfree".
      iApply (pong_spec with "[$] []"); done.
    }
    iModIntro.
    wp_seq.
    wp_apply aneris_wp_start; first done.
    iFrame.
    iSplitR "Hγpong' Hpinga Hunallocated"; last first.
    { iIntros "!> Hfree".
      iApply (ping_spec with "[$] Hunallocated [$] [$Hpinga] [$Hγpong']"); eauto.
    }
    iModIntro.
    iApply "HΦ".
    done.
  Qed.

End proof.
