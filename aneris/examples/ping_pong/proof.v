From trillium.prelude Require Import finitary.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy.
From aneris.aneris_lang.lib Require Import pers_socket_proto network_util_proof.
From aneris.examples.ping_pong Require Export code.
Set Default Proof Using "Type".

Section pong.
  Context `{dG : anerisG Mdl Σ}.

  (* The socket interpretation is abstracting over any message received through
     the socket and is a predicate on all received messages. *)
  Definition pong_si : socket_interp Σ  :=
    (λ msg,
     (* client is governed by a protocol and the message body is PING *)
     ∃ ϕ, m_sender msg ⤇ ϕ ∗ ⌜m_body msg = "PING"⌝
          (* client's protocol is satisfied with a PONG response *)
          ∗ (<pers> ∀ m, ⌜m_body m = "PONG"⌝ → ϕ m))%I.

  Lemma pong_spec a ip port A R T:
    ip = ip_of_address a →
    port = port_of_address a →
    (* a is static *)
    a ∈ A →
    (* the address [a] is governed by the pong_si socket protocol *)
    a ⤇ pong_si -∗
    (* A should contain static addresses & the port should be free *)
    fixed A -∗
    free_ports ip {[port]} -∗
    (* exclusive ownership of the [a] and its sent and received messages *)
    a @ pong_si ⤳# (R, T) -∗
    WP (pong #a) @[ip] {{ v, True }}.
  Proof.
    iIntros (-> -> Haddr) "#Hsi #Hfixed Hport Ha".
    wp_lam.
    wp_socket h as "Hh".
    wp_let.
    wp_socketbind_static.
    wp_apply (aneris_wp_pers_receivefrom with "[$Hsi $Hh $Ha]"); [done..|].
    iIntros (m) "(Hh & Ha & Hm)".
    wp_lam.
    wp_pures.
    iDestruct "Hm" as (Ψ) "(#HΨ & -> & #Hresp)".
    wp_pures.
    wp_apply (aneris_wp_pers_send with "[$Hh $Ha $HΨ]"); [done..| |].
    { iApply "Hresp". iIntros "!> /=". done. }
    iIntros "[Hh Ha]".
    auto.
  Qed.

End pong.

Section ping.
  Context `{dG : anerisG Mdl Σ}.

  Definition ping_si : socket_interp Σ :=
    (λ msg, ⌜m_body msg = "PONG"⌝)%I.

  Lemma ping_spec a b ip port A :
    ip = ip_of_address a →
    port = port_of_address a →
    (* the pong address is static *)
    b ∈ A ->
    (* the ping is not*)
    a ∉ A ->
    {{{ (* the [pong] address is governed by [pong_si] *)
         b ⤇ pong_si
        ∗ fixed A
        ∗ free_ports ip {[port]}
        ∗ a ⤳ (∅, ∅) }}}
      ping #a #b @[ip]
    {{{ v, RET v; ∃ m, ⌜v = #"PONG"⌝ ∗ ⌜v = #(m_body m)⌝ ∗
                        a ⤳ ({[m]}, {[ mkMessage a b IPPROTO_UDP "PING" ]})}}}.
  Proof.
    iIntros (-> -> Hserver Haddr Φ) "(#Hsi & #Hfixed & Hip & Ha) Hcont".
    wp_lam. wp_let.
    wp_socket sh as "Hsh".
    wp_let.
    wp_socketbind_dynamic ping_si as "#Hping".
    wp_pures.
    wp_send.
    { iExists _. eauto. }
    wp_seq.
    wp_apply (aneris_wp_receivefrom with "[$Ha $Hping $Hsh]"); try auto.
    iIntros (m) "[%Hdest [Hd | Hd]]".
    2: { iDestruct "Hd" as "[% _]". set_solver. }
    wp_lam. wp_pures. iApply "Hcont". iExists m.
    iDestruct "Hd" as "(_ & _ & Ha & _ & ->)".
    rewrite !right_id_L. iFrame. auto.
  Qed.

End ping.

Section ping_pong_runner.
  Context `{dG : anerisG Mdl Σ}.

  Definition pong_addr := SocketAddressInet "0.0.0.0" 80.
  Definition ping_addr := SocketAddressInet "0.0.0.1" 80.
  Definition addrs : gset socket_address := {[ pong_addr; ping_addr ]}.
  Definition ips : gset string :=
    {[ ip_of_address pong_addr ; ip_of_address ping_addr ]}.

  Lemma ping_pong_runner_spec (A : gset socket_address) :
    (* the pong address is static *)
    pong_addr ∈ A ->
    (* the ping adress is not *)
    ping_addr ∉ A ->
    {{{  (* the pong server satisfies its socket interpretation *)
         pong_addr ⤇ pong_si
         ∗ pong_addr ⤳ (∅, ∅)
         ∗ ping_addr ⤳ (∅, ∅)
         (* A contain static addresses, and the ips we use are free *)
         ∗ fixed A
         ∗ [∗ set] ip ∈ ips, free_ip ip }}}
      ping_pong_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (server client Φ) "(#Hsi & Hponga & Hpinga & #Hfix & Hips) Hcont".
    rewrite /ping_pong_runner.
    iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "(Hpong & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "(Hping & Hips)";
      first set_solver.
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive : port]}); eauto.
    iFrame. iSplitR "Hponga"; last first.
    { iIntros "!> Hp".
      iPoseProof (mapsto_messages_pers_alloc _ pong_si with "Hponga []") as "Ha".
      { done. }
      by iApply (pong_spec with "Hsi Hfix Hp Ha"). }
    iModIntro. wp_pures.
    wp_apply (aneris_wp_start {[80%positive : port]}); eauto.
    iFrame. iSplitR "Hpinga"; last first.
    { iIntros "!> Ha".
      iApply (ping_spec with "[$Ha $Hpinga] []"); eauto. }
    by iApply "Hcont".
  Qed.

End ping_pong_runner.

Definition ping_pong_is :=
  {|
    state_heaps :=  {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $ <["0.0.0.1" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat; apply _. Qed. 

(* map of all static socket interpretations *)
Definition socket_interp `{!anerisG empty_model Σ} sa : socket_interp Σ :=
  (match sa with
  | SocketAddressInet "0.0.0.0" 80 => pong_si (* pong *)
  | _ => λ msg, ⌜True⌝
   end)%I.

(* The static/fixed domain contains only the adress of the pong server *)
Definition fixed_dom : gset socket_address := {[ pong_addr ]}.

Theorem ping_pong_safe :
  aneris_adequate ping_pong_runner "system" ping_pong_is (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model]).
  apply (adequacy_hoare Σ _ ips fixed_dom addrs ∅ ∅ ∅);
    [..|done|set_solver|set_solver|set_solver|done|done|done].
  { apply unit_model_rel_finitary. }
  iIntros (dinvG). iExists socket_interp.
  iIntros (?) "!# (#Hf & #Hsi & Hhist & _ & Hips & _) HΦ".
  rewrite /fixed_dom big_sepS_singleton.
  rewrite /addrs (big_sepS_delete _ _ pong_addr); [|set_solver].
  rewrite (big_sepS_delete _ _ ping_addr); [|set_solver].
  iDestruct "Hhist" as "(Hpong & Hping & _)".
  wp_apply (ping_pong_runner_spec with "[$] [$]"); set_solver.
Qed.
