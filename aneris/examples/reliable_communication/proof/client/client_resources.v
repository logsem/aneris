From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap agree auth numbers frac_auth.
From iris.algebra.lib Require Import excl_auth mono_nat.
(* From iris.base_logic.lib Require Import invariants mono_nat saved_prop. *)
(* From stdpp Require Import namespaces countable. *)
From aneris.aneris_lang.lib.serialization Require Export serialization_proof.
From aneris.aneris_lang.lib Require Import network_util_code.
From aneris.aneris_lang.lib Require Import pers_socket_proto.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.aneris_lang Require Import proofmode.
From aneris.examples.reliable_communication Require Import
     client_server_code user_params.
From aneris.examples.reliable_communication.resources Require Import
     chan_session_resources socket_interp.

From actris.channel Require Export proto.
From stdpp Require Import base tactics telescopes.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Section Client_resources.
  Context `{!anerisG Mdl Σ, !chanG Σ}.
  Context `{!Reliable_communication_service_params}.
  Context `{!server_ghost_names}.

  Definition isClientSocketInternal skt s h sa bflag R T : iProp Σ :=
    RCParams_srv_saddr ⤇ server_interp ∗
      isSocket skt s h sa client_interp bflag Left ∗
      sa ⤳ (R, T) ∗
      (* The property below just allows to avoid more precise reasoning
           about the connection STS. *)
      [∗ set] m ∈ R, client_server_interp_pers Left m.

  Definition conn_incoming_msg_cond_1 clt_addr (R : gset message) : iProp Σ :=
    ∀ (m : message) (n : nat),
    ⌜m_sender m = RCParams_srv_saddr⌝ -∗
    ⌜m_destination m = clt_addr⌝ -∗
    ⌜s_is_ser (msg_serialization RCParams_srv_ser)
     (InjLV (#"INIT-ACK", #n)) (m_body m)⌝ -∗
    (⌜m ∉ R⌝ ∨ (⌜m ∈ R⌝ ∗ CookieRes clt_addr n)).

  Definition conn_incoming_msg_cond_2 clt_addr (R : gset message) : iProp Σ :=
    ∀ (m : message) (n : nat),
    ⌜m_sender m = RCParams_srv_saddr⌝ -∗
    ⌜m_destination m = clt_addr⌝ -∗
    ⌜s_is_ser (msg_serialization RCParams_srv_ser)
     (InjLV (#"COOKIE-ACK", #n)) (m_body m)⌝ -∗
    (⌜m ∉ R⌝ ∨
    (⌜m ∈ R⌝ ∗ ∃ γ, can_init γ clt_addr RCParams_protocol Left)).


  Lemma conn_incoming_msg_cond_1_extend
        clt_addr (m : message) (R0 : message_soup) (i2 : nat) :
    m_destination m = clt_addr →
    m_sender m = RCParams_srv_saddr →
    (⌜s_is_ser (msg_serialization RCParams_srv_ser) (InjLV (#"COOKIE-ACK", #i2)) (m_body m)⌝ ∨
     (∃ v, ⌜s_is_ser (msg_serialization RCParams_srv_ser) (InjRV v) (m_body m)⌝) ∨
    ⌜s_is_ser (msg_serialization RCParams_srv_ser) (InjLV (#"INIT-ACK", #i2)) (m_body m)⌝ ∗
    CookieRes clt_addr i2) -∗
    conn_incoming_msg_cond_1 clt_addr R0 -∗
    conn_incoming_msg_cond_1 clt_addr ({[m]} ∪ R0).
  Proof.
    iIntros (Hdst Hsnd) "Hser Hcnd2".
    iIntros (m0 n0 Hm1 Hm2 Hm3).
    iDestruct ("Hcnd2" $! m0 n0 Hm1 Hm2 Hm3) as "[%Hcnd|(%Hcnd & Hcnd2)]".
    { destruct (bool_decide (m0 = m)) eqn:Hmm.
      - apply bool_decide_eq_true_1 in Hmm as ->.
        iRight. iSplit; first by iPureIntro; set_solver.
        iDestruct "Hser" as "[%Hser|[(%v & %Hser)|(%Hser & Hres)]]".
        + specialize (msg_ser_is_ser_injective Right (m_body m) _ _ Hser Hm3) as Hinj.
          inversion Hinj as ((Hstr & Hvn)).
        + specialize (msg_ser_is_ser_injective Right (m_body m) _ _ Hser Hm3) as Hinj.
          inversion Hinj as ((Hstr & Hvn)).
        + specialize (msg_ser_is_ser_injective Right (m_body m) _ _ Hser Hm3) as Hinj.
          inversion Hinj as (Hi). by apply Nat2Z.inj_iff in Hi as ->.
      - destruct (bool_decide (m0 ∈ R0)) eqn:HmR.
        + by apply bool_decide_eq_true_1 in HmR.
        + iLeft. iPureIntro. apply bool_decide_eq_false_1 in Hmm. set_solver. }
    iRight. iSplit; first by iPureIntro; set_solver. eauto with iFrame.
  Qed.

  Lemma conn_incoming_msg_cond_2_extend
        clt_addr (m : message) (R0 : message_soup) (i2 : nat) :
    m_destination m = clt_addr →
    m_sender m = RCParams_srv_saddr →
    (⌜s_is_ser (msg_serialization RCParams_srv_ser) (InjLV (#"INIT-ACK", #i2)) (m_body m)⌝ ∨
     (∃ v, ⌜s_is_ser (msg_serialization RCParams_srv_ser) (InjRV v) (m_body m)⌝) ∨
     ⌜s_is_ser (msg_serialization RCParams_srv_ser) (InjLV (#"COOKIE-ACK", #i2)) (m_body m)⌝ ∗
       ∃ γ, can_init γ clt_addr RCParams_protocol Left) -∗
    conn_incoming_msg_cond_2 clt_addr R0 -∗
    conn_incoming_msg_cond_2 clt_addr ({[m]} ∪ R0).
  Proof.
    iIntros (Hdst Hsnd) "Hser Hcnd2".
    iIntros (m0 n0 Hm1 Hm2 Hm3).
    iDestruct ("Hcnd2" $! m0 n0 Hm1 Hm2 Hm3) as "[%Hcnd|(%Hcnd & Hcnd2)]".
    { destruct (bool_decide (m0 = m)) eqn:Hmm.
      - apply bool_decide_eq_true_1 in Hmm as ->.
        iRight. iSplit; first by iPureIntro; set_solver.
        iDestruct "Hser" as "[%Hser|[(%v & %Hser)|(_ & Hres)]]".
        + specialize (msg_ser_is_ser_injective Right (m_body m) _ _ Hser Hm3) as Hinj.
          inversion Hinj as ((Hstr & Hvn)).
        + specialize (msg_ser_is_ser_injective Right (m_body m) _ _ Hser Hm3) as Hinj.
          inversion Hinj as ((Hstr & Hvn)).
        + eauto with iFrame.
      - destruct (bool_decide (m0 ∈ R0)) eqn:HmR.
        + by apply bool_decide_eq_true_1 in HmR.
        + iLeft. iPureIntro. apply bool_decide_eq_false_1 in Hmm. set_solver. }
    iRight. iSplit; first by iPureIntro; set_solver. eauto with iFrame.
  Qed.

Lemma resend_listen_spec ip P Q h s R T a mt handler φ ψ :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = false →
    m_sender mt = a →
    (∀ mr,
      {{{ ⌜m_destination mr = a⌝ ∗ P ∗
          ((⌜mr ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[mr]} ∪ R, {[mt]} ∪ T) ∗ φ mr) ∨
           (⌜mr ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, {[mt]} ∪ T)))
      }}}
         (Val handler) #(m_body mr) #(m_sender mr) @[ip]
      {{{ v, RET v; Q v }}}) -∗
      {{{ P ∗ h ↪[ip] s ∗ a ⤳ (R, {[mt]} ∪ T) ∗
          a ⤇ φ ∗ (m_destination mt) ⤇ ψ }}}
         resend_listen
         #(LitSocket h) #(m_destination mt) #(m_body mt) (Val handler) @[ip]
      {{{ v, RET v; Q v }}}.
  Proof.
     iIntros (n Haddr Hsblock Hsender) "#Hhandler".
     iModIntro. iIntros (Φ) "(HP & Hsocket & Hmh & #Hsi & #Hdstsi) HΦ".
     rewrite /resend_listen.
     do 10 (wp_pure _).
     iLöb as "IH".
     wp_rec.
     wp_bind (ReceiveFrom _).
     wp_apply (aneris_wp_receivefrom_alt with "[$]"); [done|done|done|].
     iIntros (r) "[(-> & Hs & Hh) | Hrd ]"; simpl.
     - wp_pures.
        wp_apply (aneris_wp_send_duplicate with "[$Hs $Hh $Hdstsi]");
          [done | done |  | ].
       + assert ( {|
                    m_sender := a;
                    m_destination := m_destination mt;
                    m_protocol := sprotocol s;
                    m_body := m_body mt  |} = mt) as ->.
         { rewrite -Hsender. by destruct mt, m_protocol, sprotocol; simpl. }
         set_solver.
       + iIntros "(Hs & Hm)".
         do 6 (wp_pure _).
         iApply ("IH" with "[$HP][$Hs][$Hm][$HΦ]").
     - iDestruct "Hrd" as (m Hdst ->) "[ (% & Hs & Hφ) | (% & Hs) ]"; wp_pures;
         wp_apply ("Hhandler" with "[-HΦ] [HΦ]"); eauto with iFrame.
  Qed.

End Client_resources.
