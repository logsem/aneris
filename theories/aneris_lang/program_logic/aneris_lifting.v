From iris.proofmode Require Import tactics.
From iris.program_logic Require Export lifting.
From aneris.aneris_lang Require Export lifting_pure.
From aneris.aneris_lang Require Import lang basic_lifting.
From aneris.aneris_lang Require Export ground_lang.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.
From RecordUpdate Require Import RecordSet.

Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section lifting_pure_exec.
  Context `{distG Σ}.

  Implicit Types ip : ip_address.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.

  Lemma aneris_wp_pure_step_fupd ip E E' e1 e2 φ n Φ :
    PureExec φ n (mkExpr ip e1) (mkExpr ip e2) →
    φ →
    (|={E}[E']▷=>^n WP e2 @[ip] E {{ Φ }}) ⊢ WP e1 @[ip] E {{ Φ }}.
  Proof.
    rewrite (aneris_wp_unfold _ _ e1) /aneris_wp_def.
    iIntros (Hexec Hφ) "Hwp #Hin".
    iApply (wp_pure_step_fupd _ _ E'); first done.
    clear φ Hφ e1 Hexec.
    iInduction n as [|n] "IH"; simpl.
    - rewrite aneris_wp_unfold /aneris_wp_def.
      iApply "Hwp"; done.
    - iMod "Hwp"; iModIntro; iNext; iMod "Hwp"; iModIntro.
      iApply ("IH" with "Hwp"); eauto.
  Qed.

  Lemma aneris_wp_pure_step_later ip E e1 e2 φ n Φ :
    PureExec φ n (mkExpr ip e1) (mkExpr ip e2) →
    φ →
    ▷^n WP e2 @[ip] E {{ Φ }} ⊢ WP e1 @[ip] E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -aneris_wp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

End lifting_pure_exec.

Section lifting_network_local.
  Context `{distG Σ}.

  Implicit Types ip : ip_address.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.

  (** Fork *)
  Lemma aneris_wp_fork ip E e Φ :
    ▷ Φ #() ∗ ▷ WP e @[ip] ⊤ {{ _, True }} ⊢ WP Fork e @[ip] E {{ Φ }}.
  Proof.
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "[HΦ Hwp] Hin".
    iApply wp_fork.
    iSplitL "HΦ"; first by eauto.
    iNext.
    iApply wp_wand_r; iSplitL; first by iApply "Hwp".
    auto.
  Qed.

  (** Heap *)
  Lemma aneris_wp_alloc ip E v :
    {{{ True }}} Alloc (Val v) @[ip] E {{{ l, RET #l; l ↦[ip] v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    iApply wp_alloc; first done.
    iNext.
    iIntros (l) "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_load ip E l q v :
    {{{ ▷ l ↦[ip]{q} v }}} Load #l @[ip] E {{{ RET v; l ↦[ip]{q} v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    iApply (wp_load with "Hl").
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_store ip E l v' v :
  {{{ ▷ l ↦[ip] v' }}} Store #l (Val v) @[ip] E {{{ RET #(); l ↦[ip] v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    iApply (wp_store with "Hl").
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_cas_fail ip E l q v' v1 v2 :
    v' ≠ v1 →
    {{{ ▷ l ↦[ip]{q} v' }}}
      CAS #l (Val v1) (Val v2) @[ip] E
    {{{ RET #false; l ↦[ip]{q} v' }}}.
  Proof.
    iIntros (Hneq Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    iApply (wp_cas_fail with "Hl"); first done.
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_cas_suc ip E l v1 v2 :
    {{{ ▷ l ↦[ip] v1 }}}
      CAS #l (Val v1) (Val v2) @[ip] E
    {{{ RET #true; l ↦[ip] v2 }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    iApply (wp_cas_suc with "Hl").
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

End lifting_network_local.

Section lifting_network_aware.
  Context `{distG Σ}.

  Implicit Types ip : ip_address.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types e : expr.

  (** Weakest Precondition rules for Network-aware steps *)
  Lemma aneris_wp_start ip ports E e Ψ :
    ip ≠ "system" →
    ▷ FreeIP ip ∗
    ▷ Ψ (mkVal "system" #()) ∗
    ▷ (FreePorts ip ports -∗ WP e @[ip] ⊤ {{ _, True }}) ⊢
    WP (mkExpr "system" (Start (LitString ip) e)) @ E {{ Ψ }}.
  Proof.
    iIntros (Hip) "(Hip & HΦ & He)".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iApply wp_start; first done.
    iFrame.
    iNext.
    iIntros "Hin Hfp".
    iApply wp_wand_r; iSplitL; first iApply ("He" with "Hfp Hin").
    done.
  Qed.

  Lemma aneris_wp_new_socket ip E v1 v2 v3 :
  {{{ True }}}
    NewSocket
    (Val $ LitV $ LitAddressFamily v1)
    (Val $ LitV $ LitSocketType v2)
    (Val $ LitV $ LitProtocol v3) @[ip] E
  {{{ h, RET (LitV (LitSocket h));
      h s↦[ip]{1/2} ({| sfamily := v1;
                       stype := v2;
                       sprotocol := v3;
                       saddress := None |}, ∅, ∅) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    iApply wp_new_socket; first done.
    iNext.
    iIntros (h) "?".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_socketbind_static ip A E sh skt a:
    ip_of_address a = ip →
    saddress skt = None →
    a ∈ A →
    {{{ Fixed A ∗
        ▷ FreePorts ip {[(port_of_address a)]} ∗
        ▷ sh s↦[ip]{1/2} (skt, ∅, ∅) }}}
      SocketBind
      (Val $ LitV $ LitSocket sh)
      (Val $ LitV $ LitSocketAddress a) @[ip] E
    {{{ RET #0;
        sh s↦[ip]{1/2} (skt <| saddress := Some a |>, ∅, ∅) ∗ ∃ φ, a ⤇ φ }}}.
  Proof.
    iIntros (Hip Hskt Ha Φ) "(HA & Hfp & Hsh) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_socketbind_static with "[$HA $Hfp $Hsh]"); [done|done|].
    iNext.
    iIntros "(Hsh & Hproto)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_socketbind_dynamic ip s A E sh a φ :
    ip_of_address a = ip →
    saddress s = None →
    a ∉ A →
    {{{ ▷ Fixed A ∗
        ▷ FreePorts (ip_of_address a) {[port_of_address a]} ∗
        ▷ sh s↦[ip]{1/2} (s, ∅, ∅) }}}
      SocketBind
      (Val $ LitV $ LitSocket sh)
      (Val $ LitV $ LitSocketAddress a) @[ip] E
  {{{ RET #0; sh s↦[ip]{1/2} (s <| saddress := Some a |>, ∅, ∅) ∗ a ⤇ φ }}}.
  Proof.
    iIntros (Hip Hskt Ha Φ) "(HA & Hfp & Hsh) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_socketbind_dynamic with "[$HA $Hfp $Hsh]"); [done|done|].
    iNext.
    iIntros "(Hsh & Hproto)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send ip φ m sh a f E s R T :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_protocol := sprotocol s;
          m_body := m;
        |} in
    {{{ ▷ sh s↦[ip]{1/2} (s, R, T) ∗ a ⤇ φ ∗ φ msg }}}
      SendTo (Val $ LitV $ LitSocket sh) #m #a @[ip] E
    {{{ RET #(String.length m); sh s↦[ip]{1/2} (s, R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (Hip Hskt msg Φ) "(Hsh & Hproto & Hmsg) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_send with "[$Hsh $Hproto $Hmsg]"); first done.
    iNext.
    iIntros "Hsh".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send_duplicate ip m sh a f E s R T:
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_protocol := sprotocol s;
          m_body := m;
        |} in
    msg ∈ T →
    {{{ ▷ sh s↦[ip]{1/2} (s, R, T) }}}
      SendTo (Val $ LitV $ LitSocket sh) #m #a @[ip] E
    {{{ RET #(String.length m); sh s↦[ip]{1/2} (s, R, T) }}}.
   Proof.
    iIntros (Hip Hskt msg Hmsg Φ) "Hsh HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_send_duplicate with "[$Hsh]"); [done|done|].
    iNext.
    iIntros "Hsh".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
   Qed.

   Lemma aneris_wp_receive_from_gen
         (Ψo : option (socket_interp Σ)) ip a E h s R T :
     ip_of_address a = ip →
    saddress s = Some a →
    {{{ ▷ h s↦[ip]{1/2} (s, R, T) ∗ match Ψo with Some Ψ => a ⤇ Ψ | _ => True end }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h s↦[ip]{1/2} (s, R, T)) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h s↦[ip]{1/2} (s, {[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
            ⌜msg ∈ R⌝ ∗ h s↦[ip]{1/2} (s, R, T))))
    }}}.
   Proof.
     iIntros (Hip Hskt Φ) "Hshprot HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_receive_from_gen with "[$Hshprot]"); first done.
    iNext.
    iIntros (r) "Hr".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
   Qed.

   Lemma aneris_wp_receive_from ip a E h s R T :
    ip_of_address a = ip →
    saddress s = Some a →
    {{{ ▷ h s↦[ip]{1/2} (s, R, T) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h s↦[ip]{1/2} (s, R, T)) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h s↦[ip]{1/2} (s, {[ msg ]} ∪ R, T) ∗
             ∃ φ, a ⤇ φ ∗ φ msg) ∨ ⌜msg ∈ R⌝ ∗ h s↦[ip]{1/2} (s, R, T)))) }}}.
  Proof.
    iIntros (Hip Hs Φ) "Hsh HΦ".
    iApply (aneris_wp_receive_from_gen None with "[$]"); [done|done|].
    iNext.
    iIntros (r) "Hr".
    iApply "HΦ"; eauto.
  Qed.

  Lemma aneris_wp_receive_from_2 ip a E sh s R T φ :
    ip_of_address a = ip →
    saddress s = Some a →
    {{{ ▷ sh s↦[ip]{1/2} (s, R, T) ∗ a ⤇ φ }}}
      ReceiveFrom (Val $ LitV $ LitSocket sh) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ sh s↦[ip]{1/2} (s, R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh s↦[ip]{1/2} (s, {[ msg ]} ∪ R, T) ∗ φ msg) ∨
            ⌜msg ∈ R⌝ ∗ sh s↦[ip]{1/2} (s, R, T))
    }}}.
   Proof.
    iIntros (Hip Hs Φ) "Hsh HΦ".
    iApply (aneris_wp_receive_from_gen (Some φ) with "[$]"); [done|done|].
    iNext.
    iIntros (r) "Hr".
    iApply "HΦ"; eauto.
   Qed.

End lifting_network_aware.
