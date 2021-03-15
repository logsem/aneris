From iris.proofmode Require Import tactics.
From aneris.program_logic Require Export weakestpre lifting.
From aneris.aneris_lang Require Import lang base_lang lifting state_interp.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre atomic.
From RecordUpdate Require Import RecordSet.

Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Section lifting_pure_exec.
  Context `{anerisG Mdl Σ}.

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

Section lifting_mdl.
  Context `{anerisG Mdl Σ}.

  Lemma aneris_wp_atomic_take_step_model ip Φ e E1 E2
        `{!Atomic WeaklyAtomic (mkExpr ip e)} :
    TCEq (to_val e) None →
    (|={E1,E2}=> ∃ m m', ⌜Mdl m m'⌝ ∗ frag_st m ∗
     WP e @[ip] E2 {{ v, frag_st m' ={E2,E1}=∗ Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
  Proof.
    iIntros (He) "H".
    iApply (aneris_wp_atomic_take_step ip E1 E2).
    iMod "H" as "H".
    iModIntro. iIntros (σ1 κs n δ1) "Hsi".
    iDestruct "H" as (m m') "(%Htrans&Hm&Hwp)".
    iDestruct (aneris_state_interp_model_agree with "Hsi Hm") as "%Heq".
    iModIntro. iExists ({| aneris_AS_mhist := δ1.(aneris_AS_mhist);
                           aneris_AS_model := m' |}).
    iExists (frag_st m')%I.
    iFrame "Hsi".
    iSplitR "Hwp Hm".
    - iIntros (σ2 δ3 κ n') "(Hsi&%Hval&Hst)".
      iDestruct (aneris_state_interp_model_agree with "Hsi Hst") as "%Heq'".
      unfold valid_state_evolution in *. simpl in *.
      destruct Hval as [Hvalh Hvalm].
      iModIntro. iPureIntro. split; eauto.
      rewrite Heq Heq'. right; done.
    - iFrame "Hwp". iIntros "Hsi".
      iMod (aneris_state_interp_model with "Hsi Hm").
      iModIntro. iFrame.
  Qed.

End lifting_mdl.

Section lifting_node_local.
  Context `{anerisG Mdl Σ}.

  Implicit Types ip : ip_address.
  Implicit Types P : iProp Σ.
  Implicit Types Ψ Φ : val → iProp Σ.
  Implicit Types v : val.
  Implicit Types e : expr.
  Implicit Types σ : state.
  Implicit Types M R T : message_soup.
  Implicit Types m : message.
  Implicit Types A B : gset socket_address.
  Implicit Types a : socket_address.
  Implicit Types sh : socket_handle.
  Implicit Types skt : socket.

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

End lifting_node_local.

Section lifting_network.
  Context `{anerisG Mdl Σ}.

  Implicit Types ip : ip_address.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types e : expr.

  (** Network *)
  Lemma aneris_wp_start ports ip E e Ψ :
    ip ≠ "system" →
    ports ≠ ∅ →
    ▷ free_ip ip ∗ ▷ Ψ #() ∗
    ▷ (free_ports ip ports -∗
       ([∗ set] p ∈ ports, SocketAddressInet ip p ⤳ (∅, ∅)) -∗
       WP e @[ip] ⊤ {{ _, True }}) ⊢
    WP (Start (LitString ip) e) @["system"] E {{ Ψ }}.
  Proof.
    iIntros (Hip Hp) "(Hip & HΦ & He)".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    iApply wp_start; [done|done|].
    iFrame.
    iSplitL "HΦ".
    { iNext. iExists _. eauto. }
    iNext.
    iIntros "Hin' Hfp Hms".
    iApply wp_wand_r; iSplitL; first iApply ("He" with "Hfp Hms Hin'").
    done.
  Qed.

  Lemma aneris_wp_new_socket ip E v1 v2 v3 :
    {{{ True }}}
      NewSocket
      (Val $ LitV $ LitAddressFamily v1)
      (Val $ LitV $ LitSocketType v2)
      (Val $ LitV $ LitProtocol v3) @[ip] E
    {{{ h, RET (LitV (LitSocket h));
        h ↪[ip] (mkSocket v1 v2 v3 None true) }}}.
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

  Lemma aneris_wp_socketbind_static ip A E h s a :
    ip_of_address a = ip →
    saddress s = None →
    a ∈ A →
    {{{ ▷ fixed A ∗
        ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ h ↪[ip_of_address a] s }}}
      SocketBind
      (Val $ LitV $ LitSocket h)
      (Val $ LitV $ LitSocketAddress a) @[ip] E
    {{{ RET #0;
        h ↪[ip_of_address a] (s<| saddress := Some a |>) ∗
        ∃ φ, a ⤇ φ }}}.
  Proof.
    iIntros (Hip Hskt Ha Φ) "(>HA & Hfp & Hsh) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_socketbind_static with "[$HA $Hfp $Hsh]"); [done|done|].
    iNext.
    iIntros "(Hsh & Hproto)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_socketbind_dynamic ip s A E h a φ :
    ip_of_address a = ip →
    saddress s = None →
    a ∉ A →
    {{{ ▷ fixed A ∗
        ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ h ↪[ip_of_address a] s
    }}}
      SocketBind
      (Val $ LitV $ LitSocket h)
      (Val $ LitV $ LitSocketAddress a) @[ip] E
    {{{ RET #0;
        h ↪[ip_of_address a] (s <| saddress := Some a |>) ∗
        a ⤇ φ }}}.
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

  Lemma aneris_wp_send ip φ m h a f E s R T :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_protocol := sprotocol s;
          m_body := m;
        |} in
    {{{ ▷ h ↪[ip] s ∗ ▷ f ⤳ (R, T) ∗ ▷ a ⤇ φ ∗ ▷ φ msg }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m);
        h ↪[ip] s ∗ f ⤳ (R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (Hip Hskt msg Φ) "(Hsh & Hm & Hproto & Hmsg) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_send with "[$Hsh $Hm $Hproto $Hmsg]"); first done.
    iNext.
    iIntros "(Hsh & Hm)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send_duplicate ip m h a f E s R T:
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := mkMessage f a (sprotocol s) m in
    msg ∈ T →
    {{{ ▷ h ↪[ip] s ∗ ▷ f ⤳ (R, T) }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ f ⤳ (R, T) }}}.
  Proof.
    iIntros (Hip Hskt msg Hmsg Φ) "(Hsh & Hm) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_send_duplicate with "[$Hsh $Hm]"); [done|done|].
    iNext.
    iIntros "(Hsh & Hm)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_nb_gen
        (Ψo : option (socket_interp Σ)) ip a E h s R T :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip_of_address a] s ∗
        ▷ a ⤳ (R, T) ∗
        match Ψo with Some Ψ => a ⤇ Ψ | _ => True end }}}
      (ReceiveFrom (Val $ LitV $ LitSocket h)) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳ (R, T) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗
             match Ψo with Some Ψ => Ψ msg | _ => ∃ φ, a ⤇ φ ∗ φ msg end) ∨
            ⌜msg ∈ R⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳ (R, T))))) }}}.
  Proof.
    iIntros (Hip Hskt Hblock Φ) "Hshprot HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_receivefrom_nb_gen with "[$Hshprot]"); [done|done|].
    iNext.
    iIntros (r) "Hr".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
   Qed.

  Lemma aneris_wp_receivefrom_nb ip a E h s R T :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗
             ∃ φ, a ⤇ φ ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "(Hsh & Hm) HΦ".
    rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen None with "[$]");  eauto.
  Qed.

  Lemma aneris_wp_receivefrom_alt ip a E sh s R T φ :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ sh ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ }}}
      ReceiveFrom (Val $ LitV $ LitSocket sh) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ sh ↪[ip] s ∗ a ⤳ (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
            ⌜msg ∈ R⌝ ∗ sh ↪[ip] s ∗ a ⤳ (R, T)) }}}.
   Proof.
     iIntros (Hip Hs Hb Φ) "Hsh HΦ". rewrite -Hip.
     iApply (aneris_wp_receivefrom_nb_gen (Some φ) with "[$]"); eauto.
   Qed.

   Lemma aneris_wp_receivefrom ip a E h s R T φ :
     ip_of_address a = ip →
     saddress s = Some a →
     sblock s = true →
     {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
       ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
     {{{ m, RET SOMEV (PairV #(m_body m) #(m_sender m));
         ⌜m_destination m = a⌝ ∗
         ((⌜m ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
          ⌜m ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) }}}.
   Proof.
     iIntros (<- Haddr Hblk Φ) "(>Hsh & >Ha & #Hsi) HΦ".
     rewrite !aneris_wp_unfold /aneris_wp_def.
     iIntros "#Hin". iApply (wp_receivefrom with "[$Hsh $Ha]"); eauto.
     iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
     iApply "HΦ"; iFrame.
   Qed.

   Lemma aneris_wp_receivefrom_gen ip a E h s R T φ :
     ip = ip_of_address a →
     saddress s = Some a →
     {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ}}}
       ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
     {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)) }}}.
   Proof.
     iIntros (-> Haddr Φ) "(>Hsh & >Ha & #Hsi) HΦ".
     rewrite !aneris_wp_unfold /aneris_wp_def.
     iIntros "#Hin". iApply (wp_receivefrom_gen with "[$Hsh $Ha]"); eauto.
     iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
     iApply "HΦ"; iFrame.
   Qed.

   Lemma aneris_wp_rcvtimeo_unblock ip a E h s n1 n2 :
     ip_of_address a = ip →
     saddress s = Some a →
     (0 <= n1 ∧ 0 <= n2 ∧ 0 < n1 + n2)%Z →
     {{{ ▷ h ↪[ip] s }}}
       SetReceiveTimeout
       (Val $ LitV $ LitSocket h)
       (Val $ LitV $ LitInt n1)
       (Val $ LitV $ LitInt n2) @[ip] E
     {{{ RET #(); h ↪[ip] s<|sblock := false|> }}}.
   Proof.
     iIntros (Hip Hskt Hcnd Φ) "Hsh HΦ".
     rewrite !aneris_wp_unfold /aneris_wp_def.
     iIntros "#Hin".
     rewrite -Hip.
     iApply (wp_rcvtimeo_unblock _ a E h s n1 n2 with "[$Hsh]"); [done|done|].
     iNext. iIntros "Hsh". iExists _; iSplit; first done. iApply "HΦ"; iFrame.
   Qed.

  Lemma aneris_wp_rcvtimeo_block ip a E h s :
    ip_of_address a = ip →
    saddress s = Some a →
    {{{ ▷ h ↪[ip] s }}}
      SetReceiveTimeout
      (Val $ LitV $ LitSocket h)
      (Val $ LitV $ LitInt 0)
      (Val $ LitV $ LitInt 0) @[ip] E
    {{{ RET #(); h ↪[ip] s<|sblock := true|> }}}.
  Proof.
    iIntros (Hip Hskt Φ) "Hsh HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "#Hin".
    rewrite -Hip.
    iApply (wp_rcvtimeo_block _ a E h s with "[$Hsh]"); [done|].
    iNext. iIntros "Hsh". iExists _; iSplit; first done. iApply "HΦ"; iFrame.
  Qed.

End lifting_network.
