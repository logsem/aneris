From trillium.prelude Require Import finitary.
From aneris.algebra Require Import disj_gsets.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From aneris.aneris_lang.lib Require Import pers_socket_proto network_util_proof.
From aneris.examples.echo_groups Require Export code.
From iris.base_logic.lib Require Import invariants.
Set Default Proof Using "Type".

Section echo.
  Context `{dG : anerisG Mdl Σ}.

  Axiom Do : gname → iProp Σ.
  Axiom Done : gname → iProp Σ.

  Axiom hist : gname → gset message → iProp Σ.
  Axiom hist_view : gname → gset message → iProp Σ.

  Axiom hist_alloc : ⊢ |==> ∃ γ, hist γ ∅.
  Axiom hist_grow : ∀ γ E H H', H ⊆ H' → hist γ H ={E}=∗ hist γ H'.
  Axiom hist_view_alloc : ∀ γ E H, hist γ H ={E}=∗ hist γ H ∗ hist_view γ H.
  Axiom hist_view_union : ∀ γ H H', hist_view γ (H ∪ H') -∗ hist_view γ H ∗ hist_view γ H'.
  Axiom hist_le : ∀ γ H H', hist γ H -∗ hist_view γ H' -∗ ⌜H' ⊆ H⌝.

  Axiom hist_view_persistent : ∀ γ H, Persistent (hist_view γ H).
  Existing Instance hist_view_persistent.

  Axiom hist_timeless : ∀ γ H, Timeless (hist γ H).
  Existing Instance hist_timeless.

  Axiom Do_Done_alloc :  ⊢ |==> ∃ γ, Do γ ∗ Done γ.
  Axiom Do_exclusive : ∀ γ, Do γ -∗ Do γ -∗ False.
  Axiom Done_exclusive : ∀ γ, Done γ -∗ Done γ -∗ False.

  Definition echo_inv (γe γh : gname) saT sagR : iProp Σ :=
    ∃ (R T: gset message),
      sagR ⤳* (R, T) ∗ hist γh R ∗ ⌜set_Forall (λ m, m_sender m = saT) R⌝ ∗
      ((⌜R = ∅⌝ ∗ ⌜T = ∅⌝ ∗ Done γe) ∨
       (∃ m, ⌜set_Exists (λ m', m ≡g{{[saT]},sagR} m') R⌝ ∗ ⌜T = ∅⌝ ∗
             Do γe ∗ Done γe) ∨
       (∃ m, ⌜set_Exists (λ m', m ≡g{{[saT]},sagR} m') R⌝ ∗
             ⌜set_Exists (λ m', udp_msg (m_destination m) (m_sender m) "done"
                                   ≡g{sagR,{[saT]}} m') T⌝ ∗ Do γe)).

  Definition server_si γ saT : socket_interp Σ  :=
    (λ msg, ⌜m_sender msg = saT⌝ ∗ Do γ)%I.

  Definition client_si γ : socket_interp Σ  :=
    (λ msg, Done γ)%I.

  Definition message_I : message :=
    {| m_sender := SocketAddressInet "" xH;
       m_destination := SocketAddressInet "" xH;
       m_protocol := IPPROTO_UDP;
       m_body := "" |}.

  (* TODO: Move this into aneris proper *)
  Instance message_inhabited : Inhabited message :=
    populate {| m_sender := SocketAddressInet "" xH;
                m_destination := SocketAddressInet "" xH;
                m_protocol := IPPROTO_UDP;
                m_body := "" |}.

  Lemma server_spec1 saR ip port Φ :
    ip = ip_of_address saR →
    port = port_of_address saR →
    free_ports ip {[port]} -∗
    (* post condition includes the newly allocated socket handler *)
    (∀ sh,
        sh ↪[ ip_of_address saR] RecordSet.set saddress
                                 (λ _ : option socket_address, Some saR)
                                 (udp_socket None true) -∗ Φ #(LitSocket sh)) -∗
    WP (server1 #saR) @[ip] {{ v, Φ v }}.
  Proof.
    iIntros (-> ->) "Hports HΦ".
    wp_lam.
    wp_socket h as "Hh".
    wp_let.  
    wp_apply (aneris_wp_socketbind_groups with "[$Hports $Hh]"); [set_solver..|].
    iIntros "Hh".
    wp_pures.
    by iApply "HΦ".
  Qed.

  (* TODO: Make spec with texan triple instead? *)
  Lemma server_spec2 sh saT saR sagR ip port N γe γi Φ :
    ip = ip_of_address saR →
    port = port_of_address saR →
    saR ∈g sagR -∗
    (* the group [sagR] is governed by the [server_si] socket protocol *)
    sagR ⤇* server_si γe saT -∗
    (* We are immediately aware of the protocol of the client [saT] *)
    saT ⤇1 client_si γe -∗
    inv N (echo_inv γe γi saT sagR) -∗
    sh ↪[ ip_of_address saR] RecordSet.set saddress
                                 (λ _ : option socket_address, Some saR)
                                 (udp_socket None true) -∗
    (∀ m, ⌜m_sender m = saT⌝ ∗ ⌜m_destination m = saR⌝ ∗
          sh ↪[ ip_of_address saR] RecordSet.set saddress
            (λ _ : option socket_address, Some saR)
            (udp_socket None true) ∗
            hist_view γi {[m]} -∗
            Φ (PairV (LitV $ LitString (m_body m))
                     (LitV $ LitSocketAddress (m_sender m)))) -∗
     WP (server2 #(LitSocket sh)) @[ip] {{ v, Φ v }}.
  Proof.
    iIntros (-> ->) "Hin #Hsag #HsaT #Hinv Hsh HΦ".
    wp_lam.
    wp_bind (ReceiveFrom _).
    iInv N as (R T) "(Hrt & Hhist & >%Hsender & H)".
    wp_apply (aneris_wp_receivefrom_groups with "[$Hin $Hsh $Hrt $Hsag]"); [set_solver..|].
    iIntros (m) "Hm".
    iDestruct "Hm" as (sagT Hdest) "(#[%Hsend HsagT] & Hh & Hrt & [[%Hrecv Hm] | %Hrecv])".
    {
      iDestruct "H" as "[H | H]".
      { iDestruct "H" as (-> ->) "HDone".
        iDestruct "Hm" as (m' Hmeq) "[_ [%Hin' HDo]]".
        iMod (hist_grow γi _ _ {[m]} with "Hhist") as "Hhist"; [set_solver|].
        iMod (hist_view_alloc with "Hhist") as "[Hhist #Hhist_view]".
        iModIntro. rewrite /server_si.
        iDestruct (socket_interp_own with "HsaT") as "HsaT'".
        assert (m_sender m' ∈ sagT).
        { by destruct Hmeq as (_ & Hin'' & _). }
        iDestruct (socket_address_group_own_agree with "HsagT HsaT'")
          as %->; [try set_solver..|].
        iSplitL "Hrt Hhist HDone HDo".
        { iExists _, _.
          assert (({[m]}:gset _) ∪ ∅ = ({[m]}:gset _)) as Heq by set_solver.
          rewrite Heq.
          iFrame "Hrt Hhist".
          iSplit.
          { iPureIntro. intros m'' Hm''. set_solver. }
          iRight. iLeft. iExists m.
          iFrame "HDone HDo".
          iPureIntro. split; [|set_solver].
          exists m. split;[set_solver|].
          apply message_group_equiv_refl; [done|].
          by destruct Hmeq as (_ & _ & Hin''' & _).
        }
        wp_apply wp_unSOME; [done|].
        iIntros "_".
        wp_pures.
        iApply "HΦ". iFrame. iSplit; [iPureIntro;set_solver|]. iSplit; done.
      }
      iDestruct "H" as "[H | H]".
      { iDestruct "H" as (m' HR HT) " (HDo & HDone)".
        iDestruct "Hm" as (msg' Hmeq') "[HsagR Hm]".
        iDestruct "Hm" as (Hin'') "Hm".
        iDestruct (Do_exclusive with "HDo Hm") as %[]. }
      iDestruct "H" as (m' HR HT) "HDo".
      iDestruct "Hm" as (msg' Hmeq') "[HsagR Hm]".
      iDestruct "Hm" as (Hin'') "Hm".
      iDestruct (Do_exclusive with "HDo Hm") as %[].
    }
    iDestruct "H" as "[H|H]".
    {
      iDestruct "H" as (-> ->) "_".
      by destruct Hrecv as [m' [Hin' _]].
    }
    iDestruct "H" as "[H|H]".
    {
      iDestruct "H" as (m' HR HT) "(HDo & HDone)".
      iMod (hist_grow _ _ R ({[m]} ∪ R) with "Hhist") as "Hhist"; [set_solver|].
      iMod (hist_view_alloc with "Hhist") as "[Hhist Hhist_view]".
      iDestruct (hist_view_union with "Hhist_view") as "[#Hhist_view _]".
      iModIntro.
      iDestruct (socket_interp_own with "HsaT") as "HsaT'".
      destruct Hrecv as [m'' [HnR Hmeq']].
      pose proof (Hsender m'' HnR).
      simpl in *.
      destruct Hmeq' as (_ & Hsend2 & _).
      iDestruct (socket_address_group_own_agree with "HsagT HsaT'")
        as %->; [set_solver..|].
      iSplitR "HΦ Hh".
      { iExists _, _. iFrame "Hrt Hhist".
        iNext.
        iSplit.
        { iPureIntro. intros m''' Hm''.
          apply elem_of_union in Hm''.
          destruct Hm'' as [Hm'' | Hm''];
            [set_solver | by apply Hsender]. }
        iRight. iLeft.
        iExists _.
        iSplit.
        { iPureIntro. by apply set_Exists_union_2. }
        iSplit; [done|].
        iFrame "HDo HDone". }
      wp_apply wp_unSOME; [done|].
      iIntros "_".
      wp_pures. iApply "HΦ".
      iSplit; [iPureIntro;set_solver|].
      iSplit; [done|].
        by iFrame.
    }
    iDestruct "H" as (m' HR HT) "HDo".
    iMod (hist_grow _ _ R ({[m]} ∪ R) with "Hhist") as "Hhist"; [set_solver|].
    iMod (hist_view_alloc with "Hhist") as "[Hhist Hhist_view]".
    iDestruct (hist_view_union with "Hhist_view") as "[#Hhist_view _]".
    iModIntro.
    iDestruct (socket_interp_own with "HsaT") as "HsaT'".
    destruct Hrecv as [m'' [HnR Hmeq']].
    pose proof (Hsender m'' HnR).
    simpl in *.
    destruct Hmeq' as (_ & Hsend2 & _).
    iDestruct (socket_address_group_own_agree with "HsagT HsaT'")
      as %->; [set_solver..|].
    iSplitR "HΦ Hh".
    { iExists _, _. iFrame "Hrt Hhist".
      iNext.
      iSplit.
      { iPureIntro. intros m''' Hm''.
        apply elem_of_union in Hm''.
        destruct Hm'' as [Hm'' | Hm'']; [set_solver | by apply Hsender]. }
      iRight. iRight.
      iExists _.
      iSplit.
      { iPureIntro. by apply set_Exists_union_2. }
      iSplit; [done|].
      iFrame "∗#". }
    wp_apply wp_unSOME; [done|].
    iIntros "_".
    wp_pures. iApply "HΦ".
    iSplit; [iPureIntro;set_solver|].
    iSplit; [done|].
      by iFrame.
  Qed.

  Lemma server_spec3 sh saT saR sagR ip port N γe γi m :
    ip = ip_of_address saR →
    port = port_of_address saR →
    m_sender m = saT →
    m_destination m = saR →
    saR ∈g sagR -∗
    sagR ⤇* server_si γe saT -∗
    inv N (echo_inv γe γi saT sagR) -∗
    saT ⤇1 client_si γe -∗
    hist_view γi {[m]} -∗
    sh ↪[ ip_of_address saR] RecordSet.set saddress
    (λ _ : option socket_address, Some saR)
    (udp_socket None true) -∗
    (* post condition is any predicate as [pong] does not terminate *)
    WP (server3 #(LitSocket sh)) (PairV (LitV $ LitString (m_body m))
                  (LitV $ LitSocketAddress (m_sender m))) @[ip]
    {{ v, True }}.
  Proof.
    iIntros (-> -> HinT HinR) "#HsagR #Hsag #Hinv #HsaT #Hview Hsh".
    iDestruct (elem_of_group_unfold with "HsagR") as "[%Hin _]".
    iAssert ( socket_address_group_own {[saT]} )%I as "#HownT".
    { iDestruct "HsaT" as (γ) "[$ _]". }
    wp_lam.
    simpl.
    wp_pures.
    iInv N as (R T) "(Hrt & >Hhist & >%Hsender & H)".
    iDestruct "H" as "[H|H]".
    {
      iDestruct "H" as "(>%HR & >HT & H)".
      iPoseProof (hist_le with "Hhist Hview") as "%Hle".
      set_solver.
    }
    iDestruct "H" as "[H|H]".
    {
      iDestruct "H" as (m'')  "(>%HR & >%HT & HDo & HDone)".
      wp_apply (aneris_wp_send_groups
                  _ _ _ _ _ _ _ _ _ _ _ _ _
                  (udp_msg (m_destination m) (m_sender m) _)
                  with "[$Hsh $Hrt $HsaT $HsagR HDone]"); [try set_solver..|].
      { subst. eapply message_group_equiv_refl; set_solver. }
      { iSplit.
        - iSplit; [ iNext; iPureIntro ; set_solver | done  ].
        - iNext. done. }
      iIntros "[Hsh Hrt]".
      iModIntro.
      iSplit; [|done].
      iIntros "!>". iExists _, _.
      iFrame "Hrt Hhist".
      iSplit; [done|].
      iRight. iRight. iExists m''.
      iSplit; [done|].
      iFrame "HDo".
      iPureIntro.
      exists (udp_msg saR (m_sender m) "done").
      split; [set_solver|].
      destruct HR as [m''' [Hmin' Hmeq']].
      destruct Hmeq' as (Hsend12 & Hsend22 & Hdest12 & Hdest22 & _).
      split; [set_solver|].
      split; [set_solver|].
      split; [set_solver|].
      split; [set_solver|].
      split; [set_solver|].
      done.
    }
    iDestruct "H" as (m'') "(>%HR & >%HT & HDo)".
    wp_apply (aneris_wp_send_duplicate_groups with "[$Hsh $Hrt $HsaT]");
      [ try set_solver.. |].
    { destruct HT as [mT' [HinT' HmeqT]].
      exists mT'.
      split; [done|].
      destruct HR as [m''' [Hmin' Hmeq']].
      destruct Hmeq' as (Hsend12 & Hsend22 & Hdest12 & Hdest22 & Hprot2 & Hbody2).
      destruct HmeqT as (Hsend1T & Hsend2T & Hdest1T & Hdest2T & Hprot3 & Hbody3).
      split; [set_solver|].
      split; [set_solver|].
      split; [set_solver|].
      split; [set_solver|].
      split; [set_solver|].
      done. }
    { iSplit; [ done | ].
      iSplit; [ iPureIntro; set_solver | done ]. }
    iIntros "[Hsh Hrt]".
    iModIntro.
    iSplit; [|done].
    iExists _, _. iFrame "Hrt Hhist".
    iSplit; [done|].
    iRight. iRight.
    iExists m''.
    iSplit; [done|].
    iFrame "HDo".
    iPureIntro.
    exists (udp_msg saR (m_sender m) "done").
    split; [set_solver|].
    destruct HR as [m''' [Hmin' Hmeq']].
    destruct Hmeq' as (Hsend12 & Hsend22 & Hdest12 & Hdest22 & _).
    split; [set_solver|].
    split; [set_solver|].
    split; [set_solver|].
    split; [set_solver|].
    split; [set_solver|].
    done.
  Qed.

  Lemma server_spec saT saR sagR ip port N γe γi :
    ip = ip_of_address saR →
    port = port_of_address saR →
    saR ∈g sagR -∗
    sagR ⤇* server_si γe saT -∗
    free_ports ip {[port]} -∗
    saT ⤇1 client_si γe -∗
    inv N (echo_inv γe γi saT sagR) -∗
    WP (server #saR) @[ip] {{ v, True }}.
  Proof.
    iIntros (-> ->) "#Hin #Hsag Hports #HsaT #Hinv".
    wp_lam.
    wp_bind (server1 #saR).
    wp_apply (server_spec1 with "Hports"); [set_solver..|].
    iIntros (sh) "Hsh".
    wp_pures.
    wp_bind (server2 _).
    wp_apply (server_spec2 with "Hin Hsag HsaT Hinv Hsh"); [set_solver..|].
    iIntros (m) "(%Hsender & %Hdest & Hsh & Hhist)".
    wp_pures.
    wp_apply (server_spec3 with "Hin Hsag Hinv HsaT Hhist Hsh"); set_solver.
  Qed.

  Lemma client_spec (saT saR1 saR2 : socket_address)
        (sagR : socket_address_group) ip port γe Φ :
    ip = ip_of_address saT →
    port = port_of_address saT →
    saR1 ∈g sagR -∗
    saR2 ∈g sagR -∗
    saT ⤇1 client_si γe -∗
    sagR ⤇* server_si γe saT -∗
    Do γe -∗
    free_ports ip {[port]} -∗
    saT ⤳1 (∅,∅) -∗
    (Done γe -∗ Φ) -∗
    WP (client #saT #saR1 #saR2) @[ip] {{ v, Φ }}.
  Proof.
    iIntros (-> ->) "#HsaRin1 #HsaRin2 #HsaT #HsagR HDo Hports Hrt HΦ".
    iAssert (saT ∈g {[saT]}) as "HsaT'".
    { iSplit; [iPureIntro;set_solver | ].
      iDestruct "HsaT" as (γ) "[$ _]". }
    iDestruct (elem_of_group_unfold with "HsaRin1") as "[%HsaRin1 _]".
    iDestruct (elem_of_group_unfold with "HsaRin2") as "[%HsaRin2 _]".
    wp_lam.
    wp_pures.
    wp_socket h as "Hsh".
    wp_pures.
    wp_apply (aneris_wp_socketbind_groups with "[$Hports $Hsh]"); [set_solver..|].
    iIntros "Hsh".
    wp_pures.
    wp_apply (aneris_wp_send_groups _ _ _ _ saT {[saT]} saR1 sagR
                with "[$Hsh $Hrt $HsagR $HsaRin1 $HsaT' HDo]"); [try set_solver..|].
    { apply message_group_equiv_refl; set_solver. }
    { rewrite /server_si. eauto. }
    iIntros "[Hsh Hrt]".
    wp_pures.
    wp_apply (aneris_wp_send_duplicate_groups _ _ _ saT
                with "[$Hsh $Hrt $HsagR $HsaRin2 $HsaT']"); [try set_solver..|].
    { simpl. exists (udp_msg saT saR1 "do").
      split; [set_solver|]. rewrite /message_group_equiv. set_solver. }
    iIntros "[Hsh Hrt]".
    wp_pures.
    wp_apply (aneris_wp_receivefrom_groups _ saT {[saT]}
                with "[$Hsh $Hrt $HsaT $HsaT']"); [set_solver..|].
    iIntros (m) "H".
    iDestruct "H" as (sagT Hdest) "([Hsend Hown] & Hsh & Hrt & Hm)".
    wp_apply wp_unSOME; [done|].
    iIntros "_".
    wp_pures.
    iApply "HΦ".
    iDestruct "Hm" as "[Hm|%Hm]".
    { iDestruct "Hm" as (Hall) "(%m' & Hmeq & _ & $)". }
    destruct Hm as [m' [Hmin _]].
    set_solver.
  Qed.

  Definition client_addr := SocketAddressInet "0.0.0.0" 80.
  Definition server_addr1 := SocketAddressInet "0.0.0.1" 80.
  Definition server_addr2 := SocketAddressInet "0.0.0.2" 80.
  Definition server_addrs : socket_address_group :=
    {[ server_addr1 ; server_addr2 ]}.
  Definition ips : gset string :=
    {[ ip_of_address client_addr ;
     ip_of_address server_addr1 ; ip_of_address server_addr2 ]}.

  Lemma echo_runner_spec γ :
    {{{  (* the pong server satisfies its socket interpretation *)
         Do γ ∗
         Done γ ∗
         client_addr ⤇1 client_si γ ∗
         server_addrs ⤇* server_si γ client_addr ∗
         client_addr ⤳1 (∅, ∅) ∗
         server_addrs ⤳* (∅, ∅) ∗
         (* A contain static addresses, and the ips we use are free *)
         [∗ set] ip ∈ ips, free_ip ip }}}
      echo_runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(HDo & HDone & #Hcsi & #Hssi & Hclienta & Hservera & Hips) Hcont".
    rewrite /echo_runner.
    iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "(Hclient & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "(Hserver1 & Hips)";
      first set_solver.
    iDestruct (big_sepS_delete _ _ "0.0.0.2" with "Hips") as "(Hserver2 & Hips)";
      first set_solver.
    wp_pures.
    (* TODO: Move this to adequacy? *)
    iAssert (server_addr1 ∈g server_addrs)%I as "#Hserver_valid1".
    { iSplit; [iPureIntro;set_solver|].
      iDestruct "Hssi" as (γ') "[$ _]". }
    iAssert (server_addr2 ∈g server_addrs)%I as "#Hserver_valid2".
    { iSplit; [iPureIntro;set_solver|].
      iDestruct "Hssi" as (γ') "[$ _]". }
    wp_apply (aneris_wp_start {[80%positive : port]}); eauto.
    iFrame. iSplitR "Hclienta HDo"; last first.
    { iIntros "!> Hp".
      iApply (client_spec with "Hserver_valid1 Hserver_valid2
      Hcsi Hssi HDo Hp Hclienta");
        [set_solver..|].
      by iIntros "_". }
    iModIntro.
    iMod (hist_alloc) as (γh) "Hhist".
    iMod (inv_alloc (nroot .@ "") ⊤ (echo_inv γ γh client_addr server_addrs)
            with "[Hservera HDone Hhist]") as "#Hinv".
    { iExists _, _. iFrame "Hservera Hhist".
      iSplit; [done|].
      by iLeft; eauto. }
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive : port]}); eauto.
    iFrame. iSplitL; last first.
    { iIntros "!> Ha".
       by iApply (server_spec with "Hserver_valid1 Hssi Ha Hcsi Hinv"); set_solver. }
    iIntros "!>".
    wp_pures.
    wp_apply (aneris_wp_start {[80%positive : port]}); eauto.
    iFrame. iSplitL; last first.
    {
      iIntros "!> Ha".
       by iApply (server_spec with "Hserver_valid2 Hssi Ha Hcsi Hinv"); set_solver. }
    by iApply "Hcont".
  Qed.

End echo.

Definition echo_is :=
  {|
    state_heaps :=  {["system" := ∅ ]};
    state_sockets := {["system" := ∅ ]};
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $ <["0.0.0.1" := ∅ ]> $ <["0.0.0.2" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition unit_model := model _ (λ _ _, False) ().
Lemma unit_model_rel_finitary : aneris_model_rel_finitary unit_model.
Proof. intros ?. apply finite_smaller_card_nat. apply _. Qed.

(* The static/fixed domain contains only the adress of the pong server *)
Definition fixed_dom : gset socket_address_group :=
  {[ {[client_addr]} ; server_addrs ]}.

Lemma all_disjoint_fixed_dom : all_disjoint fixed_dom.
Proof.
  rewrite /fixed_dom.
  rewrite -all_disjoint_union.
  split; [apply all_disjoint_singleton|].
  split; [apply all_disjoint_singleton|].
  apply have_disj_elems_singleton.
  intros x Hx.
  apply elem_of_singleton in Hx.
  subst.
  set_solver.
Qed.

Theorem echo_safe :
  aneris_adequate echo_runner "system" echo_is (λ _, True).
Proof.
  set (Σ := #[anerisΣ unit_model]).
  apply (adequacy_groups Σ _ ips fixed_dom ∅ ∅ ∅);
    try set_solver.
  { apply all_disjoint_fixed_dom. }
  { apply set_Forall_union; apply set_Forall_singleton; set_solver. }
  { apply unit_model_rel_finitary. }
  { iIntros (dinvG).
    iIntros "!> Hf Hhist Hfrag Hips Hlbl _ _ _ _".
    iMod Do_Done_alloc as (γ) "[HDo HDone]".
    rewrite big_sepS_union; [|set_solver].
    rewrite !big_sepS_singleton.
    iDestruct (unfixed_groups_split with "Hf") as "[Hf1 Hf2]"; [set_solver|].
    iApply (aneris_wp_socket_interp_alloc_group (client_si γ) with "Hf1").
    iIntros "Hclt".
    iApply (aneris_wp_socket_interp_alloc_group (server_si γ client_addr)
             with "Hf2").
    iIntros "Hsrv".
    iDestruct "Hhist" as "[Hhistc Hhists]".
    wp_apply (echo_runner_spec with "[$]"); [try set_solver..|eauto]. }
  rewrite /ips /fixed_dom.
  intros sag sa Hsag Hsa.
  apply elem_of_union in Hsag.
  destruct Hsag as [Hsag|Hsag]; apply elem_of_singleton in Hsag; set_solver.
Qed.
