From iris.proofmode Require Import tactics.
From trillium.program_logic Require Export weakestpre lifting.
From aneris.aneris_lang.state_interp Require Import state_interp_def.
From aneris.aneris_lang Require Import lang base_lang state_interp lifting.
From aneris.aneris_lang.program_logic Require Export aneris_weakestpre.
From RecordUpdate Require Import RecordSet.

Set Default Proof Using "Type".

Import uPred.

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
    iIntros (Hexec Hφ) "Hwp %tid #Hin".
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

  Lemma aneris_wp_atomic_take_step_model_alt m m' e ip E Φ
        `{!Atomic WeaklyAtomic (mkExpr ip e)} :
    TCEq (to_val e) None →
    frag_st m ∗ ⌜m = m' ∨ Mdl m m'⌝ ∗
    WP e @[ip] E {{ v, frag_st m' -∗ Φ v }} ⊢ WP e @[ip] E {{ Φ }}.
  Proof.
    iIntros (?) "(Hfrag & % & Hwp)".
    iApply (aneris_wp_atomic_take_step).
    iModIntro. iIntros (ex atr c1 Hex) "Hsi".
    iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %Heq.
    iModIntro.
    iExists (True)%I, (frag_st m')%I.
    iFrame "Hsi".
    iSplitR "Hwp".
    - iIntros (c2 δ2 [] ?).
      iExists m', tt.
      iIntros "(Hsi&_)".
      iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %<-.
      iMod (aneris_state_interp_model_extend with "Hsi Hfrag [//] [//]") as "[? ?]".
      iModIntro; iFrame; simplify_eq/=; done.
    - iSplitR; [by iFrame; iIntros "$"|].
      iApply aneris_wp_mono; last by iApply "Hwp".
      iIntros (v) "H Hf !#". by iApply "H".
  Qed.

  Lemma aneris_wp_atomic_take_step_model ip Φ e E1 E2
        `{!Atomic WeaklyAtomic (mkExpr ip e)} :
    TCEq (to_val e) None →
    (|={E1,E2}=>
     ∃ m m', frag_st m ∗ ⌜m = m' ∨ Mdl m m'⌝ ∗
     WP e @[ip] E2 {{ v, frag_st m' ={E2,E1}=∗ Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
  Proof.
    iIntros (?) "H".
    iMod "H" as (??) "(Hm & % & Hwp)".
    iApply aneris_wp_atomic_take_step_model_alt.
    by iFrame.
  Qed.

  Lemma aneris_wp_suttering_atomic_take_step_model ip Φ e E1 E2
        `{!StutteringAtomic WeaklyAtomic (mkExpr ip e)} :
    TCEq (to_val e) None →
    (|={E1,E2}=>
     ∃ m m', frag_st m ∗ ⌜m = m' ∨ Mdl m m'⌝ ∗
     WP e @[ip] E2 {{ v, frag_st m' ={E2,E1}=∗ Φ v }}) ⊢ WP e @[ip] E1 {{ Φ }}.
  Proof.
    iIntros (He) "H".
    iApply (aneris_wp_stuttering_atomic_take_step ip E1 E2).
    iMod "H" as "H".
    iModIntro. iIntros (ex atr c1 Hex) "Hsi".
    iDestruct "H" as (m m') "(Hfrag & %Hm & Hwp)".
    iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %Heq.
    iModIntro.
    iExists (True)%I, (frag_st m')%I.
    iFrame "Hsi".
    iSplitR "Hwp".
    - iIntros (c2 δ2 ? ?).
      iExists m'.
      iIntros "(Hsi&_)".
      iDestruct (aneris_state_interp_model_agree with "Hsi Hfrag") as %<-.
      iMod (aneris_state_interp_model_extend _ _ _ atr with "Hsi Hfrag [//] [//]") as "[? ?]".
      iModIntro; iFrame; simplify_eq/=; done.
    - iSplitR; [by iFrame; iIntros "$"|]. by iApply "Hwp".
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
    iIntros "[HΦ Hwp] %tid Hin".
    iApply wp_fork.
    iSplitL "HΦ"; first by eauto.
    iIntros (?). iNext.
    iApply wp_wand_r; iSplitL; first by iApply "Hwp".
    auto.
  Qed.

  (** Heap *)
  Lemma aneris_wp_alloc ip E v :
    {{{ True }}} ref (Val v) @[ip] E {{{ l, RET #l; l ↦[ip] v }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply wp_alloc; first done.
    iNext.
    iIntros (l) "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_alloc_tracked ip E v lbl evs :
    {{{ ▷ alloc_evs lbl evs }}}
      ref<<lbl>> (Val v) @[ip] E
    {{{ l h (σ : state), RET #l; l ↦[ip] v ∗
          ⌜valid_allocObs ip l σ h⌝ ∗ alloc_evs lbl (evs ++ [allocObs ip lbl l v σ h]) }}}.
  Proof.
    iIntros (Φ) "Hevs HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply (wp_alloc_tracked with "[$]").
    iNext.
    iIntros (l h σ) "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_load ip E l q v :
    {{{ ▷ l ↦[ip]{q} v }}} Load #l @[ip] E {{{ RET v; l ↦[ip]{q} v }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
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
    iIntros "%tid #Hin".
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
    iIntros "%tid #Hin".
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
    iIntros "%tid #Hin".
    iApply (wp_cas_suc with "Hl").
    iNext.
    iIntros "Hl".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_rand ip E u :
    {{{ ⌜(0 < u)⌝%Z }}}
      Rand #u @[ip] E
    {{{ (r : Z), RET #r; ⌜r >= 0 ∧ r < u⌝%Z }}}.
  Proof.
    iIntros (Φ) "#Hgt HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply wp_rand; [iFrame "#" |].
    iModIntro.
    iIntros (r) "%Hineq".
    iExists #r. iSplitL ""; [done |].
    iApply "HΦ". done.
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
    ▷ free_ip ip ∗ ▷ Ψ #() ∗
    ▷ (free_ports ip ports -∗ WP e @[ip] ⊤ {{ _, True }}) ⊢
    WP (Start (LitString ip) e) @["system"] E {{ Ψ }}.
  Proof.
    iIntros (Hip) "(Hip & HΦ & He)".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply wp_start; [done|].
    iFrame.
    iSplitL "HΦ".
    { iNext. iExists _. eauto. }
    iNext.
    iIntros "%tid' Hin' Hfp".
    iApply wp_wand_r; iSplitL; first iApply ("He" with "Hfp Hin'").
    done.
  Qed.

  Lemma aneris_wp_new_socket ip E :
    {{{ True }}}
      NewSocket #() @[ip] E
    {{{ h, RET (LitV (LitSocket h));
          h ↪[ip] (mkSocket None true) }}}.
  Proof.
    iIntros (Φ) "Hl HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply wp_new_socket; first done.
    iNext.
    iIntros (h) "?".
    iExists _; iSplit; first done.
    iApply "HΦ"; done.
  Qed.

  Lemma aneris_wp_socketbind_groups ip E h s sa :
    ip_of_address sa = ip →
    saddress s = None →
    {{{ ▷ free_ports (ip_of_address sa) {[port_of_address sa]} ∗
        ▷ h ↪[ip_of_address sa] s }}}
      SocketBind
      (Val $ LitV $ LitSocket h)
      (Val $ LitV $ LitSocketAddress sa) @[ip] E
    {{{ RET #0;
        h ↪[ip_of_address sa] (s<| saddress := Some sa |>) }}}.
  Proof.
    iIntros (Hip Hskt Φ) "(Hfp & Hsh) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_socketbind_groups with "[$Hfp $Hsh]"); [done..|].
    iNext.
    iIntros "Hsh".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_socketbind ip E h s a :
    ip_of_address a = ip →
    saddress s = None →
    {{{ ▷ free_ports (ip_of_address a) {[port_of_address a]} ∗
        ▷ h ↪[ip_of_address a] s }}}
      SocketBind
      (Val $ LitV $ LitSocket h)
      (Val $ LitV $ LitSocketAddress a) @[ip] E
    {{{ RET #0;
        h ↪[ip_of_address a] (s<| saddress := Some a |>) }}}.
  Proof. intros. apply aneris_wp_socketbind_groups; try set_solver. Qed.

  Lemma aneris_wp_send_groups ip φ m h saT sagT saR sagR rtrck E s R T m' :
    ip_of_address saT = ip →
    saddress s = Some saT ->
    let msg := {|
          m_sender := saT;
          m_destination := saR;
          m_body := m;
        |} in
    msg ≡g{sagT,sagR} m' →
    {{{ ▷ saT ∈g sagT ∗ ▷ saR ∈g sagR ∗
        ▷ h ↪[ip] s ∗ ▷ sagT ⤳*[false, rtrck] (R, T) ∗ ▷ sagR ⤇* φ ∗ ▷ φ m' }}}
      SendTo (Val $ LitV $ LitSocket h) #m #saR @[ip] E
    {{{ RET #(String.length m);
        h ↪[ip] s ∗ sagT ⤳*[false, rtrck] (R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (Hip Hskt msg Hmeq Φ) "(HinR & HinT & Hsh & Hm & Hproto & Hmsg) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_groups with "[$]"); [done..|].
    iNext.
    iIntros "(Hsh & Hm)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send ip φ m h a f rtrck E s R T :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_body := m;
        |} in
    {{{ ▷ h ↪[ip] s ∗ ▷ f ⤳[false, rtrck] (R, T) ∗ ▷ a ⤇ φ ∗ ▷ φ msg }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m);
        h ↪[ip] s ∗ f ⤳[false, rtrck] (R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (Hip Hs msg Φ) "(Hsh & [Hrt Hown] & Hφ & Hmsg) HΦ".
    iDestruct (messages_mapsto_observed with "Hrt") as "[Hrt (%r & %t & _ & _ & #Hf & _)]".
    iAssert (▷ socket_address_group_own {[a]})%I with "[Hφ]" as "#Howna".
    { iDestruct ("Hφ") as (γ) "[$ _]". }
    iApply (aneris_wp_send_groups with "[$Hsh $Hrt $Hφ $Hmsg] [HΦ Hown]"); try set_solver.
    { apply message_group_equiv_refl; set_solver. }
    { iFrame "#". iPureIntro; set_solver. }
    iNext. iIntros "[Hip Hrt]". by iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send_duplicate_groups ip m h saT sagT saR sagR rtrck E s R T φ :
    ip_of_address saT = ip →
    saddress s = Some saT ->
    let msg := mkMessage saT saR m in
    set_Exists (λ m, m≡g{sagT,sagR} msg) T →
    {{{ ▷ saT ∈g sagT ∗ ▷ saR ∈g sagR ∗
        ▷ h ↪[ip] s ∗ ▷ sagT ⤳*[false, rtrck] (R, T) ∗ sagR ⤇* φ }}}
      SendTo (Val $ LitV $ LitSocket h) #m #saR @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ sagT ⤳*[false, rtrck] (R, {[msg]} ∪ T) }}}.
  Proof.
    iIntros (Hip Hskt msg Hmsg Φ) "(HinT & HinR & Hsh & Hm & Hφ) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_duplicate_groups with "[$HinT $HinR $Hsh $Hm $Hφ]");
      [done..| ].
    iNext.
    iIntros "(Hsh & Hm)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send_duplicate ip m h a f rtrck E s R T φ :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := mkMessage f a m in
    msg ∈ T →
    {{{ ▷ h ↪[ip] s ∗ ▷ f ⤳[false, rtrck] (R, T) ∗ ▷ a ⤇ φ }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ f ⤳[false, rtrck] (R, T) }}}.
  Proof.
    iIntros (Hip Hsa msg Hin Φ) "(Hsh & Hrt & Hφ) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_duplicate with "[$]"); [set_solver..|].
    iIntros "!> [Hsh Hrt]".
    iExists _. iSplit; [done|]. iApply "HΦ". iFrame.
  Qed.

  Lemma aneris_wp_send_tracked_groups ip φ m h saT sagT saR sagR rtrck s E R T evs
        (Ψ1 Ψ2 : state → iProp Σ) m' :
    ip_of_address saT = ip →
    let msg := mkMessage saT saR m in
    msg ≡g{sagT,sagR} m' →
    saddress s = Some saT ->
    {{{ ▷ saT ∈g sagT ∗
        ▷ saR ∈g sagR ∗
        ▷ h ↪[ip_of_address saT] s ∗
        ▷ sagT ⤳*[true, rtrck] (R, T) ∗
        ▷ sagR ⤇* φ ∗
        ▷ φ m' ∗
        ▷ sendon_evs_groups sagT evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      SendTo (Val $ LitV $ LitSocket h) #m #saR @[ip] E
    {{{ RET #(String.length m);
        h ↪[ip_of_address saT] s ∗
        sagT ⤳*[true, rtrck] (R, {[ msg ]} ∪ T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs saT st h skts s r⌝ ∗
          sendon_evs_groups sagT (evs ++ [sendonObs saT st h (m_body msg) saR s]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs saT st h (m_body msg) saR s).(post_state) }}}.
  Proof.
    iIntros (Hip msg Hmeq Hskt Φ) "(>#HinT & >#HinR & Hsh & Hm & Hproto & Hmsg & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_tracked_groups with "[$]"); [try done..|].
    iNext.
    iIntros "(Hsh & Hm & Hevs)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send_tracked ip φ m h a f rtrck s E R T evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := {|
          m_sender := f;
          m_destination := a;
          m_body := m;
        |} in
    {{{ ▷ h ↪[ip_of_address f] s ∗
        ▷ f ⤳[true, rtrck] (R, T) ∗
        ▷ a ⤇ φ ∗
        ▷ φ msg ∗
        ▷ sendon_evs f evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m);
        h ↪[ip_of_address f] s ∗
        f ⤳[true, rtrck] (R, {[ msg ]} ∪ T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs f st h skts s r⌝ ∗
          sendon_evs f (evs ++ [sendonObs f st h (m_body msg) a s]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs f st h (m_body msg) a s).(post_state) }}}.
  Proof.
    iIntros (Hip Hskt msg Φ) "(Hsh & Hm & Hproto & Hmsg & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_tracked with "[$]"); [try done..|].
    iNext.
    iIntros "(Hsh & Hm & Hevs)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send_duplicate_tracked_groups ip m h saT sagT saR sagR E rtrck s
        R T evs (Ψ1 Ψ2 : state → iProp Σ) φ :
    ip_of_address saT = ip →
    saddress s = Some saT ->
    let msg := mkMessage saT saR m in
    set_Exists (λ m, m ≡g{sagT,sagR} msg) T →
    {{{ ▷ saT ∈g sagT ∗
        ▷ saR ∈g sagR ∗
        ▷ h ↪[ip] s ∗
        ▷ sagT ⤳*[true, rtrck] (R, T) ∗
        ▷ sagR ⤇* φ ∗
        ▷ sendon_evs_groups sagT evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      SendTo (Val $ LitV $ LitSocket h) #m #saR @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ sagT ⤳*[true, rtrck] (R, {[msg]} ∪ T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs saT st h skts s r⌝ ∗
          sendon_evs_groups sagT (evs ++ [sendonObs saT st h (m_body msg) saR s]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs saT st h (m_body msg) saR s).(post_state) }}}.
  Proof.
    iIntros (Hip Hskt msg Hmsg Φ)
            "(HsagT & HsagR & Hsh & Hm & Hφ & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_duplicate_tracked_groups with "[$]"); [done..|].
    iNext.
    iIntros "(Hsh & Hm & Hevs)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_send_duplicate_tracked ip m h a f E rtrck s R T evs (Ψ1 Ψ2 : state → iProp Σ) φ :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := mkMessage f a m in
    msg ∈ T →
    {{{ ▷ h ↪[ip] s ∗
        ▷ f ⤳[true, rtrck] (R, T) ∗
        ▷ a ⤇ φ ∗
        ▷ sendon_evs f evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      SendTo (Val $ LitV $ LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ f ⤳[true, rtrck] (R, T) ∗
        ∃ st skts r,
          ⌜valid_sendonObs f st h skts s r⌝ ∗
          sendon_evs f (evs ++ [sendonObs f st h (m_body msg) a s]) ∗
          Ψ1 st ∗ Ψ2 (sendonObs f st h (m_body msg) a s).(post_state) }}}.
  Proof.
    iIntros (Hip Hskt msg HinT Φ) "(Hsh & Hproto & Hφ & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_send_duplicate_tracked with "[$]"); [try done..|].
    iNext.
    iIntros "(Hsh & Hm & Hevs)".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_nb_gen_groups
        (Ψo : option (socket_interp Σ)) ip saR sagR E h s R T :
    ip_of_address saR = ip →
    saddress s = Some saR →
    sblock s = false →
    {{{ ▷ saR ∈g sagR ∗
        ▷ h ↪[ip_of_address saR] s ∗
        ▷ sagR ⤳* (R, T) ∗
        match Ψo with Some Ψ => sagR ⤇* Ψ | _ => True end }}}
      (ReceiveFrom (Val $ LitV $ LitSocket h)) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ h ↪[ip_of_address saR] s ∗ sagR ⤳* (R, T) ∨
        (∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          h ↪[ip_of_address saR] s ∗ sagR ⤳* ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m', ¬ msg ≡g{sagT, sagR} m') R⌝ ∗
             ∃ msg', ⌜msg ≡g{sagT,sagR} msg'⌝ ∗
                     match Ψo with Some Ψ => Ψ msg' | _ => ∃ φ, sagR ⤇* φ ∗ φ msg' end) ∨
            ⌜set_Exists (λ m', msg ≡g{sagT,sagR} m') R⌝))) }}}.
  Proof.
    iIntros (Hip Hskt Hblock Φ) "(HsagR & Hsh & Hrt & Hφ) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    rewrite -Hip.
    iIntros "%tid #Hin".
    iApply (wp_receivefrom_nb_gen_groups with "[$HsagR $Hsh $Hrt Hφ]"); [done..|].
    iNext.
    iIntros (r) "Hr".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_nb_groups ip sa sag E h s R T :
    ip_of_address sa = ip →
    saddress s = Some sa →
    sblock s = false →
    {{{ ▷ sa ∈g sag ∗ ▷ h ↪[ip] s ∗ ▷ sag ⤳* (R, T) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ sag ⤳* (R, T))) ∨
        (∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = sa⌝ ∗
          m_sender msg ∈g sagT ∗
          h ↪[ip] s ∗ sag ⤳* ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m' : message, ¬ msg ≡g{sagT, sag} m') R⌝ ∗
            (∃ msg' : message,
                ⌜msg ≡g{sagT, sag} msg'⌝
                 ∗ (∃ φ : socket_interp Σ, sag ⤇* φ ∗ φ msg'))) ∨
           ⌜set_Exists (λ m' : message, msg ≡g{sagT, sag} m') R⌝)) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "(Hsag & Hsh & Hm) HΦ".
    rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen_groups None with "[$]");  eauto.
  Qed.

  Lemma aneris_wp_receivefrom_nb ip a E h s R T φ :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip] s ∗ ▷ a ⤳ (R, T) ∗ a ⤇ φ }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T))) }}}.
  Proof.
    iIntros (Hip Hskt Hblock Φ) "Hshprot HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_receivefrom_nb_gen with "[$Hshprot]"); [done|done|].
    iNext.
    iIntros (r) "Hr".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_alt_group ip sa sag E sh s R T φ :
    ip_of_address sa = ip →
    saddress s = Some sa →
    sblock s = false →
    {{{ ▷ sa ∈g sag ∗ ▷ sh ↪[ip] s ∗ ▷ sag ⤳* (R, T) ∗ sag ⤇* φ }}}
      ReceiveFrom (Val $ LitV $ LitSocket sh) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ sh ↪[ip] s ∗ sag ⤳* (R, T)) ∨
        ∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = sa⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ip] s ∗ sag ⤳* ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m' : message, ¬ msg ≡g{sagT, sag} m') R⌝ ∗
            (∃ msg' : message,
                ⌜msg ≡g{sagT, sag} msg'⌝ ∗ φ msg')) ∨
           ⌜set_Exists (λ m' : message, msg ≡g{sagT, sag} m') R⌝) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "Hsh HΦ". rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen_groups (Some φ) with "[$]"); eauto.
  Qed.

  Lemma aneris_wp_receivefrom_groups ip sa sag E h s R T φ :
    ip_of_address sa = ip →
    saddress s = Some sa →
    sblock s = true →
    {{{ ▷ sa ∈g sag ∗ ▷ h ↪[ip] s ∗ ▷ sag ⤳* (R, T) ∗ sag ⤇* φ}}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ m, RET SOMEV (PairV #(m_body m) #(m_sender m));
          ∃ sagT,
          ⌜m_destination m = sa⌝ ∗
          m_sender m ∈g sagT ∗
          h ↪[ip] s ∗ sag ⤳* ({[ m ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m' : message, ¬ m ≡g{sagT, sag} m') R⌝ ∗
            (∃ msg' : message, ⌜m ≡g{sagT, sag} msg'⌝ ∗ sag ⤇* φ ∗ φ msg')) ∨
           ⌜set_Exists (λ m' : message, m ≡g{sagT, sag} m') R⌝) }}}.
  Proof.
    iIntros (<- Haddr Hblk Φ) "(>Hsag & >Hsh & >Ha & #Hsi) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin". iApply (wp_receivefrom_groups with "[$Hsag $Hsh $Ha]"); eauto.
    iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
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
    iIntros "%tid #Hin". iApply (wp_receivefrom with "[$Hsh $Ha]"); eauto.
    iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_gen_groups ip saR sagR E h s R T φ :
    ip = ip_of_address saR →
    saddress s = Some saR →
    {{{ ▷ saR ∈g sagR ∗ ▷ h ↪[ip] s ∗ ▷ sagR ⤳* (R, T) ∗ sagR ⤇* φ}}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ sagR ⤳* (R, T)) ∨
        ∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          h ↪[ip] s ∗ sagR ⤳* ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m' : message, ¬ msg ≡g{sagT, sagR} m') R⌝ ∗
            (∃ msg' : message, ⌜msg ≡g{sagT, sagR} msg'⌝ ∗ φ msg')) ∨
           ⌜set_Exists (λ m' : message, msg ≡g{sagT, sagR} m') R⌝) }}}.
  Proof.
    iIntros (-> Haddr Φ) "(>HsagR & >Hsh & >Ha & #Hsi) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    iApply (wp_receivefrom_gen_groups with "[$HsagR $Hsh $Ha]");
      [done..|].
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
    iIntros "%tid #Hin". iApply (wp_receivefrom_gen with "[$Hsh $Ha]"); eauto.
    iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_nb_gen_tracked_groups
        (Ψo : option (socket_interp Σ)) ip saR sagR strck E h s R T evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address saR = ip →
    saddress s = Some saR →
    sblock s = false →
    {{{ ▷ saR ∈g sagR ∗
        ▷ h ↪[ip_of_address saR] s ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        match Ψo with Some Ψ => sagR ⤇* Ψ | _ => True end ∗
        ▷ receiveon_evs_groups sagR evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (ReceiveFrom (Val $ LitV $ LitSocket h)) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip_of_address saR] s ∗ sagR ⤳*[strck, true] (R, T) ∨
          (∃ msg sagT,
              ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                                (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
              ⌜m_destination msg = saR⌝ ∗
              m_sender msg ∈g sagT ∗
              h ↪[ip_of_address saR] s ∗
              sagR ⤳*[strck, true] ({[ msg ]} ∪ R, T) ∗
              ((⌜set_Forall (λ m' : message, ¬ msg ≡g{ sagT, sagR} m') R⌝ ∗
                ∃ msg' : message, ⌜msg ≡g{ sagT, sagR} msg'⌝ ∗
                                  match Ψo with
                                    Some Ψ => Ψ msg'
                                  | _ => ∃ φ, sagR ⤇* φ ∗ φ msg'
                end) ∨
               ⌜set_Exists (λ m' : message, msg ≡g{ sagT, sagR} m') R⌝) ∗
              ∃ st skts r,
                ⌜valid_receiveonObs saR st h msg skts s r⌝ ∗
                receiveon_evs_groups sagR (evs ++ [receiveonObs saR st h msg skts s r]) ∗
                Ψ1 st ∗ Ψ2 (receiveonObs saR st h msg skts s r).(post_state)))) }}}.
  Proof.
    iIntros (Hip Hskt Hblock Φ) "(HsagR & Hsh & Ha & HΨ & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_receivefrom_nb_gen_tracked_groups Ψo with "[$]"); [done..|].
    iNext.
    iIntros (r) "Hr".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_nb_gen_tracked
        (Ψ : socket_interp Σ) ip a strck E h s R T evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip_of_address a] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ Ψ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      (ReceiveFrom (Val $ LitV $ LitSocket h)) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳[strck, true] (R, T) ∨
          (∃ msg,
              ⌜m_destination msg = a⌝ ∗
              ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                                (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
              ((⌜msg ∉ R⌝ ∗ h ↪[ip_of_address a] s ∗
                a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ Ψ msg) ∨
               ⌜msg ∈ R⌝ ∗ h ↪[ip_of_address a] s ∗ a ⤳[strck, true] (R, T)) ∗
              ∃ st skts r,
                ⌜valid_receiveonObs a st h msg skts s r⌝ ∗
                receiveon_evs a (evs ++ [receiveonObs a st h msg skts s r]) ∗
                Ψ1 st ∗ Ψ2 (receiveonObs a st h msg skts s r).(post_state)))) }}}.
  Proof.
    iIntros (Hip Hskt Hblock Φ) "(Hsh & Ha & HΨ & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_receivefrom_nb_gen_tracked Ψ with "[$]"); [done|done|].
    iNext.
    iIntros (r) "Hr".
    iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_nb_tracked_groups ip saR sagR strck E h s R T evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address saR = ip →
    saddress s = Some saR →
    sblock s = false →
    {{{ ▷ saR ∈g sagR ∗
        ▷ h ↪[ip] s ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        ▷ receiveon_evs_groups sagR evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ sagR ⤳*[strck, true] (R, T))) ∨
        (∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                  (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          h ↪[ip] s ∗ sagR ⤳*[strck, true] ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m' : message, ¬ msg ≡g{ sagT, sagR } m') R⌝ ∗
               ∃ msg' : message, ⌜msg ≡g{ sagT, sagR } msg'⌝ ∗
                ∃ φ, sagR ⤇* φ ∗ φ msg') ∨
           ⌜set_Exists (λ m' : message, msg ≡g{ sagT, sagR } m') R⌝) ∗
           ∃ st skts r,
            ⌜valid_receiveonObs saR st h msg skts s r⌝ ∗
            receiveon_evs_groups sagR (evs ++ [receiveonObs saR st h msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs saR st h msg skts s r).(post_state)) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "(HsagR & Hsh & Hm & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen_tracked_groups None with "[$]"); eauto.
  Qed.

  Lemma aneris_wp_receivefrom_nb_tracked Ψ ip a strck E h s R T evs
         (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ h ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ Ψ ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
    {{{ r, RET r;
        ((⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T))) ∨
        (∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗
            Ψ msg) ∨
           ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
           ∃ st skts r,
            ⌜valid_receiveonObs a st h msg skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st h msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st h msg skts s r).(post_state)) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "(Hsh & Hm & HΨ & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen_tracked with "[$]"); eauto.
  Qed.

  Lemma aneris_wp_receivefrom_alt_tracked_groups ip saR sagR strck E sh s R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address saR = ip →
    saddress s = Some saR →
    sblock s = false →
    {{{ ▷ saR ∈g sagR ∗
        ▷ sh ↪[ip] s ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        sagR ⤇* φ ∗
        ▷ receiveon_evs_groups sagR evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket sh) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ sh ↪[ip] s ∗ sagR ⤳*[strck, true] (R, T)) ∨
        ∃ msg sagT,
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ⌜m_destination msg = saR⌝ ∗
          m_sender msg ∈g sagT ∗
          sh ↪[ip] s ∗ sagR ⤳*[strck, true] ({[ msg ]} ∪ R, T) ∗
          ((⌜set_Forall (λ m' : message, ¬ msg ≡g{ sagT, sagR } m') R⌝ ∗
               ∃ msg' : message, ⌜msg ≡g{ sagT, sagR } msg'⌝ ∗ φ msg') ∨
           ⌜set_Exists (λ m' : message, msg ≡g{ sagT, sagR } m') R⌝) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs saR st sh msg skts s r⌝ ∗
            receiveon_evs_groups sagR (evs ++ [receiveonObs saR st sh msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs saR st sh msg skts s r).(post_state) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "Hsh HΦ". rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen_tracked_groups (Some φ) with "[$]"); eauto.
  Qed.

  Lemma aneris_wp_receivefrom_alt_tracked ip a strck E sh s R T φ evs
         (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = false →
    {{{ ▷ sh ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket sh) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∨
        ∃ msg,
          ⌜m_destination msg = a⌝ ∗
          ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                            (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
          ((⌜msg ∉ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
           ⌜msg ∈ R⌝ ∗ sh ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st sh msg skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st sh msg skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st sh msg skts s r).(post_state) }}}.
  Proof.
    iIntros (Hip Hs Hb Φ) "Hsh HΦ". rewrite -Hip.
    iApply (aneris_wp_receivefrom_nb_gen_tracked φ with "[$]"); eauto.
  Qed.

  Lemma aneris_wp_receivefrom_tracked_groups ip saR sagR strck E h s R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address saR = ip →
    saddress s = Some saR →
    sblock s = true →
    {{{ ▷ saR ∈g sagR ∗
        ▷ h ↪[ip] s ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        sagR ⤇* φ ∗
        ▷ receiveon_evs_groups sagR evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
      {{{ m, RET SOMEV (PairV #(m_body m) #(m_sender m));
          ∃ sagT,
            ⌜m_destination m = saR⌝ ∗
            m_sender m ∈g sagT ∗
            h ↪[ip] s ∗ sagR ⤳*[strck, true] ({[ m ]} ∪ R, T) ∗
            ((⌜set_Forall (λ m' : message, ¬ m ≡g{ sagT, sagR } m') R⌝ ∗
              ∃ msg' : message, ⌜m ≡g{ sagT, sagR } msg'⌝ ∗
                                sagR ⤇* φ ∗ φ msg') ∨
             ⌜set_Exists (λ m' : message, m ≡g{ sagT, sagR } m') R⌝) ∗
            ∃ st skts r,
              ⌜valid_receiveonObs saR st h m skts s r⌝ ∗
              receiveon_evs_groups sagR (evs ++ [receiveonObs saR st h m skts s r]) ∗
              Ψ1 st ∗ Ψ2 (receiveonObs saR st h m skts s r).(post_state) }}}.
  Proof.
    iIntros (<- Haddr Hblk Φ) "(>HsagR & >Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin". iApply (wp_receivefrom_tracked_groups with "[$]"); eauto.
    iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_tracked ip a strck E h s R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = true →
    {{{ ▷ h ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
      {{{ m, RET SOMEV (PairV #(m_body m) #(m_sender m));
          ⌜m_destination m = a⌝ ∗
          ((⌜m ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] ({[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ φ m) ∨
           ⌜m ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
          ∃ st skts r,
            ⌜valid_receiveonObs a st h m skts s r⌝ ∗
            receiveon_evs a (evs ++ [receiveonObs a st h m skts s r]) ∗
            Ψ1 st ∗ Ψ2 (receiveonObs a st h m skts s r).(post_state) }}}.
  Proof.
    iIntros (<- Haddr Hblk Φ) "(>Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin". iApply (wp_receivefrom_tracked with "[$]"); eauto.
    iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_gen_tracked_groups ip saR sagR strck E h s R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip = ip_of_address saR →
    saddress s = Some saR →
    {{{ ▷ saR ∈g sagR ∗
        ▷ h ↪[ip] s ∗
        ▷ sagR ⤳*[strck, true] (R, T) ∗
        sagR ⤇* φ ∗
        ▷ receiveon_evs_groups sagR evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
      {{{ r, RET r;
          (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ sagR ⤳*[strck, true] (R, T)) ∨
          ∃ msg sagT,
            ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                              (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
            ⌜m_destination msg = saR⌝ ∗
            m_sender msg ∈g sagT ∗
            h ↪[ip] s ∗ sagR ⤳*[strck, true] ({[ msg ]} ∪ R, T) ∗
            ((⌜set_Forall (λ m' : message, ¬ msg ≡g{ sagT, sagR } m') R⌝ ∗
              ∃ msg' : message, ⌜msg ≡g{ sagT, sagR } msg'⌝ ∗ φ msg') ∨
             ⌜set_Exists (λ m' : message, msg ≡g{ sagT, sagR } m') R⌝) ∗
            ∃ st skts r,
              ⌜valid_receiveonObs saR st h msg skts s r⌝ ∗
              receiveon_evs_groups sagR (evs ++ [receiveonObs saR st h msg skts s r]) ∗
              Ψ1 st ∗ Ψ2 (receiveonObs saR st h msg skts s r).(post_state) }}}.
  Proof.
    iIntros (-> Haddr Φ) "(>HsagR & >Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin". iApply (wp_receivefrom_gen_tracked_groups with "[$]"); eauto.
    iNext. iIntros (r) "Hr". iExists _; iSplit; first done.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma aneris_wp_receivefrom_gen_tracked ip a strck E h s R T φ evs
        (Ψ1 Ψ2 : state → iProp Σ) :
    ip = ip_of_address a →
    saddress s = Some a →
    {{{ ▷ h ↪[ip] s ∗
        ▷ a ⤳[strck, true] (R, T) ∗
        a ⤇ φ ∗
        ▷ receiveon_evs a evs ∗
        (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                          aneris_state_interp σ δ ∗ Ψ1 σ) ∗
        ▷ (∀ (σ : state) δ, aneris_state_interp σ δ ={E}=∗
                            aneris_state_interp σ δ ∗ Ψ2 σ) }}}
      ReceiveFrom (Val $ LitV $ LitSocket h) @[ip] E
      {{{ r, RET r;
          (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∨
          ∃ msg,
            ⌜m_destination msg = a⌝ ∗
            ⌜r = SOMEV (PairV (LitV $ LitString (m_body msg))
                              (LitV $ LitSocketAddress (m_sender msg)))⌝ ∗
            ((⌜msg ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] ({[ msg ]} ∪ R, T) ∗ φ msg) ∨
             ⌜msg ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳[strck, true] (R, T)) ∗
            ∃ st skts r,
              ⌜valid_receiveonObs a st h msg skts s r⌝ ∗
              receiveon_evs a (evs ++ [receiveonObs a st h msg skts s r]) ∗
              Ψ1 st ∗ Ψ2 (receiveonObs a st h msg skts s r).(post_state) }}}.
  Proof.
    iIntros (-> Haddr Φ) "(>Hsh & >Ha & #Hsi & Hevs & HΨ1 & HΨ2) HΦ".
    rewrite !aneris_wp_unfold /aneris_wp_def.
    iIntros "%tid #Hin". iApply (wp_receivefrom_gen_tracked with "[$]"); eauto.
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
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_rcvtimeo_unblock _ a E _ h s n1 n2 with "[$Hsh]"); [done|done|].
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
    iIntros "%tid #Hin".
    rewrite -Hip.
    iApply (wp_rcvtimeo_block _ a E _ h s with "[$Hsh]"); [done|].
    iNext. iIntros "Hsh". iExists _; iSplit; first done. iApply "HΦ"; iFrame.
  Qed.

End lifting_network.
