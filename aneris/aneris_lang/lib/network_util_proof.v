From stdpp Require Import base pretty.
From iris.proofmode Require Import coq_tactics tactics.
From aneris.prelude Require Export strings gset_map.
From aneris.aneris_lang Require Import ast lang tactics proofmode network.
From aneris.aneris_lang.lib Require Import inject pers_socket_proto.
From aneris.aneris_lang.lib Require Import assert_proof list_proof map_proof set_proof.
From aneris.aneris_lang.lib Require Export network_util_code.

Set Default Proof Using "Type".
Import String.
Import uPred.

Section library.
  Context `{dG : anerisG Mdl Σ}.

  Lemma wp_unSOME ip v v' :
    {{{ ⌜v = SOMEV v'⌝ }}} unSOME (Val v) @[ip] {{{ RET v'; True }}}.
  Proof.
    iIntros (Φ ->) "HΦ".
    wp_lam. wp_match. by iApply "HΦ".
  Qed.

  Lemma listen_spec ip P Q h s R T a handler φ:
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = false →
    (∀ m,
      {{{ ⌜m_destination m = a⌝ ∗ P ∗
          ((⌜m ∉ R⌝ ∗ h ↪[ip] s ∗ a ⤳ ({[m]} ∪ R, T) ∗ φ m) ∨
           (⌜m ∈ R⌝ ∗ h ↪[ip] s ∗ a ⤳ (R, T)))
      }}}
         (Val handler) #(m_body m) #(m_sender m) @[ip]
      {{{ v, RET v; Q v }}}) -∗
      {{{ P ∗ h ↪[ip] s ∗ a ⤳ (R, T) ∗ a ⤇ φ }}}
         listen #(LitSocket h) (Val handler) @[ip]
      {{{ v, RET v; Q v }}}.
  Proof.
     iIntros (n Haddr Hsblock) "#Hhandler". iLöb as "IH".
     iModIntro. iIntros (Φ) "(HP & Hsocket & Hmh & #Hsi) HΦ".
     wp_rec. wp_let. rewrite /n. wp_bind (ReceiveFrom _).
     wp_apply (aneris_wp_receivefrom_nb with "[$]"); [done|done|done|].
     iIntros (r) "[(-> & Hs) | Hrd ]"; simpl.
     - wp_pures. iApply ("IH" with "[-HΦ]"); by iFrame "#∗".
     - iDestruct "Hrd" as (m Hdst ->) "[ (% & Hs & Hφ) | (% & Hs) ]"; wp_pures;
         wp_apply ("Hhandler" with "[-HΦ] [HΦ]"); eauto with iFrame.
  Qed.

  Lemma wp_pers_wait_receivefrom Ψ a φ R T h (f : val) :
    (∀ (m : message),
      {{{ True }}}
        f (#(m_body m), #(m_sender m))%V @[ip_of_address a]
      {{{ (b : bool), RET #b; if b then Ψ m else True }}}) -∗
    {{{ h ↪[ip_of_address a] (mkSocket (Some a) true) ∗
        a ⤇ φ ∗
        a @ φ ⤳# (R, T) }}}
      wait_receivefrom #(LitSocket h) f @[ip_of_address a]
    {{{ m R', RET (#(m_body m), #(m_sender m));
        h ↪[ip_of_address a] (mkSocket (Some a) true) ∗
        a @ φ ⤳# (R', T) ∗
        Ψ m ∗ φ m }}}.
  Proof.
    iIntros "#Hf" (Φ) "!# (Hh & #Hφ & Ha) HΦ". rewrite /wait_receivefrom.
    do 4 (wp_pure _). do 2 wp_pure _.
    iLöb as "IH" forall (R).
    wp_pures.
    wp_apply (aneris_wp_pers_receivefrom with "[$Hh $Ha $Hφ]"); [done..|].
    iIntros (m) "(Hh & Ha & Hm)".
    wp_apply wp_unSOME; [done|]; iIntros "_".
    wp_pures.
    wp_apply ("Hf"); [done|].
    iIntros ([]) "Htest"; wp_if.
    { iApply "HΦ". by iFrame. }
    wp_apply ("IH" with "Hh Ha HΦ").
  Qed.

  (* TODO: Maybe move this elsewhere *)
  Definition pair_to_msg (sa : socket_address)
             (m : message_body * socket_address) : message :=
    mkMessage m.2 sa m.1.

  Instance pair_to_msg_injective sa : Inj eq eq (pair_to_msg sa).
  Proof. intros [] [] Heq. by simplify_eq. Qed.

  Lemma pair_to_msg_id m :
    pair_to_msg (m_destination m) (m_body m, m_sender m) = m.
  Proof. by destruct m. Qed.

  Lemma wp_wait_receivefresh a φ R T h l
        (ms : list (message_body * socket_address)) :
    is_list ms l →
    R = gset_map (pair_to_msg a) (list_to_set ms) →
    {{{ h ↪[ip_of_address a] (mkSocket (Some a) true) ∗ a ⤇ φ ∗ a ⤳ (R, T) }}}
      wait_receivefresh #(LitSocket h) l @[ip_of_address a]
    {{{ m, RET (#(m_body m), #(m_sender m));
           ⌜m_destination m = a⌝ ∗
           h ↪[ip_of_address a] (mkSocket (Some a) true) ∗
           a ⤳ ({[m]} ∪ R, T) ∗ φ m }}}.
  Proof.
    iIntros (Hl Heq Φ) "(Hh & #Hsi & Ha) HΦ".
    wp_lam. rewrite /wait_receivefrom.
    do 9 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_apply (aneris_wp_receivefrom with "[$Hh $Ha $Hsi]"); [done..|].
    iIntros (m) "[%Hdest H]".
    wp_apply wp_unSOME; [done|]. iIntros "_". wp_pures.
    wp_apply (wp_list_mem _ ms l (m_body m, m_sender m)); [done|].
    iDestruct "H" as "[H|H]".
    - iDestruct "H" as "(%Hnin & Hh & Ha & _ & Hm)".
      iIntros ([]) "%Hb".
      { rewrite Heq in Hnin.
        apply (elem_of_list_to_set (C:=gset _)) in Hb.
        apply (gset_map_correct1 (pair_to_msg a)) in Hb.
        rewrite -{1}Hdest in Hb. rewrite pair_to_msg_id in Hb. done. }
      wp_pures. iApply "HΦ". by iFrame.
    - iDestruct "H" as "(%Hin & Hh & Ha)".
      iIntros ([]) "%Hb"; last first.
      { destruct Hb as [Hb|Hb]; last first.
        { rewrite Heq in Hin. rewrite Hb in Hin. set_solver. }
        rewrite Heq in Hin.
        apply (not_elem_of_list_to_set (C:=gset _)) in Hb.
        apply (gset_map_not_elem_of (pair_to_msg a)) in Hb; [|apply _].
        rewrite -{1}Hdest in Hb. rewrite pair_to_msg_id in Hb. done. }
      do 2 wp_pure _.
      iApply ("IH" with "Hh Ha HΦ").
  Qed.

  Lemma wp_pers_receivefrom_all nodes φ ns h s ip a R T :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    {{{ ⌜is_list nodes ns⌝ ∗
        h ↪[ip] s ∗
        a ⤇ φ ∗
        a @ φ ⤳# (R, T) }}}
      receivefrom_all #(LitSocket h) ns @[ip]
    {{{ vs msgs R', RET vs;
        h ↪[ip] s ∗
        a @ φ ⤳# (R', T) ∗
        ⌜length nodes = length msgs⌝ ∗
        ⌜is_list (map m_body msgs) vs⌝ ∗
        [∗ list] i↦n ∈ nodes, ∃ m, ⌜msgs !! i = Some m⌝ ∗ ⌜m_sender m = n⌝ ∗ φ m }}}.
  Proof.
    iIntros (Hip ?? Φ) "(Hns & Hh & #Hφ & Ha) HΦ".
    rewrite /receivefrom_all. wp_pures.
    wp_apply (wp_list_fold
                (λ (nodes' : list socket_address) (acc : val), ∃ msgs R,
                    h ↪[ip] s ∗ a @ φ ⤳# (R, T) ∗
                      ⌜is_list (map m_body msgs) acc⌝ ∗
                      ⌜length nodes' = length msgs⌝ ∗
                      [∗ list] i↦n ∈ nodes', (∃ m, ⌜msgs !! i = Some m⌝ ∗
                                                   ⌜m_sender m = n⌝ ∗ φ m))%I
                (λ n, True)%I (λ n, True)%I _ _ nodes NONEV with "[] [$Hns Hh Ha]").
    - iIntros (n acc lacc lrem Ψ) "!# (% & Hmsgs & _) HΨ".
      do 4 wp_pure _.
      wp_bind (((rec: "recv" _ := _)%V _))%E.
      iLöb as "IH".
      wp_pures.
      iDestruct "Hmsgs" as (msgs R') "(Hh & Ha & %Hacc & %Hlength & Hnodes)".
      wp_apply (aneris_wp_pers_receivefrom with "[$Hh $Ha $Hφ]"); [done..|].
      iIntros (m) "(Hh & Ha & Hm)".
      wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      case_bool_decide as Heq.
      + wp_pures.
        wp_apply (wp_list_cons (m_body m) []); first done.
        iIntros (??).
        wp_apply wp_list_append; [done|].
        iIntros (??).
        iApply "HΨ". iSplit; [|done].
        iExists (msgs ++ [m]), _. iFrame.
        iSplit.
        { rewrite map_app //. }
        rewrite big_sepL_app big_sepL_singleton.
        iSplit.
        { iPureIntro. rewrite !app_length Hlength //. }
        iSplitL "Hnodes".
        { iApply (big_sepL_impl with "Hnodes").
          iIntros "!#" (???).
          iDestruct 1 as (?) "(% & % & ?)".
          iExists _. iFrame. simplify_eq.
          iSplit; [|done].
          iPureIntro.
          by apply lookup_app_l_Some. }
        iExists m. iFrame.
        inversion_clear Heq.
        iSplit; [|done].
        iPureIntro.
        rewrite Hlength -plus_n_O lookup_app_r // Nat.sub_diag //.
      + wp_if.
        iApply ("IH" with "[-HΨ]").
        { iExists _, _. by iFrame. }
        iIntros (?) "[Hmsgs _]".
        iDestruct "Hmsgs" as (msgs' R'') "(Hh & Ha & %Hmsgs' & Hnodes)".
        iApply "HΨ".
        iFrame. iExists _, _. by iFrame.
    - rewrite big_sepL_emp. iFrame. iExists [], R. iFrame; auto.
    - iIntros (?) "[Hmsgs _]".
      iDestruct "Hmsgs" as (msgs R') "(Hh & Ha & %Hmsgs & % & Hnodes)".
      iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_pers_wait_receivefrom_all Ψ nodes φ ns h s ip a R T (fv : val) :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    (∀ (str : string),
      {{{ True }}}
        fv #str @[ip]
      {{{ (b : bool), RET #b; if b then Ψ str else True }}}) -∗
    {{{ ⌜is_list nodes ns⌝ ∗
        h ↪[ip] s ∗
        a ⤇ φ ∗
        a @ φ ⤳# (R, T) }}}
      wait_receivefrom_all #(LitSocket h) ns fv @[ip]
    {{{ vs msgs R', RET vs;
        h ↪[ip] s ∗
        a @ φ ⤳# (R', T) ∗
        ⌜is_list (map m_body msgs) vs⌝ ∗
        ⌜length nodes = length msgs⌝ ∗
        [∗ list] i↦n ∈ nodes, ∃ m, ⌜msgs !! i = Some m⌝ ∗
                                   ⌜m_sender m = n⌝ ∗ Ψ (m_body m) ∗ φ m }}}.
  Proof.
    iIntros (Hip ??) "#Hfv !#". iIntros (Φ) "(Hns & Hh & #Hφ & Ha) HΦ".
    rewrite /wait_receivefrom_all. wp_pures.
    wp_apply (wp_list_fold
                (λ (nodes' : list socket_address) (acc : val), ∃ msgs R,
                    h ↪[ip] s ∗ a @ φ ⤳# (R, T) ∗
                    ⌜is_list (map m_body msgs) acc⌝ ∗
                    ⌜length nodes' = length msgs⌝ ∗
                    [∗ list] i↦n ∈ nodes', (∃ m, ⌜msgs !! i = Some m⌝ ∗
                                                 ⌜m_sender m = n⌝ ∗ Ψ (m_body m) ∗ φ m))%I
                (λ n, True)%I
                (λ n, True)%I _ _ nodes NONEV with "[] [$Hns Hh Ha]").
    - iIntros (n acc lacc lrem Φ') "!# (% & Hmsgs & _) HΦ'".
      do 4 wp_pure _.
      wp_bind (((rec: "recv" _ := _)%V _))%E.
      iLöb as "IH".
      wp_pures.
      iDestruct "Hmsgs" as (msgs R') "(Hh & Ha & %Hacc & %Hlength & Hnodes)".
      wp_apply (aneris_wp_pers_receivefrom with "[$Hh $Ha $Hφ]"); [done..|].
      iIntros (m) "(Hh & Ha & Hm)".
      wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      case_bool_decide as Heq.
      + wp_pures.
        wp_apply "Hfv"; [done|].
        iIntros ([]) "Hb".
        * wp_if.
          wp_apply (wp_list_cons (m_body m) []); first done.
          iIntros (??).
          wp_apply wp_list_append; [done|].
          iIntros (??). iApply "HΦ'". iSplit; [|done].
          iExists (msgs ++ [m]), _. iFrame.
          iSplit.
          { rewrite map_app //. }
          rewrite big_sepL_app big_sepL_singleton.
          iSplit.
          { iPureIntro. rewrite !app_length Hlength //. }
          iSplitL "Hnodes".
          { iApply (big_sepL_impl with "Hnodes").
            iIntros "!#" (???).
            iDestruct 1 as (?) "(% & % & ?)".
            iExists _. iFrame. simplify_eq.
            iSplit; [|done].
            iPureIntro; by apply lookup_app_l_Some. }
          iExists m. iFrame.
          inversion_clear Heq.
          iSplit; [|done].
          iPureIntro.
          rewrite Hlength -plus_n_O lookup_app_r // Nat.sub_diag //.
        * wp_if.
          iApply ("IH" with "[-HΦ']").
          { iExists _, _. by iFrame. }
          iIntros (?) "[Hmsgs _]".
          iDestruct "Hmsgs" as (msgs' R'') "(Hh & Ha & %Hmsgs' & Hnodes)".
          iApply "HΦ'".
          iFrame. iExists _, _. by iFrame.
      + do 2 wp_if.
        iApply ("IH" with "[-HΦ']").
        { iExists _, _. by iFrame. }
        iIntros (?) "[Hmsgs _]".
        iDestruct "Hmsgs" as (msgs' R'') "(Hh & Ha & %Hmsgs' & %Hlength' & Hnodes)".
        iApply "HΦ'".
        iFrame. iExists _, _. by iFrame.
    - rewrite big_sepL_emp. iFrame. iExists [], R. iFrame; auto.
    - iIntros (?) "[Hmsgs _]".
      iDestruct "Hmsgs" as (msgs R') "(Hh & Ha & %Hmsgs & %Hlength & Hnodes)".
      iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_sendto_all f m ip a h s R T ns nodes :
    let msg n := mkMessage a n m in
    ip = ip_of_address a →
    saddress s = Some a →
    {{{ h ↪[ip] s
          ∗ a ⤳ (R, T)
          ∗ ⌜is_list nodes ns⌝
          ∗ [∗ list] n ∈ nodes, (n ⤇ f n ∗ f n (msg n)) }}}
      sendto_all #(LitSocket h) ns #m @[ip]
    {{{ T', RET #(); h ↪[ip] s ∗ a ⤳ (R, T') }}}.
  Proof.
    iIntros (??? Φ) "(Hh & Ha & %Hns & Hnodes) HΦ".
    rewrite /sendto_all. wp_pures.
    wp_apply ((wp_list_iter (λ n, n ⤇ f n ∗ f n (msg n))
                            (λ n, True)
                            (h ↪[ip] s ∗ ∃ T, a ⤳ (R, T))
                with "[] [$Hnodes $Hh Ha]")%I); [|eauto|].
    { iIntros (sa) "!>". iIntros (Φ') "([Hh Ha] & #Hφ & Hmsg) H".
      iDestruct "Ha" as (T') "Ha".
      wp_pures.
      wp_send "Hmsg"; [rewrite /msg //|]. wp_pures.
      iApply "H". iFrame. eauto. }
    iIntros "([Hh Ha] & _)".
    iDestruct "Ha" as (?) "Ha".
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_pers_sendto_all f m a h s R T ns nodes Ψ :
    let ip := ip_of_address a in
    let msg n := mkMessage a n m in
    saddress s = Some a →
    {{{ h ↪[ip] s
          ∗ a @ Ψ ⤳# (R, T)
          ∗ ⌜is_list nodes ns⌝
          ∗ [∗ list] n ∈ nodes, (n ⤇ f n ∗ f n (msg n)) }}}
      sendto_all #(LitSocket h) ns #m @[ip]
    {{{ T', RET #(); h ↪[ip] s ∗ a @ Ψ ⤳# (R, T') }}}.
  Proof.
    iIntros (??? Φ) "(Hh & Ha & %Hns & Hnodes) HΦ".
    rewrite /sendto_all. wp_pures.
    wp_apply ((wp_list_iter (λ n, n ⤇ f n ∗ f n (msg n))
                            (λ n, True)
                            (h ↪[ip] s ∗ ∃ T, a @ Ψ ⤳# (R, T)) with "[] [$Hnodes $Hh Ha]")%I); [|eauto|].
    { iIntros (sa) "!>". iIntros (Φ') "([Hh Ha] & #Hφ & Hmsg) H".
      iDestruct "Ha" as (T') "Ha".
      wp_pures.
      wp_apply (aneris_wp_pers_send with "[$Hh $Ha $Hφ Hmsg]"); [done..|].
      iIntros "(Hh & Ha)". wp_pures.
      iApply "H". iFrame. eauto. }
    iIntros "([Hh Ha] & _)".
    iDestruct "Ha" as (?) "Ha".
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_sendto_all_set f m ip a h s R T ns nodes :
    let msg n := mkMessage a n m in
    ip = ip_of_address a →
    saddress s = Some a →
    {{{ h ↪[ip] s
          ∗ a ⤳ (R, T)
          ∗ ⌜is_set nodes ns⌝
          ∗ [∗ set] n ∈ nodes, (n ⤇ f n ∗ f n (msg n)) }}}
      sendto_all_set #(LitSocket h) ns #m @[ip]
    {{{ T', RET #(); h ↪[ip] s ∗ a ⤳ (R, T') }}}.
  Proof.
    iIntros (??? Φ) "(Hh & Ha & %Hns & Hnodes) HΦ".
    rewrite /sendto_all_set. wp_pures.
    wp_apply (wp_set_iter (λ n, n ⤇ f n ∗ f n (msg n))%I
                          (λ _, True)%I
                          (λ _, True)%I
                          (h ↪[ip] s ∗ ∃ T, a ⤳ (R, T))%I with "[] [$Hh $Hnodes Ha]"); [|eauto|].
    { iIntros (n _ Ψ)" !# (%Hn & [Hh Ha] & _ & #Hf & Hmsg) H". iDestruct "Ha" as (T') "Ha".
      wp_pures.
      wp_send "Hmsg"; [rewrite /msg //|].
      wp_let.
      iApply "H". iFrame. eauto. }
    iIntros "([Hh Ha] & _)".
    iDestruct "Ha" as (?) "Ha".
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_sendto_all_vs P Q E m ip a h s ns nodes :
    let msg n := mkMessage a n m in
    ip = ip_of_address a →
    saddress s = Some a →
    is_set nodes ns →
    □ (∀ n,
          P ∗ ⌜n ∈ nodes⌝ ={⊤, E}=∗
          ∃ R T φ, a ⤳ (R, T) ∗ n ⤇ φ ∗ φ (msg n) ∗
          (a ⤳ (R, {[msg n]} ∪ T) ={E, ⊤}=∗ P ∗ Q n)) -∗
    {{{ P ∗ h ↪[ip] s }}}
      sendto_all_set #(LitSocket h) ns #m @[ip]
    {{{ RET #(); P ∗ h ↪[ip] s ∗ [∗ set] n ∈ nodes, Q n }}}.
  Proof.
    iIntros (????) "#Hvs". iIntros (Φ) "!# [HP Hh] HΦ".
    rewrite /sendto_all_set. wp_pures.
    wp_apply (wp_set_iter (λ _, True)%I Q (λ _, True)%I (P ∗ h ↪[ip] s)%I _ nodes
                with "[] [$HP $Hh]").
    { iIntros (n _ Ψ) "!# (% & [HP Hh] & _) HΨ".
      wp_pures.
      wp_bind (SendTo _ _ _).
      iMod ("Hvs" with "[$HP //]") as (R T φ) "(Ha & #Hn & Hf & Hclose)".
      wp_send "Hf"; [done|].
      iMod ("Hclose" with "Ha") as "[HP HQ]".
      iModIntro. wp_let. iApply "HΨ". iFrame. }
    { iFrame "%". iSplit; [done|]. by iApply big_sepS_forall. }
    rewrite -bi.sep_assoc bi.True_sep //.
  Qed.

  Lemma wp_sendto_all_take_step P Q Φ E m ip a h s ns nodes :
    let msg n := mkMessage a n m in
    ip = ip_of_address a →
    saddress s = Some a →
    is_set nodes ns →
    □ (∀ n nodes',
          P ∗ Φ nodes' ∗ ⌜n ∈ nodes⌝ ={⊤, E}=∗
          ∃ R T φ δ δ',
            frag_st δ ∗ a ⤳ (R, T) ∗ n ⤇ φ ∗
            ⌜δ = δ' ∨ Mdl δ δ'⌝ ∗ φ (msg n) ∗
            (a ⤳ (R, {[msg n]} ∪ T) ∗ frag_st δ'
             ={E, ⊤}=∗ P ∗ Φ (nodes' ∪ {[n]}) ∗ Q n)) -∗
    {{{ P ∗ Φ ∅ ∗ h ↪[ip] s }}}
      sendto_all_set #(LitSocket h) ns #m @[ip]
    {{{ RET #(); P ∗ h ↪[ip] s ∗ Φ nodes ∗ [∗ set] n ∈ nodes, Q n }}}.
  Proof.
    iIntros (????) "#Hvs". iIntros (Ψ) "!# (HP & HΦ & Hh) HΨ".
    rewrite /sendto_all_set. wp_pures.
    wp_apply (wp_set_iter (λ _, True)%I Q Φ (P ∗ h ↪[ip] s)%I _ nodes
                with "[] [$HP $Hh $HΦ]").
    { iIntros (n nodes' Ψ') "!# [% ([HP Hh] & HΦ & _)] HΨ".
      wp_pures.
      wp_bind (SendTo _ _ _).
      wp_apply aneris_wp_atomic_take_step_model.
      iMod ("Hvs" with "[$HP $HΦ //]")
        as (R T φ δ δ') "(Hfrag & Ha & #Hn & % & Hφ & Hcont)".
      iModIntro. iExists _, _. iFrame "∗ %".
      wp_send "Hφ"; [done|].
      iIntros "Hfrag".
      iMod ("Hcont" with "[$Ha $Hfrag]") as "[HP HQ]".
      iModIntro. wp_let. iApply "HΨ". iFrame. }
    { iFrame "%". by iApply big_sepS_forall. }
    rewrite -bi.sep_assoc //.
  Qed.

  Lemma wp_pers_sendto_all_vs P Q E m ip a h s ns nodes :
    let msg n := mkMessage a n m in
    ip = ip_of_address a →
    saddress s = Some a →
    is_set nodes ns →
    □ (∀ n,
          P ∗ ⌜n ∈ nodes⌝ ={⊤, E}=∗
          ∃ R T φ ψ, a @ ψ ⤳# (R, T) ∗ n ⤇ φ ∗ φ (msg n) ∗
          (a @ ψ ⤳# (R, {[msg n]} ∪ T) ={E, ⊤}=∗ P ∗ Q n)) -∗
    {{{ P ∗ h ↪[ip] s }}}
      sendto_all_set #(LitSocket h) ns #m @[ip]
    {{{ RET #(); P ∗ h ↪[ip] s ∗ [∗ set] n ∈ nodes, Q n }}}.
  Proof.
    iIntros (????) "#Hvs".
    iApply wp_sendto_all_vs; [done..|].
    iIntros "!#" (?) "[HP %]".
    iMod ("Hvs" with "[$HP //]") as (R T φ ψ) "(Ha & Hsi & Hφ & Hclose)".
    rewrite {3 4}mapsto_messages_pers_eq /mapsto_messages_pers_def.
    iDestruct "Ha" as "(% & Ha & HR)".
    iModIntro. iExists _, _, _. do 2 iFrame.
    iIntros "Ha /=".
    iMod ("Hclose" with "[$Ha $HR]"); eauto.
  Qed.

  Lemma wp_pers_sendto_all_take_step P Q Φ E m ip a h s ns nodes :
    let msg n := mkMessage a n m in
    ip = ip_of_address a →
    saddress s = Some a →
    is_set nodes ns →
    □ (∀ n nodes',
          P ∗ Φ nodes' ∗ ⌜n ∈ nodes⌝ ={⊤, E}=∗
          ∃ R T φ ψ δ δ',
            frag_st δ ∗ a @ ψ ⤳# (R, T) ∗ n ⤇ φ ∗
            ⌜δ = δ' ∨ Mdl δ δ'⌝ ∗ φ (msg n) ∗
            (a @ ψ ⤳# (R, {[msg n]} ∪ T) ∗ frag_st δ'
             ={E, ⊤}=∗ P ∗ Φ (nodes' ∪ {[n]}) ∗ Q n)) -∗
    {{{ P ∗ Φ ∅ ∗ h ↪[ip] s }}}
      sendto_all_set #(LitSocket h) ns #m @[ip]
    {{{ RET #(); P ∗ h ↪[ip] s ∗ Φ nodes ∗ [∗ set] n ∈ nodes, Q n }}}.
  Proof.
    iIntros (????) "#Hvs".
    iApply wp_sendto_all_take_step; [done..|].
    iIntros "!#" (??) "(HP & HΦ & %)".
    iMod ("Hvs" with "[$HP $HΦ //]")
      as (R T φ ψ δ δ') "(Hfrag & Ha & #Hn & % & Hφ & Hcont)".
    rewrite {3 4}mapsto_messages_pers_eq /mapsto_messages_pers_def.
    iDestruct "Ha" as "(% & Ha & HR)".
    iModIntro. iExists _, _, _, _, _.
    iFrame "% # ∗".
    iIntros "[Ha Hfrag] /=".
    iMod ("Hcont" with "[$Ha $Hfrag $HR]"); eauto.
  Qed.

  Definition valid_tag t := index 0 "_" t = None.

  Lemma valid_tag_String c s :
    index 0 "_" (String c "") = None → valid_tag s → valid_tag (String c s).
  Proof.
    rewrite /valid_tag /=.
    repeat (case_match; try done).
  Qed.

  Lemma valid_tag_pretty_Npos p :
    valid_tag (pretty (N.pos p)).
  Proof.
    rewrite /pretty /pretty_N.
    assert (valid_tag "") as Hemp by done; revert Hemp.
    apply (λ H, N.strong_right_induction
                  (λ n, ∀ s, valid_tag s → valid_tag (pretty_N_go n s))
                  0%N H); last done.
    intros n Hn IH s Hs.
    destruct (decide (n = 0%N)); first by subst.
    rewrite pretty_N_go_step; last lia.
    destruct (decide (n < 10)%N).
    - rewrite N.div_small; last done.
      rewrite pretty_N_go_0.
      apply valid_tag_String; auto.
      rewrite /pretty_N_char.
      repeat case_match; done.
    - apply IH; first apply N.le_0_l.
      + eapply N.lt_le_trans; last by apply (N.Div0.mul_div_le _ 10).
        assert (n `div` 10 ≠ 0)%N.
        { by intros ?%N.div_small_iff. }
        assert (0 < n `div` 10)%N by by apply N.div_str_pos; auto with lia.
        lia.
      + apply valid_tag_String; auto.
        rewrite /pretty_N_char.
        repeat case_match; done.
  Qed.

  Lemma valid_tag_stringOfZ a :
    valid_tag (StringOfZ a).
  Proof.
    destruct a; rewrite/valid_tag /=; first done.
    apply valid_tag_pretty_Npos.
      by rewrite valid_tag_pretty_Npos.
  Qed.


  Lemma tag_of_message_spec ip (s : string) t v:
    valid_tag t →
    {{{ ⌜s = t +:+ "_" +:+ v⌝ }}}
      tag_of_message #s @[ip]
    {{{ v, RET #v; ⌜v = t⌝ }}}.
  Proof.
    iIntros (Htag Φ HP) "HΦ". rewrite /tag_of_message.
    wp_pures. wp_find_from.
    { by instantiate (1:=0%nat). }
    rewrite HP (index_0_append_char "_") /=; auto.
    wp_match. wp_substring.
    { repeat split; eauto. by instantiate (1:=0%nat). }
    rewrite substring_0_length_append. by iApply "HΦ".
  Qed.

  Lemma value_of_message_spec ip (s : string) t v :
    valid_tag t →
    {{{ ⌜s = t +:+ "_" +:+ v⌝ }}}
      value_of_message #s @[ip]
    {{{ r, RET #r; ⌜r = v⌝ }}}.
  Proof.
    iIntros (Htag Φ HP) "HΦ". rewrite /value_of_message.
    wp_pures. wp_find_from.
    { by instantiate (1:=0%nat). }
    rewrite HP (index_0_append_char "_") /=; auto.  wp_match.
    wp_pures.
    wp_substring.
    { repeat split; eauto.
      instantiate (1:=(String.length t + 1)%nat). apply Nat2Z.inj_add.
      instantiate (1:=(String.length v)%nat).
      rewrite !length_app Nat.add_assoc length_Sn /= !Nat2Z.inj_add. ring. }
    rewrite substring_add_length_app substring_Sn substring_0_length.
      by iApply "HΦ".
  Qed.

End library.
