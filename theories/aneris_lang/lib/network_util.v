From aneris.aneris_lang Require Import lang tactics proofmode notation.
From aneris.aneris_lang.lib Require Import assert list map pers_socket_proto.
From iris_string_ident Require Import ltac2_string_ident.

Set Default Proof Using "Type".

Definition unSOME : base_lang.val :=
  λ: "p",
  match: "p" with NONE => assert #false | SOME "p'" => "p'" end.

Definition wait_receivefrom : base_lang.val :=
  λ: "socket" "test",
  (rec: "loop" <> :=
     let: "msg" := unSOME (ReceiveFrom "socket") in
     if: "test" "msg" then "msg" else "loop" #()) #().

Definition sendto_all : base_lang.val :=
  λ: "socket" "ns" "msg",
  list_iter (λ: "n", SendTo "socket" "msg" "n") "ns".

Definition receivefrom_all : val :=
  λ: "socket" "nodes",
  letrec: "recv" "n" :=
    let: "msg" := unSOME (ReceiveFrom "socket") in
    let: "sender" := Snd "msg" in
    if: "sender" = "n" then (Fst "msg")
    else "recv" "n" in
  list_fold  (λ: "acc" "n", list_append "acc" ["recv" "n"]) [] "nodes".

Definition wait_receivefrom_all : val :=
  λ: "socket" "nodes" "test",
  letrec: "recv" "n" :=
    let: "msg" := unSOME (ReceiveFrom "socket") in
    let: "sender" := Snd "msg" in
    let: "m" := Fst "msg" in
    if: ("sender" = "n") && ("test" "m") then "m"
    else "recv" "n" in
  list_fold  (λ: "acc" "n", list_append "acc" ["recv" "n"]) [] "nodes".

Import Network.

Section library.
  Context `{dG : anerisG Mdl Σ}.

  Lemma wp_unSOME ip v v' :
    {{{ ⌜v = SOMEV v'⌝ }}} unSOME (Val v) @[ip] {{{ RET v'; True }}}.
  Proof.
    iIntros (Φ ->) "HΦ".
    wp_lam. wp_match. by iApply "HΦ".
  Qed.

  Lemma wp_receivefrom_all nodes φ ns h s ip a R T :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    {{{ ⌜is_list (map (LitV ∘ LitSocketAddress) nodes) ns⌝ ∗
        h ↪[ip] s ∗
        a ⤇ φ ∗
        a @ φ ⤳# (R, T) }}}
      receivefrom_all #(LitSocket h) ns @[ip]
    {{{ vs msgs R', RET vs;
        h ↪[ip] s ∗
        a @ φ ⤳# (R', T) ∗
        ⌜length nodes = length msgs⌝ ∗
        ⌜is_list (map (λ m, #(m_body m)) msgs) vs⌝ ∗
        [∗ list] i↦n ∈ nodes, ∃ m, ⌜msgs !! i = Some m⌝ ∗ ⌜m_sender m = n⌝ ∗ φ m }}}.
  Proof.
    iIntros (Hip ?? Φ) "(Hns & Hh & #Hφ & Ha) HΦ".
    rewrite /receivefrom_all. wp_pures.
    wp_apply (wp_list_fold
                (λ (nodes' : list socket_address) (acc : val), ∃ msgs R,
                    h ↪[ip] s ∗ a @ φ ⤳# (R, T) ∗
                      ⌜is_list (map (λ m, #(m_body m)) msgs) acc⌝ ∗
                      ⌜length nodes' = length msgs⌝ ∗
                      [∗ list] i↦n ∈ nodes', (∃ m, ⌜msgs !! i = Some m⌝ ∗
                                                   ⌜m_sender m = n⌝ ∗ φ m))%I
                (λ n, True)%I (λ n, True)%I _ _ nodes [] with "[] [$Hns Hh Ha]").
    - iIntros (n acc lacc lrem Ψ) "!# (% & Hmsgs & _) HΨ".
      do 3 wp_pure _.
      wp_bind (((rec: "recv" _ := _)%V _))%E.
      iLöb as "IH".
      wp_pures.
      iDestruct "Hmsgs" as (msgs R') "(Hh & Ha & %Hacc & %Hlength & Hnodes)".
      wp_apply (aneris_wp_receivefrom_nodup with "[$Hh $Ha $Hφ]"); [done..|].
      iIntros (m) "(Hh & Ha & Hm)".
      wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      case_bool_decide as Heq.
      + wp_pures.
        wp_apply wp_list_singleton; [done|].
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
        rewrite Hlength -plus_n_O lookup_app_r // -minus_diag_reverse //.
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

  Lemma wp_wait_receivefrom_all Ψ nodes φ ns h s ip a R T (fv : val) :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    (∀ (str : string),
      {{{ True }}}
        fv #str @[ip]
      {{{ (b : bool), RET #b; if b then Ψ str else True }}}) -∗
    {{{ ⌜is_list (map (LitV ∘ LitSocketAddress) nodes) ns⌝ ∗
        h ↪[ip] s ∗
        a ⤇ φ ∗
        a @ φ ⤳# (R, T) }}}
      wait_receivefrom_all #(LitSocket h) ns fv @[ip]
    {{{ vs msgs R', RET vs;
        h ↪[ip] s ∗
        a @ φ ⤳# (R', T) ∗
        ⌜is_list (map (λ m, #(m_body m)) msgs) vs⌝ ∗
        ⌜length nodes = length msgs⌝ ∗
        [∗ list] i↦n ∈ nodes, ∃ m, ⌜msgs !! i = Some m⌝ ∗
                                   ⌜m_sender m = n⌝ ∗ Ψ (m_body m) ∗ φ m }}}.
  Proof.
    iIntros (Hip ??) "#Hfv !#". iIntros (Φ) "(Hns & Hh & #Hφ & Ha) HΦ".
    rewrite /wait_receivefrom_all. wp_pures.
    wp_apply (wp_list_fold
                (λ (nodes' : list socket_address) (acc : val), ∃ msgs R,
                    h ↪[ip] s ∗ a @ φ ⤳# (R, T) ∗
                    ⌜is_list (map (λ m, #(m_body m)) msgs) acc⌝ ∗
                    ⌜length nodes' = length msgs⌝ ∗
                    [∗ list] i↦n ∈ nodes', (∃ m, ⌜msgs !! i = Some m⌝ ∗
                                                 ⌜m_sender m = n⌝ ∗ Ψ (m_body m) ∗ φ m))%I
                (λ n, True)%I
                (λ n, True)%I _ _ nodes [] with "[] [$Hns Hh Ha]").
    - iIntros (n acc lacc lrem Φ') "!# (% & Hmsgs & _) HΦ'".
      do 3 wp_pure _.
      wp_bind (((rec: "recv" _ := _)%V _))%E.
      iLöb as "IH".
      wp_pures.
      iDestruct "Hmsgs" as (msgs R') "(Hh & Ha & %Hacc & %Hlength & Hnodes)".
      wp_apply (aneris_wp_receivefrom_nodup with "[$Hh $Ha $Hφ]"); [done..|].
      iIntros (m) "(Hh & Ha & Hm)".
      wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      case_bool_decide as Heq.
      + wp_pures.
        wp_apply "Hfv"; [done|].
        iIntros ([]) "Hb".
        * wp_if.  wp_apply wp_list_singleton; [done|].
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
          rewrite Hlength -plus_n_O lookup_app_r // -minus_diag_reverse //.
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
    let msg n := mkMessage a n (sprotocol s) m in
    ip = ip_of_address a →
    saddress s = Some a →
    {{{ h ↪[ip] s
          ∗ a ⤳ (R, T)
          ∗ ⌜is_list (map (LitV ∘ LitSocketAddress) nodes) ns⌝
          ∗ [∗ list] n ∈ nodes, (n ⤇ f n ∗ f n (msg n)) }}}
      sendto_all #(LitSocket h) ns #m @[ip]
    {{{ T', RET #(); h ↪[ip] s ∗ a ⤳ (R, T') }}}.
  Proof.
    iIntros (??? Φ) "(Hh & Ha & %Hns & Hnodes) HΦ".
    rewrite /sendto_all. wp_pures.
    wp_apply ((wp_list_iter (λ n, n ⤇ f n ∗ f n (msg n))
                            (λ n, True)
                            (h ↪[ip] s ∗ ∃ T, a ⤳ (R, T)) with "[] [$Hnodes $Hh Ha]")%I); [|eauto|].
    { iIntros (n Ψ)" !# (%Hn & [Hh Ha] & #Hφ & Hmsg) H". iDestruct "Ha" as (T') "Ha".
      wp_pures.
      wp_send "Hmsg"; [rewrite /msg //|].
      iApply "H". iFrame. eauto. }
    iIntros "([Hh Ha] & _)".
    iDestruct "Ha" as (?) "Ha".
    iApply "HΦ". iFrame.
  Qed.

  Lemma wp_sendto_all_nodup f m a h s R T ns nodes Ψ :
    let ip := ip_of_address a in
    let msg n := mkMessage a n (sprotocol s) m in
    saddress s = Some a →
    {{{ h ↪[ip] s
          ∗ a @ Ψ ⤳# (R, T)
          ∗ ⌜is_list (map (LitV ∘ LitSocketAddress) nodes) ns⌝
          ∗ [∗ list] n ∈ nodes, (n ⤇ f n ∗ f n (msg n)) }}}
      sendto_all #(LitSocket h) ns #m @[ip]
    {{{ T', RET #(); h ↪[ip] s ∗ a @ Ψ ⤳# (R, T') }}}.
  Proof.
    iIntros (??? Φ) "(Hh & Ha & %Hns & Hnodes) HΦ".
    rewrite /sendto_all. wp_pures.
    wp_apply ((wp_list_iter (λ n, n ⤇ f n ∗ f n (msg n))
                            (λ n, True)
                            (h ↪[ip] s ∗ ∃ T, a @ Ψ ⤳# (R, T)) with "[] [$Hnodes $Hh Ha]")%I); [|eauto|].
    { iIntros (n ?)" !# (%Hn & [Hh Ha] & #Hφ & Hmsg) H". iDestruct "Ha" as (T') "Ha".
      wp_pures.
      wp_apply (aneris_wp_send_nodup with "[$Hh $Ha $Hφ Hmsg]"); [done..|].
      iIntros "(Hh & Ha)".
      iApply "H". iFrame. eauto. }
    iIntros "([Hh Ha] & _)".
    iDestruct "Ha" as (?) "Ha".
    iApply "HΦ". iFrame.
  Qed.

End library.
