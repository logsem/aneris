From aneris.aneris_lang Require Import lang tactics proofmode notation.
From aneris.aneris_lang.lib Require Import assert list map.
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

Definition receivefrom_all : base_lang.val :=
  λ: "socket" "nodes",
  letrec: "recv" "n" :=
    let: "msg" := unSOME (ReceiveFrom "socket") in
    let: "sender" := Snd "msg" in
    if: "sender" = "n" then "msg"
    else "recv" "n" in
  list_fold  (λ: "acc" "n", "recv" "n" :: "acc") [] "nodes".

Import Network.

Section library.
  Context `{dG : anerisG Mdl Σ}.

  Lemma wp_unSOME ip v v' :
    {{{ ⌜v = SOMEV v'⌝ }}} unSOME (Val v) @[ip] {{{ RET v'; True }}}.
  Proof.
    iIntros (Φ ->) "HΦ".
    wp_lam. wp_match. by iApply "HΦ".
  Qed.

  Lemma wp_receivefrom_all nodes φ ns h s a R T :
    let ip := ip_of_address a in
    {{{ a ⤇ φ
          ∗ ⌜is_list (map (LitV ∘ LitSocketAddress) nodes) ns⌝
          ∗ h ↪[ip] s
          ∗ a ⤳ (R, T) }}}
      receivefrom_all #(LitSocket h) ns @[ip]
    {{{ vs msgs R', RET vs;
        h ↪[ip] s
          ∗ a ⤳ (R', T) 
          ∗ ⌜is_list (map (λ m, (#(m_body m), #(m_sender m))%V) msgs) vs⌝
          ∗ [∗ list] n ∈ nodes, (∃ m, ⌜m ∈ msgs⌝ ∗ ⌜m_sender m = n⌝ ∗ ⌜m ∈ R'⌝ ∗ φ m)  }}}.
  Proof.
    (* TODO: This does not work; what about duplicate messages??? *)
    Admitted. 

  Lemma wp_sendto_all f m a h s R T ns nodes :
    let ip := ip_of_address a in
    let msg n := mkMessage a n (sprotocol s) m in
    saddress s = Some a →
    {{{ h ↪[ip] s
          ∗ a ⤳ (R, T)
          ∗ ⌜is_list (map (LitV ∘ LitSocketAddress) nodes) ns⌝
          ∗ [∗ list] n ∈ nodes, (n ⤇ f n ∗ f n (msg n)) }}}
      sendto_all #(LitSocket h) ns #m @[ip]
    {{{ R' T', RET #(); h ↪[ip] s ∗ a ⤳ (R', T') ∗ ⌜∀ n, n ∈ nodes → msg n ∈ T'⌝ }}}.
  Proof.
    iIntros (??? Φ) "(Hh & Ha & %Hns & Hnodes) HΦ".
    rewrite /sendto_all. wp_pures.
    wp_apply ((wp_list_iter (λ n, n ⤇ f n ∗ f n (msg n))
                            (λ n, True)
                            (h ↪[ip] s ∗ ∃ R T, a ⤳ (R, T)) with "[] [$Hnodes $Hh Ha]")%I); [|eauto|].
    { iIntros (n Ψ)" !# (%Hn & [Hh Ha] & #Hφ & Hmsg) H". iDestruct "Ha" as (R' T') "Ha".
      wp_pures.
      wp_send "Hmsg"; [rewrite /msg //|].
      iApply "H". iFrame. eauto. }
    iIntros "(Hh & Ha)".
  Admitted.

End library.
