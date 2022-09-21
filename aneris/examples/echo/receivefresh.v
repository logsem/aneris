From aneris.aneris_lang.lib Require Import inject.
From iris.algebra Require Import excl_auth.
From trillium.prelude Require Import finitary.
From aneris.prelude Require Import gset_map.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From aneris.aneris_lang.lib Require Import network_util_proof assert_proof.
From aneris.aneris_lang.lib Require Import list_code list_proof.
Set Default Proof Using "Type".

Definition receivefresh : val :=
  λ: "skt" "ms",
    letrec: "loop" <> :=
    let: "msg" := unSOME (ReceiveFrom "skt") in
    (if: list_mem "msg" "ms" then "loop" #() else "msg") in "loop" #().

Definition pair_to_msg (sa : socket_address)
           (m : message_body * socket_address) : message :=
  mkMessage m.2 sa IPPROTO_UDP m.1.

Instance pair_to_msg_injective sa : Inj eq eq (pair_to_msg sa).
Proof. intros [] [] Heq. by simplify_eq. Qed.

Section receivefresh_proof.
  Context `{dG : !anerisG Mdl Σ}.

  Lemma wp_receivefresh a φ R T h l (ms : list (message_body * socket_address)) :
    is_list ms l →
    R = gset_map (pair_to_msg a) (list_to_set ms) →
    {{{ h ↪[ip_of_address a] (udp_socket (Some a) true) ∗
        a ⤇ φ ∗ a ⤳ (R, T) }}}
      receivefresh #(LitSocket h) l @[ip_of_address a]
    {{{ m, RET (#(m_body m), #(m_sender m));
        ⌜m_destination m = a⌝ ∗
        h ↪[ip_of_address a] (udp_socket (Some a) true) ∗
        a ⤳ ({[m]} ∪ R, T) ∗ φ m }}}.
  Proof.
    iIntros (Hl Heq Φ) "(Hh & #Hsi & Ha) HΦ".
    wp_lam.
    do 5 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_apply (aneris_wp_receivefrom with "[$Hh $Ha $Hsi]"); [try eauto..|].
    iIntros (m) "[%Hdest H]".
    wp_apply wp_unSOME; [done|]. iIntros "_".
    wp_pures.
    wp_apply (wp_list_mem _ ms l (m_body m, m_sender m)); [by iPureIntro|].
    iDestruct "H" as "[H|H]".
    - iDestruct "H" as "(%Hnin & Hh & Ha & _ & Hm)".
      iIntros ([]) "%Hb".
      { rewrite Heq in Hnin. 
        (* Search list_to_set elem_of. *)
        assert ((m_body m, m_sender m) ∈ (list_to_set ms: gset _)) as Hb'.
        { by apply elem_of_list_to_set. }
        apply (gset_map_correct1 (pair_to_msg a)) in Hb'.
        assert (pair_to_msg a (m_body m, m_sender m) = m) as Heq'.
        { destruct m. simplify_eq. done. }
        rewrite Heq' in Hb'.
        done. }
      wp_pures. iApply "HΦ". by iFrame.
    - iDestruct "H" as "(%Hin & Hh & Ha)".
      iIntros ([]) "%Hb"; last first.
      { destruct Hb as [Hb|Hb]; last first.
        { rewrite Heq in Hin. rewrite Hb in Hin. set_solver. }
        rewrite Heq in Hin.
        assert ((m_body m, m_sender m) ∉ (list_to_set ms: gset _)) as Hb'.
        { by apply not_elem_of_list_to_set. }
        apply (gset_map_not_elem_of (pair_to_msg a)) in Hb'; [|apply _].
        assert (pair_to_msg a (m_body m, m_sender m) = m) as Heq'.
        { destruct m. simplify_eq. done. }
        rewrite Heq' in Hb'.
        done. }
      wp_pure _.
      iApply ("IH" with "Hh Ha HΦ").
  Qed.

End receivefresh_proof.
