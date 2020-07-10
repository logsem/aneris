From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import tactics.
From aneris Require Import lang lifting tactics proofmode notation.
From aneris.aneris_lang.lib Require Import assert.

Section code.

  Definition unSOME : ground_lang.val :=
    λ: "p",
    match: "p" with NONE => assert #false | SOME "p'" => "p'" end.

  Definition listen : ground_lang.val :=
    (
      rec: "loop" "socket" "handle" :=
        match: ReceiveFrom "socket" with
          SOME "m" => let: "snd" := (Snd "m") in
                      "handle" (Fst "m") "snd"
        | NONE => "loop" "socket" "handle"
        end
    )%V.

  Definition listen_wait : ground_lang.val :=
    (
      rec: "loop" "socket" :=
        match: ReceiveFrom "socket" with
          SOME "m" => "m"
        | NONE => "loop" "socket"
        end
    )%V.

End code.

Notation "'assert:' e" := (assert (λ: <>, e))%E (at level 99) : expr_scope.

Set Default Proof Using "Type".

Import Network.
Import String.
Import uPred.


Section library.
  Context `{dG : distG Σ}.

  Lemma unSOME_spec n v v' :
    {{{ ⌜v = SOMEV v'⌝ }}}
      ⟨n;unSOME (Val v)⟩
    {{{ RET 〈n;v'〉; True }}}.
  Proof.
    iIntros (Φ ->) "HΦ".
    wp_lam. wp_match. by iApply "HΦ".
  Qed.

  Lemma listen_spec P Q h s R T a handler φ:
    let n := ip_of_address a in
    saddress s = Some a →
    (∀ m,
      {{{ ⌜m_destination m = a⌝ ∗ P ∗
          ((⌜m ∉ R⌝ ∗ h s↦[n]{1/2} (s, {[m]} ∪ R, T) ∗ φ m) ∨
          (⌜m ∈ R⌝ ∗ h s↦[n]{1/2} (s, R, T)))
      }}}
         ⟨n; (Val handler) #(m_body m) #(m_sender m)⟩
      {{{ v, RET 〈n;v〉; Q v }}}) -∗
      {{{ P ∗ h s↦[n]{1/2} (s, R, T) ∗ a ⤇ φ }}}
         ⟨ n; listen #(LitSocket h) (Val handler) ⟩
      {{{ v, RET 〈n;v〉; Q v }}}.
  Proof.
     iIntros (n Haddr) "#Hhandler". iLöb as "IH".
     iAlways. iIntros (Φ) "(HP & Hsocket & #Hsi) HΦ".
     wp_rec. wp_let. rewrite /n. wp_bind (ReceiveFrom _).
     wp_apply (wp_receive_from_2 with "[$]"); first done.
     iIntros (r) "[(-> & Hs) | Hrd ]"; simpl.
     - wp_pures. iApply ("IH" with "[-HΦ]"); by iFrame.
     - iDestruct "Hrd" as (m Hdst ->) "[ (% & Hs & _ & Hφ) | (% & Hs) ]"; wp_pures;
         wp_apply ("Hhandler" with "[-HΦ] [HΦ]"); eauto with iFrame.
  Qed.

  Lemma listen_wait_spec h s R T a φ :
    let n := ip_of_address a in
    saddress s = Some a →
  {{{ h s↦[n]{1/2} (s, R, T) ∗ a ⤇ φ}}}
     ⟨ n; listen_wait #(LitSocket h) ⟩
  {{{ m, RET 〈n;(#(m_body m), #(m_sender m))〉;
      ((⌜m ∉ R⌝ ∗ h s↦[n]{1/2} (s, {[ m ]} ∪ R, T) ∗ a ⤇ φ ∗ ▷ φ m) ∨
       ⌜m ∈ R⌝ ∗ h s↦[n]{1/2} (s, R, T))
  }}}.
  Proof.
    iIntros (n Haddr Φ) "(Hs & #Hsi) HΦ".
    iLöb as "IH". wp_rec.
    wp_apply (wp_receive_from_2 with "[$Hs]"); first done; try iFrame "#".
    iIntros (r)  "[(-> & Hs) | Hrd ]"; simpl; wp_pures.
    - by iApply ("IH" with "Hs HΦ").
    - iDestruct "Hrd" as (m Hdst ->) "[ (% & Hs & _ & Hφ) | (% & Hs) ]"; wp_pures.
      + iApply "HΦ". iLeft. eauto with iFrame.
      + iApply "HΦ". iRight. eauto with iFrame.
  Qed.

End library.
