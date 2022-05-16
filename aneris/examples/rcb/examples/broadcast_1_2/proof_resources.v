From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From aneris.aneris_lang Require Import proofmode.
From aneris.prelude Require Import time.
From aneris.examples.rcb Require Import spec.
From aneris.examples.rcb.examples.broadcast_1_2 Require Import prog.

Section Resources.
  Context `{!anerisG Mdl Σ, inG Σ (exclR unitO), !RCB_events, !RCB_resources Mdl Σ}.

  Definition token (γ : gname) : iProp Σ := own γ (Excl ()).

  Lemma exclusive_token γ : token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Definition Nsys := nroot.@"sys".

  (* The invariant satisfied by the two nodes.
     Only one node is broadcasting. The two broadcast messages are e1 and e2.
     Broadcasting each message requires tokens γS1 and γS2, respectively. *)
  Definition inv_sys γS1 γS2 : iProp Σ :=
    ∃ h, OwnGlobal h ∗
      (* Case 0: no message has been sent *)
      ((⌜ h = ∅ ⌝)
      (* Case 1: one message e1 has been sent, along with the token γS1. This token is used so that
         the message e1 is sent once. Conversely, while a user own the token, it knows that the
         message e1 has not yet been sent. *)
       ∨ (∃ e1, ⌜ h = {[ e1 ]} ⌝ ∗ ⌜ GE_payload e1 = #1 ⌝ ∗ token γS1)
      (* Case 1: another message e2 has been sent, along with the token γS2. This token is used so
         that the message e1 is sent once. Conversly, while a user own the token, it knows that the
         message e2 has not yet been sent. *)
       ∨ (∃ e1 e2, ⌜ h = {[ e1; e2 ]} ⌝ ∗
                   token γS1 ∗ token γS2 ∗
                   ⌜ GE_payload e1 = #1 ⌝ ∗ ⌜ GE_payload e2 = #2 ⌝ ∗
                   ⌜ vector_clock_lt (GE_vc e1) (GE_vc e2) ⌝)).
End Resources.
