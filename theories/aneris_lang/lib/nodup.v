From aneris.aneris_lang Require Import proofmode notation.
From aneris.aneris_lang.lib Require Import util set network_util.
From iris_string_ident Require Import ltac2_string_ident.
Set Default Proof Using "Type".
Import Network.

Definition receivefrom_nodup : val :=
  λ: "socket" "msgs",
  (rec: "loop" <> :=
     let: "msg" := unSOME (ReceiveFrom "socket") in
     if: set_mem "msg" "msgs" then "loop" #()
     else ("msg", set_add "msg" "msgs")) #().

Definition nodup_init : val := set_empty.

Section nodup_specs.
  Context `{dG : anerisG Mdl Σ}.

  Local Definition msg_toval : message_body * socket_address → val :=
    λ '(b, s), (#b, #s)%V.

  Local Instance: Inj (=) (=) msg_toval.
  Proof. intros [] []. by inversion 1; simplify_eq. Qed.

  Definition is_nodup (R : gset message) (a : socket_address) (v : val) : Prop :=
    is_set msg_toval (gset_map (λ m, (m_body m, m_sender m)) R) v ∧
    set_Forall (λ m, m_destination m = a) R.

  Lemma wp_nodup_init a :
    {{{ True }}}
      nodup_init #() @[ip_of_address a]
    {{{ v, RET v; ⌜is_nodup (∅ : gset message) a v⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_set_empty msg_toval); [done|].
    iIntros (??).
    iApply "HΦ". eauto.
  Qed.

  Lemma wp_receivefrom_nodup ip a φ h s R T v :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    {{{ h ↪[ip] s ∗ a ⤇ φ ∗ a ⤳ (R, T) ∗ ⌜is_nodup R a v⌝ }}}
      receivefrom_nodup #(LitSocket h) v @[ip]
    {{{ m v', RET ((#(m_body m), #(m_sender m)), v')%V;
          h ↪[ip] s ∗ a ⤳ ({[m]} ∪ R, T) ∗ ⌜is_nodup ({[m]} ∪ R) a v'⌝ ∗ φ m }}}.
  Proof.
    iIntros (-> ?? Φ) "(Hh & #Hφ & Ha & [%Hv %Hdest]) HΦ".
    wp_rec. do 3 wp_pure _.
    iLöb as "IH" forall (R Hv Hdest).
    wp_pures.
    wp_apply (aneris_wp_receivefrom with "[$Hh $Hφ $Ha]"); [done..|].
    iIntros (?) "[%Hd [(%Hm & Hh & Ha & _ & Hm) | (%Hm & Hh & Ha)]]".
    - wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      wp_apply (wp_set_mem msg_toval _ (_,_) with "[//]").
      iIntros ([] Hb).
      { apply gset_map_correct2 in Hb.
        destruct Hb as [m' [? Hm']].
        rewrite -(Hdest _ Hm') in Hd.
        simplify_eq.
        by rewrite (message_inv m m') in Hm. }
      wp_pures.
      wp_apply (wp_set_add msg_toval _ (_,_) with "[//]").
      iIntros (v' Hv').
      wp_pures. iApply "HΦ".
      iFrame. iPureIntro.
      rewrite -(gset_map_singleton (λ m, (m_body m, m_sender m)) m) -gset_map_union in Hv'.
      split; auto.
      intros ? [-> %elem_of_singleton_1 | ?]%elem_of_union; [done|].
      by apply Hdest.
    - wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      wp_apply (wp_set_mem msg_toval _ (_,_) with "[//]").
      iIntros ([] Hb); last first.
      { by apply (gset_map_correct1 (λ m, (m_body m, m_sender m))) in Hm. }
      wp_if.
      iApply ("IH" with "[//] [//] Hh Ha HΦ").
  Qed.

End nodup_specs.
