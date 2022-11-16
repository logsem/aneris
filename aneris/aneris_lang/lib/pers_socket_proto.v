From aneris.aneris_lang Require Import tactics network lifting.
From aneris.aneris_lang Require Import lang tactics proofmode.

Section def.
  Context `{!anerisG mdl Σ}.

  Definition mapsto_messages_pers_def a φ q s : iProp Σ :=
    ⌜∀ m, Persistent (φ m)⌝ ∗ a ⤳{q} s ∗ [∗ set] m ∈ s.1, φ m.

  Definition mapsto_messages_pers_aux : seal mapsto_messages_pers_def. by eexists. Qed.
  Definition mapsto_messages_pers := mapsto_messages_pers_aux.(unseal).
  Definition mapsto_messages_pers_eq :
    @mapsto_messages_pers = @mapsto_messages_pers_def :=
    mapsto_messages_pers_aux.(seal_eq).

End def.

Notation "a @ φ ⤳#{ q } s" := (mapsto_messages_pers a φ q s)
  (at level 20, q at level 50, format "a  @  φ  ⤳#{ q }  s") : bi_scope.
Notation "a @ φ ⤳# s" := (a @ φ ⤳#{ 1 } s)%I (at level 20) : bi_scope.

Section pers_messages_lemmas.
  Context `{!anerisG mdl Σ}.

  Global Instance mapsto_messages_pers_timeless a φ q s :
    (∀ m, Timeless (φ m)) →
    Timeless (a @ φ ⤳#{ q } s).
  Proof.
    rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def; apply _.
  Qed.

  Lemma mapsto_messages_pers_alloc a φ R T :
    (∀ m, Persistent (φ m)) →
    a ⤳ (R, T) -∗
    ([∗ set] m ∈ R, φ m) -∗
    a @ φ ⤳# (R, T).
  Proof.
    rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def.
    iIntros (?) "??". by iFrame.
  Qed.

  Lemma mapsto_messages_pers_alloc_empty a φ T :
    (∀ m, Persistent (φ m)) →
    a ⤳ (∅, T) -∗
    a @ φ ⤳# (∅, T).
  Proof.
    iIntros (?) "Hm".
    iApply (mapsto_messages_pers_alloc with "Hm").
    rewrite big_sepS_empty //.
  Qed.

  Lemma aneris_wp_pers_receivefrom_gen E a ip s h φ R T :
    ip_of_address a = ip →
    saddress s = Some a →
    {{{ h ↪[ip] s ∗ a @ φ ⤳# (R, T) ∗ a ⤇ φ }}}
      ReceiveFrom #(LitSocket h) @[ip] E
    {{{ r, RET r;
        (⌜r = NONEV⌝ ∗ h ↪[ip] s ∗ a @ φ ⤳# (R, T)) ∨
        (∃ m, ⌜r = SOMEV (#(m_body m), #(m_sender m))⌝ ∗ ⌜m_destination m = a⌝ ∗
              h ↪[ip] s ∗ a @ φ ⤳# ({[m]} ∪ R, T) ∗ φ m )}}}.
  Proof.
    iIntros (<- ? Φ) "(Hh & Ha & #Hφ) HΦ".
    rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def.
    iDestruct "Ha" as "(% & Ha & #HR) /=".
    wp_apply (aneris_wp_receivefrom_gen with "[$]"); [done..|].
    iIntros (?) "[(% & Hh & Ha) | H]"; subst.
    { iApply "HΦ". iLeft. by iFrame "#∗". }
    iDestruct "H" as (m) "(% & % & [(% & Hh & Ha & #Hm) | (% & Hh & Ha)])";
      simplify_eq.
    - iApply "HΦ". iRight. iFrame. iExists _.
      do 2 (iSplit; [done|]).
      iFrame "# %". iFrame.
      rewrite big_sepS_union ?big_sepS_singleton; [|set_solver].
      iFrame "#"; auto.
    - iApply "HΦ". iRight. iExists _.
      do 2 (iSplit; [done|]).
      iFrame.
      rewrite subseteq_union_1_L; [|set_solver].
      iFrame. iFrame "# %".
      by iApply big_sepS_elem_of.
  Qed.

  Lemma aneris_wp_pers_receivefrom E a ip s h φ R T :
    ip_of_address a = ip →
    saddress s = Some a →
    sblock s = true →
    {{{ h ↪[ip] s ∗ a @ φ ⤳# (R, T) ∗ a ⤇ φ }}}
      ReceiveFrom #(LitSocket h) @[ip] E
    {{{ m, RET SOMEV (#(m_body m), #(m_sender m));
          h ↪[ip] s ∗ a @ φ ⤳# ({[m]} ∪ R, T) ∗ φ m }}}.
  Proof.
    iIntros (<- ?? Φ) "(Hh & Ha & #Hφ) HΦ".
    rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def.
    iDestruct "Ha" as "(% & Ha & #HR) /=".
    wp_apply (aneris_wp_receivefrom with "[$]"); [done..|].
    iIntros (?) "[% [(% & Hh & Ha & _ & #Hm) | (% & Hh & Ha)]]".
    { iApply "HΦ". iFrame.
      rewrite big_sepS_union ?big_sepS_singleton; [|set_solver].
      iFrame "% #". }
    iApply "HΦ". iFrame.
    rewrite big_sepS_elem_of_acc //.
    iDestruct "HR" as "[#Hm HR]".
    rewrite subseteq_union_1_L; [|set_solver].
    iFrame. iFrame "# %".
    by iApply "HR".
  Qed.

  Lemma aneris_wp_pers_send ip φ ψ m h a f E s R T :
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := mkMessage f a m in
    {{{ ▷ h ↪[ip] s ∗ ▷ f @ ψ ⤳# (R, T) ∗ ▷ a ⤇ φ ∗ ▷ φ msg }}}
      SendTo #(LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ f @ ψ ⤳# (R, {[ msg ]} ∪ T) }}}.
  Proof.
    iIntros (Hip Hskt msg Φ) "(Hsh & Hf & #Hproto & Hmsg) HΦ".
    rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def.
    iDestruct "Hf" as "(>% & Hf & #HR) /=".
    wp_send "Hmsg"; [done|].
    iApply "HΦ". iFrame. iFrame "% #".
  Qed.

  Lemma aneris_wp_send_pers_duplicate ψ ip m h a f E s R T:
    ip_of_address f = ip →
    saddress s = Some f ->
    let msg := mkMessage f a m in
    msg ∈ T →
    {{{ ▷ h ↪[ip] s ∗ ▷ f @ ψ ⤳# (R, T) ∗ a ⤇ ψ }}}
      SendTo #(LitSocket h) #m #a @[ip] E
    {{{ RET #(String.length m); h ↪[ip] s ∗ f @ ψ ⤳# (R, T) }}}.
  Proof.
    iIntros (Hip Hskt msg Hmsg Φ) "(Hsh & Hf & #Hψ) HΦ".
    rewrite mapsto_messages_pers_eq /mapsto_messages_pers_def.
    iDestruct "Hf" as "(>% & Hf & #HR) /=".
    wp_send_duplicate.
    iApply "HΦ". iFrame. iFrame "% #".
  Qed.

End pers_messages_lemmas.
