From aneris.prelude Require Import gset_map.
From aneris.aneris_lang Require Import proofmode.
From aneris.aneris_lang.lib Require Import set_proof list_proof map_proof network_util_proof.
From aneris.aneris_lang.lib Require Import nodup_code.

Set Default Proof Using "Type".

Section nodup_specs.
  Context `{dG : anerisG Mdl Σ}.

  Definition is_rcvset (R : gset message) (a : socket_address) (v : val) : Prop :=
    is_set (gset_map (λ m, (m_body m, m_sender m)) R) v ∧
    set_Forall (λ m, m_destination m = a) R.

  Lemma wp_nodup_empty a :
    {{{ True }}}
      nodup_empty #() @[ip_of_address a]
    {{{ v, RET v; ⌜is_rcvset (∅ : gset message) a v⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_set_empty (message_body * socket_address)); [done|].
    iIntros (??).
    iApply "HΦ".
    iPureIntro.
    split; [done|].
    apply set_Forall_empty.
  Qed.

  Lemma wp_receivefrom_nodup ip a φ h s R T v :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    {{{ h ↪[ip] s ∗ a ⤇ φ ∗ a ⤳ (R, T) ∗ ⌜is_rcvset R a v⌝ }}}
      receivefrom_nodup v #(LitSocket h) @[ip]
    {{{ m v', RET ((#(m_body m), #(m_sender m)), v')%V;
          h ↪[ip] s ∗ a ⤳ ({[m]} ∪ R, T) ∗ φ m ∗
          ⌜m_destination m = a⌝ ∗ ⌜is_rcvset ({[m]} ∪ R) a v'⌝ ∗ ⌜m ∉ R⌝ }}}.
  Proof.
    iIntros (-> ?? Φ) "(Hh & #Hφ & Ha & [%Hv %Hdest]) HΦ".
    wp_rec. do 5 wp_pure _.
    iLöb as "IH" forall (R Hv Hdest).
    wp_pures.
    wp_apply (aneris_wp_receivefrom with "[$Hh $Hφ $Ha]"); [done..|].
    iIntros (?) "[%Hd [(%Hm & Hh & Ha & _ & Hm) | (%Hm & Hh & Ha)]]".
    - wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      wp_apply (wp_set_mem _ (m_body m, m_sender m) with "[//]");
        iIntros ([] Hb).
      { apply gset_map_correct2 in Hb.
        destruct Hb as [m' [? Hm']].
        rewrite -(Hdest _ Hm') in Hd.
        simplify_eq.
        by rewrite (message_inv m m') in Hm. }
      wp_pures.
      wp_apply (wp_set_add _ (m_body m, m_sender m) with "[//]").
      iIntros (v' Hv').
      wp_pures. iApply "HΦ".
      iFrame. iPureIntro.
      rewrite -(gset_map_singleton (λ m, (m_body m, m_sender m)) m) -gset_map_union in Hv'.
      do 3 (split; auto).
      intros ? [-> %elem_of_singleton_1 | ?]%elem_of_union; [done|].
      by apply Hdest.
    - wp_apply wp_unSOME; [done|]; iIntros "_".
      wp_pures.
      wp_apply (wp_set_mem _ (m_body m, m_sender m) with "[//]").
      iIntros ([] Hb); last first.
      { by apply (gset_map_correct1 (λ m, (m_body m, m_sender m))) in Hm. }
      wp_if.
      iApply ("IH" with "[//] [//] Hh Ha HΦ").
  Qed.

  Definition is_rcvset_log l R a : iProp Σ :=
    ∃ log, l ↦[ip_of_address a] log ∗ ⌜is_rcvset R a log⌝.

  Definition wp_nodup_rcv (rcv : val) a s l : iProp Σ :=
    □ (∀ h φ R T,
          {{{ h ↪[ip_of_address a] s ∗ a ⤇ φ ∗ a ⤳ (R, T) ∗ is_rcvset_log l R a }}}
            rcv #(LitSocket h) @[ip_of_address a]
          {{{ m, RET (#(m_body m), #(m_sender m))%V;
                h ↪[ip_of_address a] s ∗ a ⤳ ({[m]} ∪ R, T) ∗ φ m ∗
                is_rcvset_log l ({[m]} ∪ R) a ∗ ⌜m_destination m = a⌝ ∗ ⌜m ∉ R⌝ }}}).

  Lemma wp_nodup_init a s :
    saddress s = Some a →
    sblock s = true →
    {{{ True }}}
      nodup_init #() @[ip_of_address a]
    {{{ l rcv, RET rcv; is_rcvset_log l ∅ a ∗ wp_nodup_rcv rcv a s l }}}.
  Proof.
    iIntros (?? Φ) "_ HΦ".
    rewrite /nodup_init. wp_pures.
    wp_apply wp_nodup_empty; [done|].
    iIntros (log Hlog).
    wp_alloc l as "Hl". wp_pures.
    iApply "HΦ".
    iSplitL "Hl".
    { iExists _. by iFrame. }
    iIntros "!#" (h φ R T Ψ) "!# (Hh & #Hφ & Ha & Hrcv) HΨ".
    iDestruct "Hrcv" as (log') "[Hl %HR]".
    wp_pures. wp_load.
    wp_apply (wp_receivefrom_nodup with "[$Hh $Ha $Hφ //]"); [done..|].
    iIntros (m v) "(Hh & Ha & Hm & % & % & %)".
    wp_pures. wp_store.
    iApply "HΨ". iFrame. iFrame "%".
    iExists _. by iFrame.
  Qed.

  Lemma wp_receivefrom_nodup_set ip a φ h s R T addrs av (rcv : val) l :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    □ (∀ m, φ m → ⌜m_sender m ∈ addrs⌝)%I -∗
    wp_nodup_rcv rcv a s l -∗
    {{{ h ↪[ip] s ∗ a ⤇ φ ∗ a ⤳ (R, T) ∗ is_rcvset_log l R a ∗ ⌜is_set addrs av⌝ }}}
      receivefrom_nodup_set #(LitSocket h) rcv av @[ip]
    {{{ (d : gmap socket_address message_body) vd ms, RET vd;
          ⌜is_map vd d⌝ ∗ ⌜dom d = addrs⌝ ∗
          ([∗ map] n ↦ b ∈ d, ∃ (m : message),
              ⌜m ∈ ms⌝ ∗ ⌜m_destination m = a⌝ ∗ ⌜m_sender m = n⌝ ∗ ⌜m_body m = b⌝ ∗ φ m) ∗
          ⌜ms ## R⌝ ∗
          h ↪[ip] s ∗ a ⤳ (ms ∪ R, T) ∗ is_rcvset_log l (ms ∪ R) a }}}.
  Proof.
    iIntros (-> ??) "#Hincl #Hrecv". iIntros (Φ) "!# (Hh & #Hφ & Ha & Hlog & %Haddrs) HΦ".
    rewrite /receivefrom_nodup_set. wp_pures.
    wp_apply (wp_map_empty socket_address message_body); [done|].
    iIntros (vd Hd).
    wp_alloc lmsgs as "Hmsgs".
    do 3 wp_pure _.
    iAssert (∃ (d : gmap socket_address message_body) vd ms,
                ⌜is_map vd d⌝ ∗
                lmsgs ↦[ip_of_address a] vd ∗
                is_rcvset_log l (ms ∪ R) a ∗
                a ⤳ (ms ∪ R, T) ∗
                ([∗ map] n ↦ b ∈ d, ∃ (m : message),
                    ⌜m ∈ ms⌝ ∗ ⌜m_destination m = a⌝ ∗ ⌜m_sender m = n⌝ ∗ ⌜m_body m = b⌝ ∗ φ m) ∗
                ⌜ms ## R⌝)%I
      with "[Hmsgs Ha Hlog]" as "Hlogs".
    { iExists ∅, _, ∅. rewrite union_empty_l_L. iFrame "%∗".
      iSplit; [done|]. iPureIntro; set_solver. }
    clear vd Hd. do 2 wp_pure _.
    iLöb as "IH" forall (R).
    wp_pures.
    iDestruct "Hlogs" as (d vd ms) "(%Hd & Hmsgs & Hlog & Ha & Hms & %)".
    wp_load.
    wp_apply wp_map_dom; [done|].
    iIntros (??).
    wp_apply (wp_set_equal _ (dom d)); [auto|].
    iIntros ([] Hb); wp_if.
    { wp_load. iApply "HΦ". iSplit; [done|]. iFrame. auto. }
    wp_apply ("Hrecv" with "[$Hh $Hφ $Ha $Hlog]").
    iIntros (m) "(Hh & Ha & Hm & Hlog & % & %)".
    wp_pures. wp_load. wp_pures.
    wp_apply (wp_map_insert $! Hd).
    iIntros (d' Hd').
    wp_store.
    iApply ("IH" with "Hh HΦ").
    iExists (<[_:=_]> d), _, _.
    rewrite !union_assoc_L.
    iFrame.
    iSplit; [done|].
    iSplitL; [|iPureIntro; set_solver].
    iApply (big_sepM_insert_2 with "[Hm] [Hms]").
    { iExists m. iSplit; [iPureIntro; set_solver|]. eauto. }
    iApply (big_sepM_impl with "Hms").
    iIntros "!#" (???) "(%&%&%&%&%&?)".
    iExists m0. iSplit; [iPureIntro; set_solver|]. eauto.
  Qed.

End nodup_specs.
