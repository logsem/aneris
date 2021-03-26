From aneris.aneris_lang Require Import proofmode notation.
From aneris.aneris_lang.lib Require Import util set list network_util.
From iris_string_ident Require Import ltac2_string_ident.
Set Default Proof Using "Type".
Import Network.

Definition receivefrom_nodup : val :=
  λ: "rcvlog" "socket",
  (rec: "loop" <> :=
     let: "msg" := unSOME (ReceiveFrom "socket") in
     if: set_mem "msg" "rcvlog" then "loop" #()
     else ("msg", set_add "msg" "rcvlog")) #().

Definition receivefrom_nodup_n : val :=
  rec: "receivefrom_nodup_n" "socket" "msgs" "n" :=
    if: "n" = #0 then (list_nil, "msgs") else
    let: "tmp" := receivefrom_nodup "msgs" "socket" in
    let: "m" := Fst "tmp" in
    let: "msgs'" := Snd "tmp" in
    let: "tailmsgs" := "receivefrom_nodup_n" "socket" "msgs'" ("n" - #1) in
    let: "ms" := Fst "tailmsgs" in
    let: "msgs''" := Snd "tailmsgs" in
    ("m" :: "ms", "msgs''").

Definition nodup_empty : val := set_empty.

Definition nodup_init : val :=
  λ: <>,
    let: "log" := ref (nodup_empty #()) in
    λ: "socket",
      let: "tmp"  := receivefrom_nodup !"log" "socket" in
      let: "msg"  := Fst "tmp" in
      let: "log'" := Snd "tmp" in
      "log" <- "log'";;
      "msg".

Definition receivefrom_nodup_set : val :=
  λ: "socket" "rcv" "addrs",
  let: "sndrs" := ref (set_empty #()) in
  let: "msgs"  := ref (set_empty #()) in
  (rec: "loop" <> :=
     if: set_equal !"sndrs" "addrs" then !"msgs" else
     let: "msg" := "rcv" "socket" in
     let: "sndr" := Snd "msg" in
     (* if: set_mem "sndr" !"sndrs" then "loop" #() *)
     (* else *)
     "sndrs" <- set_add "sndr" !"sndrs";;
     "msgs"  <- set_add "msg"  !"msgs";;
     "loop" #()) #().

Section nodup_specs.
  Context `{dG : anerisG Mdl Σ}.

  Definition msg_toval : message_body * socket_address → val :=
    λ '(b, s), (#b, #s)%V.

  Local Instance: Inj (=) (=) msg_toval.
  Proof. intros [] []. by inversion 1; simplify_eq. Qed.

  Definition is_rcvset (R : gset message) (a : socket_address) (v : val) : Prop :=
    is_set msg_toval (gset_map (λ m, (m_body m, m_sender m)) R) v ∧
    set_Forall (λ m, m_destination m = a) R.

  Lemma wp_nodup_empty a :
    {{{ True }}}
      nodup_empty #() @[ip_of_address a]
    {{{ v, RET v; ⌜is_rcvset (∅ : gset message) a v⌝ }}}.
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
    {{{ h ↪[ip] s ∗ a ⤇ φ ∗ a ⤳ (R, T) ∗ ⌜is_rcvset R a v⌝ }}}
      receivefrom_nodup v #(LitSocket h) @[ip]
    {{{ m v', RET ((#(m_body m), #(m_sender m)), v')%V;
          h ↪[ip] s ∗ a ⤳ ({[m]} ∪ R, T) ∗ φ m ∗
          ⌜is_rcvset ({[m]} ∪ R) a v'⌝ ∗ ⌜m ∉ R⌝ }}}.
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
      do 2 (split; auto).
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

  Lemma wp_receivefrom_nodup_n ip a φ h s R T v (n : nat) :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    {{{ h ↪[ip] s ∗ a ⤇ φ ∗ a ⤳ (R, T) ∗ ⌜is_rcvset R a v⌝ }}}
      receivefrom_nodup_n #(LitSocket h) v #n @[ip]
    {{{ ms vms v' R', RET (vms, v')%V;
          ⌜is_rcvset R' a v'⌝ ∗ ⌜length ms = n⌝ ∗
          ⌜is_list (map (λ m, (#(m_body m), #(m_sender m))%V) ms) vms⌝ ∗
          h ↪[ip] s ∗ a ⤳ (R', T) ∗ [∗ list] m ∈ ms, φ m }}}.
  Proof.
    iIntros (-> ?? Φ) "(Hh & #Hφ & Ha & %Hv) HΦ".
    iInduction n as [|n'] "IH" forall (Φ v R Hv); wp_rec; wp_pures.
    { iApply ("HΦ" $! []). iFrame. auto. }
    wp_apply (wp_receivefrom_nodup with "[$Hh $Hφ $Ha //]"); [done..|].
    iIntros (m v') "(Hh & Ha & Hm & %Hv' & %Hin)".
    wp_pures.
    assert ((S n' - 1)%Z = n') as -> by lia.
    wp_apply ("IH" with "[//] Hh Ha").
    iIntros (ms vms v'' R') "(%Hv'' & %Hlen & %Hvms & Hh & Ha & Hφms)".
    wp_pures.
    wp_apply wp_list_cons; [done|].
    iIntros (vms' Hvms'). wp_pures.
    iApply ("HΦ" $! (m :: ms)).
    iFrame. iFrame "%".
    simpl. rewrite Hlen //.
  Qed.

  Definition is_rcvset_log l R a : iProp Σ :=
    ∃ log, l ↦[ip_of_address a] log ∗ ⌜is_rcvset R a log⌝.

  Definition wp_nodup_rcv (rcv : val) a s l : iProp Σ :=
    □ (∀ h φ R T,
          {{{ h ↪[ip_of_address a] s ∗ a ⤇ φ ∗ a ⤳ (R, T) ∗ is_rcvset_log l R a }}}
            rcv #(LitSocket h) @[ip_of_address a]
          {{{ m, RET (#(m_body m), #(m_sender m))%V;
                h ↪[ip_of_address a] s ∗ a ⤳ ({[m]} ∪ R, T) ∗ φ m ∗
                is_rcvset_log l ({[m]} ∪ R) a ∗ ⌜m ∉ R⌝ }}}).

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
    iIntros (m v) "(Hh & Ha & Hm & % & %)".
    wp_pures. wp_store.
    iApply "HΨ". iFrame. iFrame "%".
    iExists _. by iFrame.
  Qed.

  Global Instance :  Inj (=) (=) (LitV ∘ LitSocketAddress).
  Proof. intros ??. by inversion 1. Qed.

  Lemma wp_receivefrom_set ip a φ h s R T addrs av (rcv : val) l :
    ip = ip_of_address a →
    saddress s = Some a →
    sblock s = true →
    □ (∀ m, φ m → ⌜m_sender m ∈ addrs⌝)%I -∗
    wp_nodup_rcv rcv a s l -∗
    {{{ h ↪[ip] s ∗ a ⤇ φ ∗ a ⤳ (R, T) ∗ is_rcvset_log l R a ∗
        ⌜is_set (LitV ∘ LitSocketAddress) addrs av⌝ }}}
      receivefrom_nodup_set #(LitSocket h) rcv av @[ip]
    {{{ ms mv R', RET mv;
          ⌜is_set msg_toval (gset_map (λ m, (m_body m, m_sender m)) ms) mv⌝ ∗
          h ↪[ip] s ∗ a ⤳ (R', T) ∗ is_rcvset_log l R' a ∗
          ([∗ set] n ∈ addrs, ∃ m, ⌜m ∈ ms⌝ ∗ ⌜m_sender m = n⌝ ∗ φ m) }}}.
  Proof.
    iIntros (-> ??) "#Hincl #Hrecv". iIntros (Φ) "!# (Hh & #Hφ & Ha & Hlog & %Haddrs) HΦ".
    rewrite /receivefrom_nodup_set. wp_pures.
    wp_apply (wp_set_empty (LitV ∘ LitSocketAddress)); [done|].
    iIntros (vsndrs Hsndrs).
    wp_alloc lsndr as "Hsndr". wp_pures.
    wp_apply (wp_set_empty msg_toval); [done|].
    iIntros (vmsgs Hmsg).
    wp_alloc lmsg as "Hmsg". do 3 wp_pure _.
    iAssert (∃ sndrs msgs vsndrs vmsgs,
                lsndr ↦[ip_of_address a] vsndrs ∗
                lmsg  ↦[ip_of_address a] vmsgs ∗
                ⌜is_set (LitV ∘ LitSocketAddress) sndrs vsndrs⌝ ∗
                ⌜is_set msg_toval (gset_map (λ m, (m_body m, m_sender m)) msgs) vmsgs⌝ ∗
                [∗ set] n ∈ sndrs, ∃ m, ⌜m ∈ msgs⌝ ∗ ⌜m_sender m = n⌝ ∗ φ m)%I
      with "[Hmsg Hsndr]" as "Hlogs".
    { iExists ∅, ∅, _, _. iFrame. by iFrame "%". }
    clear Hsndrs vsndrs Hmsg vmsgs.
    iLöb as "IH" forall (R).
    wp_pures.
    iDestruct "Hlogs" as (sndrs msgs vsendrs vmsgs)
                           "(Hsndrs & Hmsgs & % & % & Hms)".
    wp_load.
    wp_apply (wp_set_equal (LitV ∘ LitSocketAddress)); [auto|].
    iIntros ([] Hb); wp_if.
    { wp_load. iApply ("HΦ" $! msgs). rewrite Hb. by iFrame. }
    wp_apply ("Hrecv" with "[$Hh $Hφ $Ha $Hlog]").
    iIntros (m) "(Hh & Ha & Hm & Hlog & %)".
    wp_pures. wp_load.
    wp_apply (wp_set_add (LitV ∘ LitSocketAddress) with "[//]").
    iIntros (vsndrs' Hsndrs'). wp_store.
    wp_load.
    wp_apply (wp_set_add msg_toval _ (_,_)  with "[//]").
    iIntros (vmsgs' Hmsgs').
    wp_store.
    iApply ("IH" with "Hh Ha Hlog [HΦ]"); last first.
    { iExists ({[m_sender m]} ∪ sndrs), ({[m]} ∪ msgs), _, _.
      iFrame.
      rewrite -(gset_map_singleton (λ m, (m_body m, m_sender m)) m)
              -gset_map_union in Hmsgs'.
      iFrame "%".
      destruct (decide (m_sender m ∈ sndrs)).
      { assert ({[m_sender m]} ∪ sndrs = sndrs) as -> by set_solver.
        iApply (big_sepS_impl with "Hms").
        iIntros "!#" (??). iDestruct 1 as (m') "(% & % & ?)".
        iExists m'. iFrame. iFrame "%". iPureIntro; set_solver. }
      rewrite big_sepS_union ?big_sepS_singleton; [|set_solver].
      iSplitL "Hm".
      { iExists m. iFrame. iSplit; [|done]. iPureIntro; set_solver. }
      iApply (big_sepS_impl with "Hms").
      iIntros "!#" (??). iDestruct 1 as (m') "(% & % & ?)".
      iExists m'. iFrame. iFrame "%". iPureIntro; set_solver. }
    iIntros (???) "(% & Hh & Ha & Hl & Hms)".
    iApply "HΦ". by iFrame.
  Qed.

End nodup_specs.
