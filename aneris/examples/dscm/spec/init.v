From iris.algebra Require Import auth gmap excl excl_auth.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.dscm.spec Require Import base time events resources.

(** Specifications for read and write operations.  *)
Section Specification.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !Maximals_Computing,
            !DB_events, !DB_resources Mdl Σ}.

  (** General specifications for read & write *)
  Definition write_spec
      (wr : val) (sa : socket_address) : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key) (v : SerializableVal)
         (P : iProp Σ) (Q : we → ghst → ghst → ghst → iProp Σ),
        ⌜↑DB_InvName ⊆ E⌝ -∗
        ⌜k ∈ DB_keys⌝ -∗
        □ (P -∗
            |={⊤, E}=> ▷
              ∃ (h s: ghst) (a_old: option we),
                ⌜at_key k h = a_old⌝ ∗
                Obs h ∗
                k ↦ₖ mval_of_we_opt a_old ∗
                Writes sa s ∗
                (∀ (hf : ghst) (a_new : we),
                  ⌜at_key k hf = None⌝ ∗
                  ⌜WE_key a_new = k⌝ ∗
                  ⌜WE_val a_new = v⌝ ∗
                  ⌜WE_origin a_new = sa⌝ ∗
                  ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
                  k ↦ₖ Some (mval_of_we a_new) ∗
                  Obs (h ++ hf ++ [a_new]) ∗
                  Writes sa (s ++ [a_new]) ={E,⊤}=∗ Q a_new h hf s)) -∗
        {{{ P }}}
          wr #k v @[ip_of_address sa]
        {{{ RET #();
           ∃ (h hf s : ghst) (a: we), Q a h hf s }}})%I.

  Definition write_spec_atomic
      (wr : val) (sa : socket_address) : iProp Σ :=
    ∀ (k : Key) (v : SerializableVal),
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ (h s : ghst) (a_old : option we),
      ⌜at_key k h = a_old⌝ ∗
      Obs h ∗
      k ↦ₖ mval_of_we_opt a_old ∗
      Writes sa s >>>
      wr #k v @[ip_of_address sa] (↑DB_InvName)
    <<<▷ ∃∃ hf a_new, RET #();
           ⌜at_key k hf = None⌝ ∗
           ⌜WE_key a_new = k⌝ ∗
           ⌜WE_val a_new = v⌝ ∗
           ⌜WE_origin a_new = sa⌝ ∗
           ⌜∀ e, e ∈ h → e <ₜ a_new⌝ ∗
           k ↦ₖ Some (mval_of_we a_new) ∗
           Obs (h ++ hf ++ [a_new]) ∗
           Writes sa (s ++ [a_new]) >>>.

  Lemma write_spec_write_spec_atomic wr sa :
    write_spec wr sa -∗ write_spec_atomic wr sa.
  Proof.
    iIntros "#Hwr" (k v Hkeys Φ E HE) "!> Hvs".
    iApply ("Hwr" $! E k v _ (λ _ _ _ _, Φ #()) with "[] [] [] Hvs"); [ done .. | | ].
    { iIntros "!> Hvs".
      iMod "Hvs".
      do 2 iModIntro.
      iDestruct "Hvs" as (h s a_old) "[(%Hatkey & Hobs & Hk & writes) Hclose]".
      eauto 10 with iFrame. }
    iIntros "!> H".
    iDestruct "H" as (_ _ _ _) "H".
    iApply "H".
  Qed.

  Definition read_spec
      (rd : val) (sa : socket_address)  : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key)
         (P : iProp Σ)
         (Q1 : option we → ghst → ghst → iProp Σ)
         (Q2 : we → ghst → ghst → iProp Σ),
        ⌜↑DB_InvName ⊆ E⌝ -∗
        ⌜k ∈ DB_keys⌝ -∗
        □ (P -∗ |={⊤, E}=> ▷
           ∃ (h s : ghst) (q : Qp) (ao: option we),
               ⌜at_key k h = ao⌝ ∗
               Obs h ∗
               k ↦ₖ{q} mval_of_we_opt ao ∗
               ((⌜ao = None⌝ ∗ (k ↦ₖ{q} None) ={E,⊤}=∗ Q1 ao h s) ∧
                  (∀ a, ⌜ao = Some a⌝ ∗ (k ↦ₖ{q} Some (mval_of_we a)) ={E,⊤}=∗ Q2 a h s))) -∗
        {{{ P }}}
          rd #k @[ip_of_address sa]
          {{{ vo, RET vo;
            ∃ (h s : ghst) (eo: option we),
              (⌜vo = NONEV⌝ ∗ ⌜eo = None⌝ ∗ Q1 eo h s) ∨
              (∃ v e, ⌜vo = SOMEV v⌝ ∗ ⌜eo = Some e⌝ ∗ ⌜WE_val e = v⌝ ∗ Q2 e h s)
         }}})%I.

  Definition read_spec_atomic
      (rd : val) (sa : socket_address) : iProp Σ :=
    ∀ (k : Key),
    ⌜k ∈ DB_keys⌝ -∗
    <<< ∀∀ (h : ghst) (q : Qp) (ao : option we),
      ⌜at_key k h = ao⌝ ∗
      Obs h ∗
      k ↦ₖ{q} mval_of_we_opt ao >>>
      rd #k @[ip_of_address sa] (↑DB_InvName)
    <<<▷ RET match ao with None => NONEV | Some a => SOMEV (WE_val a) end;
           (⌜ao = None⌝ ∗ k ↦ₖ{q} None) ∨
           (∃ e, ⌜ao = Some e⌝ ∗
           (k ↦ₖ{q} Some (mval_of_we e))) >>>.

  Lemma read_spec_read_spec_atomic rd sa :
    read_spec rd sa -∗ read_spec_atomic rd sa.
  Proof.
    iIntros "#Hrd" (k Hkeys Φ E HE) "!> Hvs".
    iApply ("Hrd" $! E k _ (λ _ _ _, Φ NONEV)
                  (λ e _ _, Φ (SOMEV (WE_val e))) with "[] [] [] Hvs");
      [ done .. | | ].
    { iIntros "!> Hvs".
      iMod "Hvs"; do 2 iModIntro;
        iDestruct "Hvs" as (h q ao) "[(%Hatkey & Hobs & Hk) Hclose]".
      iExists h, [], q, ao.
      iSplit; [done|].
      iFrame.
      iSplit.
      - iIntros "[%Heq Hk]".
        iMod ("Hclose" with "[Hk]") as "Hclose".
        { iLeft. eauto with iFrame. }
        by rewrite Heq.
      - iIntros (a) "[%Ha Hk]".
        iMod ("Hclose" with "[Hk]") as "Hclose".
        { iRight. eauto with iFrame. }
        by rewrite Ha. }
    iIntros "!>" (vo) "H".
    iDestruct "H" as (_ _ eo) "[H|H]".
    - iDestruct "H" as (-> ->) "$".
    - iDestruct "H" as (v0 e -> -> ->) "$".
  Qed.

  (* TODO: state it correctly:
  Definition weak_read_spec
      (rd : val) (sa : socket_address)  : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key)
         (P : iProp Σ)
         (Q : we → ghst → ghst → iProp Σ)
         (h : ghst) (e : we) ,
        ⌜↑DB_InvName ⊆ E⌝ -∗
        ⌜k ∈ DB_keys⌝ -∗
        □ (P ={⊤, E}=∗
            .... ) -∗
        {{{ P ∗ Obs h ∗ ⌜at_key k h = Some we⌝}}}
          rd #k @[ip_of_address sa]
          {{{ vo, RET vo;
            ...
         }}})%I.  *)


  Definition init_spec (init : val) : iProp Σ :=
    □ ∀ (sa : socket_address) (srvl : val),
        ⌜is_list DB_addresses srvl⌝ →
        ⌜sa ∉ DB_addresses⌝ →
        {{{ unallocated {[sa]} ∗
             ([∗ list] i ↦ z ∈ DB_addresses, z ⤇ DB_socket_proto) ∗
             sa ⤳ (∅, ∅) ∗
             free_ports (ip_of_address sa) {[port_of_address sa]} }}}
          init #sa srvl @[ip_of_address sa]
        {{{ rd wr, RET (rd, wr);
            Obs [] ∗
            Writes sa [] ∗
            read_spec rd sa ∗ write_spec wr sa}}}.

  Definition simplified_write_spec
      (wr : val) (sa : socket_address)
      (k : Key) (v : SerializableVal) (h : ghst) (s : ghst) : iProp Σ :=
    ⌜k ∈ DB_keys⌝ -∗
     {{{ Obs h ∗
         k ↦ₖ mval_of_we_opt (at_key k h) ∗
         Writes sa s
     }}}
       wr #k v @[ip_of_address sa]
     {{{ RET #();
        ∃ (hf : ghst) (a: we),
          ⌜WE_key a = k⌝ ∗
          ⌜WE_val a = v⌝ ∗
          ⌜WE_origin a = sa⌝ ∗
          ⌜at_key k hf = None⌝ ∗
          Obs (h ++ hf ++ [a]) ∗
          k ↦ₖ Some (mval_of_we a) ∗
          Writes sa (s ++ [a])
     }}}%I.

  Definition simplified_read_spec
             (rd : val) (sa : socket_address) (k : Key) (q : Qp)
             (w : option mval) : iProp Σ :=
      ⌜k ∈ DB_keys⌝ -∗
    {{{ k ↦ₖ{q} w }}}
      rd #k @[ip_of_address sa]
      {{{vo, RET vo;
         k ↦ₖ{q} w ∗
         (⌜vo = NONEV⌝ ∗ ⌜w = None⌝) ∨
         (∃ a, ⌜vo = SOMEV (WE_val a)⌝ ∗ ⌜w = Some (mval_of_we a)⌝)
      }}}%I.

  Lemma get_simplified_write_spec wr sa :
    write_spec wr sa ⊢ ∀ k v h s, simplified_write_spec wr sa k v h s.
  Proof.
    iIntros "#Hwr" (k v h s).
    iIntros (Hk) "!#".
    iIntros (Φ) "(#Hobs & Hk & Hw) HΦ".
    set (a_old := mval_of_we_opt (at_key k h)).
    set (P := (k ↦ₖ a_old ∗ Writes sa s)%I).
    set (Q a h1 hf s1 :=
           (  ⌜h1 = h⌝ ∗
              ⌜s1 = s⌝ ∗
              ⌜WE_key a = k⌝ ∗
              ⌜WE_val a = v⌝ ∗
              ⌜WE_origin a = sa⌝ ∗
              ⌜at_key k hf = None⌝ ∗
              Obs (h ++ hf ++ [a]) ∗
              k ↦ₖ Some (mval_of_we a) ∗
              Writes sa (s ++ [a]))%I).
    iSpecialize ("Hwr" $! ⊤ k v P Q with "[] []"); [done|done |].
    iApply ("Hwr" with "[] [$Hk Hobs $Hw]").
    - iModIntro.
      iIntros "(Hk & Hw)".
      unfold P, Q.
      iModIntro.
      iExists h, s, (at_key k h). iFrame. iFrame "#".
      iNext.
      iSplit; first done.
      iIntros (hf a_new) "(% & % & % & % & % & Hk & #Hobs' & Hw)".
      iFrame. iFrame "#". eauto.
    - iNext.
      unfold Q.
      iDestruct 1 as (h1 hf s1) "(%&%&%&%&%&%&%& #Hb & Hk & Hw)".
      iApply "HΦ". iExists hf, a.
      do 4 (iSplit; [iPureIntro; eauto |]).
      iFrame. iFrame "#".
  Qed.

End Specification.

(** Modular specification for distributed sequentially consistent memory. *)

Class DBG `{!DB_time, !DB_events} Σ :=
  {
    DBG_Global_mem_excl :>
      inG Σ (authUR (gmapUR Key (prodR fracR (agreeR (optionO (leibnizO we))))));
    DBG_Global_history_mono :> inG Σ (authUR (monotoneUR (@prefix (leibnizO we))));
    (* Not sure about that one: maybe rather a map from saddr to that type *)
    DBG_Local_writes_excl :> inG Σ (excl_authR (leibnizO (list we)));
    DBG_lockG :> lockG Σ;
}.

Definition DBΣ `{!DB_time, !DB_events} : gFunctors :=
  #[GFunctor (authUR (gmapUR Key (prodR fracR (agreeR (optionO (leibnizO we))))));
    GFunctor (authUR (monotoneUR (@prefix (leibnizO we))));
    GFunctor (excl_authR (leibnizO (list we)));
    lockΣ].

Instance subG_DBΣ `{!DB_time, !DB_events} {Σ} : subG DBΣ Σ → DBG Σ.
Proof. econstructor; solve_inG. Qed.

Class DB_init_function := { init : val }.

Section Init.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !Maximals_Computing,
            !DB_events, !DBG Σ, !DB_init_function}.

  Class DB_init := {
    DB_init_time :> DB_time;
    DB_init_events :> DB_events;
    DB_init_setup E :
        True ⊢ |={E}=> ∃ (DBRS : DB_resources Mdl Σ),
      GlobalInv ∗
      ([∗ set] k ∈ DB_keys, k ↦ₖ None) ∗
      init_spec init;
  }.

End Init.
