From iris.algebra Require Import auth gmap excl.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import list_proof lock_proof.
From aneris.examples.ccddb.spec Require Import base time events resources.

(** Specifications for read and write operations.  *)

Section Specification.
  Context `{!anerisG Mdl Σ, !DB_params, !DB_time, !Maximals_Computing,
            !DB_events, !DB_resources Mdl Σ}.

  (** General specifications for read & write *)

  Definition read_spec
       (rd : val) (i: nat) (z : socket_address) : iProp Σ :=
    Eval simpl in
    □ (∀ (k : Key) (s : lhst),
        ⌜DB_addresses !! i = Some z⌝ -∗
          {{{ Seen i s }}}
          rd #k @[ip_of_address z]
          {{{ vo, RET vo;
              ∃ (s': lhst), ⌜s ⊆ s'⌝ ∗ Seen i s' ∗
                ((⌜vo = NONEV⌝ ∗ ⌜restrict_key k s' = ∅⌝) ∨
                 (∃ (v: val) (e : ae),
                     ⌜vo = SOMEV v⌝ ∗ ⌜AE_val e = v⌝ ∗
                     ⌜e ∈ Maximals (restrict_key k s')⌝ ∗
                     OwnMemSnapshot k {[erasure e]} ∗
                     ⌜e = Observe (restrict_key k s')⌝))
          }}})%I.

  Definition write_spec
      (wr : val) (i: nat) (z : socket_address)  : iProp Σ :=
    Eval simpl in
    □ (∀ (E : coPset) (k : Key) (v : SerializableVal) (s: lhst)
         (P : iProp Σ) (Q : ae → gmem → lhst → iProp Σ),
        ⌜DB_addresses !! i = Some z⌝ -∗
        ⌜↑DB_InvName ⊆ E⌝ -∗
        □ (∀ (s1: lhst) (e: ae),
            let s' := s1 ∪ {[ e ]} in
            ⌜s ⊆ s1⌝ → ⌜e ∉ s1⌝ →
            ⌜AE_key e = k⌝ → ⌜AE_val e = v⌝ →
            P ={⊤, E}=∗
            ∀ (h : gmem),
             let a  := erasure e in
             let h' := h ∪ {[ a ]} in
             ⌜a ∉ h⌝ →
             ⌜a ∈ Maximals h'⌝ →
             ⌜Maximum s' = Some e⌝ →
             Seen i s'  -∗
             k ↦ₛ h
             ={E∖↑DB_InvName}=∗ k ↦ₛ h' ∗ |={E, ⊤}=> Q e h s1) -∗
        {{{ ⌜k ∈ DB_keys⌝ ∗ P ∗ Seen i s }}}
          wr #k v @[ip_of_address z]
        {{{ RET #();
              ∃ (h: gmem) (s1: lhst) (e: ae), ⌜s ⊆ s1⌝ ∗ Q e h s1 }}})%I.

  Definition init_spec (init : val) : iProp Σ :=
    □ ∀ (i : nat) (z : socket_address)
        (v : val),
        ⌜is_list DB_addresses v⌝ →
        ⌜DB_addresses !! i = Some z⌝ →
        {{{  ([∗ list] i ↦ z ∈ DB_addresses, z ⤇ DB_socket_proto) ∗
             z ⤳ (∅, ∅) ∗
             unbound {[z]} ∗
            init_token i}}}
          init v #i @[ip_of_address z]
        {{{ rd wr, RET (rd, wr);
            Seen i ∅ ∗ read_spec rd i z ∗ write_spec wr i z}}}.

  Definition simplified_write_spec
      (wr : val) (i: nat) (z : socket_address)
      (k : Key) (v : SerializableVal) (h : gmem) (s : lhst) : iProp Σ :=
    (⌜DB_addresses !! i = Some z⌝ -∗
     ⌜k ∈ DB_keys⌝ -∗
     {{{ k ↦ᵤ h ∗ Seen i s }}}
       wr #k v @[ip_of_address z]
     {{{ RET #();
        ∃ (s1: lhst) (e: ae),
          ⌜s ⊆ s1⌝ ∗ ⌜e ∉ s1⌝ ∗ ⌜AE_key e = k⌝ ∗ ⌜AE_val e = v⌝ ∗
          ⌜erasure e ∉ h⌝ ∗ ⌜Maximum (s1 ∪ {[ e ]}) = Some e⌝ ∗
          ⌜erasure e ∈ Maximals (h ∪ {[ erasure e ]})⌝ ∗ Seen i (s1 ∪ {[ e ]}) ∗
          k ↦ᵤ (h ∪ {[ erasure e ]}) }}})%I.

  Lemma write_spec_implies_simplified_write_spec wr i z :
    write_spec wr i z ⊢ ∀ k v h s, simplified_write_spec wr i z k v h s.
  Proof.
    iIntros "#Hwr" (k v h s).
    iIntros (Hi Hk) "!#".
    iIntros (Φ) "[Hk Hseen] HΦ".
    set (P := k ↦ᵤ h).
    set (Q e1 h1 s1 :=
           (⌜h1 = h⌝ ∗ ⌜s ⊆ s1⌝ ∗ ⌜e1 ∉ s1⌝ ∗ ⌜AE_key e1 = k⌝ ∗
            ⌜AE_val e1 = v⌝ ∗ ⌜erasure e1 ∉ h1⌝ ∗ ⌜Maximum (s1 ∪ {[e1]}) = Some e1⌝ ∗
            ⌜erasure e1 ∈ Maximals (h1 ∪ {[erasure e1]})⌝ ∗
            Seen i (s1 ∪ {[e1]}) ∗ k ↦ᵤ (h1 ∪ {[erasure e1]}))%I).
    iSpecialize ("Hwr" $! ⊤ k v s P Q with "[] []"); [done|done|].
    iApply ("Hwr" with "[] [$Hk $Hseen]"); [|done|].
    - iModIntro.
      iIntros (s1 e Hs1 Hes1 Hek Hev) "Hkh".
      unfold P, Q.
      iModIntro.
      iIntros (h' Hh' He'h' Hmax) "Hseen Hsys".
      iDestruct (User_Sys_agree with "Hkh Hsys") as %<-.
      iMod (OwnMem_update _ _ (h ∪ {[erasure e]}) with "Hkh Hsys")
        as "[Hkh Hsys]"; first set_solver.
      iModIntro; eauto with iFrame.
    - iNext.
      unfold Q.
      iDestruct 1 as (h1 s1 e2 Hse) "(->&%&%&%&%&%&%&%&?&?)".
      iApply "HΦ"; iExists _, _; eauto with iFrame.
  Qed.

End Specification.

(** Modular specification for causal memory
    vector-clock based implementation. *)

Class DBG `{!DB_time, !DB_events} Σ := {
  DBG_Global_mem_excl :> inG Σ (authUR (gmapUR Key (exclR (gsetO we))));
  DBG_Global_mem_mono :> inG Σ (authUR (gmapUR Key (gsetUR we)));
  DBG_local_history_mono :> inG Σ (authUR (monotoneUR seen_relation));
  DBG_local_history_gset :> inG Σ (authUR (gsetUR ae));
  DBG_lockG :> lockG Σ;
}.

Definition DBΣ `{!DB_time, !DB_events} : gFunctors :=
  #[GFunctor (authUR (gmapUR Key (exclR (gsetO we))));
    GFunctor (authUR (gmapUR Key (gsetUR we)));
    GFunctor (authUR (monotoneUR seen_relation));
    GFunctor (authUR (gsetUR ae));
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
      ([∗ list] i ↦ _ ∈ DB_addresses, init_token i) ∗
      ([∗ set] k ∈ DB_keys, OwnMemUser k ∅) ∗
      init_spec init;
  }.

End Init.
