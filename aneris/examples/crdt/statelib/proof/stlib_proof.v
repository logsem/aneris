From stdpp Require Import gmap.

From iris.base_logic Require Import invariants bi.
From iris.algebra Require Import agree auth excl gmap.

From aneris.algebra Require Import monotone.
From aneris.aneris_lang
  Require Import lang network tactics proofmode lifting resources.
From aneris.aneris_lang.lib
  Require Import list_proof lock_proof vector_clock_proof serialization_proof
    map_proof lock_proof network_util_proof inject.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.prelude Require Import misc time.

From aneris.examples.crdt.spec
  Require Import crdt_events crdt_resources crdt_denot crdt_time crdt_base.
From aneris.examples.crdt.statelib.resources
  Require Import resources_update resources utils resources_utils
    resources_inv resources_local resources_global resources_lock.

From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.user_model
  Require Import params model semi_join_lattices.
From aneris.examples.crdt.statelib.time Require Import time maximality.
From aneris.examples.crdt.statelib.STS
  Require Import utils gst lst mutation merge.
From aneris.examples.crdt.statelib.proof
  Require Import spec events utils
    stlib_proof_utils internal_specs.

Instance timeinst : Log_Time := timestamp_time.



(** Nomenclature:
  * In this file (in every section) there are physical and logical operations
  * and states. I will try to use the following names to help reading the proofs
  * and specifications.
  *
  *  → Operations:
  *    ↪ in AnerisLang      (type: val)  : op_v
  *    ↪ logical operations (type LogOp) : op_log
  *
  *  → States:
  *    ↪ serialized         (type: val)  : st_serialized
  *    ↪ in AnerisLang      (type: val)  : st_v
  *    ↪ logical operations (type LogSt) : st_log
  *    ↪ local states, STS  (type Lst) : lst
  *    ↪ global states, STS (type Gst) : lst
  *
  * Note on coherence:
  *
  * There are coherence predicates over these different versions of operations
  * and states:
  *
  * → Operations:
  *    ↪ LogOp → val : StLib_Op_Coh
  *
  * → States:
  *    ↪ val   ↔ serialized : StLib_StSerialization
  *    ↪ LogSt → val        : StLib_St_Coh
  *    ↪ Lst   → LogSt      : denotation
  *
  *)



Section StateLib_Proof.

  Context `{LogOp: Type, LogSt : Type,
            !anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt,
            !Internal_StLibG LogOp Σ, !StLib_GhostNames}.

  Notation princ_ev := (@principal (gset (Event LogOp)) cc_subseteq).

  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Specification for [get_state] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+       **)


  Lemma internal_get_state_spec_holds (i : nat) (saddr : socket_address)
      (lockv : val) (st_loc : loc) (γ__lock : gname) :
    {{{ StLib_GlobalInv ∗
        lock_inv saddr γ__lock lockv i st_loc }}}
      get_state lockv #st_loc @[ip_of_address saddr]
    {{{ (getst__fun : val), RET getst__fun; internal_get_state_spec getst__fun i saddr }}}.
  Proof.
    iIntros (φ) "[#Hinv #Hislock] Hφ".
    wp_lam. wp_pures. iApply "Hφ"; clear φ.

    iIntros (Haddr φ) "!> Hpre".
    wp_pures.
    wp_apply (acquire_spec with "Hislock").
    iIntros (v) "(-> & Hlocked &
      (%ip & %phys_st & %log_st & %st_h__local & %st_h__foreign & %Hip &
        Hloc & %Hcoh & (%f & %Hf & %Hislocal & %isforeign & Hst_h__local & Hst_h__foreign) & %Hcoh'))".
    rewrite Haddr in Hip.
    simplify_eq/=.
    wp_seq. wp_load.

    wp_bind (Lam _ _).
    wp_apply (aneris_wp_atomic _ _ (↑CRDT_InvName)).
    iMod "Hpre" as (s1 st_h__sub) "[(%f' & %Hf' & %Hlocal & %Hsub & Hown_local & Hown_sub & #Hlocal_snap) Hclose]".
    assert (f = f') as <-; first by apply fin_to_nat_inj.
    iDestruct (both_agree_agree with "Hst_h__local Hown_local")
      as "(Hst_h__local & Hown_local & <-)".

    iDestruct (LocState_LockInv__sub_in_foreign
      with "[] Hinv [Hown_local Hown_sub][Hst_h__foreign Hst_h__local]")
      as "> (
        (%f' & %Hf_' & Hislocal & Hisfor & Hst_h__local & Hst_h__sub & #Hsnap) &
        (%f'' & %Hf_'' & _ & _ & Hown_local & Hst_h__foreign) & %Hsub_in_for)";
      [ done
      | iExists f; by iFrame "Hown_local Hown_sub #"
      | iExists f; by iFrame "Hst_h__foreign Hst_h__local" |].
    assert(f' = f) as ->.
    { apply fin_to_nat_inj. by rewrite Hf_'. }
    assert(f'' = f) as ->.
    { apply fin_to_nat_inj. by rewrite Hf_''. }

    (** Update of the resources. *)
    iModIntro.
    iDestruct ((get_state_update _ f st_h__local st_h__foreign st_h__sub)
      with "[] Hinv [Hst_h__local Hst_h__sub] [Hst_h__foreign Hown_local]")
      as "> [Hown__local Hown_lockinv]"; first trivial.
    { iExists f. iFrame. by iFrame "#". }
    { iExists f. by iFrame. }
    wp_pures.

    iMod ("Hclose" with "[Hown__local]") as "Hφ"; last iModIntro.
    { iFrame. by iFrame "%". }

    wp_pures.
    wp_apply (release_spec with "[$Hislock $Hlocked Hown_lockinv Hloc]").
    { iExists (ip_of_address saddr), phys_st, log_st, st_h__local, st_h__foreign.
      rewrite Haddr.
      iFrame "%". iFrame.
      iSplit; first done.
      iDestruct "Hown_lockinv" as "(%h & %H2 & %H3 & %H4 & j)".
      iExists h. by iFrame. }

    iIntros (v) "->". wp_pures.
    iApply "Hφ".
  Qed.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [update] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~+                     **)
  Lemma internal_update_spec_holds (repId : nat) (addr : socket_address)
      (lockv mutator__fun : val) (st_loc : loc) (γ__lock : gname) :
    {{{ StLib_GlobalInv ∗
        lock_inv addr γ__lock lockv repId st_loc ∗
        mutator_spec mutator__fun
    }}}
      update lockv mutator__fun #repId #st_loc @[ip_of_address addr]
    {{{ (update__fun : val), RET update__fun; internal_update_spec update__fun repId addr }}}.
  Proof.
    iIntros (φ) "(#Hinv & #Hlockinv & #mutatorspec) Hφ".
    wp_lam. wp_pures.
    iApply "Hφ". clear φ.
    iIntros (op_v log_op Haddr_proj Hop_coh).
    iModIntro. iIntros (φ) "Hpre".
    wp_pures.
    wp_apply (acquire_spec with "Hlockinv").
    iIntros (v) "(-> & Hlocked & HPlock)".
    wp_pures.
    iDestruct "HPlock"
      as (ip phys_st log_st h__local h__for Hip)
        "(Hloc & %Hcoh & Hown__lockinv & %Hcoh')".
    wp_bind (!_)%E.
    wp_apply (aneris_wp_atomic _ _ (↑CRDT_InvName)).
    iMod "Hpre" as (h_g h__local' h__sub)
      "[[Hown__global Hown__local] Hclose]".


    iDestruct (StLib_OwnLocalState__get_fRepId with "Hown__local")
      as "(%f & %Hf & Hown__local)".


    iDestruct (Lock_Local__same_local with "Hown__lockinv Hown__local")
      as "(Hown__lockinv & Hown__local & ->)".


    iDestruct ((LocState_LockInv__sub_in_foreign _ f h__local h__for h__sub)
      with "[] Hinv [Hown__local] [Hown__lockinv]")
      as ">(Hown__local & Hown__lockinv & %Htmp)";
      [trivial | by rewrite -Hf | by rewrite -Hf |].
    iDestruct ((LocState_LockInv__localisvalid _ f h__local h__for h__sub)
      with "[] Hinv [Hown__local] [Hown__lockinv]")
      as ">(Hown__local & Hown__lockinv & %Htmp')";
      [trivial | by rewrite -Hf | by rewrite -Hf |].


    rewrite -Hf.
    iDestruct ((update_update _ _ log_op) with "[]Hinv Hown__local Hown__lockinv Hown__global")
      as ">(Hown__local & Hown__lockinv & Hown__global & %fev_g_fresh & %fev_fresh & %fev_maximals & %fev_max & %Hloc_valid)";
      first trivial; last iModIntro.
    wp_apply (aneris_wp_load with "[Hloc]").
    { iNext. rewrite Haddr_proj in Hip. by simplify_eq/=. }
    wp_pures.

    set fev := fresh_event (h__local ∪ h__for) log_op f.

    iIntros "Hloc'".
    iMod ("Hclose" $! fev (h_g ∪ {[fev]}) (h__local ∪ {[fev]}) h__for with "[Hown__global Hown__local]") as "Hpost"; last iModIntro.
    { iFrame. iFrame "%".
      iPureIntro.
      repeat split; try done.
      by intros Hin%(elem_of_union_l _ _ h__for). }

    wp_bind (mutator__fun _ _ _).
    rewrite Hf.
    iDestruct ("mutatorspec" $! addr repId phys_st op_v (h__local ∪ h__for) fev log_op log_st) as "mutatorspec'".
    wp_apply ("mutatorspec'" with "[]").
    { repeat iSplit; try done; iPureIntro.
      3, 4: by destruct Hloc_valid.
      - by apply elem_of_union_r, elem_of_singleton.
      - apply Maximum_correct in fev_max as [_ B].
        + intros e [He_in | ->%elem_of_singleton]%elem_of_union;
            last by apply TM_lt_irreflexive.
          assert (e ≠ fev).
          { intros Heq. rewrite Heq in He_in. by apply fev_fresh. }
          assert (e <_t fev);
            first ( apply B; [ set_solver | assumption] ).
          intros?.
          by apply TM_lt_exclusion with (time e) (time fev).
        + replace (h__local ∪ {[fresh_event (h__local ∪ h__for) log_op f]} ∪ h__for)
            with (h__local ∪ h__for ∪ {[fresh_event (h__local ∪ h__for) log_op f]});
            last set_solver.
          by apply (VLst_ext_time _ Hloc_valid). }

    iIntros (st') "(%log_st' & %Hst'_coh & %Hst'_mut)".
    wp_bind(_ <- _)%E.
    wp_store. wp_seq.

    wp_apply (release_spec with "[$Hlockinv $Hlocked Hloc' Hown__lockinv ]").
    { iExists ip, st', log_st', (h__local ∪ {[ fev ]}), h__for.
      iFrame "%".
      iSplitL "Hloc'".
      { rewrite Haddr_proj in Hip; simplify_eq/=. iFrame. }
      iSplitL; last first.
      { iPureIntro.
        replace (h__local ∪ {[fev]} ∪ h__for)
          with (h__local ∪ h__for ∪ {[fev]});
          last set_solver.
        apply st_crdtM_mut_coh with log_st; try done.
        - by apply Lst_Validity_implies_event_set_valid.
        - replace (h__local ∪ h__for ∪ {[fev]})
            with (h__local ∪ {[fev]} ∪ h__for); last set_solver.
          apply Maximum_correct in fev_max as [??]; first done.
          replace (h__local ∪ {[fresh_event (h__local ∪ h__for) log_op f]} ∪ h__for)
            with (h__local ∪ h__for ∪ {[fresh_event (h__local ∪ h__for) log_op f]}); last set_solver.
          by destruct Hloc_valid. }
      iFrame. }
    iIntros (v ->).
    iApply "Hpost".
  Qed.


  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [sendToAll] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+                  **)
  Lemma internal_sendToAll_spec_holds
    (h: socket_handle) (sock: socket) (repId: RepId) (sock_addr: socket_address)
    (dstlist: val) :
    ⌜repId < length CRDT_Addresses⌝ -∗
    ⌜is_list CRDT_Addresses dstlist⌝ -∗
    {{{ socket_inv repId h sock_addr sock }}}
    sendToAll #(LitSocket h) dstlist #repId @[ip_of_address sock_addr]
    {{{ v, RET v; internal_sendToAll_spec v h sock repId sock_addr dstlist }}}.
  Proof.
    Ltac myload Hname velim :=
      (wp_bind(!_)%E;
      iInv "Hl" as ">(%v' & Hownv & Hloc)" "Hclose";
      wp_load;
      iCombine "Hγi" "Hownv" as "H";
      iDestruct (own_valid_l with "H") as (Hname) "(Hγi & Hownv)";
      apply pair_valid in Hname as [_ <-%to_agree_op_inv_L];
      rewrite agree_idemp;
      iMod ( "Hclose"  with "[Hloc Hownv]") as "_";
      [ iNext; iExists velim; iFrame "Hownv Hloc" | iModIntro]).

    iIntros (Hi Hislist) "!> %φ #HSocketInv Hφ".
    rewrite/sendToAll.
    do 5 wp_pure _.
    wp_pures. iApply "Hφ"; clear φ.
    iIntros "!> %m #Hprotos !> %φ _ Hφ".
    wp_pure _.
    wp_alloc l as "Hl". wp_let.
    iMod(own_alloc (1%Qp, to_agree O%nat)) as (γi) "[Hγi Hi]"; first done.
    iMod (inv_alloc socket_inv_ns _
      (∃ (v: nat),
        own γi ((1/2)%Qp, to_agree v) ∗ l ↦[ip_of_address sock_addr] #v)%I
        with "[Hi Hl]") as "#Hl".
    { iNext. iExists O. iFrame "Hi Hl". }
    iAssert (∃ (v: nat), own γi ((1/2)%Qp, to_agree v))%I with "[Hγi]" as "j";
      first by iExists O.
    do 3 wp_pure _. iLöb as "IH".
    iDestruct "j" as "[%vinit Hγi]".
    wp_pures.
    (** Check whether index is valid *)
    wp_apply (wp_list_length $! Hislist ).
    iIntros (v) "->".
    myload Hvalid vinit.
    wp_pures.
    destruct (decide (vinit < length CRDT_Addresses)%nat);
      [rewrite bool_decide_eq_true_2 | rewrite bool_decide_eq_false_2];
      try lia.
    - wp_if_true.
      myload Hvalid vinit. wp_pures.
      destruct (decide (repId = vinit));
        [rewrite bool_decide_eq_true_2 | rewrite bool_decide_eq_false_2];
        try lia.
      + wp_if_true.
        myload Hvalid vinit. wp_op.
        wp_bind (_ <- _)%E.
        iInv "Hl" as "(%v & Hownv & Hloc)" "Hclose".
        wp_store.
        assert (vinit + 1 = S vinit) as ->; first lia.
        iMod (own_update_2 γi _ _ (1%Qp, to_agree (S vinit)%nat) with "Hownv Hγi")
          as "[Hγi Hownv]".
        { rewrite -pair_op frac_op Qp_half_half.
          by apply cmra_update_exclusive. }
        iMod ("Hclose" with "[Hloc Hγi]") as "_"; last iModIntro.
        { iNext. iExists (S vinit). iFrame. }
        wp_seq.
        iApply ("IH" with "Hφ"). by iExists (S vinit).
      + wp_if_false.
        myload Hvalis vinit.
        wp_apply (wp_list_nth_some _ vinit CRDT_Addresses dstlist).
        { iPureIntro. split; [ assumption | lia ]. }
        iIntros (elt) "(%r & -> & %Hsome)". apply nth_error_lookup in Hsome.
        wp_apply wp_unSOME; first by iPureIntro.
        iIntros "_".
        wp_pures.
        wp_bind (SendTo _ _ _)%E.
        iInv "HSocketInv"
          as "(%Roup & %Soup &
            >(Hh & %Hsaddr_eq & %Hsaddr_proj & Hsoup & #Hproto_respected))"
            "Hclose".

        wp_apply (aneris_wp_send _ socket_proto with "[$Hh $Hsoup ]");
          try done.
        { iDestruct (big_sepL_lookup with "Hprotos") as "[a b]"; first exact Hsome.
          by iSplit. }
        iIntros "[Hh Hsoup]".
        iMod ("Hclose" with "[$Hh Hsoup]") as "_"; last iModIntro.
        {  iExists _, _. iFrame "Hsoup". by iFrame "#". }
        wp_pures.
        myload Hvalid vinit. wp_op. wp_bind (_ <-  _)%E.
        iInv "Hl" as "(%v & Hownv & Hloc)" "Hclose".
        wp_store.
        assert (vinit + 1 = S vinit) as ->; first lia.
        iMod (own_update_2 γi _ _ (1%Qp, to_agree (S vinit)%nat) with "Hownv Hγi")
          as "[Hγi Hownv]".
        { rewrite -pair_op frac_op Qp_half_half.
          by apply cmra_update_exclusive. }
        iMod ("Hclose" with "[Hloc Hγi]") as "_"; last iModIntro.
        { iNext. iExists (S vinit). iFrame. }
        wp_seq.
        iApply ("IH" with "Hφ"). by iExists (S vinit).
    - wp_if_false.
      by iApply "Hφ".
  Qed.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [broadcast] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+                  **)
  Lemma internal_broadcast_spec_holds
    (repId : nat) s h (addr : socket_address) (lockv addr_list : val) (st_loc : loc) (γ__lock : gname):
    ⌜is_list CRDT_Addresses addr_list⌝ -∗
    ⌜repId < length CRDT_Addresses⌝%nat -∗
    ⌜ CRDT_Addresses !! repId = Some addr⌝ -∗
    ⌜ saddress s = Some addr ⌝ -∗
    ⌜ sblock s = true ⌝ -∗
    ([∗ list] k ↦ r ∈ CRDT_Addresses, r ⤇ socket_proto) -∗
    {{{ socket_inv repId h addr s ∗
        (* internal_sendToAll_spec sendToAll h s repId addr addr_list ∗ *)
        StLib_GlobalInv ∗
        lock_inv addr γ__lock lockv repId st_loc }}}
        broadcast StLib_StSerialization.(s_serializer).(s_ser) lockv #(LitSocket h) #st_loc addr_list #repId  @[ip_of_address addr]
    {{{ (v: val), RET v; False  }}}.
  Proof.
    iIntros (Hislist HrepIdlen Haddr Hsock_addr Hsock_block)
      "#Hprotos !> %φ (#Hsocket_inv & #Hinv & #Hlock_inv) Hφ".
    wp_lam. do 4 wp_let.
    wp_smart_apply (wp_loop_forever _ True);
      [ clear φ; iSplit; last done | by iIntros (?) ].
    iIntros "!> %φ _ Hφ". wp_pures.
    wp_apply (acquire_spec with "Hlock_inv").
    iIntros (v) "(-> & Hlocked &
      (%ip & %st_v & %st_log & %st_h__local & %st_h__foreign &
        %Hip & Hloc & %Hst_coh &
        (%f & %Hf & %Hisloc & %Hisfor & Hown_loc & Hown_for) & %Hdenot))".
    wp_seq.
    wp_bind (!_)%E.
    iDestruct ((broadcast_update _ f st_h__local st_h__foreign)
      with "[]Hinv[Hown_loc Hown_for]")
      as ">(Hown__lockinv & #Hsnap & %Hloc_valid)";
      first trivial.
    { iExists f. rewrite Hf. by iFrame. }

    wp_apply (aneris_wp_load with "[Hloc]").
    { rewrite Haddr in Hip. by simplify_eq/=. }
    iIntros "Hloc". wp_pures.
    wp_apply (release_spec with "[$Hlock_inv $Hlocked Hown__lockinv Hloc]").
    { iExists ip, st_v, st_log, st_h__local, st_h__foreign.
      rewrite -Hf. iFrame. iFrame "%".
      rewrite Haddr in Hip. simplify_eq/=. iFrame.
      iPureIntro. by rewrite Haddr. }
    iIntros (v ->). wp_seq.
    wp_apply (s_ser_spec);
      first by pose (StLib_StCoh_Ser st_log st_v Hst_coh).
    iIntros (msg Hmsg_ser). wp_let.
    wp_apply internal_sendToAll_spec_holds; [iPureIntro; lia | done | done | ].
    iIntros (v) "Hspec_send2all'".
    wp_apply "Hspec_send2all'"; [ | done | done].
    rewrite big_sepL_sep. iSplit.
    - rewrite -big_sepL_later. iNext. iAssumption.
    - rewrite -big_sepL_later. iNext.
      iApply big_sepL_intro.
      iIntros "!> %replica %address %Haddress_proj".
      iExists st_v, st_log, st_h__local, st_h__foreign.
      repeat (iSplit; first done).
      iSimplifyEq.
      pose (lookup_lt_Some CRDT_Addresses replica address Haddress_proj) as Hlen.
      iExists f, replica, f, (nat_to_fin Hlen).
      iFrame "%".
      iSplit; first done.
      iSplit; last iFrame "Hsnap".
      iPureIntro.
      apply fin_to_nat_to_fin.
  Qed.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [apply_thread] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+               **)
  Lemma apply_thread_spec_aux
    {h s γlock lockp stp merge_fun st'_h__local st'_h__sub st'_val φ m R}
    {repId: RepId}
    {f_sender: fRepId}
    {st'_log: LogSt}
    {Hst'_validity : Lst_Validity (st'_h__local ∪ st'_h__sub)}
    {Hst'_coh : StLib_St_Coh st'_log st'_val}
    {Hst'_ser : s_is_ser StLib_StSerialization st'_val (m_body m)}
    {Haddr_proj : CRDT_Addresses !! repId = Some (m_destination m)}
    {st'_denot : ⟦ st'_h__local ∪ st'_h__sub ⟧ ⇝ st'_log}:
    (m_destination m) ⤇ socket_proto -∗
    socket_inv repId h (m_destination m) s -∗
    StLib_GlobalInv -∗
    lock_inv (m_destination m) γlock lockp repId stp -∗
    merge_spec merge_fun -∗
    ([∗ set] m0 ∈ R, socket_proto m0) -∗
    own (γ_loc_cc' !!! f_sender)
                    (◯ princ_ev (st'_h__local ∪ st'_h__sub)) -∗
    (True -∗ φ #()) -∗

    WP let: "st'" := s_deser (s_serializer StLib_StSerialization) #(m_body m) in
       acquire lockp ;; #stp <- merge_fun ! #stp "st'" ;; release lockp @[
    ip_of_address (m_destination m)] {{ v, φ v }}.
  Proof.
    iIntros "#Hproto #Hsock_inv #Hinv #His_lock #Hmerge #Hproto_respected #Hst'_snap Hφ".
    wp_apply (s_deser_spec ); [ iFrame "%" | iIntros (_) ].
    wp_let.
    wp_apply (acquire_spec with "His_lock").
    iIntros (v) "(-> & Hlocked &
      (%ip & %phys_st & %log_st & %st_h__local & %h__foreign &
      %Hip & Hloc & %Hcoh & (%f & %Hf & %Hf_loc & %Hf_for & hf_own_loc & Hf_own_for) & %Hst_coh))".
    assert (repId = f) as ->.
    { rewrite Hf.
      apply (NoDup_lookup CRDT_Addresses repId repId (m_destination m));
        [ by apply CRDT_Addresses_NoDup
        | assumption
        | assumption ]. }

    assert (Hip_eq: ip_of_address (m_destination m) = ip).
    { rewrite Haddr_proj in Hip. by simplify_eq/=. }
    wp_seq.
    wp_bind (!_)%E.
    iMod (lock_globinv__lst_validity with "[] Hinv hf_own_loc Hf_own_for" )
      as "(%Hv & hf_own_loc & Hf_own_for)"; first trivial.
    wp_apply (aneris_wp_load with "[Hloc]").
    { rewrite Haddr_proj in Hip. by simplify_eq/=. }
    iIntros "Hloc".
    wp_bind (merge_fun _ _)%E.
    wp_apply ("Hmerge" $! (m_destination m)
      phys_st st'_val (st_h__local ∪ h__foreign) (st'_h__local ∪ st'_h__sub)
      log_st st'_log).
    { pose (Lst_Validity_implies_events_ext _ Hv).
      pose (Lst_Validity_implies_same_orig_comparable _ Hv).
      pose (Lst_Validity_implies_events_ext _ Hst'_validity).
      pose (Lst_Validity_implies_same_orig_comparable _ Hst'_validity).
      iFrame "%". }
    iIntros (st'' (st''_log & Hst''_coh & Hst''_islub)).
    wp_bind (_ <- _)%E.

    iDestruct (locals_incl_global with "Hinv Hst'_snap hf_own_loc Hf_own_for")
      as "> (hf_own_loc & Hf_own_for & (%g & %Hg))";
      first trivial.
    destruct Hg as (Hcc2 & Hcc1 & Hval).
    pose proof (VLst_ext_time _ Hval) as Hext_t.
    pose proof (VLst_same_orig_comp _ Hval) as Hsoc.
    pose proof (foreign_local_filtered_inclusion st_h__local h__foreign st'_h__local st'_h__sub g Hcc2 Hcc1 Hval Hv Hst'_validity) as Heq.

    wp_store.
    (** Update of the resources: using the [merge_update] lemma. *)
    iDestruct ((merge_update ⊤ f f_sender
      st_h__local h__foreign st'_h__local st'_h__sub)
      with "[]Hinv[hf_own_loc Hf_own_for]Hst'_snap[]")
      as "> (%f' & %Hf' & _ & _ & Hst_own__local & Hst_own__sub)";
      [ trivial | iExists f; iFrame; iSplit; first trivial; iFrame "%" | done | ].
    assert (f' = f) as ->. { apply fin_to_nat_inj. by rewrite Hf'. }

    iDestruct (Lock_RemoteLockSnap__incl
      with "[]Hinv[Hst_own__local Hst_own__sub]Hst'_snap")
      as ">[(%f_ & %Hf_ & _ & _ & Hst_own__local & Hst_own__sub) %Hincl]";
      first trivial.
    { iExists f. iFrame. iFrame "%".
      iPureIntro.
      by intros x [Hx_in%Hf_for | [Hx_orig Hx_in]%elem_of_filter]%elem_of_union. }
    assert(f_ = f) as ->. { apply fin_to_nat_inj. by rewrite Hf_. }


    wp_seq.
    wp_apply (release_spec with "[$His_lock $Hlocked Hloc Hst_own__local Hst_own__sub]").
    { iExists ip, st'', st''_log,
        st_h__local,
        (h__foreign
                ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
                    (st'_h__local ∪ st'_h__sub)).
      rewrite Hip_eq. iFrame "Hloc". iFrame "%".
      iSplit.
      - iExists f.
        iSplit; first done.
        iSplit.
        { iPureIntro.
          by intros e [?%Hf_for | [? _]%elem_of_filter]%elem_of_union. }
        iFrame "Hst_own__local Hst_own__sub".
      - iPureIntro.
        epose (st_crdtM_lub_coh (st_h__local ∪ h__foreign) (st'_h__local ∪ st'_h__sub) log_st st'_log st''_log Hst_coh st'_denot _ _ Heq Hst''_islub).
        assert(st_h__local ∪ h__foreign ∪ (st'_h__local ∪ st'_h__sub) =
          st_h__local
            ∪ (h__foreign
             ∪ filter (λ e, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__sub)))
          as <-;
          last done.
        assert (st_h__local ∪ h__foreign ∪ (st'_h__local ∪ st'_h__sub)
          = (st_h__local ∪ (st'_h__local ∪ st'_h__sub)) ∪ h__foreign) as ->;
          first set_solver.
        assert (
          st_h__local
          ∪ (h__foreign
          ∪ filter (λ e, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__sub))
          =
          (st_h__local
          ∪ filter (λ e, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__sub))
          ∪ h__foreign)
          as ->;
          first set_solver.
        assert (st_h__local ∪ (st'_h__local ∪ st'_h__sub)
          = st_h__local
            ∪ filter (λ e, EV_Orig e ≠ f)(st'_h__local ∪ st'_h__sub))
          as ->; last reflexivity.
        apply set_eq. intros x. split; last set_solver.
        intros [Hx_in | Hx_in]%elem_of_union;
          first by apply  elem_of_union_l.
        destruct (decide (EV_Orig x = f));
          [ by apply elem_of_union_l, Hincl, elem_of_filter
          | by apply elem_of_union_r, elem_of_filter]. }
    iIntros (v ->).
    by iApply "Hφ".

    Unshelve.
    all: by apply Lst_Validity_implies_event_set_valid.
  Qed.

  Lemma apply_thread_spec
    (h: socket_handle) (addr: socket_address) (s: socket)
    (repId: RepId) (γlock: gname)
    (lockp : val) (stp: loc) (merge_fun: val) :
    ⌜ CRDT_Addresses !! repId = Some addr⌝ -∗
    ⌜ saddress s = Some addr ⌝ -∗
    ⌜ sblock s = true ⌝ -∗
    addr ⤇ socket_proto -∗
    socket_inv repId h addr s -∗
    {{{
      StLib_GlobalInv ∗
      lock_inv addr γlock lockp repId stp ∗
      merge_spec merge_fun
    }}}
      (apply_thread (s_deser (s_serializer StLib_StSerialization))) lockp #(LitSocket h) #stp merge_fun @[ip_of_address addr]
    {{{
      RET #(); False (* infinite loop: doesn't terminate *)
    }}}.
  Proof.
    iIntros (Haddr Hsaddr Hsblock)
      "#Hproto #Hsock_inv %φ !> (#Hinv & #His_lock & #Hmerge) Hφ".
    wp_lam. wp_pures.
    wp_apply (wp_loop_forever _ True);
      last iAssumption.
    clear φ.
    iSplitL; last done.
    iIntros "!> %φ _ Hφ".
    wp_lam.
    wp_bind(ReceiveFrom _).
    iInv "Hsock_inv" as "(%R & %S & Hh & > (%Haddr_sock & %Haddr_proj & Hsoup & #Hproto_respected))" "Hclose".
    wp_apply ((aneris_wp_receivefrom
      (ip_of_address addr) addr _ h s R S socket_proto)
      with "[$Hh $Hsoup $Hproto]");
      try assumption; try reflexivity.
    iIntros (m) "[%Hdest
      [(%Hfresh & Hsock & Hhist & _ & #Hproto_respected_m) |
      (%Hm_inR & Hh & Hsoup)]]".
    - (** The mesage is fresh *)
      iMod ("Hclose" with "[$Hsock Hhist]") as "_"; last iModIntro.
      { iNext. iExists ({[m]} ∪ R), S.
        iFrame "%". iFrame "Hhist".
        iApply big_sepS_union; first set_solver.
        iSplit; last iAssumption.
        by iApply big_sepS_singleton. }
      wp_apply wp_unSOME; [ done | iIntros (_) ].
      wp_let. wp_proj.
      iDestruct "Hproto_respected_m"
        as "(%st'_val & %st'_log & %st'_h__local & %st'_h__sub &
          %senderId & %recipientId & %f_sender & %f_recipient &
          %Hsender_addr & %Hrecipient_addr & %Hf_sender & %Hf_recipient &
          %Hst'_ser & %Hst'_coh & %st'_denot & %Hst'_locisloc & %Hst'_subisfor
          & %Hst'_validity & #Hst'_snap)".
      simplify_eq/=.
      wp_apply ((@apply_thread_spec_aux
        h s γlock lockp stp merge_fun st'_h__local st'_h__sub st'_val φ m R
        repId f_sender st'_log Hst'_validity Hst'_coh Hst'_ser Haddr st'_denot)
        with "[$][$][$][$][$][$][$][$]").
    - (** The message is not fresh. *)
      (** TODO: Use the ownership of a local snapshot associated to the remote
        * state and the peoperties of the lub not to blindly update the
        * resources all over again. *)
      iMod ("Hclose" with "[Hh Hsoup]") as "_"; last iModIntro.
      { iNext. iExists R, S. iFrame "%". iFrame "#". iFrame. }
      wp_apply wp_unSOME; [done | iIntros (_) ].
      wp_let. wp_proj.
      iAssert (socket_proto m)
        as "(%st'_val & %st'_log & %st'_h__local & %st'_h__sub &
          %senderId & %recipientId & %f_sender & %f_recipient &
          %Hsender_addr & %Hrecipient_addr & %Hf_sender & %Hf_recipient &
          %Hst'_ser & %Hst'_coh & %st'_denot & %Hst'_locisloc & %Hst'_subisfor
          & %Hst'_validity & #Hst'_snap)";
        first by iDestruct (big_sepS_elem_of with "Hproto_respected") as "Hm";
          first exact Hm_inR.
      simplify_eq/=.
      wp_apply ((@apply_thread_spec_aux
        h s γlock lockp stp merge_fun st'_h__local st'_h__sub st'_val φ m R
        repId f_sender st'_log Hst'_validity Hst'_coh Hst'_ser Haddr st'_denot)
        with "[$][$][$][$][$][$][$][$]").
  Qed.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [statelib_init] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+              **)
  Lemma internal_init_spec_holds :
    StLib_GlobalInv -∗ internal_init_spec.
  Proof.
    iIntros "#Hinv" (i addr fixed_addr addrs_val crdt_val).
    iModIntro.
    iIntros "(%Hislist&%Haddr&#Hprotos&Hsoup&Hfree&[Huser_tok Hlock_tok]&#Hcrdt_spec)Hφ".
    wp_lam. wp_pures.
    wp_apply "Hcrdt_spec"; first trivial.
    iIntros (v) "(%init_st_fn & %mutator_fn & %merge_fn & -> &
      #init_st_spec & #mutator_spec & #merge_spec)".
    wp_pures.
    wp_apply "init_st_spec"; first trivial.
    iIntros (st Hcoh_st).
    wp_alloc stp as "Hstp". wp_pures.
    wp_apply ((newlock_spec lock_inv_ns _ (lock_inv_aux i stp)) with "[Hlock_tok Hstp]").
    { iExists (ip_of_address addr), st, st_crdtM_init_st, ∅, ∅.
      iSplit; first by rewrite Haddr/=.
      iFrame.
      iFrame "%".
      iSplit.
      - iExists i.
        repeat (iSplit; first done).
        iFrame.
      - iPureIntro.
        replace (∅ ∪ ∅) with (∅: Lst LogOp); last set_solver.
        exact st_crdtM_init_st_coh. }
    iIntros (lockp γ_lock) "#Hislock". wp_let.
    wp_socket h as "Hh". wp_pures.
    wp_apply (wp_list_nth_some _ i CRDT_Addresses).
    { iSplit; iPureIntro; first assumption.
      pose (fin_to_nat_lt i). lia. }
    iIntros (v (a & -> & HH)).
    assert (a = addr) as ->.
    { apply nth_error_lookup in HH. rewrite Haddr in HH. by simplify_eq/=. }
    wp_apply wp_unSOME; [ trivial | iIntros (_) ].
    wp_let.
    wp_apply (aneris_wp_socketbind with "[$]"); try done.
    iIntros "Hh".
    set (s := RecordSet.set saddress (λ _ : option socket_address, Some addr)
                            {| sfamily := PF_INET; stype := SOCK_DGRAM;
                               sprotocol := IPPROTO_UDP; saddress := None |}).
    iDestruct (inv_alloc socket_inv_ns _ (socket_inv_prop i h addr s)
      with "[Hh Hsoup]")
      as "> #Hsocketinv".
    { iNext. iExists ∅, ∅. iFrame.
      by repeat iSplit; last iApply big_sepS_empty. }
    wp_seq.
    wp_apply aneris_wp_fork.
    iSplitL "Huser_tok Hφ"; first (iNext; wp_seq; wp_apply aneris_wp_fork; iSplitL); iNext.
    + wp_pures.
      wp_apply ((internal_get_state_spec_holds (fin_to_nat i)) with "[$]").
      iIntros (getst_fun) "getstate_spec".
      wp_pures.
      wp_apply (internal_update_spec_holds with "[$]").
      iIntros (update_fun) "update_spec".
      wp_pures. iApply "Hφ".
      iFrame.
      iExists i.
      iDestruct "Huser_tok" as "(Hown & Hsub & Hcc)".
      iFrame.
      do 3 (iSplit; first done).
      iExists i.
      rewrite union_empty_R. by iFrame.
    + wp_apply (internal_broadcast_spec_holds _ s); try done.
      - iPureIntro. apply fin_to_nat_lt.
      - iFrame "#".
    + wp_apply ((apply_thread_spec h addr s) with "[][][][][][$]"); try done.
      by iApply (big_sepL_lookup with "Hprotos").
  Qed.

End StateLib_Proof.

