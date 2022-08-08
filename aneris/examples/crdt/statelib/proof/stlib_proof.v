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
  Require Import resources resources_inv resources_local resources_global resources_lock.

From aneris.examples.crdt.statelib Require Import statelib_code.
From aneris.examples.crdt.statelib.user_model
  Require Import params model semi_join_lattices.
From aneris.examples.crdt.statelib.time Require Import time.
From aneris.examples.crdt.statelib.STS Require Import utils gst lst mutation.
From aneris.examples.crdt.statelib.proof
  Require Import spec events resources utils resources
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
            !Internal_StLibG LogOp Σ, !StLib_GhostNames,
            st_deser: val, stser: serialization}.

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
    rewrite/get_state. wp_pures.
    iApply "Hφ"; clear φ.

    iIntros (Haddr φ) "!> Hpre".
    wp_pures.
    wp_apply (acquire_spec with "Hislock").
    iIntros (v) "(-> & Hlocked & Hlock_aux)".
    wp_pures.
    
    rewrite/lock_inv_aux.
    iDestruct "Hlock_aux"
      as (ip phys_st log_st h__own h__for Hip)
        "(Hloc & %Hcoh & (%f & %Hf & %Hislocal & %isforeign & Hown_loc & Hown_for) & %Hcoh')".
    rewrite Haddr in Hip.
    simplify_eq/=.
    wp_load.

    wp_bind (Lam _ _).
    wp_apply (aneris_wp_atomic _ _ (↑CRDT_InvName)).
    iMod "Hpre" as (s1 s2) "[(%f' & %Hf' & %Hlocal & %Hsub & Hown_local & Hown_sub & #Hlocal_snap) Hclose]".
    wp_pures.

    assert (f = f') as <-; first by apply fin_to_nat_inj.
    iDestruct (both_agree_agree with "Hown_loc Hown_local")
      as "(Hown_loc & Hown_local & <-)".

    (* open invariant *)
    iInv "Hinv" as "> (%g & Hglob_ag & Hglob_snap & %Hv & Hglob_local)" "Hclose'".
    
    iDestruct ((forall_fin f) with "Hglob_local")
      as "[(%S' & [%Hnin Hin] & Hother)
        (%h__local & %h__foreign & %h__subset &
          %Hproj & %Hlocal_evs & %Hfor_evs & %Hsub_evs & %Hcc &
          Hown_local' & Hown_foreign' & Hown_subset' & Hown_cc')]".
    iDestruct (both_agree_agree with "Hown_sub Hown_subset'")
      as "(Hown_sub & Hown_subset' & ->)".
    iDestruct (both_agree_agree with "Hown_for Hown_foreign'")
      as "(Hown_for & Hown_foreign' & ->)".
    iDestruct (both_agree_agree with "Hown_local' Hown_loc")
      as "(Hown_local' & Hown_loc & <-)".

    (** Update. *)
    iDestruct (
      (own_update_2 (γ_loc_sub !!! f) _ _ ((1/3 + 2/3)%Qp, to_agree h__foreign))
      with "Hown_subset' Hown_sub") as ">[Hown_subset' Hown_sub]".
    { rewrite -pair_op frac_op agree_idemp.
      assert (1 / 3 + 2 / 3 = 1)%Qp as ->; first compute_done.
      by apply cmra_update_exclusive. }
    iDestruct (
      (own_update (γ_loc_cc !!! f) _
      (● princ_ev (h__local ∪ h__foreign) ⋅ ◯ princ_ev (h__local ∪ h__foreign)))
      with "Hown_cc'") as ">[Hown_cc' #Hfrag]";
      first by apply monotone_update.

    iDestruct ((forall_fin' f) with "[Hown_local' Hown_foreign' Hown_subset' Hown_cc' Hin Hother]") as "Hglob_local".
    { iSplitL "Hother Hin".
      - iExists S'. iFrame "%". iFrame "Hother Hin".
      - iExists h__local, h__foreign, h__foreign.
        iFrame "%". by iFrame. }
    iMod ("Hclose'" with "[Hglob_snap Hglob_ag Hglob_local]") as "_".
    { iNext. iExists g. by iFrame. }
    iModIntro. wp_pures.
    iMod ("Hclose" with "[Hown_local Hown_sub]") as "Hφ"; last iModIntro.
    { repeat iSplit.
      - iPureIntro.
        destruct Hcc as [hsub hcc].
        intros x Hx_in.
        pose (Hsub _ Hx_in) as Hx_orig.
        apply (elem_of_union_r _ h__local) in Hx_in as Hx_in'.
        apply hsub in Hx_in'.
        apply elem_of_union in Hx_in' as [Hx_in'%Hislocal | Hx_in'];
          first by exfalso; eauto.
        exact Hx_in'.
      - iExists f. iFrame "%". iFrame.
        iExists f. by iFrame "%".
      - iFrame "%".
      - iFrame "%". }

    wp_pures.
    wp_apply (release_spec with "[$Hislock $Hlocked Hloc Hown_loc Hown_for]").
    { iExists (ip_of_address saddr), phys_st, log_st, h__local, h__foreign.
      rewrite Haddr.
      iFrame "%". iFrame.
      iSplit; first done.
      iExists f. by iFrame. }

    iIntros (v) "->". wp_pures.
    iApply "Hφ".
  Qed.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [update] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~+                     **)

  (* TODO: move somewhere else *)
  Lemma op_coh_sv_val {log_op op} :
    StLib_Op_Coh log_op op -> ∃ (sv : StLib_SerializableVal), op = StLib_SV_val sv.
  Proof. Admitted.

  Lemma internal_update_spec_holds (repId : nat) (addr : socket_address)
      (lockv broadcast__fun mutator__fun : val) (st_loc : loc) (γ__lock : gname) :
    {{{ StLib_GlobalInv ∗
        lock_inv addr γ__lock lockv repId st_loc ∗
        (** TODO: broadcast_spec broadcast__fun i saddr ∗ *)
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
    pose proof (op_coh_sv_val Hop_coh) as [sv ->].
    wp_pures.
    iDestruct "HPlock"
      as (ip phys_st log_st h__local h__for Hip)
        "(Hloc & %Hcoh & (%f & %Hf & %Hislocal & %isforeign & Hown_loc & Hown_for) & %Hcoh')".
    wp_apply (aneris_wp_load with "[Hloc]").
    { iNext. rewrite Haddr_proj in Hip. by simplify_eq/=. }
    iIntros "Hloc'".
    wp_bind (mutator__fun _ _ _).
    pose (fresh_event (h__local ∪ h__for) log_op repId) as fev.
    iDestruct ("mutatorspec" $! addr repId phys_st sv (h__local ∪ h__for) fev log_op log_st) as "mutatorspec'".
    wp_apply aneris_wp_value_fupd.
    iMod "Hpre" as (h_g h__local' h__sub)
      "[(Hglobstate &
      %f' & %Hf' & %Hlocalislocal & %Hsubisforeign & Hown_local' & Hown_sub' & #Hlocsnap)
      Hother]".
    assert (f = f') as <-.
    { apply fin_to_nat_inj. by rewrite Hf Hf'. }
    iInv "Hinv" as "> (%g & Hglob_ag & Hglob_snap & %Hv & Hglob_local)" "Hclose'".
    iDestruct ((forall_fin f) with "Hglob_local")
      as "[(%S & [%Hnin %Hin] & HdefS) (%local & %foreign & %sub & %Hg_proj & %locevs & %forevs & %forevs' & %Hcc & Hloc & Hfor & Hsub & Hcc)]".

    (** Regrouping owned resources to prepare for an update *)
    Ltac mypairvalid A B :=
      ( apply pair_valid in A as [_ A]; simpl in A;
        apply (to_agree_op_inv_L) in A as B; destruct B;
        rewrite agree_idemp; clear A ).
    iCombine "Hglob_ag" "Hglobstate" as "Hglobal".
    iDestruct (own_valid_l with "Hglobal") as "[%Hvalid Hown_global]".
    mypairvalid Hvalid Hglobal_eq.
    iCombine "Hown_loc" "Hloc" as "Hown_loc".
    iDestruct (own_valid_l with "Hown_loc") as "[%Hvalid Hown_local]".
    mypairvalid Hvalid Hlocal_eq.
    iCombine "Hown_local" "Hown_local'" as "Hown_local".
    iDestruct (own_valid_l with "Hown_local") as "[%Hvalid Hown_local]".
    mypairvalid Hvalid Hlocal_eq.
    iDestruct (both_agree_agree with "Hown_for Hfor") as "(Hown_for & Hfor & <-)".
    iDestruct (both_agree_agree with "Hown_sub' Hsub") as "(Hown_sub' & Hsub & <-)".

    assert(1/3 + 2/3 = 1)%Qp as ->; first compute_done.
    assert(1/3 + 1/3 + 1/3 = 1)%Qp as ->; first compute_done.

    iDestruct (own_update _ _ (((1/3)%Qp, to_agree ( h__local ∪ {[ fev ]} )) ⋅ ((2/3)%Qp, to_agree ( h__local ∪ {[ fev ]} )))
      with "Hown_local") as "> [Hown_local Hown_local']".
    { rewrite -pair_op agree_idemp frac_op. by apply cmra_update_exclusive. }
    iDestruct (own_update _ _ (((1/3)%Qp, to_agree ( g.1 ∪ {[ fev ]} )) ⋅ ((2/3)%Qp, to_agree (g.1 ∪ {[ fev ]} )))
      with "Hown_global") as "> [Hown_global' Hown_global]".
    { rewrite -pair_op agree_idemp frac_op. by apply cmra_update_exclusive. }
    iDestruct (own_update _ _ (● (g.1 ∪ {[ fev ]}))
      with "Hglob_snap") as "> Hown_global_snap".
    { rewrite (auth_update_auth g.1 (g.1 ∪ {[fev]})(g.1 ∪ {[fev]})); first done.
      apply gset_local_update, union_subseteq_l. }
    iDestruct (own_update _ _ (● princ_ev (h__local ∪ {[ fev ]} ∪ h__sub))
      with "Hcc") as "> Hcc".
    { admit. }

    pose (mutator_global_valid g log_op f Hv) as Hv'.
    assert (fresh_event (g.2 !!! f) log_op f = fev) as Hfev_eq.
    { unfold fev. by rewrite Hg_proj Hf'. }

    iMod ("Hclose'" with "[HdefS Hfor Hsub Hcc Hown_global' Hown_global_snap Hown_local]") as "_".
    { iNext.
      iExists (g.1 ∪ {[ fev ]}, vinsert f (g.2 !!! f ∪ {[ fev ]}) g.2).
      iFrame "Hown_global' Hown_global_snap".
      rewrite -Hfev_eq. iFrame "%".
      iExists (S ∪ {[ f ]}).
      iSplit.
      { iPureIntro. intros f'.
         destruct (decide (f' = f)) as [-> | Hneq%Hin];
          [ by apply elem_of_union_r, elem_of_singleton
          | by apply elem_of_union_l ]. }
      iApply big_sepS_union; first set_solver.
      iSplitL "HdefS".
      - admit.
      - iApply big_sepS_singleton.
        iExists (h__local ∪ {[ fev ]}), h__for, h__sub.
        iSplitR.
        { iPureIntro.
          rewrite vlookup_insert -Hfev_eq Hg_proj. set_solver. }
        iSplitR.
        { iPureIntro.
          by intros e [He_in%locevs | ->%elem_of_singleton]%elem_of_union. }
        iSplitR; first by iPureIntro.
        iSplitR; first by iPureIntro.
        iSplitR.
        { iPureIntro. admit. }
        rewrite Hfev_eq. iFrame. }

    iApply ("mutatorspec'" with "[]").
    { repeat iSplit; iPureIntro; try done.
      (** The folliwing admots can be solved by using Hv'. *)
      - intros Himp.
        rewrite -Hg_proj in Himp.
        destruct (fresh_event_not_eq_eid (g.2 !!! f) log_op f (VGst_lhst_valid _ Hv f) fev Himp).
        by rewrite Hfev_eq.
      - apply elem_of_union_r, elem_of_singleton. reflexivity.
      - admit. (** TODO: fresh_event is maximal *)
      - admit.
      - admit. (** TODO: fresh_event respects total order *) }
    assert (Hfev_op: EV_Op fev = log_op); first reflexivity.
    iDestruct ("Hother"
      $! fev (g.1 ∪ {[ fev ]}) (h__local ∪ {[ fev ]}) h__for $_)
      as "Hother".
    (** TODO: get rid of that modality. 
    iIntros (st') "[%log_st' [%Hcoh_st' %Hmut]]".
    wp_bind (_ <- _)%E. wp_store. wp_seq.
    wp_apply (release_spec with "[$Hlockinv $Hlocked Hloc' Hown_loc Hown_for]").
    { iExists ip, st', log_st', (h__local ∪ {[ fev ]}), h__for.
      simplify_eq/=. iFrame "%"; iFrame.
      rewrite Haddr_proj in Hip.
      simplify_eq/=. iFrame "%"; iFrame.
      iSplit.
      - iExists f. repeat iSplit; try done.
        + admit.
        + iFrame. admit. (* oupsi :/ *)
      - admit. }
    iIntros (v ->).
    iApply "Hother".
    *)
  Admitted.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [sendToAll] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+                  **)
  Definition internal_sendToAll_spec
    (h: socket_handle) (sock: socket) (repId: RepId) (sock_addr: socket_address)
    (dstlist: val) : iProp Σ :=
    ⌜repId < length CRDT_Addresses⌝ -∗
    ⌜is_list CRDT_Addresses dstlist⌝ -∗
    ∀ (m: string), (** TODO: require m to follow the protocol. *)
    {{{ ⌜ CRDT_Addresses !! repId = Some sock_addr ⌝ ∗
      ⌜ saddress sock = Some sock_addr ⌝ ∗
      socket_inv repId h sock_addr sock ∗
      ∃ (st_v: val) (st_log: LogSt) (h__local h__sub: event_set LogOp),
        ⌜ s_is_ser StLib_StSerialization st_v m ⌝ ∗
        ⌜ StLib_St_Coh st_log st_v ⌝ ∗
        ⌜⟦h__local ∪ h__sub⟧ ⇝ st_log⌝ ∗
        StLib_OwnLocalSnap repId h__local h__sub }}}
    sendToAll #(LitSocket h) dstlist #repId $m @[ip_of_address sock_addr]
    {{{ RET #(); True }}}.

  Lemma internal_sendToAll_spec_holds
    (h: socket_handle) (sock: socket) (repId: RepId) (sock_addr: socket_address)
    (dstlist: val) :
    ⌜repId < length CRDT_Addresses⌝ -∗
    ⌜is_list CRDT_Addresses dstlist⌝ -∗
    ∀ (m: string), (** TODO: require m to follow the protocol. *)
    {{{ socket_inv repId h sock_addr sock ∗
      ∃ (st_v: val) (st_log: LogSt) (h__local h__sub: event_set LogOp),
        ⌜ s_is_ser StLib_StSerialization st_v m ⌝ ∗
        ⌜ StLib_St_Coh st_log st_v ⌝ ∗
        ⌜⟦h__local ∪ h__sub⟧ ⇝ st_log⌝ ∗
        StLib_OwnLocalSnap repId h__local h__sub }}}
    sendToAll #(LitSocket h) dstlist #repId $m @[ip_of_address sock_addr]
    {{{ RET #(); True }}}.
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

    iIntros (Hi Hislist) "%m !> %φ (#HSocketInv &
      (%st_v & %sy_log & %h__local & %h__sub & %Hser & %Hdenot & #Hsnap))
      Hφ".
    rewrite/sendToAll. do 6 wp_pure _.
    wp_alloc l as "Hl". wp_let.
    iMod(own_alloc (1%Qp, to_agree O%nat)) as (γi) "[Hγi Hi]"; first done.
    iMod (inv_alloc (nroot .@ "jfj") _
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

        (** TODO:
          * require the caller [broadcast] to give those resources away
          * when calling sendToAll.
          * (?) difficulty: r is unknown at the call of the function *)
        wp_apply (aneris_wp_send _  (socket_proto repId) with "[$Hh $Hsoup ]");
          try done.
        { admit. }
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
  Admitted.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [broadcast] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+                  **)
(** TODO: Specification of the broadcast function. Inspiration from RCB. **)
  Definition internal_broadcast_spec
    (broadcast_fun destlist: val) (repId: RepId) addr h s addr_list : iProp Σ :=
    ∀ (v: StLib_SerializableVal),
    ⌜is_list CRDT_Addresses addr_list⌝ -∗
    ⌜repId < length CRDT_Addresses⌝ -∗
    ⌜ CRDT_Addresses !! repId = Some addr⌝ -∗
    ⌜ saddress s = Some addr ⌝ -∗
    ⌜ sblock s = true ⌝ -∗
    addr ⤇ (socket_proto repId) -∗
    socket_inv repId h addr s -∗
    <<< ∀∀ (h__global h__local h__for : event_set LogOp),
      StLib_OwnGlobalSnap h__global ∗
      StLib_OwnLocalState repId h__local h__for >>>
      broadcast_fun #() @[ip_of_address addr] ↑CRDT_InvName
    <<<▷  RET #(); False >>>.

  (** WIP *)



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [apply_thread] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+               **)
  (** WIP *)



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [statelib_init] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+              **)
  (** Not proven yet. *)


End StateLib_Proof.

