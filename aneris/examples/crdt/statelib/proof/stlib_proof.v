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
From aneris.examples.crdt.statelib.STS
  Require Import utils gst lst mutation merge.
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

    (** Update of the resources: beginning. *)
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
    (** Update of the resources: end. *)

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
    wp_bind (!_)%E.
    iInv "Hinv" as "> (%g & Hown_global & Hown_global_snap & %Hv & HS)" "Hclose".
    iDestruct ((forall_fin f) with "HS")
      as "[(%S & %S_def & HS)
        (%h__local_f & %h__foreign_f & %h__loc_f &
        %Hproj & %islocal_f & %isforeign_f & %isforeign'_f & %iscc_f &
        Hown_local_f & Hown_for_f & Hown_sub_f & Hown_cc_f)]".
    iDestruct (both_agree_agree with "Hown_local_f Hown_loc")
      as "(Hown_local_f & Hown_loc & ->)".
    iDestruct (both_agree_agree with "Hown_for_f Hown_for")
      as "(Hown_for_f & Hown_for & ->)".
    iDestruct ((forall_fin' f) with "[Hown_cc_f Hown_for_f Hown_local_f HS Hown_sub_f]") as "HS".
    { iSplitL "HS". iExists S. by iFrame.
      simpl. iExists h__local, h__for, h__loc_f. by iFrame. }
    wp_apply (aneris_wp_load with "[Hloc]").
    { iNext. rewrite Haddr_proj in Hip. by simplify_eq/=. }
    iIntros "Hloc'".
    iMod ("Hclose" with "[Hown_global Hown_global_snap HS]") as "_"; last iModIntro.
    { iNext. iExists g. by iFrame. }
    wp_bind (mutator__fun _ _ _).
    pose (fresh_event (h__local ∪ h__for) log_op repId) as fev.
    iDestruct ("mutatorspec" $! addr repId phys_st sv (h__local ∪ h__for) fev log_op log_st) as "mutatorspec'".
    iApply ("mutatorspec'" with "[]").
    { pose (mutator_lhst_valid g log_op f Hv f) as Hval.
      rewrite /= in Hval.
      repeat iSplit; iPureIntro; try done.
      - rewrite/fev -Hproj -Hf.
        exact (fresh_event_is_fresh (g.2 !!! f) f log_op (VGst_lhst_valid _ Hv f)).
      - apply elem_of_union_r, elem_of_singleton. reflexivity.
      - intros ev Hev_in Hlt.
        assert (ev <_t fev) as Himp.
        { destruct (fresh_event_time_mon (h__local ∪ h__for) log_op f) with ev;
          admit. }
        assert(fev <_t fev);
          first (apply ts_lt_trans with (EV_Time ev); assumption).
        apply ts_lt_irreflexive with (EV_Time fev); assumption.
      - intros ev ev' Hev_in Hev'_in Ht_eq.
        apply (mutator_ext_time_preservation g log_op f Hv ev ev');
          last assumption; simpl.
        + apply elem_of_union in Hev_in as [Hev_in | ->%elem_of_singleton].
          * apply elem_of_union_l.
            rewrite -Hproj in Hev_in.
            exact (gst_valid_inclusion g f Hv ev Hev_in).
          * apply elem_of_union_r, elem_of_singleton.
            by rewrite/fev Hproj Hf.
        + apply elem_of_union in Hev'_in
          as [Hev'_in | ->%elem_of_singleton].
          * apply elem_of_union_l.
            rewrite -Hproj in Hev'_in.
            exact (gst_valid_inclusion g f Hv ev' Hev'_in).
          * apply elem_of_union_r, elem_of_singleton.
            by rewrite/fev Hproj Hf.
      - intros ev ev' Hev Hev' Hneq.
        destruct (VLst_same_orig_comp _ Hval ev ev').
        + simpl. by rewrite vlookup_insert Hf Hproj -/fev.
        + simpl. by rewrite vlookup_insert Hf Hproj -/fev.
        + assumption.
        + by left.
        + by right. }
    clear Hproj Hv g S S_def.
    iIntros (st') "!> (%log_st' & %Hst'_coh & %Hst'_denot & %Hst'_mut)".

    wp_bind(_ <- _)%E.
    wp_apply (aneris_wp_atomic _ _ (↑CRDT_InvName)).
    iMod "Hpre" as (h_g h__local' h__sub)
      "[(Hglobstate &
      %f' & %Hf' & %Hlocalislocal & %Hsubisforeign & Hown_local' & Hown_sub' & #Hlocsnap)
      Hclose]".
    iModIntro.
    wp_store.
    assert (f = f') as <-.
    { apply fin_to_nat_inj. by rewrite Hf Hf'. }
    iInv "Hinv" as "> (%g & Hglob_ag & Hglob_snap & %Hv & Hglob_local)" "Hclose'".
    iDestruct ((forall_fin f) with "Hglob_local")
      as "[(%S & [%Hnin %Hin] & HdefS) (%local & %foreign & %sub & %Hg_proj & %locevs & %forevs & %forevs' & %Hcc & Hloc & Hfor & Hsub & Hcc)]".

    (** Update of the resources: beginning. *)
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
    iDestruct (own_update _ _ (● princ_ev (h__local ∪ {[ fev ]} ∪ h__sub) ⋅ ◯ princ_ev (h__local ∪ {[fev]} ∪ h__sub))
      with "Hcc") as "> [Hcc #Hcc_frag]".
    { apply auth_update_alloc. admit. }

    pose (mutator_global_valid g log_op f Hv) as Hv'.
    assert (fresh_event (g.2 !!! f) log_op f = fev) as Hfev_eq.
    { unfold fev. by rewrite Hg_proj Hf'. }
    (** Update of the resources: end. *)

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
      - iApply (big_sepS_mono with "HdefS").
        iIntros (x Hx_in) "(%__local & %__foreign & %__sub & %__Hproj & %__islocal & %__isfor & %__issub & %__iscc & __ownloc & __own)".
        iExists __local, __foreign, __sub.
        repeat iSplit; try done.
        + iPureIntro. simpl. rewrite vlookup_insert_ne; first assumption.
          set_solver.
        + iPureIntro. by destruct __iscc.
        + iPureIntro. by destruct __iscc.
        + iFrame.
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
        { iPureIntro. split.
          - rewrite (union_comm h__local _). do 2 rewrite -union_assoc.
            apply (union_mono_l {[fev]}).
            by destruct Hcc.
          - admit.
          }
        rewrite Hfev_eq. iFrame. }

    assert (Hfev_op: EV_Op fev = log_op); first reflexivity.

    iDestruct "Hown_local'" as "[Hown_local Hown_local']".
    replace (2/3/2)%Qp with (1/3)%Qp; last compute_done.
    iMod ("Hclose" $! fev (g.1 ∪ {[fev]}) (h__local ∪ {[fev]}) with "[Hown_sub' Hown_global Hown_local']") as "Hpost".
    { repeat iSplit; try done.
      - iPureIntro.
        rewrite -Hfev_eq. exact (fresh_event_is_fresh_global g f log_op Hv).
      - iPureIntro.
        rewrite -Hfev_eq.
        assert (fresh_event (g.2 !!! f) log_op f ∉ h__local ∪ h__for).
        { intros Jap.
          destruct (fresh_event_is_fresh (g.2 !!! f) f log_op (VGst_lhst_valid _ Hv f)).
          by rewrite -Hg_proj in Jap. }
        set_solver.
      - iPureIntro. (** TODO: use fresh is maximal *) admit.
      - iPureIntro. (** TODO: use fresh is maximal *) admit.
      - iFrame.
        iExists f. iFrame "%".
        iSplit.
        + iPureIntro.
          intros e [He_in%Hislocal | ->%elem_of_singleton]%elem_of_union;
            by rewrite Hf.
        + iFrame "Hown_sub' Hown_local'". iExists f. iFrame "#".
          repeat (iSplit; iPureIntro); try done.
          split; last assumption.
          intros e [He_in%Hislocal | ->%elem_of_singleton]%elem_of_union;
            by rewrite Hf. }

    iModIntro.
    wp_seq.
    wp_apply (release_spec with "[$Hlockinv $Hlocked Hown_local Hown_for Hloc']").
    { iExists ip, st', log_st', (h__local ∪ {[ fev ]}), h__for.
      iFrame "%".
      iSplitL "Hloc'".
      { rewrite Haddr_proj in Hip; simplify_eq/=. iFrame. }
      iSplitL; last first.
      { iPureIntro.
        by replace (h__local ∪ {[fev]} ∪ h__for)
          with (h__local ∪ h__for ∪ {[fev]});
          last set_solver. }
      iExists f.
      iSplit; first done.
      iSplit.
      { iPureIntro.
        by intros x [Hxin%Hislocal | ->%elem_of_singleton]%elem_of_union. }
      iFrame. }
    iIntros (v ->).
    iApply "Hpost".
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

  Lemma internal_broadcast_spec_holds
    (repId : nat) destlist s h (addr : socket_address) (lockv addr_list : val) (st_loc : loc) (γ__lock : gname):
    {{{
        internal_sendToAll_spec h s repId addr addr_list ∗
        StLib_GlobalInv ∗
        lock_inv addr γ__lock lockv repId st_loc }}}
        broadcast StLib_StSerialization.(s_serializer).(s_ser) lockv #(LitSocket h) #st_loc addr_list #repId  @[ip_of_address addr]
{{{ (v: val), RET v; internal_broadcast_spec v destlist repId addr h s addr_list  }}}.
  Proof.
    (** TODO: WIP *)
  Admitted.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [apply_thread] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+               **)
  Definition merge_spec (merge_fun : val) : iProp Σ :=
    ∀ (addr : socket_address) (st st' : val) (s s' : (event_set LogOp))
    (log_st log_st': LogSt),
    {{{ ⌜StLib_St_Coh log_st st⌝ ∗
        ⌜StLib_St_Coh log_st' st'⌝ ∗
        ⌜⟦ s ⟧ ⇝ log_st⌝ ∗
        ⌜⟦ s' ⟧ ⇝ log_st'⌝
    }}}
      merge_fun st st' @[ip_of_address addr]
    {{{ st'', RET st'';
        ∃ (log_st'' : LogSt),
          ⌜StLib_St_Coh log_st'' st''⌝ ∗
          ⌜log_st'' = lat_lub log_st log_st'⌝ ∗
        ⌜⟦ s ∪ s' ⟧ ⇝ log_st''⌝
    }}}.

  Lemma apply_thread_spec
    (h: socket_handle) (addr: socket_address) (s: socket)
    (repId: RepId) (γlock: gname)
    (lockp : val) (stp: loc) (merge_fun: val) :
    ⌜ CRDT_Addresses !! repId = Some addr⌝ -∗
    ⌜ saddress s = Some addr ⌝ -∗
    ⌜ sblock s = true ⌝ -∗
    addr ⤇ (socket_proto repId) -∗
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

    wp_apply (acquire_spec with "His_lock").
    iIntros (v) "(-> & Hlocked &
      (%ip & %phys_st & %log_st & %h__own & %h__foreign &
      %Hip & Hloc & %Hcoh & Hown_lock & %Hst_coh))".
    assert (Hip_eq: ip_of_address addr = ip).
    { rewrite Haddr in Hip. by simplify_eq/=. }
    wp_seq.

    wp_bind(ReceiveFrom _).
    iInv "Hsock_inv" as "(%R & %S & Hh & > (%Haddr_sock & %Haddr_proj & Hsoup & #Hproto_respected))" "Hclose".
    wp_apply ((aneris_wp_receivefrom
      (ip_of_address addr) addr _ h s R S (socket_proto repId))
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
        as "(%st'_val & %st'_log & %st'_h__local & %st'_h__foreign &
          %remote_orig & %Hremote_addr & %Hser &
          %Hst'_serialization & %Hst'_coherence &
          %remote_f & Hremote_f &
          Hst'_localislocal & Hst'_foreignisforeign &
          Hst'_own_cc)".
      wp_apply (s_deser_spec); [ iFrame "%" | iIntros (_) ].
      wp_let.
      wp_bind (!_)%E.
      wp_apply (aneris_wp_load with "[Hloc]").
      { rewrite Haddr_proj in Hip. by simplify_eq/=. }
      iIntros "Hloc".
      wp_bind (merge_fun _ _)%E.
      wp_apply ("Hmerge" $! addr
        phys_st st'_val (h__own ∪ h__foreign) (st'_h__local ∪ st'_h__foreign)
        log_st st'_log); first done.
      iIntros (st'' (st''_log & Hst''_coh & Hst''_islub & Hst''_denot)).
      wp_bind (_ <- _)%E.
      iInv "Hinv" as "> (%g & Hown_global & Hown_global_snap & %Hv & HS)" "Hclose".
      wp_store.
      (** TODO: Update of the resources: beginning. *)

      (* *** α) from HS:
       *       → st'__h__local ∪ st'_h__foreign ⊆_cc g.2 !!! (f_remote)
       *       → h__local ∪ h__foreign = g.2 !!! f
       *
       * *** β) from STS:
       *       → updated g is valid (Gst-wise)
       *       → filter (not from f) (st'_h__local ∪ st'_h__foreign)
       *           ⊆_cc h__local ∪ h__foreign
       * NB: remember that
       *     the updated version of g.2 !!! f
       *     is equal to (h__local ∪ h_foreign ∪ st'_h__local ∪ st'_h__foreign)
       *
       * *** γ) Actual resource update:
       *       → resources:  only affects h__foreign
       *       → properties: affects both GlobInv and OwnLock
       *      /!\ Issue with the global state if g has to be updated here.
       *          An alternative would be to postpone its update to the call of
       *          [update], but this would mean that the global state is «late».
       *)
      iDestruct ((forall_fin remote_f) with "HS")
        as "[(%T & [%HT_nin%HT_def] & HT_res)
          (%st'_h__local' & %st'_h__foreign' & %st'_h__sub' & %Hremote_proj &
          %Hst'_local' & %Hst'_foreign' & %Hst'_sub' & %Hst'_cc' &
          Hremote_own_local' & Hremote_own_foreign' & Hremote_own_sub' &
          Hremote_own_cc')]".
      iAssert (
        own (γ_loc_cc !!! remote_f) (● princ_ev (st'_h__local' ∪ st'_h__sub'))
        ∗ ⌜st'_h__local ∪ st'_h__foreign ⊆_cc g.2 !!! remote_f⌝)%I
        with "[Hremote_own_cc' Hst'_own_cc]"
        as "[Hremote_own_cc' [%Hst'_subset%Hst'_depclosed]]".
      { rewrite Hremote_proj.
        iDestruct (princ_ev__subset_cc' with "Hst'_own_cc Hremote_own_cc'")
          as "[Hremote_onw_cc %Hcc]".
        iFrame. iPureIntro.
        destruct Hst'_cc' as [Hsub' Hcc']. destruct Hcc as [Hsub Hcc].
        split.
        - intros x Hx_in%Hsub. by apply Hsub'.
        - intros x y Hx_in Hy_in Hxy_le Hy_in''.
          (** TODO: use the transitivity uf ⊆_cc instead. *)
          assert (Hy_in': y ∈ st'_h__local' ∪ st'_h__sub');
            first by apply Hsub in Hy_in''.
          by apply (Hcc x y (Hcc' x y Hx_in Hy_in Hxy_le Hy_in')). }

      iDestruct ((forall_fin' remote_f)
        with "[HT_res Hremote_own_local' Hremote_own_foreign' Hremote_own_sub'
          Hremote_own_cc']")
        as "HS".
      { iSplitL "HT_res".
        - iExists T. by iFrame "HT_res".
        - simpl.
          iExists st'_h__local', st'_h__foreign', st'_h__sub'. by iFrame. }
      clear T HT_nin HT_def.

      iDestruct "Hown_lock" as "(%f & %Hf & %Hloc & %Hfor & Hown_local & Hown_for)".
      iDestruct ((forall_fin f) with "HS")
        as "[(%T & [%HT_nin%HT_def] & HT_res)
          (%st_h__local & %st_h__foreign & %st_h__sub &
          %Hf_proj & %Hst_local & %Hst_foreign & %Hst_sub & %Hst_cc &
          Hf_own_local & Hf_own_foreign & Hf_own_sub & Hf_own_cc)]".
      (** unification of the names of local and foreign histories on repId *)
      iDestruct (both_agree_agree with "Hown_local Hf_own_local")
        as "(Hown_local & Hf_own_local & ->)".
      iDestruct (both_agree_agree with "Hown_for Hf_own_foreign")
        as "(Hown_for & Hf_own_foreign & ->)".

      (** TODO: Get rid of the shelved goal ! *)
      epose (merge_global_valid g f remote_f (st'_h__local ∪ st'_h__foreign)
        Hv Hst'_subset _) as Hv'.

      iDestruct (own_update_2 (γ_loc_for !!! f) (½, to_agree st_h__foreign) (½, to_agree st_h__foreign)
        (((1/2)%Qp, to_agree (st_h__foreign ∪ (filter (λ e, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__foreign))))
        ⋅ ((1/2)%Qp, to_agree (st_h__foreign ∪ (filter (λ e, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__foreign)))))
        with "Hf_own_foreign Hown_for")
        as "> [Hf_own_foreign Hown_for]".
      { do 2 rewrite -pair_op frac_op Qp_half_half agree_idemp.
          by apply cmra_update_exclusive. }


      (** A few assertions on the new state wrt. equality and subseteq. *)
      assert (H1in:
        filter (λ e, EV_Orig e = f) (st'_h__local ∪ st'_h__foreign)
          ⊆ g.2 !!! f).
      { intros e [He_orig He_in%Hst'_subset%gst_valid_inclusion]%elem_of_filter;  
          last exact Hv.
        destruct (VGst_incl_orig _ Hv e He_in) as (i & Hi & Hiin).
        assert (f = i) as ->.
        { apply fin_to_nat_inj. by rewrite Hi He_orig. }
        assumption. }
      assert(
        g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign) =
        g.2 !!! f
          ∪ filter
              (λ e : Event LogOp, EV_Orig e ≠ f)
              (st'_h__local ∪ st'_h__foreign)).
      { pose (filter_union_complement
          (λ e, EV_Orig e = f) (st'_h__local ∪ st'_h__foreign))
          as Hpartition.
        apply set_eq.
        intros x. split.
        - intros [?|[?%H1in|?]%Hpartition%elem_of_union]%elem_of_union;
            [by apply elem_of_union_l 
            | by apply elem_of_union_l
            | by apply elem_of_union_r].
        - intros [?|[_?]%elem_of_filter]%elem_of_union;
          [ by apply elem_of_union_l
          | by apply elem_of_union_r ]. }
      assert(
        foreign_events f
          (st_h__foreign
           ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
               (st'_h__local ∪ st'_h__foreign)));
        first by intros e
          [He_in%Hst_foreign | [He_norig _]%elem_of_filter]%elem_of_union.
      assert(
        st_h__local ∪ st_h__sub
        ⊆_cc g.2 !!! f
          ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f) (st'_h__local ∪ st'_h__foreign)).
      { split. destruct Hst_cc as [Hsubset Hcc].
        - intros e He_in%Hsubset. rewrite Hf_proj.
          by apply elem_of_union_l.
        - intros x y Hx_in Hy_in Hxy_le Hy_in'.
          admit. } 
      assert (Heq:
        st_h__local ∪ (st_h__foreign
          ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
            (st'_h__local ∪ st'_h__foreign))
          = st_h__local ∪ st_h__foreign ∪ (st'_h__local ∪ st'_h__foreign)).
      { pose (filter_union_complement
          (λ e, EV_Orig e = f) (st'_h__local ∪ st'_h__foreign))
          as Hpartition.
        apply set_eq. intros x. split.
        - intros [?|[?|[_?]%elem_of_filter]%elem_of_union]%elem_of_union;
          [ by apply elem_of_union_l, elem_of_union_l
          | by apply elem_of_union_l, elem_of_union_r
          | by apply elem_of_union_r].
        - intros [[?|?]%elem_of_union | [Hx_in%H1in|?]%Hpartition%elem_of_union]%elem_of_union;
            [ by apply elem_of_union_l
            | by apply elem_of_union_r, elem_of_union_l
            | rewrite Hf_proj in Hx_in
            |by apply elem_of_union_r, elem_of_union_r].
          apply elem_of_union in Hx_in as [?|?];
            [by apply elem_of_union_l
            | by apply elem_of_union_r, elem_of_union_l]. }



      iDestruct ((big_sepS_mono
        (λ k, StLib_GlibInv_local_part k g) (λ k, StLib_GlibInv_local_part k (g.1, vinsert f (g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign)) g.2)))
        with "[$HT_res]") as "HT_res".
      { iIntros (x Hx_in) "(%hloc & %hfor & %hsub & %Hproj & Hreste)".
        iExists hloc, hfor, hsub. iFrame.
        rewrite vlookup_insert_ne; first done.
        intros Heq'. rewrite -Heq' in Hx_in. by destruct HT_nin. }

      iDestruct ((forall_fin' f)
        with "[HT_res Hf_own_local Hf_own_foreign Hf_own_sub Hf_own_cc]")
        as "HS".
      { iSplitL "HT_res".
        - iExists T. by iFrame "HT_res".
        - simpl.
          iExists
            st_h__local,
            (st_h__foreign
              ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
                  (st'_h__local ∪ st'_h__foreign)),
            st_h__sub.
          replace (
            st_h__local
            ∪ (st_h__foreign
              ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
                  (st'_h__local ∪ st'_h__foreign)))
            with
              (g.2 !!! f
                ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
                    (st'_h__local ∪ st'_h__foreign)); last first.
          { rewrite Hf_proj. symmetry.
            rewrite Heq.
            pose (filter_union_complement
              (λ e, EV_Orig e = f) (st'_h__local ∪ st'_h__foreign))
              as Hpartition.
            apply set_eq. intros x. split.
            - intros [[?|?]%elem_of_union|[?%H1in|Hx_in]%Hpartition%elem_of_union]%elem_of_union;
                [ by do 2 apply elem_of_union_l
                | by apply elem_of_union_l, elem_of_union_r
                | apply elem_of_union_l; by rewrite -Hf_proj
                | by apply elem_of_union_r].
            - intros [[?|?]%elem_of_union | [_?]%elem_of_filter]%elem_of_union;
              [ by do 2 apply elem_of_union_l
              | by apply elem_of_union_l, elem_of_union_r
              | by apply  elem_of_union_r]. }
          iFrame. iFrame "%".
          by rewrite /= vlookup_insert. }
      clear T HT_nin HT_def.

      iMod ("Hclose" with "[HS]") as "_"; last iModIntro.
      { iNext.
        iExists (g.1, vinsert f (g.2 !!! f ∪ (st'_h__local ∪ st'_h__foreign)) g.2).
        iFrame "%". iFrame. admit. (* TODO: discuss about the global state *) }

      (** TODO: update from g to g' in the global state (or delay its update
       * until a call to update ?). *)



      (** Update of the resources: end. *)
      wp_seq.
      wp_apply (release_spec with "[$His_lock $Hlocked Hloc Hown_global Hown_global_snap Hown_local Hown_for]").
      { iExists ip, st'', st''_log,
          st_h__local,
          (st_h__foreign
                  ∪ filter (λ e : Event LogOp, EV_Orig e ≠ f)
                      (st'_h__local ∪ st'_h__foreign)).
        rewrite Hip_eq. iFrame "Hloc". iFrame "%".
        iSplit.
        - iExists f. iSplit; first done.
          iSplit; [ by rewrite -Hf | iFrame ].
        - iPureIntro.
          by rewrite Heq. }
      iIntros (v ->).
      by iApply "Hφ".
    - (** The message is not fresh. *)
      (** TODO: Use the ownership of a local snapshot associated to the remote
        * state and the peoperties of the lub not to blindly update the
        * resources all over again. *)
      iMod ("Hclose" with "[Hh Hsoup]") as "_"; last iModIntro.
      { iNext. iExists R, S. iFrame "%". iFrame "#". iFrame. }
      wp_apply wp_unSOME; [done | iIntros (_) ].
      wp_let. wp_proj.
      iAssert (socket_proto repId m)
        as "(%st'_val & %st'_log & %st'_h__local & %st'_h__foreign &
          %remote_orig & %Hremote_addr & %Hst'_ser &
          %Hst'_coh & %Hst'_denot & Hown_LocalSnap)";
        first by iDestruct (big_sepS_elem_of with "Hproto_respected") as "Hm";
          first exact Hm_inR.
      wp_apply (s_deser_spec); [ iFrame "%" | iIntros (_) ].
      wp_let.
      wp_apply (aneris_wp_load with "[Hloc]");
        first by rewrite Hip_eq.
      iIntros "Hloc".
      wp_bind (merge_fun _ _)%E.
      wp_apply ("Hmerge" $! addr
        phys_st st'_val (h__own ∪ h__foreign) (st'_h__local ∪ st'_h__foreign)
        log_st st'_log); first done.
      iIntros (st'' (st''_log & Hst''_coh & Hst''_islub & Hst''_denot)).
      wp_store.
      (** TODO: Copy the resources update above once the proofs are over
        (or rather make it a lemma to avoid duplicating the proof).
        In the future, TODO: use the pre-existence of the message to prove that
        st' is smaller than st and thus, st ∐ st' = st. *)
      iAssert
        (OwnLockInv
          repId (h__own ∪ st'_h__local) (h__foreign ∪ st'_h__foreign))
          with "[Hown_lock]" as "Hown_lock".
      { admit. }
      (** Update of the resources: end. *)
      wp_apply (release_spec with "[$His_lock $Hlocked Hloc Hown_lock]").
      { iExists ip, st'', st''_log,
          (h__own ∪ st'_h__local), (h__foreign ∪ st'_h__foreign).
        iFrame "Hown_lock".
        rewrite Hip_eq. iFrame "Hloc".
        iFrame "%".
        iPureIntro.
        assert (
          h__own ∪ st'_h__local ∪ (h__foreign ∪ st'_h__foreign)
            = h__own ∪ h__foreign ∪ (st'_h__local ∪ st'_h__foreign))
          as ->;
          [ set_solver | assumption ]. }
      iIntros (v ->).
      by iApply "Hφ".
  Admitted.



  (**       +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+
            | Speficication of [statelib_init] |
            +~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~+              **)
  (** Not proven yet. *)


End StateLib_Proof.

