From iris.algebra Require Import auth gmap excl csum.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import list_proof lock_proof vector_clock_proof serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.crdt.spec Require Import crdt_spec.
From aneris.examples.crdt.statelib.user_model
  Require Import model semi_join_lattices.
From aneris.examples.crdt.statelib.proof Require Import events.
From aneris.examples.crdt.statelib.user_model Require Import params.
From aneris.examples.crdt.statelib.proof Require Import utils.

(** * Specification of the op-based CRDT library *)


Section Specification.

  (* The following resources are all needed to _state_ the specifications of library
     functions, but they should _not_ all be provided by the user of the library
     (e.g. the user provides StLib_UserParams, but not StLib_SysParams).

     To use the library, the user should refer to class StLibSetup below.
   *)
  Context `{!anerisG Mdl Σ,
            !EqDecision LogOp,
            !Countable LogOp,
            !Lattice LogSt,
            !StLib_Params LogOp LogSt,
            !StLib_SysParams Σ,
            !CRDT_Params,
            !StLib_Res LogOp}.

  Definition get_state_spec (get_state : val) (repId : nat) (addr : socket_address) : iProp Σ :=
    ⌜CRDT_Addresses !! repId = Some addr⌝ -∗
     <<< ∀∀ (s1 s2 : gset (Event LogOp)), LocState repId s1 s2 >>>
       get_state #() @[ip_of_address addr] ↑CRDT_InvName
     <<<▷ ∃∃ (s2' : gset (Event LogOp)) (phys_st : val) (log_st : LogSt), RET phys_st;
             ⌜s2 ⊆ s2'⌝ ∗
             LocState repId s1 s2' ∗
             ⌜StLib_St_Coh log_st phys_st⌝ ∗
             ⌜⟦s1 ∪ s2'⟧ ⇝ log_st⌝ >>>.

  Definition update_spec (update : val) (repId : nat) (addr : socket_address) : iProp Σ :=
    ∀ (op : val) (log_op : LogOp),
    ⌜CRDT_Addresses !! repId = Some addr⌝ -∗
    ⌜StLib_Op_Coh log_op op⌝ -∗
    <<< ∀∀ (h s1 s2 : gset (Event LogOp)),
           GlobState h ∗
           LocState repId s1 s2 >>>
      update op @[ip_of_address addr] ↑CRDT_InvName
    <<<▷ ∃∃ (e : Event LogOp) (h' s1' s2' : event_set LogOp), RET #();
           ⌜e.(EV_Op) = log_op⌝ ∗
           ⌜e.(EV_Orig) = repId⌝ ∗
           ⌜h' = h ∪ {[ e ]}⌝ ∗
           ⌜s1' = s1 ∪ {[ e ]}⌝ ∗
           ⌜s2 ⊆ s2'⌝ ∗
           ⌜e ∉ h⌝ ∗
           ⌜e ∉ s1⌝ ∗
           ⌜e ∈ Maximals h'⌝ ∗
           ⌜Maximum (s1' ∪ s2') = Some e⌝ ∗
           GlobState h' ∗
           LocState repId s1' s2' >>>.

  Definition mutator_spec (mutator_fn : val) : iProp Σ :=
    ∀ (addr : socket_address) (repId: RepId) (st op : val) (s : (event_set LogOp))
      (log_ev : Event LogOp) (log_op: LogOp) (log_st : LogSt),
    {{{ ⌜StLib_Op_Coh log_op op⌝ ∗
        ⌜StLib_St_Coh log_st st⌝ ∗
        ⌜⟦ s ⟧ ⇝ log_st⌝ ∗
        ⌜log_ev ∉ s⌝ ∗
        ⌜maximal log_ev (s ∪ {[ log_ev ]})⌝ ∗
        ⌜events_ext (s ∪ {[ log_ev ]})⌝ ∗
        ⌜event_set_same_orig_comparable (s ∪ {[ log_ev ]})⌝
    }}}
      mutator_fn #repId st op @[ip_of_address addr]
    {{{ st', RET st';
        ∃ (log_st' : LogSt),
          ⌜StLib_St_Coh log_st' st'⌝ ∗
          ⌜st_crdtM_mut log_st log_ev log_st'⌝
    }}}.

  Definition merge_spec (merge_fn : val) : iProp Σ :=
    ∀ (addr : socket_address) (st st' : val) (s s' : (event_set LogOp))
      (log_st log_st' : LogSt),
    {{{ ⌜StLib_St_Coh log_st st⌝ ∗
        ⌜StLib_St_Coh log_st' st'⌝ ∗
        ⌜⟦ s ⟧ ⇝ log_st⌝ ∗
        ⌜⟦ s' ⟧ ⇝ log_st'⌝ ∗
        ⌜events_ext s⌝ ∗
        ⌜event_set_same_orig_comparable s⌝ ∗
        ⌜events_ext s'⌝ ∗
        ⌜event_set_same_orig_comparable s'⌝
    }}}
      merge_fn st st' @[ip_of_address addr]
    {{{ st'', RET st'';
        ∃ (log_st'' : LogSt),
          ⌜StLib_St_Coh log_st'' st''⌝ ∗
          ⌜lat_lub log_st log_st' = log_st''⌝
    }}}.

  Definition init_st_fn_spec (init_st_fun : val) : iProp Σ :=
    ∀ addr,
      {{{ True }}}
        init_st_fun #() @[ip_of_address addr]
      {{{ v, RET v; ⌜StLib_St_Coh st_crdtM_init_st v⌝ }}}.

  Definition crdt_triplet_spec (crdt_triplet : val) : iProp Σ :=
    ∃ (init_st_fn mutator_fn merge_fn : val),
      ⌜crdt_triplet = PairV (PairV init_st_fn mutator_fn) merge_fn⌝ ∗
      init_st_fn_spec init_st_fn  ∗
      mutator_spec mutator_fn ∗
      merge_spec merge_fn.

  Definition crdt_fun_spec (crdt_fun : val) : iProp Σ :=
    ∀ addr,
      {{{ True }}}
        crdt_fun #() @[ip_of_address addr]
      {{{ v, RET v; crdt_triplet_spec v }}}.

    (** TODO: discuss the differences. 
    Definition init_spec (init : val) : iProp Σ :=
    ∀ (repId : nat) (addr : socket_address) (fixedAddrs : gset socket_address)
      (addrs_val crdt_val : val) (f: (repId < length CRDT_Addresses)%nat),
        {{{ ⌜is_list CRDT_Addresses addrs_val⌝ ∗
            ⌜CRDT_Addresses !! repId = Some addr⌝ ∗
            ⌜addr ∈ fixedAddrs⌝ ∗
            fixed fixedAddrs ∗
            ([∗ list] i ↦ z ∈ CRDT_Addresses, z ⤇ StLib_SocketProto) ∗
            addr ⤳ (∅, ∅) ∗
            free_ports (ip_of_address addr) {[port_of_address addr]} ∗
            StLib_InitToken (nat_to_fin f) ∗
            crdt_fun_spec crdt_val
        }}}
          init addrs_val #repId crdt_val @[ip_of_address addr]
        {{{ get_state_val mutator_val, RET (get_state_val, mutator_val);
            LocState repId ∅ ∅ ∗
            get_state_spec get_state_val repId addr ∗
            update_spec mutator_val repId addr
        }}}. *)

  Definition init_spec (init: val) : iProp Σ :=
    ∀ (repId : (fin(length CRDT_Addresses))) (addr : socket_address)
      (fixedAddrs : gset socket_address) (addrs_val crdt_val : val),
    {{{ ⌜is_list CRDT_Addresses addrs_val⌝ ∗
        ⌜CRDT_Addresses !! (fin_to_nat repId) = Some addr⌝ ∗
        ⌜addr ∈ fixedAddrs⌝ ∗
        fixed fixedAddrs ∗
        ([∗ list] z ∈ CRDT_Addresses, z ⤇ StLib_SocketProto) ∗
        addr ⤳ (∅, ∅) ∗
        free_ports (ip_of_address addr) {[port_of_address addr]} ∗
        StLib_InitToken repId ∗
        crdt_fun_spec crdt_val
    }}}
      init addrs_val #repId crdt_val @[ip_of_address addr]
    {{{ gs_val upd_val, RET (gs_val, upd_val);
        LocState repId ∅ ∅ ∗
        get_state_spec gs_val repId addr ∗
        update_spec upd_val repId addr
    }}}.

End Specification.

(** * Library interface **)
Section StLibSetup.

  Class StLib_Init_Function := { init : val }.

  Context `{LogOp: Type, LogSt : Type,
            !anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !Lattice LogSt, !StLib_Params LogOp LogSt, !StLib_Init_Function}.

  Class StLibSetup :=
      StLibSetup_Init E :
      True ⊢ |={E}=> ∃ (Res : StLib_Res LogOp),
        GlobInv ∗
        GlobState ∅ ∗
        (∃ (S: gset (fin (length CRDT_Addresses))),
          (∀ i, ⌜i ∈ S⌝) ∗
          [∗ set] i ∈ S, StLib_InitToken i) ∗
        init_spec init.

End StLibSetup.

Section RAs.

  Context `{LogOp: Type, LogSt : Type,
            !EqDecision LogOp, !Countable LogOp}.

  Definition oneShotR := csumR (exclR unitO) (agreeR unitO).

  Class StLibG Σ := {
      StLibG_auth_gset_ev :> inG Σ (authUR (gsetUR (Event LogOp)));
      StLibG_frac_agree :> inG Σ (prodR fracR (agreeR (gsetO (Event LogOp))));
      StLibG_mono :> inG Σ (authUR (monotoneUR (@cc_subseteq LogOp _ _)));
      StLibG_lockG :> lockG Σ;
      StLibG_oneshot :> inG Σ oneShotR;
  }.

  Definition OPLIBΣ  : gFunctors :=
    #[GFunctor (authUR (gsetUR (Event LogOp)));
      GFunctor (prodR fracR (agreeR (gsetO (Event LogOp))));
      GFunctor (authUR (monotoneUR (@cc_subseteq LogOp _ _)));
      lockΣ;
      GFunctor oneShotR].

  Global Instance subG_OPLIBΣ {Σ} : subG OPLIBΣ Σ → StLibG Σ.
  Proof. constructor; solve_inG. Qed.

End RAs.

