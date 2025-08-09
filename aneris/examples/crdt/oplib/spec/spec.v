From iris.algebra Require Import auth gmap excl csum.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import network resources proofmode.
From aneris.prelude Require Import time.
From aneris.aneris_lang.lib Require Import list_proof lock_proof vector_clock_proof serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.crdt.spec Require Import crdt_spec.
From aneris.examples.crdt.oplib.spec Require Import model events.

(** * Specification of the op-based CRDT library *)

Section Params.
  Context {LogOp LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp}.

  (* User-supplied parameters when using the library. *)
  Class OpLib_Params := {
    (* Serialization of operations. *)
    OpLib_Serialization : serialization;

    (* CRDT model *)
    OpLib_Denot :> CrdtDenot LogOp LogSt;
    OpLib_Model :> OpCrdtModel LogOp LogSt;

    (* Coherence between logical and physical state: for
       states, operations, and events (event = operation + timestamp).

       For example, for a counter CRDT the logical state is
       (morally) an integer, while the physical state is an
       AnerisLang `val` (containing the integer).
       The correspondence is trivial in that case, but can
       be more complicated for other CRDTs. *)
    OpLib_State_Coh : LogSt -> val -> Prop;
    OpLib_Op_Coh : LogOp -> val -> Prop;
    OpLib_Op_Coh_Inj o1 o2 v : OpLib_Op_Coh o1 v -> OpLib_Op_Coh o2 v -> o1 = o2;
    OpLib_Coh_Ser op v : OpLib_Op_Coh op v -> Serializable OpLib_Serialization v;
  }.

  Definition OpLib_Event_Coh `{!OpLib_Params} (e : Event LogOp) (v : val) : Prop :=
    ∃ valOp valVC valOrig,
      v = ((valOp, valVC), valOrig)%V ∧
      OpLib_Op_Coh e.(EV_Op) valOp ∧
      is_vc valVC (time e) ∧
      valOrig = #(e.(EV_Orig)).

  Class OpLib_Res `{!CRDT_Params} := {
    OpLib_CRDT_Res :> CRDT_Res_Mixin Mdl Σ LogOp;
    OpLib_InitToken : nat -> iProp Σ;
    OpLib_SocketProto : nat -> socket_interp Σ;
  }.

End Params.

Global Arguments OpLib_Params (LogOp LogSt) {_ _}.
Global Arguments OpLib_Res (LogOp) {_ _ _ _ _ _}.

Section Specification.

  (* The following resources are all needed to _state_ the specifications of library
     functions, but they should _not_ all be provided by the user of the library
     (e.g. the user provides OpLib_UserParams, but not OpLib_SysParams).

     To use the library, the user should refer to class OpLibSetup below.
   *)
  Context `{!anerisG Mdl Σ,
            !EqDecision LogOp,
            !Countable LogOp,
            !OpLib_Params LogOp LogSt,
            !OpLib_SysParams Σ,
            !CRDT_Params,
            !OpLib_Res LogOp}.

  Definition get_state_spec (get_state : val) (repId : nat) (addr : socket_address) : iProp Σ :=
    ⌜CRDT_Addresses !! repId = Some addr⌝ -∗
     <<< ∀∀ (s1 s2 : gset (Event LogOp)), LocState repId s1 s2 >>>
       get_state #() @[ip_of_address addr] ↑CRDT_InvName
     <<<▷ ∃∃ (s2' : gset (Event LogOp)) (phys_st : val) (log_st : LogSt), RET phys_st;
             ⌜s2 ⊆ s2'⌝ ∗
             LocState repId s1 s2' ∗
             ⌜OpLib_State_Coh log_st phys_st⌝ ∗
             ⌜⟦s1 ∪ s2'⟧ ⇝ log_st⌝ >>>.

  Definition update_spec (update : val) (repId : nat) (addr : socket_address) : iProp Σ :=
    ∀ (op : val) (log_op : LogOp),
    ⌜CRDT_Addresses !! repId = Some addr⌝ -∗
    ⌜OpLib_Op_Coh log_op op⌝ -∗
    <<< ∀∀ (h s1 s2 : gset (Event LogOp)),
           GlobState h ∗
           LocState repId s1 s2 >>>
      update op @[ip_of_address addr] ↑CRDT_InvName
    <<<▷ ∃∃ (e : Event LogOp) (h' s1' s2' : gset (Event LogOp)), RET #();
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

  Definition effect_spec (effect_fn : val) : iProp Σ :=
    ∀ (addr : socket_address) (ev st : val) (s : (event_set LogOp))
      (log_ev : Event LogOp) (log_st : LogSt),
    {{{ ⌜OpLib_Event_Coh log_ev ev⌝ ∗
        ⌜OpLib_State_Coh log_st st⌝ ∗
        ⌜⟦ s ⟧ ⇝ log_st⌝ ∗
        ⌜log_ev ∉ s⌝ ∗
        ⌜maximal log_ev (s ∪ {[ log_ev ]})⌝ ∗
        ⌜events_ext (s ∪ {[ log_ev ]})⌝ ∗
        ⌜events_total_order (s ∪ {[ log_ev ]})⌝
    }}}
      effect_fn ev st @[ip_of_address addr]
    {{{ st', RET st';
        ∃ (log_st' : LogSt),
          ⌜OpLib_State_Coh log_st' st'⌝ ∗
          ⌜log_st -{log_ev}-> log_st'⌝
    }}}.

  Definition init_st_fn_spec (init_st_fun : val) : iProp Σ :=
    ∀ addr,
      {{{ True }}}
        init_st_fun #() @[ip_of_address addr]
      {{{ v, RET v; ⌜OpLib_State_Coh op_crdtM_init_st v⌝ }}}.

  Definition crdt_pair_spec (crdt_pair : val) : iProp Σ :=
    ∃ (init_st_fn effect_fn : val),
      ⌜crdt_pair = PairV init_st_fn effect_fn⌝ ∗
      init_st_fn_spec init_st_fn  ∗
      effect_spec effect_fn.

  Definition crdt_fun_spec (crdt_fun : val) : iProp Σ :=
    ∀ addr,
      {{{ True }}}
        crdt_fun #() @[ip_of_address addr]
      {{{ v, RET v; crdt_pair_spec v }}}.

  Definition init_spec_for_specific_crdt (init : val)  : iProp Σ :=
    ∀ (repId : nat) (addr : socket_address)
      (addrs_val : val),
        {{{ ⌜is_list CRDT_Addresses addrs_val⌝ ∗
            ⌜CRDT_Addresses !! repId = Some addr⌝ ∗
            ([∗ list] i ↦ z ∈ CRDT_Addresses, z ⤇ OpLib_SocketProto i) ∗
            addr ⤳ (∅, ∅) ∗
            free_ports (ip_of_address addr) {[port_of_address addr]} ∗
            OpLib_InitToken repId
        }}}
          init addrs_val #repId @[ip_of_address addr]
        {{{ get_state_val update_val, RET (get_state_val, update_val);
            LocState repId ∅ ∅ ∗
            get_state_spec get_state_val repId addr ∗
            update_spec update_val repId addr
        }}}.

    Definition init_spec (init : val) : iProp Σ :=
    ∀ (repId : nat) (addr : socket_address)
      (addrs_val crdt_val : val),
        {{{ ⌜is_list CRDT_Addresses addrs_val⌝ ∗
            ⌜CRDT_Addresses !! repId = Some addr⌝ ∗
            ([∗ list] i ↦ z ∈ CRDT_Addresses, z ⤇ OpLib_SocketProto i) ∗
            addr ⤳ (∅, ∅) ∗
            free_ports (ip_of_address addr) {[port_of_address addr]} ∗
            OpLib_InitToken repId ∗
            crdt_fun_spec crdt_val
        }}}
          init addrs_val #repId crdt_val @[ip_of_address addr]
        {{{ get_state_val update_val, RET (get_state_val, update_val);
            LocState repId ∅ ∅ ∗
            get_state_spec get_state_val repId addr ∗
            update_spec update_val repId addr
        }}}.

  (** * Simplified specs for when we have full ownership *)

  Definition simplified_get_state_spec (get_state : val) (repId : nat) (addr : socket_address) : iProp Σ :=
    ∀ (s1 s2 : event_set LogOp),
      ⌜CRDT_Addresses !! repId = Some addr⌝ -∗
      {{{ LocState repId s1 s2 }}}
        get_state #() @[ip_of_address addr]
      {{{ phys_st log_st, RET phys_st; ∃ s2',
          ⌜s2 ⊆ s2'⌝ ∗
          LocState repId s1 s2' ∗
          ⌜OpLib_State_Coh log_st phys_st⌝ ∗
          ⌜⟦ s1 ∪ s2' ⟧ ⇝ log_st⌝
      }}}.

  Lemma read_spec_implies_simplified_spec get_state repId addr :
    get_state_spec get_state repId addr ⊢ simplified_get_state_spec get_state repId addr.
  Proof.
    iIntros "#Hgetstate".
    rewrite /simplified_get_state_spec.
    iIntros (s1 s2) "#Haddr !>". iIntros (Φ) "Hloc HΦ".
    iApply ("Hgetstate" with "[//]").
    iExists s1, s2; iFrame.
    iApply fupd_mask_intro; [set_solver |].
    iNext.
    iIntros "Hcl ".
    iIntros (? ? ?) "(? & ? & ?)". iMod "Hcl". iModIntro.
    iApply "HΦ".
    eauto with iFrame.
  Qed.

  Definition simplified_update_spec (update : val) repId addr : iProp Σ :=
    ∀ (op : val) (log_op : LogOp) (h s1 s2 : event_set LogOp),
     ⌜CRDT_Addresses !! repId = Some addr⌝ -∗
     ⌜OpLib_Op_Coh log_op op⌝ -∗
     {{{ GlobState h ∗
         LocState repId s1 s2
     }}}
        update op @[ip_of_address addr]
     {{{ RET #();
         ∃ (e : Event LogOp) (h' s1' s2' : gset (Event LogOp)),
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
           LocState repId s1' s2' }}}.

  Lemma update_spec_implies_simplified_update update repId addr :
    update_spec update repId addr ⊢ simplified_update_spec update repId addr.
  Proof.
    iIntros "#Hupdate" (op log_op h s1 s2) "#Haddr %Hcoh".
    iModIntro.
    iIntros (Φ) "[Hglob Hloc] HΦ".
    iApply ("Hupdate" with "[//]"); [done |].
    iApply fupd_mask_intro; [set_solver |].
    iIntros "!> Hcl". iExists h, s1, s2. iFrame.
    iIntros (e h' s1' s2') "(? & ? & ? & ? & ? & ? & ? & ? & ?)".
    iMod "Hcl". iModIntro.
    iApply "HΦ". eauto with iFrame.
  Qed.

End Specification.

(** * Library interface **)
Section OpLibSetup.

  Class OpLib_Init_Function := { init : val }.

  Context {LogOp LogSt : Type}.
  Context `{!anerisG Mdl Σ, !EqDecision LogOp, !Countable LogOp,
            !CRDT_Params, !OpLib_Params LogOp LogSt, !OpLib_Init_Function}.

  Class OpLibSetup :=
      OpLibSetup_Init E :
      True ⊢ |={E}=> ∃ (Res : OpLib_Res LogOp),
        GlobInv ∗
        GlobState ∅ ∗
        ([∗ list] i ↦ _ ∈ CRDT_Addresses, OpLib_InitToken i) ∗
        init_spec init.

End OpLibSetup.

Section RAs.

  Context {LogOp LogSt : Type}.
  Context `{!EqDecision LogOp, !Countable LogOp}.

  Definition oneShotR := csumR (exclR unitO) (agreeR unitO).

  Class OpLibG Σ := {
      OpLibG_auth_gset_ev :> inG Σ (authUR (gsetUR (Event LogOp)));
      OpLibG_frac_agree :> inG Σ (prodR fracR (agreeR (gsetO (Event LogOp))));
      OpLibG_mono :> inG Σ (authUR (monotoneUR (@cc_subseteq LogOp _ _)));
      OpLibG_lockG :> lockG Σ;
      OpLibG_oneshot :> inG Σ oneShotR;
  }.

  Definition OPLIBΣ  : gFunctors :=
    #[GFunctor (authUR (gsetUR (Event LogOp)));
      GFunctor (prodR fracR (agreeR (gsetO (Event LogOp))));
      GFunctor (authUR (monotoneUR (@cc_subseteq LogOp _ _)));
      lockΣ;
      GFunctor oneShotR].

  Global Instance subG_OPLIBΣ {Σ} : subG OPLIBΣ Σ → OpLibG Σ.
  Proof. constructor; solve_inG. Qed.

End RAs.
