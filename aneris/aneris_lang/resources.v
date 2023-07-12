From stdpp Require Import fin_maps gmap.
From iris.algebra Require Import auth gmap frac agree coPset
     gset frac_auth ofe excl.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import saved_prop invariants mono_nat.
From iris.proofmode Require Import tactics.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang Require Export aneris_lang network.
From aneris.algebra Require Import disj_gsets.
From trillium.events Require Import event.
From aneris.aneris_lang Require Import events.
From aneris.prelude Require Import gset_map.
From aneris.lib Require Export singletons.

Set Default Proof Using "Type".

Import uPred.
Import ast.

Record Model :=
  model {
      model_state :> Type;
      model_rel :> model_state → model_state → Prop;
      model_state_initial : model_state;
    }.

Definition aneris_to_trace_model (M: Model): traces.Model := {|
  mstate := model_state M;
  mlabel := unit;
  mtrans x _ y := model_rel M x y;
|}.
  
Record node_gnames := Node_gname {
  heap_name : gname;
  sockets_name : gname;
}.

Definition socket_address_group := gset socket_address.
Definition socket_address_groupO := gsetO socket_address.

Definition node_gnamesO :=
  leibnizO node_gnames.
Definition node_gnames_mapUR : ucmra :=
  gmapUR ip_address (agreeR node_gnamesO).
Definition local_heapUR : ucmra :=
  gen_heapUR loc val.
Definition local_socketsUR : ucmra := gen_heapUR socket_handle socket.
Definition free_ipsUR : ucmra :=
  (gset_disjUR ip_address).
Definition free_portsUR : ucmra :=
  gmapUR ip_address (gset_disjUR port).
Definition socket_interpUR : ucmra :=
  gmapUR socket_address_group (agreeR (leibnizO gname)).
Definition socket_address_groupUR : ucmra :=
  (disj_gsetsUR socket_address).
Definition unallocated_socket_address_groupsUR : ucmra :=
  authUR (gset_disjUR socket_address_group).
Definition tracked_socket_address_groupsUR : cmra :=
  agreeR (gsetUR socket_address_group).
Definition messagesUR : ucmra :=
  gen_heapUR socket_address_group (message_soup * message_soup).

#[global] Instance system_state_mapUR_unit : Unit (gmap ip_address (agree node_gnames))
  := (∅ : gmap ip_address (agree node_gnames)).
#[global] Instance system_state_core_id (x : node_gnames_mapUR) : CoreId x.
Proof. apply _. Qed.

Definition socket_interp Σ := message -d> iPropO Σ.

Canonical Structure ModelO (Mdl : Model) := leibnizO Mdl.

Canonical Structure socket_addressO := leibnizO socket_address.

Definition aneris_events := event_obs aneris_lang.

Canonical Structure aneris_eventsO := leibnizO aneris_events.

(** The system CMRA *)
Class anerisG (Mdl : Model) Σ :=
  AnerisG {
      aneris_invG :> invGS_gen HasNoLc Σ;
      (** global tracking of the ghost names of node-local heaps *)
      aneris_node_gnames_mapG :> inG Σ (authR node_gnames_mapUR);
      aneris_node_gnames_name : gname;
      (** local heap *)
      aneris_heapG :> inG Σ (authR local_heapUR);
      (** local sockets *)
      aneris_socketG :> inG Σ (authR local_socketsUR);
      (** free ips *)
      aneris_freeipsG :> inG Σ (authUR free_ipsUR);
      aneris_freeips_name : gname;
      (** free ports  *)
      aneris_freeportsG :> inG Σ (authUR free_portsUR);
      aneris_freeports_name : gname;
      (** groups *)
      aneris_socket_address_groupG :> inG Σ (authR socket_address_groupUR);
      aneris_socket_address_group_name : gname;
      (** socket interpretations *)
      aneris_siG :> inG Σ (authR socket_interpUR);
      aneris_savedPredG :> savedPredG Σ message;
      aneris_si_name : gname;
      (** socket address groups with unallocated socket interpretations *)
      aneris_unallocated_socket_address_groupsG :>
        inG Σ (unallocated_socket_address_groupsUR);
      aneris_unallocated_socket_address_groups_name : gname;
      (** socket address groups for which we track events *)
      aneris_tracked_socket_address_groupsG :>
        inG Σ (tracked_socket_address_groupsUR);
      (** message history *)
      aneris_messagesG :> inG Σ (authR messagesUR);
      aneris_messages_name : gname;
      (** model *)
      aneris_model_name : gname;
      anerisG_model :> inG Σ (authUR (optionUR (exclR (ModelO Mdl))));
      (** steps *)
      aneris_steps_name : gname;
      anerisG_steps :> mono_natG Σ;
      (** events *)
      anerisG_allocEVS :> inG Σ (authUR (gmapUR string (exclR aneris_eventsO)));
      anerisG_sendreceiveEVS :>
        inG Σ (authUR (gmapUR socket_address_group (exclR aneris_eventsO)));
      aneris_allocEVS_name : gname;
      aneris_sendonEVS_name : gname;
      aneris_receiveonEVS_name : gname;
      aneris_observed_send_name : gname;
      aneris_observed_recv_name : gname;
    }.

Class anerisPreG Σ (Mdl : Model) :=
  AnerisPreG {
      anerisPre_invGS :> invGpreS Σ;
      anerisPre_node_gnames_mapG :> inG Σ (authR node_gnames_mapUR);
      anerisPre_heapG :> inG Σ (authR local_heapUR);
      anerisPre_socketG :> inG Σ (authR local_socketsUR);
      anerisPre_freeipsG :> inG Σ (authUR free_ipsUR);
      anerisPre_freeportsG :> inG Σ (authUR free_portsUR);
      anerisPre_socket_address_groupG :> inG Σ (authR socket_address_groupUR);
      anerisPre_siG :> inG Σ (authR socket_interpUR);
      anerisPre_savedPredG :> savedPredG Σ message;
      anerisPre_unallocated_socket_address_groupsG :>
        inG Σ (unallocated_socket_address_groupsUR);
      anerisPre_tracked_socket_address_groupsG :>
        inG Σ (tracked_socket_address_groupsUR);
      anerisPre_messagesG :> inG Σ (authR messagesUR);
      anerisPre_model :> inG Σ (authUR (optionUR (exclR (ModelO Mdl))));
      anerisPre_steps :> mono_natG Σ;
      anerisPre_allocEVSG :>
        inG Σ (authUR (gmapUR string (exclR aneris_eventsO)));
      anerisPre_sendreceiveEVSG :>
        inG Σ (authUR (gmapUR socket_address_group (exclR aneris_eventsO)));
    }.

Definition anerisΣ (Mdl : Model) : gFunctors :=
  #[invΣ;
   GFunctor (authR node_gnames_mapUR);
   GFunctor (authR local_heapUR);
   GFunctor (authR local_socketsUR);
   GFunctor (authUR free_ipsUR);
   GFunctor (authUR free_portsUR);
   GFunctor (authUR socket_address_groupUR);
   GFunctor (authR socket_interpUR);
   savedPredΣ message;
   GFunctor (unallocated_socket_address_groupsUR);
   GFunctor (tracked_socket_address_groupsUR);
   GFunctor (authR messagesUR);
   GFunctor (authUR (optionUR (exclR (ModelO Mdl))));
   mono_natΣ;
   GFunctor (authUR (gmapUR string (exclR aneris_eventsO)));
   GFunctor (authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
   ].

#[global] Instance subG_anerisPreG {Σ Mdl} :
  subG (anerisΣ Mdl) Σ → anerisPreG Σ Mdl.
Proof. solve_inG. Qed.

Section definitions.
  Context `{aG : !anerisG Mdl Σ}.

  Definition auth_st (st : Mdl) : iProp Σ :=
    own aneris_model_name (● Excl' st) ∗ ⌜rtc Mdl Mdl.(model_state_initial) st⌝.
  Definition frag_st (st : Mdl) : iProp Σ :=
    own aneris_model_name (◯ Excl' st) ∗ ⌜rtc Mdl Mdl.(model_state_initial) st⌝.

  (** Authoritative view of the system ghost names *)
  Definition node_gnames_auth (m : gmap ip_address node_gnames) :=
    own (A := authR node_gnames_mapUR)
        aneris_node_gnames_name (● (to_agree <$> m)).

  (** Fragmental view of the system ghost names. *)
  Definition mapsto_node_def (ip : ip_address) (γn : node_gnames) :=
    own (aneris_node_gnames_name) (◯ {[ ip := to_agree γn ]}).
  Definition mapsto_node_aux : seal (@mapsto_node_def). by eexists. Qed.
  Definition mapsto_node := unseal mapsto_node_aux.
  Definition mapsto_node_eq : @mapsto_node = @mapsto_node_def :=
    seal_eq mapsto_node_aux.

  Definition is_node (ip : ip_address) : iProp Σ := ∃ γn, mapsto_node ip γn.

  (** Local heap *)
  Definition heap_ctx (γn : node_gnames) (h : gmap loc val) : iProp Σ :=
    gen_heap_light_ctx (heap_name γn) h.

  Definition mapsto_heap (ip : ip_address)
             (l : loc) (q : Qp) (v : val) : iProp Σ :=
    (∃ γn, mapsto_node ip γn ∗ lmapsto (heap_name γn) l q v)%I.

  (** Local sockets *)
  Definition sockets_ctx (γn : node_gnames)
             (s : gmap socket_handle socket) : iProp Σ :=
    gen_heap_light_ctx (sockets_name γn) s.

  Definition mapsto_socket (ip : ip_address) (z : socket_handle)
             (q : Qp) (s: socket) : iProp Σ :=
    (∃ γn, mapsto_node ip γn ∗ lmapsto (sockets_name γn) z q s)%I.

  (** Free ip addresses *)
  Definition free_ips_auth (A : gset ip_address) : iProp Σ :=
    own aneris_freeips_name (● GSet A).

  Definition free_ip (ip : ip_address) : iProp Σ :=
    own aneris_freeips_name (◯ GSet {[ ip ]}).

  (** Free ports *)
  Definition free_ports_auth (P : gmap ip_address (gset_disjUR port)) : iProp Σ :=
    own aneris_freeports_name (● P).

  Definition free_ports (ip : ip_address) (ports : gset port) : iProp Σ :=
    own aneris_freeports_name (◯ ({[ ip := (GSet ports)]})).

  Definition socket_address_groups_own (sags : gset socket_address_group)
    : iProp Σ :=
    own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
        (◯ (DGSets sags)).

  Definition socket_address_group_ctx
             (sags : gset socket_address_group) : iProp Σ :=
    ⌜set_Forall is_ne sags⌝ ∗
    own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
        (● (DGSets sags)) ∗
    own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
        (◯ (DGSets sags)).

  Definition socket_address_group_own (sag : socket_address_group) : iProp Σ :=
    own (A:=authUR socket_address_groupUR) aneris_socket_address_group_name
        (◯ (DGSets {[sag]})).  

  (** Ghost names of saved socket interpretations *)
  Definition saved_si_auth
             (sis : gmap socket_address_group gname) : iProp Σ :=
    own (A:=(authR socket_interpUR)) aneris_si_name (● (to_agree <$> sis)).

  Definition saved_si (sag : socket_address_group) (γ : gname) : iProp Σ :=
    own aneris_si_name (◯ {[ sag := to_agree γ ]}).

  (** Socket interpretation [Φ] of group [sag] *)
  Definition si_pred (sag : socket_address_group)
             (Φ : socket_interp Σ) : iProp Σ :=
    ∃ γ, socket_address_group_own sag ∗ saved_si sag γ ∗
         saved_pred_own γ (DfracDiscarded) Φ.

  (** The set [A] of addresses with unallocated socket interpretations *)
  Definition unallocated_groups_auth (A : gset socket_address_group) : iProp Σ :=
    own aneris_unallocated_socket_address_groups_name
        (auth_auth (DfracOwn 1) (GSet A)).

  Definition unallocated_groups (A : gset socket_address_group) : iProp Σ :=
    own aneris_unallocated_socket_address_groups_name
        (auth_frag (GSet A)).

  Definition unallocated (A : gset socket_address) : iProp Σ :=
    unallocated_groups (to_singletons A).

  (** The set [A] of addresses for which we track send events. *)
  Definition observed_send_groups (A : gset socket_address_group) : iProp Σ :=
    own aneris_observed_send_name (to_agree A).

  (** The set [A] of addresses for which we track receive events. *)
  Definition observed_receive_groups (A : gset socket_address_group) : iProp Σ :=
    own aneris_observed_recv_name (to_agree A).

  (** The set [A] of addresses for which we track send events. *)
  Definition observed_send (A : gset socket_address) : iProp Σ :=
    observed_send_groups (to_singletons A).

  (** The set [A] of addresses for which we track receive events. *)
  Definition observed_receive (A : gset socket_address) : iProp Σ :=
    observed_receive_groups (to_singletons A).

  Definition alloc_evs_ctx (M : gmap string aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR string (exclR aneris_eventsO)))
        aneris_allocEVS_name (● (Excl <$> M)).

  Definition alloc_evs (lbl : string) (evs : aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR string (exclR aneris_eventsO)))
        aneris_allocEVS_name (◯ {[ lbl := Excl evs]}).

  Definition sendon_evs_ctx
             (M : gmap socket_address_group aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
        aneris_sendonEVS_name (● (Excl <$> M)).

  Definition sendon_evs_groups (sag : socket_address_group)
             (evs : aneris_events) : iProp Σ :=
    socket_address_group_own sag ∗
    own (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
        aneris_sendonEVS_name (◯ {[ sag := Excl evs]}).

  Definition sendon_evs (sa : socket_address) (evs : aneris_events) : iProp Σ :=
    sendon_evs_groups {[sa]} evs.

  Definition receiveon_evs_ctx
             (M : gmap socket_address_group aneris_events) : iProp Σ :=
    own (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
        aneris_receiveonEVS_name (● (Excl <$> M)).

  Definition receiveon_evs_groups (sag : socket_address_group)
             (evs : aneris_events) : iProp Σ :=
    socket_address_group_own sag ∗
    own (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
        aneris_receiveonEVS_name (◯ {[ sag := Excl evs]}).

  Definition receiveon_evs (sa : socket_address)
             (evs : aneris_events) : iProp Σ :=
    receiveon_evs_groups {[sa]} evs.

  (** Messages *)
  Definition messages_ctx
             (mh : gmap socket_address_group (message_soup * message_soup)) :=
    gen_heap_light_ctx (aneris_messages_name) mh.

  Definition message_group_equiv (sagT sagR : socket_address_group)
             (m1 m2 : message) :=
    m_sender m1 ∈ sagT ∧ m_sender m2 ∈ sagT ∧
    m_destination m1 ∈ sagR ∧ m_destination m2 ∈ sagR ∧
    m_body m1 = m_body m2.

  Notation "m1 ≡g{ sagT , sagR } m2" :=
    (message_group_equiv sagT sagR m1 m2) (at level 10).

  #[global] Instance message_group_equiv_dec sagT sagR m1 m2 :
    Decision (m1 ≡g{sagT, sagR} m2).
  Proof.
    rewrite /Decision.
    rewrite /message_group_equiv.
    destruct (decide (m_body m1 = m_body m2)); [| right; naive_solver ].
    destruct (decide (m_sender m1 ∈ sagT)); [| right; naive_solver ].
    destruct (decide (m_sender m2 ∈ sagT)); [| right; naive_solver ].
    destruct (decide (m_destination m1 ∈ sagR)); [| right; naive_solver ].
    destruct (decide (m_destination m2 ∈ sagR)); [by left | right; naive_solver ].
  Qed.

  Lemma set_Forall_Exists_message_group_equiv_dec sagT sagR m1
        (R : gset message) :
    { set_Forall (λ m2, ¬ (m1 ≡g{sagT,sagR} m2)) R} +
    { set_Exists (λ m2, m1 ≡g{sagT,sagR} m2) R}.
  Proof.
    apply set_Forall_Exists_dec.
    intros m.
    apply Sumbool.sumbool_not.
    apply message_group_equiv_dec.
  Qed.

  Lemma message_group_equiv_refl sagT sagR m :
    m_sender m ∈ sagT → m_destination m ∈ sagR → m ≡g{sagT, sagR} m.
  Proof. intros Hsend Hdest. done. Qed.

  Lemma message_group_equiv_symmetry sagT sagR m1 m2 :
    m_sender m1 ∈ sagT → m_destination m1 ∈ sagR →m1 ≡g{sagT, sagR} m2 →
    m2 ≡g{sagT, sagR} m1.
  Proof.
    rewrite /message_group_equiv.
    intros Hsend Hdest (HT1 & HT2 & HR1 & HR2 & <-).
    done.
  Qed.

  Lemma message_group_equiv_trans X sagT1 sagT2 sagR1 sagR2 m1 m2 m3 :
    all_disjoint X → sagT1 ∈ X → sagT2 ∈ X → sagR1 ∈ X → sagR2 ∈ X →
    m1 ≡g{sagT1,sagR1} m2 → m2 ≡g{sagT2,sagR2} m3 →
    sagT1 = sagT2 ∧ sagR1 = sagR2 ∧ m1 ≡g{sagT1,sagR1} m3.
  Proof.
    rewrite /message_group_equiv.
    intros Hdisj HsagT1 HsagT2 HsagR1 HsagR2.
    intros (HinT11 & HinT12 & HinR11 & HinR12 & <-).
    intros (HinT21 & HinT22 & HinR21 & HinR22 & <-).
    pose proof (elem_of_all_disjoint_eq sagT1 sagT2 _ X Hdisj HsagT1 HsagT2 HinT12 HinT21) as ->.
    pose proof (elem_of_all_disjoint_eq sagR1 sagR2 _ X Hdisj HsagR1 HsagR2 HinR12 HinR21) as ->.
    done.
  Qed.

  Lemma message_group_equiv_dest_eq X sagT1 sagT2 sagR1 sagR2 m1 m2 :
    all_disjoint X → sagT1 ∈ X → sagT2 ∈ X → sagR1 ∈ X → sagR2 ∈ X →
    m_sender m1 ∈ sagT1 →
    m_destination m1 ∈ sagR1 →
    m1 ≡g{sagT2, sagR2} m2 →
    sagT1 = sagT2 ∧ sagR1 = sagR2.
  Proof.
    intros Hdisj HsagT1 HsagT2 HsagR1 HsagR2 Hsend Hdest.
    intros (HinT1 & HinT2 & HinR1 & HinR2 & _).
    split; eapply elem_of_all_disjoint_eq; eauto.
  Qed.

  Lemma message_group_equiv_dest sagT sagR m1 m2 :
    m1 ≡g{sagT, sagR} m2 →
    m_sender m1 ∈ sagT ∧ m_sender m2 ∈ sagT ∧
    m_destination m1 ∈ sagR ∧ m_destination m2 ∈ sagR.
  Proof. by intros (Hsend1 & Hsend2 & Hdest1 & Hdest2 & _). Qed.

  Definition elem_of_group sa sag : iProp Σ :=
    ⌜sa ∈ sag⌝ ∗ socket_address_group_own sag.
  Definition not_elem_of_group sa sag : iProp Σ :=
    ⌜sa ∉ sag⌝ ∗ socket_address_group_own sag.

  Notation "sa ∈g sag" := (elem_of_group sa sag) (at level 10).
  Notation "sa ∉g sag" := (not_elem_of_group sa sag) (at level 10).

  Definition mapsto_messages (sag : socket_address_group) q
             (send_obs receive_obs : bool)
             (mh : message_soup * message_soup) : iProp Σ :=
    ∃ As Ar, observed_send_groups As ∗ observed_receive_groups Ar ∗
             (⌜(sag ∈ As ↔ (send_obs = true)) ∧ (sag ∈ Ar ↔ (receive_obs = true))⌝) ∗
             socket_address_group_own sag ∗
             lmapsto aneris_messages_name sag q mh.

  (** Steps *)
  Definition steps_auth n := mono_nat_auth_own aneris_steps_name 1 n.
  Definition steps_lb n := mono_nat_lb_own aneris_steps_name n.

End definitions.

(** Heap points-to (LaTeX: [\mapsto]) *)
Notation "l ↦[ ip ]{ q } v" :=
  (mapsto_heap ip l q v)
    (at level 20, q at level 50, format "l  ↦[ ip ]{ q }  v") : bi_scope.
Notation "l ↦[ ip ] v" :=
  (l ↦[ip]{1} v)%I (at level 20, format "l  ↦[ ip ]  v") : bi_scope.
Notation "l ↦[ ip ]{ q } -" :=
  (∃ v, l ↦[ip]{q} v)%I
    (at level 20, q at level 50, format "l  ↦[ ip ]{ q }  -") : bi_scope.

Notation "l ↦[ ip ] -" :=
  (l ↦[ip]{1} -)%I
    (at level 20, format "l  ↦[ ip ]  -") : bi_scope.

(** Socket points-to (LaTeX: [\hookrightarrow]) *)
Notation "z ↪[ ip ]{ q } s" :=
  (mapsto_socket ip z q s)
    (at level 20, q at level 50, format "z  ↪[ ip ]{ q }  s") : bi_scope.
Notation "z ↪[ ip ] s" := (z ↪[ ip ]{1} s)%I (at level 20) : bi_scope.

(** Messages points-to for groups *)
Notation "sag ⤳*{ q } s" :=
  (mapsto_messages sag q false false s)
    (at level 20, q at level 50, format "sag  ⤳*{ q }  s") : bi_scope.
Notation "sag ⤳* s" := (sag ⤳*{ 1 } s)%I (at level 20) : bi_scope.
Notation "sag ⤳*[ bs , br ]{ q } s" :=
  (mapsto_messages sag q bs br s)
    (at level 20, q at level 50, format "sag  ⤳*[ bs ,  br ]{ q }  s") : bi_scope.
Notation "sag ⤳*[ bs , br ] s" :=
  (sag ⤳*[bs,br]{ 1 } s)%I (at level 20) : bi_scope.

Notation "sag ⤇* Φ" := (si_pred sag Φ) (at level 20).

(** Singleton messages points-to *)
Notation "sa ⤳1{ q } s" :=
  ({[sa]} ⤳*{ q } s)%I
    (at level 20, q at level 50, format "sa  ⤳1{ q }  s") : bi_scope.
Notation "sa ⤳1 s" := (sa ⤳1{ 1 } s)%I (at level 20) : bi_scope.
Notation "sa ⤳1[ bs , br ]{ q } s" :=
  ({[sa]} ⤳*[ bs , br ]{ q } s)%I
    (at level 20, q at level 50, format "sa  ⤳1[ bs ,  br ]{ q }  s") : bi_scope.
Notation "sa ⤳1[ bs , br ] s" := (sa ⤳1[bs,br]{ 1 } s)%I (at level 20) : bi_scope.
Notation "sa ⤇1 Φ" := ({[sa]} ⤇* Φ) (at level 20).

Section singleton_to_singleton_connectives.
  Context `{anerisG Mdl Σ}.

  Definition message_history_singleton (sag : socket_address_group) q
             (send_obs receive_obs : bool) rt : iProp Σ :=
    sag ⤳*[send_obs, receive_obs]{q} (rt.1,rt.2) ∗
    ([∗ set] m ∈ rt.1, socket_address_group_own {[m_sender m]}).

  Definition from_singleton (φ : message → iProp Σ) : message → iProp Σ :=
    (λ m, socket_address_group_own {[m_sender m]} ∗ φ m)%I.

  Definition socket_interp_singleton (sag : socket_address_group) φ : iProp Σ :=
    sag ⤇* (from_singleton φ).

End singleton_to_singleton_connectives.

(* Singleton to singleton messages points-to *)
Notation "sa ⤳{ q } s" :=
  (message_history_singleton {[sa]} q false false s)%I
    (at level 20, q at level 50, format "sa  ⤳{ q }  s") : bi_scope.
Notation "sa ⤳ s" := (sa ⤳{ 1 } s)%I (at level 20) : bi_scope.
Notation "sa ⤳[ bs , br ]{ q } s" :=
  (message_history_singleton {[sa]} q bs br s)%I
    (at level 20, q at level 50, format "sa  ⤳[ bs ,  br ]{ q }  s") : bi_scope.
Notation "sa ⤳[ bs , br ] s" := (sa ⤳[bs,br]{ 1 } s)%I (at level 20) : bi_scope.
Notation "sa ⤇ Φ" := (socket_interp_singleton {[sa]} Φ) (at level 20).

(* Message group equivalence *)
Notation "m1 ≡g{ sagT , sagR } m2" := (message_group_equiv sagT sagR m1 m2) (at level 10).

(* Valid group membership *)
Notation "sa ∈g sag" := (elem_of_group sa sag) (at level 10).
Notation "sa ∉g sag" := (not_elem_of_group sa sag) (at level 10).

Lemma node_gnames_auth_init `{anerisPreG Σ Mdl} :
  ⊢ |==> ∃ γ, own (A:=authR node_gnames_mapUR) γ (● (to_agree <$> ∅)).
Proof. apply own_alloc. by apply auth_auth_valid. Qed.

Lemma saved_si_init `{anerisPreG Σ Mdl} :
  ⊢ |==> ∃ γ, own (A := authR socket_interpUR) γ (● (to_agree <$> ∅) ⋅
                                                  ◯ (to_agree <$> ∅)).
Proof. apply own_alloc. by apply auth_both_valid_discrete. Qed.

Lemma saved_si_update `{anerisG Mdl Σ} (A : gset socket_address_group) γsi f :
  ⊢ own (A := authR socket_interpUR) γsi (● (to_agree <$> ∅)) ∗
    own (A := authR socket_interpUR) γsi (◯ (to_agree <$> ∅)) ==∗
  ∃ M : gmap socket_address_group gname,
    ⌜elements (dom M) ≡ₚ elements A⌝ ∗
    own (A:=authR socket_interpUR) γsi (● (to_agree <$> M)) ∗
    [∗ map] a ↦ γ ∈ M, own (A:=authR socket_interpUR)
                           γsi (◯ {[ a := (to_agree γ) ]}) ∗
                       saved_pred_own (A:=message) γ (DfracDiscarded) (f a).
  iIntros "[Hsi Hsi']".
  pose proof (NoDup_elements A) as Hnd.
  iInduction (elements A) as [|a l] "IHl" forall "Hsi Hsi'".
  - iModIntro. iExists ∅.
    rewrite big_sepM_empty fmap_empty; iFrame.
    iPureIntro. by rewrite dom_empty_L.
  - inversion Hnd as [|? ? ? Hrd']; subst.
    iMod ("IHl" $! Hrd' with "Hsi Hsi'") as (M HMl) "[HM HML]"; iFrame.
    iMod (saved_pred_alloc (f a) (DfracDiscarded)) as (γ) "Hγ"; [done|].
    assert (a ∉ dom M) as Hnm.
    { by rewrite -elem_of_elements HMl. }
    iMod (own_update (A:=authR socket_interpUR) _ _
                     (● (<[a := to_agree γ]>(to_agree <$> M)) ⋅
                        (◯ ({[a := to_agree γ]}))) with "HM") as "[HM Hγ']".
    { apply auth_update_alloc. rewrite -insert_empty.
      rewrite /ε /=. apply alloc_local_update; [|done].
      apply (not_elem_of_dom (D:=gset socket_address_group)).
      rewrite dom_fmap. apply Hnm. }
    iModIntro.
    iExists (<[a:= γ]> M).
    rewrite !fmap_insert; iFrame.
    rewrite big_sepM_insert;
      [|by apply (not_elem_of_dom (D:=gset socket_address_group))].
    iFrame. iPureIntro.
    rewrite dom_insert_L elements_union_singleton //. auto.
Qed.

Lemma allocated_address_groups_init `{anerisPreG Σ Mdl} A :
  ⊢ |==> ∃ γ, own (A := agreeR (gsetUR socket_address_group)) γ (to_agree A).
Proof. by apply own_alloc. Qed.

(** Free ports lemmas *)
Lemma free_ports_auth_init `{anerisPreG Σ Mdl} Ps :
  ⊢ |==> ∃ γ, own (A:=authUR (gmapUR ip_address (gset_disjUR port))) γ (● (GSet <$> Ps)).
Proof.
  apply own_alloc. apply auth_auth_valid.
  induction Ps using map_ind; [done|].
  rewrite fmap_insert. by apply insert_valid.
Qed.

Lemma free_ports_alloc_pre `{anerisPreG Σ Mdl} γ P ip ports :
  P !! ip = None →
  own (A:=authUR (gmapUR ip_address (gset_disjUR port))) γ (● P) ==∗
  own (A:=authUR (gmapUR ip_address (gset_disjUR port))) γ (● <[ip := GSet ports]>P) ∗
  own (A:=authUR (gmapUR ip_address (gset_disjUR port))) γ (◯ ({[ ip := GSet ports]})).
Proof.
  iIntros (?) "HP"; rewrite /free_ports_auth /free_ports.
  iMod (own_update _ _ (● _ ⋅ ◯ {[ ip := (GSet ports)]}) with "HP")
    as "[HP Hip]"; last by iFrame.
  by apply auth_update_alloc, alloc_singleton_local_update.
Qed.

Lemma free_ports_auth_init_multiple `{anerisPreG Σ Mdl} P :
  ⊢ |==> ∃ γ, own (A:=authUR (gmapUR ip_address (gset_disjUR port))) γ
                  (● (GSet <$> P)) ∗
              [∗ map] ip ↦ ports ∈ P,
                own (A:=authUR (gmapUR ip_address (gset_disjUR port))) γ
                    (◯ ({[ ip := GSet ports]})).
Proof.
  iInduction P as [|ip ps P Hnin] "IHP" using map_ind.
  { iMod (free_ports_auth_init ∅) as (γ) "Hγ". iModIntro. iExists _.
    rewrite fmap_empty. iFrame.
    rewrite big_sepM_empty. done. }
  iMod "IHP" as (γ) "[HP Hps]".
  iMod (free_ports_alloc_pre γ (GSet <$> P) ip ps with "HP") as "[HP Hp]".
  { rewrite lookup_fmap. rewrite Hnin. done. }
  iModIntro. iExists γ. rewrite fmap_insert.
  iFrame. rewrite big_sepM_insert; [|done]. iFrame.
Qed.

Lemma free_ips_init `{anerisPreG Σ Mdl} (ips : gset ip_address) :
  ⊢ |==> ∃ γ, own γ (● GSet ips) ∗ [∗ set] ip ∈ ips, own γ (◯ GSet {[ ip ]}).
Proof.
  iMod (own_alloc (● GSet (∅:gset ip_address))) as (γ) "HM"; [by apply auth_auth_valid|].
  iAssert (|==>
             ∃ M : gset ip_address,
               (⌜elements M ≡ₚ elements ips⌝) ∗
               own γ (● GSet M) ∗
               [∗ set] ip ∈ M, own γ (◯ GSet {[ ip ]}))%I
    with "[HM]" as "HF".
  { pose proof (NoDup_elements ips) as Hnd.
    iInduction (elements ips) as [|a l] "IHl".
    - iModIntro. iExists ∅.
      rewrite big_sepS_empty. iFrame.
      by iPureIntro.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "HM") as (M HMl) "[HM HML]"; iFrame.
      assert (a ∉ M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update _ _ (● GSet ({[a]} ∪ M) ⋅ ◯ GSet {[a]}) with "HM")
        as "[HM Ha]".
      { apply auth_update_alloc, gset_disj_alloc_empty_local_update.
        set_solver. }
      iModIntro.
      iExists ({[a]} ∪ M); iFrame.
      iSplit; first by iPureIntro;
        rewrite elements_union_singleton // HMl.
      rewrite big_sepS_insert //. iFrame. }
  iMod "HF" as (M HMF) "[? ?]".
  replace M with ips; first by iModIntro; iExists _; iFrame.
  apply set_eq => x.
  rewrite -!elem_of_elements HMF //.
Qed.

Lemma socket_address_group_ctx_init `{anerisPreG Σ Mdl}
      (sags : gset socket_address_group) :
  all_disjoint sags →
  ⊢ |==> ∃ γ,
    own (A:=(authR socket_address_groupUR)) γ
        (● (DGSets sags)).
Proof.
  intros Hdisj.
  iMod (own_alloc (● (DGSets sags))) as (γ) "Hsags".
  { apply auth_auth_valid. done. }
  iModIntro. iExists _. iFrame.
Qed.

Lemma socket_address_group_own_alloc_subseteq_pre `{anerisPreG Σ Mdl}
      γ (sags sags' : gset socket_address_group) :
  sags' ⊆ sags →
  own (A:=(authR socket_address_groupUR)) γ
      (● (DGSets sags)) ==∗
  own (A:=(authR socket_address_groupUR)) γ
      (● (DGSets sags)) ∗
  own (A:=(authR socket_address_groupUR)) γ
      (◯ (DGSets sags')).
Proof.
  iIntros (Hle) "Hsags".
  iDestruct (own_valid with "Hsags") as %Hvalid.
  setoid_rewrite auth_auth_valid in Hvalid.
  setoid_rewrite disj_gsets_valid in Hvalid.
  iMod (own_update with "Hsags") as "[Hsags Hsags']".
  { apply auth_update_alloc.
    eapply (disj_gset_alloc_empty_local_update sags sags').
    { by eapply all_disjoint_subseteq. }
    by eapply have_disj_elems_subseteq. }
  iFrame.
  by rewrite subseteq_union_1_L.
Qed.

Lemma socket_address_group_init `{anerisPreG Σ Mdl}
      (sags : gset socket_address_group) :
  all_disjoint sags →
  ⊢ |==> ∃ γ, own (A:=(authR socket_address_groupUR)) γ
                  (● (DGSets sags)) ∗
              own (A:=(authR socket_address_groupUR)) γ
                  (◯ (DGSets sags)).
Proof.
  intros Hdisj.
  iMod socket_address_group_ctx_init as (γ) "Hauth"; [done|].
  iMod (socket_address_group_own_alloc_subseteq_pre with "Hauth")
    as "[Hauth Hown]"; [done|].
  iModIntro. iExists γ. by iFrame.
Qed.

Lemma socket_address_group_own_big_sepS `{anerisPreG Σ Mdl}
      γ
      (sags : gset socket_address_group) :
  ⊢ own (A:=(authR socket_address_groupUR)) γ
        (◯ (DGSets sags)) -∗
  [∗ set] sag ∈ sags, own (A:=(authR socket_address_groupUR)) γ
                          (◯ (DGSets {[sag]})).
Proof.
  iInduction (sags) as [|sag sags Hsag] "IH" using (set_ind_L); [by eauto|].
  iIntros "H".
  setoid_rewrite <-disj_gsets_op_union.
  rewrite auth_frag_op.
  iDestruct "H" as "[H1 H2]".
  rewrite big_sepS_union; last by set_solver.
  rewrite big_sepS_singleton.
  iFrame. by iApply "IH".
Qed.

Lemma socket_address_group_own_subseteq_pre `{anerisPreG Σ Mdl}
      γ (sags sags' : gset socket_address_group) :
  sags' ⊆ sags →
  own (A:=(authR socket_address_groupUR)) γ
      (◯ (DGSets sags)) -∗
  own (A:=(authR socket_address_groupUR)) γ
      (◯ (DGSets sags')).
Proof.
  iIntros (Hle) "Hsags".
  apply subseteq_disjoint_union_L in Hle.
  destruct Hle as [Z [-> Hdisj]].
  setoid_rewrite <-disj_gsets_op_union.
  iDestruct "Hsags" as "[H1 H2]".
  iFrame.
Qed.

Lemma messages_ctx_init `{anerisPreG Σ Mdl}
      (gs : gset socket_address_group)
      (γo γs γr : gname)
      (As Ar: gset socket_address_group) :
  ([∗ set] sag ∈ gs, own γo (◯ (DGSets {[sag]}))) -∗
  own γs (to_agree As) -∗ own γr (to_agree Ar) ==∗
  ∃ γ,
    gen_heap_light_ctx
      γ (gset_to_gmap ((∅, ∅) : message_soup * message_soup) gs) ∗
    [∗ set] sag ∈ gs,
  ∃ As' Ar', own γs (to_agree As') ∗ own γr (to_agree Ar') ∗
             (⌜(sag ∈ As' ↔ ((bool_decide (sag ∈ As)) = true)) ∧
              (sag ∈ Ar' ↔ ((bool_decide (sag ∈ Ar)) = true))⌝) ∗
             own γo (◯ (DGSets {[ sag ]})) ∗
             lmapsto γ sag 1 (∅, ∅).
Proof.
  iIntros "#Hgs #HAs #HAr".
  iMod (gen_heap_light_init
          (∅ : gmap socket_address_group (message_soup * message_soup))) as (γ) "Hctx".

  set σ' := (gset_to_gmap ((∅, ∅) : message_soup * message_soup) gs).
  iMod (gen_heap_light_alloc_gen _ σ' with "Hctx") as "[Hctx HB]".
  { apply map_disjoint_empty_r. }
  rewrite map_union_empty.
  iModIntro. iExists _. iFrame.
  subst σ'.
  iAssert ([∗ map] l↦v ∈ gset_to_gmap ((∅, ∅) : message_soup * message_soup) gs, lmapsto γ l 1 (∅, ∅))%I
    with "[HB]" as "HB".
  { iApply big_sepM_mono; simpl; last done.
    intros ??; rewrite lookup_gset_to_gmap_Some; intros [? <-]; done. }
  rewrite big_sepM_dom.
  rewrite dom_gset_to_gmap.
  iDestruct (big_sepS_sep with "[HB]") as "Hgs'".
  { iFrame "HB". iFrame "Hgs". }
  iApply (big_sepS_impl with "Hgs'").
  iIntros "!#" (x Hin) "[Hsag Hx]".
  iExists _, _; iFrame "#". iFrame.
  rewrite !bool_decide_eq_true; eauto.
Qed.

Lemma model_init `{anerisPreG Σ Mdl} (st : Mdl) :
  ⊢ |==> ∃ γ, own γ (● Excl' st) ∗ own γ (◯ Excl' st).
Proof.
  iMod (own_alloc (● Excl' st ⋅ ◯ Excl' st)) as (γ) "[Hfl Hfr]".
  { by apply auth_both_valid_2. }
  iExists _. by iFrame.
Qed.

Lemma steps_init `{anerisPreG Σ Mdl} n :
  ⊢ |==> ∃ γ, mono_nat_auth_own γ 1 n ∗ mono_nat_lb_own γ n.
Proof. iApply mono_nat_own_alloc. Qed.

Lemma unallocated_init `{anerisPreG Σ Mdl} (A : gset socket_address_group) :
  ⊢ |==> ∃ γ, own γ (● (GSet A)) ∗
              own γ (◯ (GSet A)).
Proof.
  iMod (own_alloc (● (GSet ∅) ⋅ ◯ (GSet ∅))) as (γ) "[Ha Hf]".
  { by apply auth_both_valid. }
  iExists γ.
  iInduction A as [|a A Hnin] "IH" using set_ind_L.
  - iModIntro. iFrame.
  - iMod ("IH" with "Ha Hf") as "[Ha Hf]".
    iMod (own_update with "Ha") as "[Ha Hf']".
    { apply (auth_update_alloc _ (GSet ({[a]} ∪ A))).
      apply gset_disj_alloc_empty_local_update.
      set_solver. }
    iModIntro. iFrame.
    rewrite -gset_op -gset_disj_union; [|set_solver].
    rewrite auth_frag_op.
    iApply own_op.
    iFrame.
Qed.

Lemma alloc_evs_init `{anerisPreG Σ Mdl} (lbls : gset string) :
  ⊢ |==> ∃ γ,
    own (A := authUR (gmapUR string (exclR aneris_eventsO)))
        γ (● (Excl <$> (gset_to_gmap [] lbls))) ∗
    [∗ set] lbl ∈ lbls,
  own (A := authUR (gmapUR string (exclR aneris_eventsO)))
      γ (◯ {[ lbl := Excl [] ]}).
Proof.
  iMod (own_alloc (A := authUR (gmapUR string (exclR aneris_eventsO))) (● ∅))
    as (γ) "HM"; [by apply auth_auth_valid|].
  iAssert (|==>
             ∃ M : gset string,
               ⌜elements M ≡ₚ elements lbls⌝ ∗
               own (A := authUR (gmapUR string (exclR aneris_eventsO)))
                   γ (● (Excl <$> (gset_to_gmap [] M))) ∗
               [∗ set] lbl ∈ M,
             own (A := authUR (gmapUR string (exclR aneris_eventsO)))
                 γ (◯ {[ lbl := Excl [] ]}))%I
    with "[HM]" as "HF".
  { pose proof (NoDup_elements lbls) as Hnd.
    iInduction (elements lbls) as [|lbl lbls'] "IHl".
    - iModIntro. iExists ∅.
      rewrite gset_to_gmap_empty fmap_empty big_sepS_empty. iFrame.
      by iPureIntro.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "HM") as (M HMl) "[HM HML]"; iFrame.
      assert (lbl ∉ M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update (A := authUR (gmapUR string (exclR aneris_eventsO)))
                       _ _ (● (Excl <$> gset_to_gmap [] ({[lbl]} ∪ M)) ⋅
                            ◯ {[ lbl := Excl [] ]}) with "HM")
        as "[HM Ha]".
      { rewrite gset_to_gmap_union_singleton fmap_insert.
        apply auth_update_alloc. apply: alloc_singleton_local_update; last done.
        rewrite lookup_fmap. by eapply lookup_gset_to_gmap_None in Hnm as ->. }
      iModIntro.
      iExists ({[lbl]} ∪ M); iFrame.
      iSplit; first by iPureIntro; rewrite elements_union_singleton // HMl.
      rewrite big_sepS_insert //. iFrame. }
  iMod "HF" as (M HMF) "[? ?]".
  replace M with lbls; first by iModIntro; iExists _; iFrame.
  apply set_eq => x.
  rewrite -!elem_of_elements HMF //.
Qed.

Lemma sendreceive_evs_init `{anerisPreG Σ Mdl} (sags : gset socket_address_group) :
  ⊢ |==> ∃ γ, own
                (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
                γ (● (Excl <$> (gset_to_gmap [] sags))) ∗
              [∗ set] sag ∈ sags,
  own (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
      γ (◯ {[ sag := Excl [] ]}).
Proof.
  iMod (own_alloc
          (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO))) (● ∅))
    as (γ) "HM"; [by apply auth_auth_valid|].
  iAssert (|==>
             ∃ M : gset socket_address_group,
               ⌜elements M ≡ₚ elements sags⌝ ∗
               own (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
                   γ (● (Excl <$> (gset_to_gmap [] M))) ∗
               [∗ set] sa ∈ M,
             own (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
                 γ (◯ {[ sa := Excl [] ]}))%I
    with "[HM]" as "HF".
  { pose proof (NoDup_elements sags) as Hnd.
    iInduction (elements sags) as [|sag sags'] "IHl".
    - iModIntro. iExists ∅.
      rewrite gset_to_gmap_empty fmap_empty big_sepS_empty. iFrame.
      by iPureIntro.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "HM") as (M HMl) "[HM HML]"; iFrame.
      assert (sag ∉ M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
                       _ _ (● (Excl <$> gset_to_gmap [] ({[sag]} ∪ M)) ⋅
                            ◯ {[ sag := Excl [] ]}) with "HM")
        as "[HM Ha]".
      { rewrite gset_to_gmap_union_singleton fmap_insert.
        apply auth_update_alloc. apply: alloc_singleton_local_update; last done.
        rewrite lookup_fmap. by eapply lookup_gset_to_gmap_None in Hnm as ->. }
      iModIntro.
      iExists ({[sag]} ∪ M); iFrame.
      iSplit; first by iPureIntro; rewrite elements_union_singleton // HMl.
      rewrite big_sepS_insert //. iFrame. }
  iMod "HF" as (M HMF) "[? ?]".
  replace M with sags; first by iModIntro; iExists _; iFrame.
  apply set_eq => x.
  rewrite -!elem_of_elements HMF //.
Qed.

Section resource_lemmas.
  Context `{aG : !anerisG Mdl Σ}.

  #[global] Instance mapsto_node_persistent ip γn : Persistent (mapsto_node ip γn).
  Proof. rewrite mapsto_node_eq /mapsto_node_def. apply _. Qed.
  #[global] Instance mapsto_node_timeless ip γn : Timeless (mapsto_node ip γn).
  Proof. rewrite mapsto_node_eq /mapsto_node_def. apply _. Qed.

  #[global] Instance is_node_persistent ip : Persistent (is_node ip).
  Proof. apply _. Qed.

  Lemma auth_frag_st_agree st st' :
    auth_st st -∗ frag_st st' -∗ ⌜st = st'⌝.
  Proof.
    iIntros "[Ha %] [Hf %]".
    by iDestruct (own_valid_2 with "Ha Hf") as
        %[Heq%Excl_included%leibniz_equiv ?]%auth_both_valid_discrete.
  Qed.

  Lemma auth_frag_st_update st st' :
    rtc Mdl Mdl.(model_state_initial) st' →
    auth_st st -∗ frag_st st ==∗ auth_st st' ∗ frag_st st'.
  Proof.
    iIntros (?) "[Hauth %] [Hfrag %]".
    iMod ((own_update _ (● (Excl' st) ⋅ ◯ (Excl' st))
                      (● (Excl' st') ⋅ ◯ (Excl' st')))
            with "[Hauth Hfrag]") as "[??]".
    { by apply auth_update, option_local_update, exclusive_local_update. }
    { rewrite own_op //. iFrame. }
    by iFrame "∗ %".
  Qed.

  Lemma frag_st_rtc st :
    frag_st st -∗ ⌜rtc Mdl Mdl.(model_state_initial) st⌝.
  Proof. by iIntros "[_ %]". Qed.

  Lemma mapsto_node_agree ip γn γn' :
    mapsto_node ip γn -∗ mapsto_node ip γn' -∗ ⌜γn = γn'⌝.
  Proof.
    apply wand_intro_r.
    rewrite /node_gnames_auth mapsto_node_eq -own_op own_valid discrete_valid.
    f_equiv=> /auth_frag_valid /=. rewrite singleton_op singleton_valid.
    apply (to_agree_op_inv_L (A := node_gnamesO)).
  Qed.

  Lemma node_gnames_valid ip γn m :
    node_gnames_auth m -∗ mapsto_node ip γn -∗ ⌜m !! ip = Some γn⌝.
  Proof.
    iIntros "H1 H2".
    iCombine "H2" "H1" as "H".
    rewrite /node_gnames_auth mapsto_node_eq -own_op own_valid.
    iDestruct "H" as %HvalidR. iPureIntro.
    revert HvalidR.
    rewrite comm auth_both_valid_discrete.
    rewrite singleton_included_l=> -[[y [Hlookup Hless]] Hvalid].
    assert (Hvalidy := lookup_valid_Some _ ip y Hvalid Hlookup).
    revert Hlookup.
    rewrite lookup_fmap fmap_Some_equiv=> -[v' [Hl Heq]]. revert Hless Heq.
    rewrite Some_included_total.
    destruct (to_agree_uninj y Hvalidy) as [y' <-].
    rewrite to_agree_included.
    intros Heq%leibniz_equiv Heq'%(to_agree_inj y' v')%leibniz_equiv.
    by simplify_eq.
  Qed.

  Lemma node_gnames_alloc γn m ip :
    m !! ip = None →
    node_gnames_auth m ==∗ node_gnames_auth (<[ip:=γn]> m) ∗ mapsto_node ip γn.
  Proof.
    iIntros (?) "Hm". rewrite mapsto_node_eq /mapsto_node_def.
    iMod (own_update _ _
                     (● (to_agree <$> (<[ip:=γn]> m)) ⋅ (◯ {[ ip := to_agree γn ]})
                      : authR node_gnames_mapUR) with "Hm") as "[Hm Hn]".
    { rewrite fmap_insert. eapply auth_update_alloc.
      apply (alloc_singleton_local_update
               (A := (agreeR node_gnamesO))); last done.
      rewrite -not_elem_of_dom dom_fmap_L not_elem_of_dom //. }
    iModIntro. iFrame.
  Qed.

  Lemma node_gnames_alloc_strong γs ip σ s :
    γs !! ip = None →
    node_gnames_auth γs ==∗ ∃ (γn : node_gnames),
        node_gnames_auth (<[ip:=γn]>γs) ∗
        mapsto_node ip γn ∗
        heap_ctx γn σ ∗
        ([∗ map] l ↦ v ∈ σ, l ↦[ip] v) ∗
        sockets_ctx γn s ∗
        ([∗ map] sh ↦ sb ∈ s, sh ↪[ip] sb).
  Proof.
    iIntros (HNone) "Hγs".
    iMod (gen_heap_light_init_strong σ) as (γσ) "[Hσ Hσs]".
    iMod (gen_heap_light_init_strong s) as (γss) "[Hs Hss]".
    set (γn := Node_gname γσ γss).
    iMod (node_gnames_alloc γn with "Hγs") as "[Hγs #Hγ]"; [done|].
    iModIntro. iExists γn. iFrame "#∗".
    iSplitL "Hσs".
    - iApply (big_sepM_impl with "Hσs").
      iIntros "!>" (k x HSome) "Hmapsto". iExists γn. iFrame "#∗".
    - iApply (big_sepM_impl with "Hss").
      iIntros "!>" (k x HSome) "Hmapsto". iExists γn. iFrame "#∗".
  Qed.

  Lemma node_gnames_alloc_strong_multiple σ γs' :
    dom $ state_heaps σ = dom $ state_sockets σ →
    dom γs' ## dom $ state_heaps σ →
    node_gnames_auth γs' ==∗
    ∃ γs, ⌜dom γs = dom $ state_heaps σ⌝ ∗ ⌜dom γs = dom $ state_sockets σ⌝ ∗
          node_gnames_auth (γs' ∪ γs) ∗
          ([∗ set] ip ∈ dom $ state_heaps σ, is_node ip) ∗
          ([∗ map] ip↦γ ∈ γs, mapsto_node ip γ ∗
                              heap_ctx γ (state_heaps σ !!! ip) ∗
                              sockets_ctx γ (fst <$> (state_sockets σ !!! ip))) ∗
          ([∗ set] ip ∈ dom $ state_heaps σ, ([∗ map] l ↦ v ∈ state_heaps σ !!! ip, l ↦[ip] v) ∗
                                             ([∗ map] sh ↦ sb ∈ state_sockets σ !!! ip, sh ↪[ip] sb.1)).
  Proof.
    assert (∃ ips, ips = dom $ state_heaps σ) as [ips Hips]; [by eexists|].
    revert Hips.
    iInduction ips as [|ip ips Hnin] "IHips" using set_ind_L forall (γs' σ);
      iIntros (Hdom1 Hdom2 Hdom3) "Hγs".
    { iModIntro. iExists ∅.
      rewrite right_id_L.
      iSplit; [iPureIntro; set_solver|].
      iSplit; [iPureIntro; set_solver|].
      iFrame. rewrite -!Hdom1.
      rewrite !big_sepS_empty.
      rewrite !big_sepM_empty. done. }
    assert (γs' !! ip = None).
    { simpl in *.
      apply not_elem_of_dom. rewrite -Hdom1 in Hdom3. set_solver. }
    iMod (node_gnames_alloc_strong _ ip with "Hγs")
      as (γn) "(Hγs & #Hip & Hσ & Hσs & Hs & Hss)"; [done|].
    iMod ("IHips" $! _
                  (mkState (delete ip $ state_heaps σ)
                           (delete ip $ state_sockets σ)
                           (state_ms σ)) with "[] [] [] Hγs") as "Hγs".
    { iPureIntro. set_solver. }
    { iPureIntro. set_solver. }
    { iPureIntro. set_solver. }
    iDestruct "Hγs" as (γs Hdom1' Hdom2') "(Hγs & #Hip' & Hσ' & Hσs')".
    simpl.
    iModIntro. iExists (<[ip:=γn]> γs).
    iSplit.
    { iPureIntro. rewrite -Hdom1. set_solver. }
    iSplit.
    { iPureIntro. rewrite -Hdom2 -Hdom1. set_solver. }
    iSplitL "Hγs".
    { rewrite !insert_union_singleton_l.
      replace ({[ip := γn]} ∪ γs' ∪ γs) with (γs' ∪ ({[ip := γn]} ∪ γs)).
      iFrame.
      rewrite assoc. f_equiv.
      rewrite map_union_comm; [done|].
      apply map_disjoint_alt. intros.
      destruct (decide (ip = i)).
      - set_solver.
      - right. by rewrite lookup_insert_ne. }
    rewrite !dom_delete_L. rewrite -!Hdom1.
    replace (({[ip]} ∪ ips) ∖ {[ip]}) with ips by set_solver.
    rewrite !big_sepS_union; [|set_solver|set_solver].
    rewrite !big_sepS_singleton.
    assert (γs !! ip = None).
    { simpl in *. rewrite dom_delete_L in Hdom1'.
      apply not_elem_of_dom. rewrite Hdom1'. set_solver. }
    rewrite big_sepM_insert; [|done].
    iFrame "#∗".
    iSplit; [iExists _; iFrame "#"|].
    iSplitL "Hσ'".
    { iApply (big_sepM_impl with "Hσ'").
      iIntros "!>" (k x HSome) "[Hnode [Hheap Hsocket]]".
      simpl in *. assert (k ≠ ip) by set_solver.
      rewrite lookup_total_delete_ne; [|done].
      rewrite lookup_total_delete_ne; [|done]. iFrame. }
    iSplitL "Hss".
    { rewrite big_sepM_fmap. iFrame. }
    iApply (big_sepS_impl with "Hσs'").
    iIntros "!>" (x Hin) "[Hσ Hs]".
    assert (x ≠ ip) by set_solver.
    rewrite lookup_total_delete_ne; [|done].
    rewrite lookup_total_delete_ne; [|done].
    iFrame.
  Qed.

  Lemma node_ctx_init σ s :
    ⊢ |==> ∃ (γn : node_gnames), heap_ctx γn σ ∗ sockets_ctx γn s.
  Proof.
    iMod (gen_heap_light_init σ) as (γh) "Hh".
    iMod (gen_heap_light_init s) as (γs) "Hs".
    iExists {| heap_name := γh; sockets_name := γs |}.
    iModIntro. iFrame.
  Qed.

  Lemma is_node_alloc σ ip :
    σ !! ip = None →
    node_gnames_auth σ ==∗
    ∃ γn, node_gnames_auth (<[ip := γn]>σ) ∗ is_node ip.
  Proof.
    iIntros (Hnone) "Hauth".
    iMod (node_ctx_init ∅ ∅) as (γn) "[Hh Hs]".
    iMod (node_gnames_alloc γn _ ip with "[$]") as "[Hmp Hγn]"; [done|].
    iExists _. iFrame. iExists _. by iFrame.
  Qed.

  Lemma is_node_alloc_multiple σ :
    dom (state_heaps σ) = dom (state_sockets σ) →
    node_gnames_auth ∅ ==∗
    ∃ γs, ⌜dom γs = dom $ state_heaps σ⌝ ∗ ⌜dom γs = dom $ state_sockets σ⌝ ∗
          node_gnames_auth γs ∗
          ([∗ set] ip ∈ (dom $ state_heaps σ), is_node ip) ∗
          ([∗ map] ip↦γ ∈ γs, mapsto_node ip γ ∗
                              heap_ctx γ (state_heaps σ !!! ip) ∗
                              sockets_ctx γ (fst <$> (state_sockets σ !!! ip))) ∗
          ([∗ set] ip ∈ (dom $ state_heaps σ), ([∗ map] l ↦ v ∈ state_heaps σ !!! ip, l ↦[ip] v) ∗
                                               ([∗ map] sh ↦ sb ∈ state_sockets σ !!! ip, sh ↪[ip] sb.1)).
  Proof.
    iIntros (Hdom) "Hγs".
    iMod (node_gnames_alloc_strong_multiple σ ∅ with "Hγs") as (γs) "H";
      [done|set_solver|].
    rewrite left_id_L.
    iModIntro. iExists γs. done.
  Qed.

  #[global] Instance mapsto_heap_timeless l ip q v :
    Timeless (l ↦[ip]{q} v).
  Proof. apply _. Qed.
  #[global] Instance mapsto_heap_fractional l ip v :
    Fractional (λ q, l ↦[ip]{q} v)%I.
  Proof.
    rewrite /mapsto_heap /Fractional=> p q. iSplit.
    - iDestruct 1 as (?) "[#? [H1 H2]]".
      iSplitL "H1"; iExists _; eauto.
    - iDestruct 1 as "[H1 H2]".
      iDestruct "H1" as (?) "[Hn1 Hp]".
      iDestruct "H2" as (?) "[Hn2 Hq]".
      iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
      iExists _. iFrame.
  Qed.
  #[global] Instance mapsto_heap_as_fractional l ip q v :
    AsFractional (l ↦[ip]{q} v) (λ q, l ↦[ip]{q} v)%I q.
  Proof. split; [done|]. apply _. Qed.

  #[global] Instance mapsto_socket_timeless z ip q s :
    Timeless (z ↪[ ip ]{ q } s).
  Proof. apply _. Qed.

  #[global] Instance mapsto_socket_fractional z ip s :
    Fractional (λ q, z ↪[ip]{q} s)%I.
  Proof.
    rewrite /Fractional=> p q. iSplit.
    - iDestruct 1 as (?) "[#? [H1 H2]]".
      iSplitL "H1"; iExists _; eauto.
    - iDestruct 1 as "[H1 H2]".
      iDestruct "H1" as (?) "[Hn1 Hp]".
      iDestruct "H2" as (?) "[Hn2 Hq]".
      iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
      iExists _. iFrame.
  Qed.

  #[global] Instance mapsto_socket_as_fractional z ip q s :
    AsFractional (z ↪[ip]{q} s) (λ q, z ↪[ip]{q} s)%I q.
  Proof. split; [done|]. apply _. Qed.

  Lemma observed_send_agree A A' :
    observed_send_groups A -∗ observed_send_groups A' -∗ ⌜A = A'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%to_agree_op_valid%leibniz_equiv.
    done.
  Qed.

  Lemma observed_receive_agree A A' :
    observed_receive_groups A -∗ observed_receive_groups A' -∗ ⌜A = A'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%to_agree_op_valid%leibniz_equiv.
    done.
  Qed.

  #[global] Instance mapsto_messages_timeless a q bs br s :
    Timeless (a ⤳*[bs, br]{ q } s).
  Proof. apply _. Qed.

  Lemma socket_address_group_ctx_valid sags :
    socket_address_group_ctx sags -∗
    ⌜all_disjoint sags⌝ ∗ ⌜set_Forall is_ne sags⌝.
  Proof.
    iIntros "[%Hne [Hsags _]]".
    iDestruct (own_valid with "Hsags") as %Hvalid.
    pose proof (auth_auth_valid {| dgsets_of := sags |}) as [H _].
    apply H in Hvalid.
    pose proof (disj_gsets_valid sags) as [H' _].
    apply H' in Hvalid.
    done.
  Qed.

  Lemma socket_address_groups_ctx_own sags :
    socket_address_group_ctx sags -∗
    socket_address_groups_own sags.
  Proof. by iIntros "[_ [_ Hsags]]". Qed.

  #[global] Instance socket_address_group_own_timeless sag :
    Timeless (socket_address_group_own sag).
  Proof. apply _. Qed.

  #[global] Instance socket_address_group_own_persistent sag :
    Persistent (socket_address_group_own sag).
  Proof. apply _. Qed.

  #[global] Instance socket_address_groups_own_timeless sags :
    Timeless (socket_address_groups_own sags).
  Proof. apply _. Qed.

  #[global] Instance socket_address_groups_own_persistent sags :
    Persistent (socket_address_groups_own sags).
  Proof. apply _. Qed.

  Lemma socket_address_group_ctx_update sags sags' :
    all_disjoint sags' → have_disj_elems sags' sags →
    set_Forall is_ne sags' →
    socket_address_group_ctx sags ==∗
    socket_address_group_ctx (sags' ∪ sags) ∗
    socket_address_groups_own sags'.
  Proof.
    iIntros (Hdisj Helems Hne) "[%Hne' [Hctx #Hsag]]".
    iMod (own_update with "Hctx") as "[Hsags #Hsag']".
    { apply auth_update_alloc.
      by eapply disj_gset_alloc_empty_local_update. }
    iModIntro. iFrame "#∗".
    iSplit; [by iPureIntro; apply set_Forall_union|].
    rewrite -disj_gsets_op_union auth_frag_op.
    iApply own_op. by iFrame "#".
  Qed.

  Lemma socket_address_group_own_agree sa sag1 sag2 :
    sa ∈ sag1 → sa ∈ sag2 →
    socket_address_group_own sag1 -∗
    socket_address_group_own sag2 -∗
    ⌜sag1 = sag2⌝.
  Proof.
    iIntros (Hin1 Hin2) "Hsag1 Hsag2".
    iDestruct (own_valid_2 with "Hsag1 Hsag2") as %Hvalid.
    rewrite -auth_frag_op in Hvalid.
    pose proof (auth_frag_valid (A:=socket_address_groupUR)
                                (DGSets {[sag1]} ⋅ DGSets {[sag2]}))
      as [Hv _].
    apply Hv in Hvalid.
    apply disj_gsets_valid_op in Hvalid.
    destruct Hvalid as (Hgdisj & Hgdisj' & Hdisjgg').
    destruct (Hdisjgg' sag1 sag2) as [-> | H2];
      [ set_solver | set_solver | done | set_solver ].
  Qed.

  Lemma socket_address_groups_own_union sags1 sags2 :
    ⊢ socket_address_groups_own sags1 ∗
      socket_address_groups_own sags2
      ∗-∗
      socket_address_groups_own (sags1 ∪ sags2).
  Proof.
    rewrite /socket_address_groups_own.
    rewrite -disj_gsets_op_union.
    rewrite auth_frag_op.
    rewrite own_op.
    eauto.
  Qed.

  Lemma socket_address_group_own_subseteq sags1 sags2 :
    sags2 ⊆ sags1 →
    socket_address_groups_own sags1 -∗
    socket_address_groups_own sags2.
  Proof.
    iIntros (Hle) "Hsags".
    rewrite /socket_address_groups_own.
    apply subseteq_disjoint_union_L in Hle.
    destruct Hle as [Z [-> Hdisj]].
    setoid_rewrite <-disj_gsets_op_union.
    iDestruct "Hsags" as "[H1 H2]".
    iFrame.
  Qed.

  #[global] Instance mapsto_messages_fractional sag bs br s :
    Fractional (λ q, sag ⤳*[bs,br]{q} s)%I.
  Proof.
    intros p q.
    iSplit.
    - iDestruct 1 as (? ?) "(#?&#?&#?&(#Hsag & [H1 H2]))".
      iFrame. iSplit; iExists _, _; iFrame "#".
    - iIntros "[Hp Hq]".
      iDestruct "Hp" as (? ?) "(#HAs1&#HAr1&#?&#Hsag&Hp)".
      iDestruct "Hq" as (? ?) "(#HAs2&#HAr2&#?&_&Hq)".
      iExists _,_; iFrame "#∗".
  Qed.

  #[global] Instance mapsto_messages_as_fractional sag q bs br s :
    AsFractional (sag ⤳*[bs,br]{q} s) (λ q, sag ⤳*[bs,br]{q} s)%I q.
  Proof. split; [ done | by apply mapsto_messages_fractional ]. Qed.

  Lemma messages_mapsto_observed sag q bs br s :
    sag ⤳*[bs, br]{ q } s -∗
    sag ⤳*[bs, br]{ q } s ∗
    ∃ As Ar, observed_send_groups As ∗ observed_receive_groups Ar ∗
             socket_address_group_own sag ∗
             ⌜(sag ∈ As ↔ (bs = true)) ∧ (sag ∈ Ar ↔ (br = true))⌝.
  Proof.
    iDestruct 1 as (? ?) "(#?&#?&%H&#Hown&?)".
    destruct H as [HAs HAr].
    iSplitL; first by iExists _,_; eauto.
    iExists _, _; eauto.
  Qed.

  Lemma heap_mapsto_agree l ip q1 q2 v1 v2 :
    l ↦[ip]{q1} v1 -∗ l ↦[ip]{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "(% & Hn1 & Hv1) (% & Hn2 & Hv2)".
    iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
    iApply (lmapsto_agree with "Hv1 Hv2").
  Qed.

  Lemma socket_mapsto_agree z ip q1 q2 s1 s2 :
    z ↪[ip]{q1} s1 -∗ z ↪[ip]{q2} s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "(% & Hn1 & Hv1) (% & Hn2 & Hv2)".
    iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
    iApply (lmapsto_agree with "Hv1 Hv2").
  Qed.

  Lemma messages_mapsto_valid sag bs br R T:
    sag ⤳*[bs, br] (R, T) -∗
    socket_address_group_own sag.
  Proof. by iDestruct 1 as  (??) "(?&?&?&$&?&$)". Qed.

  Lemma messages_mapsto_update sag bs br R T R' T' mhm :
    sag ⤳*[bs, br] (R, T) ∗ messages_ctx mhm ==∗
    sag ⤳*[bs, br] (R', T') ∗ messages_ctx (<[sag := (R',T')]>mhm).
  Proof.
    iIntros "(Hl & Ha)".
    iDestruct "Hl" as (??) "(?&?&?&#Hsag&Hl)".
    iMod (gen_heap_light_update _ mhm sag (R,T) (R', T')
            with "Ha Hl") as "[Ha Hf]".
    iModIntro.
    iFrame "#∗". iExists As, Ar. iFrame "#∗".
  Qed.

  Lemma messages_mapsto_ctx_valid sag bs br R T mh :
    sag ⤳*[bs, br] (R, T) -∗ messages_ctx mh -∗ ⌜mh !! sag = Some (R,T)⌝.
  Proof.
    iIntros "Hf Ha".
    iDestruct "Hf" as (??) "(?&?&?&?&Hf&Hown)".
    by iApply (gen_heap_light_valid with "Ha Hf").
  Qed.

  Lemma messages_mapsto_agree sa sag1 sag2 bs br bs' br' R T R' T' q1 q2 :
    sa ∈ sag1 → sa ∈ sag2 →
    sag1 ⤳*[bs, br]{q1} (R, T) -∗ sag2 ⤳*[bs', br']{q2} (R', T') -∗
    ⌜sag1 = sag2 ∧ bs = bs' ∧ br = br' ∧ R = R' ∧ T = T'⌝.
  Proof.
    iIntros (Hin1 Hin2) "Ha1 Ha2".
    iDestruct "Ha1" as (??) "(HAs1&HAr1&[%Heq1 %Heq2]&(#Hsag1 & Ha1 & Hown1))".
    iDestruct "Ha2" as (??) "(HAs2&HAr2&[%Heq3 %Heq4]&(#Hsag2 & Ha2 & Hown2))".
    iDestruct (observed_send_agree with "HAs1 HAs2") as %->.
    iDestruct (observed_receive_agree with "HAr1 HAr2") as %->.
    iDestruct (socket_address_group_own_agree with "Hsag1 Hsag2")
      as %<-; [ done | done | ].
    revert Heq3; rewrite Heq1; intros Heq3.
    revert Heq4; rewrite Heq2; intros Heq4.
    assert (bs = bs' ∧ br = br') as [-> ->].
    { destruct bs; destruct bs'; destruct br; destruct br'; intuition done. }
    iDestruct (lmapsto_agree with "Ha1 Ha2") as %?.
    by simplify_eq.
  Qed.

  Lemma unallocated_groups_split A1 A2 :
    A1 ## A2 →
    ⊢ unallocated_groups (A1 ∪ A2) ∗-∗
      unallocated_groups A1 ∗ unallocated_groups A2.
  Proof.
    intros Hdisj.
    rewrite -gset_op {1}/unallocated_groups -gset_disj_union; [|done].
    iSplit.
    - iIntros "H". iDestruct "H" as "[H1 H2]". by iFrame.
    - iIntros "[H1 H2]". rewrite auth_frag_op. iApply own_op. iFrame.
  Qed.

  Lemma unallocated_split A1 A2 :
    A1 ## A2 →
    ⊢ unallocated (A1 ∪ A2) ∗-∗
      unallocated A1 ∗ unallocated A2.
  Proof.
    rewrite /unallocated. rewrite to_singletons_union.
    intros Hdisj.
    iApply unallocated_groups_split.
    set_solver.
  Qed.

  Lemma unallocated_update_alloc A B :
    A ## B →
    ⊢ unallocated_groups_auth A ==∗
      unallocated_groups_auth (A ∪ B) ∗ unallocated_groups B.
  Proof.
    iIntros (Hdisj) "HA".
    iMod (own_update with "HA") as "[HA HB]".
    { by apply auth_update_alloc, gset_disj_alloc_empty_local_update. }
    iModIntro. replace (B ∪ A) with (A ∪ B) by set_solver. by iFrame.
  Qed.

  Lemma unallocated_update_dealloc A B :
    ⊢ unallocated_groups_auth A ∗ unallocated_groups B ==∗
      unallocated_groups_auth (A ∖ B).
  Proof.
    iIntros "[HA HB]".
    rewrite /unallocated_groups_auth /unallocated_groups.
    iDestruct (own_valid_2 with "HA HB") as %Hvalid.
    rewrite auth_both_valid_discrete in Hvalid.
    destruct Hvalid as [Hincluded Hvalid].
    rewrite gset_disj_included in Hincluded.
    apply subseteq_disjoint_union_L in Hincluded.
    destruct Hincluded as [C [-> Hdisj]].
    rewrite -gset_disj_union; [|done].
    replace ((B ∪ C) ∖ B) with C; [|set_solver].
    iMod (own_update_2 with "HA HB") as "HA"; [|done].
    apply auth_update_dealloc. 
    apply gset_disj_dealloc_empty_local_update.
  Qed.

  Lemma unallocated_update_dealloc_union A B :
    A ## B →
    ⊢ unallocated_groups_auth (A ∪ B) ∗ unallocated_groups B ==∗
      unallocated_groups_auth A.
  Proof.
    iIntros (Hdisj) "[HA HB]".
    replace (A ∪ B) with (B ∪ A) by set_solver.
    rewrite /unallocated_groups_auth -gset_op -gset_disj_union; [|done].
    iMod (own_update_2 with "HA HB") as "HA"; [|done].
    apply auth_update_dealloc. 
    by apply gset_disj_dealloc_empty_local_update.
  Qed.

  #[global] Instance saved_pred_proper `{savedPredG Σ A} n γ dq :
    Proper ((dist n) ==> (dist n))
           (@saved_pred_own Σ A _ γ dq : (A -d> iPropO Σ) -d> iPropO Σ).
  Proof.
    intros Φ Ψ Hps.
    f_equiv.
    destruct n; [apply dist_later_0| ]. 
    apply dist_later_S. eapply dist_lt; eauto.
  Qed.

  #[global] Instance saved_pred_proper' `{savedPredG Σ A} γ dq :
    Proper ((≡) ==> (≡)) (@saved_pred_own Σ A _ γ dq
                          : (A -d> iPropO Σ) -d> iPropO Σ).
  Proof. solve_proper. Qed.
  #[global] Instance si_pred_prop `{anerisG Mdl Σ} a :
    Proper ((≡) ==> (≡)) (si_pred a).
  Proof. solve_proper. Qed.

  Lemma free_ip_included A ip :
    free_ips_auth A -∗ free_ip ip -∗ ⌜ip ∈ A⌝.
  Proof.
    iIntros "HF Hip". iDestruct (own_valid_2 with "HF Hip") as %[_ Hi].
    iPureIntro.
    move: (Hi 0%nat). rewrite /= left_id.
    move => [? [/to_agree_injN /discrete
                 /leibniz_equiv_iff <- [/gset_disj_included ? _]]].
    by apply elem_of_subseteq_singleton.
  Qed.

  Lemma free_ip_dealloc A ip :
    free_ips_auth A -∗ free_ip ip ==∗ free_ips_auth (A ∖ {[ ip ]}).
  Proof.
    iIntros "HF Hip".
    iDestruct (free_ip_included with "HF Hip") as %Hip.
    replace A with ({[ ip ]} ∪ (A ∖ {[ ip ]})) at 1; last first.
    { rewrite (comm_L _ {[ _ ]}) difference_union_L
      -(comm_L _ {[ _ ]}) subseteq_union_1_L //.
      by apply elem_of_subseteq_singleton. }
    iCombine "HF" "Hip" as "H".
    iMod (own_update with "H") as "H"; last by iFrame "H".
    apply auth_update_dealloc.
    rewrite -gset_disj_union; last by set_solver.
    by apply gset_disj_dealloc_empty_local_update.
  Qed.

  Lemma free_ports_included P ip ports :
    free_ports_auth P -∗
    free_ports ip ports -∗
    ∃ ports', ⌜P !! ip = Some (GSet ports') ∧ ports ⊆ ports'⌝.
  Proof.
    iIntros "HP Hip"; rewrite /free_ports_auth /free_ports.
    iDestruct (own_valid_2 with "HP Hip") as
        %[[y [Hy1%leibniz_equiv Hy2]]%singleton_included_l Hv]
         %auth_both_valid_discrete.
    iPureIntro.
    revert Hy2; rewrite Some_included_total.
    destruct y as [ports'|].
    - eexists; split; first by rewrite Hy1.
      by apply gset_disj_included.
    - by specialize (Hv ip); rewrite Hy1 in Hv.
  Qed.

  Lemma free_ports_split ip ports ports' :
    ports ## ports' →
    free_ports ip (ports ∪ ports') ⊣⊢
    free_ports ip ports ∗ free_ports ip ports'.
  Proof.
    intros ?.
    by rewrite /free_ports -gset_disj_union //
    -own_op -auth_frag_op singleton_op.
  Qed.

  Lemma free_ports_alloc P ip ports :
    ip ∉ (dom P) →
    free_ports_auth P ==∗
    free_ports_auth (<[ ip := GSet ports ]>P) ∗ free_ports ip ports.
  Proof.
    iIntros (?) "HP"; rewrite /free_ports_auth /free_ports.
    iMod (own_update _ _ (● _ ⋅ ◯ {[ ip := (GSet ports)]}) with "HP")
      as "[HP Hip]"; last by iFrame.
    apply auth_update_alloc, alloc_singleton_local_update; last done.
    by eapply (not_elem_of_dom (D := gset ip_address)).
  Qed.

  Lemma free_ports_dealloc P ip ports :
    free_ports_auth P -∗
    free_ports ip ports ==∗
    ∃ ports', ⌜P !! ip = Some (GSet ports') ∧
              ports ⊆ ports'⌝ ∗
              free_ports_auth (<[ip := GSet (ports' ∖ ports)]> P).
  Proof.
    iIntros "HP Hip".
    iDestruct (free_ports_included with "HP Hip") as (ports') "[% %]".
    iMod (own_update_2 _ _ _
                       (● <[ip := GSet (ports' ∖ ports)]>P ⋅
                        ◯ <[ ip := GSet ∅ ]>{[ ip := (GSet ports)]})
            with "HP Hip")
      as "[? ?]".
    { apply auth_update.
      eapply insert_local_update;
        [done|eapply (lookup_singleton (M := gmap _))|].
      apply gset_disj_dealloc_local_update. }
    by iExists _; iFrame.
  Qed.

  Lemma socket_interp_alloc sag φ sis :
    sis !! sag = None →
    socket_address_group_own sag -∗
    saved_si_auth sis ==∗
    ∃ γsi, saved_si_auth (<[sag:=γsi]>sis) ∗ sag ⤇* φ.
  Proof.
    iIntros (Hnone) "Hsag Hsi".
    iMod (saved_pred_alloc φ DfracDiscarded) as (γsi) "Hsipred"; [done|].
    iMod (own_update _ _
                     (● (to_agree <$> (<[sag:=γsi]> sis)) ⋅
                      ◯ {[ sag := to_agree γsi ]}
                      : authR socket_interpUR) with "Hsi") as "[Hsi #sip]".
    { rewrite fmap_insert.
      apply auth_update_alloc, alloc_singleton_local_update; [|done].
      rewrite lookup_fmap Hnone //. }
    iModIntro. iExists _. iFrame. iExists _. iFrame "#∗".
  Qed.

  Lemma socket_interp_agree (sag1 sag2 : gset socket_address)
        ϕ ψ (sa : socket_address) x :
    sa ∈ sag1 → sa ∈ sag2 →
    sag1 ⤇* ϕ -∗ sag2 ⤇* ψ -∗ ⌜sag1 = sag2⌝ ∗ ▷ (ϕ x ≡ ψ x).
  Proof.
    iIntros (Hin1 Hin2) "Hsag1 Hsag2".
    iDestruct ("Hsag1") as (γ1) "[Hsag1 [Hγ1 Hϕ1]]".
    iDestruct ("Hsag2") as (γ2) "[Hsag2 [Hγ2 Hϕ2]]".
    iDestruct (socket_address_group_own_agree with "Hsag1 Hsag2") as %<- ;
      [ done | done | ].
    iSplit; [ done | ].
    iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hvalid.
    rewrite -auth_frag_op singleton_op in Hvalid.
    apply auth_frag_valid_1, singleton_valid in Hvalid.
    apply (to_agree_op_inv_L γ1 γ2) in Hvalid.
    rewrite Hvalid.
    iDestruct (saved_pred_agree _ _ _ _ _ x with "Hϕ1 Hϕ2") as "H".
    iExact "H".
  Qed.

  Lemma socket_interp_pred_equiv sa sag1 sag2 Φ Ψ :
    sa ∈ sag1 → sa ∈ sag2 →
    sag1 ⤇* Φ -∗ sag2 ⤇* Ψ -∗ ▷ (Φ ≡ Ψ).
  Proof.
    iIntros (Hin1 Hin2) "#H1 #H2".
    rewrite discrete_fun_equivI; iIntros (?).
    iDestruct (socket_interp_agree with "H1 H2") as "[_ $]"; done.
  Qed.

  Lemma socket_interp_own sag Φ :
    sag ⤇* Φ -∗ socket_address_group_own sag.
  Proof. by iDestruct 1 as (γ) "[Hown H]". Qed.

  Lemma alloc_evs_lookup M lbl evs :
    alloc_evs_ctx M -∗ alloc_evs lbl evs -∗ ⌜M !! lbl = Some evs⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl ?]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_exclusive_l in Hvl; [|apply _|done].
    apply leibniz_equiv in Hvl.
    rewrite lookup_fmap in Hvl.
    revert Hvl; case: (M !! lbl); intros; simplify_eq/=; done.
  Qed.

  Lemma alloc_evs_update M lbl evs evs' :
    alloc_evs_ctx M -∗
    alloc_evs lbl evs ==∗
    alloc_evs_ctx (<[lbl := evs']>M) ∗ alloc_evs lbl evs'.
  Proof.
    iIntros "H1 H2".
    iDestruct (alloc_evs_lookup with "H1 H2") as %Hlu.
    iMod (own_update_2 (A := authUR (gmapUR string (exclR aneris_eventsO)))
                       _ _ _ (● (Excl <$> <[lbl := evs']>M) ⋅
                              ◯ {[lbl := Excl evs']}) with "H1 H2") as "[$ $]";
      last done.
    apply auth_update.
    rewrite fmap_insert.
    apply: singleton_local_update; last by apply exclusive_local_update.
    rewrite lookup_fmap Hlu; done.
  Qed.

  Lemma sendon_evs_lookup M sag evs :
    sendon_evs_ctx M -∗ sendon_evs_groups sag evs -∗ ⌜M !! sag = Some evs⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H2" as "[Hsag H2]".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl ?]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_exclusive_l in Hvl; [|apply _|done].
    apply leibniz_equiv in Hvl.
    rewrite lookup_fmap in Hvl.
    revert Hvl; case: (M !! sag); intros; simplify_eq/=; done.
  Qed.

  Lemma sendon_evs_update M sag evs evs' :
    sendon_evs_ctx M -∗
    sendon_evs_groups sag evs ==∗
    sendon_evs_ctx (<[sag := evs']>M) ∗ sendon_evs_groups sag evs'.
  Proof.
    iIntros "H1 H2".
    iDestruct (sendon_evs_lookup with "H1 H2") as %Hlu.
    iDestruct "H2" as "[#Hsag H2]".
    iMod (own_update_2 (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
                       _ _ _ (● (Excl <$> <[sag := evs']>M) ⋅
                              ◯ {[sag := Excl evs']}) with "H1 H2") as "[H1 H2]".
    {
      apply auth_update.
      rewrite fmap_insert.
      apply: singleton_local_update; last by apply exclusive_local_update.
      rewrite lookup_fmap Hlu; done.
    }
    iModIntro. iFrame "#∗".
  Qed.

  Lemma receiveon_evs_lookup M sag evs :
    receiveon_evs_ctx M -∗ receiveon_evs_groups sag evs -∗ ⌜M !! sag = Some evs⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct "H2" as "[Hsag H2]".
    iDestruct (own_valid_2 with "H1 H2") as %[Hvl ?]%auth_both_valid_discrete.
    iPureIntro.
    apply singleton_included_exclusive_l in Hvl; [|apply _|done].
    apply leibniz_equiv in Hvl.
    rewrite lookup_fmap in Hvl.
    revert Hvl; case: (M !! sag); intros; simplify_eq/=; done.
  Qed.

  Lemma receiveon_evs_update M sag evs evs' :
    receiveon_evs_ctx M -∗
    receiveon_evs_groups sag evs ==∗
    receiveon_evs_ctx (<[sag := evs']>M) ∗ receiveon_evs_groups sag evs'.
  Proof.
    iIntros "H1 H2".
    iDestruct (receiveon_evs_lookup with "H1 H2") as %Hlu.
    iDestruct "H2" as "[#Hsag H2]".
    iMod (own_update_2 (A := authUR (gmapUR socket_address_group (exclR aneris_eventsO)))
                       _ _ _ (● (Excl <$> <[sag := evs']>M) ⋅
                              ◯ {[sag := Excl evs']}) with "H1 H2") as "[H1 H2]".
    {
      apply auth_update.
      rewrite fmap_insert.
      apply: singleton_local_update; last by apply exclusive_local_update.
      rewrite lookup_fmap Hlu; done.
    }
    iModIntro. iFrame "#∗".
  Qed.

  Lemma elem_of_group_unfold sa sag :
    sa ∈g sag -∗ ⌜sa ∈ sag⌝ ∗ socket_address_group_own sag.
  Proof. eauto. Qed.

  #[global] Instance elem_of_group_persistent sa sag : Persistent (sa ∈g sag).
  Proof. apply _. Qed.

  Lemma elem_of_group_eq sa sag1 sag2 :
    sa ∈g sag1 -∗ sa ∈g sag2 -∗ ⌜sag1 = sag2⌝.
  Proof.
    iIntros "[%Hsag1 H1] [%Hsag2 H2]".
    by iApply (socket_address_group_own_agree with "H1 H2").
  Qed.

  Lemma elem_of_group_neq sa1 sa2 sag1 sag2 :
    sag1 ≠ sag2 → sa1 ∈g sag1 -∗ sa2 ∈g sag2 -∗ ⌜sa1 ≠ sa2⌝.
  Proof.
    iIntros (Hneq) "[%Hsag1 H1] [%Hsag2 H2]".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite -auth_frag_op in Hvalid.
    pose proof (auth_frag_valid (A:=socket_address_groupUR)
                                (DGSets {[sag1]} ⋅ DGSets {[sag2]}))
      as [Hv _].
    apply Hv in Hvalid.
    apply disj_gsets_valid_op in Hvalid.
    destruct Hvalid as [_ [_ Hvalid]].
    iPureIntro.
    destruct (Hvalid sag1 sag2); [set_solver|set_solver| | ].
    - done.
    - set_solver.
  Qed.

  Lemma steps_lb_valid n m :
    steps_auth n -∗ steps_lb m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "Hauth Hlb".
    iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ H].
    iPureIntro. lia.
  Qed.

  Lemma steps_lb_get n :
    steps_auth n -∗ steps_lb n.
  Proof. iApply mono_nat_lb_own_get. Qed.

  Lemma steps_lb_le (n n' : nat) :
    (n' ≤ n)%nat → steps_lb n -∗ steps_lb n'.
  Proof. intros Hle. by iApply mono_nat_lb_own_le. Qed.

  Lemma steps_auth_update (n n' : nat) :
    (n ≤ n')%nat → steps_auth n ==∗ steps_auth n' ∗ steps_lb n'.
  Proof. intros Hle. by iApply mono_nat_own_update. Qed.

  Lemma steps_auth_update_S n :
    steps_auth n ==∗ steps_auth (S n).
  Proof.
    iIntros "Hauth".
    iMod (mono_nat_own_update with "Hauth") as "[$ _]"; [lia|done].
  Qed.

End resource_lemmas.
