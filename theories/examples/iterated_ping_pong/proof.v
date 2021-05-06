From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth excl cmra gmap gset auth.
From aneris.aneris_lang Require Import lifting tactics proofmode notation resources network state_interp.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre
     aneris_adequacy.
From aneris.examples.iterated_ping_pong Require Export code.
From RecordUpdate Require Import RecordSet.

Import Network.
Import String.
Import RecordSetNotations.

  Program Instance AndMon : Monoid and :=
    {| monoid_unit := True |}.

(* Network helpers *)
Section network.

  (* The network topology consists of a server and multiple clients.
     All addresses are statically known. *)
  Class NetworkTopo := mkTopo {
    n_server : socket_address;
    n_clients : gset socket_address;
    n_all := n_clients ∪ {[ n_server ]};
    addrs_disj : n_clients ## {[ n_server ]}
  }.

  Context `{!NetworkTopo}.

  (* A ping message goes from the server to some client. *)
  Definition mkPing (dest : socket_address) :=
    {| m_sender := n_server;
       m_destination := dest;
       m_protocol := IPPROTO_UDP ;
       m_body := "PING" |}.

  (* A pong message goes from some client to the server. *)
  Definition mkPong (sender : socket_address) :=
    {| m_sender := sender;
       m_destination := n_server;
       m_protocol := IPPROTO_UDP ;
       m_body := "PONG" |}.

End network.

(* Model definitions *)
Section model.

  Context `{!NetworkTopo}.

  Definition msg_trace := list message.

  Definition trace_to_gset := list_to_set (C := message_soup).

  Definition app_msg (msgs : msg_trace) (msg : message) := msgs ++ [msg].

  Notation "msgs ++_m m" := (app_msg msgs m) (at level 90, left associativity).

  (* The transition relation of the STS *)
  Inductive next : msg_trace -> msg_trace -> Prop :=
  | next_ping msgs dest :
      (* if we haven't already pinged the client *)
      not (In (mkPing dest) msgs) ->
      (* and the client address is valid *)
      dest ∈ n_clients ->
      (* then we can ping *)
      next msgs (msgs ++_m (mkPing dest))
  | next_pong msgs sender :
      (* if we have already pinged the client that's responding *)
      (In (mkPing sender) msgs) ->
      (* and the client hasn't already responded *)
      not (In (mkPong sender) msgs) ->
      (* then the client can send a pong back *)
      next msgs (msgs ++_m (mkPong sender)).

  (* TODO: add tests for transition relation *)

  Program Definition ping_pong_model : Model := {|
    model_state := msg_trace;
    model_rel := next
  |}.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
End model.

Notation "msgs ++_m m" := (app_msg msgs m) (at level 90, left associativity).

Section ghost.
  Record HandleSt := mkHandleSt {
    handle : socket_handle;
    skt : socket;
    recv : message_soup;
    sent : message_soup;
  }.

  Canonical Structure HandleStO := leibnizO HandleSt.

  Definition handle_map := gmap socket_address HandleSt.

  (* TODO: rename to something shorter *)
  (* TODO: use big_opM *)
  Definition handles_big_union `{EqDecision T} `{Countable T}
             (m : handle_map) (f : socket_address -> HandleSt -> gset T) : gset T :=
    map_fold (fun a st acc => acc ∪ (f a st)) ∅ m.

  Notation "'[∪' 'map]' a ↦ st ∈ m , e" :=
    (handles_big_union m (fun a st => e)) (at level 200, m at level 10, a, st at level 1).

  Lemma handles_big_union_insert_new `{EqDecision T} `{Countable T}
        (m : handle_map) (f : socket_address -> HandleSt -> gset T)
        (k : socket_address) (k_st : HandleSt) :
    m !! k = None ->
    ([∪ map] a ↦ st ∈ <[ k := k_st ]> m, f a st) =
    ([∪ map] a ↦ st ∈ m, f a st ) ∪ (f k k_st).
  Proof.
    intros Hnotin.
    rewrite /handles_big_union.
    rewrite map_fold_insert_L; [done | | done].
    intros a1 a2 st1 st2 S Hne Ha1 Ha2.
    set_solver.
  Qed.

  Lemma handles_big_union_insert_delete `{!EqDecision T} `{!Countable T}
        (m : handle_map) (f : socket_address -> HandleSt -> gset T)
        (k : socket_address) (k_st : HandleSt) :
    ([∪ map] a ↦ st ∈ <[ k := k_st ]> m, f a st) =
    (f k k_st) ∪ ([∪ map] a ↦ st ∈ delete k m, f a st).
  Proof.
    rewrite /handles_big_union.
    rewrite -insert_delete map_fold_insert_L.
    - set_solver.
    - intros ? ? ? ? ? ? ? ?. set_solver.
    - apply lookup_delete.
  Qed.

  Lemma elem_of_handles_big_union `{!EqDecision T} `{!Countable T}
        (m : handle_map) (f : socket_address -> HandleSt -> gset T) (x : T) :
        (x ∈ [∪ map] a ↦ st ∈ m, f a st) <-> (exists a st, m !! a = Some st /\ x ∈ f a st).
  Proof.
    induction m using map_ind; split.
    - rewrite /handles_big_union.
      rewrite map_fold_empty.
      set_solver.
    - intros [a [st [Hsome _]]].
      rewrite lookup_empty in Hsome.
      discriminate.
    - rewrite /handles_big_union.
      rewrite map_fold_insert_L; [| set_solver | done].
      rewrite elem_of_union.
      intros [Hl | Hr].
      + rewrite /handles_big_union in IHm.
        apply IHm in Hl as [a [st [Hsome Hin]]].
        exists a, st.
        rewrite lookup_insert_ne; [auto |].
        intros ->.
        rewrite H in Hsome.
        discriminate.
      + exists i, x0.
        rewrite lookup_insert; auto.
    - intros [a [st [Hsome Hf]]].
      rewrite handles_big_union_insert_delete.
      destruct (decide (a = i)) as [-> | ].
      + rewrite lookup_insert in Hsome.
        inversion Hsome; subst.
        set_solver.
      + rewrite lookup_insert_ne in Hsome; [ | auto].
        rewrite delete_notin; [ | auto].
        rewrite elem_of_union; right.
        apply IHm; eauto.
  Qed.

  Definition freeUR : ucmra :=
    authUR (gset_disjUR socket_address).

  Definition handlesUR : ucmra :=
    authUR (gmapUR socket_address (exclR HandleStO)).

  (* TODO: find out why inlining this makes typeclass search fail *)
  Definition handles_to_excl (m : handle_map) :
    gmapUR socket_address (exclR HandleStO) :=
    fmap Excl m.

  Lemma handles_to_excl_invert (m : handle_map)
        (a : socket_address) (st : HandleSt) :
    handles_to_excl m !! a = Some (Excl st) -> m !! a = Some (st).
  Proof.
    rewrite lookup_fmap.
    destruct (m !! a) as [st' | ] eqn:Heq; rewrite Heq;
      simpl; intros H; [by inversion H | discriminate].
  Qed.

  (* The messages in the trace match the local view of what's been sent *)
  Definition sent_consistent (mtrace : msg_trace) (handles : handle_map) : Prop :=
    trace_to_gset mtrace = [∪ map] a ↦ st ∈ handles, st.(sent).

  (* The local view of what's been received is a subset of the messages
     in the trace. This is because not every sent message has been received. *)
  Definition recv_consistent (mtrace : msg_trace) (handles : handle_map) : Prop :=
   ([∪ map] a ↦ st ∈ handles, st.(recv)) ⊆ trace_to_gset mtrace.

  Definition pingTokR : cmra := exclR natO.

  (* Ghost and invariant names used throughout the example *)
  Class GhostInvNames `{!NetworkTopo} := mkGhostnames {
    (* Name for the state that tracks free handles *)
    γ_free : gname;
    (* Name for the state that tracks active handles *)
    γ_handles : gname;
    (* Generate ghost names for client tokens.
       It's up to the user to define the domain ... *)
    gen_tok_name : socket_address -> option gname;
    (* ... but it should be at least all client addresses *)
    gen_tok_name_defined :
      forall (a : socket_address), a ∈ n_clients -> is_Some (gen_tok_name a);
    (* The name of the global protocol invariant *)
    inv_ns : namespace
  }.



End ghost.

Section inv.
  Context `{!NetworkTopo}.
  Context `{!GhostInvNames}.
  Context `{distG : !anerisG ping_pong_model Σ}.
  Context `{!inG Σ freeUR}.
  Context `{!inG Σ handlesUR}.
  Context `{!inG Σ pingTokR}.

  Definition handle_st_to_mapsto (a : socket_address) (st : HandleSt) : iProp Σ :=
    st.(handle) ↪[ip_of_address a] st.(skt) ∗ a ⤳ (st.(recv), st.(sent)).

  Definition free_addrs (F : gset socket_address) : iProp Σ :=
    [∗ set] a ∈ F, free_ports (ip_of_address a) {[port_of_address a]}.

  Definition mapsto_handles (hs : handle_map) : iProp Σ :=
    ([∗ map] a ↦ st ∈ hs, handle_st_to_mapsto a st).

  Definition auth_handles (hs : handle_map) : iProp Σ :=
    own γ_handles (● (handles_to_excl hs)).

  (*
   * Given a resource a ↪ (handle, skt, recv, sent):
   *   1) the socket address must be `a`
   *   2) all messages in `recv` must have `a` as destination
   *   3) all mesages in `sent` must have `a` as source
   *)
  (* TODO: make this a pure proposition *)
  Definition handle_addr_match (a : socket_address) (st : HandleSt) : iProp Σ :=
    (⌜st.(skt).(saddress) = Some a⌝ ∗
     ([∗ set] m ∈ st.(recv), ⌜m_destination m = a⌝) ∗
     ([∗ set] m ∈ st.(sent), ⌜m_sender m = a⌝))%I.

  Definition handle_addrs_match (hs : handle_map) : iProp Σ :=
    [∗ map] a ↦ st ∈ hs, handle_addr_match a st.

  Definition generic_inv (mdl_st : ping_pong_model) : iProp Σ :=
    ∃ (P F : gset socket_address) (handles : handle_map),
      (* We can split all addresses A into participating addresses P and
         free addresses F *)
      (* Both sets are disjoint *)
      ⌜P ## F⌝ ∗
      (* Ghost state that tracks free addresses, so we can pull information
         out of the invariant *)
      own γ_free (● (GSet F)) ∗
      (* The ghost state that tracks participating addresses tracks the
         right addresses *)
      ⌜dom _ handles = P⌝ ∗
      (* The authoritative part that tracks participating addresses *)
      auth_handles handles ∗
      (* The handle states are consistent with their key (address) *)
      handle_addrs_match handles ∗
      (* We have mapsto for every participating address *)
      mapsto_handles handles ∗
      (* The current state of the model *)
      frag_st mdl_st ∗
      (* Our tracking of sends is consistent with the model *)
      ⌜sent_consistent mdl_st handles⌝ ∗
      (* Our tracking of receives is consistent with the model *)
      ⌜recv_consistent mdl_st handles⌝.

  (* Generates optional ping tokens *)
  Definition ping_tok (a : socket_address) : iProp Σ :=
    match (gen_tok_name a) with
    | Some γ => own γ (Excl 0)
    | None => True
    end.

  Definition ping_pong_inv : iProp Σ :=
    ∃ (mdl_st : ping_pong_model),
      generic_inv mdl_st ∗
      (* If we have a ping token we can know that the corresponding ping
         message has been recorded in the model trace *)
      ([∗ set] a ∈ n_clients, ((ping_tok a) ∨ ⌜In (mkPing a) mdl_st⌝)%I).

  (* User-level resource indicating that the given address is free *)
  Definition ufree (a : socket_address) : iProp Σ :=
    own γ_free (◯ GSet {[ a ]}).

  (* User resource for tracking an allocated socket handle *)
  Definition uhandle (a : socket_address) (st : HandleSt) : iProp Σ :=
    own γ_handles (◯ {[ a := Excl st ]}).

  Notation "a '↪h' '(' h ',' s ',' R ',' S ')'" :=
    (uhandle a (mkHandleSt h s R S)) (at level 90).

  (* We now prove some helper lemmas that help us work with the invariant *)

  (* If we have the user free resource we can recover
     the socket free resource *)
  Lemma ufree_free (a : socket_address) (F : gset socket_address) :
    ufree a -∗
    own γ_free (● (GSet F)) -∗
    (ufree a ∗
     ⌜a ∈ F⌝ ∗
     own γ_free (● (GSet F))).
  Proof.
    iIntros "Hfrag Hauth".
    iDestruct (own_valid_2 with "Hauth Hfrag") as
        %[Helem%gset_disj_included
               %elem_of_subseteq_singleton _] %auth_both_valid_discrete.
    iFrame. done.
  Qed.

  Lemma uhandle_handles_some (a : socket_address)
                             (h : socket_handle)
                             (skt : socket)
                             (R S : gset message)
                             (handles : handle_map) :
    a ↪h (h, skt, R, S) -∗
    auth_handles handles -∗
    ⌜handles !! a = Some (mkHandleSt h skt R S)⌝.
  Proof.
    iIntros "Hfrag Hauth".
    iDestruct (own_valid_2 with "Hauth Hfrag") as
        %[Hincl Hv]%auth_both_valid_discrete.
    apply (singleton_included_exclusive_l _ _ _ _ Hv) in Hincl.
    apply leibniz_equiv in Hincl.
    apply handles_to_excl_invert in Hincl.
    by iPureIntro.
  Qed.

  (* If we have the user socket handle we can recover
     the socket mapsto resource *)
  Lemma uhandle_handle (a : socket_address)
                       (h : socket_handle)
                       (s : socket)
                       (R S : gset message)
                       (handles : handle_map) :
    a ↪h (h, s, R, S) -∗
    auth_handles handles -∗
    mapsto_handles handles -∗
    (a ↪h (h, s, R, S) ∗
     auth_handles handles ∗
     handle_st_to_mapsto a (mkHandleSt h s R S) ∗
     mapsto_handles (delete a handles) ∗
     ⌜handles !! a = Some (mkHandleSt h s R S)⌝).
  Proof.
    iIntros "Hfrag Hauth Hmapsto".
    iDestruct (uhandle_handles_some with "Hfrag Hauth") as %Hincl.
    iPoseProof (big_opM_delete _ _ _) as "Hrw"; [eassumption|].
    iDestruct ("Hrw" with "Hmapsto") as "[? ?]"; iFrame.
    by iPureIntro.
  Qed.

  (* We can simultaneously allocate a uhandle and
     the corresponding socket mapsto *)
  Lemma uhandle_alloc (a : socket_address)
                      (sh : socket_handle)
                      (s : socket)
                      (handles : handle_map)
                      (R S : message_soup) :
    ⌜a ∉ dom (gset socket_address) handles⌝ -∗
    auth_handles handles -∗
    mapsto_handles handles -∗
    sh ↪[ ip_of_address a] s -∗ a ⤳ (R, S) ==∗
    let handles' := <[ a := mkHandleSt sh s R S ]> handles in
      a ↪h (sh, s, R, S) ∗
      auth_handles handles' ∗
      mapsto_handles handles'.
  Proof.
    iIntros "%Hnotin Hauth Hsh Hmapsto Hleadsto".
    iMod (own_update _ _
           (● (handles_to_excl (<[ a := mkHandleSt sh s R S ]> handles )) ⋅
            ◯ {[ a := Excl (mkHandleSt sh s R S)]}) with "Hauth")
      as "Halloc".
    { apply auth_update_alloc.
      rewrite /handles_to_excl.
      rewrite fmap_insert.
      (* Had to supply the RA manually for some reason *)
      apply (alloc_singleton_local_update (A := exclR HandleStO));
        [ | by constructor ].
      rewrite lookup_fmap.
      assert (Hnone: handles !! a = None).
      { apply not_elem_of_dom; assumption. }
      by rewrite Hnone.
    }
    iDestruct (own_op with "Halloc") as "[Hauth Hfrag]".
    iModIntro; iFrame.
    iApply (big_sepM_insert_2 with "[Hmapsto Hleadsto] Hsh").
    iFrame. (* TODO: why can't we frame this directly in the line above. *)
   Qed.

  (* We can delete from the authoritative ufree set *)
  Lemma ufree_delete (F : gset socket_address) (a : socket_address ) :
    own γ_free (● GSet F) -∗
    ufree a ==∗
    own γ_free (● GSet (F ∖ {[ a ]})).
  Proof.
    iIntros "Hauth Hfrag".
    iMod (own_update_2 with "Hauth Hfrag");
      last by iFrame.
    apply auth_update_dealloc.
    apply gset_disj_dealloc_local_update.
  Qed.

  Lemma delete_insert_eq (m : handle_map) (i : socket_address) (x : HandleSt) :
    m !! i = Some x ->
    <[ i := x ]> (delete i m) = m.
  Proof.
    intros Hsome.
    rewrite insert_delete.
    apply insert_id; assumption.
  Qed.

  Lemma mapsto_reconstitute (sh : socket_handle)
                            (a : socket_address)
                            (skt : socket)
                            (handles : handle_map)
                            (R S : gset message) :
    ⌜handles !! a = Some (mkHandleSt sh skt R S)⌝ -∗
    sh ↪[ ip_of_address a] skt -∗ a ⤳ (R, S) -∗
    mapsto_handles (delete a handles) -∗
    mapsto_handles handles.
  Proof.
    iIntros "%Hsome Hsh Hmapsto Hleadsto".
    iDestruct (big_sepM_insert handle_st_to_mapsto
                               (delete a handles)
                               a
                               (mkHandleSt sh skt R S)
                 with "[Hsh Hmapsto Hleadsto]") as "Hmapsto'".
    - apply lookup_delete_None; auto.
    - iFrame.
    - rewrite delete_insert_eq; [iFrame | assumption].
  Qed.

  Lemma mapsto_reconstitute_new (sh : socket_handle)
                                (a : socket_address)
                                (skt : socket)
                                (handles : handle_map)
                                (R S : gset message) :
    sh ↪[ ip_of_address a] skt -∗ a ⤳ (R, S) -∗
    mapsto_handles (delete a handles) -∗
    mapsto_handles (<[ a := mkHandleSt sh skt R S ]> handles).
  Proof.
    rewrite /mapsto_handles.
    iIntros "Hsh Hmapsto Hleadsto".
    remember {| handle := sh; skt := skt; recv := R; sent := S |} as st'.
    assert (<[a:=st']> handles = <[a := st' ]> (delete a handles)) as ->.
    { rewrite insert_delete; done. }
    rewrite big_sepM_insert; [ | apply lookup_delete].
    rewrite /handle_st_to_mapsto; subst; simpl.
    iFrame.
  Qed.

  Lemma handles_to_excl_insert (handles : handle_map)
                               (a : socket_address)
                               (st : HandleSt) :
    handles_to_excl (<[a:=st]> handles) = <[a := Excl st]> (handles_to_excl handles).
  Proof.
    rewrite /handles_to_excl.
    by rewrite fmap_insert.
  Qed.

  Lemma uhandle_update (a : socket_address)
                       (handles : handle_map)
                       (st st' : HandleSt) :
    ⌜handles !! a = Some st⌝ -∗
    auth_handles handles -∗
    uhandle a st ==∗
    auth_handles (<[ a := st' ]> handles) ∗
    uhandle a st'.
  Proof.
    iIntros "%Hsome Hauth Hfrag".
    iApply own_op.
    iApply (own_update_2 with "Hauth Hfrag").
    apply auth_update.
    rewrite handles_to_excl_insert.
    rewrite -[({[_ := Excl st']})](insert_singleton _ (Excl st)).
    apply (insert_local_update _ _ _ (Excl st) (Excl st)).
    - rewrite /handles_to_excl.
      by rewrite lookup_fmap Hsome.
    - by rewrite lookup_singleton.
    - apply exclusive_local_update; done.
  Qed.

  Lemma handle_addrs_match_insert (handles : handle_map)
                                  (a : socket_address)
                                  (st st' : HandleSt) :
    handle_addrs_match handles -∗
    ⌜handles !! a = Some st⌝ -∗
    handle_addr_match a st' -∗
    handle_addrs_match (<[a := st']> handles).
  Proof.
    iIntros "Hmatch %Hsome Hmatch_st'".
    rewrite /handle_addrs_match.
    assert (handles = <[a := st]> handles) as ->.
    { rewrite insert_id; eauto. }
    do 2 rewrite big_sepM_insert_delete.
    rewrite delete_insert_delete.
    iDestruct "Hmatch" as "[_ ?]".
    iFrame.
  Qed.

  Lemma extract_ping_tok (a : socket_address)
                         (mdl : msg_trace) :
    ⌜a ∈ n_clients⌝ -∗
    ping_tok a -∗
    ([∗ set] a ∈ n_clients, ping_tok a ∨ ⌜In (mkPing a) mdl⌝) -∗
    (([∗ set] a ∈ n_clients, ping_tok a ∨ ⌜In (mkPing a) mdl⌝) ∗
     ⌜In (mkPing a) mdl⌝).
  Proof.
    iIntros "%Hin Htok Hall".
    iDestruct (big_sepS_elem_of_acc _ _ a with "Hall") as
        "[[Htok' | Hin]  Himpl]"; try done.
    - (* duplicated token: contradiction *)
      iExFalso.
      rewrite /ping_tok.
      destruct (gen_tok_name_defined a Hin) as [nm ->].
      by iDestruct (own_valid_2 with "Htok Htok'") as "%Hvalid".
    - (* ping in trace *)
      iFrame.
      iApply "Himpl"; eauto.
  Qed.

  Lemma sent_consistent_after_receive (handles : handle_map)
                                      (a : socket_address)
                                      (st st' : HandleSt)
                                      (mdl : msg_trace) :
    sent_consistent mdl handles ->
    handles !! a = Some st ->
    st.(sent) = st'.(sent) ->
    sent_consistent mdl (<[a := st']> handles).
  Proof.
    rewrite /sent_consistent.
    intros Hcons Hsome Heq.
    rewrite handles_big_union_insert_delete.
    rewrite -[handles](insert_id _ a st) in Hcons; [ | assumption].
    rewrite Hcons handles_big_union_insert_delete Heq.
    reflexivity.
  Qed.

  Lemma sent_consistent_after_send (handles : handle_map)
                                   (a : socket_address)
                                   (st st' : HandleSt)
                                   (mdl : msg_trace)
                                   (m : message) :
    sent_consistent mdl handles ->
    handles !! a = Some st ->
    st'.(sent) = st.(sent) ∪ {[ m ]} ->
    sent_consistent (mdl ++_m m) (<[a := st']> handles).
  Proof.
    rewrite /sent_consistent.
    intros Hcons Hsome Heq.
    rewrite handles_big_union_insert_delete.
    rewrite -[handles](insert_id _ a st) in Hcons; [ | assumption].
    rewrite /trace_to_gset /app_msg.
    rewrite list_to_set_app_L Heq; simpl.
    rewrite union_empty_r_L.
    assert (list_to_set mdl = sent st ∪ handles_big_union (delete a handles) (λ (_ : socket_address) (st : HandleSt), sent st)) as ->; [ | set_solver].
    rewrite /trace_to_gset in Hcons.
    rewrite handles_big_union_insert_delete in Hcons.
    set_solver.
  Qed.

  Lemma in_subseteq (m : message) (mdl : msg_trace) :
    In m mdl -> {[m]} ⊆ trace_to_gset mdl.
  Proof.
    intros Hin.
    rewrite -elem_of_subseteq_singleton
             elem_of_list_to_set
             elem_of_list_In; done.
  Qed.

  Lemma recv_consistent_after_receive (handles : handle_map)
                                      (a : socket_address)
                                      (st st' : HandleSt)
                                      (mdl : msg_trace)
                                      (m : message) :
    recv_consistent mdl  handles ->
    handles !! a = Some st ->
    st.(recv) ∪ {[m]} = st'.(recv) ->
    In m mdl ->
    recv_consistent mdl (<[a := st']> handles).
  Proof.
    rewrite /recv_consistent.
    intros Hcons Hsome Hsub Hin.
    rewrite handles_big_union_insert_delete.
    rewrite -[handles](insert_id _ a st) in Hcons; [ | assumption].
    rewrite handles_big_union_insert_delete in Hcons.
    apply union_least; [ | set_solver].
    rewrite -Hsub.
    apply union_least; [set_solver |].
    apply in_subseteq; done.
  Qed.

  Lemma recv_consistent_after_send (handles : handle_map)
                                   (a : socket_address)
                                   (st st' : HandleSt)
                                   (mdl : msg_trace)
                                   (m : message) :
    recv_consistent mdl handles ->
    handles !! a = Some st ->
    st'.(recv) = st.(recv) ->
    recv_consistent (mdl ++_m m) (<[a := st']> handles).
  Proof.
    rewrite /recv_consistent.
    intros Hcons Hsome Heq.
    rewrite /trace_to_gset /app_msg list_to_set_app.
    rewrite handles_big_union_insert_delete.
    rewrite -(delete_insert_eq handles a st) in Hcons; [ | assumption].
    rewrite handles_big_union_insert_delete in Hcons.
    rewrite delete_idemp in Hcons.
    apply union_subseteq in Hcons as [HL HR].
    rewrite /trace_to_gset in HL.
    apply union_subseteq; set_solver.
  Qed.

  Lemma recv_consistent_elem (msgs : msg_trace)
                             (handles : handle_map)
                             (a : socket_address)
                             (st : HandleSt)
                             (m : message) :
    recv_consistent msgs handles ->
    handles !! a = Some st ->
    m ∈ st.(recv) ->
    m ∈ msgs.
  Proof.
    rewrite /recv_consistent /trace_to_gset.
    intros Hcons Hsome Hin.
    rewrite <- elem_of_list_to_set.
    assert (H': m ∈ handles_big_union handles (λ (_ : socket_address) (st : HandleSt), recv st)); [ | set_solver].
    rewrite elem_of_handles_big_union; eauto.
  Qed.

  Lemma sent_consistent_elem (msgs : msg_trace)
                             (handles : handle_map)
                             (a : socket_address)
                             (st : HandleSt)
                             (m : message) :
    ⌜sent_consistent msgs handles⌝ -∗
    ⌜handles !! a = Some st⌝ -∗
    ⌜m ∈ msgs⌝ -∗
    ⌜m_sender m = a⌝ -∗
    handle_addrs_match handles -∗
    ⌜m ∈ st.(sent)⌝.
  Proof.
    rewrite /handle_addrs_match /sent_consistent.
    iIntros "%Hcons %Hsome %Hin %Hsender Hmatch".
    rewrite /trace_to_gset in Hcons.
    rewrite <- elem_of_list_to_set in Hin.
    assert (Hin': m ∈ handles_big_union handles
                    (λ (_ : socket_address) (st : HandleSt), sent st)).
    { set_solver. }
    apply elem_of_handles_big_union in Hin' as [a' [st' [Hsome' Hin']]].
    iDestruct ((big_sepM_lookup handle_addr_match handles a') with "Hmatch")
      as "(%H1 & _ & H3)"; [eauto |].
    iDestruct (big_sepS_elem_of _ _ _ Hin' with "H3") as "%Heq"; subst.
    rewrite Hsome in Hsome'.
    inversion Hsome'; auto.
  Qed.

  From aneris Require Import lib.util.

  From aneris Require Import program_logic.adequacy.
  (* Lemma socket_state_same_one σ κs k *)
  (*       (δ: aux_state (@aneris_AS ping_pong_model)) a hst: *)
  (*      state_interp σ δ κs k -∗ *)
  (*       handle hst ↪[ ip_of_address a] skt hst -∗ a ⤳ (recv hst, sent hst) -∗ *)
  (*       ⌜ match σ with *)
  (*           mkState _ c_skts c_in_use _ => *)
  (*           ∃ c_skt_map : sockets, *)
  (*                          c_skts !! ip_of_address a = Some c_skt_map *)
  (*                          ∧ (∃ (c_skt : socket) (R S : gset message), *)
  (*                               c_skt_map !! handle hst = Some (c_skt, R, S) *)
  (*                               ∧ c_skt = skt hst ∧ R = recv hst ∧ S = sent hst) *)
  (* end⌝. *)
  (* Proof. *)
  (*   iIntros "Hsi Hhan". *)
  (*   unfold state_interp, anerisG_irisG. Search aneris_state_interp. *)
  (*   iPoseProof (aneris_state_interp_socket_valid with "[$] [$]") as (hh) "%Hh". *)
  (*   destruct Hh as [Hh Hh']. *)
  (*   iPureIntro. destruct σ as [A B C D]. simpl in Hh. exists hh. *)
  (*   split; first done. by do 3 eexists. *)
  (* Qed. *)

  (* Lemma socket_state_same σ κs k st (handles: handle_map):  *)
  (*      state_interp σ κs k st -∗ *)
  (*       ([∗ map] a↦hst ∈ handles,  handle hst ↪[ ip_of_address a ] (skt hst, recv hst, sent hst)) -∗ *)
  (*       ⌜ match σ with *)
  (*           mkState _ c_skts c_in_use _ => *)
  (*             ([^ and map] a↦hst ∈ handles, *)
  (*               exists c_skt_map : sockets, *)
  (*                 c_skts !! (ip_of_address a) = Some c_skt_map /\ *)
  (*                 exists (c_skt : socket) (R S : gset message), *)
  (*                   c_skt_map !! hst.(handle) = Some (c_skt, R, S) /\ *)
  (*                   c_skt = hst.(skt) /\ *)
  (*                   R = hst.(recv) /\ *)
  (*                   S = hst.(sent)) *)
  (*         end⌝. *)
  (* Proof. *)
  (*   induction handles as [| a hst handles Hnotin IH] using map_ind; iIntros "Hst H"; destruct σ; *)
  (*    first by iPureIntro;  rewrite big_opM_empty.  *)
  (*   rewrite !big_opM_insert //. iDestruct "H" as "[H Hr]". *)
  (*   iSplit. *)
  (*   - by iPoseProof (socket_state_same_one with "Hst H") as "?". *)
  (*   - by iApply (IH with "[$]"). *)
  (* Qed.       *)

End inv.

Notation "a '↪h' '(' h ',' s ',' R ',' S ')'" :=
  (uhandle a (mkHandleSt h s R S)) (at level 90).

Section client.
  Context `{!NetworkTopo}.
  Context `{!GhostInvNames}.
  Context `{!inG Σ freeUR}.
  Context `{!inG Σ handlesUR}.
  Context `{!inG Σ pingTokR}.
  Context `{distG : !anerisG ping_pong_model Σ}.

  Definition client_si (a : socket_address) : socket_interp Σ :=
    (λ msg, (ping_tok a) ∗
            ⌜msg = mkPing a⌝ ∗
            (∃ ϕ, m_sender msg ⤇ ϕ ∗
                 ∀ m, ⌜m = mkPong a⌝ -∗ ϕ m))%I.

  Lemma client_spec (client_addr : socket_address)
                    (ip : ip_address) :
    ip = ip_of_address client_addr ->
    client_addr ∈ n_clients ->
    inv inv_ns ping_pong_inv -∗
    fixed n_all -∗
    ufree client_addr -∗
    free_ports (ip_of_address client_addr) {[ port_of_address client_addr ]} -∗
    client_addr ⤇ client_si client_addr -∗
    client_addr ⤳ (∅, ∅) -∗
    WP client #client_addr @[ip] {{ v, True }}.
  Proof.
    iIntros (-> Hin) "#Hinv #Hfixed Hufree Hfreeport #Hsi Hlt".
    rewrite /client. wp_pures.
    (* Allocate the socket *)
    wp_bind (NewSocket _ _ _)%E.
    wp_socket sh as "Hsh". wp_pures.
    (* Static bind the socket, for which we need to open the invariant *)
    wp_bind (SocketBind _ _).
    iInv inv_ns as (mdl) "> (Hgen & Htoks)" "Hclose".
    iDestruct "Hgen" as (P F handles) "(%Hdisj & Hfree_auth &
              %Hdom & Hauth_handles & #Haddrs_match & Hmapsto & Hrest)".
    assert (Hin_all: client_addr ∈ n_all) by set_solver.
    iDestruct (ufree_free with "Hufree Hfree_auth") as
        "(Hufree & %Helem & Hfree_auth)".
    wp_socketbind_static.
    (* Now close the invariant *)
    iMod (ufree_delete with "Hfree_auth Hufree") as "Hfree_auth".
    iMod (uhandle_alloc with "[] Hauth_handles Hmapsto Hsh Hlt") as
        "(Huhandle & Hauth_handles' & Hmapsto')".
    { iPureIntro; subst ; set_solver. }
    iMod ("Hclose" with "[Htoks Hfree_auth Hrest Hauth_handles' Hmapsto']") as "_".
    { iNext. iExists mdl.
      iFrame.
      iExists (P ∪ {[ client_addr ]}), (F ∖ {[ client_addr ]}), _.
      iDestruct "Hrest" as "(Hfrag & %Hsent & %Hrecv)".
      iFrame.
      repeat iSplit; try iPureIntro.
      - set_solver.
      - set_solver.
      - unfold handle_addrs_match.
        iApply big_sepM_insert.
        { apply not_elem_of_dom; set_solver. }
        iFrame "#".
        repeat iSplit; eauto.
      - unfold sent_consistent.
        rewrite handles_big_union_insert_new;
          (try apply not_elem_of_dom); set_solver.
      - unfold recv_consistent.
        rewrite handles_big_union_insert_new;
          (try apply not_elem_of_dom); set_solver.
    }
    iModIntro; wp_pures.
    wp_bind (ReceiveFrom _).

    clear mdl. (* It's ok to forget about the old state of the model *)
    iInv inv_ns as (mdl) "> (Hgen & Htoks)".
    iClear "Haddrs_match".
    clear Hdisj Hdom Helem P F handles.
    iDestruct "Hgen" as (P F handles) "(%Hdisj & Hfree_auth &
            %Hdom & Hauth_handles & #Haddrs_match & Hmapsto & Hmdl & %Hscons & %Hrcons)".
    iDestruct (uhandle_handle with "Huhandle Hauth_handles Hmapsto") as
        "(Huhandle & Hauth_handles & Hmapsto & Hmapsto_rest & %Hsome)".

    remember (udp_socket (Some client_addr) true) as skt eqn:Heq.
    iAssert (⌜ handle_st_to_mapsto client_addr {| handle := sh; skt := skt; recv := ∅; sent := ∅ |} = (sh ↪[ ip_of_address client_addr] skt ∗ client_addr ⤳ (∅, ∅)) ⌝%I) as "->".
    { iPureIntro; reflexivity. }

    wp_apply (aneris_wp_receivefrom _ _ _ _ (udp_socket (Some _) true) with "[Hmapsto]") => //.
    { iFrame "Hsi". iApply bi.later_sep_1; iNext. subst. iFrame. }

    iIntros (msg) "(Hsh&Hmsg)".
    iDestruct "Hmsg" as "[(#Hnotin & Hleadsto & Hsi_ok) | [%?]]";
      last by set_solver.
    remember (mkHandleSt sh skt {[mkPing client_addr]} ∅) as st'.
    iMod (uhandle_update _ _ _ st' with
              "[//] Hauth_handles Huhandle") as "[Hauth_handles Huhandle]".
    unfold client_si.
    iDestruct "Hsi_ok" as "(Hclienthist & Hclient & Htok & -> & Hsi_ok)".
    iDestruct (extract_ping_tok with "[//] Htok Htoks") as "[Htoks %Hping]".
    iModIntro. iSplitR "Huhandle Hsi_ok".
    { iNext. iExists mdl; iFrame.
    iExists P, F, (<[ client_addr := st' ]> handles). iFrame "∗#".
    iSplit; [by iPureIntro |].
    iSplit.
    { iPureIntro. rewrite -Hdom dom_insert_L.
      have Hindom: client_addr ∈ dom (gset socket_address) handles
        by rewrite elem_of_dom Hsome; eauto.
      set_solver. }
    iSplitR.
    { iApply handle_addrs_match_insert; eauto with iFrame.
      repeat iSplit; rewrite Heqst'; eauto.
      * by rewrite Heq.
      * by rewrite big_sepS_singleton. }
    iSplitL "Hleadsto Hmapsto_rest Hsh Hclienthist".
    { rewrite /mapsto_handles  big_sepM_insert_delete.
      rewrite /handle_st_to_mapsto Heqst'; simpl.
      rewrite union_empty_r_L.
      subst; iFrame. }
    iSplit.
    { iPureIntro.
      eapply sent_consistent_after_receive; eauto.
      rewrite Heqst'; reflexivity. }
    iPureIntro.
    eapply recv_consistent_after_receive; eauto.
    rewrite Heqst'; set_solver. }
    wp_apply wp_unSOME =>//; iIntros "_".
    wp_pures.


    clear mdl Hscons Hrcons Hping. (* It's ok to forget about the old state of the model *)
    iClear "Haddrs_match".
    clear Hdisj Hdom P F handles Hsome.

    iApply (aneris_wp_atomic_take_step_model) =>//.
    iInv inv_ns as (mdl) "> (Hgen & Htoks)" "Hclose"; iModIntro.
    iDestruct "Hgen" as (P F handles) "(%Hdisj & Hfree_auth & %Hdom & Hauth_handles & #Haddrs_match & Hmapsto & Hfrag_mdl & %Hscons & %Hrcons)".
    remember (mdl ++_m (mkPong client_addr)) as mdl'.
    iExists mdl, mdl'.

    destruct st' as [h skt' R S].
    iDestruct (uhandle_handles_some with "Huhandle Hauth_handles") as "%Hsome".
    pose proof (recv_consistent_elem _ _ _ _
                   (mkPing client_addr) Hrcons Hsome) as Hin_mdl.
    iAssert (⌜(mkPing client_addr) ∈ mdl⌝%I) as "%Hping_in".
    { iPureIntro. set_solver. }
    (* Show that (mkPong client_addr) ∉ mdl' *)
    iAssert (⌜(mkPong client_addr) ∉ mdl⌝%I) as "%Hpong_notin".
    { iIntros (contra).
      iDestruct (sent_consistent_elem with "[] [] [] [] Haddrs_match")
        as "%Hpong_in"; eauto with iFrame.
      rewrite Heqst' in Hpong_in. set_solver. }

    iFrame; iSplit.
    { iPureIntro. rewrite Heqmdl'.
      apply next_pong; rewrite <- elem_of_list_In; assumption. }

    (* Pick out socket protocol and apply wp_send *)
    iDestruct (uhandle_handle with "Huhandle Hauth_handles Hmapsto") as
          "(Huhandle & Hauth_handles & [Hmapstoph Hmapstolog] & Hmapsto_rest & _)".
    rewrite /handle_addrs_match.
    injection Heqst'. intros **; subst.
    iDestruct ((big_sepM_lookup _ _ client_addr
                               {| handle := sh;
                                  skt := udp_socket (Some client_addr) true;
                                  recv := {[mkPing client_addr]} ;
                                  sent := ∅ |}) with "Haddrs_match") as
        "(%addr_ok & _ & _)"; [done|].
    simpl in addr_ok; subst.
    iDestruct "Hsi_ok" as (ϕ) "[Hsender Hres]".
    simpl.
    wp_apply (aneris_wp_send _ ϕ _ _ _ _ _
                             (udp_socket (Some client_addr) true)
                with "[Hmapstolog Hmapstoph Hsender Hres]"); eauto.
    unfold handle_st_to_mapsto.
    +  iFrame "∗#". iModIntro. by iApply "Hres".
    + iIntros "[Hshph Hshlog] Hfrag".
      simpl.
      remember (mkHandleSt sh
                           (udp_socket (Some client_addr) true)
                           {[mkPing client_addr]}
                           {[mkPong client_addr]}) as st' eqn:Heq.
      iMod (uhandle_update _ _ _ st' with
                "[//] Hauth_handles Huhandle") as "[Hauth_handles' Huhandle']".
      assert ({| m_sender := client_addr; m_destination := n_server; m_protocol := IPPROTO_UDP; m_body := "PONG" |} = (mkPong client_addr)) as ->; [auto |].
      iAssert ((mapsto_handles (<[ client_addr := st' ]> handles)))
        with "[Hmapsto_rest Hshlog Hshph]" as "Hmapsto'".
      { rewrite Heq.
        assert ({[mkPong client_addr]} ∪ ∅ = {[mkPong client_addr]}) as ->.
        { set_solver. }
        iApply (mapsto_reconstitute_new with "[$] [$] [$]"). }
      iMod ("Hclose" with "[-]") as "_"; last done.
      iModIntro.
      rewrite /ping_pong_inv /generic_inv.
      iExists (mdl ++_m mkPong client_addr).
      iSplitR "Htoks"; last first.
      { iApply (big_sepS_impl with "Htoks").
        iModIntro.
        iIntros (x) "_ [Htok | %Hin']"; [iLeft; iFrame |].
        iRight; iPureIntro.
        apply in_or_app; auto. }
      iExists  (dom (gset socket_address) handles),
               F,
               (<[client_addr:=st']> handles).
      iFrame; iFrame "#".
      iSplitL ""; [iPureIntro; assumption |].
      iSplitL ""; [iPureIntro |].
      { rewrite dom_insert_L.
        rewrite subseteq_union_1_L; [reflexivity |].
        rewrite -elem_of_subseteq_singleton elem_of_dom; eauto. }
      iSplitL "Haddrs_match".
      { rewrite /handle_addrs_match.
        rewrite -insert_delete big_sepM_insert; [ | apply lookup_delete].
        iSplitL "".
        - rewrite /handle_addr_match Heq; simpl.
          iSplitL; [done |].
          do 2 (rewrite big_sepS_singleton); iPureIntro; done.
        - iDestruct (big_sepM_delete with "Haddrs_match") as
              "[_ ?]"; [eauto | done].
      }
      iPureIntro.
      split.
      * eapply sent_consistent_after_send;
          [assumption | eapply Hsome | set_solver ].
      * eapply recv_consistent_after_send;
          [assumption | apply Hsome | by rewrite Heq].
  Qed.
End client.

Section server.
  Context `{!NetworkTopo}.
  Context `{!GhostInvNames}.
  Context `{!inG Σ freeUR}.
  Context `{!inG Σ handlesUR}.
  Context `{!inG Σ pingTokR}.
  Context `{distG : !anerisG ping_pong_model Σ}.

  Definition server_si : socket_interp Σ :=
    (λ msg, ∃ a, ⌜a ∈ n_clients /\ msg = mkPing a⌝)%I.

  Definition set_match_list (addrs : gset socket_address) (addrs': list socket_address): Prop :=
    list_to_set addrs' = addrs.

  Fixpoint client_addrs (addrs : list socket_address) : base_lang.expr :=
    match addrs with
    | nil => list_nil
    | a :: addrs' => list_cons #a (client_addrs addrs')
    end.

  Lemma server_spec (ip : ip_address) l l':
    (set_match_list n_clients l') ->
    (is_list (map (LitV ∘ LitSocketAddress) l') l) ->
    ip = ip_of_address n_server ->
    {{{ inv inv_ns ping_pong_inv ∗
        fixed n_all ∗
        ufree n_server ∗
        n_server ⤇ server_si }}}
      server #n_server l  @[ip]
    {{{ v, RET v; True }}}.
  Proof. Admitted.

End server.

Section topo.

  Definition mkAddr ip := SocketAddressInet ip 80.
  Global Instance ping_pong_topo : NetworkTopo.
  Proof.
    apply (mkTopo (mkAddr "0.0.0.99")
                  {[ mkAddr "0.0.0.1"; mkAddr "0.0.0.2"; mkAddr "0.0.0.3" ]}).
    set_solver.
  Defined.
End topo.

Section alloc.

  Context `{NetworkTopo}.
  Context `{inG Σ freeUR}.
  Context `{!inG Σ handlesUR}.
  Context `{!inG Σ pingTokR}.

  From iris Require Import algebra.auth.

  Definition ping_tok' (f: gmap socket_address gname) (a : socket_address) : iProp Σ :=
    match (f !! a) with
    | Some γ => own γ (Excl 0)
    | None => True
    end.

  Lemma alloc_tokens (addrs: gset socket_address):
    ⊢ |==> ∃ f, ⌜ dom (gset _) f = addrs ⌝ ∧ [∗ set] addr ∈ addrs, ping_tok' f addr.
  Proof.
    induction addrs as [|x X Hnotin IH] using set_ind_L.
    { iModIntro. iExists ∅. iSplit=>//. iPureIntro; set_solver. }
    iStartProof.
    iMod (own_alloc (Excl 0)) as (γ) "Hγ" =>//.
    iMod IH as (f) "[%Hdom H]".
    iExists (<[x:=γ]>f).
    iModIntro; iSplit.
    { iPureIntro. set_solver. }
    iApply big_sepS_insert=>//; iSplitL "Hγ".
    - by rewrite /ping_tok' lookup_insert.
    - iApply (big_sepS_impl with "H").
      iIntros "!>" (y Hy) "H".
      rewrite /ping_tok' lookup_insert_ne =>//.
      by set_solver.
  Qed.

  Lemma toto `{!inG Σ (X:ucmra)} γ (A B: X):
    A ≡ B ->
    own γ A ⊣⊢ own γ B.
  Proof. by move=> ->. Qed.

  Lemma union_singletons A `{GhostInvNames}:
    own γ_free (◯ GSet A) ⊢
        own proof.γ_free (◯ ([^op set] x ∈ A, GSet {[x]})).
  Proof.
    iIntros "H".
    rewrite toto => //.
    f_equiv.
    induction A as [|x X Hnotin IH] using set_ind_L.
    { by rewrite big_opS_empty. }
    rewrite big_opS_insert //. rewrite -IH -gset_disj_union //; last set_solver.
  Qed.

  Lemma alloc_gnames: (⊢ |==> ∃c: GhostInvNames,
                            ([∗ set] a ∈ n_all, ufree a) ∗
                            own γ_free (● GSet n_all) ∗
                            auth_handles ∅ ∗ own γ_handles (◯ (handles_to_excl ∅)) ∗
                            ([∗ set] a ∈ n_clients, ping_tok a)
                      ).
  Proof.
    iMod (own_alloc (● GSet n_all ⋅ ◯ GSet n_all)) as (γ_free) "[Hfree Hfree']".
    { apply auth_both_valid_2; eauto. by compute. }
    iMod (alloc_tokens n_clients) as (f_tokens) "[%Htokdom Htoks]".
    iMod (own_alloc (● handles_to_excl ∅ ⋅ ◯ handles_to_excl ∅)) as (γ_handles) "Hh".
    { apply auth_both_valid_2; eauto. vm_compute. done. }

    iModIntro.
    iExists {| gen_tok_name := fun a => f_tokens !! a ;
               γ_free := γ_free ;
               γ_handles := γ_handles ;
               inv_ns := nroot .@ "iterated_ping_pong"
            |}.
    iFrame. rewrite !own_op. iFrame.
    rewrite /ufree -big_opS_own; last set_solver.
    rewrite -big_opS_commute1; last set_solver.
    by rewrite -union_singletons.

    Unshelve.
    - intros a Hin. apply elem_of_dom. congruence.
  Qed.

  Definition protomap `{GhostInvNames} `{anerisG ping_pong_model Σ}: socket_address -> socket_interp Σ :=
    fun a => if decide (a = mkAddr "0.0.0.99") then server_si else client_si a.

End alloc.

Section runner.

  Definition invN := nroot .@ "ping_pong".

  Context `{!inG Σ freeUR}.
  Context `{!inG Σ handlesUR}.
  Context `{!inG Σ pingTokR}.
  Context `{!GhostInvNames}.
  Context `{distG : !anerisG ping_pong_model Σ}.


  Lemma runner_spec :
    {{{ n_server ⤇ server_si
        ∗ ([∗ set] a ∈ n_clients, a ⤇ client_si a)
        ∗ fixed n_all
        ∗ ([∗ set] a ∈ n_all, free_ip (ip_of_address a))
        ∗ ([∗ set] a ∈ n_all, a ⤳ (∅, ∅))
        ∗ ([∗ set] a ∈ n_all, ufree a)
        ∗ inv inv_ns ping_pong_inv
    }}}
      runner @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(Hserver & Hprotos & #Hfixed & Hips & Hlts & Hufrees & #Hinv) Hkont". rewrite /runner.
    rewrite /n_clients /ping_pong_topo.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.1") with "Hips") as "[Hn1 Hips]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.2") with "Hips") as "[Hn2 Hips]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.3") with "Hips") as "[Hn3 Hips]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.99") with "Hips") as "[Hns _]"; first set_solver.

    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.1") with "Hlts") as "[Hlt1 Hlts]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.2") with "Hlts") as "[Hlt2 Hlts]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.3") with "Hlts") as "[Hlt3 Hlts]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.99") with "Hlts") as "[Hlts _]"; first set_solver.

    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.1") with "Hprotos") as "[Hp1 Hprotos]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.2") with "Hprotos") as "[Hp2 Hprotos]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.3") with "Hprotos") as "[Hp3 _]"; first set_solver.

    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.1") with "Hufrees") as "[Hu1 Hufrees]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.2") with "Hufrees") as "[Hu2 Hufrees]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.3") with "Hufrees") as "[Hu3 Hufrees]"; first set_solver.
    iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.99") with "Hufrees") as "[Hus _]"; first set_solver.

    do 3 (wp_makeaddress; wp_let). (* Lots of time in typeclasses eauto 🐌 *)

    wp_bind (list_nil).
    wp_apply wp_list_nil. done. iIntros (vv1 Hvv1).
    wp_bind (list_cons _ vv1).
    wp_apply wp_list_cons. done. iIntros (vv2 Hvv2).
    wp_bind (list_cons _ vv2).
    wp_apply wp_list_cons. done. iIntros (vv3 Hvv3).
    wp_bind (list_cons _ vv3).
    wp_apply wp_list_cons. done. iIntros (vv4 Hvv4).

    clear Hvv1 vv1 Hvv2 vv2 Hvv3 vv3.
    pose proof Hvv4 as HH.
    do 3 destruct Hvv4 as [? [-> Hvv4]]. rewrite Hvv4. rewrite Hvv4 in HH.

    wp_pures.

    wp_bind (Start _ _).
    wp_apply (aneris_wp_start {[80%positive]} with "[-]"); eauto. iFrame.
    iSplitR "Hp1 Hu1 Hlt1"; first last.
    { iModIntro. iIntros "Hfp".
      wp_apply (client_spec with "[$] [] [$] [$] [$] [-]"); eauto.
      set_solver. }
    iModIntro. wp_pures.
    wp_apply (aneris_wp_start {[80%positive]} with "[-]"); auto. iFrame.
    iSplitR "Hp2 Hu2 Hlt2"; first last.
    { iModIntro. iIntros "Hfp".
      wp_apply (client_spec with "[$] [] [$] [$] [$] [-]"); eauto.
      set_solver. }
    iModIntro. wp_pures.
    wp_apply (aneris_wp_start {[80%positive]} with "[-]"); auto. iFrame.
    iSplitR "Hp3 Hu3 Hlt3"; first last.
    { iModIntro. iIntros "Hfp".
      wp_apply (client_spec with "[$] [] [$] [$] [$] [-]"); eauto.
      set_solver. }

    iModIntro. wp_pures.
    wp_apply (aneris_wp_start {[80%positive]} with "[-]"); auto. iFrame.

    iSplitL "Hkont"; first by iApply "Hkont".
    iModIntro. iIntros "_".
    iApply (server_spec _ _ [mkAddr "0.0.0.1"; mkAddr "0.0.0.2"; mkAddr "0.0.0.3"] with "[-]"); eauto.
    { set_solver. }
  Qed.

End runner.

Lemma big_sepS_map_inverse `{Σ: gFunctors} `{Countable A} `{Countable B} (X: gset A)
        (f: A -> B) (g: B -> A) (P: A -> iProp Σ):
    (forall x, g (f x) = x) ->
    (([∗ set] x ∈ set_map f X, P (g x)) ⊣⊢ [∗ set] x ∈ X, P x)%I.
Proof.
  intros Hinv. induction X as [| x X Hnotin IH] using set_ind_L.
  { iStartProof. iSplit; iIntros "?"; done. }
  iStartProof.
  rewrite set_map_union_L.
  rewrite big_sepS_union; try set_solver; last first.
  - have Hfinj: forall x y, f x = f y -> x = y.
    { move=> a b Hab. have: g (f a) = g (f b) by f_equal. congruence. }
    move=> a Hs Hr.
    rewrite -> elem_of_map in Hs. destruct Hs as (x' & Heq & Hs).
    rewrite -> elem_of_map in Hr. destruct Hr as (y & Heq' & Hr).
    subst. apply Hfinj in Heq'. set_solver.
  - rewrite big_sepS_union; last set_solver.
    rewrite set_map_singleton_L !big_sepS_singleton. rewrite Hinv.
    iSplit; iIntros "[??]"; iFrame; by iApply IH.
Qed.


Lemma big_sepS_duh `{Σ: gFunctors} `{Countable A} `{Countable B} (X Y: gset A)
         (P: A -> iProp Σ):
  X = Y ->
    (([∗ set] x ∈ X, P x) ⊣⊢ [∗ set] x ∈ Y, P x)%I.
Proof.
  iIntros (Heq). rewrite Heq. reflexivity.
Qed.

Section simulation.
  (* Bug in coq! please report to coq.inria.fr *)
  (* Definition mkAddrPair (a: ip_address): ip_address * (gset _) := (a, {[ 80 ]}). *)

  (* Definition mkAddrPair (a: ip_address): ip_address * (gset port) := (a, {[ 80%positive ]}). *)
  Definition mkAddrPair (a: ip_address): ip_address * (gset port) := (a, ∅).

  Definition n_all_piu: ports_in_use :=
    list_to_map [ mkAddrPair "0.0.0.1"; mkAddrPair "0.0.0.2"; mkAddrPair "0.0.0.3"; mkAddrPair "0.0.0.99" ].

  Definition initial_state: state aneris_lang := {|
    state_heaps := {["system" := ∅]};
    state_sockets := {["system" := ∅]};
    state_ports_in_use := n_all_piu;
    state_ms := ∅ |}.

  (* Notice we're using the previously-declared NetworkTopo.
     This is required as an implicit argument of ping_pong_model. *)

  Definition simulates (ex : execution_trace aneris_lang)
                       (sm : auxiliary_trace (@aneris_AS ping_pong_model)) : Prop :=
    exists (conf : cfg aneris_lang) (curr_st : ping_pong_model) (mh: messages_history) curr_δ,
      exec_ends_in ex conf /\
      auxtr_ends_in sm curr_δ /\
      curr_st = curr_δ.(aneris_AS_model) ∧
      mh = curr_δ.(aneris_AS_mhist) ∧
      match (snd conf) with
        mkState _ c_skts c_in_use _ =>
        exists (P F : gset socket_address) (handles : handle_map),
        P ## F /\
        (* The tracked addresses match physical addresses on the network *)
        (* P ∪ F = n_all /\ *)
        (* The participating addresses are the keys in the handle map *)
        dom _ handles = P /\
        (* The participating sockets are allocated *)
        (* ([^ and map] a ↦ hst ∈ handles, hst.(skt).(saddress) = Some a) /\ *)
        (* (* Free addresses really are free *) *)
        (* ([^ and set] a ∈ F, *)
        (*   match c_in_use !! (ip_of_address a) with *)
        (*     None => True *)
        (*   | Some ports => port_of_address a ∉ ports *)
        (*   end) /\ *)
        (* Our tracking of sends is consistent with the model *)
        sent_consistent curr_st handles /\
        (* Our tracking of receives is consistent with the model *)
        recv_consistent curr_st handles /\
        forall a, a ∈ P -> ∃ hst, handles !! a = Some hst ∧
              (forall m, m ∈ hst.(sent) -> (m.(m_sender) = a ∧ m ∈ mh.2))
      end.

  Definition runner_expr: expr aneris_lang := mkExpr "system" runner.


  From stdpp Require Import sets.
  From aneris Require Import lib.util.

  (* Lemma big_sepS_gset_map Φ Ψ X f g: *)
  (*  forall x, f (g x) = x *)
  (*   ([∗ set] x ∈ X, Φ x) -∗ *)
  (*   [∗ set] x ∈ (gset_map f X), Ψ (g x). *)

  Class ppG Σ := { free_ur_inG:> inG Σ freeUR
                 ; handles_inG:> inG Σ handlesUR
                 ; pingtok_inG:> inG Σ pingTokR }.

  Definition myΣ: gFunctors := #[ anerisΣ ping_pong_model
                                ; GFunctor freeUR
                                ; GFunctor handlesUR
                                ; GFunctor pingTokR ].

  Instance subG_ppΣ {Σ}: subG myΣ Σ -> ppG Σ.
  Proof. solve_inG. Qed.

  (* Instance whatamidoing: anerisG myΣ ping_pong_model. *)
  (* Proof. Admitted. *)

  From stdpp Require Import fin_sets.
  From aneris.aneris_lang Require Import adequacy.

  Theorem ping_pong_simulation :
    continued_simulation
      simulates
      (singleton_exec (([runner_expr], initial_state)))
      (@singleton_auxtr _ (@aneris_AS ping_pong_model)
         {| aneris_AS_mhist := (∅,∅) ; aneris_AS_model := []:ping_pong_model |}).
  Proof.
    eapply (simulation_adequacy
              myΣ _
              NotStuck
              {[ "0.0.0.1"; "0.0.0.2"; "0.0.0.3"; "0.0.0.99" ]}
              n_all);
      eauto; try set_solver.
    { admit. (* finite branching *) }
    { move => a Ha. unfold n_all, n_clients in Ha. set_solver. }
    move=> Haneris. iStartProof.
    iMod alloc_gnames as (?) "(Hufrees&Hfreeall&Hah&Hfh&Htok)".
    iModIntro.
    iExists (λ v, ∃ w, ⌜v = mkVal "system" w⌝ ∗ (fun _ => True) w)%I, protomap.
    iIntros "#Hfixed Hprotos Hlts Hfrees Hsystemnode Hfragst".

    iMod (inv_alloc inv_ns _ ping_pong_inv with "[-Hlts Hufrees Hsystemnode Hprotos Hfrees]") as "#Hinv".
    { iNext. rewrite /ping_pong_inv. iExists ∅. iSplitR "Htok".
      - rewrite /generic_inv. iExists ∅, n_all, ∅. iFrame.
        iSplit. iPureIntro; set_solver.
        iSplit. iPureIntro; set_solver.
        iSplitL "". { unfold handle_addrs_match. done. }
        iSplitL "". { unfold mapsto_handles. eauto. }
        iSplit; eauto.
      - iApply (big_sepS_impl with "Htok") =>//.
          by iIntros "!>" (a Ha) "Hpk"; iLeft.
    }
    iSplitL.
    - iApply fupd_wp.

      iRevert "Hsystemnode".
      iAssert (aneris_wp_def "system" ⊤ runner ⊤)%I with "[-]" as "H"; first last.
      { rewrite /aneris_wp_def. iIntros "Hnode". iSpecialize ("H" with "Hnode").
        iExact "H". }
      rewrite -aneris_wp_eq.
      iAssert (WP runner @["system"] {{⊤}})%I with "[-]" as "H"; last by eauto.
      wp_apply (runner_spec with "[-]"); eauto.

      iDestruct (big_sepS_delete _ _ (mkAddr "0.0.0.99") with "Hprotos") as "[Hserverproto Hprotos]"; first set_solver.
      rewrite {1}/protomap /=.
      destruct (decide (mkAddr "0.0.0.99" = mkAddr "0.0.0.99")); [|done].
      iFrame "# Hserverproto". iSplitL "Hprotos".
      { have ->: {[mkAddr "0.0.0.1"; mkAddr "0.0.0.2"; mkAddr "0.0.0.3"]} =
          (n_all ∖ {[mkAddr "0.0.0.99"]}) by rewrite /n_all; set_solver.
        iApply (big_sepS_impl with "Hprotos").
        iModIntro. iIntros (x Hx) "H".
        rewrite /protomap. destruct (decide (x = mkAddr "0.0.0.99")) as [->|];
                             first by set_solver. done. }
      iFrame.
      iPoseProof (big_sepS_map_inverse _ mkAddr ip_of_address with "Hfrees") as "H"=> //.
      assert (Heq: n_all = set_map mkAddr (C := gset _) {["0.0.0.1"; "0.0.0.2"; "0.0.0.3"; "0.0.0.99"]}).
      { unfold mkAddr, n_all, n_clients, ping_pong_topo, n_server. set_solver. }
      rewrite Heq. iExact "H".
    - do 2 iModIntro.
      iIntros (ex atr δ' c' κs' Hval Hexst Hauxst Hexend Hauxend).
      iIntros (Hsim Hnotstuck) "Hsi Hposts".
      iInv inv_ns as "> Hgi" "Hclose".

      unfold simulates.
      unfold ping_pong_inv.
      iDestruct "Hgi" as (mdl) "[Hgi ?]".
      iDestruct "Hgi" as (P F handles) "(%&?&%&?&Hhandles&Hm&Hfrag&%&%)".

      unfold handle_addrs_match, handle_addr_match,
        mapsto_handles, handle_st_to_mapsto.
      iAssert (⌜ ∀ a : socket_address,
                    a ∈ dom (gset socket_address) handles
                    → ∃ hst : HandleSt,
                      handles !! a = Some hst
                      ∧ (∀ m : message, m ∈ sent hst ->
                      m_sender m = a ∧ m ∈ (aneris_AS_mhist δ').2) ⌝)%I as "%".
      { iIntros (a Ha). apply elem_of_dom in Ha as [hst Ha]. iExists hst.
        iSplit; first done. iIntros (m Hm).

        iDestruct (big_sepM_delete _ handles _ hst Ha with "Hhandles")
          as "[[? [? H]] _]".
        iDestruct (big_sepM_delete _ handles _ hst Ha with "Hm")
          as "[[_ Hahist] _]".
        iSplit; first by
            iDestruct (big_sepS_delete _ (sent hst) m Hm with "H") as "[? _]".
        iDestruct (aneris_state_interp_sent_mapsto_agree with "Hahist Hsi")
          as "%Hx". rewrite <- Hx in *.
        iPureIntro.

        unfold messages_sent_from in Hx. destruct δ'. simpl in *.
        set_solver.
      }

      unfold mapsto_handles, handle_st_to_mapsto.

      iAssert (⌜δ'.(aneris_AS_model)  = mdl ⌝)%I with "[Hsi Hfrag]" as "%".
      { iApply (aneris_state_interp_model_agree with "Hsi Hfrag").  }
      subst.

      iApply (fupd_mask_weaken ∅); first set_solver. iIntros "_ !>".

      (* iPoseProof (socket_state_same with "[$] [$]") as "%Hsame". *)
      iPureIntro. eexists c', δ'.(aneris_AS_model), δ'.(aneris_AS_mhist), δ'.
      split. eauto using exec_extend_ends_in.
      split. eauto using auxtr_extend_ends_in.
      split. done.
      split. done.
      destruct c'.2.
      eexists _, F, handles.
      do 4 (split; eauto).
  Admitted.

End simulation.
