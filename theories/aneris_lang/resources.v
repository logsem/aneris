From iris.algebra Require Import auth gmap frac agree coPset gset frac_auth ofe.
From iris.base_logic Require Export own gen_heap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Export helpers lang notation tactics network.
From stdpp Require Import fin_maps gmap.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Record node_gnames := Node_gname {
  heap_name : gname;
  heap_meta_name : gname;
  socket_name : gname;
  socket_meta_name : gname;
}.

Definition node_gnamesO := leibnizO node_gnames.
Definition system_state_mapUR : ucmraT := gmapUR ip_address (agreeR node_gnamesO).

Definition socket_interpR : cmraT :=
  authR (gmapUR socket_address (agreeR (leibnizO gname))).

Instance system_state_mapUR_unit : Unit (gmap ip_address (agree node_gnames)) :=
  (∅ : gmap ip_address (agree node_gnames)).
Global Instance system_state_core_id (x : system_state_mapUR) : CoreId x.
Proof. apply _. Qed.

Definition socket_interp Σ := message -d> iPropO Σ.

(** The system CMRA. *)
Class distG Σ := DistG {
  dist_invG :> invG Σ;
  dist_mapG :> inG Σ (authR system_state_mapUR);
  dist_map_name : gname;
  dist_heapG :> gen_heapPreG loc ground_lang.val Σ;
  (* network *)
  dist_socketG :> gen_heapPreG socket_handle (socket * message_soup * message_soup) Σ;
  dist_freeipsG :> inG Σ (authUR (gset_disjUR ip_address));
  dist_freeips_name : gname;
  dist_freeportsG :> inG Σ (authUR (gmapUR ip_address (gset_disjUR port)));
  dist_freeports_name : gname;
  dist_siG :> inG Σ socket_interpR;
  dist_si_name : gname;
  dist_fixedG :> inG Σ (agreeR (gsetUR socket_address));
  dist_fixed_name : gname;
  dist_savedPredG :> savedPredG Σ message;
}.

Arguments gen_heap_name {_ _ _ _ _} _ : assert.
Arguments gen_meta_name {_ _ _ _ _} _ : assert.

Definition gen_heap_loc_instance γ γ' `{distG Σ} :=
  GenHeapG loc ground_lang.val _ _ _ _ _ _ γ γ'.

Definition gen_heap_soc_instance γ γ' `{distG Σ} :=
  GenHeapG socket_handle (socket * message_soup * message_soup) _ _ _ _ _ _ γ γ'.

Section Definitions.
  Context `{dG : distG Σ}.

  Definition mapsto_node_def (ip : ip_address) (x : node_gnames) :=
    own (dist_map_name) (◯ {[ ip := to_agree x ]} : auth system_state_mapUR).
  Definition mapsto_node_aux : seal (@mapsto_node_def). by eexists. Qed.
  Definition mapsto_node := unseal mapsto_node_aux.
  Definition mapsto_node_eq : @mapsto_node = @mapsto_node_def :=
    seal_eq mapsto_node_aux.

  Global Instance mapsto_node_persistent n x : Persistent (mapsto_node n x).
  Proof. rewrite mapsto_node_eq /mapsto_node_def. apply _. Qed.

  (** Ghost state for the heap of a given node *)
  Definition mapsto_l n l q v :=
    (∃ γ's, mapsto_node n γ's ∗
            mapsto (hG := gen_heap_loc_instance
                            (heap_name γ's)
                            (heap_meta_name γ's)) l q v)%I.

  (** Ghost state for the sockets of a given node *)
  Definition mapsto_s n h q (s: socket * message_soup * message_soup) :=
    (∃ γ's, mapsto_node n γ's ∗
            mapsto (hG := gen_heap_soc_instance
                            (socket_name γ's)
                            (socket_meta_name γ's)) h q s)%I.
End Definitions.

Notation "n n↦ x" := (mapsto_node n x)
                       (at level 20, format "n  n↦  x") : uPred_scope.

Open Scope uPred_scope.

(** Ghost state notations for heap and socket resources *)

(** Heaps n↦ *)
Notation "l ↦[ n ]{ q } v" := (mapsto_l n l q v)
  (at level 20, q at level 50, format "l  ↦[ n ]{ q }  v") : uPred_scope.
Notation "l ↦[ n ] v" := (l ↦[n]{1} v) (at level 20) : uPred_scope.
Notation "l ↦[ n ]{ q } -" := (∃ v, l ↦[n]{q} v)%I
  (at level 20, q at level 50, format "l  ↦[ n ]{ q }  -") : uPred_scope.
Notation "l ↦[ n ] -" := (l ↦[n]{1} -)%I (at level 20) : uPred_scope.

(** Sockets s↦ *)
Notation "h s↦[ n ]{ q } z" := (mapsto_s n h q z)
  (at level 20, q at level 50, format "h  s↦[ n ]{ q }  z") : uPred_scope.
Notation "h s↦[ n ] z" := (mapsto_s n h 1 z) (at level 20) : uPred_scope.

(** Lookup stored socket interpretation γ↦ *)
Notation "a γ↦ γ" :=
  (own (A:=socket_interpR)
       dist_si_name (◯ {[ a := (to_agree γ) ]})) (at level 20) : uPred_scope.

(* For some reason, Coq cannot find these RAs, so we define them explicitly *)
Definition ownS γ (m : gmap ip_address node_gnames) `{distG Σ} :=
  own (A := authR system_state_mapUR) γ (● (to_agree <$> m)).

Definition ownF (f : gset socket_address) `{distG} :=
  own dist_fixed_name (to_agree f).

Global Instance mapsto_n_timeless
       `{distG Σ} (n : ip_address) v : Timeless (n n↦ v).
Proof. rewrite mapsto_node_eq /mapsto_node_def. apply _. Qed.

Global Instance mapsto_l_timeless
       `{distG Σ} (n : ip_address) l q v : Timeless (mapsto_l n l q v).
Proof.
  rewrite /mapsto_l /Timeless.
  iIntros ">H". iDestruct "H" as (γ's) "(H1 & H2)".
  iExists γ's. iFrame.
Qed.

Lemma mapsto_node_agree `{distG Σ} n γs γs' :
  n n↦ γs -∗ n n↦ γs' -∗ ⌜γs = γs'⌝.
Proof.
  apply wand_intro_r.
  rewrite /ownS mapsto_node_eq -own_op own_valid discrete_valid.
  f_equiv=> /auth_frag_proj_valid /=. rewrite singleton_op singleton_valid.
  apply (agree_op_invL' (A := node_gnamesO)).
Qed.

Lemma node_in_map `{distG Σ} n γ's (m : gmap ip_address node_gnames) :
  ⊢ (n n↦ γ's -∗ ownS dist_map_name m -∗ ⌜m !! n = Some γ's⌝)%I.
Proof.
  iIntros "H1 H2".
  iCombine "H2" "H1" as "H".
  rewrite /ownS mapsto_node_eq -own_op own_valid.
  iDestruct "H" as %HvalidR. iPureIntro.
  revert HvalidR.
  rewrite auth_both_valid.
  rewrite singleton_included_l=> -[[y [Hlookup Hless]] Hvalid].
  assert (Hvalidy := lookup_valid_Some _ n y Hvalid Hlookup).
  revert Hlookup.
  rewrite lookup_fmap fmap_Some_equiv=> -[v' [Hl Heq]]. revert Hless Heq.
  rewrite Some_included_total.
  destruct (to_agree_uninj y Hvalidy) as [y' <-].
  rewrite to_agree_included.
  intros Heq Heq'%(to_agree_inj y' v').
  apply leibniz_equiv in Heq.
  apply leibniz_equiv in Heq'.
    by simplify_eq.
Qed.

Global Instance mapsto_s_fractional `{distG Σ} (n : ip_address) h q z :
  AsFractional (mapsto_s n h q z) (λ q, mapsto_s n h q z) q.
Proof.
  constructor; first trivial. intros p p'. rewrite /mapsto_s. iSplit.
  - iDestruct 1 as (?) "[#? Hmap]".
    iDestruct (fractional_split with "Hmap") as "[Hmap Hmap']".
    iSplitL "Hmap"; iExists _; eauto.
  - iDestruct 1 as "[Hmap Hmap']". iDestruct "Hmap" as (?) "[#Hn1 Hmap]".
    iDestruct "Hmap'" as (?) "[#Hn2 Hmap']".
    iDestruct (mapsto_node_agree with "Hn1 Hn2") as %->.
    iExists _. iFrame "#"; iFrame.
Qed.

Definition IsNode `{distG Σ} n := (∃ γs, n n↦ γs)%I.
Global Instance IsNode_persistent `{distG Σ} n : Persistent (IsNode n).
Proof. apply _. Qed.

Lemma exists_IsNode `{distG Σ} n γs : n n↦ γs -∗ IsNode n.
Proof. iIntros "?". by iExists _. Qed.

Global Opaque IsNode.

(** Fixed socket end-points in the system *)

Definition Fixed `{distG Σ} A := ownF A.

Lemma ownF_agree `{distG Σ} A B : Fixed A -∗ Fixed B -∗ ⌜A = B⌝.
Proof.
  iIntros "HA HB".
  by iDestruct (own_valid_2 with "HA HB") as %?%agree_op_invL'.
Qed.

(** Socket interpretations a ⤇ Φ *)

Global Instance saved_pred_proper `{savedPredG Σ A} n γ:
  Proper ((dist n) ==> (dist n)) (@saved_pred_own Σ A _ γ : (A -d> iPropO Σ) -d> iPropO Σ).
Proof.
  intros Φ Ψ Hps.
  f_equiv.
  destruct n; first done.
    by apply dist_S.
Qed.

Global Instance saved_pred_proper' `{savedPredG Σ A} γ:
  Proper ((≡) ==> (≡)) (@saved_pred_own Σ A _ γ : (A -d> iPropO Σ) -d> iPropO Σ).
Proof.
  apply ne_proper => n. apply _.
Qed.

Definition si_pred `{distG Σ} a (Φ : socket_interp Σ) : iProp Σ :=
  (∃ γ, a γ↦ γ ∗ saved_pred_own γ Φ)%I.

Global Instance si_pred_prop `{distG Σ} a : Proper ((≡) ==> (≡)) (si_pred a).
Proof.
  intros x y Heq.
  apply exist_proper => z; f_equiv.
  by rewrite Heq.
Qed.

Notation "a ⤇ Φ" := (si_pred a Φ) (at level 20).

(** Free IP addresses *)

Definition FreeIPs_ctx `{distG Σ} (F : gset ip_address) :=
  own dist_freeips_name (● GSet F).

Definition FreeIP `{distG Σ} (ip : ip_address) :=
  own dist_freeips_name (◯ GSet {[ ip ]}).

Lemma is_FreeIP `{distG Σ} F ip :
  FreeIPs_ctx F -∗ FreeIP ip -∗ ⌜ip ∈ F⌝.
Proof.
  iIntros "HF Hip". iDestruct (own_valid_2 with "HF Hip") as %[_ Hi].
  iPureIntro.
  move: (Hi 0%nat). rewrite /= left_id.
  move => [? [/to_agree_injN /discrete /leibniz_equiv_iff <- [/gset_disj_included ? _]]].
  by apply elem_of_subseteq_singleton.
Qed.

Lemma Use_FreeIP `{distG Σ} F ip :
  FreeIPs_ctx F -∗ FreeIP ip ==∗ FreeIPs_ctx (F ∖ {[ ip ]}).
Proof.
  iIntros "HF Hip".
  iDestruct (is_FreeIP with "HF Hip") as %Hip.
  replace F with ({[ ip ]} ∪ (F ∖ {[ ip ]})) at 1; last first.
  { rewrite (comm_L _ {[ _ ]}) difference_union_L
    -(comm_L _ {[ _ ]}) subseteq_union_1_L //.
    by apply elem_of_subseteq_singleton. }
  iCombine "HF" "Hip" as "H".
  iMod (own_update with "H") as "H"; last by iFrame "H".
  apply auth_update_dealloc.
  rewrite -gset_disj_union; last by set_solver.
  by apply gset_disj_dealloc_empty_local_update.
Qed.

Lemma FreeIps_alloc `{inG Σ (authUR (gset_disjUR ip_address))}
      (F : gset ip_address) :
  ⊢ |==> ∃ γ, own γ (● GSet F) ∗ [∗ set] ip ∈ F, own γ (◯ GSet {[ ip ]}).
Proof.
  iMod (own_alloc (● GSet ∅)) as (γ) "HM"; first by apply auth_auth_valid.
  iAssert (|==>
             ∃ M : gset ip_address,
               (⌜elements M ≡ₚ elements F⌝)
                 ∗ own γ (● GSet M) ∗ [∗ set] ip ∈ M, own γ (◯ GSet {[ ip ]}))%I
    with "[HM]" as "HF".
  { pose proof (NoDup_elements F) as Hnd.
    iInduction (elements F) as [|a l] "IHl".
    - iModIntro. iExists ∅.
      rewrite big_sepS_empty. iFrame.
      by iPureIntro.
    - inversion Hnd as [|? ? ? Hrd']; subst.
      iMod ("IHl" $! Hrd' with "HM") as (M HMl) "[HM HML]"; iFrame.
      assert (a ∉ M) as Hnm.
      { by rewrite -elem_of_elements HMl. }
      iMod (own_update _ _ (● GSet ({[a]} ∪ M) ⋅ ◯ GSet {[a]}) with "HM")
        as "[HM Ha]".
      { apply auth_update_alloc.
        apply gset_disj_alloc_empty_local_update; last by set_solver. }
      iModIntro.
      iExists ({[a]} ∪ M); iFrame.
      iSplit; first by iPureIntro; rewrite elements_union_singleton // HMl.
      rewrite big_sepS_insert; last done. iFrame. }
  iMod "HF" as (M HMF) "[? ?]".
  replace M  with F; first by iModIntro; iExists _; iFrame.
  apply elem_of_equiv_L => x.
  rewrite -!elem_of_elements.
  rewrite -elem_of_list_permutation_proper; eauto.
Qed.

Definition FreePorts_ctx `{distG Σ} (P : gmap ip_address (gset_disjUR port)) :=
  own dist_freeports_name (● P).

Definition FreePorts `{distG Σ} (ip : ip_address) (ports : gset port) :=
  own dist_freeports_name (◯ ({[ ip := (GSet ports)]})).

Lemma FreePorts_included `{distG Σ} P ip ports :
  FreePorts_ctx P -∗ FreePorts ip ports -∗
    ∃ ports', ⌜P !! ip = Some (GSet ports') ∧ ports ⊆ ports'⌝.
Proof.
  iIntros "HP Hip"; rewrite /FreePorts_ctx /FreePorts.
  iDestruct (own_valid_2 with "HP Hip") as
      %[[y [Hy1%leibniz_equiv Hy2]]%singleton_included_l Hv]%auth_both_valid.
  iPureIntro.
  revert Hy2; rewrite Some_included_total.
  destruct y as [ports'|].
  - eexists; split; first by rewrite Hy1.
    by apply gset_disj_included.
  - by specialize (Hv ip); rewrite Hy1 in Hv.
Qed.

Lemma FreePorts_distribute `{distG Σ} ip ports ports' :
  ports ## ports' →
  FreePorts ip (ports ∪ ports') ⊣⊢ FreePorts ip ports ∗ FreePorts ip ports'.
Proof.
  intros ?.
  by rewrite /FreePorts -gset_disj_union // -own_op -auth_frag_op singleton_op.
Qed.

Lemma FreePorts_alloc `{distG Σ} P ip ports :
  ip ∉ (dom (gset _) P) →
  FreePorts_ctx P ==∗ FreePorts_ctx (<[ ip := GSet ports ]>P) ∗ FreePorts ip ports.
Proof.
  iIntros (?) "HP"; rewrite /FreePorts_ctx /FreePorts.
  iMod (own_update _ _ (● _ ⋅ ◯ {[ ip := (GSet ports)]}) with "HP")
    as "[HP Hip]"; last by iFrame.
  apply auth_update_alloc, alloc_singleton_local_update; last done.
  by eapply (not_elem_of_dom (D := gset ip_address)).
Qed.

Lemma FreePorts_dealloc `{distG Σ} P ip ports :
  FreePorts_ctx P -∗ FreePorts ip ports ==∗
    ∃ ports', ⌜P !! ip = Some (GSet ports') ∧ ports ⊆ ports'⌝ ∗
      FreePorts_ctx (<[ip := GSet (ports' ∖ ports)]> P).
Proof.
  iIntros "HP Hip"; rewrite /FreePorts_ctx /FreePorts.
  iDestruct (FreePorts_included with "HP Hip") as (ports') "[% %]".
  iMod (own_update_2 _ _ _
          (● <[ip := GSet (ports' ∖ ports)]>P ⋅
           ◯ <[ ip := GSet ∅ ]>{[ ip := (GSet ports)]}) with "HP Hip")
    as "[? ?]".
  { apply auth_update.
    eapply insert_local_update;
      [done|eapply (lookup_singleton (M := gmap _))|].
    apply gset_disj_dealloc_local_update. }
  by iExists _; iFrame.
Qed.

(** Definitions for the global state invariant *)

Definition gnames_coherence (γmap : gmap ip_address node_gnames)
           (heaps : gmap ip_address heap) (sockets : gmap ip_address sockets) :=
  dom (gset ip_address) γmap = dom (gset ip_address) heaps ∧
  dom (gset ip_address) γmap = dom (gset ip_address) sockets.

Definition IPs (P : ports_in_use) := dom (gset ip_address) P.

(* Addresses with interpretations are bound. *)
Definition socket_interp_coherence `{distG Σ} (P : ports_in_use) :=
  (∃ si A,
    (* the addresses in A are also in the domain of ips *)
    ⌜∀ a, a ∈ A → ip_of_address a ∈ IPs P⌝ ∗
    (* for all addresses in the system, being in si means either having a
       Fixed interpretation (a ∈ A) or being dynamically bound. *)
    ⌜∀ a, (ip_of_address a ∈ IPs P) →
      (a ∈ dom (gset socket_address) si ↔
       a ∈ A ∨ (a ∉ A ∧ ∀ ps, P !! ip_of_address a = Some ps → port_of_address a ∈ ps))⌝ ∗
      Fixed A ∗
      own (A:=socket_interpR) dist_si_name (● si) ∗
      ([∗ set] s ∈ (dom (gset socket_address) si), ∃ φ, s ⤇ φ))%I.

(* The local state of each node *)
Definition local_state_interp `{distG Σ}
      (σ : state) (ip : ip_address) (x : node_gnames) :=
  (∃ (h : heap) (Sn : sockets),
      (* there should be a heap *)
      ⌜state_heaps σ !! ip = Some h⌝ ∗
      (* there should be a socket map *)
      ⌜state_sockets σ !! ip = Some Sn⌝ ∗
      (* its a valid node *)
      ip n↦ x ∗
      (* the state owns the authoritative part of the heaps *)
      gen_heap_ctx (hG := gen_heap_loc_instance (heap_name x) (heap_meta_name x)) h ∗
      gen_heap_ctx (hG := gen_heap_soc_instance (socket_name x) (socket_meta_name x)) Sn ∗
     (* we own half of the resource for all the sockets to disallow
       'fabricating' receiving messages *)
      ([∗ map] h↦s ∈ Sn, h s↦[ip]{1/2} s)
  )%I.

(* The ports of all bound addresses are in ips *)
Definition bound_ports_coherence (S : sockets) (Piu : ports_in_use) :=
  ∀ h s a P R T, S !! h = Some (s, R, T) →
               saddress s = Some a →
               Piu !! ip_of_address a = Some P →
               (port_of_address a) ∈ P.

Definition socket_handlers_coherence (Sn : sockets)  :=
  ∀ h h' s s' R R' T T',
    Sn !! h = Some (s, R, T) →
    Sn !! h' = Some (s', R', T') →
    is_Some (saddress s) → saddress s' = saddress s →
    h' = h.

(* Received messages at a socket are in the message soup *)
Definition socket_messages_coherence (Sn : sockets) (M : message_soup) :=
  ∀ h s R T a,
    Sn !! h = Some (s, R, T) →
    saddress s = Some a →
     (∀ m, m ∈ R → m_destination m = a ∧ m ∈ M) ∧
     (∀ m, m ∈ T → m_sender m = a ∧ m ∈ M).

(* ips adresses of each nodes are disjoint *)
Definition socket_addresses_coherence (Sn: sockets) (ip: ip_address) :=
  ∀ h s R T a,
    Sn !! h = Some (s, R, T) →
    saddress s = Some a →
    ip_of_address a = ip.

Definition network_sockets_coherence
    (S : gmap ip_address sockets) M P :=
  ∀ (ip : ip_address) (Sn : sockets),
    S !! ip = Some Sn →
    (* the network should be coherent wrt. to the node n *)
    bound_ports_coherence Sn P ∧
    socket_handlers_coherence Sn ∧
    (* the messages received should be coherent wrt. to node n *)
    socket_messages_coherence Sn M ∧
    socket_addresses_coherence Sn ip.

 Definition message_received_at `{distG Σ}
   (S : gmap ip_address sockets) (m : message) (a: socket_address) :=
   ∃ Sn h s R T,
     S !! (ip_of_address a) = Some Sn ∧
     Sn !! h = Some (s, R, T) ∧
     saddress s = Some a ∧
     m ∈ R.

Definition message_received `{distG Σ} (S : gmap ip_address sockets) (m : message) :=
  ∃ a, message_received_at S m a.

Definition network_messages_coherence
           `{distG Σ} (S : gmap ip_address sockets) (M : message_soup) :=
  ([∗ set] m ∈ M,
   (* either m is governed by a protocol and the network owns the resources *)
     (∃ (Φ : socket_interp Σ), (m_destination m) ⤇ Φ ∗ ▷ Φ m) ∨
   (* or m has been delivered *)
     ⌜message_received S m⌝)%I.

Definition network_coherence `{distG Σ} S M P :=
  (⌜network_sockets_coherence S M P⌝ ∗ network_messages_coherence S M)%I.

Definition FipPiu `{distG Σ} σ :=
  (∃ Fip Piu, (⌜dom (gset _) Piu ## Fip ∧
               (∀ ip, ip ∈ Fip → state_ports_in_use σ !! ip = Some ∅) ∧
               (∀ ip, ip ∈ Fip → state_heaps σ !! ip = None ∧
                                 state_sockets σ !! ip = None) ∧
               (∀ ip P, Piu !! ip = Some (GSet P) →
                        ∃ Q, (state_ports_in_use σ) !! ip = Some Q ∧ P ## Q )⌝)
                ∗ FreeIPs_ctx Fip ∗ FreePorts_ctx Piu)%I.

(* global state interpretation *)
Global Instance distG_irisG `{distG Σ} :
  irisG aneris_lang Σ :=
  {|
    iris_invG := _;
    state_interp σ κ _ :=
      (
        ∃ (m : gmap ip_address node_gnames),
          ⌜gnames_coherence m (state_heaps σ) (state_sockets σ)⌝ ∗
           socket_interp_coherence (state_ports_in_use σ) ∗
           ownS dist_map_name m ∗
           ([∗ map] n ↦ γs ∈ m, local_state_interp σ n γs) ∗
           FipPiu σ ∗
           network_coherence
           (state_sockets σ) (state_ms σ) (state_ports_in_use σ)
      )%I;
    fork_post _ := True%I;
  |}.

Global Opaque iris_invG.
