From iris.algebra Require Import auth gmap frac agree coPset gset frac_auth ofe.
From iris.base_logic Require Export own gen_heap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import viewshifts saved_prop gen_heap.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.proofmode Require Import tactics.
From aneris.aneris_lang Require Export helpers lang notation tactics network resources.
From stdpp Require Import fin_maps gmap.
From RecordUpdate Require Import RecordSet.
Set Default Proof Using "Type".

Import uPred.
Import Network.
Import RecordSetNotations.

Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl : core.
Local Hint Constructors head_step : core.
Local Hint Resolve alloc_fresh : core.
Local Hint Resolve to_of_val : core.

 Ltac ddeq k1 k2 :=
    destruct (decide (k1 = k2)); subst;
    repeat match goal with
     | Hyp : context[ (<[_:=_]>_) !! _ ] |- _ =>
       rewrite lookup_insert in Hyp || (rewrite lookup_insert_ne in Hyp; last done);
       simplify_eq /=
     | Hyp : is_Some _ |- _ => destruct Hyp
     | |- context[ (<[_:=_]>_) !! _ ] =>
       rewrite lookup_insert || (rewrite lookup_insert_ne; last done);
       simplify_eq /=
     |  H1 : ?x = ?z, Heq : ?x = ?y |- _ =>
        rewrite Heq in H1; simplify_eq /=; try eauto
     | Hdel : context[ delete ?n ?m !! ?n = _] |- _ =>
            rewrite lookup_delete in Hdel; simplify_eq /=
     end.

Section GhostStateLemmas.
  Context `{distG Σ}.

  (** Inversion lemmas on local state interpretation of a given node *)

  Lemma node_in_state_heaps n γ's (m : gmap ip_address node_gnames) σ :
    m !! n = Some γ's →
    ([∗ map] n' ↦ γ's ∈ m, local_state_interp σ n' γ's) ⊢
   ⌜∃ (h: heap), (state_heaps σ) !! n = Some h⌝.
  Proof.
    iIntros (Hninm) "Hmap".
    iDestruct (big_sepM_lookup (local_state_interp σ) m n _ with "[Hmap]") as "Hl";
      first done; iFrame.
    iDestruct "Hl" as (h s p) "(% & _)". iPureIntro; by exists h.
  Qed.

  Lemma node_in_state_sockets n γ's (m : gmap ip_address node_gnames) σ :
    m !! n = Some γ's →
    ([∗ map] n' ↦ γ's ∈ m, local_state_interp σ n' γ's) ⊢
    ⌜∃ (S: sockets), (state_sockets σ) !! n = Some S⌝.
  Proof.
    iIntros (Hninm) "Hmap".
    iDestruct (big_sepM_lookup (local_state_interp σ) m n _ with "[Hmap]") as "Hl";
      first done; iFrame.
    iDestruct "Hl" as (??) "(_ & % & _ & _)". eauto.
  Qed.

   Lemma node_local_state n γ's m (σ : state) :
    m !! n = Some γ's →
    ([∗ map] n' ↦ x ∈ m, local_state_interp σ n' x) ⊢
   local_state_interp σ n γ's ∗
    [∗ map] n' ↦ x ∈ (delete n m), local_state_interp σ n' x.
  Proof.
    iIntros (Hinm) "Hmap".
      by rewrite -(big_sepM_delete (local_state_interp σ) m n).
  Qed.

  (** Lemmas about updating a component of the local_state of a node  *)

  Lemma map_local_state_i_update_heaps n m h (σ : state) :
    ([∗ map] n' ↦ x ∈ (delete n m), local_state_interp σ n' x) ⊢
    [∗ map] n' ↦ x ∈ (delete n m), local_state_interp {|
                                     state_heaps := <[n:=h]>(state_heaps σ);
                                     state_sockets := state_sockets σ;
                                     state_ports_in_use := state_ports_in_use σ;
                                     state_ms := state_ms σ;
                                     |} n' x.
  Proof.
    erewrite (big_sepM_mono (local_state_interp σ) (local_state_interp _)).
    - iIntros "Hmap"; iFrame.
    - intros k x Hdel. ddeq k n.
      by rewrite /local_state_interp lookup_insert_ne; last done.
  Qed.

  Lemma map_local_state_i_update_sockets n m S (σ : state) :
    ([∗ map] n' ↦ x ∈ (delete n m), local_state_interp σ n' x) ⊢
    [∗ map] n' ↦ x ∈ (delete n m), local_state_interp {|
                                     state_heaps := state_heaps σ;
                                     state_sockets := <[n:=S]> (state_sockets σ);
                                     state_ports_in_use := state_ports_in_use σ;
                                     state_ms := state_ms σ;
                                     |} n' x.
  Proof.
    erewrite (big_sepM_mono (local_state_interp σ) (local_state_interp _)).
    - iIntros "Hmap"; iFrame.
    - intros k x Hdel. ddeq k n.
      by rewrite /local_state_interp lookup_insert_ne; last done.
  Qed.

  Lemma map_local_state_i_update m σ P M :
    ([∗ map] n ↦ x ∈ m, local_state_interp σ n x) ⊢
      [∗ map] n ↦ x ∈ m, local_state_interp {|
                          state_heaps := state_heaps σ;
                          state_sockets := state_sockets σ;
                          state_ports_in_use := P;
                          state_ms := M;
                           |} n x.
  Proof. rewrite /local_state_interp; simpl. iIntros "H". iFrame. Qed.

  Lemma node_local_state_rev n γ's m (σ : state) :
    m !! n = Some γ's →
    local_state_interp σ n γ's ⊢
    ([∗ map] n' ↦ x ∈ (delete n m), local_state_interp σ n' x) -∗
     [∗ map] n' ↦ x ∈ m, local_state_interp σ n' x.
  Proof.
    iIntros (Hinm) "Hl Hmap".
    iDestruct (big_sepM_insert (local_state_interp σ)
                               (delete n m) n γ's with "[Hl Hmap]") as "HP".
    - apply lookup_delete.
    - iFrame.
    - apply insert_id in Hinm.
        by rewrite insert_delete Hinm.
  Qed.

(** Lemmas on socket_interpretation predicates *)

  Lemma si_pred_agree a Φ Ψ x :
    a ⤇ Φ -∗ a ⤇ Ψ -∗ ▷ (Φ x ≡ Ψ x).
  Proof.
    iIntros "#H1 #H2".
    iDestruct "H1" as (γ) "[H1 H1']".
    iDestruct "H2" as (γ') "[H2 H2']".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite -auth_frag_op singleton_op in Hvalid.
    apply singleton_valid in Hvalid.
    apply (agree_op_invL' γ γ') in Hvalid.
    rewrite Hvalid.
    iDestruct (saved_pred_agree _ _ _ x with "H1' H2'") as "H".
    iExact "H".
  Qed.

  Lemma si_pred_equiv a Φ Ψ :
    a ⤇ Φ -∗ a ⤇ Ψ -∗ ▷ (Φ ≡ Ψ).
  Proof.
    iIntros "#H1 #H2".
    iDestruct "H1" as (γ) "[H1 H1']".
    iDestruct "H2" as (γ') "[H2 H2']".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite -auth_frag_op singleton_op in Hvalid.
    apply singleton_valid in Hvalid.
    apply (agree_op_invL' γ γ') in Hvalid.
    rewrite Hvalid discrete_fun_equivI. iIntros (?).
      by iDestruct (saved_pred_agree with "H1' H2'") as "H".
  Qed.

  Lemma find_fixed_socket_interp a A ips :
    a ∈ A →
    Fixed A -∗ socket_interp_coherence ips -∗ ∃ Φ, a ⤇ Φ.
  Proof.
    iIntros (HaA) "#HA Hsoccoh".
    iDestruct "Hsoccoh" as (si fx HA Hdom) "(#Hsi & Hfix & #Hdyn)".
    iDestruct (ownF_agree with "HA Hsi") as %?; subst.
    iDestruct (big_sepS_elem_of (A:=socket_address) with "Hdyn") as "$".
      by rewrite (Hdom _ (HA _ HaA)); left.
  Qed.

  Lemma network_messages_sepM_later (S : gmap ip_address sockets) (M : message_soup) :
    ([∗ set] m ∈ M,
      (∃ (Φ : socket_interp Σ), (m_destination m) ⤇ Φ ∗ Φ m) ∨
      ⌜message_received S m⌝) ⊢
      ([∗ set] m ∈ M,
       (∃ (Φ : socket_interp Σ), (m_destination m) ⤇ Φ ∗ ▷ Φ m) ∨
       ⌜message_received S m⌝).
  Proof.
    iIntros "H". rewrite big_sepS_mono; first done.
    iIntros (? ?) "[H | H]".
    - iDestruct "H" as (?) "[? ?]". iLeft. iExists _. by iFrame.
    - by iRight.
  Qed.

  Lemma network_coherence_later S M P :
    ⌜network_sockets_coherence S M P⌝ ∗
     ([∗ set] m ∈ M,
      (∃ (Φ : socket_interp Σ), (m_destination m) ⤇ Φ ∗ Φ m) ∨ ⌜message_received S m⌝)
     ⊢ network_coherence S M P.
  Proof.
    iIntros "H". iDestruct "H" as "($ & H)".
    by iDestruct (network_messages_sepM_later S M with "H") as "H".
  Qed.

  Lemma mapsto_s_update v v' E
     (S: sockets) (h: socket_handle)
     (ip: ip_address)  γs :
    let hG := gen_heap_soc_instance (socket_name γs) (socket_meta_name γs) in
    S !! h = Some v →
    ⊢ (ip n↦ γs ∗
      gen_heap_ctx S ∗
       ([∗ map] h0 ↦ v0 ∈ S, h0 s↦[ip]{1/2} v0) ∗
       mapsto h (1/2) v) -∗
        |={E}=> gen_heap_ctx (<[h:=v']> S) ∗
         ([∗ map] h0 ↦ v0 ∈ (<[h:=v']> S), h0 s↦[ip]{1/2} v0) ∗
         h s↦[ip]{1/2} v'.
  Proof.
    destruct γs.
    iIntros (hG Hs) "(#Hn & Hctx & Hshs & Hs)".
    iDestruct (big_sepM_delete _ S with "Hshs") as "[Hs' Hshs]"; first done.
    iDestruct "Hs'" as ([??]) "(#Hn' & Hs')".
    iDestruct (mapsto_node_agree with "Hn Hn'") as %Heq.
    simplify_eq /=. iClear "Hn'". iCombine "Hs" "Hs'" as "Hs".
    iMod (gen_heap_update _ h v v' with "Hctx Hs") as "(Hctx & Hs)".
    iAssert (h s↦[ip]{1} v') with "[Hs Hn]" as "(Hs & Hs')".
    { iExists _. iFrame "#". iFrame. }
    iDestruct (big_sepM_insert with "[Hs' Hn $Hshs]") as "Hshs"; try done.
    apply lookup_delete.
    rewrite insert_delete.
      by iFrame.
  Qed.

  Lemma message_received_at_coherence S M P a m ip Sn h s R T:
    network_sockets_coherence S M P →
    S !! ip = Some Sn →
    Sn !! h = Some (s, R, T) →
    saddress s = Some a →
    message_received_at S m a →
    m ∈ R.
  Proof.
    intros HsCoh HS Hh Hs Hm.
    destruct (HsCoh ip Sn HS) as (_ & HshCoh & _ & HsaddrCoh).
    destruct Hm as (Sn' & h' & s' & R' & T' & HS' & Hh' & Hs' & Hm').
    assert (saddress s = saddress s'). { by rewrite -Hs' in Hs. }
    set (ip' := ip_of_address a).
    destruct (decide (ip' = ip)); simplify_eq /=.
    - assert (h' = h). { eauto using HshCoh. } set_solver.
    - destruct (HsCoh ip' Sn' HS') as (_ & _ & _ & HsaddrCoh').
      specialize (HsaddrCoh h s R T a Hh Hs).
      specialize (HsaddrCoh' h' s' R' T' a Hh' Hs').
      set_solver.
  Qed.

  (** Network components coherence lemmas *)

  Lemma FiuPiu_new_ip σ1 ip Fip Piu ports:
    (state_heaps σ1) !! ip = None →
    (state_sockets σ1) !! ip = None →
    dom (gset ip_address) Piu ## Fip →
    (∀ ip, ip ∈ Fip → state_ports_in_use σ1 !! ip = Some ∅) →
    (∀ ip, ip ∈ Fip → state_heaps σ1 !! ip = None ∧ state_sockets σ1 !! ip = None) →
    (∀ ip (P: gset positive), Piu !! ip = Some (GSet P) →
       ∃ Q : gset positive, state_ports_in_use σ1 !! ip = Some Q ∧ P ## Q) →
    ip ∈ Fip →
    FreeIPs_ctx (Fip ∖ {[ip]}) -∗
    FreePorts_ctx (<[ip:=GSet ports]> Piu) -∗
    FipPiu
    {|
      state_heaps := <[ip:=∅]> (state_heaps σ1);
      state_sockets := <[ip:=∅]> (state_sockets σ1);
      state_ports_in_use := state_ports_in_use σ1;
      state_ms := state_ms σ1 |}.
  Proof.
    iIntros (??? HFip ? HPiu ?) "H1 H2".
    iExists _, _; iFrame. iPureIntro; simpl; repeat split.
    - rewrite dom_insert ; set_solver.
    - intros ? ?; apply HFip; set_solver.
    - ddeq ip0 ip; set_solver.
    - ddeq ip0 ip; set_solver.
    - intros ip0 Q HipQ. ddeq ip0 ip.
      -- rewrite HFip //. eexists; split; eauto. set_solver.
      -- by eapply HPiu.
  Qed.

  Lemma network_messages_coherence_new_ip σ1 ip :
    (state_sockets σ1) !! ip = None →
    network_messages_coherence (state_sockets σ1) (state_ms σ1) -∗
    network_messages_coherence (<[ip:=∅]> (state_sockets σ1)) (state_ms σ1).
  Proof.
    iIntros (Hnone) "H".
    iApply big_sepS_mono; last done.
    iIntros (??) "[H |H]"; first by iLeft.
    iDestruct "H" as (a h Sn' s R T) "%".
    iRight. iPureIntro. exists a, h, Sn', s, R, T.
    ddeq (ip_of_address a) ip; set_solver.
  Qed.

  Lemma socket_messages_coherence_insert (Sn : sockets) M h s :
    socket_messages_coherence Sn M  →
    socket_messages_coherence (<[h:=(s, ∅, ∅)]> Sn) M.
  Proof. intros Hh h' **. ddeq h h'; first by set_solver. eauto using Hh. Qed.

  Lemma socket_interp_coherence_insert P Pa a A:
    a ∈ A →
    P !! ip_of_address a = Some Pa →
    port_of_address a ∉ Pa →
    Fixed A -∗
    socket_interp_coherence P -∗
    socket_interp_coherence (<[ip_of_address a:={[port_of_address a]} ∪ Pa]> P).
  Proof.
    iIntros (???) "Hf HsiCoh".
    iDestruct "HsiCoh" as (si fx Hfx Hdms) "(#Hfx & Hsi & Hsis)".
    iDestruct (ownF_agree with "Hf Hfx") as %?; subst A.
        rewrite /socket_interp_coherence.
        iExists _,_. iFrame; iFrame "#". iPureIntro. split; intros b.
        * intros Hb. specialize (Hfx _ Hb).
          rewrite /IPs. by rewrite dom_insert elem_of_union; right.
        * rewrite /IPs dom_insert elem_of_union.
          intros Hb. rewrite Hdms; last first.
        { destruct (decide (a = b)); subst; first by apply Hfx.
          destruct Hb as [Hb|]; last done. apply elem_of_singleton in Hb.
          rewrite Hb. by apply Hfx. }
         split; intros [|[Hnb Hdm]]; auto; right; (split; first done).
          ** destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
             *** intros P'. rewrite Heq. rewrite lookup_insert. intros; simplify_eq.
                 apply elem_of_union_r. apply Hdm. by rewrite -Heq.
             *** intros P'. rewrite lookup_insert_ne //. apply Hdm.
          ** destruct (decide (ip_of_address a = ip_of_address b)) as [Heq|].
             *** intros P'. rewrite Heq in Hdm. rewrite lookup_insert in Hdm.
                 match goal with
                 | H: port_of_address a ∉ ?P |- _ =>
                   specialize (Hdm ({[port_of_address a]} ∪ P) eq_refl)
                 end.
                 apply elem_of_union in Hdm. destruct Hdm as [Hdm | Hdm].
          ++ apply elem_of_singleton in Hdm. destruct a, b. simpl in *; by subst.
          ++ rewrite -Heq. by intros; simplify_eq.
             *** rewrite lookup_insert_ne in Hdm; done.
  Qed.

  (** coherence preservation for socket allocation *)

  Lemma bound_ports_coherence_insert_new
        (Sn : sockets) (P : ports_in_use) h s :
    Sn !! h = None →
    saddress s = None →
    bound_ports_coherence Sn P →
    bound_ports_coherence (<[h:=(s, ∅, ∅)]> Sn) P.
  Proof. intros ?? HbpCoh h' **. ddeq h' h. eauto using HbpCoh. Qed.

  Lemma socket_handlers_coherence_insert (Sn : sockets) h s :
    saddress s = None →
    socket_handlers_coherence Sn →
    socket_handlers_coherence (<[h:=(s, ∅, ∅)]> Sn).
  Proof.
    intros ? ? h1 h2 **. ddeq h2 h1; ddeq h1 h; ddeq h2 h; eauto. Qed.

  Lemma socket_addresses_coherence_insert (Sn : sockets) h s n :
    saddress s = None →
    socket_addresses_coherence Sn n →
    socket_addresses_coherence (<[h:=(s, ∅, ∅)]> Sn) n.
  Proof. intros ? ? h' **; ddeq h' h; eauto. Qed.

  Lemma network_sockets_coherence_insert_new
        (S : gmap ip_address sockets) (Sn : sockets) M (P : ports_in_use) n h s :
    S !! n = Some Sn →
    Sn !! h = None →
    saddress s = None →
    network_sockets_coherence S M P →
    network_sockets_coherence (<[n:=<[h:=(s, ∅, ∅)]> Sn]> S) M P.
  Proof.
    intros HS HhNone HsNone HnetCoh.
    intros n' Sn' HSn.
    ddeq n' n.
    - specialize (HnetCoh n Sn HS) as (HBpCoh & HshCoh & HmrCoh & HsaCoh).
      eauto 424 using
            bound_ports_coherence_insert_new,
            socket_handlers_coherence_insert,
            socket_messages_coherence_insert,
            socket_addresses_coherence_insert.
    - specialize (HnetCoh n' Sn' HSn) as (HBpCoh & HmrCoh); done.
  Qed.

  Lemma message_received_insert_new S m Sn n h s:
    S !! n = Some Sn →
    Sn !! h = None →
    message_received S m →
    message_received (<[n:=<[h:=(s, ∅, ∅)]> Sn]> S) m.
  Proof.
    intros HSn HhNone (a' & Sn' & h' & s' & R' & T' & HSn' & Hh' & Ha' & HmR').
    ddeq (ip_of_address a') n; exists a'.
    - ddeq h' h; simplify_eq /=.
      exists  (<[h:=(s, ∅, ∅)]> Sn), h', s', R',  T'.
      rewrite lookup_insert. repeat split; try done. by rewrite lookup_insert_ne.
    - exists Sn', h', s', R', T'. rewrite lookup_insert_ne; try done.
  Qed.

  Lemma network_messages_coherence_insert_new
        (M : message_soup) (S : gmap ip_address sockets) (Sn : sockets) n h z :
    S !! n = Some Sn →
    Sn !! h = None →
    network_messages_coherence S M ⊢
     network_messages_coherence (<[n:=<[h:=(z, ∅, ∅)]>Sn]> S) M.
  Proof.
    iIntros (??) "Hsent". rewrite /network_messages_coherence.
    rewrite big_sepS_mono; first done.
    iIntros (??) "[Htt | % ]".
    - by iLeft.
    - iRight. iPureIntro. by apply message_received_insert_new.
  Qed.

  Lemma network_coherence_insert_new S M (P : ports_in_use) Sn n h z :
    S !! n = Some Sn →
    Sn !! h = None →
    saddress z = None →
    network_coherence S M P ⊢
     network_coherence (<[n:=<[h:=(z, ∅, ∅)]> Sn]> S) M P.
  Proof.
    iIntros (? ? ?) "(% & Hmsg)". iSplitR.
    - iPureIntro. by apply network_sockets_coherence_insert_new.
    - by iDestruct (network_messages_coherence_insert_new with "Hmsg") as "Hmsg".
  Qed.

  (** coherence preservation for socket binding *)

  Lemma bound_ports_coherence_insert_bind
     (P: ports_in_use) (Sn : sockets) (P_a : gset port)
     (h : socket_handle) (skt : socket) (a: socket_address) :

    (* facts about ports and the ip address a *)
    P !! ip_of_address a = Some P_a →
    (* network in the previous state is coherent *)
    bound_ports_coherence Sn P →
    (* goal: *)
    bound_ports_coherence
      (<[h:=(skt <| saddress := (Some a) |>, ∅, ∅)]> Sn)
      (<[ip_of_address a:={[port_of_address a]} ∪ P_a]> P).
  Proof.
    iIntros (HP HbpsCoh).
    intros h' s' a' R' T' P' Hsh' Hskt' HP'.
    destruct (decide (h' = h)); subst.
    - rewrite lookup_insert in Hsh'; simplify_eq /=.
      rewrite lookup_insert in HP'; by set_solver.
    - rewrite lookup_insert_ne in Hsh'; last done.
      destruct (decide ((ip_of_address a') = (ip_of_address a))).
      + rewrite e in HP'. rewrite lookup_insert in HP'. simplify_eq /=.
        destruct (decide (port_of_address a' = port_of_address a)).
        * set_solver.
        * apply elem_of_union_r. eapply HbpsCoh; try done. rewrite -e in HP. set_solver.
      + rewrite lookup_insert_ne in HP'; last done. eapply HbpsCoh; try done.
  Qed.



  (* state_ports_in_use σ1 !! ip_of_address a = Some P  *)
  (* port_of_address a ∉ P0 *)
  (* S !! ipa = Sn *)


   Lemma socket_handlers_coherence_insert_bind
    (Sn : sockets)
    (h : socket_handle) (s : socket) (a: socket_address) :
    ( ∀ h' s' R' T' a',
        Sn !! h' = Some (s', R', T') →
        saddress s' = Some a' →
        port_of_address a' ≠ port_of_address a ) →
    socket_handlers_coherence Sn →
    socket_handlers_coherence
    (<[h:=(s <| saddress ::= constructor (Some a) |>, ∅, ∅)]> Sn).
  Proof.
    intros **. intros h1 h2 **.
    ddeq h1 h; simplify_eq /=.
    - ddeq h2 h; simplify_eq /=; first done.
     specialize (H0 h2 s' R' T' x H3 H5). set_solver.
    - ddeq h2 h; simplify_eq /=.
      + specialize (H0 h1 s0 R T x H2 H4). rewrite H4 in H5. simplify_eq /=.
      + eapply H1; eauto.
  Qed.

  Lemma socket_addresses_coherence_insert_bind (Sn : sockets) h s a :
    saddress s = None →
    socket_addresses_coherence Sn (ip_of_address a) →
    socket_addresses_coherence
      (<[h:=(s <| saddress := (Some a) |>, ∅, ∅)]> Sn) (ip_of_address a).
  Proof. intros ? ? h' **; ddeq h' h; eauto. Qed.

  Lemma network_sockets_coherence_insert_bind
     (S : gmap ip_address sockets) (P: ports_in_use) M  (Sn : sockets)
     (P_a : gset port) (h : socket_handle) (s : socket) (a : socket_address)  :
    let ip := ip_of_address a in
    S !! ip = Some Sn →
    (* facts about ports and the ip address a *)
    P !! ip = Some P_a →
    port_of_address a ∉ P_a →
    (* network in the previous state is coherent *)
    network_sockets_coherence S M P  →
    Sn !! h = Some (s, ∅, ∅) →
    saddress s = None →
    (* goal: *)
    network_sockets_coherence
      (<[ip:=
           <[h:=
               (s <| saddress := (Some a) |>, ∅, ∅)]> Sn]> S) M
      (<[ip:={[port_of_address a]} ∪ P_a]> P) .
  Proof.
   intros ip HS HP Hnotin HnetCoh HSnh Hnone.
   intros ip' Sn' HSn.
   assert (∀ h' s' R' T' a',
        Sn !! h' = Some (s', R', T') →
        saddress s' = Some a' →
        port_of_address a' ≠ port_of_address a ).
   { specialize (HnetCoh ip Sn HS) as (HBpCoh & HshCoh & HmrCoh & HsaCoh).
     intros **. intro.
     (* assert (h' ≠ h). *)
     (* { intro. simplify_eq /=. } *)
     assert (ip_of_address a' = ip).
     { eapply HsaCoh; eauto. }
     assert (port_of_address a' ∈ P_a).
     simplify_eq /=.
     { eapply HBpCoh; eauto. rewrite H3. done. }
     rewrite H2 in H4. set_solver. }
   ddeq ip' ip.
   - specialize (HnetCoh ip Sn HS) as (HBpCoh & HshCoh & HmrCoh & HsaCoh).
       by eauto 42 using
            bound_ports_coherence_insert_bind,
            socket_handlers_coherence_insert_bind,
            socket_messages_coherence_insert,
            socket_addresses_coherence_insert_bind.
   - specialize (HnetCoh ip' Sn' HSn) as (HBpCoh & HshCoh & HmrCoh & HsaCoh).
     split. intros ? **.
     assert (ip_of_address a0 = ip').
     { eapply HsaCoh; eauto. }
     simplify_eq /=; rewrite lookup_insert_ne in H3; last done.
     eapply HBpCoh; try done.
     done.
  Qed.

  Lemma message_received_insert_bind S m Sn h s a:
    let ip := ip_of_address a in
    S !! ip = Some Sn →
    Sn !! h = Some (s, ∅, ∅) →
    message_received S m →
    message_received (<[ip:=<[h:=(s <| saddress := (Some a) |>, ∅, ∅)]> Sn]> S) m.
  Proof.
    intros ip HSn HhSome (a' & Sn' & h' & s' & R' & T' & HSn' & Hh' & Ha' & Hm).
    ddeq (ip_of_address a') ip.
    - rewrite e in HSn'. ddeq h' h; first done.
      exists a', (<[h:=(s<| saddress := (Some a) |>, ∅, ∅)]> Sn), h', s',  R', T'.
      rewrite e. rewrite lookup_insert.
      repeat split; try done. by rewrite lookup_insert_ne.
    - exists a', Sn', h', s', R', T'.  rewrite lookup_insert_ne; try done.
  Qed.

  Lemma network_messages_coherence_insert_bind
    (S : gmap ip_address sockets)  M (Sn : sockets)
    (h : socket_handle) (s : socket) (a: socket_address) :
    let ip := ip_of_address a in
    S !! ip = Some Sn →
    Sn !! h = Some (s, ∅, ∅) →
    saddress s = None →
    network_messages_coherence S M -∗
    network_messages_coherence
      (<[ip:=<[h:=(s <| saddress := (Some a) |>, ∅, ∅)]> Sn]> S) M.
  Proof.
   iIntros (????) "Hsent". rewrite /network_messages_coherence.
    rewrite big_sepS_mono; first done.
    iIntros (msg Hmsg) "[Htt | %]".
    - by iLeft.
    - iRight. iPureIntro. by apply message_received_insert_bind.
  Qed.

  Lemma network_coherence_insert_bind
        (S : gmap ip_address sockets) (P: ports_in_use) M (Sn : sockets)
        (P_a : gset port) (h : socket_handle) (s : socket) (a: socket_address) :
    let ip := ip_of_address a in
    S !! ip = Some Sn →
    Sn !! h = Some (s, ∅, ∅) →
    saddress s = None →
    port_of_address a ∉ P_a →
    P !! ip = Some P_a →
    network_coherence S M P -∗
    network_coherence
      (<[ip:=<[h:=(s <| saddress := (Some a) |>, ∅, ∅)]> Sn]> S) M
      (<[ip:={[port_of_address a]} ∪ P_a]> P).
  Proof.
    iIntros (? ? ? ? ? ?) "(% & Hmsg)". iSplitR.
    - iPureIntro; by apply network_sockets_coherence_insert_bind.
    - by iDestruct (network_messages_coherence_insert_bind with "Hmsg") as "Hmsg".
  Qed.

  (** Coherence preservation for sending a message *)
  Lemma network_messages_coherence_insert_sent
    (S : gmap ip_address sockets) M (Si : sockets)
    (h : socket_handle) (skt : socket) (a to: socket_address) m R T Φ P:
    let ip := ip_of_address a in
    let msg := {| m_sender := a;
                  m_destination := to;
                  m_protocol := sprotocol skt;
                  m_body := m |} in
     saddress skt = Some a →
     S !! ip = Some Si →
     Si !! h = Some (skt, R, T) →
     network_sockets_coherence S M P →
     (m_destination msg) ⤇ Φ -∗
     Φ msg -∗
     network_messages_coherence S M -∗
     network_messages_coherence (<[ip:=<[h:=(skt, R, {[msg]} ∪ T)]> Si]> S) ({[msg]} ∪ M).
  Proof.
    iIntros (ip msg Hsa Hh Hsi HnetCoh) "Hsi Hmsg Hsent".
    rewrite /network_messages_coherence.
    destruct (decide (msg ∈ M)).
    - assert (M = {[msg]} ∪ M) as <- by set_solver.
      iApply (big_sepS_mono with "Hsent").
      iIntros (msg' Hmsg') "[Htt | Hrd]"; first by iLeft.
      iDestruct "Hrd" as %Hrd. iRight; iPureIntro.
      destruct Hrd as (a'&Sa'&h'&s'&R'&T'&Hsi'&Hs'&Hsa'&HinR').
      rewrite /message_received /message_received_at.
      ddeq (ip_of_address a') ip; last first.
      + exists a', Sa', h', s', R', T'. repeat split; eauto; by rewrite lookup_insert_ne.
      + exists a'. rewrite e0 lookup_insert.
        rewrite e0 in Hsi'. assert (Sa' = Si) by set_solver. subst.
        exists (<[h:=(skt, R, {[msg]} ∪ T)]> Si). simplify_eq /=.
        ddeq h' h.
        * exists h, skt, R, ({[msg]} ∪ T). repeat split; eauto; try set_solver.
          rewrite lookup_insert. done.
        * exists h', s', R', T'. repeat split; eauto. by rewrite lookup_insert_ne.
    - rewrite (big_sepS_union _ _ M ) // /=; last by set_solver.
       iSplitL "Hmsg Hsi". rewrite big_sepS_singleton. iLeft. eauto.
        iApply (big_sepS_mono with "Hsent").
        iIntros (msg' Hmsg') "[Htt | Hrd]"; first by iLeft.
         iDestruct "Hrd" as %Hrd. iRight; iPureIntro.
      destruct Hrd as (a'&Sa'&h'&s'&R'&T'&Hsi'&Hs'&Hsa'&HinR').
      rewrite /message_received /message_received_at.
      ddeq (ip_of_address a') ip; last first.
      + exists a', Sa', h', s', R', T'. repeat split; eauto; by rewrite lookup_insert_ne.
      + exists a'. rewrite e lookup_insert.
        rewrite e in Hsi'. assert (Sa' = Si) by set_solver. subst.
        exists (<[h:=(skt, R, {[msg]} ∪ T)]> Si). simplify_eq /=.
        ddeq h' h.
        * exists h, skt, R, ({[msg]} ∪ T). repeat split; eauto; try set_solver.
          rewrite lookup_insert. done.
        * exists h', s', R', T'. repeat split; eauto. by rewrite lookup_insert_ne.
  Qed.

  Lemma network_sockets_coherence_insert_sent
        (S : gmap ip_address sockets) (P: ports_in_use) M (Si : sockets)
        (h : socket_handle) (skt : socket) (a to: socket_address)
        (m : message_body) (R T: message_soup) :
    let ip := ip_of_address a in
    let msg := {| m_sender := a;
                  m_destination := to;
                  m_protocol := sprotocol skt;
                  m_body := m |} in
    saddress skt = Some a →
    S !! ip = Some Si →
    Si !! h = Some (skt, R, T) →
    network_sockets_coherence S M P →
    network_sockets_coherence (<[ip:=<[h:=(skt, R, {[msg]} ∪ T)]> Si]> S) ({[msg]} ∪ M) P.
  Proof.
    intros ip msg Hsa Hsi Hh HnetCoh.
    intros ip0 Sn0 Hip0.
    ddeq ip0 ip.
    - specialize (HnetCoh ip Si Hsi) as (HBpCoh & HshCoh & HsmCoh & HsaCoh).
      split. intros h' **. ddeq h' h; eauto using HBpCoh.
      split. intros h1 h2 **.
      ddeq h1 h; simplify_eq /=.
      { ddeq h2 h; simplify_eq /=; first done.
        assert (is_Some (saddress s)) by eauto.
          by specialize (HshCoh h h2 s s' R0 R' T T' Hh H1 H2 H3). }
      { ddeq h2 h; simplify_eq /=.
        assert (is_Some (saddress s)) by eauto.
         by specialize (HshCoh h1 h2 s s' R0 R' T0 T' H0 H1 H4 H3). }
      split.
      { intros h' s' **; ddeq h' h; split; intros m0 Hm0.
        - specialize (HsmCoh h s' R0 T a Hh Hsa); set_solver.
        - specialize (HsmCoh h s' R0 T a Hh Hsa); set_solver.
        - specialize (HsmCoh h' s' R0 T0 a0 H0 H1); set_solver.
        - specialize (HsmCoh h' s' R0 T0 a0 H0 H1); set_solver. }
      intros h' **; ddeq h' h; eauto.
    - specialize (HnetCoh ip0 Sn0 Hip0) as (HBpCoh & HshCoh & HsmCoh & HsaCoh).
      split; eauto. split; eauto. split; last done.
      intros h' **. specialize (HsmCoh h' s R0 T0 a0 H0 H1).
      split; intros m0 Hm0; set_solver.
  Qed.

  Lemma network_coherence_insert_sent
        (S : gmap ip_address sockets) (P: ports_in_use) M (Sn : sockets)
        (h : socket_handle) (skt : socket) (a to: socket_address)
        (m : message_body) (Φ : socket_interp Σ) R T :
    let n := ip_of_address a in
    let msg := {| m_sender := a;
                  m_destination := to;
                  m_protocol := sprotocol skt;
                  m_body := m |} in
    saddress skt = Some a →
    S !! n = Some Sn →
    Sn !! h = Some (skt, R, T) →
    (m_destination msg) ⤇ Φ -∗
    Φ msg -∗
    network_coherence S M P -∗
    network_coherence (<[n:=<[h:=(skt, R, {[msg]} ∪ T)]> Sn]> S) ({[msg]} ∪ M) P.
   Proof.
    iIntros (n msg ? ? ?) "Hpred Hr [% Hmsg]". iSplit.
    - iPureIntro. by apply network_sockets_coherence_insert_sent.
    - by iDestruct (network_messages_coherence_insert_sent with "Hpred Hr Hmsg") as "Hmsg".
   Qed.

End GhostStateLemmas.
