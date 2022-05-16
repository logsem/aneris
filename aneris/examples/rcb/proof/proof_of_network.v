(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.
From aneris.prelude Require Import misc.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import list_proof map_proof lock_proof network_util_proof inject.
From aneris.examples.rcb Require Import rcb_code.
From aneris.examples.rcb.spec Require Import  base.
From aneris.examples.rcb.model Require Import
     model_lst model_gst model_update_system.
From aneris.examples.rcb.resources Require Import
     base resources_global resources_lhst resources_local_inv resources_global_inv.
From aneris.examples.rcb.util Require Import list_proof_alt.

Import ast.

Section proof.
  Context `{!anerisG Mdl Σ, !RCB_params, !internal_RCBG Σ}.
  Context (γGown γGsnap : gname) (γLs : list gname).


  Lemma wp_loop_forever (fv : val) P ip :
    {{{ {{{ P }}} fv #() @[ip] {{{ RET #(); P }}} ∗
        P
    }}}
      loop_forever fv @[ip]
    {{{ RET #(); False }}}.
  Proof.
    iIntros (ϕ) "[#Hfv HP] Hϕ".
    iLöb as "IH".
    rewrite /loop_forever.
    wp_pures.
    wp_bind (fv _).
    iApply ("Hfv" with "HP").
    iModIntro.
    iIntros "HP". do 2 wp_pure _.
    iApply ("IH" with "HP").
    done.
  Qed.

  Record ack_msg := AckMsg {
    ack_orig : nat;
    ack_seqnum : nat;
    ack_src : nat
  }.

  (* For partition tolerance, the events that we send and receive
     contain not just the originating replica id, but also the "source"
     id. This is because a message can be created by a node (its origin),
     but then retransmitted by another one (the source). The source field
     is not exposed to the user in e.g. `deliver`, so we don't track it in the
     model. *)
  Record broadcast_msg := BroadcastMsg {
    bc_payload : val;
    bc_time : vector_clock;
    bc_orig : nat;
    bc_src : nat
  }.

  (* Drop the source field to turn a broadcast event into a global one. *)
  Definition broadcast_to_global (e : broadcast_msg) : global_event :=
    GlobalEvent e.(bc_payload) e.(bc_time) e.(bc_orig).

  Definition global_to_broadcast (e : global_event) src_id :=
    BroadcastMsg e.(ge_payload) e.(ge_time) e.(ge_orig) src_id.

  Lemma global_broadcast_orig a i:
    (global_to_broadcast a i).(bc_orig) = a.(ge_orig).
  Proof. done. Qed.

  Lemma broadcast_global_orig a:
    (broadcast_to_global a).(ge_orig) = a.(bc_orig).
  Proof. done. Qed.

  Lemma broadcast_global_payload a :
    (broadcast_to_global a).(ge_payload) = a.(bc_payload).
  Proof. done. Qed.

  Lemma global_broadcast_inv a i :
    broadcast_to_global (global_to_broadcast a i) = a.
  Proof. destruct a; done. Qed.

  Hint Rewrite global_broadcast_orig : core.
  Hint Rewrite global_broadcast_inv : core.

  Lemma broadcast_to_global_time e :
    (broadcast_to_global e).(ge_time) = e.(bc_time).
  Proof. destruct e; done. Qed.

  Global Program Instance Inject_broadcast_msg : Inject broadcast_msg val :=
    {|
      inject e := $(e.(bc_payload), vector_clock_to_val e.(bc_time), e.(bc_orig), e.(bc_src))
    |}.
  Next Obligation.
    intros w1 w2 Heq.
    inversion Heq as [[Hp Ht Ho Hs]].
    assert (bc_time w1 = bc_time w2) as Ht'.
    { by apply (inj (R := eq)) in Ht; [ | apply _]. }
    destruct w1, w2; simpl in *.
    apply Z_of_nat_inj in Ho; subst.
    apply Z_of_nat_inj in Hs; subst.
    done.
  Qed.

  (* Does the ack correspond to the given global_event? *)
  Definition ack_global_compat ack ge :=
    match ack, ge with
    | AckMsg ack_orig ack_sn _, GlobalEvent _ vc ge_orig =>
      ack_orig = ge_orig ∧
      (∃ ge_sn, vc !! ge_orig = Some ge_sn ∧ ge_sn = ack_sn)
    end.

  Definition rcb_msg := (ack_msg + broadcast_msg)%type.

  Program Instance ack_msg_inject : Inject ack_msg val :=
    {| inject ack := $(ack.(ack_orig), ack.(ack_seqnum), ack.(ack_src)) |}.
  Next Obligation.
    intros a1 a2 Heq.
    inversion Heq as [[Horig Hsn Hsender]].
    destruct a1, a2; simpl in *.
    repeat (lazymatch goal with
            | [ H : Z.of_nat ?x = Z.of_nat ?y |- _ ] =>
              assert (x = y) by lia; clear H
            end); subst.
    done.
  Qed.

  Definition broadcast_msg_ser : serialization :=
    prod_serialization
      (prod_serialization
         (prod_serialization RCB_serialization (* payload *)
                             vc_serialization) (* vc *)
          int_serialization) (* orig_id *)
       int_serialization.    (* sender_id *)


  Definition ack_msg_ser : serialization :=
    prod_serialization
      (prod_serialization int_serialization  (* orig_id *)
                          int_serialization) (* seqnum *)
       int_serialization. (* sender_id *)

  Definition rcb_msg_serialization : serialization :=
    sum_serialization ack_msg_ser broadcast_msg_ser.

  Lemma rcb_msg_serializable_l (orig sn from_id : nat) :
    s_valid_val rcb_msg_serialization (InjLV (#orig, #sn, #from_id)).
  Proof.
    econstructor. left.
    repeat econstructor; eauto.
  Qed.

  Lemma rcb_msg_serializable_r (qe : broadcast_msg) :
    RCB_Serializable (bc_payload qe) →
    s_valid_val rcb_msg_serialization (InjRV ($ qe)).
  Proof.
    intros ?.
    econstructor. right.
    repeat econstructor; eauto.
    eapply vector_clock_to_val_is_vc.
  Qed.

  Definition socket_proto (i : nat) : socket_interp Σ :=
    (λ m,
       let (from, to) := (m_sender m, m_destination m) in
       let mb := m_body m in
       ∃ (msg : rcb_msg),
         ⌜s_is_ser rcb_msg_serialization ($ msg) mb⌝ ∗
         ((∃ (ack : ack_msg) orig ge,
             ⌜msg = inl ack⌝ ∗
             ⌜RCB_addresses !! ack.(ack_orig) = Some orig⌝ ∗
             ⌜RCB_addresses !! ack.(ack_src) = Some from⌝ ∗
             ⌜ack_global_compat ack ge⌝ ∗
             own_global_snap γGsnap {[ ge ]})
          ∨
          (∃ (bcmsg : broadcast_msg) orig,
              ⌜msg = inr bcmsg⌝ ∗
              ⌜RCB_addresses !! bcmsg.(bc_orig) = Some orig⌝ ∗
              ⌜not (bcmsg.(bc_orig) = i)⌝ ∗
              ⌜RCB_addresses !! bcmsg.(bc_src) = Some from⌝ ∗
              own_global_snap γGsnap {[ broadcast_to_global bcmsg ]})))%I.

  Definition socket_inv z h s i :=
    inv RCB_InvName (∃ R S, h ↪[ip_of_address z] s ∗
                           z ⤳ (R, S) ∗
                           [∗ set] m ∈ R, socket_proto i m).

  Lemma send_thread_spec h s i T SeenLoc IQ OQ lk γlk z vl :
    {{{ ⌜saddress s = Some z⌝ ∗
        ⌜RCB_addresses !! i = Some z⌝ ∗
        ([∗ list] i ↦ z ∈ RCB_addresses, z ⤇ socket_proto i) ∗
        socket_inv z h s i ∗
        ⌜is_list RCB_addresses vl⌝ ∗
        local_invariant γGsnap γLs i T SeenLoc IQ OQ lk γlk z }}}
      send_thread RCB_serialization.(s_serializer).(s_ser) #i #(LitSocket h) lk vl #OQ
        @[ip_of_address z]
    {{{ RET #(); False }}}.
   Proof.
     iIntros (Φ) "(% & %Hiz & #Hprotos & #Hinv & % & #Hlinv) _".
     iDestruct (big_sepL_lookup _ _ i z with "Hprotos") as "Hz"; first done.
     rewrite /send_thread.
     wp_pures.
     wp_apply (wp_loop_forever _ True); last first.
     { iIntros (contra). inversion contra. }
     iSplitL ""; [ | done].
     clear Φ. iIntros (Φ).
     iModIntro. iIntros (_) "HΦ".
     wp_pures.
     remember (ip_of_address z) as ip.
     rewrite /local_invariant -Heqip.
     wp_apply acquire_spec; first iExact "Hlinv".
     iIntros (?) "(-> & Hlk & Hli)".
     iDestruct "Hli" as (vt vseen viq voq t seen liq loq s' ip')
       "(%Hip'& HT & %Hvc & HSeen & %Hvc_seen & %Hlen_eq & HIQ & HOQ & Hlock & %Hvalid)".
     rewrite Hiz /= -Heqip in Hip'; simplify_eq Hip'; intros <-.
     wp_pures.
     iDestruct "HOQ" as "(HOQ_pt&#HilP&#Hlen&Hown_l)".
     wp_load.
     set γ := λ i lq, single_queue_inv γGsnap i lq.
     wp_apply (wp_list_iteriP loq _ voq is_queue γ γ with "[Hown_l]").
     - iFrame; iFrame "#".
       iModIntro.
       iIntros (i' q qv ϕ). iModIntro.
       iIntros "[%Hiq [%Hlen Hγ]] Hϕ".
       wp_pures.
       wp_apply (wp_queue_peek_opt q); [done |].
       iIntros (peek_res) "%Hres".
       destruct Hres as [[-> ->] | [a [t' [-> ->]]]]; wp_pures.
       { iApply "Hϕ". iFrame. }
       wp_apply wp_list_nth; [done |].
       iIntros (v) "[[_ %Hle] | Hsome]".
       { iDestruct "Hlen" as "%Hlen_loq".
         lia. }
       iDestruct "Hsome" as (r) "[-> %Hnth]".
       wp_apply wp_unSOME; [done |].
       iIntros (_). wp_pures.
       wp_bind (msg_ser _ _).
       iDestruct (single_queue_inv_dup_front with "Hγ") as "[Hγ [%Hser [#Hsnap [%Hne %Horig]]]]".
       assert ((ge_payload a, vector_clock_to_val (ge_time a), #(ge_orig a), #i)%V =
               $ (global_to_broadcast a i)) as Hinj; [done |].
       wp_apply (s_ser_spec rcb_msg_serialization with "[Hsnap]").
       { iPureIntro.
         rewrite Hinj.
         apply rcb_msg_serializable_r; done. }
       iIntros (ser_msg) "%His_ser".
       wp_bind (SendTo _ _ _).
       iInv RCB_InvName as (R S) "(Hh & Hmsgs & HR)" "Hcl".
       rewrite Heqip.
       apply nth_error_lookup in Hnth.
       iDestruct (big_sepL_lookup _ _ i' r with "Hprotos") as "Hr"; first done.
       wp_apply (aneris_wp_send with "[Hh Hmsgs]"); [done|done| iFrame; iFrame "#" |].
       { iModIntro.
         iExists _.
         iSplitL "".
         { iPureIntro.
           assert ((InjRV (ge_payload a, vector_clock_to_val (ge_time a), #(ge_orig a), #i)) =
                   $ (inr (global_to_broadcast a i))) as Hinj'.
           { done. }
           rewrite Hinj' in His_ser.
           done. }
         iRight.
         destruct Horig as [orig_addr Horig].
         iExists _, _.
         repeat (iSplitL; autorewrite with core in *; eauto).
       }
       iIntros "[Hh Hmsgs]".
       iMod ("Hcl" with "[Hh Hmsgs HR]") as "_".
       { iNext.
         iExists _, _; iFrame "Hh Hmsgs"; done. }
       iModIntro.
       wp_pures.
       iApply "Hϕ".
       iFrame.
     - iIntros "Hown".
       wp_pures.
       wp_apply (release_spec with "[$Hlk $Hlinv HT HSeen HIQ Hown HOQ_pt Hlock]").
       { rewrite /local_inv_def.
         iExists _, _, _, _, _, _, _, _.
         iExists _, _.
         iFrame.
         iSplitL "".
         { iPureIntro.
           rewrite Hiz Heqip; done. }
         iFrame "#".
         by iPureIntro. }
       iIntros (v) "->".
       iApply "HΦ"; done.
   Qed.

   Lemma wp_prune_ack (orig seqnum from_id : nat) (q : list global_event) qv ip :
     {{{ Global_Inv γGown γGsnap γLs ∗
         ⌜(orig < length RCB_addresses)%nat⌝ ∗
         ⌜is_queue q qv⌝ ∗
         single_queue_inv γGsnap from_id q
     }}}
       prune_ack #orig #seqnum qv @[ip]
     {{{ qv', RET qv'; ∃ q',
           ⌜is_queue q' qv'⌝ ∗
            single_queue_inv γGsnap from_id q'
     }}}.
   Proof.
     iIntros (Φ) "[#HGinv [%Hlen [#Hiq Hinv]]] HΦ".
     rewrite /prune_ack. wp_pures.
     wp_apply (wp_queue_peek_opt with "Hiq").
     iIntros (hv) "[[-> ->] | %Hsome]".
     - wp_pures. iApply "HΦ"; eauto.
     - destruct Hsome as [a [t [-> ->]]]. wp_pures.
       iDestruct (single_queue_inv_dup_front with "Hinv") as "[#Hinv [_ [Hsnap _]]]".
       iMod ((own_global_snap_time_length _ _ _ a {[ a ]} ⊤) with "[] Hsnap") as "%Hlength";
         try (set_solver || done).
       wp_bind (vect_nth _ _).
       pose proof (vector_clock_to_val_is_vc (ge_time a)) as Hisvc.
       wp_apply wp_vect_nth; [ | done |].
       { eauto with lia. }
       iIntros (v) "#Hres". iDestruct "Hres" as (j) "[-> %Horig]".
       wp_pures.
       destruct (bool_decide (@eq Z (ge_orig a) orig)) eqn:Heq; wp_pures; last first.
       { iApply "HΦ"; eauto. }
       destruct (bool_decide (@eq Z j seqnum)); wp_pures; last first.
       { iApply "HΦ"; eauto. }
       wp_apply (wp_queue_take_opt (a :: t)); [done | ].
       iIntros (rv) "%Hopt". destruct Hopt as [[Hcontra _] | Hsome].
       { exfalso. done. }
       destruct Hsome as [h [gevs [tv [Hleq [-> Hiq_tv]]]]].
       wp_apply wp_unSOME; [done |].
       iIntros (_). wp_pures.
       iApply "HΦ". iExists _.
       iSplitL ""; [by eauto |].
       assert (t = gevs) as ->.
       { inversion Hleq; done. }
       iApply single_queue_inv_tail; done.
   Qed.

   Lemma wp_send_ack handle skt ge (orig sn from_id : nat) (from_addr to_addr : socket_address) ip :
     {{{ Global_Inv γGown γGsnap γLs ∗
         ⌜RCB_addresses !! from_id = Some from_addr⌝ ∗
         ⌜saddress skt = Some from_addr⌝ ∗
         ⌜ip_of_address from_addr = ip⌝ ∗
         socket_inv from_addr handle skt from_id ∗
         (∃ to_id, to_addr ⤇ socket_proto to_id)  ∗
         own_global_snap γGsnap {[ ge ]} ∗
         ⌜ge.(ge_orig) = orig⌝ ∗
         ⌜ge.(ge_time) !! ge.(ge_orig) = Some sn⌝ }}}
       send_ack RCB_serialization.(s_serializer).(s_ser) #(LitSocket handle) #orig #sn #from_id #to_addr @[ip]
     {{{ RET #(); True }}}.
   Proof.
     iIntros (Φ) "(#HGI & %Hfrom & %Hskta & %Hfrom_ip & #HSI & #Hto_proto & #Hsnap & %Horig_eq & %Htime) HΦ".
     rewrite /send_ack. wp_pures.
     wp_apply (s_ser_spec rcb_msg_serialization).
     { iPureIntro.
       apply rcb_msg_serializable_l; done. }
     iIntros (s) "%His". wp_pures.
     iMod (own_global_snap_orig _ _ _ ge _ ⊤ with "HGI Hsnap") as "%Horig";
       [done | set_solver |].
     apply lookup_lt_is_Some in Horig.
     destruct Horig as [? Horig].
     rewrite Horig_eq in Horig.
     wp_bind (SendTo _ _ _).
     iDestruct "Hto_proto" as (to_id) "Hto_proto".
     iAssert (socket_proto to_id {| m_sender := from_addr;
                                    m_destination := to_addr;
                                    m_protocol := sprotocol skt;
                                    m_body := s |}) as "#Hsp".
     { iExists _.
       iSplitL "".
       { iPureIntro.
         assert ((InjLV (#orig, #sn, #from_id)) =
                 (@inject rcb_msg val _ (inl (AckMsg orig sn from_id)))) as Heq; [done |].
         rewrite Heq in His.
         eauto. }
       iLeft.
       iExists _, _, _.
       repeat iSplitL ""; eauto.
       simpl in *; destruct ge; eauto. }
     iInv RCB_InvName as "> HInv" "Hcl".
     iDestruct "HInv" as (R S) "(Hhandle & Hpt & #Hproto)".
     wp_apply (aneris_wp_send _ _ _ _ to_addr from_addr with "[-Hcl HΦ]"); [done | done | |].
     { rewrite Hfrom_ip.
       iFrame; iFrame "#".
       eauto. }
     iIntros "[Hhandle Hfrom]".
     iMod ("Hcl" with "[Hhandle Hfrom]") as "_".
     { rewrite Hfrom_ip. iModIntro.
       iExists _, _.
       iFrame. iApply "Hproto". }
     iModIntro. wp_pures.
     by iApply "HΦ".
   Qed.

   Lemma recv_thread_spec h s i T SeenLoc addrs IQ OQ lk γlk z :
   {{{  Global_Inv γGown γGsnap γLs ∗
        ([∗ list] i ↦ z ∈ RCB_addresses, z ⤇ socket_proto i) ∗
        ⌜saddress s = Some z⌝ ∗
        ⌜sblock s = true⌝ ∗
        ⌜is_list RCB_addresses addrs⌝ ∗
        ⌜RCB_addresses !! i = Some z⌝ ∗
        socket_inv z h s i ∗
        z ⤇ socket_proto i ∗
        local_invariant γGsnap γLs i T SeenLoc IQ OQ lk γlk z }}}
     let ser := RCB_serialization.(s_serializer) in
       recv_thread ser.(s_ser) ser.(s_deser) #i #(LitSocket h) lk addrs #IQ #OQ #SeenLoc
        @[ip_of_address z]
    {{{ RET #(); False }}}.
   Proof.
     iIntros (Φ) "(#HGInv & #Hsproto & % & % & %Hil & %Hiz & #Hinv & #Hz & #Hlinv) HΦ".
     rewrite /recv_thread.
     wp_pures.
     wp_apply (wp_loop_forever _ True); last first.
     { iIntros (contra). done. }
     iSplitL; [ | done].
     clear Φ.
     iIntros (Φ). iModIntro. iIntros (_) "HΦ".
     wp_pures.
     remember (ip_of_address z) as ip.
     wp_bind (ReceiveFrom _).
     iApply (aneris_wp_wand
               _ _ _
               (λ v, ∃ m, ⌜v = SOMEV (#(m_body m), #(m_sender m))%V⌝ ∗
                          socket_proto i m))%I.
     { iInv RCB_InvName as (R S) "> (Hh & Hmsgs & HR)" "Hcl".
       rewrite Heqip.
       wp_apply (aneris_wp_receivefrom with "[Hh Hmsgs]");
         [done|done| done| by iFrame; iFrame "#"|].
       iIntros (r) "[% [(% & Hh & Hmsgs & _ & #Hsp) | (% & Hh & Hmsgs)]]".
       - iMod ("Hcl" with "[Hh HR Hmsgs]") as "_".
         { iNext.
           iExists _, _; iFrame; iFrame.
           rewrite big_sepS_union; last set_solver.
           rewrite big_sepS_singleton; iFrame; iFrame "#". }
         iModIntro.
         iExists _; iFrame "#"; eauto.
       - iDestruct (big_sepS_elem_of with "HR") as "#Hmsg"; first done.
         iMod ("Hcl" with "[Hh HR Hmsgs]") as "_".
         { iNext.
           iExists _, _; iFrame. }
         iModIntro.
         wp_pures; eauto. }
     iIntros (v).
     iDestruct 1 as (m) "[-> #Hm]".
     wp_apply wp_unSOME; [done | iIntros (_)].
     wp_pures.
     rewrite /local_invariant -Heqip.
     iDestruct "Hm" as (msg) "[%His HM]".
     wp_apply (s_deser_spec rcb_msg_serialization); [done |].
     iIntros (_). wp_pures.
     wp_apply acquire_spec; first iExact "Hlinv".
     iIntros (v) "[-> [Hlocked Hli]]".
     iDestruct "HM" as "[Hack | Hbcst]".
     - (* ack *)
       iDestruct "Hack" as (ack orig ge) "(-> & %Horig & %Hsrc & %Hcompat & #Hsnap)".
       wp_pures.
       iDestruct "Hli" as (vt vseen viq voq t seen liq loq s' ip')
         "(%Hip'& HT & %Hvc & HSeen & %Hvc_seen & %Hlen_eq & HIQ & HOQ & Hlock & %Hvalid)".
       iDestruct "HOQ" as "(HOQ_pt & #? & %Hlen_loq & #Hown)".
       assert (ip = ip') as ->.
       { rewrite Hiz in Hip'.
         inversion Hip'. done. }
       wp_load.
       wp_apply wp_list_nthP; [done |].
       iIntros (v) "[%Hnone | %Hsome]".
       { exfalso.
         destruct Hnone as [_ Hnone].
         rewrite Hlen_loq in Hnone.
         apply lookup_lt_Some in Hsrc.
         lia. }
       destruct Hsome as [wv [w [-> [Hiq Hnerr]]]].
       wp_apply wp_unSOME; [done |].
       iIntros (_). wp_pures.
       wp_bind (prune_ack _ _ _).
       apply nth_error_lookup in Hnerr.
       iDestruct ((big_sepL_lookup _ loq (ack.(ack_src)) w) with "Hown") as "H";
         [done | ].
       assert (ack_orig ack < length RCB_addresses)%nat.
       { apply lookup_lt_is_Some; eauto. }
       wp_apply wp_prune_ack; [iSplit; eauto | ].
       iIntros (qv') "Hqv'".
       iDestruct "Hqv'" as (q') "[%Hiqq' #Hsq_inv]".
       wp_pures. wp_load.
       assert (ack_src ack < length loq) as Hlt.
       { assert ((ack_src ack < length loq)%nat ->
                 (ack_src ack < length loq)) as Himpl.
         { eauto with lia. }
         apply Himpl.
         apply lookup_lt_is_Some; eauto. }
       wp_apply wp_list_updateP; [done | |].
       { iSplit; [done |].
         by iPureIntro; eauto. }
       iIntros (lv') "#Hil". wp_store.
       wp_apply (release_spec with "[-HΦ]").
       { repeat iSplit; try (iFrame || done).
         iAssert (OutQueues_inv γGsnap ip' OQ (<[ack_src ack:=q']> loq) lv')
                    with "[HOQ_pt]" as "HOQ".
         { rewrite /OutQueues_inv.
           iFrame.
           rewrite insert_length.
           repeat iSplit; eauto.
           iPoseProof (big_sepL_insert_acc with "[$Hown]") as "[_ Hsplit]"; [done |].
           iApply "Hsplit"; done. }
         rewrite /local_inv_def.
         eauto 15 with iFrame. }
       iIntros (r) "->". by iApply "HΦ".
     - iDestruct "Hbcst" as (bcmsg orig) "(-> & %Horig & %Hne & %Hsrc & #Hsnap)".
       wp_pures.
       iMod (own_global_snap_time_length _ _ _ (broadcast_to_global bcmsg) with "HGInv Hsnap") as "%Hlen";
         [done | set_solver  |].
       assert (length (bc_time bcmsg) = length RCB_addresses) as Heq; [by eauto |].
       wp_apply (wp_vect_nth _ _ _ (bc_time bcmsg)).
       + apply lookup_lt_Some in Horig; lia.
       + eauto using vector_clock_to_val_is_vc.
       + iIntros (v) "#Hv".
         iDestruct "Hv" as (j) "[-> %Hbc_time]". wp_pures.
         wp_apply wp_list_nth; [done | ].
         iIntros (v) "[[-> %Hcontra] | Hsome]".
         { exfalso.
           apply lookup_lt_Some in Hsrc.
           lia. }
         iDestruct "Hsome" as  (r) "[-> %Hnerr']".
         wp_apply wp_unSOME; [done |].
         iIntros (_). wp_pures.
         iAssert (r ⤇ socket_proto (bc_src bcmsg)) as "#Hrproto".
         {  iDestruct (big_sepL_lookup _ _ (bc_src bcmsg) r with "Hsproto") as "Hr"; [ | done].
            apply nth_error_lookup; done. }
         wp_apply wp_send_ack.
         { eauto 10 with iFrame. }
         iIntros (_). wp_pures.
         iDestruct "Hli" as (vt vseen viq voq t seen liq loq s' ip')
           "(%Hip'& HT & %Hvc & HSeen & %Hvc_seen & %Hlen_eq & HIQ & HOQ & Hlock & %Hvalid)".
         assert (ip' = ip) as ->.
         { rewrite Hiz in Hip'.
           simpl in Hip'. rewrite -Heqip in Hip'.
             by inversion Hip'. }
         wp_load.
         iMod (own_global_snap_orig _ _ _ (broadcast_to_global bcmsg) _ ⊤ with "HGInv Hsnap") as "%Hbcmsg";
           [done | set_solver |].
         rewrite broadcast_global_orig in Hbcmsg.
         wp_apply (wp_vect_nth); eauto with iFrame.
         { apply RCBM_LSTV_time_length in Hvalid. simpl in Hvalid.
           rewrite /RCBM_lst_time_length in Hvalid.
           rewrite -Hvalid in Hbcmsg.
           rewrite -Hlen_eq in Hbcmsg.
           lia. }
         iIntros (v) "%Hres".
         destruct Hres as [j' [-> Hseen]].
         wp_pures.
         wp_bind (if: _ then _ else _)%E.
         destruct (bool_decide (j' < j)); wp_pures; last first.
         { wp_apply (release_spec with "[-HΦ]").
           * iFrame. iFrame "#".
             rewrite /local_inv_def.
             eauto 12 with iFrame.
           * iIntros (v) "->".
             by iApply "HΦ". }
           wp_load.
           wp_apply (wp_vect_update); eauto with iFrame.
           { assert ((bc_orig bcmsg < length seen)%nat -> bc_orig bcmsg < length seen) as Himpl by lia.
             apply Himpl.
             eapply lookup_lt_Some; eauto. }
           iIntros (v) "#Hvc". wp_store.
         (* Show that we keep the inqueue invariant *)
         rewrite /InQueue_inv.
         iDestruct "HIQ" as "(HIQ & %Hilist & #Hown)".
         wp_load. wp_pures.
         replace (bc_payload bcmsg, vector_clock_to_val (bc_time bcmsg), #(bc_orig bcmsg))%V
           with $ (broadcast_to_global bcmsg); [ | done].
         wp_apply wp_list_cons; [eauto |].
         iIntros (viq') "%Hil_viq'".
         wp_store.
         iAssert (InQueue_inv γGsnap i ip IQ (broadcast_to_global bcmsg :: liq) viq') with "[$HIQ]" as "HIQ_inv".
         { iSplitL ""; [done | ].
           iApply big_sepL_cons; iFrame "#".
           done. }
         (* Show that we keep the outqueue invariant *)
         (* Specify a bunch of arguments to wp_list_mapiP that aren't easy to infer *)
         (* TODO: factor out this call to mapi here and in broadcast? *)
         set ev := broadcast_to_global bcmsg.
         set f : nat -> list global_event -> list global_event :=
           λ j q, if ((j =? i) || (j =? bcmsg.(bc_orig)) || (j =? bcmsg.(bc_src))) then q else q ++ [ev].
         set Parg := (@is_queue global_event _).
         set Qarg := Parg.
         remember  (λ (i : nat) x, single_queue_inv γGsnap i x) as γ.
         set ψ := γ.
         rewrite /OutQueues_inv.
         iDestruct "HOQ" as "(HOQ & #HilP & %Hlen_loq & #Hown_l)".
         wp_load. wp_pures.
         wp_bind (list_mapi _ _).
         iApply ((wp_list_mapiP f _ _ _ Parg Qarg γ ψ) with "[$HilP Hown_l]").
         { rewrite Heqγ; iFrame "#".
           iModIntro.
           subst Parg Qarg γ ψ f.
           iIntros (i' qe qev ϕ).
           iModIntro.
           iIntros "[Hsq_inv %Hisq] Hϕ".
           rewrite /single_queue_inv.
           wp_pures.
           destruct (bool_decide (Z.of_nat i' = Z.of_nat i)) eqn:Heqi1; wp_pures.
           { iApply "Hϕ".
             apply bool_decide_eq_true_1 in Heqi1.
             rewrite Heqi1.
             rewrite Z.eqb_refl. simpl.
             eauto with iFrame. }
           destruct (bool_decide (Z.of_nat i' = Z.of_nat (bcmsg.(bc_src)))) eqn:Heqi2; wp_pures.
           { iApply "Hϕ".
             apply bool_decide_eq_true_1 in Heqi2.
             rewrite Heqi2.
             rewrite Z.eqb_refl orb_true_r.
             eauto with iFrame. }
           destruct (bool_decide (Z.of_nat i' = Z.of_nat (bc_orig bcmsg))) eqn:Heqi3; wp_pures.
           { iApply "Hϕ".
             apply bool_decide_eq_true_1 in Heqi3.
             rewrite Heqi3.
             rewrite Z.eqb_refl orb_true_r orb_true_l.
             eauto with iFrame. }
           replace (bc_payload bcmsg, vector_clock_to_val (bc_time bcmsg), #(bc_orig bcmsg))%V
             with $ (broadcast_to_global bcmsg); last first; [done |].
           assert ((Val ($ (broadcast_to_global bcmsg))) =
                   (@inject global_event expr _ (broadcast_to_global bcmsg))) as ->; [done |].
           iPoseProof (wp_queue_add qe qev (broadcast_to_global bcmsg ) ip ϕ) as "Hqa".
           iApply "Hqa"; [eauto |].
           iModIntro.
           iIntros (rv) "%Hiq'".
           iApply "Hϕ".
           apply bool_decide_eq_false_1, Z.eqb_neq in Heqi1.
           apply bool_decide_eq_false_1, Z.eqb_neq in Heqi2.
           apply bool_decide_eq_false_1, Z.eqb_neq in Heqi3.
           rewrite Heqi1 Heqi2 Heqi3.
           simpl. subst ev.
           iSplitL ""; eauto.
           iApply big_sepL_app.
           iFrame.
           iApply big_sepL_singleton.
           rewrite broadcast_global_orig broadcast_global_payload.
           (* TODO: cleanup *)
           assert (RCB_Serializable (bcmsg.(bc_payload))).
           { apply s_is_ser_valid in His.
             rewrite /rcb_msg_serialization in His.
             simpl in His.
             rewrite /sum_valid_val in His.
             simpl in His.
             rewrite /prod_valid_val in His.
             simpl in His.
             rewrite /prod_valid_val in His.
             simpl in His.
             rewrite /prod_valid_val in His.
             simpl in His.
             destruct His as [w [[Hl _] | [Heqw Hr]]].
             - exfalso.
               by inversion Hl.
             - inversion Heqw as [Hsubst].
               rewrite -Hsubst in Hr.
               destruct Hr as [v1 [v2 [Heqv1v2 [Hv1 Hv2]]]].
               inversion Heqv1v2 as [[Hv1' Hv2']].
               rewrite -Hv1' in Hv1.
               destruct Hv1 as [v1' [v2' [Heq' Hrest]]].
               inversion Heq' as [[Hl HH]].
               rewrite -Hl in Hrest.
               destruct Hrest as [[v1'' [v2'' [Heq'' [Hpayload _]]]] _].
               inversion Heq''.
               subst.
               eauto. }
           assert (i' ≠ bc_orig bcmsg) as Hne'.
           { intros contra.
             rewrite contra in Heqi3.
             pose proof (Z.eqb_refl (Z.of_nat (bc_orig bcmsg))) as Heqz.
             rewrite Heqz in Heqi3.
             done. }
           assert (bc_orig bcmsg ≠ i') as ?.
           { intros contra.
             rewrite contra in Hne'.
             done. }
           iFrame "#"; eauto.
         }
         iModIntro.
         subst ψ. rewrite Heqγ.
         iIntros (rv) "[%HilP #Hown_l']".
         wp_store. wp_pures.
         wp_apply (release_spec with "[-HΦ]").
         { iFrame; iFrame "#".
           rewrite /local_inv_def.
           iExists _, _, _, _, _, _, _, _. iExists _, _.
           iFrame.
           repeat iSplitL ""; eauto.
           - rewrite -Hlen_eq insert_length; done.
           - rewrite mapi_length; done.
         }
         iIntros (v'') "->". by iApply "HΦ".
   Qed.

End proof.
