(** Proof the causal memory implementation w.r.t. modular specification. *)
From iris.algebra Require Import agree auth excl gmap.
From iris.base_logic Require Import invariants.
From aneris.prelude Require Import misc.
From aneris.aneris_lang Require Import lang network tactics proofmode lifting.
From aneris.aneris_lang.lib.vector_clock Require Import vector_clock_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang.lib Require Import list_proof map_proof lock_proof network_util_proof inject.
From aneris.examples.ccddb Require Import ccddb_code.
From aneris.examples.ccddb.spec Require Import  base.
From aneris.examples.ccddb.model Require Import
     model_lst model_gst model_update_system.
From aneris.examples.ccddb.resources Require Import
     base resources_gmem resources_lhst resources_local_inv resources_global_inv.

Import ast.

Section proof.
  Context `{!anerisG Mdl Σ, !DB_params, !internal_DBG Σ}.
  Context (γGsnap : gname) (γLs : list (gname * gname)).

  Definition write_event_serialization : serialization :=
    prod_serialization
      (prod_serialization
         (prod_serialization string_serialization DB_serialization)
         vc_serialization) int_serialization.

  Lemma write_event_serializable a :
    DB_Serializable (we_val a) →
    s_valid_val write_event_serialization ($ a).
  Proof.
    intros ?.
    repeat econstructor; eauto.
    eapply vector_clock_to_val_is_vc.
  Qed.

  (* protocol for the received msg:
     - source must be among DB_addresses;
     - the message body should be of the form (((k,v),t),j)
       where
         + k ∈ DB_keys;
         + v is a value (assume integer for simplicity);
         + t is a vector clock;
         + DB_addresses at j should be the address of the source;
     - a memory snapshot certificate containting the write event
       corresponding to the (k,v,t,j) tuple. *)
  Definition socket_proto : socket_interp Σ :=
    (λ m,
    let (orig, to) := (m_sender m, m_destination m) in
    let mb := m_body m in
    ∃ (a : write_event) (i: nat),
    ⌜a.(we_key) ∈ DB_keys⌝ ∧
    ⌜s_is_ser write_event_serialization ($ a) mb⌝ ∧
    ⌜DB_addresses !! a.(we_orig) = Some orig⌝ ∧
    ⌜DB_addresses !! i = Some to⌝ ∧ ⌜i ≠ a.(we_orig)⌝ ∧
    own_mem_snapshot γGsnap a.(we_key) {[a]})%I.

  Definition socket_inv z h s :=
    inv DB_InvName (∃ R S, h ↪[ip_of_address z] s ∗
                           z ⤳ (R, S) ∗
                           [∗ set] m ∈ R, socket_proto m).

  Lemma send_thread_spec h s i DB T IQ OQ lk γlk z vl :
    {{{ ⌜saddress s = Some z⌝ ∗
        ⌜DB_addresses !! i = Some z⌝ ∗
        ([∗ list] i ↦ z ∈ DB_addresses, z ⤇ socket_proto) ∗
        socket_inv z h s ∗
        ⌜is_list DB_addresses vl⌝ ∗
        local_invariant γGsnap γLs i DB T IQ OQ lk γlk z }}}
      send_thread DB_serialization.(s_serializer).(s_ser) #i #(LitSocket h) lk vl #OQ
        @[ip_of_address z]
    {{{ RET #(); False }}}.
   Proof.
     iIntros (Φ) "(% & Hiz & #Hprotos & #Hinv & % & #Hlinv) _".
     iDestruct "Hiz" as %Hiz.
     iDestruct (big_sepL_lookup _ _ i z with "Hprotos") as "Hz"; first done.
     rewrite /recv_thread.
     wp_lam; do 4 wp_let. wp_pure _.
     wp_closure.
     wp_pure _.
     iLöb as "IH".
     wp_pures.
     remember (ip_of_address z) as ip.
     rewrite /local_invariant -Heqip.
     wp_apply acquire_spec; first iExact "Hlinv".
     iIntros (?) "(-> & Hlk & Hli)".
     iDestruct "Hli" as (vd vt viq voq d t liq loq s' ip')
       "(Hip'& HDB & HT & HIQ & HOQ & #Hdict & #Hvc &Hliv &#Hlstv)".
     iDestruct "Hip'" as %Hip'.
     rewrite Hiz /= -Heqip in Hip'; simplify_eq Hip'; intros <-.
     wp_pures.
     iDestruct "HOQ" as "(HOQ&%&Hloq)".
     wp_load.
     wp_pures.
     wp_apply wp_list_is_empty; first done.
     destruct loq as [|a loq]; simpl.
     { iIntros (? ->).
       wp_pures.
       iAssert (OutQueue_of_write_events γGsnap i ip OQ [] voq)
       with "[HOQ Hloq]" as "HOQ".
       { iFrame; simpl; done. }
       wp_apply (release_spec with "[$Hlk HDB HT HOQ HIQ Hliv]").
       { iFrame "Hlinv".
         iExists _, _, _, _, _, _, _, _; iExists _, _.
         rewrite Hiz /= -Heqip.
         iFrame; iFrame "#"; done. }
       iIntros (? ->); simpl.
       do 2 wp_pure _.
       iApply "IH". }
     iIntros (? ->).
     wp_pures.
     wp_apply wp_list_tail; first done.
     iIntros (voq' Hvoq'); simpl.
     wp_store.
     wp_pures.
     iDestruct "Hloq" as "[Ha Hloq]".
     iAssert (OutQueue_of_write_events γGsnap i ip OQ loq voq')
       with "[HOQ Hloq]" as "HOQ".
     { iFrame; done. }
     wp_apply (release_spec with "[$Hlk HDB HT HOQ HIQ Hliv]").
     { iFrame "Hlinv".
       iExists _, _, _, _, _, _, _, _; iExists _, _.
       rewrite Hiz /= -Heqip.
       iFrame; iFrame "#"; done. }
     iIntros (? ->); simpl.
     wp_pures.
     wp_apply wp_list_head; first done.
     iIntros (?) "[[% %]|Hv] //".
     iDestruct "Hv" as %(v' & l' & Hv'l' & ->).
     simplify_eq Hv'l'; intros <- <-; simpl.
     wp_apply wp_unSOME; first done.
     iIntros (_); simpl.
     wp_pures.
     iDestruct "Ha" as "(% & % & Hao & #Ha)".
     iDestruct "Hao" as %Hao.
     wp_apply (s_ser_spec write_event_serialization).
     { by iPureIntro; apply write_event_serializable. }
     iIntros (msg Hmsg); simpl.
     wp_pure _.
     wp_pure _.
     wp_bind (Rec _ _ _); simpl.
     iApply (aneris_wp_wand _ _ _ (λ (v : val),
                                        ∀ j : Z, {{{⌜0 ≤ j⌝%Z}}}
                                                   v #j @[ip]
                                                   {{{u, RET u; True}}})%I).

     { wp_pures.
       iIntros (j Ψ) "!# Hj HΨ".
       iDestruct "Hj" as %Hj.
       iClear "IH".
       iLöb as "IH" forall (j Hj).
       wp_pures.
       wp_apply wp_list_length; first done.
       iIntros (? ->); simpl.
       wp_pures.
       destruct (decide (j < length DB_addresses)%Z); last first.
       { rewrite bool_decide_eq_false_2; last done.
         wp_pures. iApply "HΨ"; done. }
       rewrite bool_decide_eq_true_2; last done.
       wp_pures.
       destruct (decide (i = j :> Z)).
       { rewrite bool_decide_eq_true_2; last done.
         do 2 wp_pure _.
         iApply "IH"; auto with lia. }
       rewrite bool_decide_eq_false_2; last done.
       wp_pures.
       replace #j with #(Z.to_nat j); last first.
       { repeat f_equal; lia. }
       wp_apply wp_list_nth; first done.
       iIntros (v) "[[% %]| Hv]"; first lia.
       iDestruct "Hv" as %(r & -> & Hr%nth_error_lookup); simpl.
       (* apply map_lookup_Some in Hr as (z' & -> & Hz'). *)
       wp_apply wp_unSOME; first done.
       iIntros "_"; simpl.
       wp_pures.
       iDestruct (big_sepL_lookup _ _ (Z.to_nat j) r with "Hprotos") as "Hz'";
         first done.
       wp_bind (SendTo _ _ _).
       iInv DB_InvName as (R S) "(Hh & Hmsgs & HR)" "Hcl".
       rewrite Heqip.

       wp_apply (aneris_wp_send with "[Hh Hmsgs]"); [done|done|iFrame; iFrame "#"|].
       {iExists a, (Z.to_nat j); simpl.
        simpl in Hmsg.
        repeat iSplit; auto with lia.
        iNext. iPureIntro.
        by rewrite Hao.
       }
       iIntros "[Hh Hmsgs]".
       iMod ("Hcl" with "[Hh Hmsgs HR]") as "_".
       { iNext.
         iExists _, _; iFrame "Hh Hmsgs"; done. }
       iModIntro.
       do 5 wp_pure _.
       iApply "IH"; auto with lia. }
     iIntros (?) "Hsnd".
     wp_pures.
     wp_apply "Hsnd"; first done.
     iIntros (?) "_"; simpl.
     do 2 wp_pure _.
     iApply "IH".
   Qed.

  Lemma recv_thread_spec h s i DB T IQ OQ lk γlk z :
    {{{ ⌜saddress s = Some z⌝ ∗
        ⌜sblock s = true⌝ ∗
        ⌜ip_of_address <$> DB_addresses !! i = Some (ip_of_address z)⌝ ∗
        socket_inv z h s ∗ z ⤇ socket_proto ∗
        local_invariant γGsnap γLs i DB T IQ OQ lk γlk z }}}
      recv_thread DB_serialization.(s_serializer).(s_deser) #(LitSocket h) lk #IQ
        @[ip_of_address z]
    {{{ RET #(); False }}}.
   Proof.
     iIntros (Φ) "(% & % & Hiz & #Hinv & #Hz & #Hlinv) _".
     iDestruct "Hiz" as %Hiz.
     rewrite /recv_thread.
     wp_lam; do 2 wp_let. wp_pure _.
     wp_closure.
     wp_pure _.
     iLöb as "IH".
     wp_pures.
     remember (ip_of_address z) as ip.
     wp_bind (ReceiveFrom _).
     iApply (aneris_wp_wand
               _ _ _
               (λ v, ∃ m, ⌜v = SOMEV (#(m_body m), #(m_sender m))%V⌝ ∗
                          socket_proto m))%I.
     { iClear "IH".
       iInv DB_InvName as (R S) "> (Hh & Hmsgs & HR)" "Hcl".
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
     iDestruct "Hm" as (a j) "(%&%&%&%&%&Ha)".
     rewrite /unSOME.
     wp_pures.
     rewrite /local_invariant -Heqip.
     wp_apply acquire_spec; first iExact "Hlinv".
     iIntros (?) "(-> & Hlk & Hli)".
     iDestruct "Hli" as (vd vt viq voq d t liq loq s' ip')
       "(Hip'& HDB & HT & HIQ & HOQ & #Hdict & #Hvc &Hliv &#Hlstv)".
     iDestruct "Hip'" as %Hip'.
     rewrite Hiz in Hip'; simplify_eq Hip'; intros <-.
     wp_pures.
     wp_apply (s_deser_spec write_event_serialization); first done.
     iIntros "_ /=".
     wp_pures.
     iDestruct "HIQ" as "(HIQ&%&Hliq)".
     wp_load.
     (* TODO: fix hack *)
     replace (#(we_key a), we_val a, vector_clock_to_val (we_time a), #(we_orig a))%V with ($ a : val); last done.
     wp_apply wp_list_cons; first done.
     iIntros (viq' Hviq'); simpl.
     wp_store.
     wp_pures.
     iAssert (InQueue_of_write_events γGsnap ip IQ (a :: liq) viq')
       with "[HIQ Hliq Ha]" as "HIQ".
     { iFrame; iFrame "#"; done. }
     wp_apply (release_spec with "[$Hlk HDB HT HOQ HIQ Hliv]").
    { iFrame "Hlinv".
      iExists _, _, _, _, _, _, _, _; iExists _, _.
      iFrame; iFrame "#"; done. }
    iIntros (? ->); simpl.
    do 2 wp_pure _.
    iApply "IH".
   Qed.

End proof.
