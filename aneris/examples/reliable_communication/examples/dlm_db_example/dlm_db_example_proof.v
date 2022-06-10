From iris.algebra Require Import excl.
From aneris.aneris_lang Require Import ast.
From aneris.aneris_lang.lib.serialization Require Import serialization_code.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang Require Import tactics proofmode.
From aneris.aneris_lang.program_logic
     Require Import aneris_weakestpre aneris_lifting.
From aneris.aneris_lang.lib Require Import assert_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.reliable_communication.prelude
     Require Import ser_inj.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_code.
From aneris.examples.reliable_communication.lib.repdb
     Require Import repdb_code.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_prelude dlm_resources dlm_code dlm_spec.
From aneris.examples.reliable_communication.lib.repdb.spec
     Require Import
     ras events resources api_spec.
From aneris.examples.reliable_communication.examples.dlm_db_example
     Require Import dlm_db_example_code.


(* -------------------------------------------------------------------------- *)
(** The definition of the resource guarded by the distributed lock manager. *)
(* -------------------------------------------------------------------------- *)
Section proof_of_code.
  Context `{!anerisG Mdl Σ}.
  Context `{TM: !DB_time, !DBPreG Σ}.
  Context (leader_si : message → iProp Σ).
  Context (db_sa db_Fsa dlm_sa : socket_address).

  (* ------------------------------------------------------------------------ *)
  (** The definition of the parameters for DB and DL and shared resources. *)
  (* ------------------------------------------------------------------------ *)

  Local Instance DLSrv : DL_params :=
    {|
      DL_server_addr := dlm_sa;
      DL_namespace := (nroot .@ "DLInv");
    |}.

  Local Instance DBSrv : DB_params :=
    {|
      DB_addr := db_sa;
      DB_addrF := db_Fsa;
      DB_keys := {["x"; "y"]};
      DB_InvName := (nroot .@ "DBInv");
      DB_serialization := int_serialization;
      DB_ser_inj := int_ser_is_ser_injective;
      DB_ser_inj_alt := int_ser_is_ser_injective_alt
    |}.

  Context `{!@DB_resources _ _ _ _ DBSrv}.
  Context `{!DlockG Σ, !DL_resources}.

  Definition SharedRes : iProp Σ :=
      ∃ (xv yv : option we) (h : ghst),
        "x" ↦ₖ xv ∗
        "y" ↦ₖ yv ∗
        Obs DB_addr h ∗
        ⌜at_key "x" h = xv⌝ ∗
        ⌜at_key "y" h = yv⌝ ∗
        ⌜ (∃ xw, xv = Some xw ∧ xw.(we_val) = #37) ↔
          (∃ yw, yv = Some yw ∧ yw.(we_val) = #1)⌝.

  (* ------------------------------------------------------------------------ *)
  (** The proof of the internal do_writes call *)
  (* ------------------------------------------------------------------------ *)
  Lemma wp_do_writes dl wr clt_00 clt_01 :
    ip_of_address clt_00 = ip_of_address clt_01 →
    {{{ GlobalInv ∗
        ⌜(dl_acquire_spec SharedRes clt_00 dl)⌝ ∗
        ⌜(dl_release_spec SharedRes clt_00 dl)⌝ ∗
        (∀ k v h, simplified_write_spec wr clt_01 k v h) ∗
        DLockCanAcquire clt_00 dl SharedRes }}}
      do_writes dl wr @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (HipEq Φ) "(#HGinv & %Hacq & %Hrel & (#Hwr & Hdl)) HΦ".
    rewrite /do_writes.
    wp_pures.
    wp_apply (Hacq with "[$Hdl]").
    iIntros (v) "(-> & Hrel & Hdlk & Hres)".
    wp_pures.
    iDestruct "Hres" as (xv yv h) "(Hx & Hy & #Hobs & %Hhx & %Hhy & %Hcnd)".
    rewrite HipEq.
    wp_apply ("Hwr" $! "x" (SerVal #37) h _ with "[Hx Hobs]").
    { iExists _. iFrame "#∗". done. }
    iIntros "Hpost".
    wp_pures.
    iDestruct "Hpost" as (hfx ax) "(%Hax & %Hwax & %Hatx & #Hobsx & Hx)".
    iApply fupd_aneris_wp.
    rewrite -Hhy.
    assert (h ≤ₚ (h ++ hfx ++ [ax])) as Hprefix.
    { by apply prefix_app_r. }
    iCombine "Hy" "Hobsx" as "HyObsx".
    iMod (OwnMemKey_obs_frame_prefix DB_addr "y" 1%Qp h (h ++ hfx ++ [ax]) ⊤ _ Hprefix
           with "HGinv HyObsx") as "(Hy & %HyHeq)".
    iModIntro.
    assert (at_key "x" (h ++ hfx ++ [ax]) = Some ax) as HatAx.
    { rewrite app_assoc. by apply at_key_snoc_some. }
    wp_apply ("Hwr" $! "y" (SerVal #1) (h ++ hfx ++ [ax]) _ with "[Hy Hobsx]").
    { iFrame "#∗".
      iExists _. iFrame "#∗". naive_solver. }
    iIntros "Hpost".
    wp_pures.
    iDestruct "Hpost" as (hfy ay) "(%Hay & %Hway & %Haty & #Hobsy & Hy)".
    rewrite -HipEq.
    iApply fupd_aneris_wp.
    rewrite -HatAx.
    assert ((h ++ hfx ++ [ax]) ≤ₚ ((h ++ hfx ++ [ax]) ++ hfy ++ [ay])) as Hprefix'.
    {  by apply prefix_app_r. }
    iCombine "Hx" "Hobsy" as "HxObsy".
    iMod (OwnMemKey_obs_frame_prefix
            DB_addr "x" 1%Qp
            (h ++ hfx ++ [ax]) ((h ++ hfx ++ [ax]) ++ hfy ++ [ay]) ⊤ _ Hprefix'
           with "HGinv HxObsy") as "(Hx & %HxHeq)".
    iModIntro.
    assert (at_key "y" ((h ++ hfx ++ [ax]) ++ hfy ++ [ay]) = Some ay) as HatAy.
    { rewrite app_assoc. by apply at_key_snoc_some. }
    iApply (Hrel with "[$Hrel $Hdlk Hx Hy]").
    { iExists (at_key "x" (h ++ hfx ++ [ax])),
              (Some ay),
              ((h ++ hfx ++ [ax]) ++ hfy ++ [ay]).
      iFrame "#∗".
      iSplit; first done.
      iSplit; first done.
      iPureIntro.
      split.
      { intros Hx. by exists ay. }
      intros Hy. by exists ax. }
    iNext.
    iIntros (v) "(-> & _)".
    by iApply "HΦ".
    Unshelve. done. done. done. done.
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** The proof of the internal do_reads call *)
  (* ------------------------------------------------------------------------ *)
  Lemma wp_do_reads dl rd clt_10 clt_11 :
    ip_of_address clt_10 = ip_of_address clt_11 →
    {{{ GlobalInv ∗
        (∀ k q h, read_spec rd clt_11 k q h) ∗
        ⌜(dl_acquire_spec SharedRes clt_10 dl)⌝ ∗
        ⌜(dl_release_spec SharedRes clt_10 dl)⌝ ∗
        DLockCanAcquire clt_10 dl SharedRes }}}
      do_reads dl rd @[ip_of_address clt_10]
    {{{ v, RET v; ⌜v = SOMEV #1⌝ }}}.
  Proof.
    iIntros (HipEq Φ).
    iIntros "(#HGinv & #Hrd & %Hacq & %Hrel & Har) HΦ".
    rewrite /do_reads.
    do 6 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_apply (Hacq with "[$Har]").
    iIntros (v) "(-> & Hrel & Hdlk & Hres)".
    wp_pures.
    iDestruct "Hres" as (xv yv h) "(Hx & Hy & #Hobs & %Hhx & %Hhy & %Hcnd)".
    rewrite HipEq.
    wp_apply ("Hrd" $! "x" 1%Qp xv with "[//][$Hx]").
    iIntros (vo) "Hvo".
    iDestruct "Hvo" as "(Hx & %Hxv)".
    wp_pures.
    rewrite -HipEq.
    destruct Hxv as [(-> & ->) | (xwe & -> & ->) ].
    - do 2 (wp_pure _).
      wp_apply (Hrel with "[$Hrel $Hdlk Hx Hy]").
      { iExists _, _, _.
        by iFrame "#∗". }
      iIntros (v) "(-> & Har)".
      do 4 (wp_pure _).
      by iApply ("IH" with "[$Har]").
    - wp_pures.
      case_bool_decide as Hxc.
      -- wp_pures.
         rewrite HipEq.
         wp_apply ("Hrd" $! "y" 1%Qp yv with "[//][$Hy]").
         iIntros (vo) "Hvo".
         iDestruct "Hvo" as "(Hy & %Hyv)".
         destruct Hyv as [(-> & ->) | (ywe & -> & ->) ].
         --- wp_pures.
             destruct Hcnd as (Hcnd & _).
             assert (∃ yw : we, None = Some yw ∧ we_val yw = #1) as Habs.
             { apply Hcnd. naive_solver. }
             naive_solver.
         --- do 2 (wp_pure _).
             assert (∃ yw : we, Some ywe = Some yw ∧ we_val yw = #1) as Hy.
             { apply Hcnd. naive_solver. }
             wp_apply wp_assert.
             wp_pures.
             destruct Hy as (yw & Heq & Heq2).
             assert (we_val ywe = we_val yw) as -> by naive_solver.
             rewrite Heq2.
             iSplit; first done.
             iNext.
             wp_pures.
             rewrite -HipEq.
             wp_apply (Hrel with "[$Hrel $Hdlk Hx Hy]").
             { iExists _, _, _.
               by iFrame "#∗". }
             iIntros (v) "(-> & Har)".
             wp_pures.
             by iApply "HΦ".
      -- wp_pures.
         wp_apply (Hrel with "[$Hrel $Hdlk Hx Hy]").
         { iExists _, _, _.
           by iFrame "#∗". }
         iIntros (v) "(-> & Har)".
         do 4 (wp_pure _).
         by iApply ("IH" with "[$Har]").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** The proof of the node 0 (writer) *)
  (* ------------------------------------------------------------------------ *)

  Lemma proof_of_node0 (clt_00 clt_01 : socket_address) A :
    ip_of_address clt_00 = ip_of_address clt_01 →
    {{{ GlobalInv ∗
        (* preconditions for subscribing client to dlock. *)
        ⌜clt_00 ∉ A⌝ ∗
        ⌜DL_server_addr ∈ A⌝ ∗
        (∀ sa A, dl_subscribe_client_spec SharedRes sa A) ∗
        fixed A ∗
        free_ports (ip_of_address clt_00) {[port_of_address clt_00]} ∗
        clt_00 ⤳ (∅, ∅) ∗
        dlm_sa ⤇ dl_reserved_server_socket_interp ∗
        (* preconditions to start a client proxy for the database. *)
        ⌜db_sa ∈ A⌝ ∗
        ⌜clt_01 ∉ A⌝ ∗
        (∀ A ca, init_client_proxy_leader_spec A ca leader_si) ∗
        db_sa ⤇ leader_si ∗
        clt_01 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_01) {[port_of_address clt_01]}
    }}}
      node0 #clt_00 #clt_01 #dlm_sa #db_sa @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (HipEq Φ).
    iIntros "(#HGinv & %HnInA & %HdlinA & #HdlCltS &
              #Hf & Hfps & Hclt00 & #Hdlmsi & Hpre) HΦ".
    iDestruct "Hpre" as "(%HinA & %HninA2 & HdbCltS & #Hdbsa & Hclt01 & Hfps3)".
    rewrite /node0.
    wp_pures.
    wp_apply ("HdlCltS" with "[$Hfps $Hclt00 $Hdlmsi $Hf]"); first done.
    iIntros (dl) "(Hdl & %Hacq & %Hrel)".
    wp_pures.
    rewrite HipEq.
    simplify_eq /=.
    wp_apply ("HdbCltS" $! A clt_01 with "[//][//][$Hfps3 $Hclt01 $Hdbsa $Hf]").
    iIntros (wr rd) "(#Hrd & Hwr)".
    iDestruct (get_simplified_write_spec with "Hwr") as "Hwr".
    wp_pures.
    rewrite -HipEq.
    wp_apply (wp_do_writes with "[HGinv Hwr Hdl]"); first done.
    { by iFrame "#∗". }
    done.
  Qed.

  Lemma proof_of_node1 (clt_10 clt_11 : socket_address) A :
    ip_of_address clt_10 = ip_of_address clt_11 →
    {{{ GlobalInv ∗
        (* preconditions for subscribing client to dlock. *)
        ⌜clt_10 ∉ A⌝ ∗
        ⌜DL_server_addr ∈ A⌝ ∗
        fixed A ∗
        (∀ sa A, dl_subscribe_client_spec SharedRes sa A) ∗
        free_ports (ip_of_address clt_10) {[port_of_address clt_10]} ∗
        clt_10 ⤳ (∅, ∅) ∗
        dlm_sa ⤇ dl_reserved_server_socket_interp ∗
        (* preconditions to start a client proxy for the database. *)
        ⌜db_sa ∈ A⌝ ∗
        ⌜clt_11 ∉ A⌝ ∗
        (∀ A ca, init_client_proxy_leader_spec A ca leader_si) ∗
        db_sa ⤇ leader_si ∗
        clt_11 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_11) {[port_of_address clt_11]}
    }}}
      node1 #clt_10 #clt_11 #dlm_sa #db_sa @[ip_of_address clt_10]
    {{{ v, RET v; ⌜v = SOMEV #1⌝ }}}.
  Proof.
    iIntros (HipEq Φ).
    iIntros "(#HGinv & %HnInA & %HdlinA & #Hf & #HdlCltS &
                      Hfps & Hclt00 & #Hdlmsi & Hpre) HΦ".
    iDestruct "Hpre" as "(%HinA & %HninA2 & HdbCltS & #Hdbsa & Hclt01 & Hfps3)".
    rewrite /node1.
    wp_pures.
    wp_apply ("HdlCltS" with "[$Hfps $Hclt00 $Hdlmsi $Hf]"); first done.
    iIntros (dl) "(Hdl & %Hacq & %Hrel)".
    wp_pures.
    rewrite HipEq.
    simplify_eq /=.
    wp_apply ("HdbCltS" $! A clt_11 with "[//][//][$Hfps3 $Hclt01 $Hdbsa $Hf]").
    iIntros (wr rd) "(#Hrd & Hwr)".
    wp_pures.
    rewrite -HipEq.
    wp_apply (wp_do_reads with "[HGinv Hwr Hdl]"); first done.
    { by iFrame "#∗". }
    iIntros.
    by iApply "HΦ".
  Qed.

End proof_of_code.

(** Concrete parameters (addresses, ips) *)
Definition db_sa := SocketAddressInet "0.0.0.0" 80.
Definition db_Fsa := SocketAddressInet "0.0.0.0" 81.
Definition dlm_sa := SocketAddressInet "0.0.0.1" 80.
Definition clt_sa00 := SocketAddressInet "0.0.0.2" 80.
Definition clt_sa01 := SocketAddressInet "0.0.0.2" 81.
Definition clt_sa10 := SocketAddressInet "0.0.0.3" 80.
Definition clt_sa11 := SocketAddressInet "0.0.0.3" 81.
Definition A : gset socket_address := {[ db_sa; db_Fsa; dlm_sa ]}.
Definition ips : gset string := {[ "0.0.0.0" ; "0.0.0.1"; "0.0.0.2"; "0.0.0.3" ]}.
Global Instance DLP : DL_params :=
    {|
      DL_server_addr := dlm_sa;
      DL_namespace := (nroot .@ "DLInv");
    |}.

Global Instance DBP : DB_params :=
    {|
      DB_addr := db_sa;
      DB_addrF := db_Fsa;
      DB_keys := {["x"; "y"]};
      DB_InvName := (nroot .@ "DBInv");
      DB_serialization := int_serialization;
      DB_ser_inj := int_ser_is_ser_injective;
      DB_ser_inj_alt := int_ser_is_ser_injective_alt
    |}.

Definition main : expr :=
    Start "0.0.0.0" (init_leader (DB_serialization.(s_serializer)) #DB_addr #DB_addrF);;
    Start "0.0.0.1" (dlock_start_service #dlm_sa) ;;
    Start "0.0.0.2" (node0 #clt_sa00 #clt_sa01 #dlm_sa #db_sa) ;;
    Start "0.0.0.3" (node1 #clt_sa10 #clt_sa11 #dlm_sa #db_sa).

Section proof_of_main.
  Context `{!anerisG Mdl Σ, lockG Σ}.
  Context `{TM: !DB_time, !DBPreG Σ}.
  Context (leader_si leaderF_si : message → iProp Σ).
  Context (Init_leader : iProp Σ).
  Context `{!DlockG Σ, !DL_resources}.
  Context `{DBRes : !@DB_resources _ _ _ _ DBP}.
  Notation SharedRes := (@SharedRes _ _ _ _ db_sa db_Fsa DBRes).

  Lemma main_spec :
    ⊢ |={⊤}=>
         GlobalInv -∗
         (∀ A, dl_server_start_service_spec SharedRes A) -∗
         (∀ sa A, dl_subscribe_client_spec SharedRes sa A) -∗
         (∀ A, init_leader_spec A Init_leader leader_si leaderF_si) -∗
         (∀ A ca, init_client_proxy_leader_spec A ca leader_si) -∗
         ⌜DL_server_addr ∈ A⌝ -∗
         db_sa ⤇ leader_si -∗
         db_Fsa ⤇ leaderF_si -∗
         dlm_sa ⤇ dl_reserved_server_socket_interp -∗
         fixed A -∗
         free_ip "0.0.0.0" -∗
         free_ip "0.0.0.1" -∗
         free_ip "0.0.0.2" -∗
         free_ip "0.0.0.3" -∗
         SocketAddressInet "0.0.0.0" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.0" 81 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.1" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.2" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.2" 81 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.3" 80 ⤳ (∅, ∅) -∗
         SocketAddressInet "0.0.0.3" 81 ⤳ (∅, ∅) -∗
         dl_service_init -∗
         Init_leader -∗
         SharedRes -∗
         WP main @["system"]
      {{ v, True }}.
  Proof.
    iIntros "".
    iModIntro.
    iIntros "#HGinv HdlSrvS #HdlCltS HdbSrvS #HdbCltS".
    iIntros "#HinA #Hsrv0 #Hsrv1 #Hsrv2 #Hfixed Hfree0 Hfree1 Hfree2 Hfree3".
    iIntros "Hsa0 Hsa1 Hsa2 Hsa3 Hsa4 Hsa5 Hsa6 HSrvInit0 HSrvInit1 HR".
    rewrite /main.
    (* Server 1. *)
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree0".
    iSplitR "Hsa0 Hsa1 HSrvInit1 HdbSrvS"; last first.
    { iNext. iIntros "Hfps".
      iApply ("HdbSrvS" $! A
               with "[][][][][HSrvInit1 Hfps Hsa0 Hsa1]"); [eauto .. | | done ].
      iDestruct (free_ports_split
                    "0.0.0.0"
                    {[80%positive]} {[81%positive]}) as "(Hfp1 & _)"; [set_solver|].
      iFrame "#∗". iApply "Hfp1". iFrame. }
    iNext. wp_pures.
    (* Server 2. *)
    wp_apply aneris_wp_start; first done.
    iFrame "Hfree1".
    iSplitR "Hsa2 HSrvInit0 HdlSrvS HR"; last first.
    { iNext. iIntros "Hfps".
      iApply ("HdlSrvS" $! A with "[Hfps HSrvInit0 Hsa2 HR]"); last done. iFrame "#∗". }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree2".
    iSplitR "Hsa3 Hsa4"; last first.
    { iNext. iIntros "Hfps".
      iApply (proof_of_node0 leader_si db_sa db_Fsa dlm_sa clt_sa00 clt_sa01 A
               with "[$HGinv $Hsa3 $Hsa4 Hfps]"); first done.
      iSplit.
      { iPureIntro. eauto with set_solver. }
      iDestruct (free_ports_split
                   "0.0.0.2"
                   {[80%positive]} {[81%positive]}) as "(Hfp1 & _)"; [set_solver|].
      iDestruct ("Hfp1" with "Hfps") as "(Hfp & Hfp')".
      iFrame "#∗".
      iPureIntro; set_solver.
      done. }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree3".
    iSplitR "Hsa5 Hsa6"; last first.
    { iNext. iIntros "Hfps".
      iApply (proof_of_node1 leader_si db_sa db_Fsa dlm_sa clt_sa10 clt_sa11 A
               with "[$HGinv $Hsa5 $Hsa6 Hfps]"); first done.
      iSplit.
      { iPureIntro. eauto with set_solver. }
      iDestruct (free_ports_split
                   "0.0.0.3"
                   {[80%positive]} {[81%positive]}) as "(Hfp1 & _)"; [set_solver|].
      iDestruct ("Hfp1" with "Hfps") as "(Hfp & Hfp')".
      iFrame "#∗".
      iPureIntro; set_solver.
      done. }
    done.
  Qed.

End proof_of_main.

(* -------------------------------------------------------------------------- *)
(** The proof of adequacy. *)
(* -------------------------------------------------------------------------- *)

Definition init_state :=
  {|
    state_heaps := {[ "system" := ∅ ]};
    state_sockets := {[ "system" := ∅ ]};
    state_ports_in_use :=
      <["0.0.0.0" := ∅ ]> $
      <["0.0.0.1" := ∅ ]> $
      <["0.0.0.2" := ∅ ]> $
      <["0.0.0.3" := ∅ ]> $ ∅;
    state_ms := ∅;
  |}.

Definition fixed_dom : gset socket_address := {[ db_sa; db_Fsa; dlm_sa ]}.

Definition dummy_model := model unit (fun x y => True) ().

Lemma dummy_model_finitary : adequacy.aneris_model_rel_finitary dummy_model.
Proof.
 intros st.
 intros f Hnot.
 pose proof (Hnot 0%nat 1%nat) as H.
 assert (0%nat = 1%nat -> False) as Himpl. {
   intros Heq.
   discriminate Heq.
 }
 apply Himpl; apply H.
 destruct (f 0%nat) as [s0 r0].
 destruct (f 1%nat) as [s1 r1].
 destruct s0, s1, st, r0, r1.
 reflexivity.
Qed.

From stdpp Require Import fin_maps gmap.
From iris.algebra Require Import auth gmap frac excl agree coPset
     gset frac_auth ofe excl.
From aneris.algebra Require Import disj_gsets.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.program_logic Require Import aneris_adequacy.
From aneris.examples.reliable_communication.lib.repdb
     Require Import model.
From aneris.examples.reliable_communication.lib.dlm
     Require Import dlm_proof.
From aneris.examples.reliable_communication.spec Require Import prelude ras.



Definition socket_interp `{!anerisG empty_model Σ}
  db_si dbF_si dlm_si sa : socket_interp Σ :=
  (match sa with
   | SocketAddressInet "0.0.0.0" 80 =>  db_si
   | SocketAddressInet "0.0.0.0" 81 =>  dbF_si
   | SocketAddressInet "0.0.0.1" 80 =>  dlm_si
   | _ => λ msg, ⌜True⌝
   end)%I.

Notation ShRes := (@SharedRes _ _ _ _ db_sa db_Fsa).

From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import proof_of_db_init.


Theorem adequacy : aneris_adequate main "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ dummy_model; DBΣ; SpecChanΣ]).
  eapply (@adequacy
            Σ dummy_model _ _ ips fixed_dom
            {[db_sa; db_Fsa; dlm_sa; clt_sa00; clt_sa01; clt_sa10; clt_sa11]} ∅ ∅ ∅);
    try done; last first.
  { set_solver. }
  { intros i. rewrite /ips !elem_of_union !elem_of_singleton.
    intros [|]; subst; simpl; set_solver. }
  { rewrite /ips /= !dom_insert_L dom_empty_L right_id_L //. set_solver. }
  iIntros (Hdg) "".
  2:{ apply dummy_model_finitary . }
  assert (DBPreG Σ) as HPreG by apply _.
  iMod (db_init_empty.(DB_init_setup) ⊤ $! I) as (DBRes) "Hdb";
    [solve_ndisj|set_solver|set_solver| ].
  iDestruct "Hdb"
    as (init_leader leader_si leaderF_si) "(#HGinv & #Hobs & Hkeys & HdbInit & #Hspecs)".
  iDestruct "Hspecs"
    as "((#HdbSrvS & #HdbCltS) & _)".
  iMod (dlinit.(DL_init_setup) ⊤ DLP ShRes)
    as (DLRes) "(HdlInit & #HdlSrvS & #HdlCltS)";
    [solve_ndisj| ].
  iExists (socket_interp leader_si leaderF_si dl_reserved_server_socket_interp).
  iMod (@main_spec
          _ _ _
          int_time leader_si leaderF_si init_leader DLRes DBRes) as "Hmain".
  iModIntro.
  iIntros "Hf Hsis Hb Hfg Hips _ _ _ _ _".
  simpl in *.
  iDestruct (big_sepS_delete _ _ db_sa with "Hsis") as "[Hsi0 Hsis]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ db_Fsa with "Hsis") as "[Hsi1 Hsis]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ dlm_sa with "Hsis") as "[Hsi2 _]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.0" with "Hips") as "[Hip0 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.1" with "Hips") as "[Hip1 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.2" with "Hips") as "[Hip2 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "0.0.0.3" with "Hips") as "[Hip3 Hips]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ db_sa with "Hb") as "[Hm0 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ db_Fsa with "Hms") as "[Hm1 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ dlm_sa with "Hms") as "[Hm2 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa00 with "Hms") as "[Hc00 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa01 with "Hms") as "[Hc01 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa10 with "Hms") as "[Hc10 Hms]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ clt_sa11 with "Hms") as "[Hc11 _]";
    first set_solver.
  iApply ("Hmain" with
           "[$HGinv][$HdlSrvS][$HdlCltS][$HdbSrvS][$HdbCltS][//]
            [$Hsi0][$Hsi1][$Hsi2][$Hf]
            [$Hip0][$Hip1][$Hip2][$Hip3]
            [$Hm0][$Hm1][$Hm2][$Hc00][$Hc01][$Hc10][$Hc11]
            [$HdlInit][$HdbInit]").
  iExists None, None,  [].
  iDestruct (big_sepS_delete _ _ "x" with "Hkeys") as "[Hx Hkeys]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "y" with "Hkeys") as "[Hy _]";
   first set_solver.
  iFrame "#∗".
  iPureIntro; split_and!; [done|done|].
  intros. naive_solver.
Qed.
