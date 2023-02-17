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
      DB_followers := ∅;
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
        (dl_acquire_spec SharedRes (ip_of_address clt_00) dl) ∗
        (dl_release_spec SharedRes (ip_of_address clt_00) dl) ∗
        (∀ k v h, simplified_write_spec wr clt_01 k v h) ∗
        DLockCanAcquire (ip_of_address clt_00) dl SharedRes }}}
      do_writes dl wr @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (HipEq Φ) "(#HGinv & #Hacq & #Hrel & (#Hwr & Hdl)) HΦ".
    rewrite /do_writes.
    wp_pures.
    wp_apply ("Hacq" with "[$Hdl]").
    iIntros "(Hcanrel & Hres)".
    wp_pures.
    iDestruct "Hres" as (xv yv h) "(Hx & Hy & #Hobs & %Hhx & %Hhy & %Hcnd)".
    rewrite HipEq.
    wp_apply ("Hwr" $! "x" (SerVal #37) h with "[//] [Hx Hobs]").
    { iExists _. iFrame "#∗". done. }
    iIntros "Hpost".
    wp_pures.
    iDestruct "Hpost" as (hfx ax) "(%Hax & %Hwax & %Hatx & #Hobsx & Hx)".
    iApply fupd_aneris_wp.
    rewrite -Hhy.
    assert (h ≤ₚ (h ++ hfx ++ [ax])) as Hprefix.
    { by apply prefix_app_r. }
    iCombine "Hy" "Hobsx" as "HyObsx".
    iMod (OwnMemKey_obs_frame_prefix DB_addr "y" 1%Qp h (h ++ hfx ++ [ax]) ⊤
           with "HGinv HyObsx") as "(Hy & %HyHeq)"; [done|done|].
    iModIntro.
    assert (at_key "x" (h ++ hfx ++ [ax]) = Some ax) as HatAx.
    { rewrite app_assoc. by apply at_key_snoc_some. }
    wp_apply ("Hwr" $! "y" (SerVal #1) (h ++ hfx ++ [ax]) with "[//] [Hy Hobsx]").
    { iFrame "#∗". iExists _. iFrame "#∗". naive_solver. }
    iIntros "Hpost".
    wp_pures.
    iDestruct "Hpost" as (hfy ay) "(%Hay & %Hway & %Haty & #Hobsy & Hy)".
    rewrite -HipEq.
    iApply fupd_aneris_wp.
    rewrite -HatAx.
    assert ((h ++ hfx ++ [ax]) ≤ₚ ((h ++ hfx ++ [ax]) ++ hfy ++ [ay])) as Hprefix'.
    { by apply prefix_app_r. }
    iCombine "Hx" "Hobsy" as "HxObsy".
    iMod (OwnMemKey_obs_frame_prefix
            DB_addr "x" 1%Qp
            (h ++ hfx ++ [ax]) ((h ++ hfx ++ [ax]) ++ hfy ++ [ay])
           with "HGinv HxObsy") as "(Hx & %HxHeq)"; [done|done|].
    iModIntro.
    assert (at_key "y" ((h ++ hfx ++ [ax]) ++ hfy ++ [ay]) = Some ay) as HatAy.
    { rewrite app_assoc. by apply at_key_snoc_some. }
    iApply ("Hrel" with "[$Hcanrel Hx Hy]").
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
    iIntros "_".
    by iApply "HΦ".
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** The proof of the internal do_reads call *)
  (* ------------------------------------------------------------------------ *)
  Lemma wp_do_reads dl rd clt_10 clt_11 :
    ip_of_address clt_10 = ip_of_address clt_11 →
    {{{ GlobalInv ∗
        (∀ k q h, read_spec rd clt_11 k q h) ∗
        (dl_acquire_spec SharedRes (ip_of_address clt_10) dl) ∗
        (dl_release_spec SharedRes (ip_of_address clt_10) dl) ∗
        DLockCanAcquire (ip_of_address clt_10) dl SharedRes }}}
      do_reads dl rd @[ip_of_address clt_10]
    {{{ v, RET v; ⌜v = SOMEV #1⌝ }}}.
  Proof.
    iIntros (HipEq Φ).
    iIntros "(#HGinv & #Hrd & #Hacq & #Hrel & Har) HΦ".
    rewrite /do_reads.
    do 6 wp_pure _.
    iLöb as "IH".
    wp_pures.
    wp_apply ("Hacq" with "[$Har]").
    iIntros "(Hcanrel & Hres)".
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
      wp_apply ("Hrel" with "[$Hcanrel Hx Hy]").
      { iExists _, _, _.
        by iFrame "#∗". }
      iIntros "Har".
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
             wp_apply ("Hrel" with "[$Hcanrel Hx Hy]").
             { iExists _, _, _.
               by iFrame "#∗". }
             iIntros "Har".
             wp_pures.
             by iApply "HΦ".
      -- wp_pures.
         wp_apply ("Hrel" with "[$Hcanrel Hx Hy]").
         { iExists _, _, _.
           by iFrame "#∗". }
         iIntros "Har".
         do 4 (wp_pure _).
         by iApply ("IH" with "[$Har]").
  Qed.

  (* ------------------------------------------------------------------------ *)
  (** The proof of the node 0 (writer) *)
  (* ------------------------------------------------------------------------ *)

  Lemma proof_of_node0 (clt_00 clt_01 : socket_address) :
    ip_of_address clt_00 = ip_of_address clt_01 →
    {{{ GlobalInv ∗
        (* preconditions for subscribing client to dlock. *)
        dl_subscribe_client_spec SharedRes ∗
        unallocated {[clt_00]} ∗
        free_ports (ip_of_address clt_00) {[port_of_address clt_00]} ∗
        clt_00 ⤳ (∅, ∅) ∗
        dlm_sa ⤇ dl_reserved_server_socket_interp ∗
        (* preconditions to start a client proxy for the database. *)
        init_client_proxy_leader_spec leader_si ∗
        unallocated {[clt_01]} ∗
        db_sa ⤇ leader_si ∗
        clt_01 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_01) {[port_of_address clt_01]}
    }}}
      node0 #clt_00 #clt_01 #dlm_sa #db_sa @[ip_of_address clt_00]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (HipEq Φ).
    iIntros "(#HGinv & #HdlCltS & Hf0 & Hfps0 & Hpre) HΦ".
    iDestruct "Hpre" as "(Hclt00 & Hdlm_si & #HdbCltS & Hf1 & #Hdbsa & Hclt01 & Hfps1)".
    rewrite /node0.
    wp_pures.
    wp_apply ("HdlCltS" with "[$Hfps0 $Hclt00 $Hdlm_si $Hf0]").
    iIntros (dl) "(Hdl & #Hacq & #Hrel)".
    wp_pures.
    rewrite HipEq.
    simplify_eq /=.
    wp_apply ("HdbCltS" with "[$Hfps1 $Hclt01 $Hdbsa $Hf1]").
    iIntros (wr rd) "(#Hrd & Hwr)".
    iDestruct (get_simplified_write_spec with "Hwr") as "Hwr".
    wp_pures.
    rewrite -HipEq.
    wp_apply (wp_do_writes with "[HGinv Hwr Hdl]"); first done.
    { by iFrame "#∗". }
    done.
  Qed.

  Lemma proof_of_node1 (clt_10 clt_11 : socket_address) :
    ip_of_address clt_10 = ip_of_address clt_11 →
    {{{ GlobalInv ∗
        (* preconditions for subscribing client to dlock. *)
        dl_subscribe_client_spec SharedRes ∗
        unallocated {[clt_10]} ∗
        free_ports (ip_of_address clt_10) {[port_of_address clt_10]} ∗
        clt_10 ⤳ (∅, ∅) ∗
        dlm_sa ⤇ dl_reserved_server_socket_interp ∗
        (* preconditions to start a client proxy for the database. *)
        init_client_proxy_leader_spec leader_si ∗
        unallocated {[clt_11]} ∗
        db_sa ⤇ leader_si ∗
        clt_11 ⤳ (∅, ∅) ∗
        free_ports (ip_of_address clt_11) {[port_of_address clt_11]}
    }}}
      node1 #clt_10 #clt_11 #dlm_sa #db_sa @[ip_of_address clt_10]
    {{{ v, RET v; ⌜v = SOMEV #1⌝ }}}.
  Proof.
    iIntros (HipEq Φ).
    iIntros "(#HGinv & #HdlCltS & Hf0 &
                      Hfps0 & Hclt00 & #Hdlmsi & Hpre) HΦ".
    iDestruct "Hpre" as "(HdbCltS & Hf1 & #Hdbsa & Hclt01 & Hfps1)".
    rewrite /node1.
    wp_pures.
    wp_apply ("HdlCltS" with "[$Hfps0 $Hclt00 $Hdlmsi $Hf0]").
    iIntros (dl) "(Hdl & #Hacq & #Hrel)".
    wp_pures.
    rewrite HipEq.
    simplify_eq /=.
    wp_apply ("HdbCltS" with "[$Hfps1 $Hclt01 $Hdbsa $Hf1]").
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
Global Instance DLP : DL_params := DLSrv dlm_sa.
Global Instance DBP : DB_params := DBSrv db_sa db_Fsa.

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
         dl_server_start_service_spec SharedRes -∗
         dl_subscribe_client_spec SharedRes -∗
         init_leader_spec Init_leader leader_si leaderF_si -∗
         init_client_proxy_leader_spec leader_si -∗
         db_sa ⤇ leader_si -∗
         db_Fsa ⤇ leaderF_si -∗
         dlm_sa ⤇ dl_reserved_server_socket_interp -∗
         unallocated {[clt_sa00;clt_sa01;clt_sa10;clt_sa11]} -∗
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
    iIntros "#Hsrv0 #Hsrv1 #Hsrv2 Hf Hfree0 Hfree1 Hfree2 Hfree3".
    iIntros "Hsa0 Hsa1 Hsa2 Hsa3 Hsa4 Hsa5 Hsa6 HSrvInit0 HSrvInit1 HR".
    rewrite /main.
    (* replace ({[clt_sa00; clt_sa01; clt_sa10; clt_sa11]}) *)
    (*         with (({[clt_sa00; clt_sa01]} ∪ {[clt_sa10; clt_sa11]}) *)
    (*                :gset socket_address) by set_solver. *)
    iDestruct (unallocated_split with "Hf") as "[Hf Hf11]"; [set_solver|].
    iDestruct (unallocated_split with "Hf") as "[Hf Hf10]"; [set_solver|].
    iDestruct (unallocated_split with "Hf") as "[Hf00 Hf01]"; [set_solver|].
    (* Server 1. *)
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree0".
    iSplitR "Hsa0 Hsa1 HSrvInit1 HdbSrvS"; last first.
    { iNext. iIntros "Hfps".
      iApply ("HdbSrvS"
               with "[][][HSrvInit1 Hfps Hsa0 Hsa1]"); [eauto .. | | done ].
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
      iApply ("HdlSrvS" with "[Hfps HSrvInit0 Hsa2 HR]"); last done. iFrame "#∗". }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree2".
    iSplitR "Hsa3 Hsa4 Hf00 Hf01"; last first.
    { iNext. iIntros "Hfps".
      iApply (proof_of_node0 leader_si db_sa db_Fsa dlm_sa clt_sa00 clt_sa01
               with "[$HGinv $Hsa3 $Hsa4 Hfps $Hf00 $Hf01]"); [done| |done].
      iFrame "#∗".
      iDestruct (free_ports_split
                   "0.0.0.2"
                   {[80%positive]} {[81%positive]}) as "(Hfp1 & _)"; [set_solver|].
      iDestruct ("Hfp1" with "Hfps") as "(Hfp & Hfp')".
      iFrame "#∗". }
    iNext. wp_pures.
    wp_apply (aneris_wp_start {[80%positive; 81%positive]}); first done.
    iFrame "Hfree3".
    iSplitR "Hsa5 Hsa6 Hf10 Hf11"; last first.
    { iNext. iIntros "Hfps".
      iApply (proof_of_node1 leader_si db_sa db_Fsa dlm_sa clt_sa10 clt_sa11
               with "[$HGinv $Hsa5 $Hsa6 Hfps $Hf10 Hf11]"); [done| |done].
      iDestruct (free_ports_split
                   "0.0.0.3"
                   {[80%positive]} {[81%positive]}) as "(Hfp1 & _)"; [set_solver|].
      iDestruct ("Hfp1" with "Hfps") as "(Hfp & Hfp')".
      iFrame "#∗". }
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
    state_ms := ∅;
  |}.

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

Notation ShRes := (@SharedRes _ _ _ _ db_sa db_Fsa).

From aneris.examples.reliable_communication.lib.repdb.proof
     Require Import proof_of_db_init.

Theorem adequacy : aneris_adequate main "system" init_state (λ _, True).
Proof.
  set (Σ := #[anerisΣ dummy_model; DBΣ; SpecChanΣ]).
  eapply (@adequacy
            Σ dummy_model _ _ ips
            {[clt_sa00; clt_sa01; clt_sa10; clt_sa11; db_sa; db_Fsa; dlm_sa]} _ ∅ ∅);
    try set_solver; last first.
  2:{ apply dummy_model_finitary . }
  iIntros (Hdg) "".
  assert (DBPreG Σ) as HPreG by apply _.
  iMod (db_init_instance.(DB_init_setup) ⊤) as (DBRes) "Hdb";
    [solve_ndisj|set_solver|set_solver| ].
  iDestruct "Hdb"
    as (init_leader leader_si leaderF_si) "(#HGinv & #Hobs & Hkeys & HdbInit & #Hspecs)".
  iDestruct "Hspecs"
    as "((#HdbSrvS & #HdbCltS) & _)".
  iMod (dlinit.(DL_init_setup) ⊤ DLP ShRes)
    as (DLRes) "(HdlInit & #HdlSrvS & #HdlCltS)";
    [solve_ndisj| ].
  iMod (@main_spec
          _ _ _
          int_time leader_si leaderF_si init_leader DLRes DBRes) as "Hmain".
  iModIntro.
  iIntros "Hf Hb Hfg Hips _ _ _ _ _".
  simpl in *.
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
  (* TODO: Split things *)
  iDestruct (unallocated_split with "Hf") as "[Hf Hfdlm_sa]"; [set_solver|].
  iDestruct (unallocated_split with "Hf") as "[Hf Hfdb_Fsa]"; [set_solver|].
  iDestruct (unallocated_split with "Hf") as "[Hf Hfdb_sa]"; [set_solver|].
  iApply (aneris_wp_socket_interp_alloc_singleton dl_reserved_server_socket_interp with "Hfdlm_sa").
  iIntros "Hfdlm_si".
  iApply (aneris_wp_socket_interp_alloc_singleton leaderF_si with "Hfdb_Fsa").
  iIntros "Hfdb_Fsi".
  iApply (aneris_wp_socket_interp_alloc_singleton leader_si with "Hfdb_sa").
  iIntros "Hfdb_si".
  iApply ("Hmain" with
           "HGinv HdlSrvS HdlCltS HdbSrvS HdbCltS
            Hfdb_si Hfdb_Fsi Hfdlm_si Hf
            Hip0 Hip1 Hip2 Hip3
            Hm0 Hm1 Hm2 Hc00 Hc01 Hc10 Hc11
            HdlInit HdbInit").
  iExists None, None,  [].
  iDestruct (big_sepS_delete _ _ "x" with "Hkeys") as "[Hx Hkeys]";
    first set_solver.
  iDestruct (big_sepS_delete _ _ "y" with "Hkeys") as "[Hy _]";
   first set_solver.
  iFrame "#∗".
  iPureIntro; split_and!; [done|done|].
  intros. naive_solver.
Qed.
