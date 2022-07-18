From iris.algebra Require Import excl.
From trillium.prelude Require Import finitary.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof set_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import tactics proofmode.
From actris.channel Require Export proto.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.examples.reliable_communication Require Import user_params.
From aneris.examples.reliable_communication.spec Require Import resources proofmode api_spec prelude ras.
From aneris.examples.reliable_communication.lib.dlm Require Import dlm_code dlm_prelude dlm_spec.
From aneris.examples.reliable_communication.instantiation
     Require Import
     instantiation_of_resources
     instantiation_of_init.

Import client_server_code.
Import lock_proof.

Section DL_proof_of_code.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!DL_params}.
  Context (dl_locked_internal : iProp Σ).
  Context (dl_locked_internal_exclusive : dl_locked_internal -∗ dl_locked_internal -∗ False).
  Context (R : iProp Σ).

  Notation srv_sa := DL_server_addr.
  Notation srv_ip := (ip_of_address DL_server_addr).
  Notation srv_port := (port_of_address DL_server_addr).
  Notation dlN := (DL_namespace .@ "lk").

  Definition dlock_protocol_aux (rec : bool -d> iProto Σ) : bool -d> iProto Σ :=
    λ b, if b then
           (<!> MSG #"acquire" ;
           <?> MSG #"acquire_OK" {{ dl_locked_internal ∗ R }};
           rec (negb b))%proto
         else
           (<!> MSG #"release" {{ dl_locked_internal ∗ R }};
           rec (negb b))%proto.

  Global Instance dlock_protocol_aux_contractive : Contractive dlock_protocol_aux.
  Proof. solve_proper_prepare. f_equiv; solve_proto_contractive. Qed.
  Definition dlock_protocol := fixpoint (dlock_protocol_aux).
  Global Instance dlock_protocol_unfold s :
    ProtoUnfold (dlock_protocol s) (dlock_protocol_aux dlock_protocol s).
  Proof. apply proto_unfold_eq, (fixpoint_unfold dlock_protocol_aux). Qed.

  Local Instance UP : Reliable_communication_service_params :=
    {| RCParams_clt_ser := string_serialization;
      RCParams_srv_ser := string_serialization;
      RCParams_srv_ser_inj := ser_inj.string_ser_is_ser_injective;
      RCParams_srv_ser_inj_alt := ser_inj.string_ser_is_ser_injective_alt;
      RCParams_clt_ser_inj := ser_inj.string_ser_is_ser_injective;
      RCParams_clt_ser_inj_alt := ser_inj.string_ser_is_ser_injective_alt;
      RCParams_srv_saddr := DL_server_addr;
      RCParams_protocol := dlock_protocol true;
      RCParams_srv_N := DL_namespace;
    |}.

  Context `{cmh: !@Chan_mapsto_resource Σ}.
  Context `{SnRes : !SessionResources UP}.
  Context `{HspecS : !Reliable_communication_Specified_API_session cmh}.
  Context `{HspecN : !Reliable_communication_Specified_API_network UP SnRes}.

  Definition is_dlock_lock ip γlk lk : iProp Σ :=
    is_lock dlN ip γlk lk (R ∗ dl_locked_internal).

  Definition is_dlock_server_connection_state
             (ip : ip_address) (γlk : gname) (c : val) (b : bool) : iProp Σ :=
    (if b then ⌜True⌝%I else locked γlk) ∗
    c ↣{ ip, string_serialization} (iProto_dual (dlock_protocol b)).

  Definition dl_acquire_internal_spec (sa : socket_address) (dl : val) : Prop :=
    {{{ dl ↣{ ip_of_address sa, string_serialization }
           (dlock_protocol true) }}}
      dlock_acquire dl @[ip_of_address sa]
    {{{ RET #(); dl ↣{ ip_of_address sa, string_serialization }
                    (dlock_protocol false) ∗
                 dl_locked_internal ∗ R }}}.

  Lemma dl_acquire_internal_spec_holds sa dl : dl_acquire_internal_spec sa dl.
  Proof.
    iIntros (Φ) "Hdlk HΦ".
    rewrite /dlock_acquire.
    wp_pures.
    wp_send with "[//]".
    wp_pures.
    wp_recv as "[Hdlk_key HR]".
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Definition dl_release_internal_spec (sa : socket_address) (dl : val) : Prop :=
    {{{ dl ↣{ ip_of_address sa, string_serialization } (dlock_protocol false) ∗
        dl_locked_internal ∗ R }}}
       dlock_release dl @[ip_of_address sa]
     {{{ RET #(); dl ↣{ ip_of_address sa, string_serialization } (dlock_protocol true) }}}.

  Lemma dl_release_internal_spec_holds sa dl : dl_release_internal_spec sa dl.
  Proof.
    iIntros (Φ) "(Hdlk & Hkey & HR) HΦ".
    rewrite /dlock_release.
    wp_pures.
    wp_send with "[$Hkey $HR]".
    by iApply "HΦ"; eauto with iFrame.
  Qed.

Definition dl_subscribe_client_internal_spec sa : iProp Σ :=
    {{{ unfixed {[sa]} ∗
        free_ports (ip_of_address sa) {[port_of_address sa]} ∗
        DL_server_addr ⤇ reserved_server_socket_interp ∗
        sa ⤳ (∅, ∅) }}}
      dlock_subscribe_client #sa #DL_server_addr @[ip_of_address sa]
    {{{ dl, RET dl; dl ↣{ ip_of_address sa, string_serialization }
                       (dlock_protocol true) ∗
                    ⌜dl_acquire_internal_spec sa dl⌝ ∗
                    ⌜dl_release_internal_spec sa dl⌝ }}}.

  Lemma dl_subscribe_client_internal_spec_holds sa :
    ⊢ dl_subscribe_client_internal_spec sa.
  Proof.
    iIntros (Φ) "!#".
    iIntros "(Hf & Hfp & #Hsi & Hmh) HΦ".
    rewrite /dlock_subscribe_client.
    wp_pures.
    wp_apply (RCSpec_make_client_skt_spec with "[$Hmh $Hsi $Hf $Hfp][HΦ]").
    iNext. iIntros (skt) "Hcl". wp_pures.
    wp_apply (RCSpec_connect_spec with "[$Hcl][HΦ]").
    iNext. iIntros (dl) "Hc". wp_pures.
    iApply "HΦ".
    iFrame.
    by eauto using dl_acquire_internal_spec_holds,
      dl_release_internal_spec_holds.
  Qed.

  Lemma wp_listen_to_client c lk γlk b :
    {{{ is_dlock_server_connection_state srv_ip γlk c b ∗
         is_lock dlN srv_ip γlk lk (dl_locked_internal ∗ R) }}}
      listen_to_client lk c @[ip_of_address RCParams_srv_saddr]
      {{{ v, RET v ; False }}}.
  Proof.
    iIntros (Φ) "(Hci & #Hlk) HΦ". rewrite /listen_to_client.
    do 6 wp_pure _.
    iLöb as "IH" forall (b).
    iDestruct "Hci" as "[Hlkey Hci]".
    destruct b.
    - wp_recv as "_".
      wp_pures. wp_lam. wp_pures.
      wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#".
      iIntros (v) "(-> & HlKey & HdlkKey & HR)".
      wp_pures.
      wp_send with "[$HdlkKey $HR]".
      wp_pure _. wp_lam.
      by iApply ("IH" with "[$Hci $HlKey]").
    - wp_pures.
      simpl in *.
      wp_recv as "[Hdlk HR]".
      wp_pures.
      wp_apply (release_spec with "[$Hlk $Hlkey $HR $Hdlk]").
      iIntros (v ->). do 2 wp_pure _.
      iApply ("IH" with "[Hci]").
      rewrite /is_dlock_server_connection_state.
      iFrame. eauto with iFrame.
  Qed.

  Lemma wp_connections_loop skt lk γlk :
    {{{ RCParams_srv_saddr ⤇ reserved_server_socket_interp ∗
          SrvListens skt ∗
        is_lock dlN srv_ip γlk lk (dl_locked_internal ∗ R) }}}
      connections_loop skt lk @[ip_of_address RCParams_srv_saddr]
      {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "(#Hsi & Hlistens & #Hlk) HΦ". rewrite /connections_loop.
    do 6 (wp_pure _).
    iLöb as "IH".
    wp_pure _.
    wp_smart_apply (RCSpec_accept_spec with "[$Hlistens]").
    iIntros (c clt_addr) "(Hlistens & Hc)".
    wp_pures.
    wp_apply (aneris_wp_fork with "[-]").
    iSplitL "Hlistens".
    - iNext. do 2 wp_pure _. iApply ("IH" with "[$Hlistens]"). by iIntros.
    - iNext. wp_pures. iApply (wp_listen_to_client with "[$Hc $Hlk]").
      eauto with iFrame.
  Qed.

  Definition dl_server_start_service_internal_spec : Prop :=
    {{{ free_ports srv_ip {[srv_port]} ∗
        DL_server_addr ⤇ reserved_server_socket_interp ∗
        srv_sa ⤳ (∅, ∅) ∗
        SrvInit ∗
        dl_locked_internal ∗ R }}}
      dlock_start_service #srv_sa @[srv_ip]
    {{{ RET #(); True }}}.

  Lemma dl_server_start_service_internal_spec_holds : dl_server_start_service_internal_spec.
  Proof.
    iIntros (Φ) "Hdlk HΦ".
    iDestruct "Hdlk" as "(Hfp & #Hsi & Hmh & Hinit & Hdlocked & HR)".
    rewrite /dlock_start_service.
    wp_pures.
    wp_apply (RCSpec_make_server_skt_spec with "[$Hmh $Hsi $Hinit $Hfp][Hdlocked HR HΦ]").
    iNext. iIntros (skt) "Hcl". wp_pures.
    wp_apply (newlock_spec dlN srv_ip (dl_locked_internal ∗ R) with "[$HR $Hdlocked]").
    iIntros (lk γlk) "#Hlk".
    wp_pures.
    wp_apply (RCSpec_server_listen_spec with "[$Hcl][HΦ]").
    iNext. iIntros "Hp". wp_pures.
    iApply (wp_connections_loop with "[$]").
    iNext. by iIntros.
  Qed.

End DL_proof_of_code.

Section DL_proof_of_resources.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!DL_params}.
  Context (dl_locked_internal : iProp Σ).
  Context (Hexcl: dl_locked_internal -∗ dl_locked_internal -∗ False).
  Context (Html: Timeless dl_locked_internal).
  Context (R : iProp Σ).
  Context `{cmh: !@Chan_mapsto_resource Σ}.
  Context `{SnRes : !SessionResources (UP dl_locked_internal R)}.

  Lemma Hexcl_init : dl_locked_internal ∗ SnRes.(SrvInit) -∗
                    dl_locked_internal ∗ SnRes.(SrvInit) -∗ False.
  Proof.
    iIntros "(H1 & _) (H2 & _)".
    by iApply (Hexcl with "[H1][H2]").
  Qed.

  Lemma Html_init : Timeless (dl_locked_internal ∗ SnRes.(SrvInit)).
  Proof.
    apply bi.sep_timeless; first done. apply _.
  Qed.

  Global Instance dlri : DL_resources := {
    DLockCanAcquire ip dl R :=
      dl ↣{ ip, string_serialization }
         (dlock_protocol dl_locked_internal R true);
    DLockCanRelease ip dl R :=
        (dl ↣{ ip, string_serialization }
           (dlock_protocol dl_locked_internal R false) ∗
        dl_locked_internal)%I;
    dl_service_init := dl_locked_internal ∗ SrvInit;
    dl_service_init_exclusive := Hexcl_init;
    dl_service_init_timeless := Html_init;
    dl_reserved_server_socket_interp := SnRes.(reserved_server_socket_interp)
  }.

End DL_proof_of_resources.

Section DL_proof_of_the_init.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!DL_params}.
  Context `{!Reliable_communication_init}.

  Definition dl_locked_internal (γdlk : gname) : iProp Σ := own γdlk (Excl ()).
  Lemma dl_locked_internal_exclusive γdlk : dl_locked_internal γdlk -∗ dl_locked_internal γdlk -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.
  Global Instance dlt γdlk : Timeless (dl_locked_internal γdlk).
  Proof. apply _. Qed.

  Lemma init_setup_holds (E : coPset) (R : iProp Σ) :
    ↑DL_namespace ⊆ E →
    ⊢ |={E}=>
          ∃ (DLRS : DL_resources),
            dl_service_init ∗
             (dl_server_start_service_spec R) ∗
             (dl_subscribe_client_spec R).
  Proof.
    iIntros (HE).
    iMod (own_alloc (Excl ())) as (γdlk) "Hdlk"; first done.
    set (DLUP := UP (own γdlk (Excl ())) R).
    assert (DL_namespace = DLUP.(RCParams_srv_N)) as Hnmeq by done.
    rewrite Hnmeq in HE.
    iMod (Reliable_communication_init_setup E DLUP HE)
      as (chn sgn) "(Hinit & Hspecs)".
    iDestruct "Hspecs"
    as "(
           %HmkClt & %HmkSrv
         & %Hconnect
         & %Hlisten & %Haccept
         & %Hsend & %HsendTele
         & %HtryRecv & %Hrecv)".
    eset (dlr := dlri (dl_locked_internal γdlk) (dl_locked_internal_exclusive γdlk) (dlt γdlk) R).
    iExists dlr.
    iFrame.
    iSplitL.
    - iModIntro.
      iIntros (Φ) "!#".
      iIntros "(Hfp & Hmh & #Hsi & HR & (Hinit & HsrvInit)) HΦ".
      iDestruct (dl_server_start_service_internal_spec_holds) as "HserviceSpec".
      split; try done.
      split; try done.
      iApply ("HserviceSpec" with "[$Hfp $Hsi $Hmh $HR $Hinit $HsrvInit][$]").
    - iModIntro.
      iIntros (sa).
      iIntros (Φ) "!#".
      iIntros "(Hf & Hfp & Hmh & #Hsi) HΦ".
      iDestruct (dl_subscribe_client_internal_spec_holds) as "#HclientSpec".
      split; try done.
      split; try done.
      iApply ("HclientSpec" with "[$Hf $Hfp $Hmh $Hsi][HΦ]").
      rewrite /dlock_subscribe_client.
      iNext. iIntros (dl) "(Hinit & %HaS & %HrS)".
      iApply "HΦ". iFrame.
      rewrite /dl_acquire_internal_spec.
      rewrite /dl_release_internal_spec.
      iSplit.
      + iIntros (Ψ).
        specialize (HaS Ψ).
        iIntros "!> Hr HΨ".
        iApply (HaS with "[$Hr][HΨ]").
        iNext. iIntros "[Hrel Hr]".
        iApply "HΨ". by iFrame.
      + iIntros (Ψ).
        specialize (HrS Ψ).
        iIntros "!> [[Hrel Hlocked] Hr] HΨ".
        iApply (HrS with "[$Hrel $Hlocked $Hr][HΨ]").
        iNext. iIntros "Hr".
        iApply "HΨ". by iFrame.
  Qed.

End DL_proof_of_the_init.

Section DL_proof_of_the_init_class.
  Context `{!anerisG Mdl Σ}.
  Context `{!lockG Σ}.
  Context `{!SpecChanG Σ}.
  Context `{!DL_params}.

  Global Instance dlinit : DL_init.
  Proof.
    split. iIntros (E DL R HE).
    iMod (init_setup_holds E R HE) as  (dlr) "(Ha & Hb & Hc)".
    iModIntro.
    iExists dlr.
    by iFrame.
  Qed.

End DL_proof_of_the_init_class.
