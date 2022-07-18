From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof set_proof list_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.aneris_lang Require Import tactics proofmode.
From actris.channel Require Export proto.
From aneris.aneris_lang.program_logic Require Import aneris_lifting.
From aneris.examples.reliable_communication Require Import user_params.
From aneris.examples.reliable_communication.spec
	  Require Import resources proofmode api_spec.
From aneris.examples.reliable_communication.lib.reliable_rpc
	  Require Import reliable_rpc_code params.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.

Import reliable_rpc_code.
Import lock_proof.
Import client_server_code.

Section RPC_proof_of_code.
	Context `{ !anerisG Mdl Σ, !lockG Σ}.
	Context `{ !RPC_user_params }.
	Context `{ IP : !@RPC_interface_params Σ }.
	Notation srv_ip := (ip_of_address RPC_saddr).
	


	Definition req_prot_aux (rec : iProto Σ) : iProto Σ :=
		(<! (RP : RPC_rpc_params) (s_arg : string) (arg : val) (argd : RP.(RPC_arg_data)) >
			MSG (#RP.(RPC_name), #s_arg)%V 
			{{ ⌜In RP IP.(RPC_inter)⌝ ∗ ⌜s_is_ser RP.(RPC_arg_ser) arg s_arg⌝ ∗ RP.(RPC_pre) arg argd }} ;
		<? (s_rep : string) (rep : val) (repd : RP.(RPC_rep_data)) >
			MSG #s_rep 
			{{ ⌜s_is_ser RP.(RPC_rep_ser) rep s_rep⌝ ∗ RP.(RPC_post) rep argd repd }};
		rec)%proto.

	Instance req_prot_aux_contractive : Contractive (req_prot_aux).
	Proof. solve_proto_contractive. Qed.
	Definition req_prot : iProto Σ := fixpoint (req_prot_aux).
	Global Instance req_prot_unfold :
		ProtoUnfold req_prot (req_prot_aux req_prot).
	Proof. apply proto_unfold_eq, fixpoint_unfold. Qed.



	Global Instance MT_UP : Reliable_communication_service_params :=
	{| RCParams_clt_ser := prod_serialization string_serialization string_serialization;
		RCParams_srv_ser := string_serialization;
		RCParams_srv_ser_inj := string_ser_is_ser_injective;
		RCParams_srv_ser_inj_alt := string_ser_is_ser_injective_alt;
		RCParams_clt_ser_inj := prod_ser_is_ser_injective string_serialization string_serialization string_ser_is_ser_injective string_ser_is_ser_injective;
		RCParams_clt_ser_inj_alt := prod_ser_is_ser_injective_alt string_serialization string_serialization string_ser_is_ser_injective_alt string_ser_is_ser_injective_alt;
		RCParams_srv_saddr := RPC_saddr;
		RCParams_protocol := req_prot;
		RCParams_srv_N := RPC_mN;
	|}.

	Context `{cmh: !@Chan_mapsto_resource Σ}.
	Context `{SnRes : !SessionResources MT_UP}.
	Context `{HspecS : !Reliable_communication_Specified_API_session cmh}.
	Context `{HspecN : !Reliable_communication_Specified_API_network MT_UP SnRes}.

	Definition call_handler_spec (RP : RPC_rpc_params) (II : RPC_interface_implementation IP) : iProp Σ :=
		{{{ ⌜In RP IP.(RPC_inter)⌝ }}}
			call_handler II.(RPC_inter_val) #RP.(RPC_name) @[srv_ip]
		{{{ h, RET h; ⌜is_impl_handler_of_rpc h RP⌝ }}}.

	Lemma call_handler_spec_holds (RP : RPC_rpc_params) (II : RPC_interface_implementation IP) :
		⊢ call_handler_spec RP II.
	Proof.
		rewrite /call_handler_spec.
		iIntros (Φ). iModIntro. iIntros "%HRP Hcont".
		rewrite /call_handler.
		wp_pures. iApply "Hcont".
		iPureIntro. rewrite /is_impl_handler_of_rpc.
		iIntros (argv argd s_arg Ψ) "[%Hargser Hpre] Hcont".
		wp_pures. wp_lam. wp_pure _.
		iAssert 
		(
			(∀ (inter : val),
			(∃ (inter_list : list val) (inter_params : list RPC_rpc_params),
			⌜is_list inter_list inter ∧
			is_list_of_interface inter_list inter_params ∧
			List.NoDup (map (fun RP => RP.(RPC_name)) inter_params) ∧
			In RP inter_params⌝) -∗
			WP let: "func" := network_util_code.unSOME
                    ((rec: "loop" "m" :=
                        match: "m" with
                          InjL <> => InjL #()
                        | InjR "p" =>
                          if: Fst (Fst "p") =
                              #RP.(RPC_name)
                          then InjR (Snd (Fst "p"))
                          else "loop" (Snd "p")
                        end)%V inter) in
   			"func" #s_arg @[srv_ip] {{ v, Ψ v }})%I
		) with "[Hpre Hcont]" as "Hassert".
		2 : 
		{
			iApply "Hassert".
			iExists RPC_inter_list, IP.(RPC_inter).
			iPureIntro. split.
			apply RPC_inter_spec. split.
			apply RPC_inter_spec. split.
			apply RPC_inter_nodup. apply HRP.
		}
		iLöb as "IH".
		iIntros (inter) "H".
		iDestruct "H" as (inter_list inter_params) "(%Hlist & %Hlistof & %Hnodup & %Hin)".
		destruct inter_params as [| RP' inter']; first contradiction.
		destruct inter_list; first contradiction.
		simpl in Hlist. destruct Hlist as [l' [-> Hlist]].
		destruct v; try contradiction.
		destruct Hlistof as [-> [Hhand Hlistof]]. 

		destruct Hin as [-> | Hin].
		- wp_pures.
		  case_bool_decide; last contradiction.
		  rewrite /network_util_code.unSOME. wp_pures.
		  wp_apply (Hhand with "[$Hpre]"); first done.
		  iApply "Hcont".
		- wp_pures.
		  case_bool_decide as Hnameeq.
		  { assert (RP.(RPC_name) = RP'.(RPC_name)) as Heq.
		  	{ by inversion Hnameeq. }  
		  	simpl in Hnodup. apply (NoDup_cons_iff RPC_name _) in Hnodup. 
			destruct Hnodup as [Hnotin _].
			apply (@in_map _ _ (λ RP : RPC_rpc_params, RP.(RPC_name)) _ _) in Hin.
			rewrite Heq in Hin. contradiction.
		  }
		  wp_if. wp_proj. 
		  iApply ("IH" with "[$Hpre] [$Hcont]").
		  iExists inter_list, inter'. iPureIntro.
		  split. assumption.
		  split. assumption.
		  split.
		  simpl in Hnodup. inversion Hnodup.
		  assumption. assumption.
	Qed.

	Lemma service_loop_proof (II : RPC_interface_implementation IP) (c : val) :
		{{{ c ↣{ ip_of_address RPC_saddr, string_serialization } iProto_dual req_prot }}}
		service_loop c II.(RPC_inter_val) #() @[srv_ip]
		{{{ RET #(); ⌜True⌝ }}}.
	Proof.
		iIntros (Φ) "Hc Hcont".
		rewrite /service_loop. do 8 wp_pure _.
		iLöb as "IH".
		wp_pures.
		wp_recv (rpc s_arg arg argd) as "(%Hin & Hser & Hpre)".
		wp_pures.
		(* wp_apply (monitor_acquire_spec with "[Hmon]"); first by iFrame "#".
		iIntros (v) "(-> & Hlocked & HR)". wp_seq. *)
		wp_apply (call_handler_spec_holds); first by iFrame "#".
		iIntros (h Hh). rewrite /is_impl_handler_of_rpc.
		wp_apply (Hh with "[$Hpre $Hser]").
		iIntros (repv repd s_rep) "[Hser Hpost]".
		wp_let.
		(* wp_apply (monitor_release_spec with "[$Hmon $HR $Hlocked]").
		iIntros (v ->). wp_seq. *)
		wp_send with "[$Hser $Hpost]". wp_seq.
		iApply ("IH" with "[$Hc] [$Hcont]").
	Qed.
		
		
		

	Lemma accept_new_connections_loop_proof (II : RPC_interface_implementation IP) skt  :
		{{{ RPC_saddr ⤇ reserved_server_socket_interp ∗
			SrvListens skt }}}
		accept_new_connections_loop skt II.(RPC_inter_val) #() @[srv_ip]
		{{{ RET #(); False }}}.
	Proof.
		iIntros (Φ) "[#Hsi Hlistens] Hcont".
		rewrite /accept_new_connections_loop.
		do 8 wp_pure _.
		iLöb as "IH". wp_pure _.
		wp_smart_apply (RCSpec_accept_spec with "[$Hlistens]").
		iIntros (c client_addr v) "(-> & Hlistens & Hc)". wp_pures.
		wp_apply (aneris_wp_fork with "[-]").
		iSplitL "Hlistens".
		- iNext.
			do 2 wp_pure _.
			iApply ("IH" with "[$Hlistens]").
			by iIntros.
		- iNext.
			wp_pures.
			simpl in *.
			by wp_apply (service_loop_proof with "[$Hc]").
		Qed.

	Definition init_server_stub_internal_spec (II : RPC_interface_implementation IP) : iProp Σ :=
		∀ A,
		{{{ ⌜RPC_saddr ∈ A⌝ ∗
				fixed A ∗
				free_ports (ip_of_address RPC_saddr) {[port_of_address RPC_saddr]} ∗
				RPC_saddr ⤇ reserved_server_socket_interp ∗
				RPC_saddr ⤳ (∅, ∅) ∗
				SrvInit }}}
			init_server_stub #RPC_saddr II.(RPC_inter_val) @[srv_ip]
		{{{ RET #(); ⌜False⌝ }}}.

	Lemma init_server_stub_internal_spec_holds (II : RPC_interface_implementation IP) :
		⊢ init_server_stub_internal_spec II.
	Proof.
		iIntros (A Φ) "!#". 
		iIntros "(#HA & #Hfix & Hfp & #Hsi & Hhist & Hinit) Hcont".
		rewrite /init_server_stub. wp_pures.
		wp_apply (RCSpec_make_server_skt_spec with "[$HA $Hhist $Hsi $Hfix $Hinit $Hfp] [Hcont]").
		iNext. iIntros (skt) "Hcl". wp_pures.
		wp_apply (RCSpec_server_listen_spec with "[$Hcl] [Hcont]").
		iNext. iIntros (v) "[-> Hlistens]". wp_seq.
		wp_apply (accept_new_connections_loop_proof with "[$]").
		iApply "Hcont".
	Qed.




	Definition implement_spec {RP : RPC_rpc_params} (IMP : RPC_implementation_params RP) : iProp Σ :=
		{{{ ⌜In RP IP.(RPC_inter)⌝ }}}
			implement IMP.(RPC_val) IMP.(RPC_handler) @[srv_ip]
		{{{ h, RET (#RP.(RPC_name), h)%V; ⌜is_impl_handler_of_rpc h RP⌝ }}}.

	Lemma implement_spec_holds {RP : RPC_rpc_params} (IMP : RPC_implementation_params RP) : 
		⊢ implement_spec IMP.
	Proof.
		iIntros (Φ) "!#". iIntros (HRP) "Hcont".
		rewrite /implement.
		rewrite RPC_rpc_match. wp_pures.
		iApply "Hcont". iPureIntro.
		rewrite /is_impl_handler_of_rpc.
		iIntros (argv argd s_arg Ψ) "[%Hargser Hpre] Hcont".
		wp_pures. wp_apply (s_deser_spec RPC_arg_ser); first done.
		iIntros "_". wp_pures.
		wp_apply (RPC_handler_spec with "Hpre").
		iIntros (repv repd) "[%Hseria Hpost]". wp_pures.
		wp_apply (s_ser_spec RPC_rep_ser); first done.
		iIntros (s Hrepser). iApply "Hcont".
		by iFrame.
	Qed.

	Definition init_client_stub_internal_spec : iProp Σ :=
		∀ A clt_addr,
		{{{ ⌜clt_addr ∉ A⌝ ∗ 
				fixed A ∗ 
				free_ports (ip_of_address clt_addr) {[port_of_address clt_addr]} ∗
				clt_addr ⤳ (∅, ∅) ∗ 
				RPC_saddr ⤇ reserved_server_socket_interp }}}
			init_client_stub #clt_addr #RPC_saddr @[ip_of_address clt_addr]
		{{{ chan, RET chan; chan ↣{ip_of_address clt_addr,RCParams_clt_ser} RCParams_protocol }}}.

	Lemma init_client_stub_internal_spec_holds : ⊢ init_client_stub_internal_spec.
	Proof.
		rewrite /init_client_stub_internal_spec.
		iIntros (A clt_addr Φ) "!#". iIntros "(#Hna & #Hfix & Hfp & Hhist & #Hsi) Hcont".
		rewrite /init_client_stub. wp_pures.
		wp_apply (RCSpec_make_client_skt_spec with "[$Hfix $Hfp $Hhist $Hsi]"). iAssumption.
		iIntros (skt) "Hcl". wp_pures.
		wp_apply (RCSpec_connect_spec with "[$Hcl]").
		iIntros (c) "Hcl". wp_pures.
		by iApply "Hcont".
	Qed.

	Definition call_internal_spec {RP : RPC_rpc_params} (IMP : RPC_implementation_params RP) : iProp Σ :=
		∀ chan clt_addr argv argd,
		{{{ ⌜In RP IP.(RPC_inter)⌝ ∗ 
			chan ↣{ip_of_address clt_addr,RCParams_clt_ser} RCParams_protocol ∗
			⌜Serializable RP.(RPC_arg_ser) argv⌝ ∗ 
			RP.(RPC_pre) argv argd }}}
			call chan IMP.(RPC_val) argv @[ip_of_address clt_addr]
		{{{ repv repd, RET repv; 
			chan ↣{ip_of_address clt_addr,RCParams_clt_ser} RCParams_protocol ∗
			RP.(RPC_post) repv argd repd }}}.

	Lemma call_internal_spec_holds {RP : RPC_rpc_params} (IMP : RPC_implementation_params RP) :
		⊢ call_internal_spec IMP.
	Proof.
		rewrite /call_internal_spec.
		iIntros (chan clt_addr argv argd Φ) "!#".
		iIntros "(%HRP & Hc & %Hseria & Hpre) Hcont".
		rewrite /call. wp_pures.
		rewrite RPC_rpc_match. wp_pures.
		wp_apply s_ser_spec; first done.
		iIntros (s Hisserarg). wp_pures.
		wp_send with "[$Hpre]"; first done.
		wp_seq.
		wp_recv (s_rep repv repd) as "[%Hisserep Hpost]". wp_pures.
		wp_apply s_deser_spec; first done.
		iIntros "_". iApply "Hcont". iFrame.
	Qed.



	(* Definition rpc_spec {RP : RPC_rpc_params} (f : val) clt_addr : iProp Σ :=
		∀ argv argd,
		{{{ ⌜Serializable RP.(RPC_arg_ser) argv⌝ ∗ RP.(RPC_pre) argv argd }}}
			f argv @[ip_of_address clt_addr]
		{{{ repv repd, RET repv; RP.(RPC_post) repv argd repd }}}.

	Definition call_internal_spec {RP : RPC_rpc_params} (IMP : RPC_implementation_params RP) : iProp Σ :=
		∀ chan clt_addr,
		{{{ ⌜In RP IP.(RPC_inter)⌝ ∗ chan ↣{ip_of_address clt_addr,RCParams_clt_ser} RCParams_protocol }}}
			call chan IMP.(RPC_val) @[ip_of_address clt_addr]
		{{{ f, RET f; @rpc_spec RP f clt_addr }}}.

	Lemma call_internal_spec_holds {RP : RPC_rpc_params} (IMP : RPC_implementation_params RP) :
		⊢ call_internal_spec IMP.
	Proof.
		rewrite /call_internal_spec.
		iIntros (chan clt_addr Φ) "!#".
		iIntros "[%HRP Hc] Hcont".
		rewrite /call. wp_pures.
		(* rewrite /rpc_spec. *)
		iApply "Hcont".
		rewrite /rpc_spec. 
		iIntros (argv argd Ψ) "!> [%Hseria Hpre] Hcont".
		(* iDestruct "Hc" as (c lk γ ->) "Hlk". wp_pures. *)
		rewrite RPC_rpc_match. wp_pures.
		wp_apply s_ser_spec; first done.
		iIntros (s Hisserarg). wp_pures.
		wp_send with "[$Hpre]"; first done.
		wp_seq.
		wp_recv (s_rep repv repd) as "[%Hisserep Hpost]". wp_pures.
		wp_apply (release_spec with "[$Hlk $Hc $Hlocked]").
		iIntros (? ->). wp_seq. wp_pures. 
		wp_apply s_deser_spec; first done.
		iIntros "_". by iApply "Hcont".
	Qed. *)

	Global Definition Channel chan clt_addr := chan ↣{ip_of_address clt_addr,RCParams_clt_ser} RCParams_protocol.

End RPC_proof_of_code.

From aneris.examples.reliable_communication.spec
     Require Import ras.
From aneris.examples.reliable_communication.instantiation
     Require Import instantiation_of_init.
From aneris.examples.reliable_communication.lib.reliable_rpc
     Require Import api_spec.

Section RPC_proof_of_init.
	Context `{ !anerisG Mdl Σ, !lockG Σ}.
	Context `{ !RPC_user_params }.
	Context `{ IP : !@RPC_interface_params Σ }.
	Context `{ !SpecChanG Σ }.

	Lemma RPC_init_setup_holds (E : coPset) :
	↑RPC_mN ⊆ E →
    ⊢ |={E}=> ∃ (srv_si : message → iProp Σ) (SrvInit : iProp Σ)
								(Channel : val → socket_address → iProp Σ),
			SrvInit ∗
			(∀ (II : RPC_interface_implementation IP), 
				init_server_stub_spec SrvInit srv_si II) ∗
			(init_client_stub_spec srv_si Channel) ∗
			( ∀ (RP : RPC_rpc_params) (IMP : RPC_implementation_params RP),
				@call_spec _ _ _ _ IP Channel RP IMP).
	Proof.
		iIntros (HE).
		iMod (Reliable_communication_init_setup E MT_UP HE)
      		as (chn sgn) "(Hinit & Hspecs)".
		iDestruct "Hspecs"
		as "(
			%HmkClt & %HmkSrv
			& %Hconnect
			& %Hlisten & %Haccept
			& %Hsend & %HsendTele
			& %HtryRecv & %Hrecv)".
		iExists reserved_server_socket_interp, SrvInit, Channel.
		iFrame. iModIntro. iSplitL.
		- iIntros (II). rewrite /init_server_stub_spec.
			iIntros (A Φ) "!#".
			iIntros "(#Hsi & Hfix & HA & Hhist & Hfp & Hinit) Hcont".
			iApply (init_server_stub_internal_spec_holds with "[$HA $Hfix $Hfp $Hsi $Hhist $Hinit][$]").
			Unshelve. done. done. done.
		- iSplitL.
			+ rewrite /init_client_stub_spec.
				iIntros (A clt_addr Φ) "!#".
				iIntros "(#Hsi & Hfix & HA & Hhist & Hfp) Hcont".
				iApply (init_client_stub_internal_spec_holds with "[$HA $Hfix $Hfp $Hsi $Hhist][$]").
				Unshelve. done.
			+ iIntros (RP IMP). rewrite /call_spec.
				iIntros (chan clt_addr argv argd Φ) "!#".
				iIntros "(HRP & Hchan & Hseria & Hpre) Hcont".
				iApply (call_internal_spec_holds IMP with "[$HRP $Hchan $Hseria $Hpre][$]").
				Unshelve. done.
		Qed.

End RPC_proof_of_init.

Section RPC_proof_of_init_class.
	Context `{!anerisG Mdl Σ}.
	Context `{!lockG Σ}.
	Context `{!MTS_user_params}.
	Context `{!SpecChanG Σ}.

	Global Instance rpc_init : RPC_init.
	Proof.
		split. iIntros (E UP IP HE).
		iMod (RPC_init_setup_holds E HE) as (srv_si SrvInit Channel) "[Hinit Hspecs]".
		iModIntro.
		iExists _, _, _. iFrame.
	Qed.

End RPC_proof_of_init_class.

