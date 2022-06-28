From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.
From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof set_proof.
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
Import monitor_proof.
Import lock_proof.
Import client_server_code.

Section RPC_proof_of_code.
	Context `{ !anerisG Mdl Σ, !lockG Σ}.
	Context `{ !RPC_user_params }.
	Context (SrvInit : iProp Σ).
	Context (srv_si : message → iProp Σ).
	Notation srv_ip := (ip_of_address RPC_saddr).

	Definition req_prot_aux (rec : iProto Σ) : iProto Σ :=
		(<! (UP : RPC_handler_user_params) (req : val) (s_arg : string) (argv : val) (argd : RPC_arg_data) >
			MSG req {{ ⌜req = (#UP.(RPC_name), #s_arg)%V ∧ s_is_ser RPC_arg_ser argv s_arg⌝ ∗ RPC_handler_pre argv argd }} ;
		<? (s_rep : string) (repv : val) (repd : RPC_rep_data) >
			MSG #s_rep {{ ⌜s_is_ser RPC_rep_ser repv s_rep⌝ ∗ RPC_handler_post repv argd repd }};
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

  Definition is_val_of_serialization (seria_val : val) (seria : serialization) : Prop :=
	  ∃ ser_val deser_val,
	  seria_val = (ser_val, deser_val)%V ∧ 
		ser_val = s_ser (s_serializer seria) ∧ deser_val = s_deser (s_serializer seria).

  Definition s_call_spec `{UP: !RPC_handler_user_params} (name : val) (s_handler : val): iProp Σ :=
		⌜#RPC_name = name⌝ →
		∀ argd argv s_arg (mon : val),
		{{{ ⌜s_is_ser RPC_arg_ser argv s_arg⌝ ∗ RPC_handler_pre argv argd }}}
			s_handler mon #s_arg @[srv_ip]
		{{{ repd repv (s_rep : string), RET #s_rep; ⌜s_is_ser RPC_rep_ser repv s_rep⌝ ∗ RPC_handler_post repv argd repd }}}.

	(*Definition handler_spec `{UP: !RPC_handler_user_params} (handler : val) : iProp Σ :=
		∀ argd argv (mon : val),
		{{{ RPC_handler_pre argv argd }}}
			handler mon argv @[srv_ip]
		{{{ repd repv, RET repv; RPC_handler_post repv argd repd ∗ ⌜Serializable RPC_rep_ser repv⌝ }}}.*)

 	(* Definition implement_spec `{UP : !RPC_handler_user_params} : iProp Σ :=
		∀ (rpc : val) handler name ser1 ser2,
		⌜rpc = (name, (ser1, ser2))%V⌝ ∧
		⌜name = #RPC_name⌝ ∧ 
		⌜is_val_of_serialization ser1 RPC_arg_ser ∧ is_val_of_serialization ser2 RPC_rep_ser⌝ -∗
		{{{ handler_spec handler }}}
			implement rpc handler @[srv_ip]
		{{{ v s_handler, RET v; ⌜v = (name, s_handler)%V⌝ ∗ s_call_spec name s_handler }}}.

	Lemma implement_spec_holds `{UP : !RPC_handler_user_params} : ⊢ implement_spec.
	Proof.
		iIntros (rpc handler name ser1 ser2 Hrpc Φ). iModIntro. iIntros "#Hspec Hcont".
		rewrite /implement. wp_pures.
		destruct Hrpc as [-> [-> [Hser1 Hser2]]]. wp_pures.
		iApply "Hcont". iSplitL; try done.
		rewrite /s_call_spec. iIntros "_". iIntros (argd argv s_arg mon Ψ). iModIntro. iIntros "[%Hser Hpre] Hcont".
		wp_pures.
		destruct Hser1 as [ser_val [deser_val [-> [-> ->]]]]. wp_pures.
		wp_apply (s_deser_spec RPC_arg_ser). iPureIntro. apply Hser. iIntros "_".
		wp_pures.
		destruct Hser2 as [ser_val [deser_val [-> [-> ->]]]]. 
		wp_apply ("Hspec" with "[$Hpre]").
		iIntros (repd repv) "[Hpost %Hrep]".
		wp_pures.
		wp_apply (s_ser_spec RPC_rep_ser).
		{ iPureIntro. apply Hrep. }
		iIntros (s Hrepser). iApply "Hcont".
		iFrame. done.
	Qed. *)

	(* spécification de ce qui est obtenu quand on fait "call chan aRPC"
	Definition user_handler_spec `{UP : !RPC_handler_user_params} handler clt_addr : iProp Σ :=
		∀ argv argd,
		{{{ ⌜Serializable RPC_arg_ser argv⌝ ∗ RPC_handler_pre argv argd }}}
			handler argv @[ip_of_address clt_addr]
		{{{ repv repd, RET repv; RPC_handler_post repv argd repd }}}. *)

	Definition LockedChannel (chan : val) clt_addr : iProp Σ :=
		∃ c lk (γ : gname), ⌜chan = (c, lk)%V⌝ ∧ 
		is_lock (RPC_mN.@"proxy") (ip_of_address clt_addr) γ lk
			(c ↣{ip_of_address clt_addr,RCParams_clt_ser} RCParams_protocol).

	Definition init_client_stub_spec A clt_addr : iProp Σ :=
		{{{ ⌜clt_addr ∉ A⌝ ∗ fixed A ∗ free_ports (ip_of_address clt_addr) {[port_of_address clt_addr]} ∗
			clt_addr ⤳ (∅, ∅) ∗ RPC_saddr ⤇ reserved_server_socket_interp }}}
			init_client_stub #clt_addr #RPC_saddr @[ip_of_address clt_addr]
		{{{ chan, RET chan; LockedChannel chan clt_addr }}}.

	Lemma init_client_stub_spec_holds A clt_addr : ⊢ init_client_stub_spec A clt_addr.
	Proof.
		rewrite /init_client_stub_spec.
		iIntros (Φ) "!#". iIntros "(#Hna & #Hfix & Hfp & Hhist & #Hsi) Hcont".
		rewrite /init_client_stub. wp_pures.
		wp_apply (RCSpec_make_client_skt_spec with "[$Hfix $Hfp $Hhist $Hsi]"). iAssumption.
		iIntros (skt) "Hcl". wp_pures.
		wp_apply (RCSpec_connect_spec with "[$Hcl]").
		iIntros (c) "Hcl". wp_pures.
		wp_apply (newlock_spec
					 (RPC_mN .@ "proxy") _
					 ( c ↣{ip_of_address clt_addr,RCParams_clt_ser} RCParams_protocol) with "[$Hcl]").
		iIntros (lk γ) "#Hlk". wp_pures.
		iApply "Hcont".
		iExists c, lk, γ. iFrame "#". done.
	Qed.

	Definition call_spec `{UP : !RPC_handler_user_params} clt_addr : iProp Σ :=
		∀ chan arg_ser rep_ser,
		⌜is_val_of_serialization arg_ser RPC_arg_ser ∧ is_val_of_serialization rep_ser RPC_rep_ser⌝ -∗
		∀ argv argd,
		{{{ ⌜Serializable RPC_arg_ser argv⌝ ∗ RPC_handler_pre argv argd ∗ LockedChannel chan clt_addr }}}
			call chan (#RPC_name, (arg_ser, rep_ser))%V argv @[ip_of_address clt_addr]
		{{{ repv repd, RET repv; RPC_handler_post repv argd repd }}}.

	Lemma call_spec_holds `{UP : !RPC_handler_user_params} clt_addr : ⊢ call_spec clt_addr.
	Proof.
		rewrite /call_spec.
		iIntros (chan arg_ser rep_ser [Hargser Hrepser] argv argd Φ) "!#".
		iIntros "(%Hser & Hpre & #Hlc) Hcont".
		rewrite /call. 
		iDestruct "Hlc" as (c lk γ ->) "Hlk". wp_pures.
		destruct Hargser as [_ [_ [-> [-> ->]]]]. wp_pures. 
		wp_apply (s_ser_spec RPC_arg_ser). {iPureIntro. apply Hser. }
		iIntros (s Hisser). wp_pures.
		wp_apply (acquire_spec with "[$Hlk]").
		iIntros (?) "(-> & Hlocked & Hc)". wp_seq.
		wp_send with "[$Hpre]"; first done.
		wp_seq.
		wp_recv (s_rep repv repd) as "[%Hisserep Hpost]". wp_pures.
		wp_apply (release_spec with "[$Hlk $Hc $Hlocked]").
		iIntros (? ->). wp_seq.
		wp_pures. destruct Hrepser as [_ [_ [-> [-> ->]]]]. wp_pures.
		wp_apply (s_deser_spec RPC_rep_ser); first done.
		iIntros "_". by iApply "Hcont".
	Qed.

	Definition call_handler_spec : iProp Σ :=
		⌜is_map handlers handlers_map⌝ -∗
		{{{ 
				is_monitor RPC_mN (ip_of_address RPC_saddr) RPC_mγ RPC_mv RPC_mR ∗
				locked RPC_mγ ∗ RPC_mR ∗
				RPC_handler_pre reqv reqd  }}}
			call_handler handlers name s_arg
		{{{ repv repd, RET repv;
				⌜Serializable RPC_rep_ser repv⌝ ∗
				locked RPC_mγ ∗ RPC_mR ∗
				RPC_handler_post repv reqd repd }}}

	Lemma service_loop_proof `{UP : !RPC_handler_user_params} (c : val) :
    {{{ is_monitor RPC_mN (ip_of_address RPC_saddr) RPC_mγ RPC_mv RPC_mR ∗
      c ↣{ ip_of_address RPC_saddr, RPC_rep_ser } iProto_dual req_prot  }}}
      service_loop c RPC_mv RPC_handler #() @[ip_of_address RPC_saddr]
    {{{ RET #(); ⌜True⌝  }}}.


