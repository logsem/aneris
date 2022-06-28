From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.aneris_lang.lib
     Require Import lock_proof monitor_proof serialization_proof.
From aneris.examples.reliable_communication.lib.reliable_rpc
     Require Import params reliable_rpc_code.

Section Spec.
  Context `{ !anerisG Mdl Σ, !lockG Σ}.
	Context `{ !RPC_user_params }.
	Context (SrvInit : iProp Σ).
	Context (srv_si : message → iProp Σ).
	Notation srv_ip := (ip_of_address RPC_saddr).

	Context (LockedChannel : val → socket_address → iProp Σ).

  Definition is_val_of_serialization (seria_val : val) (seria : serialization) : Prop :=
	  ∃ ser_val deser_val,
	  seria_val = (ser_val, deser_val)%V ∧ 
		ser_val = s_ser (s_serializer seria) ∧ deser_val = s_deser (s_serializer seria).

 	Definition init_client_stub_spec A clt_addr : iProp Σ :=
		{{{ ⌜clt_addr ∉ A⌝ ∗ fixed A ∗ free_ports (ip_of_address clt_addr) {[port_of_address clt_addr]} ∗
			clt_addr ⤳ (∅, ∅) ∗ RPC_saddr ⤇ srv_si }}}
			init_client_stub #clt_addr #RPC_saddr @[ip_of_address clt_addr]
		{{{ chan, RET chan; LockedChannel chan clt_addr }}}.

	Definition call_spec `{UP : !RPC_handler_user_params} clt_addr : iProp Σ :=
		∀ chan arg_ser rep_ser,
		⌜is_val_of_serialization arg_ser RPC_arg_ser ∧ is_val_of_serialization rep_ser RPC_rep_ser⌝ -∗
		∀ argv argd,
		{{{ ⌜Serializable RPC_arg_ser argv⌝ ∗ RPC_handler_pre argv argd ∗ LockedChannel chan clt_addr }}}
			call chan (#RPC_name, (arg_ser, rep_ser))%V argv @[ip_of_address clt_addr]
		{{{ repv repd, RET repv; RPC_handler_post repv argd repd }}}.





  Definition s_call_spec `{UP: !RPC_handler_user_params} (name : val) (s_handler : val): iProp Σ :=
		⌜#RPC_name = name⌝ →
		∀ argd argv s_arg,
		{{{ ⌜s_is_ser RPC_arg_ser argv s_arg⌝ ∗ RPC_handler_pre argv argd }}}
			s_handler #s_arg @[srv_ip]
		{{{ repd repv (s_rep : string), RET #s_rep; ⌜s_is_ser RPC_rep_ser repv s_rep⌝ ∗ RPC_handler_post repv argd repd }}}.

	Definition handler_spec `{UP: !RPC_handler_user_params} (handler : val) :=
		∀ argd argv mon,
		{{{ RPC_handler_pre argv argd }}}
			handler mon argv @[srv_ip]
		{{{ repd repv, RET repv; RPC_handler_post repv argd repd }}}. Check (#1, #2)%V.

 	Definition implement_spec `{UP : !RPC_handler_user_params} : iProp Σ :=
		∀ (rpc : val) handler name v2,
		⌜rpc = (name, v2)%V⌝ ∧
		⌜name = #RPC_name⌝ -∗
		{{{ ⌜handler_spec handler⌝ }}}
			implement rpc handler @[srv_ip]
		{{{ v s_handler, RET v; ⌜v = (name, s_handler)%V⌝ ∗ s_call_spec name s_handler }}}.

		
			
(* Definition init_server_stub_spec A : iProp Σ :=
	{{{ RPC_saddr ⤇ srv_si ∗
			⌜RPC_saddr ∈ A⌝ ∗
			fixed A ∗
			RPC_saddr ⤳ (∅,∅) ∗
			free_ports (srv_ip) {[port_of_address RPC_saddr]} ∗
			SrvInit ∗
			is_monitor RPC_mN srv_ip RPC_mγ RPC_mv RPC_mR }}}
		run_server
				(s_serializer RPC_rep_ser)
				(s_serializer RPC_req_ser)
				#RPC_saddr
				RPC_mv
				RPC_handlers
				@[srv_ip]
	{{{ RET #(); ⌜True⌝ }}}.

Definition call_spec `{UP : RPC_handler_user_params} (handler : val) clt_addr : iProp Σ :=
	∀ reqv reqd,
	{{{ RPC_handler_pre reqv reqd }}}
		handler reqv @[ip_of_address clt_addr]
	{{{ repd, repv, RET repv; RPC_handler_post repv reqd repd }}}.

Definition init_client_stub_spec A sa : iProp Σ :=
	{{{ ⌜sa ∉ A⌝ ∗
			fixed A ∗
			free_ports (ip_of_address sa) {[port_of_address sa]} ∗ sa ⤳ (∅, ∅) ∗
			RPC_saddr ⤇ srv_si }}}
		init_client_stub
				#sa
				#RPC_saddr
			@[ip_of_address sa]
	{{{ }}}. *)