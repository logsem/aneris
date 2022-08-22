From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.aneris_lang.lib
     Require Import lock_proof monitor_proof serialization_proof.
From aneris.examples.reliable_communication.lib.reliable_rpc
     Require Import params reliable_rpc_code.

Section Spec.
	Context `{ !anerisG Mdl Σ, !lockG Σ}.
	Context `{ !RPC_user_params }.
	Context `{ IP : !@RPC_interface_params Σ }.
	Context (SrvInit : iProp Σ).
	Context (srv_si : message → iProp Σ).
	Notation srv_ip := (ip_of_address RPC_saddr).

	Context (Channel : val → socket_address → iProp Σ).

	Definition implement_spec (*{RP : RPC_rpc_params}*) (*IMP : RPC_implementation_params RP*) : iProp Σ :=
		∀ (RP : RPC_rpc_params) rpc_val handler,
		{{{ ⌜In RP IP.(RPC_inter)⌝ ∗
			⌜is_rpc_val RP rpc_val⌝ ∗
			handler_spec RP handler }}}
			implement rpc_val handler @[srv_ip]
		{{{ h, RET (#RP.(RPC_name), h)%V; ⌜is_impl_handler_of_rpc h RP⌝ }}}.

	Definition init_server_stub_spec (II : RPC_interface_implementation IP) : iProp Σ :=
		∀ A,
		{{{ RPC_saddr ⤇ srv_si ∗
				fixed A ∗
				⌜RPC_saddr ∈ A⌝ ∗
				RPC_saddr ⤳ (∅, ∅) ∗
				free_ports (srv_ip) {[port_of_address RPC_saddr]} ∗
				SrvInit }}}
			init_server_stub #RPC_saddr II.(RPC_inter_val) @[srv_ip]
		{{{ RET #(); ⌜False⌝ }}}.

	Definition init_client_stub_spec : iProp Σ :=
		∀ A clt_addr,
		{{{ RPC_saddr ⤇ srv_si ∗
				fixed A ∗
				⌜clt_addr ∉ A⌝ ∗
				clt_addr ⤳ (∅, ∅) ∗
				free_ports (ip_of_address clt_addr) {[port_of_address clt_addr]} }}}
			init_client_stub #clt_addr #RPC_saddr @[ip_of_address clt_addr]
		{{{ chan, RET chan; Channel chan clt_addr }}}.

	Definition call_spec (*{RP : RPC_rpc_params}*) (*IMP : RPC_implementation_params RP*) : iProp Σ :=
		∀ (RP : RPC_rpc_params) chan clt_addr argv argd rpc_val,
		{{{ ⌜In RP IP.(RPC_inter)⌝ ∗
			⌜is_rpc_val RP rpc_val⌝ ∗ 
			Channel chan clt_addr ∗
			⌜Serializable RP.(RPC_arg_ser) argv⌝ ∗ 
			RP.(RPC_pre) argv argd }}}
			call chan rpc_val argv @[ip_of_address clt_addr]
		{{{ repv repd, RET repv; 
			Channel chan clt_addr ∗
			RP.(RPC_post) repv argd repd }}}.

End Spec.


Section RPC_Init.

	Context `{ !anerisG Mdl Σ, !lockG Σ}.

	Class RPC_init := {
		RPC_init_setup E (UP : RPC_user_params) (IP : RPC_interface_params) :
		↑RPC_mN ⊆ E →
    ⊢ |={E}=> ∃ (srv_si : message → iProp Σ) (SrvInit : iProp Σ)
								(Channel : val → socket_address → iProp Σ),
			SrvInit ∗
			(∀ (II : RPC_interface_implementation IP), 
				init_server_stub_spec SrvInit srv_si II) ∗
			(init_client_stub_spec srv_si Channel) ∗
			( @call_spec _ _ _ IP Channel)
	}.

End RPC_Init.
