From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof serialization_proof list_proof.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From actris.channel Require Import proto.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Import lock_proof.

Section Sec.


Context `{ !anerisG Mdl Σ, !lockG Σ } .


Class RPC_user_params :=
{
  RPC_saddr : socket_address;
  RPC_mN : namespace;
}.

Context `{ !RPC_user_params }.

(* Params that characterize an RPC *)
Class RPC_rpc_params :=
{
  RPC_name : string;
  RPC_arg_ser  : serialization;
  RPC_arg_data : Type;
  RPC_rep_ser  : serialization;
  RPC_rep_data : Type;
  RPC_pre  : val → RPC_arg_data → iProp Σ;
  RPC_post : val → RPC_arg_data → RPC_rep_data → iProp Σ;
}.

(* List of RPC params, i.e. params of the interface *)
Definition RPC_interface_params := list RPC_rpc_params.

(* Params to match the concrete rpc and handler implementations *)
Class RPC_implementation_params (RP : RPC_rpc_params) :=
{
  RPC_val : val;
  RPC_handler : val;
  RPC_rpc_match :
    RPC_val = (#RP.(RPC_name), 
      ((RP.(RPC_arg_ser).(s_serializer).(s_ser), 
      RP.(RPC_arg_ser).(s_serializer).(s_deser))%V,
      (RP.(RPC_rep_ser).(s_serializer).(s_ser), 
      RP.(RPC_rep_ser).(s_serializer).(s_deser))%V)%V
    )%V;
  RPC_handler_spec :
    (∀ argv argd,
    {{{ RP.(RPC_pre) argv argd }}}
    RPC_handler argv @[ip_of_address RPC_saddr]
    {{{ repv repd, RET repv; RP.(RPC_post) repv argd repd }}})
}. 

(* Check if a given concrete handler (a val) match the spec of an given RPC *)
Definition is_impl_handler_of_rpc (handler : val) (RP : RPC_rpc_params):=
  (∀ argv argd s_arg,
    {{{ ⌜s_is_ser RP.(RPC_arg_ser) argv s_arg⌝ ∗
        RP.(RPC_pre) argv argd }}}
    handler #s_arg @[ip_of_address RPC_saddr]
    {{{ repv repd s_rep, RET #s_rep;
        ⌜s_is_ser RP.(RPC_rep_ser) repv s_rep⌝ ∗
        RP.(RPC_post) repv argd repd }}}).

Fixpoint is_list_of_interface (handlers : list val) (IP : RPC_interface_params) :=
  match handlers, IP with
  | [], [] => True
  | (name, h)%V :: l', RP :: IP' => 
      name = #RP.(RPC_name) ∧
      is_impl_handler_of_rpc h RP ∧ 
      is_list_of_interface l' IP'
  | _, _ => False
  end. 

(* Matches the logical interface with the concrete interface *)
Class RPC_interface_implementation (IP : RPC_interface_params) := 
{
  RPC_inter_val : val;
  RPC_inter_list : list val;
  RPC_inter_spec :
    (is_list RPC_inter_list RPC_inter_val ∧ 
     is_list_of_interface RPC_inter_list IP)
}.


End Sec.
