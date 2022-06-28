From aneris.aneris_lang Require Import lang.
From aneris.aneris_lang.lib Require Import lock_proof monitor_proof serialization_proof.
From aneris.aneris_lang.program_logic Require Import aneris_weakestpre.
From aneris.examples.reliable_communication.prelude Require Import ser_inj.
From actris.channel Require Import proto.

Set Default Proof Using "Type".

Canonical Structure valO := leibnizO val.
Notation iProto Σ := (iProto Σ val).
Notation iMsg Σ := (iMsg Σ val).

Import lock_proof.

Definition ser_list_is_injective ser_list :=
  Forall ser_is_injective ser_list.

Definition ser_pair_list_is_injective ser_list :=
  ser_list_is_injective (fst (split ser_list)) 
  ∧ ser_list_is_injective (snd (split ser_list)).

(* Tentatives avec un Fixpoint *)
(*
Fixpoint hlist (TS : list Type) : Type :=
  match TS with
    | nil => unit
    | T :: TS' => prod T (hlist TS')
  end.

Definition head {T : Type} {TS : list Type} (h : hlist (T :: TS)) : T :=
  fst h.

Definition tail {T : Type} {TS : list Type} (h : hlist (T :: TS)) : hlist TS :=
  snd h.

Fixpoint data_to_pre (Σ : gFunctors) (TS : list Type) : list Type :=
  match TS with
    | nil => []
    | T :: TS' => (val -> T -> iProp Σ) :: (data_to_pre Σ TS')
  end.

Fixpoint data_to_post (Σ : gFunctors) (TSargs : list Type) (TSreps : list Type) : list Type :=
  match TSargs with
    | nil => []
    | Targ :: TSargs' => match TSreps with
      | nil => [] (* shouldn't happen *)
      | Trep :: TSreps => (val -> Targ -> Trep -> iProp Σ) :: (data_to_post Σ TSargs TSreps)
    end
  end. 

Fixpoint hforall {Σ : gFunctors} (TS : list Type) (h : hlist TS) P : iProp Σ :=
  match TS with
    | nil => True
    | T :: TS' => P (head h) ∧ hforall TS' (tail h) P
  end. 
*)


(* Inductive hlist : list Type -> Type :=
  | Hnil : hlist nil
  | Hcons : forall {T} {TS}, T -> hlist TS -> hlist (T :: TS). 





Class MTS_user_params `{ !anerisG Mdl Σ, !lockG Σ } :=
  { 
    
    RPC_ser_list : list (serialization * serialization);
    RPC_ser_inj  : ser_pair_list_is_injective RPC_ser_list; 
    (* do same thing for inj_alt *)

    RPC_args_data : list Type;
    RPC_reps_data : list Type;
    RPC_handlers_pre : hlist (data_to_pre Σ RPC_args_data);
    RPC_handlers_post : hlist (data_to_post Σ RPC_args_data RPC_reps_data);

    RPC_saddr : socket_address;
    RPC_mN : namespace;
  }.

Arguments MTS_user_params {_ _ _ _}. *)




Class RPC_handler_user_params `{ !anerisG Mdl Σ, !lockG Σ } :=
{
  RPC_arg_ser  : serialization;
  RPC_arg_ser_inj : ser_is_injective RPC_arg_ser;
  RPC_arg_ser_inj_alt : ser_is_injective_alt RPC_arg_ser;
  RPC_arg_data : Type;
  RPC_rep_ser  : serialization;
  RPC_rep_ser_inj : ser_is_injective RPC_rep_ser;
  RPC_rep_ser_inj_alt : ser_is_injective_alt RPC_rep_ser;
  RPC_rep_data : Type;
  RPC_handler_pre  : val → RPC_arg_data → iProp Σ;
  RPC_handler_post : val → RPC_arg_data → RPC_rep_data → iProp Σ;
}.

Arguments RPC_handler_user_params {_ _ _ _}. Check RPC_handler_user_params.

Definition list_params `{ !anerisG Mdl Σ, !lockG Σ } := list RPC_handler_user_params.
Check list_params.

Class RPC_user_params `{ !anerisG Mdl Σ, !lockG Σ } :=
{
  RPC_saddr : socket_address;
  RPC_mN : namespace;
}.

Class RPC_spec_params `{ !anerisG Mdl Σ, !lockG Σ } := {
  RPC_mR : iProp Σ;
  RPC_mγ : gname;
  RPC_mv : val;
}.

Class RPC_handler_spec_params `{ !anerisG Mdl Σ, !lockG Σ } (HUP : RPC_handler_user_params) (UP : RPC_user_params)
  (SP : RPC_spec_params) :=
{
  RPC_handler : val;
  RPC_handler_spec :
  (∀ reqv reqd,
  {{{ is_monitor RPC_mN (ip_of_address RPC_saddr) RPC_mγ RPC_mv RPC_mR ∗
      locked RPC_mγ ∗ RPC_mR ∗
      RPC_handler_pre reqv reqd }}}
    RPC_handler RPC_mv reqv @[ip_of_address RPC_saddr]
  {{{ repv repd, RET repv;
      ⌜Serializable RPC_rep_ser repv⌝ ∗
      locked RPC_mγ ∗ RPC_mR ∗
      RPC_handler_post repv reqd repd }}})
}.

